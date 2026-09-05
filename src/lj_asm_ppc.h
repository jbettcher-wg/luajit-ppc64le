/*
** PPC IR assembler (SSA IR -> machine code).
** Copyright (C) 2005-2026 Mike Pall. See Copyright Notice in luajit.h
*/

/* -- PPC64 phase-1 gate --------------------------------------------------- */

#if LJ_ARCH_PPC64
/* The handlers below are still the ppc32 backend: 32-bit loads, 32-bit
** tags, ppc32 frame. Until each one is converted (Phases 2-4 of the
** ppc64le backend plan) every path that could emit code is redirected here,
** so a JIT-enabled build degrades to the interpreter instead of running
** ppc32 code on a 64-bit machine. The per-handler redirection block at the
** end of this file is generated from lj_asm.c/lj_asm_ppc.h; remove a
** handler's line there when its 64-bit version lands.
*/
static void asm_nyi64(ASMState *as, IRIns *ir, const void *handler)
{
  UNUSED(handler);  /* Keeps the still-unconverted ppc32 handler referenced. */
  setintV(&as->J->errinfo, ir->o);
  lj_trace_err_info(as->J, LJ_TRERR_NYIIR);
}
#endif

/* -- PPC64 GC64 tagged values (D4) --------------------------------------- */

#if LJ_ARCH_PPC64
/* A TValue is one 64-bit word: a 17-bit tag in bits 63..47 and a 47-bit
** payload (lj_obj.h). The tag read with an arithmetic shift is the signed
** 17-bit itype, i.e. exactly (int32_t)irt_toitype(t) for a tagged value,
** and for any double (NaN-boxed) a value that is unsigned-below
** (int64_t)LJ_TISNUM -- so "is a number" is one cmpld against a hoisted
** li -14, and "is exactly type T" is one cmpdi.
**
** The shift is a macro only so the handbook's tag-corruption controls can
** move it by one bit in a single-variable build: LJ_TEST_BREAK_TAGSHIFT
** breaks the extract (every guard on a tagged value fires),
** LJ_TEST_BREAK_TAGSTORE breaks the insert (stores plant a tag no reader
** accepts, so results differ).
*/
#ifdef LJ_TEST_BREAK_TAGSHIFT
#define LJ_TAGSHIFT		46
#else
#define LJ_TAGSHIFT		47
#endif
#ifdef LJ_TEST_BREAK_TAGSTORE
#define LJ_TAGSHIFT_ST		46
#else
#define LJ_TAGSHIFT_ST		47
#endif

/* tag = v >> LJ_TAGSHIFT, arithmetic. */
#define emit_tag(as, tag, v)	emit_sradi(as, (tag), (v), LJ_TAGSHIFT)
/* payload = v with the tag bits cleared (GC pointer, lightud seg|ofs). */
#define emit_untag(as, dst, v)	emit_clrldi(as, (dst), (v), 64-LJ_TAGSHIFT)

/* 64-bit constants for tag stores (unsigned arithmetic: no UB shifts). */
#define tvtag64(t) \
  ((int64_t)((uint64_t)irt_toitype((t)) << LJ_TAGSHIFT_ST))
#define tvpri64(t) \
  ((int64_t)~((uint64_t)~irt_toitype((t)) << LJ_TAGSHIFT_ST))
/* The int tag as the sradi result reads it: -14. */
#define tvtisnum		((int32_t)LJ_TISNUM)

/* GPR <-> FPR moves (ISA 2.07). VSR number == FPR number for f0-f31;
** XT/XS travel in the T field, the GPR in the A field (encoding oracle).
*/
#define emit_mtvsrd(as, f, r)	emit_tab(as, PPCI_MTVSRD, ((f) & 31), (r), 0)
#define emit_mtvsrwa(as, f, r)	emit_tab(as, PPCI_MTVSRWA, ((f) & 31), (r), 0)
#define emit_mtvsrwz(as, f, r)	emit_tab(as, PPCI_MTVSRWZ, ((f) & 31), (r), 0)
#define emit_mfvsrd(as, r, f)	emit_tab(as, PPCI_MFVSRD, ((f) & 31), (r), 0)
#define emit_mfvsrwz(as, r, f)	emit_tab(as, PPCI_MFVSRWZ, ((f) & 31), (r), 0)

/* D/DS-form load/store opcode -> its X-form (indexed) twin. The ppc32
** trick of folding the primary opcode into the XO field does not cover
** the DS-form ld/std/lwa.
*/
static PPCIns asm_xform(PPCIns pi)
{
  switch (pi) {
  case PPCI_LD: return PPCI_LDX;
  case PPCI_STD: return PPCI_STDX;
  case PPCI_LWA: return PPCI_LWAX;
  default: return PPCI_LWZX | ((pi >> 20) & 0x780);
  }
}

/* DS-form (ld/std/lwa): displacement must be a multiple of 4. */
#define asm_isdsform(pi)	(((pi) >> 26) == 58 || ((pi) >> 26) == 62)
#endif

/* -- Register allocator extensions --------------------------------------- */

/* Allocate a register with a hint. */
static Reg ra_hintalloc(ASMState *as, IRRef ref, Reg hint, RegSet allow)
{
  Reg r = IR(ref)->r;
  if (ra_noreg(r)) {
    if (!ra_hashint(r) && !iscrossref(as, ref))
      ra_sethint(IR(ref)->r, hint);  /* Propagate register hint. */
    r = ra_allocref(as, ref, allow);
  }
  ra_noweak(as, r);
  return r;
}

/* Allocate two source registers for three-operand instructions. */
static Reg ra_alloc2(ASMState *as, IRIns *ir, RegSet allow)
{
  IRIns *irl = IR(ir->op1), *irr = IR(ir->op2);
  Reg left = irl->r, right = irr->r;
  if (ra_hasreg(left)) {
    ra_noweak(as, left);
    if (ra_noreg(right))
      right = ra_allocref(as, ir->op2, rset_exclude(allow, left));
    else
      ra_noweak(as, right);
  } else if (ra_hasreg(right)) {
    ra_noweak(as, right);
    left = ra_allocref(as, ir->op1, rset_exclude(allow, right));
  } else if (ra_hashint(right)) {
    right = ra_allocref(as, ir->op2, allow);
    left = ra_alloc1(as, ir->op1, rset_exclude(allow, right));
  } else {
    left = ra_allocref(as, ir->op1, allow);
    right = ra_alloc1(as, ir->op2, rset_exclude(allow, left));
  }
  return left | (right << 8);
}

/* -- Guard handling ------------------------------------------------------ */

/* Setup exit stubs after the end of each trace. */
static void asm_exitstub_setup(ASMState *as, ExitNo nexits)
{
  ExitNo i;
  int ind;
  uintptr_t target = (uintptr_t)(void *)lj_vm_exit_handler;
  MCode *mxp = as->mctop;
  if (mxp - (nexits + 4 + MCLIM_REDZONE) < as->mclim)
    asm_mclimit(as);
  ind = ((target - (uintptr_t)(mxp - nexits - 2) + 0x02000000u) >> 26) ? 2 : 0;
  /* !ind: 1: mflr r0; bl ->vm_exit_handler; li r0, traceno;
  **  ind: 1: lwz r0, K32_VXH(jgl); mtctr r0; mflr r0; bctrl; li r0, traceno;
  **          bl <1; bl <1; ...
  ** PPC64 ind: ld r0, K64_VXH(jgl) instead of lwz. r0 (RID_TMP) is the only
  ** register that may be clobbered here: every allocatable register is live
  ** at an exit and lands in the ExitState, so r12 is *not* an option even
  ** though ELFv2 would like it (->vm_exit_handler has no TOC prologue and
  ** does not need it, see D2/Model A).
  */
  for (i = nexits-1; (int32_t)i >= 0; i--)
    *--mxp = PPCI_BL | (((-3-ind-i) & 0x00ffffffu) << 2);
  as->mcexit = mxp;
  *--mxp = PPCI_LI|PPCF_T(RID_TMP)|as->T->traceno;  /* Read by exit handler. */
  if (ind) {
    *--mxp = PPCI_BCTRL;
    *--mxp = PPCI_MFLR | PPCF_T(RID_TMP);
    *--mxp = PPCI_MTCTR | PPCF_T(RID_TMP);
#if LJ_ARCH_PPC64
    emit_guard(as, (jglofs(as, &as->J->k64[LJ_K64_VM_EXIT_HANDLER]) & 3) == 0);
    *--mxp = PPCI_LD | PPCF_T(RID_TMP) | PPCF_A(RID_JGL) |
	     jglofs(as, &as->J->k64[LJ_K64_VM_EXIT_HANDLER]);
#else
    *--mxp = PPCI_LWZ | PPCF_T(RID_TMP) | PPCF_A(RID_JGL) |
	     jglofs(as, &as->J->k32[LJ_K32_VM_EXIT_HANDLER]);
#endif
  } else {
    mxp--;
    *mxp = PPCI_BL | ((target - (uintptr_t)mxp) & 0x03fffffcu);
    *--mxp = PPCI_MFLR | PPCF_T(RID_TMP);
  }
  as->mctop = mxp;
}

static MCode *asm_exitstub_addr(ASMState *as, ExitNo exitno)
{
  /* Keep this in-sync with exitstub_trace_addr(). */
  return as->mcexit + exitno;
}

/* Emit conditional branch to exit for guard. */
#if LJ_ARCH_PPC64
/* Emit conditional branch to exit for guard, testing bit cc of CR field
** crf (PPC_CRF_CMP for compares, PPC_CRF_OV for the mcrxrx projection).
*/
static void asm_guardcr(ASMState *as, int crf, PPCCC cc)
{
  MCode *target = asm_exitstub_addr(as, as->snapno);
  MCode *p = as->mcp;
  if (LJ_UNLIKELY(p == as->invmcp)) {
    as->loopinv = 1;
    *p = PPCI_B | (((target-p) & 0x00ffffffu) << 2);
    emit_condbranch_crf(as, PPCI_BC, crf, cc^4, p);
    return;
  }
  emit_condbranch_crf(as, PPCI_BC, crf, cc, target);
}
#define asm_guardcc(as, cc)	asm_guardcr(as, PPC_CRF_CMP, (cc))
#else
static void asm_guardcc(ASMState *as, PPCCC cc)
{
  MCode *target = asm_exitstub_addr(as, as->snapno);
  MCode *p = as->mcp;
  if (LJ_UNLIKELY(p == as->invmcp)) {
    as->loopinv = 1;
    *p = PPCI_B | (((target-p) & 0x00ffffffu) << 2);
    emit_condbranch(as, PPCI_BC, cc^4, p);
    return;
  }
  emit_condbranch(as, PPCI_BC, cc, target);
}
#endif

/* -- Operand fusion ------------------------------------------------------ */

/* Limit linear search to this distance. Avoids O(n^2) behavior. */
#define CONFLICT_SEARCH_LIM	31

/* Check if there's no conflicting instruction between curins and ref. */
static int noconflict(ASMState *as, IRRef ref, IROp conflict)
{
  IRIns *ir = as->ir;
  IRRef i = as->curins;
  if (i > ref + CONFLICT_SEARCH_LIM)
    return 0;  /* Give up, ref is too far away. */
  while (--i > ref)
    if (ir[i].o == conflict)
      return 0;  /* Conflict found. */
  return 1;  /* Ok, no conflict. */
}

/* Fuse the array base of colocated arrays. */
static int32_t asm_fuseabase(ASMState *as, IRRef ref)
{
  IRIns *ir = IR(ref);
  if (ir->o == IR_TNEW && ir->op1 <= LJ_MAX_COLOSIZE &&
      !neverfuse(as) && noconflict(as, ref, IR_NEWREF))
    return (int32_t)sizeof(GCtab);
  return 0;
}

/* Indicates load/store indexed is ok. */
#define AHUREF_LSX	((int32_t)0x80000000)

/* Fuse array/hash/upvalue reference into register+offset operand. */
static Reg asm_fuseahuref(ASMState *as, IRRef ref, int32_t *ofsp, RegSet allow)
{
  IRIns *ir = IR(ref);
  if (ra_noreg(ir->r)) {
    if (ir->o == IR_AREF) {
      if (mayfuse(as, ref)) {
	if (irref_isk(ir->op2)) {
	  IRRef tab = IR(ir->op1)->op1;
	  int32_t ofs = asm_fuseabase(as, tab);
	  IRRef refa = ofs ? tab : ir->op1;
	  ofs += 8*IR(ir->op2)->i;
	  if (checki16(ofs)) {
	    *ofsp = ofs;
	    return ra_alloc1(as, refa, allow);
	  }
	}
	if (*ofsp == AHUREF_LSX) {
	  Reg base = ra_alloc1(as, ir->op1, allow);
	  Reg idx = ra_alloc1(as, ir->op2, rset_exclude(RSET_GPR, base));
	  return base | (idx << 8);
	}
      }
    } else if (ir->o == IR_HREFK) {
      if (mayfuse(as, ref)) {
	int32_t ofs = (int32_t)(IR(ir->op2)->op2 * sizeof(Node));
	if (checki16(ofs)) {
	  *ofsp = ofs;
	  return ra_alloc1(as, ir->op1, allow);
	}
      }
    } else if (ir->o == IR_UREFC) {
      if (irref_isk(ir->op1)) {
	GCfunc *fn = ir_kfunc(IR(ir->op1));
	intptr_t ofs = (intptr_t)&gcref(fn->l.uvptr[(ir->op2 >> 8)])->uv.tv;
	intptr_t jgl = (intptr_t)J2G(as->J);
	if ((uintptr_t)(ofs-jgl) < 65536) {
	  *ofsp = (int32_t)(ofs-jgl-32768);
	  return RID_JGL;
	} else {
	  *ofsp = (int32_t)(int16_t)ofs;  /* uv.tv is 8-aligned: DS-form ok. */
	  return ra_allock(as, ofs-(int16_t)ofs, allow);
	}
      }
    } else if (ir->o == IR_TMPREF) {
      *ofsp = (int32_t)(offsetof(global_State, tmptv)-32768);
      return RID_JGL;
    }
  }
  *ofsp = 0;
  return ra_alloc1(as, ref, allow);
}

#if LJ_ARCH_PPC64
/* Fuse XLOAD/XSTORE reference into load/store operand. */
static void asm_fusexref(ASMState *as, PPCIns pi, Reg rt, IRRef ref,
			 RegSet allow, int32_t ofs)
{
  IRIns *ir = IR(ref);
  Reg base;
  if (ra_noreg(ir->r) && canfuse(as, ir)) {
    if (ir->o == IR_ADD) {
      intptr_t ofs2;
      if (irref_isk(ir->op2) && (ofs2 = ofs + get_kval(as, ir->op2),
				  checki16(ofs2)) &&
	  (!asm_isdsform(pi) || (ofs2 & 3) == 0)) {
	ofs = (int32_t)ofs2;
	ref = ir->op1;
      } else if (ofs == 0) {
	Reg right, left = ra_alloc2(as, ir, allow);
	right = (left >> 8); left &= 255;
	emit_fab(as, asm_xform(pi), rt, left, right);
	return;
      }
    } else if (ir->o == IR_STRREF) {
      lj_assertA(ofs == 0, "bad usage");
      ofs = (int32_t)sizeof(GCstr);
      if (irref_isk(ir->op2)) {
	ofs += IR(ir->op2)->i;
	ref = ir->op1;
      } else {
	/* String base + sign-extended 32-bit index (D3 widening site). */
	Reg tmp, right, left = ra_alloc2(as, ir, allow);
	right = (left >> 8); left &= 255;
	tmp = ra_scratch(as, rset_exclude(rset_exclude(allow, left), right));
	emit_fai(as, pi, rt, tmp, ofs);
	emit_tab(as, PPCI_ADD, tmp, left, tmp);
	emit_extsw(as, tmp, right);
	return;
      }
      if (!checki16(ofs) || (asm_isdsform(pi) && (ofs & 3))) {
	Reg left = ra_alloc1(as, ref, allow);
	Reg right = ra_allock(as, ofs, rset_exclude(allow, left));
	emit_fab(as, asm_xform(pi), rt, left, right);
	return;
      }
    }
  }
  base = ra_alloc1(as, ref, allow);
  emit_fai(as, pi, rt, base, ofs);
}
#else
/* Fuse XLOAD/XSTORE reference into load/store operand. */
static void asm_fusexref(ASMState *as, PPCIns pi, Reg rt, IRRef ref,
			 RegSet allow, int32_t ofs)
{
  IRIns *ir = IR(ref);
  Reg base;
  if (ra_noreg(ir->r) && canfuse(as, ir)) {
    if (ir->o == IR_ADD) {
      int32_t ofs2;
      if (irref_isk(ir->op2) && (ofs2 = ofs + IR(ir->op2)->i, checki16(ofs2))) {
	ofs = ofs2;
	ref = ir->op1;
      } else if (ofs == 0) {
	Reg right, left = ra_alloc2(as, ir, allow);
	right = (left >> 8); left &= 255;
	emit_fab(as, PPCI_LWZX | ((pi >> 20) & 0x780), rt, left, right);
	return;
      }
    } else if (ir->o == IR_STRREF) {
      lj_assertA(ofs == 0, "bad usage");
      ofs = (int32_t)sizeof(GCstr);
      if (irref_isk(ir->op2)) {
	ofs += IR(ir->op2)->i;
	ref = ir->op1;
      } else if (irref_isk(ir->op1)) {
	ofs += IR(ir->op1)->i;
	ref = ir->op2;
      } else {
	/* NYI: Fuse ADD with constant. */
	Reg tmp, right, left = ra_alloc2(as, ir, allow);
	right = (left >> 8); left &= 255;
	tmp = ra_scratch(as, rset_exclude(rset_exclude(allow, left), right));
	emit_fai(as, pi, rt, tmp, ofs);
	emit_tab(as, PPCI_ADD, tmp, left, right);
	return;
      }
      if (!checki16(ofs)) {
	Reg left = ra_alloc1(as, ref, allow);
	Reg right = ra_allock(as, ofs, rset_exclude(allow, left));
	emit_fab(as, PPCI_LWZX | ((pi >> 20) & 0x780), rt, left, right);
	return;
      }
    }
  }
  base = ra_alloc1(as, ref, allow);
  emit_fai(as, pi, rt, base, ofs);
}
#endif

/* Fuse XLOAD/XSTORE reference into indexed-only load/store operand. */
static void asm_fusexrefx(ASMState *as, PPCIns pi, Reg rt, IRRef ref,
			  RegSet allow)
{
  IRIns *ira = IR(ref);
  Reg right, left;
  if (canfuse(as, ira) && ira->o == IR_ADD && ra_noreg(ira->r)) {
    left = ra_alloc2(as, ira, allow);
    right = (left >> 8); left &= 255;
  } else {
    right = ra_alloc1(as, ref, allow);
    left = RID_R0;
  }
  emit_tab(as, pi, rt, left, right);
}

#if !LJ_SOFTFP
/* Fuse to multiply-add/sub instruction. */
static int asm_fusemadd(ASMState *as, IRIns *ir, PPCIns pi, PPCIns pir)
{
  IRRef lref = ir->op1, rref = ir->op2;
  IRIns *irm;
  if ((as->flags & JIT_F_OPT_FMA) &&
      lref != rref &&
      ((mayfuse(as, lref) && (irm = IR(lref), irm->o == IR_MUL) &&
	ra_noreg(irm->r)) ||
       (mayfuse(as, rref) && (irm = IR(rref), irm->o == IR_MUL) &&
	(rref = lref, pi = pir, ra_noreg(irm->r))))) {
    Reg dest = ra_dest(as, ir, RSET_FPR);
    Reg add = ra_alloc1(as, rref, RSET_FPR);
    Reg right, left = ra_alloc2(as, irm, rset_exclude(RSET_FPR, add));
    right = (left >> 8); left &= 255;
    emit_facb(as, pi, dest, left, right, add);
    return 1;
  }
  return 0;
}
#endif

/* -- Calls --------------------------------------------------------------- */

#if LJ_ARCH_PPC64
/* An ASMREF_L/TMP1/TMP2 argument holds a pointer the handler put there;
** only real IR refs (constants and instructions) carry an IR width.
*/
#define asm_isasmref(ref)	((ref) >= ASMREF_TMP1 && (ref) <= ASMREF_L)

/* Generate a call to a C function: ELFv2 argument marshalling.
**
** Every argument, GPR- or FPR-class, occupies one doubleword slot of the
** parameter list: slots 0..7 are r3..r10, slot k >= 8 is at 96+8*(k-8)(sp)
** (SPS_FIRST), i.e. above the 96-byte header whose bytes 32..95 are the
** callee-scratch parameter save area (R8). A non-variadic FP argument goes
** to the next free FPR f1..f13 and still consumes its slot; nothing is
** stored to the slot. Arguments after the recorder's varargs marker (a 0
** ref planted by lj_crecord.c) are variadic: FP values travel in the GPR
** slot as their double image (mfvsrd), exactly what lj_ccall.c's per-arg
** isva does and what GCC 16 emits for a variadic call site.
**
** Width discipline (D3): the callee does not re-extend sub-doubleword
** integers (GCC 16 emits a bare blr for long f(int a){return a;}), so every
** 32-bit IR value is sign- or zero-extended here, in the argument register
** itself, or into r0 before a std to a stack slot.
*/
static void asm_gencall(ASMState *as, const CCallInfo *ci, IRRef *args)
{
  uint32_t n, nargs = CCI_XNARGS(ci);
  int32_t ofs = sps_scale(SPS_FIRST);
  Reg gpr = REGARG_FIRSTGPR, fpr = REGARG_FIRSTFPR;
  int isva = 0;
  if ((void *)ci->func)
    emit_call(as, (void *)ci->func);
  for (n = 0; n < nargs; n++) {  /* Setup args. */
    IRRef ref = args[n];
    IRIns *ir;
    if (!ref) {  /* Marker for the start of the variadic part. */
      isva = 1;
      continue;
    }
    ir = IR(ref);
    if (irt_isfp(ir->t) && !isva) {
      if (fpr <= REGARG_LASTFPR) {
	lj_assertA(rset_test(as->freeset, fpr),
		   "reg %d not free", fpr);  /* Already evicted. */
	ra_leftov(as, fpr, ref);
	fpr++;
	if (gpr <= REGARG_LASTGPR) gpr++; else ofs += 8;  /* Slot consumed. */
      } else {  /* 14th+ FP argument: its slot is on the stack by then. */
	Reg r = ra_alloc1(as, ref, RSET_FPR);
	lj_assertA(gpr > REGARG_LASTGPR, "FP arg 14+ in GPR slot range");
	emit_spstore(as, ir, r, ofs);
	ofs += 8;
      }
    } else if (irt_isfp(ir->t)) {  /* Variadic FP argument: GPR image. */
      Reg r;
      lj_assertA(irt_isnum(ir->t), "vararg float not promoted to double");
      if (gpr <= REGARG_LASTGPR) {
	RegSet of = as->freeset;
	lj_assertA(rset_test(as->freeset, gpr), "reg %d not free", gpr);
	/* Protect the argument GPRs from being used for rematerialization. */
	as->freeset &= ~RSET_RANGE(REGARG_FIRSTGPR, REGARG_LASTGPR+1);
	r = ra_alloc1(as, ref, RSET_FPR);
	as->freeset |= (of & RSET_RANGE(REGARG_FIRSTGPR, REGARG_LASTGPR+1));
	emit_tab(as, PPCI_MFVSRD, (r & 31), gpr, 0);
	gpr++;
      } else {
	r = ra_alloc1(as, ref, RSET_FPR);
	emit_fai(as, PPCI_STFD, r, RID_SP, ofs);
	ofs += 8;
      }
    } else {  /* GPR argument. */
      int wide = asm_isasmref(ref) || irt_is64(ir->t);
      if (gpr <= REGARG_LASTGPR) {
	lj_assertA(rset_test(as->freeset, gpr),
		   "reg %d not free", gpr);  /* Already evicted. */
	if (!wide) emit_widen(as, ir->t, gpr, gpr);  /* After the move. */
	ra_leftov(as, gpr, ref);
	gpr++;
      } else {
	Reg r = ra_alloc1(as, ref, RSET_GPR);
	if (wide) {
	  emit_tai(as, PPCI_STD, r, RID_SP, ofs);
	} else {
	  emit_tai(as, PPCI_STD, RID_TMP, RID_SP, ofs);
	  emit_widen(as, ir->t, RID_TMP, r);
	}
	ofs += 8;
      }
    }
    checkmclim(as);
  }
}
#else
/* Generate a call to a C function. */
static void asm_gencall(ASMState *as, const CCallInfo *ci, IRRef *args)
{
  uint32_t n, nargs = CCI_XNARGS(ci);
  int32_t ofs = 8;
  Reg gpr = REGARG_FIRSTGPR;
#if !LJ_SOFTFP
  Reg fpr = REGARG_FIRSTFPR;
#endif
  if ((void *)ci->func)
    emit_call(as, (void *)ci->func);
  for (n = 0; n < nargs; n++) {  /* Setup args. */
    IRRef ref = args[n];
    if (ref) {
      IRIns *ir = IR(ref);
#if !LJ_SOFTFP
      if (irt_isfp(ir->t)) {
	if (fpr <= REGARG_LASTFPR) {
	  lj_assertA(rset_test(as->freeset, fpr),
		     "reg %d not free", fpr);  /* Already evicted. */
	  ra_leftov(as, fpr, ref);
	  fpr++;
	} else {
	  Reg r = ra_alloc1(as, ref, RSET_FPR);
	  if (irt_isnum(ir->t)) ofs = (ofs + 4) & ~4;
	  emit_spstore(as, ir, r, ofs);
	  ofs += irt_isnum(ir->t) ? 8 : 4;
	}
      } else
#endif
      {
	if (gpr <= REGARG_LASTGPR) {
	  lj_assertA(rset_test(as->freeset, gpr),
		     "reg %d not free", gpr);  /* Already evicted. */
	  ra_leftov(as, gpr, ref);
	  gpr++;
	} else {
	  Reg r = ra_alloc1(as, ref, RSET_GPR);
	  emit_spstore(as, ir, r, ofs);
	  ofs += 4;
	}
      }
    } else {
      if (gpr <= REGARG_LASTGPR)
	gpr++;
      else
	ofs += 4;
    }
    checkmclim(as);
  }
#if !LJ_SOFTFP
  if ((ci->flags & CCI_VARARG))  /* Vararg calls need to know about FPR use. */
    emit_tab(as, fpr == REGARG_FIRSTFPR ? PPCI_CRXOR : PPCI_CREQV, 6, 6, 6);
#endif
}
#endif

/* Setup result reg/sp for call. Evict scratch regs. */
static void asm_setupresult(ASMState *as, IRIns *ir, const CCallInfo *ci)
{
  RegSet drop = RSET_SCRATCH;
  int hiop = ((ir+1)->o == IR_HIOP && !irt_isnil((ir+1)->t));
#if !LJ_SOFTFP
  if ((ci->flags & CCI_NOFPRCLOBBER))
    drop &= ~RSET_FPR;
#endif
  if (ra_hasreg(ir->r))
    rset_clear(drop, ir->r);  /* Dest reg handled below. */
  if (hiop && ra_hasreg((ir+1)->r))
    rset_clear(drop, (ir+1)->r);  /* Dest reg handled below. */
  ra_evictset(as, drop);  /* Evictions must be performed first. */
  if (ra_used(ir)) {
    lj_assertA(!irt_ispri(ir->t), "PRI dest");
    if (!LJ_SOFTFP && irt_isfp(ir->t)) {
      if ((ci->flags & CCI_CASTU64)) {
#if LJ_ARCH_PPC64
	/* u64 result in r3 reinterpreted as a double: mtvsrd, no memory. */
	int32_t ofs = sps_scale(ir->s);
	Reg dest = ir->r;
	if (ra_hasreg(dest)) {
	  ra_free(as, dest);
	  ra_modified(as, dest);
	  emit_tab(as, PPCI_MTVSRD, (dest & 31), RID_RET, 0);
	}
	if (ofs)
	  emit_tai(as, PPCI_STD, RID_RET, RID_SP, ofs);
#else
	/* Use spill slot or temp slots. */
	int32_t ofs = ir->s ? sps_scale(ir->s) : SPOFS_TMP;
	Reg dest = ir->r;
	if (ra_hasreg(dest)) {
	  ra_free(as, dest);
	  ra_modified(as, dest);
	  emit_fai(as, PPCI_LFD, dest, RID_SP, ofs);
	}
	emit_tai(as, PPCI_STW, RID_RETHI, RID_SP, ofs);
	emit_tai(as, PPCI_STW, RID_RETLO, RID_SP, ofs+4);
#endif
      } else {
	ra_destreg(as, ir, RID_FPRET);
      }
    } else if (hiop) {
      ra_destpair(as, ir);
    } else {
      ra_destreg(as, ir, RID_RET);
    }
  }
}

static void asm_callx(ASMState *as, IRIns *ir)
{
  IRRef args[CCI_NARGS_MAX*2];
  CCallInfo ci;
  IRRef func;
  IRIns *irf;
  ci.flags = asm_callx_flags(as, ir);
  asm_collectargs(as, ir, &ci, args);
  asm_setupresult(as, ir, &ci);
  func = ir->op2; irf = IR(func);
  if (irf->o == IR_CARG) { func = irf->op1; irf = IR(func); }
  if (irref_isk(func)) {  /* Call to constant address. */
    ci.func = (ASMFunction)(void *)get_kval(as, func);
#if LJ_ARCH_PPC64
  } else {  /* Indirect call: the callee address must be in r12 (D2). */
    Reg r = ra_alloc1(as, func, RID2RSET(RID_CFUNCADDR));
    MCode *p = as->mcp;
    *--p = PPCI_LD | PPCF_T(RID_SYS1) | PPCF_A(RID_SP) | 24;
    *--p = PPCI_BCTRL;
    *--p = PPCI_MTCTR | PPCF_T(RID_CFUNCADDR);
    if (r != RID_CFUNCADDR)  /* Value already lives elsewhere: r12 is scratch. */
      *--p = PPCI_MR | PPCF_T(r) | PPCF_A(RID_CFUNCADDR) | PPCF_B(r);
    as->mcp = p;
    ci.func = (ASMFunction)(void *)0;
  }
#else
  } else {  /* Need a non-argument register for indirect calls. */
    RegSet allow = RSET_GPR & ~RSET_RANGE(RID_R0, REGARG_LASTGPR+1);
    Reg freg = ra_alloc1(as, func, allow);
    *--as->mcp = PPCI_BCTRL;
    *--as->mcp = PPCI_MTCTR | PPCF_T(freg);
    ci.func = (ASMFunction)(void *)0;
  }
#endif
  asm_gencall(as, &ci, args);
}

/* -- Returns ------------------------------------------------------------- */

#if LJ_ARCH_PPC64
static void asm_retf(ASMState *as, IRIns *ir)
{
  Reg base = ra_alloc1(as, REF_BASE, RSET_GPR);
  void *pc = ir_kptr(IR(ir->op2));
  int32_t delta = 1+LJ_FR2+bc_a(*((const BCIns *)pc - 1));
  as->topslot -= (BCReg)delta;
  if ((int32_t)as->topslot < 0) as->topslot = 0;
  irt_setmark(IR(REF_BASE)->t);  /* Children must not coalesce with BASE reg. */
  emit_setgl(as, base, jit_base);
  emit_addptr(as, base, -8*delta);
  asm_guardcc(as, CC_NE);
  emit_ab(as, PPCI_CMPD, RID_TMP,
	  ra_allock(as, (intptr_t)pc, rset_exclude(RSET_GPR, base)));
  emit_tai(as, PPCI_LD, RID_TMP, base, -8);  /* Frame link: FR2 pc slot. */
}
#else
/* Return to lower frame. Guard that it goes to the right spot. */
static void asm_retf(ASMState *as, IRIns *ir)
{
  Reg base = ra_alloc1(as, REF_BASE, RSET_GPR);
  void *pc = ir_kptr(IR(ir->op2));
  int32_t delta = 1+LJ_FR2+bc_a(*((const BCIns *)pc - 1));
  as->topslot -= (BCReg)delta;
  if ((int32_t)as->topslot < 0) as->topslot = 0;
  irt_setmark(IR(REF_BASE)->t);  /* Children must not coalesce with BASE reg. */
  emit_setgl(as, base, jit_base);
  emit_addptr(as, base, -8*delta);
  asm_guardcc(as, CC_NE);
  emit_ab(as, PPCI_CMPW, RID_TMP,
	  ra_allock(as, i32ptr(pc), rset_exclude(RSET_GPR, base)));
  emit_tai(as, PPCI_LWZ, RID_TMP, base, -8);
}
#endif

/* -- Buffer operations --------------------------------------------------- */

#if LJ_HASBUFFER
static void asm_bufhdr_write(ASMState *as, Reg sb)
{
  Reg tmp = ra_scratch(as, rset_exclude(RSET_GPR, sb));
  IRIns irgc;
  irgc.ot = IRT(0, IRT_PGC);  /* GC type. */
  emit_storeofs(as, &irgc, RID_TMP, sb, offsetof(SBuf, L));
  emit_rot(as, PPCI_RLWIMI, RID_TMP, tmp, 0, 31-lj_fls(SBUF_MASK_FLAG), 31);
  emit_getgl(as, RID_TMP, cur_L);
  emit_loadofs(as, &irgc, tmp, sb, offsetof(SBuf, L));
}
#endif

/* -- Type conversions ---------------------------------------------------- */

#if !LJ_SOFTFP
#if LJ_ARCH_PPC64
static void asm_tointg(ASMState *as, IRIns *ir, Reg left)
{
  /* fctiwz t,f; mfvsrwz r,t; mtvsrwa t2,r; fcfid t2,t2; fcmpu t2,f; bne.
  ** A NaN fails the fcmpu (unordered clears EQ); an out-of-range value
  ** saturates and cannot round-trip; -0.0 does round-trip (as lj_num2int).
  */
  RegSet allow = RSET_FPR;
  Reg tmp = ra_scratch(as, rset_clear(allow, left));
  Reg tmp2 = ra_scratch(as, rset_clear(allow, tmp));
  Reg dest = ra_dest(as, ir, RSET_GPR);
  asm_guardcc(as, CC_NE);
  emit_fab(as, PPCI_FCMPU, 0, tmp2, left);
  emit_fb(as, PPCI_FCFID, tmp2, tmp2);
  emit_mtvsrwa(as, tmp2, dest);
  emit_mfvsrwz(as, dest, tmp);
  emit_fb(as, PPCI_FCTIWZ, tmp, left);
}
#else
static void asm_tointg(ASMState *as, IRIns *ir, Reg left)
{
  RegSet allow = RSET_FPR;
  Reg tmp = ra_scratch(as, rset_clear(allow, left));
  Reg fbias = ra_scratch(as, rset_clear(allow, tmp));
  Reg dest = ra_dest(as, ir, RSET_GPR);
  Reg hibias = ra_allock(as, 0x43300000, rset_exclude(RSET_GPR, dest));
  asm_guardcc(as, CC_NE);
  emit_fab(as, PPCI_FCMPU, 0, tmp, left);
  emit_fab(as, PPCI_FSUB, tmp, tmp, fbias);
  emit_fai(as, PPCI_LFD, tmp, RID_SP, SPOFS_TMP);
  emit_tai(as, PPCI_STW, RID_TMP, RID_SP, SPOFS_TMPLO);
  emit_tai(as, PPCI_STW, hibias, RID_SP, SPOFS_TMPHI);
  emit_asi(as, PPCI_XORIS, RID_TMP, dest, 0x8000);
  emit_tai(as, PPCI_LWZ, dest, RID_SP, SPOFS_TMPLO);
  emit_lsptr(as, PPCI_LFS, (fbias & 31),
	     (void *)&as->J->k32[LJ_K32_2P52_2P31], RSET_GPR);
  emit_fai(as, PPCI_STFD, tmp, RID_SP, SPOFS_TMP);
  emit_fb(as, PPCI_FCTIWZ, tmp, left);
}
#endif

#if LJ_ARCH_PPC64
static void asm_tobit(ASMState *as, IRIns *ir)
{
  RegSet allow = RSET_FPR;
  Reg dest = ra_dest(as, ir, RSET_GPR);
  Reg left = ra_alloc1(as, ir->op1, allow);
  Reg right = ra_alloc1(as, ir->op2, rset_clear(allow, left));
  Reg tmp = ra_scratch(as, rset_clear(allow, right));
  emit_mfvsrwz(as, dest, tmp);
  emit_fab(as, PPCI_FADD, tmp, left, right);
}
#else
static void asm_tobit(ASMState *as, IRIns *ir)
{
  RegSet allow = RSET_FPR;
  Reg dest = ra_dest(as, ir, RSET_GPR);
  Reg left = ra_alloc1(as, ir->op1, allow);
  Reg right = ra_alloc1(as, ir->op2, rset_clear(allow, left));
  Reg tmp = ra_scratch(as, rset_clear(allow, right));
  emit_tai(as, PPCI_LWZ, dest, RID_SP, SPOFS_TMPLO);
  emit_fai(as, PPCI_STFD, tmp, RID_SP, SPOFS_TMP);
  emit_fab(as, PPCI_FADD, tmp, left, right);
}
#endif
#endif

#if LJ_ARCH_PPC64
static void asm_conv(ASMState *as, IRIns *ir)
{
  IRType st = (IRType)(ir->op2 & IRCONV_SRCMASK);
  int stfp = (st == IRT_NUM || st == IRT_FLOAT);
  int st64 = (st == IRT_I64 || st == IRT_U64 || st == IRT_P64);
  IRRef lref = ir->op1;
  lj_assertA(irt_type(ir->t) != st, "inconsistent types for CONV");
  if (irt_isfp(ir->t)) {
    Reg dest = ra_dest(as, ir, RSET_FPR);
    if (stfp) {  /* FP to FP conversion. */
      if (st == IRT_NUM)  /* double -> float conversion. */
	emit_fb(as, PPCI_FRSP, dest, ra_alloc1(as, lref, RSET_FPR));
      else  /* float -> double conversion is a no-op on PPC. */
	ra_leftov(as, dest, lref);  /* Do nothing, but may need to move regs. */
    } else {  /* Integer to FP conversion (no memory temps: mtvsr + fcfid). */
      Reg left = ra_alloc1(as, lref, RSET_GPR);
      if (irt_isfloat(ir->t)) emit_fb(as, PPCI_FRSP, dest, dest);
      if (st64) {
	emit_fb(as, st == IRT_U64 ? PPCI_FCFIDU : PPCI_FCFID, dest, dest);
	emit_mtvsrd(as, dest, left);
      } else {
	/* mtvsrwa/wz extend the low word, so upper-half garbage (D3) is
	** irrelevant here.
	*/
	emit_fb(as, PPCI_FCFID, dest, dest);
	if (st == IRT_U32)
	  emit_mtvsrwz(as, dest, left);
	else
	  emit_mtvsrwa(as, dest, left);
      }
    }
  } else if (stfp) {  /* FP to integer conversion. */
    if (irt_isguard(ir->t)) {
      /* Checked conversions are only supported from number to int. */
      lj_assertA(irt_isint(ir->t) && st == IRT_NUM,
		 "bad type for checked CONV");
      asm_tointg(as, ir, ra_alloc1(as, lref, RSET_FPR));
    } else {
      Reg dest = ra_dest(as, ir, RSET_GPR);
      Reg left = ra_alloc1(as, lref, RSET_FPR);
      Reg tmp = ra_scratch(as, rset_exclude(RSET_FPR, left));
      if (irt_isu64(ir->t)) {
	/* num -> u64 as ->vm_num2u64 and x64 do it: the signed truncation
	** (fctidz) unless it saturated to INT64_MAX (x >= 2^63), then the
	** unsigned one. Negative inputs wrap, NaN gives 2^63; a plain
	** fctiduz (arm64's fcvtzu) gives 0 for both and disagrees with the
	** interpreter of this port. The C cast is undefined for these.
	*/
	Reg gtmp = ra_scratch(as, rset_exclude(RSET_GPR, dest));
	emit_isel(as, dest, gtmp, dest, 4*PPC_CRF_CMP + (CC_EQ & 3));
	emit_tab(as, PPCI_CMPD, PPC_CRF_CMP, dest, RID_TMP);
	emit_clrldi(as, RID_TMP, RID_TMP, 1);  /* r0 = INT64_MAX */
	emit_ti(as, PPCI_LI, RID_TMP, -1);
	emit_mfvsrd(as, gtmp, tmp);
	emit_fb(as, PPCI_FCTIDUZ, tmp, left);
	emit_mfvsrd(as, dest, tmp);
	emit_fb(as, PPCI_FCTIDZ, tmp, left);
      } else if (irt_isi64(ir->t)) {
	emit_mfvsrd(as, dest, tmp);
	emit_fb(as, PPCI_FCTIDZ, tmp, left);
      } else if (irt_isu32(ir->t)) {
	/* u32 = low word of the truncated int64 (wraps like x64/mips64). */
	emit_mfvsrwz(as, dest, tmp);
	emit_fb(as, PPCI_FCTIDZ, tmp, left);
      } else {
	emit_mfvsrwz(as, dest, tmp);
	emit_fb(as, PPCI_FCTIWZ, tmp, left);
      }
    }
  } else {
    Reg dest = ra_dest(as, ir, RSET_GPR);
    if (st >= IRT_I8 && st <= IRT_U16) {  /* Extend to 32 bit integer. */
      Reg left = ra_alloc1(as, ir->op1, RSET_GPR);
      lj_assertA(irt_isint(ir->t) || irt_isu32(ir->t), "bad type for CONV EXT");
      if ((ir->op2 & IRCONV_SEXT))
	emit_as(as, st == IRT_I8 ? PPCI_EXTSB : PPCI_EXTSH, dest, left);
      else
	emit_rot(as, PPCI_RLWINM, dest, left, 0, st == IRT_U8 ? 24 : 16, 31);
    } else if (irt_is64(ir->t) && !st64) {
      /* 32 to 64 bit: the D3 widening site. Sign or zero per the source. */
      Reg left = ra_alloc1(as, lref, RSET_GPR);
      if ((ir->op2 & IRCONV_SEXT))
	emit_extsw(as, dest, left);
      else
	emit_zextw(as, dest, left);
    } else {  /* 64/64 bit or 64 to 32 bit: no-op (cast). */
      ra_leftov(as, dest, lref);  /* Do nothing, but may need to move regs. */
    }
  }
}
#else
static void asm_conv(ASMState *as, IRIns *ir)
{
  IRType st = (IRType)(ir->op2 & IRCONV_SRCMASK);
#if !LJ_SOFTFP
  int stfp = (st == IRT_NUM || st == IRT_FLOAT);
#endif
  IRRef lref = ir->op1;
  /* 64 bit integer conversions are handled by SPLIT. */
  lj_assertA(!(irt_isint64(ir->t) || (st == IRT_I64 || st == IRT_U64)),
	     "IR %04d has unsplit 64 bit type",
	     (int)(ir - as->ir) - REF_BIAS);
#if LJ_SOFTFP
  /* FP conversions are handled by SPLIT. */
  lj_assertA(!irt_isfp(ir->t) && !(st == IRT_NUM || st == IRT_FLOAT),
	     "IR %04d has FP type",
	     (int)(ir - as->ir) - REF_BIAS);
  /* Can't check for same types: SPLIT uses CONV int.int + BXOR for sfp NEG. */
#else
  lj_assertA(irt_type(ir->t) != st, "inconsistent types for CONV");
  if (irt_isfp(ir->t)) {
    Reg dest = ra_dest(as, ir, RSET_FPR);
    if (stfp) {  /* FP to FP conversion. */
      if (st == IRT_NUM)  /* double -> float conversion. */
	emit_fb(as, PPCI_FRSP, dest, ra_alloc1(as, lref, RSET_FPR));
      else  /* float -> double conversion is a no-op on PPC. */
	ra_leftov(as, dest, lref);  /* Do nothing, but may need to move regs. */
    } else {  /* Integer to FP conversion. */
      /* IRT_INT: Flip hibit, bias with 2^52, subtract 2^52+2^31. */
      /* IRT_U32: Bias with 2^52, subtract 2^52. */
      RegSet allow = RSET_GPR;
      Reg left = ra_alloc1(as, lref, allow);
      Reg hibias = ra_allock(as, 0x43300000, rset_clear(allow, left));
      Reg fbias = ra_scratch(as, rset_exclude(RSET_FPR, dest));
      if (irt_isfloat(ir->t)) emit_fb(as, PPCI_FRSP, dest, dest);
      emit_fab(as, PPCI_FSUB, dest, dest, fbias);
      emit_fai(as, PPCI_LFD, dest, RID_SP, SPOFS_TMP);
      emit_lsptr(as, PPCI_LFS, (fbias & 31),
		 &as->J->k32[st == IRT_U32 ? LJ_K32_2P52 : LJ_K32_2P52_2P31],
		 rset_clear(allow, hibias));
      emit_tai(as, PPCI_STW, st == IRT_U32 ? left : RID_TMP,
	       RID_SP, SPOFS_TMPLO);
      emit_tai(as, PPCI_STW, hibias, RID_SP, SPOFS_TMPHI);
      if (st != IRT_U32) emit_asi(as, PPCI_XORIS, RID_TMP, left, 0x8000);
    }
  } else if (stfp) {  /* FP to integer conversion. */
    if (irt_isguard(ir->t)) {
      /* Checked conversions are only supported from number to int. */
      lj_assertA(irt_isint(ir->t) && st == IRT_NUM,
		 "bad type for checked CONV");
      asm_tointg(as, ir, ra_alloc1(as, lref, RSET_FPR));
    } else {
      Reg dest = ra_dest(as, ir, RSET_GPR);
      Reg left = ra_alloc1(as, lref, RSET_FPR);
      Reg tmp = ra_scratch(as, rset_exclude(RSET_FPR, left));
      lj_assertA(!irt_isu32(ir->t), "bad CONV u32.fp emitted");
      emit_tai(as, PPCI_LWZ, dest, RID_SP, SPOFS_TMPLO);
      emit_fai(as, PPCI_STFD, tmp, RID_SP, SPOFS_TMP);
      emit_fb(as, PPCI_FCTIWZ, tmp, left);
    }
  } else
#endif
  {
    Reg dest = ra_dest(as, ir, RSET_GPR);
    if (st >= IRT_I8 && st <= IRT_U16) {  /* Extend to 32 bit integer. */
      Reg left = ra_alloc1(as, ir->op1, RSET_GPR);
      lj_assertA(irt_isint(ir->t) || irt_isu32(ir->t), "bad type for CONV EXT");
      if ((ir->op2 & IRCONV_SEXT))
	emit_as(as, st == IRT_I8 ? PPCI_EXTSB : PPCI_EXTSH, dest, left);
      else
	emit_rot(as, PPCI_RLWINM, dest, left, 0, st == IRT_U8 ? 24 : 16, 31);
    } else {  /* 32/64 bit integer conversions. */
      /* Only need to handle 32/32 bit no-op (cast) on 32 bit archs. */
      ra_leftov(as, dest, lref);  /* Do nothing, but may need to move regs. */
    }
  }
}
#endif

static void asm_strto(ASMState *as, IRIns *ir)
{
  const CCallInfo *ci = &lj_ir_callinfo[IRCALL_lj_strscan_num];
  IRRef args[2];
  int32_t ofs = SPOFS_TMP;
#if LJ_SOFTFP
  ra_evictset(as, RSET_SCRATCH);
  if (ra_used(ir)) {
    if (ra_hasspill(ir->s) && ra_hasspill((ir+1)->s) &&
	(ir->s & 1) == LJ_BE && (ir->s ^ 1) == (ir+1)->s) {
      int i;
      for (i = 0; i < 2; i++) {
	Reg r = (ir+i)->r;
	if (ra_hasreg(r)) {
	  ra_free(as, r);
	  ra_modified(as, r);
	  emit_spload(as, ir+i, r, sps_scale((ir+i)->s));
	}
      }
      ofs = sps_scale(ir->s & ~1);
    } else {
      Reg rhi = ra_dest(as, ir+1, RSET_GPR);
      Reg rlo = ra_dest(as, ir, rset_exclude(RSET_GPR, rhi));
      emit_tai(as, PPCI_LWZ, rhi, RID_SP, ofs);
      emit_tai(as, PPCI_LWZ, rlo, RID_SP, ofs+4);
    }
  }
#else
  RegSet drop = RSET_SCRATCH;
  if (ra_hasreg(ir->r)) rset_set(drop, ir->r);  /* Spill dest reg (if any). */
  ra_evictset(as, drop);
  if (ir->s) ofs = sps_scale(ir->s);
#endif
  asm_guardcc(as, CC_EQ);
  emit_ai(as, PPCI_CMPWI, RID_RET, 0);  /* Test return status. */
  args[0] = ir->op1;      /* GCstr *str */
  args[1] = ASMREF_TMP1;  /* TValue *n  */
  asm_gencall(as, ci, args);
  /* Store the result to the spill slot or temp slots. */
  emit_tai(as, PPCI_ADDI, ra_releasetmp(as, ASMREF_TMP1), RID_SP, ofs);
}

/* -- Memory references --------------------------------------------------- */

#if LJ_ARCH_PPC64
/* Store the tagged 64-bit TValue for ref at base+ofs. */
static void asm_tvstore64(ASMState *as, Reg base, int32_t ofs, IRRef ref)
{
  RegSet allow = rset_exclude(RSET_GPR, base);
  IRIns *ir = IR(ref);
  lj_assertA(irt_ispri(ir->t) || irt_isaddr(ir->t) || irt_isinteger(ir->t),
	     "store of IR type %d", irt_type(ir->t));
  if (irref_isk(ref)) {
    TValue k;
    lj_ir_kvalue(as->J->L, &k, ir);
    emit_tai(as, PPCI_STD, ra_allock(as, (intptr_t)k.u64, allow), base, ofs);
  } else {
    Reg src = ra_alloc1(as, ref, allow);
    Reg type = ra_allock(as, (intptr_t)tvtag64(ir->t),
			 rset_exclude(allow, src));
    emit_tai(as, PPCI_STD, RID_TMP, base, ofs);
    if (irt_isinteger(ir->t)) {
      /* |1..1|itype|0..0|int|: the upper half of src is garbage (D3). */
      emit_asb(as, PPCI_OR, RID_TMP, RID_TMP, type);
      emit_zextw(as, RID_TMP, src);
    } else {
      emit_asb(as, PPCI_OR, RID_TMP, src, type);  /* ptr < 2^47: or == add. */
    }
  }
}
#endif
#if LJ_ARCH_PPC64
static void asm_tvptr(ASMState *as, Reg dest, IRRef ref, MSize mode)
{
  int32_t tmpofs = (int32_t)(offsetof(global_State, tmptv)-32768);
  if ((mode & IRTMPREF_IN1)) {
    IRIns *ir = IR(ref);
    if (irt_isnum(ir->t)) {
      if ((mode & IRTMPREF_OUT1)) {
	Reg src = ra_alloc1(as, ref, RSET_FPR);
	emit_tai(as, PPCI_ADDI, dest, RID_JGL, tmpofs);
	emit_fai(as, PPCI_STFD, src, RID_JGL, tmpofs);
      } else if (irref_isk(ref)) {
	/* Use the number constant itself as a TValue. */
	ra_allockreg(as, (intptr_t)ir_knum(ir), dest);
      } else {
	/* Otherwise force a spill and use the spill slot. */
	emit_tai(as, PPCI_ADDI, dest, RID_SP, ra_spill(as, ir));
      }
    } else {
      /* Otherwise use g->tmptv to hold the TValue. */
      asm_tvstore64(as, dest, 0, ref);
      emit_tai(as, PPCI_ADDI, dest, RID_JGL, tmpofs);
    }
  } else {
    emit_tai(as, PPCI_ADDI, dest, RID_JGL, tmpofs);
  }
}
#else
/* Get pointer to TValue. */
static void asm_tvptr(ASMState *as, Reg dest, IRRef ref, MSize mode)
{
  int32_t tmpofs = (int32_t)(offsetof(global_State, tmptv)-32768);
  if ((mode & IRTMPREF_IN1)) {
    IRIns *ir = IR(ref);
    if (irt_isnum(ir->t)) {
      if ((mode & IRTMPREF_OUT1)) {
#if LJ_SOFTFP
	lj_assertA(irref_isk(ref), "unsplit FP op");
	emit_tai(as, PPCI_ADDI, dest, RID_JGL, tmpofs);
	emit_setgl(as,
		   ra_allock(as, (int32_t)ir_knum(ir)->u32.lo, RSET_GPR),
		   tmptv.u32.lo);
	emit_setgl(as,
		   ra_allock(as, (int32_t)ir_knum(ir)->u32.hi, RSET_GPR),
		   tmptv.u32.hi);
#else
	Reg src = ra_alloc1(as, ref, RSET_FPR);
	emit_tai(as, PPCI_ADDI, dest, RID_JGL, tmpofs);
	emit_fai(as, PPCI_STFD, src, RID_JGL, tmpofs);
#endif
      } else if (irref_isk(ref)) {
	/* Use the number constant itself as a TValue. */
	ra_allockreg(as, i32ptr(ir_knum(ir)), dest);
      } else {
#if LJ_SOFTFP
	lj_assertA(0, "unsplit FP op");
#else
	/* Otherwise force a spill and use the spill slot. */
	emit_tai(as, PPCI_ADDI, dest, RID_SP, ra_spill(as, ir));
#endif
      }
    } else {
      /* Otherwise use g->tmptv to hold the TValue. */
      Reg type;
      emit_tai(as, PPCI_ADDI, dest, RID_JGL, tmpofs);
      if (!irt_ispri(ir->t)) {
	Reg src = ra_alloc1(as, ref, RSET_GPR);
	emit_setgl(as, src, tmptv.gcr);
      }
      if (LJ_SOFTFP && (ir+1)->o == IR_HIOP && !irt_isnil((ir+1)->t))
	type = ra_alloc1(as, ref+1, RSET_GPR);
      else
	type = ra_allock(as, irt_toitype(ir->t), RSET_GPR);
      emit_setgl(as, type, tmptv.it);
    }
  } else {
    emit_tai(as, PPCI_ADDI, dest, RID_JGL, tmpofs);
  }
}
#endif

static void asm_aref(ASMState *as, IRIns *ir)
{
  Reg dest = ra_dest(as, ir, RSET_GPR);
  Reg idx, base;
  if (irref_isk(ir->op2)) {
    IRRef tab = IR(ir->op1)->op1;
    int32_t ofs = asm_fuseabase(as, tab);
    IRRef refa = ofs ? tab : ir->op1;
    ofs += 8*IR(ir->op2)->i;
    if (checki16(ofs)) {
      base = ra_alloc1(as, refa, RSET_GPR);
      emit_tai(as, PPCI_ADDI, dest, base, ofs);
      return;
    }
  }
  base = ra_alloc1(as, ir->op1, RSET_GPR);
  idx = ra_alloc1(as, ir->op2, rset_exclude(RSET_GPR, base));
  emit_tab(as, PPCI_ADD, dest, RID_TMP, base);
  emit_slwi(as, RID_TMP, idx, 3);
}

#if LJ_ARCH_PPC64
/* Inlined hash lookup. Specialized for key type and for const keys.
** The equivalent C code is:
**   Node *n = hashkey(t, key);
**   do {
**     if (lj_obj_equal(&n->key, key)) return &n->val;
**   } while ((n = nextnode(n)));
**   return niltv(L);
** GC64: one ld + one cmpd per chain step against the tagged 64-bit key;
** the hash of a non-constant key is hashrot(lo32, hi32) of the tagged
** word (lj_tab.h hashgcref / hashnum), so the tag is built before hashing.
*/
static void asm_href(ASMState *as, IRIns *ir, IROp merge)
{
  RegSet allow = RSET_GPR;
  int destused = ra_used(ir);
  Reg dest = ra_dest(as, ir, allow);
  Reg tab = ra_alloc1(as, ir->op1, rset_clear(allow, dest));
  Reg key = RID_NONE, tmp1 = RID_TMP, tmp2, cmp64 = RID_NONE;
  Reg tisnum = RID_NONE, tmpnum = RID_NONE;
  IRRef refkey = ir->op2;
  IRIns *irkey = IR(refkey);
  int isk = irref_isk(refkey);
  IRType1 kt = irkey->t;
  uint32_t khash;
  MCLabel l_end, l_loop, l_next;

  rset_clear(allow, tab);
  if (irt_isnum(kt)) {
    key = ra_alloc1(as, refkey, RSET_FPR);
    tmpnum = ra_scratch(as, rset_exclude(RSET_FPR, key));
    tisnum = ra_allock(as, tvtisnum, allow);
    rset_clear(allow, tisnum);
  } else if (!irt_ispri(kt)) {
    key = ra_alloc1(as, refkey, allow);
    rset_clear(allow, key);
  }
  tmp2 = ra_scratch(as, allow);
  rset_clear(allow, tmp2);
  if (!irt_isnum(kt)) {
    /* The tagged 64-bit word the chain keys are compared against. */
    if (!isk && irt_isaddr(kt)) {
      cmp64 = tmp2;  /* Built below the loop: key | itype<<47. */
    } else {
      int64_t k;
      if (isk && irt_isaddr(kt)) {
	k = tvtag64(kt) | (int64_t)get_kval(as, refkey);
      } else {
	lj_assertA(irt_ispri(kt) && !irt_isnil(kt), "bad HREF key type");
	k = tvpri64(kt);
      }
      cmp64 = ra_allock(as, (intptr_t)k, allow);
      rset_clear(allow, cmp64);
    }
  }

  /* Key not found in chain: jump to exit (if merged) or load niltv. */
  l_end = emit_label(as);
  as->invmcp = NULL;
  if (merge == IR_NE)
    asm_guardcc(as, CC_EQ);
  else if (destused)
    emit_loada(as, dest, niltvg(J2G(as->J)));

  /* Follow hash chain until the end. */
  l_loop = --as->mcp;
  emit_ai(as, PPCI_CMPDI, dest, 0);
  emit_tai(as, PPCI_LD, dest, dest, (int32_t)offsetof(Node, next));
  l_next = emit_label(as);

  /* Type and value comparison. */
  if (merge == IR_EQ)
    asm_guardcc(as, CC_EQ);
  else
    emit_condbranch(as, PPCI_BC|PPCF_Y, CC_EQ, l_end);
  if (irt_isnum(kt)) {
    emit_fab(as, PPCI_FCMPU, 0, tmpnum, key);
    emit_condbranch(as, PPCI_BC, CC_GE, l_next);  /* Not a number: next. */
    emit_ab(as, PPCI_CMPLD, tmp1, tisnum);
    emit_tag(as, tmp1, tmp1);
    emit_mtvsrd(as, tmpnum, tmp1);
  } else {
    emit_ab(as, PPCI_CMPD, tmp1, cmp64);
  }
  emit_tai(as, PPCI_LD, tmp1, dest, (int32_t)offsetof(Node, key.u64));
  *l_loop = PPCI_BC | PPCF_Y | PPCF_CC(CC_NE) |
	    (((char *)as->mcp-(char *)l_loop) & 0xffffu);
  if (!isk && irt_isaddr(kt)) {
    Reg type = ra_allock(as, (intptr_t)tvtag64(kt), allow);
    emit_asb(as, PPCI_OR, tmp2, key, type);
    rset_clear(allow, type);
  }

  /* Load main position relative to tab->node into dest. */
  khash = isk ? ir_khash(as, irkey) : 1;
  if (khash == 0) {
    emit_tai(as, PPCI_LD, dest, tab, (int32_t)offsetof(GCtab, node));
  } else {
    Reg tmphash = tmp1;
    if (isk)
      tmphash = ra_allock(as, (int32_t)khash, allow);
    emit_tab(as, PPCI_ADD, dest, dest, tmp1);
    emit_tai(as, PPCI_MULLI, tmp1, tmp1, sizeof(Node));
    emit_asb(as, PPCI_AND, tmp1, tmp2, tmphash);  /* hmask is clean: so is this. */
    emit_tai(as, PPCI_LD, dest, tab, (int32_t)offsetof(GCtab, node));
    emit_tai(as, PPCI_LWZ, tmp2, tab, (int32_t)offsetof(GCtab, hmask));
    if (isk) {
      /* Nothing to do. */
    } else if (irt_isstr(kt)) {
      emit_tai(as, PPCI_LWZ, tmp1, key, (int32_t)offsetof(GCstr, sid));
    } else {  /* Must match with hashrot() in lj_tab.h: lo in tmp2, hi in tmp1. */
      emit_tab(as, PPCI_SUBF, tmp1, tmp2, tmp1);
      emit_rotlwi(as, tmp2, tmp2, HASH_ROT3);
      emit_asb(as, PPCI_XOR, tmp1, tmp1, tmp2);
      emit_rotlwi(as, tmp1, tmp1, (HASH_ROT2+HASH_ROT1)&31);
      emit_tab(as, PPCI_SUBF, tmp2, dest, tmp2);
      emit_asb(as, PPCI_XOR, tmp2, tmp2, tmp1);
      emit_rotlwi(as, dest, tmp1, HASH_ROT1);
      if (irt_isnum(kt)) {
	/* hashnum: lo = u32.lo, hi = u32.hi << 1. */
	emit_tab(as, PPCI_ADD, tmp1, tmp1, tmp1);
	emit_srdi(as, tmp1, tmp2, 32);
	emit_mfvsrd(as, tmp2, key);
      } else {
	/* hashgcref (GC64): lo/hi words of the tagged key. */
	Reg type = ra_allock(as, (intptr_t)tvtag64(kt), allow);
	emit_srdi(as, tmp1, tmp2, 32);
	emit_asb(as, PPCI_OR, tmp2, key, type);
      }
    }
  }
  checkmclim(as);
}
#else
/* Inlined hash lookup. Specialized for key type and for const keys.
** The equivalent C code is:
**   Node *n = hashkey(t, key);
**   do {
**     if (lj_obj_equal(&n->key, key)) return &n->val;
**   } while ((n = nextnode(n)));
**   return niltv(L);
*/
static void asm_href(ASMState *as, IRIns *ir, IROp merge)
{
  RegSet allow = RSET_GPR;
  int destused = ra_used(ir);
  Reg dest = ra_dest(as, ir, allow);
  Reg tab = ra_alloc1(as, ir->op1, rset_clear(allow, dest));
  Reg key = RID_NONE, tmp1 = RID_TMP, tmp2;
  Reg tisnum = RID_NONE, tmpnum = RID_NONE;
  IRRef refkey = ir->op2;
  IRIns *irkey = IR(refkey);
  int isk = irref_isk(refkey);
  IRType1 kt = irkey->t;
  uint32_t khash;
  MCLabel l_end, l_loop, l_next;

  rset_clear(allow, tab);
#if LJ_SOFTFP
  if (!isk) {
    key = ra_alloc1(as, refkey, allow);
    rset_clear(allow, key);
    if (irkey[1].o == IR_HIOP) {
      if (ra_hasreg((irkey+1)->r)) {
	tmpnum = (irkey+1)->r;
	ra_noweak(as, tmpnum);
      } else {
	tmpnum = ra_allocref(as, refkey+1, allow);
      }
      rset_clear(allow, tmpnum);
    }
  }
#else
  if (irt_isnum(kt)) {
    key = ra_alloc1(as, refkey, RSET_FPR);
    tmpnum = ra_scratch(as, rset_exclude(RSET_FPR, key));
    tisnum = ra_allock(as, (int32_t)LJ_TISNUM, allow);
    rset_clear(allow, tisnum);
  } else if (!irt_ispri(kt)) {
    key = ra_alloc1(as, refkey, allow);
    rset_clear(allow, key);
  }
#endif
  tmp2 = ra_scratch(as, allow);
  rset_clear(allow, tmp2);

  /* Key not found in chain: jump to exit (if merged) or load niltv. */
  l_end = emit_label(as);
  as->invmcp = NULL;
  if (merge == IR_NE)
    asm_guardcc(as, CC_EQ);
  else if (destused)
    emit_loada(as, dest, niltvg(J2G(as->J)));

  /* Follow hash chain until the end. */
  l_loop = --as->mcp;
  emit_ai(as, PPCI_CMPWI, dest, 0);
  emit_tai(as, PPCI_LWZ, dest, dest, (int32_t)offsetof(Node, next));
  l_next = emit_label(as);

  /* Type and value comparison. */
  if (merge == IR_EQ)
    asm_guardcc(as, CC_EQ);
  else
    emit_condbranch(as, PPCI_BC|PPCF_Y, CC_EQ, l_end);
  if (!LJ_SOFTFP && irt_isnum(kt)) {
    emit_fab(as, PPCI_FCMPU, 0, tmpnum, key);
    emit_condbranch(as, PPCI_BC, CC_GE, l_next);
    emit_ab(as, PPCI_CMPLW, tmp1, tisnum);
    emit_fai(as, PPCI_LFD, tmpnum, dest, (int32_t)offsetof(Node, key.n));
  } else {
    if (!irt_ispri(kt)) {
      emit_ab(as, PPCI_CMPW, tmp2, key);
      emit_condbranch(as, PPCI_BC, CC_NE, l_next);
    }
    if (LJ_SOFTFP && ra_hasreg(tmpnum))
      emit_ab(as, PPCI_CMPW, tmp1, tmpnum);
    else
      emit_ai(as, PPCI_CMPWI, tmp1, irt_toitype(irkey->t));
    if (!irt_ispri(kt))
      emit_tai(as, PPCI_LWZ, tmp2, dest, (int32_t)offsetof(Node, key.gcr));
  }
  emit_tai(as, PPCI_LWZ, tmp1, dest, (int32_t)offsetof(Node, key.it));
  *l_loop = PPCI_BC | PPCF_Y | PPCF_CC(CC_NE) |
	    (((char *)as->mcp-(char *)l_loop) & 0xffffu);

  /* Load main position relative to tab->node into dest. */
  khash = isk ? ir_khash(as, irkey) : 1;
  if (khash == 0) {
    emit_tai(as, PPCI_LWZ, dest, tab, (int32_t)offsetof(GCtab, node));
  } else {
    Reg tmphash = tmp1;
    if (isk)
      tmphash = ra_allock(as, khash, allow);
    emit_tab(as, PPCI_ADD, dest, dest, tmp1);
    emit_tai(as, PPCI_MULLI, tmp1, tmp1, sizeof(Node));
    emit_asb(as, PPCI_AND, tmp1, tmp2, tmphash);
    emit_tai(as, PPCI_LWZ, dest, tab, (int32_t)offsetof(GCtab, node));
    emit_tai(as, PPCI_LWZ, tmp2, tab, (int32_t)offsetof(GCtab, hmask));
    if (isk) {
      /* Nothing to do. */
    } else if (irt_isstr(kt)) {
      emit_tai(as, PPCI_LWZ, tmp1, key, (int32_t)offsetof(GCstr, sid));
    } else {  /* Must match with hash*() in lj_tab.c. */
      emit_tab(as, PPCI_SUBF, tmp1, tmp2, tmp1);
      emit_rotlwi(as, tmp2, tmp2, HASH_ROT3);
      emit_asb(as, PPCI_XOR, tmp1, tmp1, tmp2);
      emit_rotlwi(as, tmp1, tmp1, (HASH_ROT2+HASH_ROT1)&31);
      emit_tab(as, PPCI_SUBF, tmp2, dest, tmp2);
      if (LJ_SOFTFP ? (irkey[1].o == IR_HIOP) : irt_isnum(kt)) {
#if LJ_SOFTFP
	emit_asb(as, PPCI_XOR, tmp2, key, tmp1);
	emit_rotlwi(as, dest, tmp1, HASH_ROT1);
	emit_tab(as, PPCI_ADD, tmp1, tmpnum, tmpnum);
#else
	int32_t ofs = ra_spill(as, irkey);
	emit_asb(as, PPCI_XOR, tmp2, tmp2, tmp1);
	emit_rotlwi(as, dest, tmp1, HASH_ROT1);
	emit_tab(as, PPCI_ADD, tmp1, tmp1, tmp1);
	emit_tai(as, PPCI_LWZ, tmp2, RID_SP, ofs+4);
	emit_tai(as, PPCI_LWZ, tmp1, RID_SP, ofs);
#endif
      } else {
	emit_asb(as, PPCI_XOR, tmp2, key, tmp1);
	emit_rotlwi(as, dest, tmp1, HASH_ROT1);
	emit_tai(as, PPCI_ADDI, tmp1, tmp2, HASH_BIAS);
	emit_tai(as, PPCI_ADDIS, tmp2, key, (HASH_BIAS + 32768)>>16);
      }
    }
  }
}
#endif

#if LJ_ARCH_PPC64
static void asm_hrefk(ASMState *as, IRIns *ir)
{
  IRIns *kslot = IR(ir->op2);
  IRIns *irkey = IR(kslot->op1);
  int32_t ofs = (int32_t)(kslot->op2 * sizeof(Node));
  int32_t kofs = ofs + (int32_t)offsetof(Node, key);
  Reg dest = (ra_used(ir)||ofs > 32736) ? ra_dest(as, ir, RSET_GPR) : RID_NONE;
  Reg node = ra_alloc1(as, ir->op1, RSET_GPR);
  RegSet allow = rset_exclude(RSET_GPR, node);
  Reg key, idx = node;
  int64_t k;
  lj_assertA(ofs % sizeof(Node) == 0, "unaligned HREFK slot");
  if (ofs > 32736) {
    idx = dest;
    rset_clear(allow, dest);
    kofs = (int32_t)offsetof(Node, key);
  } else if (ra_hasreg(dest)) {
    emit_tai(as, PPCI_ADDI, dest, node, ofs);
  }
  key = ra_scratch(as, allow);
  rset_clear(allow, key);
  if (irt_ispri(irkey->t)) {
    lj_assertA(!irt_isnil(irkey->t), "bad HREFK key type");
    k = tvpri64(irkey->t);
  } else if (irt_isnum(irkey->t)) {
    k = (int64_t)ir_knum(irkey)->u64;
  } else {
    k = tvtag64(irkey->t) | (int64_t)get_kval(as, kslot->op1);
  }
  /* One ld + one cmpd against the whole tagged key. */
  asm_guardcc(as, CC_NE);
  emit_ab(as, PPCI_CMPD, key, ra_allock(as, (intptr_t)k, allow));
  emit_tai(as, PPCI_LD, key, idx, kofs);
  if (ofs > 32736) {
    emit_tai(as, PPCI_ADDIS, dest, dest, (ofs + 32768) >> 16);
    emit_tai(as, PPCI_ADDI, dest, node, ofs);
  }
}
#else
static void asm_hrefk(ASMState *as, IRIns *ir)
{
  IRIns *kslot = IR(ir->op2);
  IRIns *irkey = IR(kslot->op1);
  int32_t ofs = (int32_t)(kslot->op2 * sizeof(Node));
  int32_t kofs = ofs + (int32_t)offsetof(Node, key);
  Reg dest = (ra_used(ir)||ofs > 32736) ? ra_dest(as, ir, RSET_GPR) : RID_NONE;
  Reg node = ra_alloc1(as, ir->op1, RSET_GPR);
  Reg key = RID_NONE, type = RID_TMP, idx = node;
  RegSet allow = rset_exclude(RSET_GPR, node);
  lj_assertA(ofs % sizeof(Node) == 0, "unaligned HREFK slot");
  if (ofs > 32736) {
    idx = dest;
    rset_clear(allow, dest);
    kofs = (int32_t)offsetof(Node, key);
  } else if (ra_hasreg(dest)) {
    emit_tai(as, PPCI_ADDI, dest, node, ofs);
  }
  asm_guardcc(as, CC_NE);
  if (!irt_ispri(irkey->t)) {
    key = ra_scratch(as, allow);
    rset_clear(allow, key);
  }
  rset_clear(allow, type);
  if (irt_isnum(irkey->t)) {
    emit_cmpi(as, key, (int32_t)ir_knum(irkey)->u32.lo);
    asm_guardcc(as, CC_NE);
    emit_cmpi(as, type, (int32_t)ir_knum(irkey)->u32.hi);
  } else {
    if (ra_hasreg(key)) {
      emit_cmpi(as, key, irkey->i);  /* May use RID_TMP, i.e. type. */
      asm_guardcc(as, CC_NE);
    }
    emit_ai(as, PPCI_CMPWI, type, irt_toitype(irkey->t));
  }
  if (ra_hasreg(key)) emit_tai(as, PPCI_LWZ, key, idx, kofs+4);
  emit_tai(as, PPCI_LWZ, type, idx, kofs);
  if (ofs > 32736) {
    emit_tai(as, PPCI_ADDIS, dest, dest, (ofs + 32768) >> 16);
    emit_tai(as, PPCI_ADDI, dest, node, ofs);
  }
}
#endif

#if LJ_ARCH_PPC64
static void asm_uref(ASMState *as, IRIns *ir)
{
  Reg dest = ra_dest(as, ir, RSET_GPR);
  int guarded = (irt_t(ir->t) & (IRT_GUARD|IRT_TYPE)) == (IRT_GUARD|IRT_PGC);
  if (irref_isk(ir->op1) && !guarded) {
    GCfunc *fn = ir_kfunc(IR(ir->op1));
    MRef *v = &gcref(fn->l.uvptr[(ir->op2 >> 8)])->uv.v;
    emit_lsptr(as, PPCI_LD, dest, v, RSET_GPR);
  } else {
    if (guarded) {
      asm_guardcc(as, ir->o == IR_UREFC ? CC_NE : CC_EQ);
      emit_ai(as, PPCI_CMPWI, RID_TMP, 1);
    }
    if (ir->o == IR_UREFC)
      emit_tai(as, PPCI_ADDI, dest, dest, (int32_t)offsetof(GCupval, tv));
    else
      emit_tai(as, PPCI_LD, dest, dest, (int32_t)offsetof(GCupval, v));
    if (guarded)
      emit_tai(as, PPCI_LBZ, RID_TMP, dest, (int32_t)offsetof(GCupval, closed));
    if (irref_isk(ir->op1)) {
      GCfunc *fn = ir_kfunc(IR(ir->op1));
      GCobj *o = gcref(fn->l.uvptr[(ir->op2 >> 8)]);
      emit_loada(as, dest, o);
    } else {
      emit_tai(as, PPCI_LD, dest, ra_alloc1(as, ir->op1, RSET_GPR),
	       (int32_t)offsetof(GCfuncL, uvptr) +
	       (int32_t)sizeof(GCRef) * (int32_t)(ir->op2 >> 8));
    }
  }
}
#else
static void asm_uref(ASMState *as, IRIns *ir)
{
  Reg dest = ra_dest(as, ir, RSET_GPR);
  int guarded = (irt_t(ir->t) & (IRT_GUARD|IRT_TYPE)) == (IRT_GUARD|IRT_PGC);
  if (irref_isk(ir->op1) && !guarded) {
    GCfunc *fn = ir_kfunc(IR(ir->op1));
    MRef *v = &gcref(fn->l.uvptr[(ir->op2 >> 8)])->uv.v;
    emit_lsptr(as, PPCI_LWZ, dest, v, RSET_GPR);
  } else {
    if (guarded) {
      asm_guardcc(as, ir->o == IR_UREFC ? CC_NE : CC_EQ);
      emit_ai(as, PPCI_CMPWI, RID_TMP, 1);
    }
    if (ir->o == IR_UREFC)
      emit_tai(as, PPCI_ADDI, dest, dest, (int32_t)offsetof(GCupval, tv));
    else
      emit_tai(as, PPCI_LWZ, dest, dest, (int32_t)offsetof(GCupval, v));
    if (guarded)
      emit_tai(as, PPCI_LBZ, RID_TMP, dest, (int32_t)offsetof(GCupval, closed));
    if (irref_isk(ir->op1)) {
      GCfunc *fn = ir_kfunc(IR(ir->op1));
      int32_t k = (int32_t)gcrefu(fn->l.uvptr[(ir->op2 >> 8)]);
      emit_loadi(as, dest, k);
    } else {
      emit_tai(as, PPCI_LWZ, dest, ra_alloc1(as, ir->op1, RSET_GPR),
	       (int32_t)offsetof(GCfuncL, uvptr) + 4*(int32_t)(ir->op2 >> 8));
    }
  }
}
#endif

static void asm_fref(ASMState *as, IRIns *ir)
{
  UNUSED(as); UNUSED(ir);
  lj_assertA(!ra_used(ir), "unfused FREF");
}

#if LJ_ARCH_PPC64
static void asm_strref(ASMState *as, IRIns *ir)
{
  RegSet allow = RSET_GPR;
  Reg dest = ra_dest(as, ir, allow);
  Reg base = ra_alloc1(as, ir->op1, allow);
  IRIns *irr = IR(ir->op2);
  int32_t ofs = (int32_t)sizeof(GCstr);
  rset_clear(allow, base);
  if (irref_isk(ir->op2) && checki16(ofs + irr->i)) {
    emit_tai(as, PPCI_ADDI, dest, base, ofs + irr->i);
  } else {
    /* The index is a 32-bit int: sign-extend before the pointer add (D3). */
    Reg idx = ra_alloc1(as, ir->op2, allow);
    emit_tai(as, PPCI_ADDI, dest, dest, ofs);
    emit_tab(as, PPCI_ADD, dest, base, RID_TMP);
    emit_extsw(as, RID_TMP, idx);
  }
}
#else
static void asm_strref(ASMState *as, IRIns *ir)
{
  Reg dest = ra_dest(as, ir, RSET_GPR);
  IRRef ref = ir->op2, refk = ir->op1;
  int32_t ofs = (int32_t)sizeof(GCstr);
  Reg r;
  if (irref_isk(ref)) {
    IRRef tmp = refk; refk = ref; ref = tmp;
  } else if (!irref_isk(refk)) {
    Reg right, left = ra_alloc1(as, ir->op1, RSET_GPR);
    IRIns *irr = IR(ir->op2);
    if (ra_hasreg(irr->r)) {
      ra_noweak(as, irr->r);
      right = irr->r;
    } else if (mayfuse(as, irr->op2) &&
	       irr->o == IR_ADD && irref_isk(irr->op2) &&
	       checki16(ofs + IR(irr->op2)->i)) {
      ofs += IR(irr->op2)->i;
      right = ra_alloc1(as, irr->op1, rset_exclude(RSET_GPR, left));
    } else {
      right = ra_allocref(as, ir->op2, rset_exclude(RSET_GPR, left));
    }
    emit_tai(as, PPCI_ADDI, dest, dest, ofs);
    emit_tab(as, PPCI_ADD, dest, left, right);
    return;
  }
  r = ra_alloc1(as, ref, RSET_GPR);
  ofs += IR(refk)->i;
  if (checki16(ofs))
    emit_tai(as, PPCI_ADDI, dest, r, ofs);
  else
    emit_tab(as, PPCI_ADD, dest, r,
	     ra_allock(as, ofs, rset_exclude(RSET_GPR, r)));
}
#endif

/* -- Loads and stores ---------------------------------------------------- */

#if LJ_ARCH_PPC64
static PPCIns asm_fxloadins(ASMState *as, IRIns *ir)
{
  UNUSED(as);
  switch (irt_type(ir->t)) {
  case IRT_I8: return PPCI_LBZ;  /* Needs sign-extension. */
  case IRT_U8: return PPCI_LBZ;
  case IRT_I16: return PPCI_LHA;
  case IRT_U16: return PPCI_LHZ;
  case IRT_NUM: return PPCI_LFD;
  case IRT_FLOAT: return PPCI_LFS;
  default: return irt_is64(ir->t) ? PPCI_LD : PPCI_LWZ;
  }
}
#else
static PPCIns asm_fxloadins(ASMState *as, IRIns *ir)
{
  UNUSED(as);
  switch (irt_type(ir->t)) {
  case IRT_I8: return PPCI_LBZ;  /* Needs sign-extension. */
  case IRT_U8: return PPCI_LBZ;
  case IRT_I16: return PPCI_LHA;
  case IRT_U16: return PPCI_LHZ;
  case IRT_NUM: lj_assertA(!LJ_SOFTFP, "unsplit FP op"); return PPCI_LFD;
  case IRT_FLOAT: if (!LJ_SOFTFP) return PPCI_LFS;
  default: return PPCI_LWZ;
  }
}
#endif

#if LJ_ARCH_PPC64
static PPCIns asm_fxstoreins(ASMState *as, IRIns *ir)
{
  UNUSED(as);
  switch (irt_type(ir->t)) {
  case IRT_I8: case IRT_U8: return PPCI_STB;
  case IRT_I16: case IRT_U16: return PPCI_STH;
  case IRT_NUM: return PPCI_STFD;
  case IRT_FLOAT: return PPCI_STFS;
  default: return irt_is64(ir->t) ? PPCI_STD : PPCI_STW;
  }
}
#else
static PPCIns asm_fxstoreins(ASMState *as, IRIns *ir)
{
  UNUSED(as);
  switch (irt_type(ir->t)) {
  case IRT_I8: case IRT_U8: return PPCI_STB;
  case IRT_I16: case IRT_U16: return PPCI_STH;
  case IRT_NUM: lj_assertA(!LJ_SOFTFP, "unsplit FP op"); return PPCI_STFD;
  case IRT_FLOAT: if (!LJ_SOFTFP) return PPCI_STFS;
  default: return PPCI_STW;
  }
}
#endif

static void asm_fload(ASMState *as, IRIns *ir)
{
  Reg dest = ra_dest(as, ir, RSET_GPR);
  PPCIns pi = asm_fxloadins(as, ir);
  Reg idx;
  int32_t ofs;
  if (ir->op1 == REF_NIL) {  /* FLOAD from GG_State with offset. */
    idx = RID_JGL;
    ofs = (ir->op2 << 2) - 32768 - GG_OFS(g);
  } else {
    idx = ra_alloc1(as, ir->op1, RSET_GPR);
    if (ir->op2 == IRFL_TAB_ARRAY) {
      ofs = asm_fuseabase(as, ir->op1);
      if (ofs) {  /* Turn the t->array load into an add for colocated arrays. */
	emit_tai(as, PPCI_ADDI, dest, idx, ofs);
	return;
      }
    }
    ofs = field_ofs[ir->op2];
  }
  lj_assertA(!irt_isi8(ir->t), "unsupported FLOAD I8");
  emit_tai(as, pi, dest, idx, ofs);
}

static void asm_fstore(ASMState *as, IRIns *ir)
{
  if (ir->r != RID_SINK) {
    Reg src = ra_alloc1(as, ir->op2, RSET_GPR);
    IRIns *irf = IR(ir->op1);
    Reg idx = ra_alloc1(as, irf->op1, rset_exclude(RSET_GPR, src));
    int32_t ofs = field_ofs[irf->op2];
    PPCIns pi = asm_fxstoreins(as, ir);
    emit_tai(as, pi, src, idx, ofs);
  }
}

static void asm_xload(ASMState *as, IRIns *ir)
{
  Reg dest = ra_dest(as, ir,
    (!LJ_SOFTFP && irt_isfp(ir->t)) ? RSET_FPR : RSET_GPR);
  lj_assertA(!(ir->op2 & IRXLOAD_UNALIGNED), "unaligned XLOAD");
  if (irt_isi8(ir->t))
    emit_as(as, PPCI_EXTSB, dest, dest);
  asm_fusexref(as, asm_fxloadins(as, ir), dest, ir->op1, RSET_GPR, 0);
}

#if LJ_ARCH_PPC64
static void asm_xstore_(ASMState *as, IRIns *ir, int32_t ofs)
{
  IRIns *irb;
  if (ir->r == RID_SINK)
    return;
  if (ofs == 0 && mayfuse(as, ir->op2) && (irb = IR(ir->op2))->o == IR_BSWAP &&
      ra_noreg(irb->r) &&
      (irt_isint(ir->t) || irt_isu32(ir->t) || irt_isi64(ir->t) || irt_isu64(ir->t))) {
    /* Fuse BSWAP with XSTORE to stwbrx/stdbrx. */
    Reg src = ra_alloc1(as, irb->op1, RSET_GPR);
    asm_fusexrefx(as, irt_is64(ir->t) ? PPCI_STDBRX : PPCI_STWBRX, src,
		  ir->op1, rset_exclude(RSET_GPR, src));
  } else {
    Reg src = ra_alloc1(as, ir->op2, irt_isfp(ir->t) ? RSET_FPR : RSET_GPR);
    asm_fusexref(as, asm_fxstoreins(as, ir), src, ir->op1,
		 rset_exclude(RSET_GPR, src), ofs);
  }
}
#else
static void asm_xstore_(ASMState *as, IRIns *ir, int32_t ofs)
{
  IRIns *irb;
  if (ir->r == RID_SINK)
    return;
  if (ofs == 0 && mayfuse(as, ir->op2) && (irb = IR(ir->op2))->o == IR_BSWAP &&
      ra_noreg(irb->r) && (irt_isint(ir->t) || irt_isu32(ir->t))) {
    /* Fuse BSWAP with XSTORE to stwbrx. */
    Reg src = ra_alloc1(as, irb->op1, RSET_GPR);
    asm_fusexrefx(as, PPCI_STWBRX, src, ir->op1, rset_exclude(RSET_GPR, src));
  } else {
    Reg src = ra_alloc1(as, ir->op2,
      (!LJ_SOFTFP && irt_isfp(ir->t)) ? RSET_FPR : RSET_GPR);
    asm_fusexref(as, asm_fxstoreins(as, ir), src, ir->op1,
		 rset_exclude(RSET_GPR, src), ofs);
  }
}
#endif

#define asm_xstore(as, ir)	asm_xstore_(as, ir, 0)

#if LJ_ARCH_PPC64
static void asm_ahuvload(ASMState *as, IRIns *ir)
{
  IRType1 t = ir->t;
  Reg dest = RID_NONE, gpr, base, idx;
  RegSet allow = RSET_GPR;
  int32_t ofs = AHUREF_LSX;
  if (ra_used(ir)) {
    lj_assertA(irt_isnum(ir->t) || irt_isint(ir->t) || irt_isaddr(ir->t),
	       "bad load type %d", irt_type(ir->t));
    dest = ra_dest(as, ir, irt_isnum(t) ? RSET_FPR : allow);
    rset_clear(allow, dest);
    if (irt_isaddr(t))
      emit_untag(as, dest, dest);  /* After the guard, in program order. */
  }
  idx = asm_fuseahuref(as, ir->op1, &ofs, allow);
  if (ir->o == IR_VLOAD) {
    ofs = ofs != AHUREF_LSX ? ofs + 8 * ir->op2 :
	  ir->op2 ? 8 * ir->op2 : AHUREF_LSX;
  }
  base = (idx & 255);
  /* The 64-bit word is loaded into a GPR: dest if it is one, else r0.
  ** An int payload is the low word of that register (D3); an FPR dest
  ** gets its own lfd from the same address.
  */
  gpr = (ra_hasreg(dest) && dest < RID_MAX_GPR) ? dest : RID_TMP;
  if (irt_isnum(t)) {
    Reg tisnum = ra_allock(as, tvtisnum,
			   rset_exclude(rset_exclude(allow, base), (idx>>8)));
    asm_guardcc(as, CC_GE);
    emit_ab(as, PPCI_CMPLD, RID_TMP, tisnum);
  } else {
    asm_guardcc(as, CC_NE);
    emit_ai(as, PPCI_CMPDI, RID_TMP, (int32_t)irt_toitype(t));
  }
  emit_tag(as, RID_TMP, gpr);
  if (ofs == AHUREF_LSX) {
    emit_tab(as, PPCI_LDX, gpr, base, RID_TMP);
    if (ra_hasreg(dest) && dest >= RID_MAX_GPR)
      emit_fab(as, PPCI_LFDX, dest, base, RID_TMP);
    emit_slwi(as, RID_TMP, (idx>>8), 3);  /* Zero-extends the index (D3). */
  } else {
    emit_tai(as, PPCI_LD, gpr, idx, ofs);
    if (ra_hasreg(dest) && dest >= RID_MAX_GPR)
      emit_fai(as, PPCI_LFD, dest, idx, ofs);
  }
}
#else
static void asm_ahuvload(ASMState *as, IRIns *ir)
{
  IRType1 t = ir->t;
  Reg dest = RID_NONE, type = RID_TMP, tmp = RID_TMP, idx;
  RegSet allow = RSET_GPR;
  int32_t ofs = AHUREF_LSX;
  if (LJ_SOFTFP && (ir+1)->o == IR_HIOP) {
    t.irt = IRT_NUM;
    if (ra_used(ir+1)) {
      type = ra_dest(as, ir+1, allow);
      rset_clear(allow, type);
    }
    ofs = 0;
  }
  if (ra_used(ir)) {
    lj_assertA((LJ_SOFTFP ? 0 : irt_isnum(ir->t)) ||
	       irt_isint(ir->t) || irt_isaddr(ir->t),
	       "bad load type %d", irt_type(ir->t));
    if (LJ_SOFTFP || !irt_isnum(t)) ofs = 0;
    dest = ra_dest(as, ir, (!LJ_SOFTFP && irt_isnum(t)) ? RSET_FPR : allow);
    rset_clear(allow, dest);
  }
  idx = asm_fuseahuref(as, ir->op1, &ofs, allow);
  if (ir->o == IR_VLOAD) {
    ofs = ofs != AHUREF_LSX ? ofs + 8 * ir->op2 :
	  ir->op2 ? 8 * ir->op2 : AHUREF_LSX;
  }
  if (irt_isnum(t)) {
    Reg tisnum = ra_allock(as, (int32_t)LJ_TISNUM, rset_exclude(allow, idx));
    asm_guardcc(as, CC_GE);
    emit_ab(as, PPCI_CMPLW, type, tisnum);
    if (ra_hasreg(dest)) {
      if (!LJ_SOFTFP && ofs == AHUREF_LSX) {
	tmp = ra_scratch(as, rset_exclude(rset_exclude(RSET_GPR,
						       (idx&255)), (idx>>8)));
	emit_fab(as, PPCI_LFDX, dest, (idx&255), tmp);
      } else {
	emit_fai(as, LJ_SOFTFP ? PPCI_LWZ : PPCI_LFD, dest, idx,
		 ofs+4*LJ_SOFTFP);
      }
    }
  } else {
    asm_guardcc(as, CC_NE);
    emit_ai(as, PPCI_CMPWI, type, irt_toitype(t));
    if (ra_hasreg(dest)) emit_tai(as, PPCI_LWZ, dest, idx, ofs+4);
  }
  if (ofs == AHUREF_LSX) {
    emit_tab(as, PPCI_LWZX, type, (idx&255), tmp);
    emit_slwi(as, tmp, (idx>>8), 3);
  } else {
    emit_tai(as, PPCI_LWZ, type, idx, ofs);
  }
}
#endif

#if LJ_ARCH_PPC64
static void asm_ahustore(ASMState *as, IRIns *ir)
{
  RegSet allow = RSET_GPR;
  Reg idx, src = RID_NONE, type = RID_NONE, tmp = RID_TMP;
  int32_t ofs = AHUREF_LSX;
  if (ir->r == RID_SINK)
    return;
  if (irt_isnum(ir->t)) {
    src = ra_alloc1(as, ir->op2, RSET_FPR);
  } else if (irt_ispri(ir->t)) {
    tmp = ra_allock(as, (intptr_t)tvpri64(ir->t), allow);
    rset_clear(allow, tmp);
  } else {
    src = ra_alloc1(as, ir->op2, allow);
    rset_clear(allow, src);
    type = ra_allock(as, (intptr_t)tvtag64(ir->t), allow);
    rset_clear(allow, type);
    ofs = 0;  /* The tagged word is built in r0: no indexed form. */
  }
  idx = asm_fuseahuref(as, ir->op1, &ofs, allow);
  if (irt_isnum(ir->t)) {
    if (ofs == AHUREF_LSX) {
      emit_fab(as, PPCI_STFDX, src, (idx&255), RID_TMP);
      emit_slwi(as, RID_TMP, (idx>>8), 3);
    } else {
      emit_fai(as, PPCI_STFD, src, idx, ofs);
    }
  } else {
    if (ofs == AHUREF_LSX) {
      emit_tab(as, PPCI_STDX, tmp, (idx&255), RID_TMP);
      emit_slwi(as, RID_TMP, (idx>>8), 3);
    } else {
      emit_tai(as, PPCI_STD, tmp, idx, ofs);
    }
    if (ra_hasreg(src)) {
      if (irt_isinteger(ir->t)) {
	emit_asb(as, PPCI_OR, tmp, tmp, type);
	emit_zextw(as, tmp, src);
      } else {
	emit_asb(as, PPCI_OR, tmp, src, type);
      }
    }
  }
}
#else
static void asm_ahustore(ASMState *as, IRIns *ir)
{
  RegSet allow = RSET_GPR;
  Reg idx, src = RID_NONE, type = RID_NONE;
  int32_t ofs = AHUREF_LSX;
  if (ir->r == RID_SINK)
    return;
  if (!LJ_SOFTFP && irt_isnum(ir->t)) {
    src = ra_alloc1(as, ir->op2, RSET_FPR);
  } else {
    if (!irt_ispri(ir->t)) {
      src = ra_alloc1(as, ir->op2, allow);
      rset_clear(allow, src);
      ofs = 0;
    }
    if (LJ_SOFTFP && (ir+1)->o == IR_HIOP)
      type = ra_alloc1(as, (ir+1)->op2, allow);
    else
      type = ra_allock(as, (int32_t)irt_toitype(ir->t), allow);
    rset_clear(allow, type);
  }
  idx = asm_fuseahuref(as, ir->op1, &ofs, allow);
  if (!LJ_SOFTFP && irt_isnum(ir->t)) {
    if (ofs == AHUREF_LSX) {
      emit_fab(as, PPCI_STFDX, src, (idx&255), RID_TMP);
      emit_slwi(as, RID_TMP, (idx>>8), 3);
    } else {
      emit_fai(as, PPCI_STFD, src, idx, ofs);
    }
  } else {
    if (ra_hasreg(src))
      emit_tai(as, PPCI_STW, src, idx, ofs+4);
    if (ofs == AHUREF_LSX) {
      emit_tab(as, PPCI_STWX, type, (idx&255), RID_TMP);
      emit_slwi(as, RID_TMP, (idx>>8), 3);
    } else {
      emit_tai(as, PPCI_STW, type, idx, ofs);
    }
  }
}
#endif

#if LJ_ARCH_PPC64
static void asm_sload(ASMState *as, IRIns *ir)
{
  int32_t ofs = 8*((int32_t)ir->op1-1-LJ_FR2);
  IRType1 t = ir->t;
  Reg dest = RID_NONE, base;
  RegSet allow = RSET_GPR;
  lj_assertA(!(ir->op2 & IRSLOAD_PARENT),
	     "bad parent SLOAD");  /* Handled by asm_head_side(). */
  lj_assertA(irt_isguard(ir->t) || !(ir->op2 & IRSLOAD_TYPECHECK),
	     "inconsistent SLOAD variant");
  lj_assertA(LJ_DUALNUM ||
	     !irt_isint(t) ||
	     (ir->op2 & (IRSLOAD_CONVERT|IRSLOAD_FRAME|IRSLOAD_KEYINDEX)),
	     "bad SLOAD type");
  if ((ir->op2 & IRSLOAD_CONVERT) && irt_isguard(t) && irt_isint(t)) {
    dest = ra_scratch(as, RSET_FPR);
    asm_tointg(as, ir, dest);
    t.irt = IRT_NUM;  /* Continue with a regular number type check. */
  } else if (ra_used(ir)) {
    lj_assertA(irt_isnum(t) || irt_isint(t) || irt_isaddr(t),
	       "bad SLOAD type %d", irt_type(ir->t));
    dest = ra_dest(as, ir, irt_isnum(t) ? RSET_FPR : allow);
    rset_clear(allow, dest);
    base = ra_alloc1(as, REF_BASE, allow);
    rset_clear(allow, base);
    if ((ir->op2 & IRSLOAD_CONVERT)) {
      if (irt_isint(t)) {  /* Unchecked number to int: truncate. */
	Reg tmp = ra_scratch(as, RSET_FPR);
	emit_mfvsrwz(as, dest, tmp);
	emit_fb(as, PPCI_FCTIWZ, tmp, tmp);
	dest = tmp;
	t.irt = IRT_NUM;  /* Check for original type. */
      } else {  /* Int to number. */
	Reg tmp = ra_scratch(as, allow);
	emit_fb(as, PPCI_FCFID, dest, dest);
	emit_mtvsrwa(as, dest, tmp);
	dest = tmp;
	t.irt = IRT_INT;  /* Check for original type. */
      }
    } else if (irt_isaddr(t)) {
      emit_untag(as, dest, dest);  /* After the guard, in program order. */
    }
    goto dotypecheck;
  }
  base = ra_alloc1(as, REF_BASE, allow);
  rset_clear(allow, base);
dotypecheck:
  if ((ir->op2 & IRSLOAD_TYPECHECK)) {
    /* The 64-bit slot word goes to a GPR: dest if it is one, else r0. */
    Reg gpr = (ra_hasreg(dest) && dest < RID_MAX_GPR) ? dest : RID_TMP;
    if (irt_isnum(t)) {
      Reg tisnum = ra_allock(as, tvtisnum, allow);
      asm_guardcc(as, CC_GE);
      emit_ab(as, PPCI_CMPLD, RID_TMP, tisnum);
      emit_tag(as, RID_TMP, gpr);
      if (ra_hasreg(dest) && dest >= RID_MAX_GPR)
	emit_fai(as, PPCI_LFD, dest, base, ofs);
    } else if ((ir->op2 & IRSLOAD_KEYINDEX)) {
      /* The ITERN control slot: LJ_KEYINDEX in the high word (D2, Phase 0). */
      asm_guardcc(as, CC_NE);
      emit_ai(as, PPCI_CMPWI, RID_TMP, (LJ_KEYINDEX & 0xffff));
      emit_asi(as, PPCI_XORIS, RID_TMP, RID_TMP, (LJ_KEYINDEX >> 16));
      emit_srdi(as, RID_TMP, gpr, 32);
    } else {
      asm_guardcc(as, CC_NE);
      emit_ai(as, PPCI_CMPDI, RID_TMP, (int32_t)irt_toitype(t));
      emit_tag(as, RID_TMP, gpr);
    }
    emit_tai(as, PPCI_LD, gpr, base, ofs);
  } else if (ra_hasreg(dest)) {
    if (irt_isnum(t))
      emit_fai(as, PPCI_LFD, dest, base, ofs);
    else
      emit_tai(as, PPCI_LD, dest, base, ofs);
  }
}
#else
static void asm_sload(ASMState *as, IRIns *ir)
{
  int32_t ofs = 8*((int32_t)ir->op1-1) + ((ir->op2 & IRSLOAD_FRAME) ? 0 : 4);
  IRType1 t = ir->t;
  Reg dest = RID_NONE, type = RID_NONE, base;
  RegSet allow = RSET_GPR;
  int hiop = (LJ_SOFTFP && (ir+1)->o == IR_HIOP);
  if (hiop)
    t.irt = IRT_NUM;
  lj_assertA(!(ir->op2 & IRSLOAD_PARENT),
	     "bad parent SLOAD");  /* Handled by asm_head_side(). */
  lj_assertA(irt_isguard(ir->t) || !(ir->op2 & IRSLOAD_TYPECHECK),
	     "inconsistent SLOAD variant");
  lj_assertA(LJ_DUALNUM ||
	     !irt_isint(t) ||
	     (ir->op2 & (IRSLOAD_CONVERT|IRSLOAD_FRAME|IRSLOAD_KEYINDEX)),
	     "bad SLOAD type");
#if LJ_SOFTFP
  lj_assertA(!(ir->op2 & IRSLOAD_CONVERT),
	     "unsplit SLOAD convert");  /* Handled by LJ_SOFTFP SPLIT. */
  if (hiop && ra_used(ir+1)) {
    type = ra_dest(as, ir+1, allow);
    rset_clear(allow, type);
  }
#else
  if ((ir->op2 & IRSLOAD_CONVERT) && irt_isguard(t) && irt_isint(t)) {
    dest = ra_scratch(as, RSET_FPR);
    asm_tointg(as, ir, dest);
    t.irt = IRT_NUM;  /* Continue with a regular number type check. */
  } else
#endif
  if (ra_used(ir)) {
    lj_assertA(irt_isnum(t) || irt_isint(t) || irt_isaddr(t),
	       "bad SLOAD type %d", irt_type(ir->t));
    dest = ra_dest(as, ir, (!LJ_SOFTFP && irt_isnum(t)) ? RSET_FPR : allow);
    rset_clear(allow, dest);
    base = ra_alloc1(as, REF_BASE, allow);
    rset_clear(allow, base);
    if (!LJ_SOFTFP && (ir->op2 & IRSLOAD_CONVERT)) {
      if (irt_isint(t)) {
	emit_tai(as, PPCI_LWZ, dest, RID_SP, SPOFS_TMPLO);
	dest = ra_scratch(as, RSET_FPR);
	emit_fai(as, PPCI_STFD, dest, RID_SP, SPOFS_TMP);
	emit_fb(as, PPCI_FCTIWZ, dest, dest);
	t.irt = IRT_NUM;  /* Check for original type. */
      } else {
	Reg tmp = ra_scratch(as, allow);
	Reg hibias = ra_allock(as, 0x43300000, rset_clear(allow, tmp));
	Reg fbias = ra_scratch(as, rset_exclude(RSET_FPR, dest));
	emit_fab(as, PPCI_FSUB, dest, dest, fbias);
	emit_fai(as, PPCI_LFD, dest, RID_SP, SPOFS_TMP);
	emit_lsptr(as, PPCI_LFS, (fbias & 31),
		   (void *)&as->J->k32[LJ_K32_2P52_2P31],
		   rset_clear(allow, hibias));
	emit_tai(as, PPCI_STW, tmp, RID_SP, SPOFS_TMPLO);
	emit_tai(as, PPCI_STW, hibias, RID_SP, SPOFS_TMPHI);
	emit_asi(as, PPCI_XORIS, tmp, tmp, 0x8000);
	dest = tmp;
	t.irt = IRT_INT;  /* Check for original type. */
      }
    }
    goto dotypecheck;
  }
  base = ra_alloc1(as, REF_BASE, allow);
  rset_clear(allow, base);
dotypecheck:
  if (irt_isnum(t)) {
    if ((ir->op2 & IRSLOAD_TYPECHECK)) {
      Reg tisnum = ra_allock(as, (int32_t)LJ_TISNUM, allow);
      asm_guardcc(as, CC_GE);
#if !LJ_SOFTFP
      type = RID_TMP;
#endif
      emit_ab(as, PPCI_CMPLW, type, tisnum);
    }
    if (ra_hasreg(dest)) emit_fai(as, LJ_SOFTFP ? PPCI_LWZ : PPCI_LFD, dest,
				  base, ofs-(LJ_SOFTFP?0:4));
  } else {
    if ((ir->op2 & IRSLOAD_TYPECHECK)) {
      asm_guardcc(as, CC_NE);
      if ((ir->op2 & IRSLOAD_KEYINDEX)) {
	emit_ai(as, PPCI_CMPWI, RID_TMP, (LJ_KEYINDEX & 0xffff));
	emit_asi(as, PPCI_XORIS, RID_TMP, RID_TMP, (LJ_KEYINDEX >> 16));
      } else {
	emit_ai(as, PPCI_CMPWI, RID_TMP, irt_toitype(t));
      }
      type = RID_TMP;
    }
    if (ra_hasreg(dest)) emit_tai(as, PPCI_LWZ, dest, base, ofs);
  }
  if (ra_hasreg(type)) emit_tai(as, PPCI_LWZ, type, base, ofs-4);
}
#endif

/* -- Allocations --------------------------------------------------------- */

#if LJ_HASFFI
#if LJ_ARCH_PPC64
static void asm_cnew(ASMState *as, IRIns *ir)
{
  CTState *cts = ctype_ctsG(J2G(as->J));
  CTypeID id = (CTypeID)IR(ir->op1)->i;
  CTSize sz;
  CTInfo info = lj_ctype_info(cts, id, &sz);
  const CCallInfo *ci = &lj_ir_callinfo[IRCALL_lj_mem_newgco];
  IRRef args[4];
  RegSet drop = RSET_SCRATCH;
  lj_assertA(sz != CTSIZE_INVALID || (ir->o == IR_CNEW && ir->op2 != REF_NIL),
	     "bad CNEW/CNEWI operands");

  as->gcsteps++;
  if (ra_hasreg(ir->r))
    rset_clear(drop, ir->r);  /* Dest reg handled below. */
  ra_evictset(as, drop);
  if (ra_used(ir))
    ra_destreg(as, ir, RID_RET);  /* GCcdata * */

  /* Initialize immutable cdata object. */
  if (ir->o == IR_CNEWI) {
    RegSet allow = (RSET_GPR & ~RSET_SCRATCH);
    lj_assertA(sz == 4 || sz == 8, "bad CNEWI size %d", sz);
    emit_tai(as, sz == 8 ? PPCI_STD : PPCI_STW, ra_alloc1(as, ir->op2, allow),
	     RID_RET, sizeof(GCcdata));
  } else if (ir->op2 != REF_NIL) {  /* Create VLA/VLS/aligned cdata. */
    ci = &lj_ir_callinfo[IRCALL_lj_cdata_newv];
    args[0] = ASMREF_L;     /* lua_State *L */
    args[1] = ir->op1;      /* CTypeID id   */
    args[2] = ir->op2;      /* CTSize sz    */
    args[3] = ASMREF_TMP1;  /* CTSize align */
    asm_gencall(as, ci, args);
    emit_loadi(as, ra_releasetmp(as, ASMREF_TMP1), (int32_t)ctype_align(info));
    return;
  }

  /* Initialize gct and ctypeid. lj_mem_newgco() already sets marked. */
  emit_tai(as, PPCI_STB, RID_RET+1, RID_RET, offsetof(GCcdata, gct));
  emit_tai(as, PPCI_STH, RID_TMP, RID_RET, offsetof(GCcdata, ctypeid));
  emit_ti(as, PPCI_LI, RID_RET+1, ~LJ_TCDATA);
  emit_ti(as, PPCI_LI, RID_TMP, id);  /* Lower 16 bit used. Sign-ext ok. */
  args[0] = ASMREF_L;     /* lua_State *L */
  args[1] = ASMREF_TMP1;  /* MSize size   */
  asm_gencall(as, ci, args);
  ra_allockreg(as, (int32_t)(sz+sizeof(GCcdata)),
	       ra_releasetmp(as, ASMREF_TMP1));
}
#else
static void asm_cnew(ASMState *as, IRIns *ir)
{
  CTState *cts = ctype_ctsG(J2G(as->J));
  CTypeID id = (CTypeID)IR(ir->op1)->i;
  CTSize sz;
  CTInfo info = lj_ctype_info(cts, id, &sz);
  const CCallInfo *ci = &lj_ir_callinfo[IRCALL_lj_mem_newgco];
  IRRef args[4];
  RegSet drop = RSET_SCRATCH;
  lj_assertA(sz != CTSIZE_INVALID || (ir->o == IR_CNEW && ir->op2 != REF_NIL),
	     "bad CNEW/CNEWI operands");

  as->gcsteps++;
  if (ra_hasreg(ir->r))
    rset_clear(drop, ir->r);  /* Dest reg handled below. */
  ra_evictset(as, drop);
  if (ra_used(ir))
    ra_destreg(as, ir, RID_RET);  /* GCcdata * */

  /* Initialize immutable cdata object. */
  if (ir->o == IR_CNEWI) {
    RegSet allow = (RSET_GPR & ~RSET_SCRATCH);
    int32_t ofs = sizeof(GCcdata);
    lj_assertA(sz == 4 || sz == 8, "bad CNEWI size %d", sz);
    if (sz == 8) {
      ofs += 4;
      lj_assertA((ir+1)->o == IR_HIOP, "expected HIOP for CNEWI");
    }
    for (;;) {
      Reg r = ra_alloc1(as, ir->op2, allow);
      emit_tai(as, PPCI_STW, r, RID_RET, ofs);
      rset_clear(allow, r);
      if (ofs == sizeof(GCcdata)) break;
      ofs -= 4; ir++;
    }
  } else if (ir->op2 != REF_NIL) {  /* Create VLA/VLS/aligned cdata. */
    ci = &lj_ir_callinfo[IRCALL_lj_cdata_newv];
    args[0] = ASMREF_L;     /* lua_State *L */
    args[1] = ir->op1;      /* CTypeID id   */
    args[2] = ir->op2;      /* CTSize sz    */
    args[3] = ASMREF_TMP1;  /* CTSize align */
    asm_gencall(as, ci, args);
    emit_loadi(as, ra_releasetmp(as, ASMREF_TMP1), (int32_t)ctype_align(info));
    return;
  }

  /* Initialize gct and ctypeid. lj_mem_newgco() already sets marked. */
  emit_tai(as, PPCI_STB, RID_RET+1, RID_RET, offsetof(GCcdata, gct));
  emit_tai(as, PPCI_STH, RID_TMP, RID_RET, offsetof(GCcdata, ctypeid));
  emit_ti(as, PPCI_LI, RID_RET+1, ~LJ_TCDATA);
  emit_ti(as, PPCI_LI, RID_TMP, id);  /* Lower 16 bit used. Sign-ext ok. */
  args[0] = ASMREF_L;     /* lua_State *L */
  args[1] = ASMREF_TMP1;  /* MSize size   */
  asm_gencall(as, ci, args);
  ra_allockreg(as, (int32_t)(sz+sizeof(GCcdata)),
	       ra_releasetmp(as, ASMREF_TMP1));
}
#endif
#endif

/* -- Write barriers ------------------------------------------------------ */

#if LJ_ARCH_PPC64
static void asm_tbar(ASMState *as, IRIns *ir)
{
  Reg tab = ra_alloc1(as, ir->op1, RSET_GPR);
  Reg mark = ra_scratch(as, rset_exclude(RSET_GPR, tab));
  Reg link = RID_TMP;
  MCLabel l_end = emit_label(as);
  emit_tai(as, PPCI_STD, link, tab, (int32_t)offsetof(GCtab, gclist));
  emit_tai(as, PPCI_STB, mark, tab, (int32_t)offsetof(GCtab, marked));
  emit_setgl(as, tab, gc.grayagain);
  lj_assertA(LJ_GC_BLACK == 0x04, "bad LJ_GC_BLACK");
  emit_rot(as, PPCI_RLWINM, mark, mark, 0, 30, 28);  /* Clear black bit. */
  emit_getgl(as, link, gc.grayagain);
  emit_condbranch(as, PPCI_BC|PPCF_Y, CC_EQ, l_end);
  emit_asi(as, PPCI_ANDIDOT, RID_TMP, mark, LJ_GC_BLACK);
  emit_tai(as, PPCI_LBZ, mark, tab, (int32_t)offsetof(GCtab, marked));
}
#else
static void asm_tbar(ASMState *as, IRIns *ir)
{
  Reg tab = ra_alloc1(as, ir->op1, RSET_GPR);
  Reg mark = ra_scratch(as, rset_exclude(RSET_GPR, tab));
  Reg link = RID_TMP;
  MCLabel l_end = emit_label(as);
  emit_tai(as, PPCI_STW, link, tab, (int32_t)offsetof(GCtab, gclist));
  emit_tai(as, PPCI_STB, mark, tab, (int32_t)offsetof(GCtab, marked));
  emit_setgl(as, tab, gc.grayagain);
  lj_assertA(LJ_GC_BLACK == 0x04, "bad LJ_GC_BLACK");
  emit_rot(as, PPCI_RLWINM, mark, mark, 0, 30, 28);  /* Clear black bit. */
  emit_getgl(as, link, gc.grayagain);
  emit_condbranch(as, PPCI_BC|PPCF_Y, CC_EQ, l_end);
  emit_asi(as, PPCI_ANDIDOT, RID_TMP, mark, LJ_GC_BLACK);
  emit_tai(as, PPCI_LBZ, mark, tab, (int32_t)offsetof(GCtab, marked));
}
#endif

static void asm_obar(ASMState *as, IRIns *ir)
{
  const CCallInfo *ci = &lj_ir_callinfo[IRCALL_lj_gc_barrieruv];
  IRRef args[2];
  MCLabel l_end;
  Reg obj, val, tmp;
  /* No need for other object barriers (yet). */
  lj_assertA(IR(ir->op1)->o == IR_UREFC, "bad OBAR type");
  ra_evictset(as, RSET_SCRATCH);
  l_end = emit_label(as);
  args[0] = ASMREF_TMP1;  /* global_State *g */
  args[1] = ir->op1;      /* TValue *tv      */
  asm_gencall(as, ci, args);
  emit_tai(as, PPCI_ADDI, ra_releasetmp(as, ASMREF_TMP1), RID_JGL, -32768);
  obj = IR(ir->op1)->r;
  tmp = ra_scratch(as, rset_exclude(RSET_GPR, obj));
  emit_condbranch(as, PPCI_BC|PPCF_Y, CC_EQ, l_end);
  emit_asi(as, PPCI_ANDIDOT, tmp, tmp, LJ_GC_BLACK);
  emit_condbranch(as, PPCI_BC, CC_EQ, l_end);
  emit_asi(as, PPCI_ANDIDOT, RID_TMP, RID_TMP, LJ_GC_WHITES);
  val = ra_alloc1(as, ir->op2, rset_exclude(RSET_GPR, obj));
  emit_tai(as, PPCI_LBZ, tmp, obj,
	   (int32_t)offsetof(GCupval, marked)-(int32_t)offsetof(GCupval, tv));
  emit_tai(as, PPCI_LBZ, RID_TMP, val, (int32_t)offsetof(GChead, marked));
}

/* -- Arithmetic and logic operations ------------------------------------- */

#if !LJ_SOFTFP
static void asm_fparith(ASMState *as, IRIns *ir, PPCIns pi)
{
  Reg dest = ra_dest(as, ir, RSET_FPR);
  Reg right, left = ra_alloc2(as, ir, RSET_FPR);
  right = (left >> 8); left &= 255;
  if (pi == PPCI_FMUL)
    emit_fac(as, pi, dest, left, right);
  else
    emit_fab(as, pi, dest, left, right);
}

static void asm_fpunary(ASMState *as, IRIns *ir, PPCIns pi)
{
  Reg dest = ra_dest(as, ir, RSET_FPR);
  Reg left = ra_hintalloc(as, ir->op1, dest, RSET_FPR);
  emit_fb(as, pi, dest, left);
}

#if LJ_ARCH_PPC64
static void asm_fpmath(ASMState *as, IRIns *ir)
{
  if (ir->op2 <= IRFPM_TRUNC) {
    /* frim/frip/friz (ISA 2.02+): IEEE round-to-integer in the FPR, the
    ** same result as C floor/ceil/trunc for every input incl. NaN, +-0,
    ** +-inf and |x| >= 2^52. No call, no memory temp.
    */
    asm_fpunary(as, ir, ir->op2 == IRFPM_FLOOR ? PPCI_FRIM :
			ir->op2 == IRFPM_CEIL ? PPCI_FRIP : PPCI_FRIZ);
  } else if (ir->op2 == IRFPM_SQRT && (as->flags & JIT_F_SQRT)) {
    asm_fpunary(as, ir, PPCI_FSQRT);
  } else {
    asm_callid(as, ir, IRCALL_lj_vm_floor + ir->op2);
  }
}
#else
static void asm_fpmath(ASMState *as, IRIns *ir)
{
  if (ir->op2 == IRFPM_SQRT && (as->flags & JIT_F_SQRT))
    asm_fpunary(as, ir, PPCI_FSQRT);
  else
    asm_callid(as, ir, IRCALL_lj_vm_floor + ir->op2);
}
#endif
#endif

#if LJ_ARCH_PPC64
static void asm_add(ASMState *as, IRIns *ir)
{
  if (irt_isnum(ir->t)) {
    if (!asm_fusemadd(as, ir, PPCI_FMADD, PPCI_FMADD))
      asm_fparith(as, ir, PPCI_FADD);
  } else {
    /* add/addi/addis are width-agnostic (D3); no CR0 fusion on PPC64,
    ** a dot-form would test the 64-bit result of a 32-bit op.
    */
    Reg dest = ra_dest(as, ir, RSET_GPR);
    Reg right, left = ra_hintalloc(as, ir->op1, dest, RSET_GPR);
    if (irref_isk(ir->op2)) {
      intptr_t k = get_kval(as, ir->op2);
      if (checki16(k)) {
	emit_tai(as, PPCI_ADDI, dest, left, (int32_t)k);
	return;
      } else if ((k & 0xffff) == 0 && checki16(k >> 16)) {
	emit_tai(as, PPCI_ADDIS, dest, left, (int32_t)(k >> 16));
	return;
      } else if (!as->sectref && checki16((k + 32768) >> 16)) {
	emit_tai(as, PPCI_ADDIS, dest, dest, (int32_t)((k + 32768) >> 16));
	emit_tai(as, PPCI_ADDI, dest, left, (int32_t)k);
	return;
      }
    }
    right = ra_alloc1(as, ir->op2, rset_exclude(RSET_GPR, left));
    emit_tab(as, PPCI_ADD, dest, left, right);
  }
}
#else
static void asm_add(ASMState *as, IRIns *ir)
{
#if !LJ_SOFTFP
  if (irt_isnum(ir->t)) {
    if (!asm_fusemadd(as, ir, PPCI_FMADD, PPCI_FMADD))
      asm_fparith(as, ir, PPCI_FADD);
  } else
#endif
  {
    Reg dest = ra_dest(as, ir, RSET_GPR);
    Reg right, left = ra_hintalloc(as, ir->op1, dest, RSET_GPR);
    PPCIns pi;
    if (irref_isk(ir->op2)) {
      int32_t k = IR(ir->op2)->i;
      if (checki16(k)) {
	pi = PPCI_ADDI;
	/* May fail due to spills/restores above, but simplifies the logic. */
	if (as->flagmcp == as->mcp) {
	  as->flagmcp = NULL;
	  as->mcp++;
	  pi = PPCI_ADDICDOT;
	}
	emit_tai(as, pi, dest, left, k);
	return;
      } else if ((k & 0xffff) == 0) {
	emit_tai(as, PPCI_ADDIS, dest, left, (k >> 16));
	return;
      } else if (!as->sectref) {
	emit_tai(as, PPCI_ADDIS, dest, dest, (k + 32768) >> 16);
	emit_tai(as, PPCI_ADDI, dest, left, k);
	return;
      }
    }
    pi = PPCI_ADD;
    /* May fail due to spills/restores above, but simplifies the logic. */
    if (as->flagmcp == as->mcp) {
      as->flagmcp = NULL;
      as->mcp++;
      pi |= PPCF_DOT;
    }
    right = ra_alloc1(as, ir->op2, rset_exclude(RSET_GPR, left));
    emit_tab(as, pi, dest, left, right);
  }
}
#endif

#if LJ_ARCH_PPC64
static void asm_sub(ASMState *as, IRIns *ir)
{
  if (irt_isnum(ir->t)) {
    if (!asm_fusemadd(as, ir, PPCI_FMSUB, PPCI_FNMSUB))
      asm_fparith(as, ir, PPCI_FSUB);
  } else {
    Reg dest = ra_dest(as, ir, RSET_GPR);
    Reg left, right;
    if (irref_isk(ir->op1)) {
      intptr_t k = get_kval(as, ir->op1);
      if (checki16(k)) {
	right = ra_alloc1(as, ir->op2, RSET_GPR);
	emit_tai(as, PPCI_SUBFIC, dest, right, (int32_t)k);
	return;
      }
    }
    left = ra_hintalloc(as, ir->op1, dest, RSET_GPR);
    right = ra_alloc1(as, ir->op2, rset_exclude(RSET_GPR, left));
    emit_tab(as, PPCI_SUBF, dest, right, left);  /* Subtract right _from_ left. */
  }
}
#else
static void asm_sub(ASMState *as, IRIns *ir)
{
#if !LJ_SOFTFP
  if (irt_isnum(ir->t)) {
    if (!asm_fusemadd(as, ir, PPCI_FMSUB, PPCI_FNMSUB))
      asm_fparith(as, ir, PPCI_FSUB);
  } else
#endif
  {
    PPCIns pi = PPCI_SUBF;
    Reg dest = ra_dest(as, ir, RSET_GPR);
    Reg left, right;
    if (irref_isk(ir->op1)) {
      int32_t k = IR(ir->op1)->i;
      if (checki16(k)) {
	right = ra_alloc1(as, ir->op2, RSET_GPR);
	emit_tai(as, PPCI_SUBFIC, dest, right, k);
	return;
      }
    }
    /* May fail due to spills/restores above, but simplifies the logic. */
    if (as->flagmcp == as->mcp) {
      as->flagmcp = NULL;
      as->mcp++;
      pi |= PPCF_DOT;
    }
    left = ra_hintalloc(as, ir->op1, dest, RSET_GPR);
    right = ra_alloc1(as, ir->op2, rset_exclude(RSET_GPR, left));
    emit_tab(as, pi, dest, right, left);  /* Subtract right _from_ left. */
  }
}
#endif

#if LJ_ARCH_PPC64
static void asm_mul(ASMState *as, IRIns *ir)
{
  if (irt_isnum(ir->t)) {
    asm_fparith(as, ir, PPCI_FMUL);
  } else {
    /* mullw is the smull analogue: the 64-bit product of the low words,
    ** independent of the upper halves (D3, arith32.c); mulli likewise.
    ** 64-bit IR types (FFI) use mulld. No CR0 fusion (C21).
    */
    Reg dest = ra_dest(as, ir, RSET_GPR);
    Reg right, left = ra_hintalloc(as, ir->op1, dest, RSET_GPR);
    if (irref_isk(ir->op2)) {
      intptr_t k = get_kval(as, ir->op2);
      if (checki16(k)) {
	emit_tai(as, PPCI_MULLI, dest, left, (int32_t)k);
	return;
      }
    }
    right = ra_alloc1(as, ir->op2, rset_exclude(RSET_GPR, left));
    emit_tab(as, irt_is64(ir->t) ? PPCI_MULLD : PPCI_MULLW, dest, left, right);
  }
}
#else
static void asm_mul(ASMState *as, IRIns *ir)
{
#if !LJ_SOFTFP
  if (irt_isnum(ir->t)) {
    asm_fparith(as, ir, PPCI_FMUL);
  } else
#endif
  {
    PPCIns pi = PPCI_MULLW;
    Reg dest = ra_dest(as, ir, RSET_GPR);
    Reg right, left = ra_hintalloc(as, ir->op1, dest, RSET_GPR);
    if (irref_isk(ir->op2)) {
      int32_t k = IR(ir->op2)->i;
      if (checki16(k)) {
	emit_tai(as, PPCI_MULLI, dest, left, k);
	return;
      }
    }
    /* May fail due to spills/restores above, but simplifies the logic. */
    if (as->flagmcp == as->mcp) {
      as->flagmcp = NULL;
      as->mcp++;
      pi |= PPCF_DOT;
    }
    right = ra_alloc1(as, ir->op2, rset_exclude(RSET_GPR, left));
    emit_tab(as, pi, dest, left, right);
  }
}
#endif

#define asm_fpdiv(as, ir)	asm_fparith(as, ir, PPCI_FDIV)

#if LJ_ARCH_PPC64
static void asm_neg(ASMState *as, IRIns *ir)
{
  if (irt_isnum(ir->t)) {
    asm_fpunary(as, ir, PPCI_FNEG);
  } else {
    /* neg is width-agnostic: the low 32 bits of -x depend on x's low 32. */
    Reg dest = ra_dest(as, ir, RSET_GPR);
    Reg left = ra_hintalloc(as, ir->op1, dest, RSET_GPR);
    emit_tab(as, PPCI_NEG, dest, left, 0);
  }
}
#else
static void asm_neg(ASMState *as, IRIns *ir)
{
#if !LJ_SOFTFP
  if (irt_isnum(ir->t)) {
    asm_fpunary(as, ir, PPCI_FNEG);
  } else
#endif
  {
    Reg dest, left;
    PPCIns pi = PPCI_NEG;
    if (as->flagmcp == as->mcp) {
      as->flagmcp = NULL;
      as->mcp++;
      pi |= PPCF_DOT;
    }
    dest = ra_dest(as, ir, RSET_GPR);
    left = ra_hintalloc(as, ir->op1, dest, RSET_GPR);
    emit_tab(as, pi, dest, left, 0);
  }
}
#endif

#define asm_abs(as, ir)		asm_fpunary(as, ir, PPCI_FABS)

#if LJ_ARCH_PPC64
/* Overflow-checked 32-bit add/sub/mul (IR_ADDOV/SUBOV/MULOV), D5/3.7.
**
** ISA 3.0 (JIT_F_ISA30, the default on POWER9):
**   addo   d, a, b        (subfo d, b, a / mullwo d, a, b)
**   mcrxrx cr7            cr7: LT=OV GT=OV32 EQ=CA SO=CA32
**   bgt    cr7 -> exit
** OV32 is computed from the low words alone, so the tag garbage in the
** upper halves of IR ints (D3) cannot false-overflow -- the handbook's
** arith32.c shows add+extsw+cmpd is wrong on 5 of 8 such rows. OV/OV32 are
** rewritten by every OE=1 instruction: nothing is sticky, nothing is
** cleared. Reading LT (the 64-bit OV) here is the named control
** (LJ_TEST_BREAK_OVBIT): 2^31-1 + 1 then wraps silently.
**
** POWER8 (ISA 2.07, the floor, LUAJIT_PPC_ISA30=0 on this box):
**   sldi   r0,  a, 32
**   sldi   tmp, b, 32
**   addo.  r0, r0, tmp    64-bit overflow of the shifted words == 32-bit
**   add    d,  a, b       overflow of a+b; cr0.SO <- XER.SO
**   bso    -> exit
** cr0.SO is the *sticky* XER.SO, so XER must be zero when the trace is
** entered: the trace head clears it (as->xerclr, C9) at 37.5 ns per entry
** (C1) -- only traces that contain such a guard pay, and only on this
** path. mullwo. needs no shifts (mullw sign-interprets the low words).
** LJ_TEST_BREAK_P8OV drops the shifts: the 64-bit add then never
** overflows and the same rows wrap.
*/
static void asm_arithov(ASMState *as, IRIns *ir, PPCIns pi)
{
  Reg dest, left, right;
  lj_assertA(!irt_is64(ir->t), "bad usage");
  if ((as->flags & JIT_F_ISA30)) {
#ifdef LJ_TEST_BREAK_OVBIT
    asm_guardcr(as, PPC_CRF_OV, CC_LT);
#else
    asm_guardcr(as, PPC_CRF_OV, CC_GT);
#endif
    *--as->mcp = PPCI_MCRXRX | PPCF_CRF(PPC_CRF_OV);
    dest = ra_dest(as, ir, RSET_GPR);
    left = ra_alloc2(as, ir, RSET_GPR);
    right = (left >> 8); left &= 255;
    if (pi == PPCI_SUBFO) { Reg tmp = left; left = right; right = tmp; }
    emit_tab(as, pi, dest, left, right);
  } else {
    as->xerclr = 1;
    asm_guardcc(as, CC_SO);
    dest = ra_dest(as, ir, RSET_GPR);
    left = ra_alloc2(as, ir, RSET_GPR);
    right = (left >> 8); left &= 255;
    if (pi == PPCI_MULLWO) {
      emit_tab(as, PPCI_MULLWO|PPCF_DOT, dest, left, right);
    } else {
      Reg tmp = ra_scratch(as, rset_exclude(rset_exclude(rset_exclude(RSET_GPR,
					    dest), left), right));
      if (pi == PPCI_SUBFO) {
	emit_tab(as, PPCI_SUBF, dest, right, left);  /* left - right */
	emit_tab(as, PPCI_SUBFO|PPCF_DOT, RID_TMP, tmp, RID_TMP);
      } else {
	emit_tab(as, PPCI_ADD, dest, left, right);
	emit_tab(as, PPCI_ADDO|PPCF_DOT, RID_TMP, RID_TMP, tmp);
      }
#ifdef LJ_TEST_BREAK_P8OV
      emit_mr(as, tmp, right);
      emit_mr(as, RID_TMP, left);
#else
      emit_sldi(as, tmp, right, 32);
      emit_sldi(as, RID_TMP, left, 32);
#endif
    }
  }
}
#else
static void asm_arithov(ASMState *as, IRIns *ir, PPCIns pi)
{
  Reg dest, left, right;
  if (as->flagmcp == as->mcp) {
    as->flagmcp = NULL;
    as->mcp++;
  }
  asm_guardcc(as, CC_SO);
  dest = ra_dest(as, ir, RSET_GPR);
  left = ra_alloc2(as, ir, RSET_GPR);
  right = (left >> 8); left &= 255;
  if (pi == PPCI_SUBFO) { Reg tmp = left; left = right; right = tmp; }
  emit_tab(as, pi|PPCF_DOT, dest, left, right);
}
#endif

#define asm_addov(as, ir)	asm_arithov(as, ir, PPCI_ADDO)
#define asm_subov(as, ir)	asm_arithov(as, ir, PPCI_SUBFO)
#define asm_mulov(as, ir)	asm_arithov(as, ir, PPCI_MULLWO)

#if LJ_HASFFI && LJ_32
static void asm_add64(ASMState *as, IRIns *ir)
{
  Reg dest = ra_dest(as, ir, RSET_GPR);
  Reg right, left = ra_alloc1(as, ir->op1, RSET_GPR);
  PPCIns pi = PPCI_ADDE;
  if (irref_isk(ir->op2)) {
    int32_t k = IR(ir->op2)->i;
    if (k == 0)
      pi = PPCI_ADDZE;
    else if (k == -1)
      pi = PPCI_ADDME;
    else
      goto needright;
    right = 0;
  } else {
  needright:
    right = ra_alloc1(as, ir->op2, rset_exclude(RSET_GPR, left));
  }
  emit_tab(as, pi, dest, left, right);
  ir--;
  dest = ra_dest(as, ir, RSET_GPR);
  left = ra_alloc1(as, ir->op1, RSET_GPR);
  if (irref_isk(ir->op2)) {
    int32_t k = IR(ir->op2)->i;
    if (checki16(k)) {
      emit_tai(as, PPCI_ADDIC, dest, left, k);
      return;
    }
  }
  right = ra_alloc1(as, ir->op2, rset_exclude(RSET_GPR, left));
  emit_tab(as, PPCI_ADDC, dest, left, right);
}

static void asm_sub64(ASMState *as, IRIns *ir)
{
  Reg dest = ra_dest(as, ir, RSET_GPR);
  Reg left, right = ra_alloc1(as, ir->op2, RSET_GPR);
  PPCIns pi = PPCI_SUBFE;
  if (irref_isk(ir->op1)) {
    int32_t k = IR(ir->op1)->i;
    if (k == 0)
      pi = PPCI_SUBFZE;
    else if (k == -1)
      pi = PPCI_SUBFME;
    else
      goto needleft;
    left = 0;
  } else {
  needleft:
    left = ra_alloc1(as, ir->op1, rset_exclude(RSET_GPR, right));
  }
  emit_tab(as, pi, dest, right, left);  /* Subtract right _from_ left. */
  ir--;
  dest = ra_dest(as, ir, RSET_GPR);
  right = ra_alloc1(as, ir->op2, RSET_GPR);
  if (irref_isk(ir->op1)) {
    int32_t k = IR(ir->op1)->i;
    if (checki16(k)) {
      emit_tai(as, PPCI_SUBFIC, dest, right, k);
      return;
    }
  }
  left = ra_alloc1(as, ir->op1, rset_exclude(RSET_GPR, right));
  emit_tab(as, PPCI_SUBFC, dest, right, left);
}

static void asm_neg64(ASMState *as, IRIns *ir)
{
  Reg dest = ra_dest(as, ir, RSET_GPR);
  Reg left = ra_alloc1(as, ir->op1, RSET_GPR);
  emit_tab(as, PPCI_SUBFZE, dest, left, 0);
  ir--;
  dest = ra_dest(as, ir, RSET_GPR);
  left = ra_alloc1(as, ir->op1, RSET_GPR);
  emit_tai(as, PPCI_SUBFIC, dest, left, 0);
}
#endif

#if LJ_ARCH_PPC64
static void asm_bnot(ASMState *as, IRIns *ir)
{
  Reg dest, left, right;
  PPCIns pi = PPCI_NOR;  /* nor/nand/eqv are width-agnostic. */
  dest = ra_dest(as, ir, RSET_GPR);
  if (mayfuse(as, ir->op1)) {
    IRIns *irl = IR(ir->op1);
    if (irl->o == IR_BAND)
      pi = PPCI_NAND;
    else if (irl->o == IR_BXOR)
      pi = PPCI_EQV;
    else if (irl->o != IR_BOR)
      goto nofuse;
    left = ra_hintalloc(as, irl->op1, dest, RSET_GPR);
    right = ra_alloc1(as, irl->op2, rset_exclude(RSET_GPR, left));
  } else {
nofuse:
    left = right = ra_hintalloc(as, ir->op1, dest, RSET_GPR);
  }
  emit_asb(as, pi, dest, left, right);
}
#else
static void asm_bnot(ASMState *as, IRIns *ir)
{
  Reg dest, left, right;
  PPCIns pi = PPCI_NOR;
  if (as->flagmcp == as->mcp) {
    as->flagmcp = NULL;
    as->mcp++;
    pi |= PPCF_DOT;
  }
  dest = ra_dest(as, ir, RSET_GPR);
  if (mayfuse(as, ir->op1)) {
    IRIns *irl = IR(ir->op1);
    if (irl->o == IR_BAND)
      pi ^= (PPCI_NOR ^ PPCI_NAND);
    else if (irl->o == IR_BXOR)
      pi ^= (PPCI_NOR ^ PPCI_EQV);
    else if (irl->o != IR_BOR)
      goto nofuse;
    left = ra_hintalloc(as, irl->op1, dest, RSET_GPR);
    right = ra_alloc1(as, irl->op2, rset_exclude(RSET_GPR, left));
  } else {
nofuse:
    left = right = ra_hintalloc(as, ir->op1, dest, RSET_GPR);
  }
  emit_asb(as, pi, dest, left, right);
}
#endif

#if LJ_ARCH_PPC64
static void asm_bswap(ASMState *as, IRIns *ir)
{
  Reg dest = ra_dest(as, ir, RSET_GPR);
  IRIns *irx;
  int is64 = irt_is64(ir->t);
  if (mayfuse(as, ir->op1) && (irx = IR(ir->op1))->o == IR_XLOAD &&
      ra_noreg(irx->r) &&
      (is64 ? (irt_isi64(irx->t) || irt_isu64(irx->t)) :
	      (irt_isint(irx->t) || irt_isu32(irx->t)))) {
    /* Fuse BSWAP with XLOAD to lwbrx/ldbrx. */
    asm_fusexrefx(as, is64 ? PPCI_LDBRX : PPCI_LWBRX, dest, irx->op1, RSET_GPR);
  } else {
    Reg left = ra_alloc1(as, ir->op1, RSET_GPR);
    if (is64) {
      /* No register byte-reverse before POWER10: go through the LR save
      ** doubleword (SPOFS_TMP, dead between calls): addi r0,sp,16;
      ** stdbrx left,0,r0; ld dest,16(sp).
      */
      emit_tai(as, PPCI_LD, dest, RID_SP, SPOFS_TMP);
      emit_tab(as, PPCI_STDBRX, left, 0, RID_TMP);
      emit_tai(as, PPCI_ADDI, RID_TMP, RID_SP, SPOFS_TMP);
    } else {
      /* rotlwi/rlwimi work on the low word and leave a zero-extended
      ** result: garbage-tolerant either way (D3).
      */
      Reg tmp = dest;
      if (tmp == left) {
	tmp = RID_TMP;
	emit_mr(as, dest, RID_TMP);
      }
      emit_rot(as, PPCI_RLWIMI, tmp, left, 24, 16, 23);
      emit_rot(as, PPCI_RLWIMI, tmp, left, 24, 0, 7);
      emit_rotlwi(as, tmp, left, 8);
    }
  }
}
#else
static void asm_bswap(ASMState *as, IRIns *ir)
{
  Reg dest = ra_dest(as, ir, RSET_GPR);
  IRIns *irx;
  if (mayfuse(as, ir->op1) && (irx = IR(ir->op1))->o == IR_XLOAD &&
      ra_noreg(irx->r) && (irt_isint(irx->t) || irt_isu32(irx->t))) {
    /* Fuse BSWAP with XLOAD to lwbrx. */
    asm_fusexrefx(as, PPCI_LWBRX, dest, irx->op1, RSET_GPR);
  } else {
    Reg left = ra_alloc1(as, ir->op1, RSET_GPR);
    Reg tmp = dest;
    if (tmp == left) {
      tmp = RID_TMP;
      emit_mr(as, dest, RID_TMP);
    }
    emit_rot(as, PPCI_RLWIMI, tmp, left, 24, 16, 23);
    emit_rot(as, PPCI_RLWIMI, tmp, left, 24, 0, 7);
    emit_rotlwi(as, tmp, left, 8);
  }
}
#endif

/* Fuse BAND with contiguous bitmask and a shift to rlwinm. */
static void asm_fuseandsh(ASMState *as, PPCIns pi, int32_t mask, IRRef ref)
{
  IRIns *ir;
  Reg left;
  if (mayfuse(as, ref) && (ir = IR(ref), ra_noreg(ir->r)) &&
      irref_isk(ir->op2) && ir->o >= IR_BSHL && ir->o <= IR_BROR) {
    int32_t sh = (IR(ir->op2)->i & 31);
    switch (ir->o) {
    case IR_BSHL:
      if ((mask & ((1u<<sh)-1))) goto nofuse;
      break;
    case IR_BSHR:
      if ((mask & ~((~0u)>>sh))) goto nofuse;
      sh = ((32-sh)&31);
      break;
    case IR_BROL:
      break;
    default:
      goto nofuse;
    }
    left = ra_alloc1(as, ir->op1, RSET_GPR);
    *--as->mcp = pi | PPCF_T(left) | PPCF_B(sh);
    return;
  }
nofuse:
  left = ra_alloc1(as, ref, RSET_GPR);
  *--as->mcp = pi | PPCF_T(left);
}

#if LJ_ARCH_PPC64
static void asm_band(ASMState *as, IRIns *ir)
{
  Reg dest, left, right;
  IRRef lref = ir->op1;
  IRRef op2;
  int is64 = irt_is64(ir->t);
  dest = ra_dest(as, ir, RSET_GPR);
  if (irref_isk(ir->op2)) {
    intptr_t k = get_kval(as, ir->op2);
    uint64_t u = is64 ? (uint64_t)k : (uint64_t)(uint32_t)k;
    if (!is64 && (uint32_t)u) {
      /* 32 bit: a contiguous (or wrapped) bitmask folds into rlwinm,
      ** possibly together with a shift of the operand (asm_fuseandsh).
      */
      uint32_t s1 = lj_ffs((uint32_t)u);
      uint32_t k1 = ((uint32_t)u >> s1);
      if ((k1 & (k1+1)) == 0) {
	asm_fuseandsh(as, PPCI_RLWINM | PPCF_A(dest) |
			  PPCF_MB(31-lj_fls((uint32_t)u)) | PPCF_ME(31-s1),
			  (int32_t)u, lref);
	return;
      }
      if (~(uint32_t)u) {
	uint32_t s2 = lj_ffs(~(uint32_t)u);
	uint32_t k2 = (~(uint32_t)u >> s2);
	if ((k2 & (k2+1)) == 0) {
	  asm_fuseandsh(as, PPCI_RLWINM | PPCF_A(dest) |
			    PPCF_MB(32-s2) | PPCF_ME(30-lj_fls(~(uint32_t)u)),
			    (int32_t)u, lref);
	  return;
	}
      }
    }
    /* andi./andis. zero everything above the 16 mask bits: right for
    ** both widths. Their CR0 write is dead (no CR0 fusion on PPC64).
    */
    if ((u >> 16) == 0) {
      left = ra_alloc1(as, lref, RSET_GPR);
      emit_asi(as, PPCI_ANDIDOT, dest, left, (int32_t)u);
      return;
    } else if ((u & 0xffff) == 0 && (u >> 32) == 0) {
      left = ra_alloc1(as, lref, RSET_GPR);
      emit_asi(as, PPCI_ANDISDOT, dest, left, (int32_t)(u >> 16));
      return;
    } else if (is64 && (u & (u+1)) == 0) {  /* Low ones: clrldi. */
      left = ra_alloc1(as, lref, RSET_GPR);
      emit_clrldi(as, dest, left, 63 - (int32_t)lj_fls64(u));
      return;
    } else if (is64 && ~u != 0 && ((~u) & (~u+1)) == 0) {  /* High ones. */
      left = ra_alloc1(as, lref, RSET_GPR);
      emit_clrrdi(as, dest, left, (int32_t)lj_fls64(~u) + 1);
      return;
    }
  }
  op2 = ir->op2;
  if (mayfuse(as, op2) && IR(op2)->o == IR_BNOT && ra_noreg(IR(op2)->r)) {
    left = ra_hintalloc(as, lref, dest, RSET_GPR);
    right = ra_alloc1(as, IR(op2)->op1, rset_exclude(RSET_GPR, left));
    emit_asb(as, PPCI_ANDC, dest, left, right);
    return;
  }
  left = ra_hintalloc(as, lref, dest, RSET_GPR);
  right = ra_alloc1(as, op2, rset_exclude(RSET_GPR, left));
  emit_asb(as, PPCI_AND, dest, left, right);
}
#else
static void asm_band(ASMState *as, IRIns *ir)
{
  Reg dest, left, right;
  IRRef lref = ir->op1;
  PPCIns dot = 0;
  IRRef op2;
  if (as->flagmcp == as->mcp) {
    as->flagmcp = NULL;
    as->mcp++;
    dot = PPCF_DOT;
  }
  dest = ra_dest(as, ir, RSET_GPR);
  if (irref_isk(ir->op2)) {
    int32_t k = IR(ir->op2)->i;
    if (k) {
      /* First check for a contiguous bitmask as used by rlwinm. */
      uint32_t s1 = lj_ffs((uint32_t)k);
      uint32_t k1 = ((uint32_t)k >> s1);
      if ((k1 & (k1+1)) == 0) {
	asm_fuseandsh(as, PPCI_RLWINM|dot | PPCF_A(dest) |
			  PPCF_MB(31-lj_fls((uint32_t)k)) | PPCF_ME(31-s1),
			  k, lref);
	return;
      }
      if (~(uint32_t)k) {
	uint32_t s2 = lj_ffs(~(uint32_t)k);
	uint32_t k2 = (~(uint32_t)k >> s2);
	if ((k2 & (k2+1)) == 0) {
	  asm_fuseandsh(as, PPCI_RLWINM|dot | PPCF_A(dest) |
			    PPCF_MB(32-s2) | PPCF_ME(30-lj_fls(~(uint32_t)k)),
			    k, lref);
	  return;
	}
      }
    }
    if (checku16(k)) {
      left = ra_alloc1(as, lref, RSET_GPR);
      emit_asi(as, PPCI_ANDIDOT, dest, left, k);
      return;
    } else if ((k & 0xffff) == 0) {
      left = ra_alloc1(as, lref, RSET_GPR);
      emit_asi(as, PPCI_ANDISDOT, dest, left, (k >> 16));
      return;
    }
  }
  op2 = ir->op2;
  if (mayfuse(as, op2) && IR(op2)->o == IR_BNOT && ra_noreg(IR(op2)->r)) {
    dot ^= (PPCI_AND ^ PPCI_ANDC);
    op2 = IR(op2)->op1;
  }
  left = ra_hintalloc(as, lref, dest, RSET_GPR);
  right = ra_alloc1(as, op2, rset_exclude(RSET_GPR, left));
  emit_asb(as, PPCI_AND ^ dot, dest, left, right);
}
#endif

#if LJ_ARCH_PPC64
static void asm_bitop(ASMState *as, IRIns *ir, PPCIns pi, PPCIns pik)
{
  Reg dest = ra_dest(as, ir, RSET_GPR);
  Reg right, left = ra_hintalloc(as, ir->op1, dest, RSET_GPR);
  if (irref_isk(ir->op2)) {
    intptr_t k = get_kval(as, ir->op2);
    /* ori/oris/xori/xoris take zero-extended 16-bit immediates and touch
    ** only the low 32 bits: usable for any constant below 2^32 (as the
    ** 32-bit pattern for 32-bit IR types, whatever its sign).
    */
    uint64_t u = irt_is64(ir->t) ? (uint64_t)k : (uint64_t)(uint32_t)k;
    if ((u >> 32) == 0) {
      Reg tmp = left;
      if ((u >> 16) == 0 || (u & 0xffff) == 0 || (tmp = dest, !as->sectref)) {
	if ((u >> 16) != 0) {
	  emit_asi(as, pik ^ (PPCI_ORI ^ PPCI_ORIS), dest, tmp, (int32_t)(u >> 16));
	  if ((u & 0xffff) == 0) return;
	}
	emit_asi(as, pik, dest, left, (int32_t)(u & 0xffff));
	return;
      }
    }
  }
  right = ra_alloc1(as, ir->op2, rset_exclude(RSET_GPR, left));
  emit_asb(as, pi, dest, left, right);
}
#else
static void asm_bitop(ASMState *as, IRIns *ir, PPCIns pi, PPCIns pik)
{
  Reg dest = ra_dest(as, ir, RSET_GPR);
  Reg right, left = ra_hintalloc(as, ir->op1, dest, RSET_GPR);
  if (irref_isk(ir->op2)) {
    int32_t k = IR(ir->op2)->i;
    Reg tmp = left;
    if ((checku16(k) || (k & 0xffff) == 0) || (tmp = dest, !as->sectref)) {
      if (!checku16(k)) {
	emit_asi(as, pik ^ (PPCI_ORI ^ PPCI_ORIS), dest, tmp, (k >> 16));
	if ((k & 0xffff) == 0) return;
      }
      emit_asi(as, pik, dest, left, k);
      return;
    }
  }
  /* May fail due to spills/restores above, but simplifies the logic. */
  if (as->flagmcp == as->mcp) {
    as->flagmcp = NULL;
    as->mcp++;
    pi |= PPCF_DOT;
  }
  right = ra_alloc1(as, ir->op2, rset_exclude(RSET_GPR, left));
  emit_asb(as, pi, dest, left, right);
}
#endif

#define asm_bor(as, ir)		asm_bitop(as, ir, PPCI_OR, PPCI_ORI)
#define asm_bxor(as, ir)	asm_bitop(as, ir, PPCI_XOR, PPCI_XORI)

#if LJ_ARCH_PPC64
/* Shifts. 32 bit: slw/srw/sraw and their rlwinm/srawi immediate forms use
** the low word and leave a zero- or sign-extended result (D3). Counts are
** masked by the recorder (LJ_TARGET_MASKSHIFT 0: BAND 31 / BAND 63), which
** slw/sld require -- a count >= 32/64 yields zero, not a masked shift.
** 64 bit (FFI): sld/srd/srad/rldcl and rldicr/rldicl/sradi.
*/
static void asm_bitshift(ASMState *as, IRIns *ir, IROp op)
{
  Reg dest = ra_dest(as, ir, RSET_GPR);
  Reg left = ra_alloc1(as, ir->op1, RSET_GPR);
  if (irt_is64(ir->t)) {
    if (irref_isk(ir->op2)) {  /* Constant shifts. */
      int32_t sh = (int32_t)(get_kval(as, ir->op2) & 63);
      switch (op) {
      case IR_BSHL: emit_rotd(as, PPCI_RLDICR, dest, left, sh, 63-sh); break;
      case IR_BSHR: emit_rotd(as, PPCI_RLDICL, dest, left, (64-sh)&63, sh); break;
      case IR_BSAR: emit_sradi(as, dest, left, sh); break;
      default: emit_rotd(as, PPCI_RLDICL, dest, left, sh, 0); break;  /* rotldi */
      }
    } else {
      Reg right = ra_alloc1(as, ir->op2, rset_exclude(RSET_GPR, left));
      switch (op) {
      case IR_BSHL: emit_asb(as, PPCI_SLD, dest, left, right); break;
      case IR_BSHR: emit_asb(as, PPCI_SRD, dest, left, right); break;
      case IR_BSAR: emit_asb(as, PPCI_SRAD, dest, left, right); break;
      default:  /* rotld = rldcl dest,left,right,0 */
	*--as->mcp = PPCI_RLDCL | PPCF_T(left) | PPCF_A(dest) | PPCF_B(right) |
		     PPCF_M6(0);
	break;
      }
    }
  } else {
    if (irref_isk(ir->op2)) {  /* Constant shifts. */
      int32_t sh = (IR(ir->op2)->i & 31);
      switch (op) {
      case IR_BSHL: emit_rot(as, PPCI_RLWINM, dest, left, sh, 0, 31-sh); break;
      case IR_BSHR: emit_rot(as, PPCI_RLWINM, dest, left, (32-sh)&31, sh, 31); break;
      case IR_BSAR: emit_asb(as, PPCI_SRAWI, dest, left, sh); break;
      default: emit_rot(as, PPCI_RLWINM, dest, left, sh, 0, 31); break;  /* rotlwi */
      }
    } else {
      Reg right = ra_alloc1(as, ir->op2, rset_exclude(RSET_GPR, left));
      switch (op) {
      case IR_BSHL: emit_asb(as, PPCI_SLW, dest, left, right); break;
      case IR_BSHR: emit_asb(as, PPCI_SRW, dest, left, right); break;
      case IR_BSAR: emit_asb(as, PPCI_SRAW, dest, left, right); break;
      default:  /* rotlw = rlwnm dest,left,right,0,31 */
	emit_asb(as, PPCI_RLWNM|PPCF_MB(0)|PPCF_ME(31), dest, left, right);
	break;
      }
    }
  }
}

#define asm_bshl(as, ir)	asm_bitshift(as, ir, IR_BSHL)
#define asm_bshr(as, ir)	asm_bitshift(as, ir, IR_BSHR)
#define asm_bsar(as, ir)	asm_bitshift(as, ir, IR_BSAR)
#define asm_brol(as, ir)	asm_bitshift(as, ir, IR_BROL)
#define asm_bror(as, ir)	lj_assertA(0, "unexpected BROR")
#else
static void asm_bitshift(ASMState *as, IRIns *ir, PPCIns pi, PPCIns pik)
{
  Reg dest, left;
  Reg dot = 0;
  if (as->flagmcp == as->mcp) {
    as->flagmcp = NULL;
    as->mcp++;
    dot = PPCF_DOT;
  }
  dest = ra_dest(as, ir, RSET_GPR);
  left = ra_alloc1(as, ir->op1, RSET_GPR);
  if (irref_isk(ir->op2)) {  /* Constant shifts. */
    int32_t shift = (IR(ir->op2)->i & 31);
    if (pik == 0)  /* SLWI */
      emit_rot(as, PPCI_RLWINM|dot, dest, left, shift, 0, 31-shift);
    else if (pik == 1)  /* SRWI */
      emit_rot(as, PPCI_RLWINM|dot, dest, left, (32-shift)&31, shift, 31);
    else
      emit_asb(as, pik|dot, dest, left, shift);
  } else {
    Reg right = ra_alloc1(as, ir->op2, rset_exclude(RSET_GPR, left));
    emit_asb(as, pi|dot, dest, left, right);
  }
}

#define asm_bshl(as, ir)	asm_bitshift(as, ir, PPCI_SLW, 0)
#define asm_bshr(as, ir)	asm_bitshift(as, ir, PPCI_SRW, 1)
#define asm_bsar(as, ir)	asm_bitshift(as, ir, PPCI_SRAW, PPCI_SRAWI)
#define asm_brol(as, ir) \
  asm_bitshift(as, ir, PPCI_RLWNM|PPCF_MB(0)|PPCF_ME(31), \
		       PPCI_RLWINM|PPCF_MB(0)|PPCF_ME(31))
#define asm_bror(as, ir)	lj_assertA(0, "unexpected BROR")
#endif

#if LJ_SOFTFP
static void asm_sfpmin_max(ASMState *as, IRIns *ir)
{
  CCallInfo ci = lj_ir_callinfo[IRCALL_softfp_cmp];
  IRRef args[4];
  MCLabel l_right, l_end;
  Reg desthi = ra_dest(as, ir, RSET_GPR), destlo = ra_dest(as, ir+1, RSET_GPR);
  Reg righthi, lefthi = ra_alloc2(as, ir, RSET_GPR);
  Reg rightlo, leftlo = ra_alloc2(as, ir+1, RSET_GPR);
  PPCCC cond = (IROp)ir->o == IR_MIN ? CC_EQ : CC_NE;
  righthi = (lefthi >> 8); lefthi &= 255;
  rightlo = (leftlo >> 8); leftlo &= 255;
  args[0^LJ_BE] = ir->op1; args[1^LJ_BE] = (ir+1)->op1;
  args[2^LJ_BE] = ir->op2; args[3^LJ_BE] = (ir+1)->op2;
  l_end = emit_label(as);
  if (desthi != righthi) emit_mr(as, desthi, righthi);
  if (destlo != rightlo) emit_mr(as, destlo, rightlo);
  l_right = emit_label(as);
  if (l_end != l_right) emit_jmp(as, l_end);
  if (desthi != lefthi) emit_mr(as, desthi, lefthi);
  if (destlo != leftlo) emit_mr(as, destlo, leftlo);
  if (l_right == as->mcp+1) {
    cond ^= 4; l_right = l_end; ++as->mcp;
  }
  emit_condbranch(as, PPCI_BC, cond, l_right);
  ra_evictset(as, RSET_SCRATCH);
  emit_cmpi(as, RID_RET, 1);
  asm_gencall(as, &ci, args);
}
#endif

#if LJ_ARCH_PPC64
/* IR_MIN/IR_MAX are defined by the fold (lj_vm_foldarith): x < y ? x : y
** and x > y ? x : y, so a NaN in either operand and an equal pair (+0/-0)
** both yield the *right* operand. The ppc32 fsub+fsel form yields the left
** one on NaN and the wrong zero for max, so it is replaced by fcmpu and a
** branch (a bge/ble after fcmpu fires on unordered, which is exactly what
** is wanted here: NaN -> right). Integers: cmpw + isel.
*/
static void asm_min_max(ASMState *as, IRIns *ir, int ismax)
{
  if (irt_isnum(ir->t)) {
    Reg dest = ra_dest(as, ir, RSET_FPR);
    Reg right, left = ra_alloc2(as, ir, RSET_FPR);
    MCLabel l_end;
    right = (left >> 8); left &= 255;
    l_end = emit_label(as);
    if (dest == left) {
      /* fcmpu; b<lt|gt> l_end; fmr dest,right; l_end: */
      emit_fb(as, PPCI_FMR, dest, right);
      emit_condbranch(as, PPCI_BC, ismax ? CC_GT : CC_LT, l_end);
    } else {
      /* fcmpu; [fmr dest,right]; b<!lt|!gt> l_end; fmr dest,left; l_end: */
      emit_fb(as, PPCI_FMR, dest, left);
      emit_condbranch(as, PPCI_BC, ismax ? CC_LE : CC_GE, l_end);
      if (dest != right) emit_fb(as, PPCI_FMR, dest, right);
    }
    emit_fab(as, PPCI_FCMPU, 0, left, right);
  } else {
    Reg dest = ra_dest(as, ir, RSET_GPR);
    Reg right, left = ra_alloc2(as, ir, RSET_GPR);
    right = (left >> 8); left &= 255;
    /* cmpw left,right; isel dest, left, right, cr0.LT (min) / cr0.GT (max) */
    emit_isel(as, dest, left, right, ismax ? 1 : 0);
    emit_tab(as, PPCI_CMPW, PPC_CRF_CMP, left, right);
  }
}
#else
static void asm_min_max(ASMState *as, IRIns *ir, int ismax)
{
  if (!LJ_SOFTFP && irt_isnum(ir->t)) {
    Reg dest = ra_dest(as, ir, RSET_FPR);
    Reg tmp = dest;
    Reg right, left = ra_alloc2(as, ir, RSET_FPR);
    right = (left >> 8); left &= 255;
    if (tmp == left || tmp == right)
      tmp = ra_scratch(as, rset_exclude(rset_exclude(rset_exclude(RSET_FPR,
					dest), left), right));
    emit_facb(as, PPCI_FSEL, dest, tmp, left, right);
    emit_fab(as, PPCI_FSUB, tmp, ismax ? left : right, ismax ? right : left);
  } else {
    Reg dest = ra_dest(as, ir, RSET_GPR);
    Reg tmp1 = RID_TMP, tmp2 = dest;
    Reg right, left = ra_alloc2(as, ir, RSET_GPR);
    right = (left >> 8); left &= 255;
    if (tmp2 == left || tmp2 == right)
      tmp2 = ra_scratch(as, rset_exclude(rset_exclude(rset_exclude(RSET_GPR,
					 dest), left), right));
    emit_tab(as, PPCI_ADD, dest, tmp2, right);
    emit_asb(as, ismax ? PPCI_ANDC : PPCI_AND, tmp2, tmp2, tmp1);
    emit_tab(as, PPCI_SUBFE, tmp1, tmp1, tmp1);
    emit_tab(as, PPCI_SUBFC, tmp2, tmp2, tmp1);
    emit_asi(as, PPCI_XORIS, tmp2, right, 0x8000);
    emit_asi(as, PPCI_XORIS, tmp1, left, 0x8000);
  }
}
#endif

#define asm_min(as, ir)		asm_min_max(as, ir, 0)
#define asm_max(as, ir)		asm_min_max(as, ir, 1)

/* -- Comparisons --------------------------------------------------------- */

#define CC_UNSIGNED	0x08	/* Unsigned integer comparison. */
#define CC_TWO		0x80	/* Check two flags for FP comparison. */

/* Map of comparisons to flags. ORDER IR. */
static const uint8_t asm_compmap[IR_ABC+1] = {
  /* op     int cc                 FP cc */
  /* LT  */ CC_GE               + (CC_GE<<4),
  /* GE  */ CC_LT               + (CC_LE<<4) + CC_TWO,
  /* LE  */ CC_GT               + (CC_GE<<4) + CC_TWO,
  /* GT  */ CC_LE               + (CC_LE<<4),
  /* ULT */ CC_GE + CC_UNSIGNED + (CC_GT<<4) + CC_TWO,
  /* UGE */ CC_LT + CC_UNSIGNED + (CC_LT<<4),
  /* ULE */ CC_GT + CC_UNSIGNED + (CC_GT<<4),
  /* UGT */ CC_LE + CC_UNSIGNED + (CC_LT<<4) + CC_TWO,
  /* EQ  */ CC_NE               + (CC_NE<<4),
  /* NE  */ CC_EQ               + (CC_EQ<<4),
  /* ABC */ CC_LE + CC_UNSIGNED + (CC_LT<<4) + CC_TWO  /* Same as UGT. */
};

#if LJ_ARCH_PPC64
/* Integer or pointer compare. is64 selects cmpd/cmpld (64-bit IR types)
** over cmpw/cmplw, which compare the low word only (D3). The ppc32 CR0
** fusion (as->flagmcp) is never armed on PPC64.
*/
static void asm_intcomp_(ASMState *as, IRRef lref, IRRef rref, Reg cr,
			 PPCCC cc, int is64)
{
  Reg right, left = ra_alloc1(as, lref, RSET_GPR);
  if (irref_isk(rref)) {
    intptr_t k = get_kval(as, rref);
    if ((cc & CC_UNSIGNED) == 0) {  /* Signed comparison with constant. */
      if (checki16(k)) {
	emit_tai(as, is64 ? PPCI_CMPDI : PPCI_CMPWI, cr, left, (int32_t)k);
	return;
      } else if ((cc & 3) == (CC_EQ & 3) && !is64) {  /* CMPLWI for EQ or NE. */
	if (checku16(k)) {
	  emit_tai(as, PPCI_CMPLWI, cr, left, (int32_t)k);
	  return;
	} else if (!as->sectref && ra_noreg(IR(rref)->r)) {
	  emit_tai(as, PPCI_CMPLWI, cr, RID_TMP, (int32_t)k);
	  emit_asi(as, PPCI_XORIS, RID_TMP, left, (int32_t)(k >> 16));
	  return;
	}
      }
    } else {  /* Unsigned comparison with constant. */
      if (checku16(k)) {
	emit_tai(as, is64 ? PPCI_CMPLDI : PPCI_CMPLWI, cr, left, (int32_t)k);
	return;
      }
    }
    if (is64 && (cc & 3) == (CC_EQ & 3) && checku16(k)) {  /* 64-bit EQ/NE. */
      emit_tai(as, PPCI_CMPLDI, cr, left, (int32_t)k);
      return;
    }
  }
  right = ra_alloc1(as, rref, rset_exclude(RSET_GPR, left));
  emit_tab(as, (cc & CC_UNSIGNED) ? (is64 ? PPCI_CMPLD : PPCI_CMPLW) :
				    (is64 ? PPCI_CMPD : PPCI_CMPW),
	   cr, left, right);
}
#else
static void asm_intcomp_(ASMState *as, IRRef lref, IRRef rref, Reg cr, PPCCC cc)
{
  Reg right, left = ra_alloc1(as, lref, RSET_GPR);
  if (irref_isk(rref)) {
    int32_t k = IR(rref)->i;
    if ((cc & CC_UNSIGNED) == 0) {  /* Signed comparison with constant. */
      if (checki16(k)) {
	emit_tai(as, PPCI_CMPWI, cr, left, k);
	/* Signed comparison with zero and referencing previous ins? */
	if (k == 0 && lref == as->curins-1)
	  as->flagmcp = as->mcp;  /* Allow elimination of the compare. */
	return;
      } else if ((cc & 3) == (CC_EQ & 3)) {  /* Use CMPLWI for EQ or NE. */
	if (checku16(k)) {
	  emit_tai(as, PPCI_CMPLWI, cr, left, k);
	  return;
	} else if (!as->sectref && ra_noreg(IR(rref)->r)) {
	  emit_tai(as, PPCI_CMPLWI, cr, RID_TMP, k);
	  emit_asi(as, PPCI_XORIS, RID_TMP, left, (k >> 16));
	  return;
	}
      }
    } else {  /* Unsigned comparison with constant. */
      if (checku16(k)) {
	emit_tai(as, PPCI_CMPLWI, cr, left, k);
	return;
      }
    }
  }
  right = ra_alloc1(as, rref, rset_exclude(RSET_GPR, left));
  emit_tab(as, (cc & CC_UNSIGNED) ? PPCI_CMPLW : PPCI_CMPW, cr, left, right);
}
#endif

#if LJ_ARCH_PPC64
static void asm_comp(ASMState *as, IRIns *ir)
{
  PPCCC cc = asm_compmap[ir->o];
  if (irt_isnum(ir->t)) {
    Reg right, left = ra_alloc2(as, ir, RSET_FPR);
    right = (left >> 8); left &= 255;
    asm_guardcc(as, (cc >> 4));
    if ((cc & CC_TWO))
      emit_tab(as, PPCI_CROR, ((cc>>4)&3), ((cc>>4)&3), (CC_EQ&3));
    emit_fab(as, PPCI_FCMPU, 0, left, right);
  } else {
    IRRef lref = ir->op1, rref = ir->op2;
    if (irref_isk(lref) && !irref_isk(rref)) {
      /* Swap constants to the right (only for ABC). */
      IRRef tmp = lref; lref = rref; rref = tmp;
      if ((cc & 2) == 0) cc ^= 1;  /* LT <-> GT, LE <-> GE */
    }
    asm_guardcc(as, cc);
    asm_intcomp_(as, lref, rref, 0, cc, irt_is64(ir->t));
  }
}
#else
static void asm_comp(ASMState *as, IRIns *ir)
{
  PPCCC cc = asm_compmap[ir->o];
  if (!LJ_SOFTFP && irt_isnum(ir->t)) {
    Reg right, left = ra_alloc2(as, ir, RSET_FPR);
    right = (left >> 8); left &= 255;
    asm_guardcc(as, (cc >> 4));
    if ((cc & CC_TWO))
      emit_tab(as, PPCI_CROR, ((cc>>4)&3), ((cc>>4)&3), (CC_EQ&3));
    emit_fab(as, PPCI_FCMPU, 0, left, right);
  } else {
    IRRef lref = ir->op1, rref = ir->op2;
    if (irref_isk(lref) && !irref_isk(rref)) {
      /* Swap constants to the right (only for ABC). */
      IRRef tmp = lref; lref = rref; rref = tmp;
      if ((cc & 2) == 0) cc ^= 1;  /* LT <-> GT, LE <-> GE */
    }
    asm_guardcc(as, cc);
    asm_intcomp_(as, lref, rref, 0, cc);
  }
}
#endif

#define asm_equal(as, ir)	asm_comp(as, ir)

#if LJ_SOFTFP
/* SFP comparisons. */
static void asm_sfpcomp(ASMState *as, IRIns *ir)
{
  const CCallInfo *ci = &lj_ir_callinfo[IRCALL_softfp_cmp];
  RegSet drop = RSET_SCRATCH;
  Reg r;
  IRRef args[4];
  args[0^LJ_BE] = ir->op1; args[1^LJ_BE] = (ir+1)->op1;
  args[2^LJ_BE] = ir->op2; args[3^LJ_BE] = (ir+1)->op2;

  for (r = REGARG_FIRSTGPR; r <= REGARG_FIRSTGPR+3; r++) {
    if (!rset_test(as->freeset, r) &&
	regcost_ref(as->cost[r]) == args[r-REGARG_FIRSTGPR])
      rset_clear(drop, r);
  }
  ra_evictset(as, drop);
  asm_setupresult(as, ir, ci);
  switch ((IROp)ir->o) {
  case IR_ULT:
    asm_guardcc(as, CC_EQ);
    emit_ai(as, PPCI_CMPWI, RID_RET, 0);
  case IR_ULE:
    asm_guardcc(as, CC_EQ);
    emit_ai(as, PPCI_CMPWI, RID_RET, 1);
    break;
  case IR_GE: case IR_GT:
    asm_guardcc(as, CC_EQ);
    emit_ai(as, PPCI_CMPWI, RID_RET, 2);
  default:
    asm_guardcc(as, (asm_compmap[ir->o] & 0xf));
    emit_ai(as, PPCI_CMPWI, RID_RET, 0);
    break;
  }
  asm_gencall(as, ci, args);
}
#endif

#if LJ_HASFFI && LJ_32
/* 64 bit integer comparisons. */
#if !LJ_ARCH_PPC64  /* Split 32/32 compares never exist on PPC64. */
static void asm_comp64(ASMState *as, IRIns *ir)
{
  PPCCC cc = asm_compmap[(ir-1)->o];
  if ((cc&3) == (CC_EQ&3)) {
    asm_guardcc(as, cc);
    emit_tab(as, (cc&4) ? PPCI_CRAND : PPCI_CROR,
	     (CC_EQ&3), (CC_EQ&3), 4+(CC_EQ&3));
  } else {
    asm_guardcc(as, CC_EQ);
    emit_tab(as, PPCI_CROR, (CC_EQ&3), (CC_EQ&3), ((cc^~(cc>>2))&1));
    emit_tab(as, (cc&4) ? PPCI_CRAND : PPCI_CRANDC,
	     (CC_EQ&3), (CC_EQ&3), 4+(cc&3));
  }
  /* Loword comparison sets cr1 and is unsigned, except for equality. */
  asm_intcomp_(as, (ir-1)->op1, (ir-1)->op2, 4,
	       cc | ((cc&3) == (CC_EQ&3) ? 0 : CC_UNSIGNED));
  /* Hiword comparison sets cr0. */
  asm_intcomp_(as, ir->op1, ir->op2, 0, cc);
  as->flagmcp = NULL;  /* Doesn't work here. */
}
#endif
#endif

/* -- Split register ops -------------------------------------------------- */

/* Hiword op of a split 32/32 bit op. Previous op is be the loword op. */
static void asm_hiop(ASMState *as, IRIns *ir)
{
#if LJ_32
  /* HIOP is marked as a store because it needs its own DCE logic. */
  int uselo = ra_used(ir-1), usehi = ra_used(ir);  /* Loword/hiword used? */
  if (LJ_UNLIKELY(!(as->flags & JIT_F_OPT_DCE))) uselo = usehi = 1;
#if LJ_HASFFI || LJ_SOFTFP
  if ((ir-1)->o == IR_CONV) {  /* Conversions to/from 64 bit. */
    as->curins--;  /* Always skip the CONV. */
#if LJ_HASFFI && !LJ_SOFTFP
    if (usehi || uselo)
      asm_conv64(as, ir);
    return;
#endif
  } else if ((ir-1)->o <= IR_NE) {  /* 64 bit integer comparisons. ORDER IR. */
    as->curins--;  /* Always skip the loword comparison. */
#if LJ_SOFTFP
    if (!irt_isint(ir->t)) {
      asm_sfpcomp(as, ir-1);
      return;
    }
#endif
#if LJ_HASFFI
    asm_comp64(as, ir);
#endif
    return;
#if LJ_SOFTFP
  } else if ((ir-1)->o == IR_MIN || (ir-1)->o == IR_MAX) {
      as->curins--;  /* Always skip the loword min/max. */
    if (uselo || usehi)
      asm_sfpmin_max(as, ir-1);
    return;
#endif
  } else if ((ir-1)->o == IR_XSTORE) {
    as->curins--;  /* Handle both stores here. */
    if ((ir-1)->r != RID_SINK) {
      asm_xstore_(as, ir, 0);
      asm_xstore_(as, ir-1, 4);
    }
    return;
  }
#endif
  if (!usehi) return;  /* Skip unused hiword op for all remaining ops. */
  switch ((ir-1)->o) {
#if LJ_HASFFI
  case IR_ADD: as->curins--; asm_add64(as, ir); break;
  case IR_SUB: as->curins--; asm_sub64(as, ir); break;
  case IR_NEG: as->curins--; asm_neg64(as, ir); break;
  case IR_CNEWI:
    /* Nothing to do here. Handled by lo op itself. */
    break;
#endif
#if LJ_SOFTFP
  case IR_SLOAD: case IR_ALOAD: case IR_HLOAD: case IR_ULOAD: case IR_VLOAD:
  case IR_STRTO:
    if (!uselo)
      ra_allocref(as, ir->op1, RSET_GPR);  /* Mark lo op as used. */
    break;
  case IR_ASTORE: case IR_HSTORE: case IR_USTORE: case IR_TOSTR: case IR_TMPREF:
    /* Nothing to do here. Handled by lo op itself. */
    break;
#endif
  case IR_CALLN: case IR_CALLL: case IR_CALLS: case IR_CALLXS:
    if (!uselo)
      ra_allocref(as, ir->op1, RID2RSET(RID_RETLO));  /* Mark lo op as used. */
    break;
  default: lj_assertA(0, "bad HIOP for op %d", (ir-1)->o); break;
  }
#else
  /* PPC64: the only HIOP is the second result register of a call
  ** (lj_vm_next's continuation index in RID_RETHI = r4).
  */
  int uselo = ra_used(ir-1), usehi = ra_used(ir);  /* Loword/hiword used? */
  if (LJ_UNLIKELY(!(as->flags & JIT_F_OPT_DCE))) uselo = usehi = 1;
  if (!usehi) return;  /* Skip unused hiword op for all remaining ops. */
  switch ((ir-1)->o) {
  case IR_CALLN: case IR_CALLL: case IR_CALLS: case IR_CALLXS:
    if (!uselo)
      ra_allocref(as, ir->op1, RID2RSET(RID_RETLO));  /* Mark lo op as used. */
    break;
  default: lj_assertA(0, "bad HIOP for op %d", (ir-1)->o); break;
  }
#endif
}

/* -- Profiling ----------------------------------------------------------- */

/* PPC64: unchanged from ppc32. hookmask is a uint8_t (lbz off JGL through
** emit_lsglptr, the narrow-field form), andi. sets cr0 (PPC_CRF_CMP), the
** guard exits when HOOK_PROFILE is set so lj_trace_exit hands the sample
** to the profiler.
*/
static void asm_prof(ASMState *as, IRIns *ir)
{
  UNUSED(ir);
#ifdef LJ_TEST_BREAK_PROF
  asm_guardcc(as, CC_EQ);  /* Control (Phase 5): exits when NOT profiling. */
#else
  asm_guardcc(as, CC_NE);
#endif
  emit_asi(as, PPCI_ANDIDOT, RID_TMP, RID_TMP, HOOK_PROFILE);
  emit_lsglptr(as, PPCI_LBZ, RID_TMP,
	       (int32_t)offsetof(global_State, hookmask));
}

/* -- Stack handling ------------------------------------------------------ */

/* Check Lua stack size for overflow. Use exit handler as fallback. */
static void asm_stack_check(ASMState *as, BCReg topslot,
			    IRIns *irp, RegSet allow, ExitNo exitno)
{
  /* Try to get an unused temp. register, otherwise spill/restore RID_RET*. */
  Reg tmp, pbase = irp ? (ra_hasreg(irp->r) ? irp->r : RID_TMP) : RID_BASE;
  rset_clear(allow, pbase);
  tmp = allow ? rset_pickbot(allow) :
		(pbase == RID_RETHI ? RID_RETLO : RID_RETHI);
  emit_condbranch(as, PPCI_BC, CC_LT, asm_exitstub_addr(as, exitno));
#if LJ_ARCH_PPC64
  /* 64-bit pointers throughout; the scratch slot is the LR save doubleword
  ** at 16(sp), dead between calls (SPOFS_TMPW, see lj_target_ppc.h).
  */
  if (allow == RSET_EMPTY)  /* Restore temp. register. */
    emit_tai(as, PPCI_LD, tmp, RID_SP, SPOFS_TMPW);
  else
    ra_modified(as, tmp);
  emit_ai(as, PPCI_CMPLDI, RID_TMP, (int32_t)(8*topslot));
  emit_tab(as, PPCI_SUBF, RID_TMP, pbase, tmp);
  emit_tai(as, PPCI_LD, tmp, tmp, offsetof(lua_State, maxstack));
  if (pbase == RID_TMP)
    emit_getgl(as, RID_TMP, jit_base);
  emit_getgl(as, tmp, cur_L);
  if (allow == RSET_EMPTY)  /* Spill temp. register. */
    emit_tai(as, PPCI_STD, tmp, RID_SP, SPOFS_TMPW);
#else
  if (allow == RSET_EMPTY)  /* Restore temp. register. */
    emit_tai(as, PPCI_LWZ, tmp, RID_SP, SPOFS_TMPW);
  else
    ra_modified(as, tmp);
  emit_ai(as, PPCI_CMPLWI, RID_TMP, (int32_t)(8*topslot));
  emit_tab(as, PPCI_SUBF, RID_TMP, pbase, tmp);
  emit_tai(as, PPCI_LWZ, tmp, tmp, offsetof(lua_State, maxstack));
  if (pbase == RID_TMP)
    emit_getgl(as, RID_TMP, jit_base);
  emit_getgl(as, tmp, cur_L);
  if (allow == RSET_EMPTY)  /* Spill temp. register. */
    emit_tai(as, PPCI_STW, tmp, RID_SP, SPOFS_TMPW);
#endif
}

#if LJ_ARCH_PPC64
/* Restore Lua stack from on-trace state. */
static void asm_stack_restore(ASMState *as, SnapShot *snap)
{
  SnapEntry *map = &as->T->snapmap[snap->mapofs];
#ifdef LUA_USE_ASSERT
  SnapEntry *flinks = &as->T->snapmap[snap_nextofs(as->T, snap)-1-LJ_FR2];
#endif
  MSize n, nent = snap->nent;
  /* Store the value of all modified slots to the Lua stack. FR2 frame
  ** links arrive as KNUM constants (lj_snap.c snapshot_slots) and take
  ** the number path; nothing else is written for frames.
  */
  for (n = 0; n < nent; n++) {
    SnapEntry sn = map[n];
    BCReg s = snap_slot(sn);
    int32_t ofs = 8*((int32_t)s-1-LJ_FR2);
    IRRef ref = snap_ref(sn);
    IRIns *ir = IR(ref);
    if ((sn & SNAP_NORESTORE))
      continue;
    if ((sn & SNAP_KEYINDEX)) {
      /* ITERN control slot: (LJ_KEYINDEX << 32) | u32, as two word stores
      ** so the int payload never carries an int tag into the high word.
      */
      RegSet allow = rset_exclude(RSET_GPR, RID_BASE);
      Reg r = irref_isk(ref) ? ra_allock(as, ir->i, allow) :
			       ra_alloc1(as, ref, allow);
      rset_clear(allow, r);
      emit_tai(as, PPCI_STW, r, RID_BASE, ofs);
      emit_tai(as, PPCI_STW, ra_allock(as, (int32_t)LJ_KEYINDEX, allow),
	       RID_BASE, ofs+4);
    } else if (irt_isnum(ir->t)) {
      Reg src = ra_alloc1(as, ref, RSET_FPR);
      emit_fai(as, PPCI_STFD, src, RID_BASE, ofs);
    } else {
      asm_tvstore64(as, RID_BASE, ofs, ref);
    }
    checkmclim(as);
  }
  lj_assertA(map + nent == flinks, "inconsistent frames in snapshot");
}
#else
/* Restore Lua stack from on-trace state. */
static void asm_stack_restore(ASMState *as, SnapShot *snap)
{
  SnapEntry *map = &as->T->snapmap[snap->mapofs];
  SnapEntry *flinks = &as->T->snapmap[snap_nextofs(as->T, snap)-1];
  MSize n, nent = snap->nent;
#if LJ_ARCH_PPC64
  /* Phase 3: the stores below are ppc32 (32-bit it/gcr pairs). Until the
  ** GC64 version lands, a snapshot with entries cannot be restored; an
  ** empty one emits nothing and is fine.
  */
  if (nent) asm_nyi64_gate(as);
#endif
  /* Store the value of all modified slots to the Lua stack. */
  for (n = 0; n < nent; n++) {
    SnapEntry sn = map[n];
    BCReg s = snap_slot(sn);
    int32_t ofs = 8*((int32_t)s-1);
    IRRef ref = snap_ref(sn);
    IRIns *ir = IR(ref);
    if ((sn & SNAP_NORESTORE))
      continue;
    if (irt_isnum(ir->t)) {
#if LJ_SOFTFP
      Reg tmp;
      RegSet allow = rset_exclude(RSET_GPR, RID_BASE);
      /* LJ_SOFTFP: must be a number constant. */
      lj_assertA(irref_isk(ref), "unsplit FP op");
      tmp = ra_allock(as, (int32_t)ir_knum(ir)->u32.lo, allow);
      emit_tai(as, PPCI_STW, tmp, RID_BASE, ofs+(LJ_BE?4:0));
      if (rset_test(as->freeset, tmp+1)) allow = RID2RSET(tmp+1);
      tmp = ra_allock(as, (int32_t)ir_knum(ir)->u32.hi, allow);
      emit_tai(as, PPCI_STW, tmp, RID_BASE, ofs+(LJ_BE?0:4));
#else
      Reg src = ra_alloc1(as, ref, RSET_FPR);
      emit_fai(as, PPCI_STFD, src, RID_BASE, ofs);
#endif
    } else {
      Reg type;
      RegSet allow = rset_exclude(RSET_GPR, RID_BASE);
      lj_assertA(irt_ispri(ir->t) || irt_isaddr(ir->t) || irt_isinteger(ir->t),
		 "restore of IR type %d", irt_type(ir->t));
      if (!irt_ispri(ir->t)) {
	Reg src = ra_alloc1(as, ref, allow);
	rset_clear(allow, src);
	emit_tai(as, PPCI_STW, src, RID_BASE, ofs+4);
      }
      if ((sn & (SNAP_CONT|SNAP_FRAME))) {
	if (s == 0) continue;  /* Do not overwrite link to previous frame. */
	type = ra_allock(as, (int32_t)(*flinks--), allow);
#if LJ_SOFTFP
      } else if ((sn & SNAP_SOFTFPNUM)) {
	type = ra_alloc1(as, ref+1, rset_exclude(RSET_GPR, RID_BASE));
#endif
      } else if ((sn & SNAP_KEYINDEX)) {
	type = ra_allock(as, (int32_t)LJ_KEYINDEX, allow);
      } else {
	type = ra_allock(as, (int32_t)irt_toitype(ir->t), allow);
      }
      emit_tai(as, PPCI_STW, type, RID_BASE, ofs);
    }
    checkmclim(as);
  }
  lj_assertA(map + nent == flinks, "inconsistent frames in snapshot");
}
#endif

/* -- GC handling --------------------------------------------------------- */

/* Marker to prevent patching the GC check exit. */
#define PPC_NOPATCH_GC_CHECK	PPCI_ORIS

/* Check GC threshold and do one or more GC steps. */
static void asm_gc_check(ASMState *as)
{
  const CCallInfo *ci = &lj_ir_callinfo[IRCALL_lj_gc_step_jit];
  IRRef args[2];
  MCLabel l_end;
  Reg tmp;
  ra_evictset(as, RSET_SCRATCH);
  l_end = emit_label(as);
  /* Exit trace if in GCSatomic or GCSfinalize. Avoids syncing GC objects. */
  asm_guardcc(as, CC_NE);  /* Assumes asm_snap_prep() already done. */
  *--as->mcp = PPC_NOPATCH_GC_CHECK;
  emit_ai(as, PPCI_CMPWI, RID_RET, 0);
  args[0] = ASMREF_TMP1;  /* global_State *g */
  args[1] = ASMREF_TMP2;  /* MSize steps     */
  asm_gencall(as, ci, args);
  emit_tai(as, PPCI_ADDI, ra_releasetmp(as, ASMREF_TMP1), RID_JGL, -32768);
  tmp = ra_releasetmp(as, ASMREF_TMP2);
  emit_loadi(as, tmp, as->gcsteps);
  /* Jump around GC step if GC total < GC threshold. */
#ifdef LJ_TEST_BREAK_GCCHECK
  /* Control (Phase 5): inverted sense -- the step runs only while the heap
  ** is *below* its threshold and never once it is above, so an allocating
  ** loop that never leaves its trace grows the heap without bound.
  */
  emit_condbranch(as, PPCI_BC|PPCF_Y, CC_GE, l_end);
#else
  emit_condbranch(as, PPCI_BC|PPCF_Y, CC_LT, l_end);
#endif
  emit_ab(as, LJ_GC64 ? PPCI_CMPLD : PPCI_CMPLW, RID_TMP, tmp);  /* GCSize. */
  emit_getgl(as, tmp, gc.threshold);
  emit_getgl(as, RID_TMP, gc.total);
  as->gcsteps = 0;
  checkmclim(as);
}

/* -- Loop handling ------------------------------------------------------- */

/* Fixup the loop branch. */
static void asm_loop_fixup(ASMState *as)
{
  MCode *p = as->mctop;
  MCode *target = as->mcp;
  if (as->loopinv) {  /* Inverted loop branch? */
    /* asm_guardcc already inverted the cond branch and patched the final b. */
    p[-2] = (p[-2] & (0xffff0000u & ~PPCF_Y)) | (((target-p+2) & 0x3fffu) << 2);
  } else {
    p[-1] = PPCI_B|(((target-p+1)&0x00ffffffu)<<2);
  }
}

/* Fixup the tail of the loop. */
static void asm_loop_tail_fixup(ASMState *as)
{
  UNUSED(as);  /* Nothing to do. */
}

/* -- Head of trace ------------------------------------------------------- */

#if LJ_ARCH_PPC64
/* POWER8 overflow path (3.7, C9): a trace that guards on the sticky cr0.SO
** clears XER once, at its head, instead of BC_JLOOP clearing it on every
** entry. Emitted first here, so it executes last in the head, after the
** frame push and the register moves and before the first guard; r0 is
** never live across handlers. mtxer is a serializing SPR write (37.5 ns,
** C1), which is why only traces that need it emit it. The ISA 3.0 path
** never tests SO and never gets this. LJ_TEST_BREAK_XERCLR omits it: a
** stale SO planted before the entry then exits the trace at its first
** overflow guard, on every entry.
**
** Side traces (Phase 5, C27): a side trace attached to a bso exit is
** entered with SO *set* -- that is why the parent exited -- so it depends
** on this clear exactly as ppc32 depended on the mcrxr that
** lj_asm_patchexit prepended. LJ_TEST_BREAK_XERCLR_SIDE omits the clear
** in side-trace heads only: a side trace with its own SO guard, reached
** from a real overflow, then mis-exits at that guard on every entry.
*/
static void asm_head_clearxer(ASMState *as, int side)
{
#ifdef LJ_TEST_BREAK_XERCLR_SIDE
  if (side) return;
#else
  UNUSED(side);
#endif
#ifndef LJ_TEST_BREAK_XERCLR
  if (as->xerclr) {
    emit_tab(as, PPCI_MTXER, RID_TMP, 0, 0);
    emit_ti(as, PPCI_LI, RID_TMP, 0);
  }
#else
  UNUSED(as);
#endif
}
#else
#define asm_head_clearxer(as, side)	UNUSED(as)
#endif

/* Coalesce BASE register for a root trace. */
static void asm_head_root_base(ASMState *as)
{
  IRIns *ir = IR(REF_BASE);
  Reg r = ir->r;
  asm_head_clearxer(as, 0);
  if (ra_hasreg(r)) {
    ra_free(as, r);
    if (rset_test(as->modset, r) || irt_ismarked(ir->t))
      ir->r = RID_INIT;  /* No inheritance for modified BASE register. */
    if (r != RID_BASE)
      emit_mr(as, r, RID_BASE);
  }
}

/* Coalesce BASE register for a side trace. */
static Reg asm_head_side_base(ASMState *as, IRIns *irp)
{
  IRIns *ir = IR(REF_BASE);
  Reg r = ir->r;
  asm_head_clearxer(as, 1);
  if (ra_hasreg(r)) {
    ra_free(as, r);
    if (rset_test(as->modset, r) || irt_ismarked(ir->t))
      ir->r = RID_INIT;  /* No inheritance for modified BASE register. */
    if (irp->r == r) {
      return r;  /* Same BASE register already coalesced. */
    } else if (ra_hasreg(irp->r) && rset_test(as->freeset, irp->r)) {
      emit_mr(as, r, irp->r);  /* Move from coalesced parent reg. */
      return irp->r;
    } else {
      emit_getgl(as, r, jit_base);  /* Otherwise reload BASE. */
    }
  }
  return RID_NONE;
}

/* -- Tail of trace ------------------------------------------------------- */

/* Fixup the tail code. */
static void asm_tail_fixup(ASMState *as, TraceNo lnk)
{
  uintptr_t target = lnk ? (uintptr_t)traceref(as->J, lnk)->mcode : (uintptr_t)(void *)lj_vm_exit_interp;
  MCode *mcp = as->mctail;
  int32_t spadj = as->T->spadjust;
  if (spadj) {  /* Emit stack adjustment. */
    lj_assertA(checki16(CFRAME_SIZE+spadj), "stack adjustment out of range");
    *mcp++ = PPCI_ADDI | PPCF_T(RID_TMP) | PPCF_A(RID_SP) | (CFRAME_SIZE+spadj);
#if LJ_ARCH_PPC64
    /* Pop the trace frame; the interpreter frame's 24(sp) already holds
    ** the TOC (SAVE_TOC), so no reload is needed on this edge (D2).
    */
    emit_guard(as, (spadj & 3) == 0);
    *mcp++ = PPCI_STDU | PPCF_T(RID_TMP) | PPCF_A(RID_SP) | spadj;
#else
    *mcp++ = PPCI_STWU | PPCF_T(RID_TMP) | PPCF_A(RID_SP) | spadj;
#endif
  }
  /* Emit exit branch. */
  if ((((target - (uintptr_t)mcp) + 0x02000000u) >> 26) == 0) {
    *mcp = PPCI_B | ((target - (uintptr_t)mcp) & 0x03fffffcu); mcp++;
  } else {
#if LJ_ARCH_PPC64
    *mcp++ = PPCI_LD | PPCF_T(RID_TMP) | PPCF_A(RID_JGL) |
	     jglofs(as, &as->J->k64[LJ_K64_VM_EXIT_INTERP]);
#else
    *mcp++ = PPCI_LWZ | PPCF_T(RID_TMP) | PPCF_A(RID_JGL) |
	     jglofs(as, &as->J->k32[LJ_K32_VM_EXIT_INTERP]);
#endif
    *mcp++ = PPCI_MTCTR | PPCF_T(RID_TMP);
    *mcp++ = PPCI_BCTR;
  }
  while (as->mctop > mcp) *--as->mctop = PPCI_NOP;
}

/* Prepare tail of code. */
static void asm_tail_prep(ASMState *as, TraceNo lnk)
{
  MCode *p = as->mctop - 1;  /* Leave room for exit branch. */
  if (as->loopref) {
    as->invmcp = as->mcp = p;
  } else {
    if (!lnk) {
      uintptr_t target = (uintptr_t)(void *)lj_vm_exit_interp;
      if ((((target - (uintptr_t)p) + 0x02000000u) >> 26) ||
	  (((target - (uintptr_t)(p-2)) + 0x02000000u) >> 26)) p -= 2;
    }
    p -= 2;  /* Leave room for stack pointer adjustment. */
    as->mcp = p;
    as->invmcp = NULL;
  }
  as->mctail = p;
}

/* -- Trace setup --------------------------------------------------------- */

/* Ensure there are enough stack slots for call arguments. */
static Reg asm_setup_call_slots(ASMState *as, IRIns *ir, const CCallInfo *ci)
{
  IRRef args[CCI_NARGS_MAX*2];
  uint32_t i, nargs = CCI_XNARGS(ci);
#if LJ_ARCH_PPC64
  /* ELFv2: every argument takes a doubleword slot, FP or not; slots 8+
  ** are on the stack from SPS_FIRST (byte 96). The varargs marker (0 ref)
  ** takes none.
  */
  int nslots = SPS_FIRST, ngpr = REGARG_NUMGPR;
  asm_collectargs(as, ir, ci, args);
  for (i = 0; i < nargs; i++)
    if (args[i]) {
      if (ngpr > 0) ngpr--; else nslots += 2;
    }
#else
  int nslots = 2, ngpr = REGARG_NUMGPR, nfpr = REGARG_NUMFPR;
  asm_collectargs(as, ir, ci, args);
  for (i = 0; i < nargs; i++)
    if (!LJ_SOFTFP && args[i] && irt_isfp(IR(args[i])->t)) {
      if (nfpr > 0) nfpr--; else nslots = (nslots+3) & ~1;
    } else {
      if (ngpr > 0) ngpr--; else nslots++;
    }
#endif
  if (nslots > as->evenspill)  /* Leave room for args in stack slots. */
    as->evenspill = nslots;
  return (!LJ_SOFTFP && irt_isfp(ir->t)) ? REGSP_HINT(RID_FPRET) :
					   REGSP_HINT(RID_RET);
}

static void asm_setup_target(ASMState *as)
{
#if LJ_ARCH_PPC64
  as->xerclr = 0;
#endif
  asm_exitstub_setup(as, as->T->nsnap + (as->parent ? 1 : 0));
}

/* -- Trace patching ------------------------------------------------------ */

#if LJ_ARCH_PPC64
/* Patch exit jumps of existing machine code to a new target.
**
** PPC64: no `clearso' prepend. ppc32 grew the new side trace by one mcrxr
** when the patched exit was a bso, because SO is sticky and the side trace
** starts with it set. Here every trace that tests SO clears XER in its own
** head (asm_head_clearxer), root or side, so a side trace reached from an
** SO exit is covered by construction and the ISA 3.0 path (cr7.GT) never
** tests SO at all. The bc detection is by opcode and displacement, so the
** cr7 guards are patched like any other.
*/
void lj_asm_patchexit(jit_State *J, GCtrace *T, ExitNo exitno, MCode *target)
{
  MCode *p = T->mcode;
  MCode *pe = (MCode *)((char *)p + T->szmcode);
  MCode *px;
  MCode *cstart = NULL;
  MCode *mcarea = lj_mcode_patch(J, p, 0);
  int patchlong = 1;
#ifdef LJ_TEST_BREAK_PATCHEXIT
  /* Control (Phase 5): redirect the neighbouring exit instead of the one
  ** the side trace was compiled for.
  */
  exitno = (ExitNo)((exitno + 1) % T->nsnap);
#endif
  px = exitstub_trace_addr(T, exitno);
  for (; p < pe; p++) {
    /* Look for exitstub branch, try to replace with branch to target. */
    uint32_t ins = *p;
    if ((ins & 0xfc000000u) == 0x40000000u &&
	((ins ^ ((char *)px-(char *)p)) & 0xffffu) == 0) {
      ptrdiff_t delta = (char *)target - (char *)p;
      /* Many, but not all short-range branches can be patched directly. */
      if (p[-1] == PPC_NOPATCH_GC_CHECK) {
	patchlong = 0;
      } else if (((delta + 0x8000) >> 16) == 0) {
	*p = (ins & 0xffdf0000u) | ((uint32_t)delta & 0xffffu) |
	     ((delta & 0x8000) * (PPCF_Y/0x8000));
	if (!cstart) cstart = p;
      }
    } else if ((ins & 0xfc000000u) == PPCI_B &&
	       ((ins ^ ((char *)px-(char *)p)) & 0x03ffffffu) == 0) {
      ptrdiff_t delta = (char *)target - (char *)p;
      lj_assertJ(((delta + 0x02000000) >> 26) == 0,
		 "branch target out of range");
      *p = PPCI_B | ((uint32_t)delta & 0x03ffffffu);
      if (!cstart) cstart = p;
    }
  }
  /* Always patch long-range branch in exit stub itself. Except, if we can't. */
  if (patchlong) {
    ptrdiff_t delta = (char *)target - (char *)px;
    lj_assertJ(((delta + 0x02000000) >> 26) == 0,
	       "branch target out of range");
    *px = PPCI_B | ((uint32_t)delta & 0x03ffffffu);
  }
  if (!cstart) cstart = px;
  lj_mcode_sync(cstart, px+1);
  lj_mcode_patch(J, mcarea, 1);
}
#else
/* Patch exit jumps of existing machine code to a new target. */
void lj_asm_patchexit(jit_State *J, GCtrace *T, ExitNo exitno, MCode *target)
{
  MCode *p = T->mcode;
  MCode *pe = (MCode *)((char *)p + T->szmcode);
  MCode *px = exitstub_trace_addr(T, exitno);
  MCode *cstart = NULL;
  MCode *mcarea = lj_mcode_patch(J, p, 0);
  int clearso = 0, patchlong = 1;
  for (; p < pe; p++) {
    /* Look for exitstub branch, try to replace with branch to target. */
    uint32_t ins = *p;
    if ((ins & 0xfc000000u) == 0x40000000u &&
	((ins ^ ((char *)px-(char *)p)) & 0xffffu) == 0) {
      ptrdiff_t delta = (char *)target - (char *)p;
      if (((ins >> 16) & 3) == (CC_SO&3)) {
	clearso = sizeof(MCode);
	delta -= sizeof(MCode);
      }
      /* Many, but not all short-range branches can be patched directly. */
      if (p[-1] == PPC_NOPATCH_GC_CHECK) {
	patchlong = 0;
      } else if (((delta + 0x8000) >> 16) == 0) {
	*p = (ins & 0xffdf0000u) | ((uint32_t)delta & 0xffffu) |
	     ((delta & 0x8000) * (PPCF_Y/0x8000));
	if (!cstart) cstart = p;
      }
    } else if ((ins & 0xfc000000u) == PPCI_B &&
	       ((ins ^ ((char *)px-(char *)p)) & 0x03ffffffu) == 0) {
      ptrdiff_t delta = (char *)target - (char *)p;
      lj_assertJ(((delta + 0x02000000) >> 26) == 0,
		 "branch target out of range");
      *p = PPCI_B | ((uint32_t)delta & 0x03ffffffu);
      if (!cstart) cstart = p;
    }
  }
  /* Always patch long-range branch in exit stub itself. Except, if we can't. */
  if (patchlong) {
    ptrdiff_t delta = (char *)target - (char *)px - clearso;
    lj_assertJ(((delta + 0x02000000) >> 26) == 0,
	       "branch target out of range");
    *px = PPCI_B | ((uint32_t)delta & 0x03ffffffu);
  }
  if (!cstart) cstart = px;
  lj_mcode_sync(cstart, px+1);
  if (clearso) {  /* Extend the current trace. Ugly workaround. */
    MCode *pp = J->cur.mcode;
    J->cur.szmcode += sizeof(MCode);
    *--pp = PPCI_MCRXR;  /* Clear SO flag. */
    J->cur.mcode = pp;
    lj_mcode_sync(pp, pp+1);
  }
  lj_mcode_patch(J, mcarea, 1);
}
#endif


/* -- PPC64 per-handler redirection (generated) --------------------------- */

/* Handlers whose 64-bit version has landed are listed here and excluded
** by tests/lib/lj_ppc64_nyi_gen.py; everything else lj_asm.c can reach is
** redirected to asm_nyi64 below.
*/
/* PPC64_CONVERTED: asm_callx asm_ahuvload asm_ahustore asm_sload asm_fload
   asm_fstore asm_xload asm_xstore asm_href asm_hrefk asm_uref asm_fref
   asm_strref asm_aref asm_retf asm_cnew asm_tbar asm_obar asm_add asm_sub
   asm_comp asm_equal asm_conv asm_tobit asm_hiop
   asm_mul asm_neg asm_abs asm_fpdiv asm_fpmath asm_addov asm_subov asm_mulov
   asm_bnot asm_bswap asm_band asm_bor asm_bxor asm_bshl asm_bshr asm_bsar
   asm_brol asm_min asm_max asm_strto asm_prof */

#if LJ_ARCH_PPC64
/* BEGIN GENERATED: lj_ppc64_nyi_gen.py -- do not edit by hand. */
#undef asm_bror
#define asm_bror(as, ir)	asm_nyi64((as), (ir), NULL)
/* END GENERATED */
#endif
