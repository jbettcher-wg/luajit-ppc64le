/*
** PPC instruction emitter.
** Copyright (C) 2005-2026 Mike Pall. See Copyright Notice in luajit.h
*/

/* -- Constant helpers ---------------------------------------------------- */

#if LJ_64
static intptr_t get_k64val(ASMState *as, IRRef ref)
{
  IRIns *ir = IR(ref);
  if (ir->o == IR_KINT64) {
    return (intptr_t)ir_kint64(ir)->u64;
  } else if (ir->o == IR_KGC) {
    return (intptr_t)ir_kgc(ir);
  } else if (ir->o == IR_KPTR || ir->o == IR_KKPTR) {
    return (intptr_t)ir_kptr(ir);
  } else {
    lj_assertA(ir->o == IR_KINT || ir->o == IR_KNULL,
	       "bad 64 bit const %d", ir->o);
    return ir->i;  /* Sign-extended. */
  }
}
#define get_kval(as, ref)	get_k64val(as, ref)
#else
#define get_kval(as, ref)	(IR((ref))->i)
#endif

/* -- Encoder guards ------------------------------------------------------ */

/* Release-active guards for operand fields whose overflow is silent: the
** survey (ppc64le-jit-survey.md, Deliverable 2) records M-form SH/MB/ME
** bleeding into the *destination register field*, rldimi's wrapping mask,
** DS/DQ-form displacements losing their low bits, sradi's split 6-bit SH
** and isel's absolute CR bit index. lj_assertA is compiled out of release
** builds, so a violation here aborts the trace instead (R9): the trace is
** penalized and the interpreter runs the code, which is always correct.
*/
static LJ_NOINLINE void emit_badenc(ASMState *as)
{
  lj_trace_err(as->J, LJ_TRERR_BADENC);
}

#ifndef emit_guard  /* The handbook's guard control builds with it defined away. */
#define emit_guard(as, cond) \
  do { if (LJ_UNLIKELY(!(cond))) emit_badenc(as); } while (0)
#endif

/* -- Emit basic instructions --------------------------------------------- */

static void emit_tab(ASMState *as, PPCIns pi, Reg rt, Reg ra, Reg rb)
{
  *--as->mcp = pi | PPCF_T(rt) | PPCF_A(ra) | PPCF_B(rb);
}

#define emit_asb(as, pi, ra, rs, rb)	emit_tab(as, (pi), (rs), (ra), (rb))
#define emit_as(as, pi, ra, rs)		emit_tab(as, (pi), (rs), (ra), 0)
#define emit_ab(as, pi, ra, rb)		emit_tab(as, (pi), 0, (ra), (rb))

/* D-form and DS-form. D-form immediates are masked to 16 bits by design:
** callers (emit_loadi, emit_cmpi, ...) pass whole constants and pick the
** half with the opcode (ori/oris, lis). DS-form (primary opcodes 58 and 62:
** ld/ldu/lwa, std/stdu) keeps its XO in the low two bits of the word and
** its callers pass displacements, so those are range- and alignment-checked
** -- a dropped low bit there is a load from the wrong address, or a
** different instruction (ld with disp 6 is lwa from disp 4).
*/
static void emit_tai(ASMState *as, PPCIns pi, Reg rt, Reg ra, int32_t i)
{
  uint32_t op = (uint32_t)pi >> 26;
  if (op == 58 || op == 62)
    emit_guard(as, (checki16(i) || checku16(i)) && (i & 3) == 0);
  *--as->mcp = pi | PPCF_T(rt) | PPCF_A(ra) | (i & 0xffff);
}

#define emit_ti(as, pi, rt, i)		emit_tai(as, (pi), (rt), 0, (i))
#define emit_ai(as, pi, ra, i)		emit_tai(as, (pi), 0, (ra), (i))
#define emit_asi(as, pi, ra, rs, i)	emit_tai(as, (pi), (rs), (ra), (i))

#define emit_fab(as, pi, rf, ra, rb) \
  emit_tab(as, (pi), (rf)&31, (ra)&31, (rb)&31)
#define emit_fb(as, pi, rf, rb)		emit_tab(as, (pi), (rf)&31, 0, (rb)&31)
#define emit_fac(as, pi, rf, ra, rc) \
  emit_tab(as, (pi) | PPCF_C((rc) & 31), (rf)&31, (ra)&31, 0)
#define emit_facb(as, pi, rf, ra, rc, rb) \
  emit_tab(as, (pi) | PPCF_C((rc) & 31), (rf)&31, (ra)&31, (rb)&31)
#define emit_fai(as, pi, rf, ra, i)	emit_tai(as, (pi), (rf)&31, (ra), (i))

/* M-form: rlwinm/rlwimi/rlwnm. SH, MB and ME are 5 bits each; SH >= 32
** would set bit 16 and rewrite the RA (destination) field.
*/
static void emit_rot(ASMState *as, PPCIns pi, Reg ra, Reg rs,
		     int32_t n, int32_t b, int32_t e)
{
  emit_guard(as, (uint32_t)n < 32 && (uint32_t)b < 32 && (uint32_t)e < 32);
  *--as->mcp = pi | PPCF_T(rs) | PPCF_A(ra) | PPCF_B(n) |
	       PPCF_MB(b) | PPCF_ME(e);
}

static void emit_slwi(ASMState *as, Reg ra, Reg rs, int32_t n)
{
  lj_assertA(n >= 0 && n < 32, "shift out or range");
  emit_rot(as, PPCI_RLWINM, ra, rs, n, 0, 31-n);
}

static void emit_rotlwi(ASMState *as, Reg ra, Reg rs, int32_t n)
{
  lj_assertA(n >= 0 && n < 32, "shift out or range");
  emit_rot(as, PPCI_RLWINM, ra, rs, n, 0, 31);
}

#if LJ_ARCH_PPC64
/* MD-form: rldicl/rldicr/rldic/rldimi with split 6-bit SH and MB/ME
** (PPCF_SH/PPCF_M6, gas-verified by the encoding oracle since C6).
*/
static void emit_rotd(ASMState *as, PPCIns pi, Reg ra, Reg rs,
		      int32_t sh, int32_t m6)
{
  emit_guard(as, (uint32_t)sh < 64 && (uint32_t)m6 < 64);
  *--as->mcp = pi | PPCF_T(rs) | PPCF_A(ra) | PPCF_SH(sh) | PPCF_M6(m6);
}

/* rldimi inserts under MASK(MB, 63-SH), and MASK wraps when MB > 63-SH:
** the insert then has two windows and gas encodes it without a word.
*/
static LJ_AINLINE void emit_rldimi(ASMState *as, Reg ra, Reg rs, int32_t sh, int32_t mb)
{
  emit_guard(as, (uint32_t)sh < 64 && (uint32_t)mb < 64 && mb + sh <= 63);
  emit_rotd(as, PPCI_RLDIMI, ra, rs, sh, mb);
}

#define emit_rotldi(as, ra, rs, n)	emit_rotd(as, PPCI_RLDICL, (ra), (rs), (n), 0)
#define emit_sldi(as, ra, rs, n)	emit_rotd(as, PPCI_RLDICR, (ra), (rs), (n), 63-(n))
#define emit_srdi(as, ra, rs, n)	emit_rotd(as, PPCI_RLDICL, (ra), (rs), 64-(n), (n))
#define emit_clrldi(as, ra, rs, n)	emit_rotd(as, PPCI_RLDICL, (ra), (rs), 0, (n))
#define emit_clrrdi(as, ra, rs, n)	emit_rotd(as, PPCI_RLDICR, (ra), (rs), 0, 63-(n))

/* XS-form: sradi. SH's 6th bit lives at bit 1 of the word (PPCF_SH). */
static LJ_AINLINE void emit_sradi(ASMState *as, Reg ra, Reg rs, int32_t sh)
{
  emit_guard(as, (uint32_t)sh < 64);
  *--as->mcp = PPCI_SRADI | PPCF_T(rs) | PPCF_A(ra) | PPCF_SH(sh);
}

/* A-form isel: BC is an absolute CR bit index 0..31 (4*crfield + bit),
** not a PPCCC and not a field number.
*/
static LJ_AINLINE void emit_isel(ASMState *as, Reg rt, Reg ra, Reg rb, int32_t bc)
{
  emit_guard(as, (uint32_t)bc < 32);
  *--as->mcp = PPCI_ISEL | PPCF_T(rt) | PPCF_A(ra) | PPCF_B(rb) | PPCF_C(bc);
}

/* DQ-form lxv/stxv (ISA 3.0): 12-bit displacement field holds dq>>4, so
** the displacement must be a multiple of 16; range is -32768..32752.
** xt is a VSR number 0..63 (FPR f<n> == VSR n).
*/
static LJ_AINLINE void emit_dq(ASMState *as, PPCIns pi, Reg xt, Reg ra, int32_t dq)
{
  emit_guard(as, (dq & 15) == 0 && dq >= -32768 && dq <= 32752);
  *--as->mcp = pi | PPCF_T(xt & 31) | PPCF_A(ra) | (dq & 0xfff0) |
	       (((uint32_t)xt >> 5) << 3);
}

/* -- Width discipline (D3) -----------------------------------------------
** A register holding a 32-bit IR value has undefined bits 32..63. These
** are the only sanctioned ways to widen one: signed or unsigned according
** to the IR type. Everything that hands a 32-bit value to C, to an address
** computation or to a 64-bit compare goes through here.
*/
#define emit_extsw(as, ra, rs)		emit_as(as, PPCI_EXTSW, (ra), (rs))
#define emit_zextw(as, ra, rs)		emit_clrldi(as, (ra), (rs), 32)

static LJ_AINLINE void emit_widen(ASMState *as, IRType1 t, Reg dst, Reg src)
{
  if (irt_isu32(t) || irt_isu8(t) || irt_isu16(t))
    emit_zextw(as, dst, src);
  else
    emit_extsw(as, dst, src);
}
#endif

/* -- Emit loads/stores --------------------------------------------------- */

#define jglofs(as, k) \
  (((uintptr_t)(k) - (uintptr_t)J2G(as->J) - 32768) & 0xffff)

/* Prefer rematerialization of BASE/L from global_State over spills. */
#define emit_canremat(ref)	((ref) <= REF_BASE)

/* Value of a register that holds a constant, or 0 with *ok cleared.
** Only real constants qualify: ASMREF_TMP1/TMP2 are below ASMREF_L too but
** hold whatever the current handler put there.
*/
static intptr_t emit_kregval(ASMState *as, IRRef ref, int *ok)
{
  *ok = 1;
  if (ra_iskref(ref)) {
    return ra_krefk(as, ref);
  } else {
    IRIns *ir = IR(ref);
#if LJ_64
    if (ir->o == IR_KINT64) return (intptr_t)ir_kint64(ir)->u64;
#if LJ_GC64
    if (ir->o == IR_KGC) return (intptr_t)ir_kgc(ir);
    if (ir->o == IR_KPTR || ir->o == IR_KKPTR) return (intptr_t)ir_kptr(ir);
#endif
#endif
    if (ir->o == IR_KINT || ir->o == IR_KNULL ||
	(!LJ_GC64 && (ir->o == IR_KGC || ir->o == IR_KPTR || ir->o == IR_KKPTR)))
      return (intptr_t)ir->i;
    *ok = 0;
    return 0;
  }
}

/* Try to find a one step delta relative to another constant. */
static int emit_kdelta1(ASMState *as, Reg rd, intptr_t i)
{
  RegSet work = ~as->freeset & RSET_GPR;
  while (work) {
    Reg r = rset_picktop(work);
    IRRef ref = regcost_ref(as->cost[r]);
    lj_assertA(r != rd, "dest reg %d not free", rd);
    if (ref < ASMREF_TMP1) {
      int ok;
      intptr_t k = emit_kregval(as, ref, &ok);
      if (ok) {
	intptr_t delta = i - k;
	if (checki16(delta)) {
	  emit_tai(as, PPCI_ADDI, rd, r, (int32_t)delta);
	  return 1;
	}
      }
    }
    rset_clear(work, r);
  }
  return 0;  /* Failed. */
}

/* Load a 32 bit constant into a GPR (sign-extended to 64 bits on PPC64). */
static void emit_loadi(ASMState *as, Reg r, int32_t i)
{
  if (checki16(i)) {
    emit_ti(as, PPCI_LI, r, i);
  } else {
    if ((i & 0xffff)) {
      intptr_t jgl = (intptr_t)(void *)J2G(as->J);
      /* Full-width compare: on 64 bit a 32-bit truncation of the delta
      ** could match while the real address is gigabytes away.
      */
      if ((uintptr_t)((intptr_t)i-jgl) < 65536) {
	emit_tai(as, PPCI_ADDI, r, RID_JGL, (int32_t)((intptr_t)i-jgl-32768));
	return;
      } else if (emit_kdelta1(as, r, (intptr_t)i)) {
	return;
      }
      emit_asi(as, PPCI_ORI, r, r, i);
    }
    emit_ti(as, PPCI_LIS, r, (i >> 16));
  }
}

#if LJ_ARCH_PPC64
/* Load a 64 bit constant into a GPR. The ladder, cheapest first:
**  1-2  checki32:            li / lis [ori]      (emit_loadi, incl. JGL/kdelta)
**  1    JGL-relative 16 bit: addi r, JGL, d
**  1    kdelta1:             addi r, r', d       (r' holds a nearby constant)
**  2    li m; sldi s         every itype<<47 tag constant, powers of two
**  2    li m; rotldi n       every primitive TValue ~((~itype)<<47)
**  2    JGL-relative 32 bit: addis r, JGL, hi; addi r, r, lo
**  2-3  32-bit unsigned:     lis [ori]; clrldi 32
**  3-5  general:             li|lis [ori]; sldi 32; [oris]; [ori]
** Every tier leaves the exact 64-bit value in r (no garbage-tolerance
** here: constants are also used as addresses and tags).
*/
static void emit_loadu64(ASMState *as, Reg r, uint64_t u64)
{
  int64_t k = (int64_t)u64;
  intptr_t jgl = (intptr_t)(void *)J2G(as->J) + 32768;
  int64_t d = k - (int64_t)jgl;
  int n;
  if (checki32(k)) {
    emit_loadi(as, r, (int32_t)k);
    return;
  }
  if (checki16(d)) {
    emit_tai(as, PPCI_ADDI, r, RID_JGL, (int32_t)d);
    return;
  }
  if (emit_kdelta1(as, r, (intptr_t)k))
    return;
  n = (int)lj_ffs64(u64);  /* u64 != 0 here. */
  if (checki16(k >> n)) {  /* li m; sldi n */
    emit_sldi(as, r, r, n);
    emit_ti(as, PPCI_LI, r, (int32_t)(k >> n));
    return;
  }
  for (n = 1; n < 64; n++) {  /* li m; rotldi n */
    uint64_t m = (u64 >> n) | (u64 << (64-n));  /* rotr(u64, n) */
    if (checki16((int64_t)m)) {
      emit_rotldi(as, r, r, n);
      emit_ti(as, PPCI_LI, r, (int32_t)(int64_t)m);
      return;
    }
  }
  if (checki32(d) && checki16((d - (int16_t)d) >> 16)) {
    /* addis r, JGL, hi; addi r, r, lo. The second test excludes the top
    ** 32 KB of the range, where hi would be 32768.
    */
    int32_t lo = (int32_t)(int16_t)d;
    emit_tai(as, PPCI_ADDI, r, r, lo);
    emit_tai(as, PPCI_ADDIS, r, RID_JGL, (int32_t)((d - lo) >> 16));
    return;
  }
  if ((u64 >> 32) == 0) {  /* lis [ori]; clrldi 32 */
    emit_clrldi(as, r, r, 32);
    emit_loadi(as, r, (int32_t)u64);
    return;
  }
  {  /* General: high word by emit_loadi, then shift and or in the low word. */
    uint32_t lo = (uint32_t)u64;
    if ((lo & 0xffff)) emit_asi(as, PPCI_ORI, r, r, (int32_t)(lo & 0xffff));
    if ((lo >> 16)) emit_asi(as, PPCI_ORIS, r, r, (int32_t)(lo >> 16));
    emit_sldi(as, r, r, 32);
    emit_loadi(as, r, (int32_t)(u64 >> 32));
  }
}

#define emit_loada(as, r, addr)		emit_loadu64(as, (r), u64ptr((addr)))
#else
#define emit_loada(as, r, addr)		emit_loadi(as, (r), i32ptr((addr)))
#endif

static Reg ra_allock(ASMState *as, intptr_t k, RegSet allow);
static void ra_allockreg(ASMState *as, intptr_t k, Reg r);

/* Get/set from constant pointer. */
static void emit_lsptr(ASMState *as, PPCIns pi, Reg r, void *p, RegSet allow)
{
  intptr_t jgl = (intptr_t)(void *)J2G(as->J);
  intptr_t i = (intptr_t)p;
  Reg base;
  if ((uintptr_t)(i-jgl) < 65536) {
    i = i-jgl-32768;
    base = RID_JGL;
  } else {
    base = ra_allock(as, i-(int16_t)i, allow);
    i = (int16_t)i;
  }
  emit_tai(as, pi, r, base, (int32_t)i);
}

#if LJ_ARCH_PPC64
/* Load a 64 bit IR constant into a GPR (KINT64/KGC/KPTR/KKPTR) or a KNUM
** into an FPR. ra_left() calls this with GPR destinations under GC64.
*/
static void emit_loadk64(ASMState *as, Reg r, IRIns *ir)
{
  if (r < RID_MAX_GPR) {
    uint64_t k;
    if (ir->o == IR_KINT64) k = ir_kint64(ir)->u64;
    else if (ir->o == IR_KGC) k = (uint64_t)(uintptr_t)ir_kgc(ir);
    else k = (uint64_t)(uintptr_t)ir_kptr(ir);
    emit_loadu64(as, r, k);
  } else {
    emit_lsptr(as, PPCI_LFD, (r & 31), (void *)&ir_knum(ir)->u64, RSET_GPR);
  }
}
#else
#define emit_loadk64(as, r, ir) \
  emit_lsptr(as, PPCI_LFD, ((r) & 31), (void *)&ir_knum((ir))->u64, RSET_GPR)
#endif

/* Get/set global_State fields. */
static void emit_lsglptr(ASMState *as, PPCIns pi, Reg r, int32_t ofs)
{
  emit_tai(as, pi, r, RID_JGL, ofs-32768);
}

/* Pointer-width accessors: every field these are used for (jit_base,
** cur_L, gc.total/threshold under GC64) is 8 bytes on PPC64. Narrower
** fields go through emit_lsglptr with an explicit opcode.
*/
#if LJ_ARCH_PPC64
#define emit_getgl(as, r, field) \
  emit_lsglptr(as, PPCI_LD, (r), (int32_t)offsetof(global_State, field))
#define emit_setgl(as, r, field) \
  emit_lsglptr(as, PPCI_STD, (r), (int32_t)offsetof(global_State, field))
#else
#define emit_getgl(as, r, field) \
  emit_lsglptr(as, PPCI_LWZ, (r), (int32_t)offsetof(global_State, field))
#define emit_setgl(as, r, field) \
  emit_lsglptr(as, PPCI_STW, (r), (int32_t)offsetof(global_State, field))
#endif

/* Trace number is determined from per-trace exit stubs. */
#define emit_setvmstate(as, i)		UNUSED(i)

/* -- Emit control-flow instructions -------------------------------------- */

/* Label for internal jumps. */
typedef MCode *MCLabel;

/* Return label pointing to current PC. */
#define emit_label(as)		((as)->mcp)

/* Conditional branch: 14-bit displacement, +-32 KB. A trace longer than
** that from its exit stubs cannot be encoded; abort it (R9), a release
** build must not truncate the field.
*/
static void emit_condbranch(ASMState *as, PPCIns pi, PPCCC cc, MCode *target)
{
  MCode *p = --as->mcp;
  ptrdiff_t delta = (char *)target - (char *)p;
  if (LJ_UNLIKELY(((delta + 0x8000) >> 16) != 0))
    lj_trace_err(as->J, LJ_TRERR_MCODEOV);
  pi ^= (delta & 0x8000) * (PPCF_Y/0x8000);
  *p = pi | PPCF_CC(cc) | ((uint32_t)delta & 0xffffu);
}

static void emit_jmp(ASMState *as, MCode *target)
{
  MCode *p = --as->mcp;
  ptrdiff_t delta = (char *)target - (char *)p;
  if (LJ_UNLIKELY(((delta + 0x02000000) >> 26) != 0))
    lj_trace_err(as->J, LJ_TRERR_MCODEOV);
  *p = PPCI_B | (delta & 0x03fffffcu);
}

#if LJ_ARCH_PPC64
/* Call a C function from a trace: the ELFv2 model A sequence (D2).
**
**   <r12 = target>       via ra_allockreg: addi off JGL/another constant,
**                        or the emit_loadu64 ladder
**   mtctr r12
**   bctrl                the callee's global entry computes r2 from r12
**   ld    r2, 24(sp)     restore our TOC from the frame's save slot
**
** This is the ONLY call emitter: a bctrl without the reload leaves r2
** pointing at the callee's TOC and fails silently, elsewhere (R2). The
** frame's slot 24(sp) is written by emit_spsub() for trace frames and is
** SAVE_TOC of the interpreter frame when spadjust == 0. lj_toc_scan.sh
** checks emitted code for exactly this shape.
*/
static void emit_call(ASMState *as, void *target)
{
  MCode *p = as->mcp;
  *--p = PPCI_LD | PPCF_T(RID_SYS1) | PPCF_A(RID_SP) | 24;
  *--p = PPCI_BCTRL;
  *--p = PPCI_MTCTR | PPCF_T(RID_CFUNCADDR);
  as->mcp = p;
  ra_allockreg(as, (intptr_t)target, RID_CFUNCADDR);
}
#else
static void emit_call(ASMState *as, void *target)
{
  MCode *p = --as->mcp;
  ptrdiff_t delta = (char *)target - (char *)p;
  if ((((delta>>2) + 0x00800000) >> 24) == 0) {
    *p = PPCI_BL | (delta & 0x03fffffcu);
  } else {  /* Target out of range: need indirect call. Don't use arg reg. */
    RegSet allow = RSET_GPR & ~RSET_RANGE(RID_R0, REGARG_LASTGPR+1);
    Reg r = ra_allock(as, i32ptr(target), allow);
    *p = PPCI_BCTRL;
    p[-1] = PPCI_MTCTR | PPCF_T(r);
    as->mcp = p-1;
  }
}
#endif

/* -- Emit generic operations --------------------------------------------- */

#define emit_mr(as, dst, src) \
  emit_asb(as, PPCI_MR, (dst), (src), (src))

/* Generic move between two regs. */
static void emit_movrr(ASMState *as, IRIns *ir, Reg dst, Reg src)
{
  UNUSED(ir);
  if (dst < RID_MAX_GPR)
    emit_mr(as, dst, src);
  else
    emit_fb(as, PPCI_FMR, dst, src);
}

/* Generic load of register with base and (small) offset address.
** Spill slots are 4 bytes; 64-bit IR types get an even slot pair from
** ra_spill(), so ld/std displacements are always multiples of 8.
*/
static void emit_loadofs(ASMState *as, IRIns *ir, Reg r, Reg base, int32_t ofs)
{
  if (r < RID_MAX_GPR)
    emit_tai(as, (LJ_64 && irt_is64(ir->t)) ? PPCI_LD : PPCI_LWZ, r, base, ofs);
  else
    emit_fai(as, irt_isnum(ir->t) ? PPCI_LFD : PPCI_LFS, r, base, ofs);
}

/* Generic store of register with base and (small) offset address. */
static void emit_storeofs(ASMState *as, IRIns *ir, Reg r, Reg base, int32_t ofs)
{
  if (r < RID_MAX_GPR)
    emit_tai(as, (LJ_64 && irt_is64(ir->t)) ? PPCI_STD : PPCI_STW, r, base, ofs);
  else
    emit_fai(as, irt_isnum(ir->t) ? PPCI_STFD : PPCI_STFS, r, base, ofs);
}

#if !LJ_ARCH_PPC64
/* Emit a compare (for equality) with a constant operand. */
static void emit_cmpi(ASMState *as, Reg r, int32_t k)
{
  if (checki16(k)) {
    emit_ai(as, PPCI_CMPWI, r, k);
  } else if (checku16(k)) {
    emit_ai(as, PPCI_CMPLWI, r, k);
  } else {
    emit_ai(as, PPCI_CMPLWI, RID_TMP, k);
    emit_asi(as, PPCI_XORIS, RID_TMP, r, (k >> 16));
  }
}
#endif

/* Add offset to pointer. */
static void emit_addptr(ASMState *as, Reg r, int32_t ofs)
{
  if (ofs) {
    emit_tai(as, PPCI_ADDI, r, r, ofs);
    if (!checki16(ofs))
      emit_tai(as, PPCI_ADDIS, r, r, (ofs + 32768) >> 16);
  }
}

#if LJ_ARCH_PPC64
/* Push a trace frame of ofs bytes below the current one (executes as):
**
**   addi r0, sp, CFRAME_SIZE + parent_spadjust   ; back chain: the frame
**                                                ; above the interpreter's
**   stdu r0, -ofs(sp)                            ; new frame, chain stored
**   std  r2, 24(sp)                              ; TOC save slot live (D2)
**
** ofs is a multiple of 16 (sps_align) so the DS-form displacement is
** legal; stdu's 16-bit field caps a trace frame at 32 KB, which
** ra_spill()'s 256-slot limit (1 KB) keeps far away.
*/
static void emit_spsub(ASMState *as, int32_t ofs)
{
  if (ofs) {
    emit_guard(as, (ofs & 15) == 0 && ofs <= 32752);
    emit_tai(as, PPCI_STD, RID_SYS1, RID_SP, 24);
    emit_tai(as, PPCI_STDU, RID_TMP, RID_SP, -ofs);
    emit_tai(as, PPCI_ADDI, RID_TMP, RID_SP,
	     CFRAME_SIZE + (as->parent ? as->parent->spadjust : 0));
  }
}
#else
static void emit_spsub(ASMState *as, int32_t ofs)
{
  if (ofs) {
    emit_tai(as, PPCI_STWU, RID_TMP, RID_SP, -ofs);
    emit_tai(as, PPCI_ADDI, RID_TMP, RID_SP,
	     CFRAME_SIZE + (as->parent ? as->parent->spadjust : 0));
  }
}
#endif
