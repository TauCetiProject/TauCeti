/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
public import Mathlib.RingTheory.ClassGroup.Basic
public import TauCeti.NumberTheory.LFunctions.DedekindZeta.PartialZeta
public import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.FundamentalCone
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Count.TrivialModulus
import TauCeti.Analysis.SpecialFunctions.Pow.Complex
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Convergence
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Estimates
import TauCeti.NumberTheory.NumberField.Global.RayClass.Integral
import TauCeti.NumberTheory.NumberField.Units.Dirichlet

/-!
# The partial zeta function of an ideal class as a sum over the fundamental cone

Let `J` be a nonzero integral ideal of a number field `K`, and let `𝔎` be the ideal class of `J⁻¹`.
The integral ideals of `𝔎` are the ideals `𝔟` with `𝔟 J` principal, and `𝔟 ↦ 𝔟 J` matches them
with the principal ideals `(a)` divisible by `J`, that is with the nonzero `a ∈ J` up to units.
Mathlib's fundamental cone is a fundamental domain for the units modulo torsion, so each such
ideal has exactly `w = #μ(K)` generators in the cone. Since `N(𝔟 J) = N(𝔟) N(J)` and
`N((a)) = |N(a)|`, the partial zeta function of `𝔎` is, for `Re s > 1`,

`ζ(𝔎, s) = ∑_{𝔟 ∈ 𝔎} N(𝔟)^(-s) = N(J)^s / w · ∑_{x ∈ σ(J) ∩ cone} |N(x)|^(-s)`

(`LSeries_rayClassCoeff_one_eq_tsum_idealSet`), where `σ(J) ∩ cone` is Mathlib's
`NumberField.mixedEmbedding.fundamentalCone.idealSet K J`. Clearing denominators by the positive
integer norm of a denominator ideal extends this identity to any invertible fractional ideal `I`
(`hasSum_norm_cpow_fundamentalCone_inter_idealLattice`,
`tsum_norm_cpow_fundamentalCone_inter_idealLattice`,
`LSeries_rayClassCoeff_one_eq_tsum_fundamentalCone_inter_idealLattice`), because real positive
dilations preserve the fundamental cone and cancel between the lattice norms and `N(I)^s`. This is
Neukirch's (5.3)–(5.4): it turns the Dirichlet series of an ideal class into a sum over the points
of an ideal lattice in a fundamental domain for the units, which is the sum that the theta series
of that lattice, integrated over a fundamental domain on the norm-one hypersurface, produces in
Hecke's proof of the functional equation (where the dual side is the fractional trace dual). Here
`ζ(𝔎, s)` is the Dirichlet series of the class indicator `rayClassCoeff (Modulus.one K) c`, the ray
class `c` of the trivial modulus corresponding to `𝔎` under `oneEquivClassGroup`.

The restriction to the cone, or to some other fundamental domain for the units, cannot be dropped.
In positive unit rank every nonzero element of an ideal has infinitely many distinct unit multiples
in that ideal, all generating the same principal ideal, so the sum of `N((a))^(-s)` over all
nonzero `a` of a nonzero ideal does not converge for any `s`
(`NumberField.Units.not_summable_absNorm_of_rank_pos`). A construction that sums over all the
points of the lattice, such as the radial Mellin transform of the theta series with a single
parameter, therefore cannot produce a partial zeta function once the unit rank is positive.

## Main results

* `TauCeti.LFunctions.hasSum_norm_cpow_idealSet`: for `Re s > 1`, the sum of `|N(x)|^(-s)` over the
  points `x` of `J` in the fundamental cone is `w N(J)^(-s)` times the sum of `N(𝔟)^(-s)` over the
  nonzero integral ideals `𝔟` with `𝔟 J` principal.
* `TauCeti.LFunctions.LSeries_rayClassCoeff_one_eq_tsum`: the Dirichlet series of an ideal class
  is that sum over ideals.
* `TauCeti.LFunctions.LSeries_rayClassCoeff_one_eq_tsum_idealSet`: Neukirch's (5.3)–(5.4), the
  Dirichlet series of the class of `J⁻¹` as a sum over the points of `J` in the fundamental cone.
* `TauCeti.LFunctions.hasSum_norm_cpow_fundamentalCone_inter_idealLattice`,
  `TauCeti.LFunctions.tsum_norm_cpow_fundamentalCone_inter_idealLattice`,
  `TauCeti.LFunctions.LSeries_rayClassCoeff_one_eq_tsum_classGroup`,
  `TauCeti.LFunctions.LSeries_rayClassCoeff_one_eq_tsum_fundamentalCone_inter_idealLattice`: the
  fractional-ideal identities (`HasSum` on `Re s > 1` and unconditional `tsum` / `LSeries` for all
  `s : ℂ`).

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, (5.3) and (5.4).
-/

public section

open NumberField NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
  NumberField.Units Ideal Submodule TauCeti.GlobalNumberFields
open scoped nonZeroDivisors ComplexOrder

namespace TauCeti.LFunctions

variable {K : Type*} [Field K] [NumberField K]

/-! ### The ideals of the class of `J⁻¹` -/

/-- **Multiplying by `J` matches the ideals of the class of `J⁻¹` with the principal multiples of
`J`.** The sum of `N(I)^(-s)` over the principal ideals `I` divisible by `J` is `N(J)^(-s)` times
the sum of `N(𝔟)^(-s)` over the nonzero integral ideals `𝔟` with `𝔟 J` principal. Both sides are
`tsum`s, so the identity also holds where neither family is summable. -/
theorem tsum_absNorm_cpow_dvd_isPrincipal (J : (Ideal (𝓞 K))⁰) (s : ℂ) :
    ∑' I : {I : (Ideal (𝓞 K))⁰ // (J : Ideal (𝓞 K)) ∣ I ∧ IsPrincipal (I : Ideal (𝓞 K))},
        (absNorm (I : Ideal (𝓞 K)) : ℂ) ^ (-s) =
      (absNorm (J : Ideal (𝓞 K)) : ℂ) ^ (-s) *
        ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // IsPrincipal ((𝔟 : Ideal (𝓞 K)) * (J : Ideal (𝓞 K)))},
          (absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s) := by
  -- `𝔟 ↦ J 𝔟` matches the nonzero ideals with the multiples of `J` (Mathlib's `Equiv.dvd` in the
  -- cancellative monoid of nonzero ideals), and carries the condition on `𝔟 J` along.
  let e : {𝔟 : (Ideal (𝓞 K))⁰ // IsPrincipal ((𝔟 : Ideal (𝓞 K)) * (J : Ideal (𝓞 K)))} ≃
      {I : (Ideal (𝓞 K))⁰ // (J : Ideal (𝓞 K)) ∣ I ∧ IsPrincipal (I : Ideal (𝓞 K))} :=
    ((Equiv.dvd J).subtypeEquiv (q := fun I ↦ IsPrincipal (I.1 : Ideal (𝓞 K)))
        fun 𝔟 ↦ by rw [Equiv.dvd_apply, Submonoid.coe_mul, mul_comm]).trans <|
      (Equiv.subtypeSubtypeEquivSubtypeInter (fun I ↦ J ∣ I)
        fun I : (Ideal (𝓞 K))⁰ ↦ IsPrincipal (I : Ideal (𝓞 K))).trans <|
        Equiv.subtypeEquivRight fun _ ↦ by rw [nonZeroDivisors_dvd_iff_dvd_coe]
  rw [← e.tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun 𝔟 ↦ ?_
  simp [e, map_mul, Complex.natCast_mul_natCast_cpow]

/-- **The sum over the points of `J` in the fundamental cone.** For `Re s > 1`, the sum of
`|N(x)|^(-s)` over the points `x` of the fundamental cone that are images of elements of `J`
(Mathlib's `idealSet K J`) is `w N(J)^(-s)` times the sum of `N(𝔟)^(-s)` over the nonzero integral
ideals `𝔟` with `𝔟 J` principal, the ideals of the class of `J⁻¹`; here `w = #μ(K)` is
`torsionOrder K`. -/
theorem hasSum_norm_cpow_idealSet (J : (Ideal (𝓞 K))⁰) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun a : idealSet K J ↦ ((mixedEmbedding.norm (a : mixedSpace K) : ℝ) : ℂ) ^ (-s))
      (torsionOrder K * (absNorm (J : Ideal (𝓞 K)) : ℂ) ^ (-s) *
        ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // IsPrincipal ((𝔟 : Ideal (𝓞 K)) * (J : Ideal (𝓞 K)))},
          (absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s)) := by
  -- The summand only depends on the ideal component of `idealSetEquivPrincipal`, and the torsion
  -- component runs over a finite set of `w` elements.
  set F : {I : (Ideal (𝓞 K))⁰ // (J : Ideal (𝓞 K)) ∣ I ∧ IsPrincipal (I : Ideal (𝓞 K))} → ℂ :=
    fun I ↦ (absNorm (I : Ideal (𝓞 K)) : ℂ) ^ (-s) with hF
  have hFn : Summable fun I ↦ ‖F I‖ := by
    refine ((summable_absNorm_rpow_ideal_iff (K := K)).mpr hs).subtype _ |>.congr fun I ↦ ?_
    rw [Function.comp_apply, hF, Complex.norm_natCast_cpow_of_pos
      (absNorm_pos_of_nonZeroDivisors I.1), Complex.neg_re]
  have h1 : Summable fun _ : torsion K ↦ ‖(1 : ℂ)‖ := Summable.of_finite
  have hprod : HasSum (fun p : {I : (Ideal (𝓞 K))⁰ // (J : Ideal (𝓞 K)) ∣ I ∧
      IsPrincipal (I : Ideal (𝓞 K))} × torsion K ↦ F p.1 * 1)
      ((∑' I, F I) * ∑' _ : torsion K, (1 : ℂ)) := by
    rw [tsum_mul_tsum_of_summable_norm hFn h1]
    exact (summable_mul_of_summable_norm hFn h1).hasSum
  have hval : torsionOrder K * (absNorm (J : Ideal (𝓞 K)) : ℂ) ^ (-s) *
      ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // IsPrincipal ((𝔟 : Ideal (𝓞 K)) * (J : Ideal (𝓞 K)))},
        (absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s) = (∑' I, F I) * ∑' _ : torsion K, (1 : ℂ) := by
    rw [hF, tsum_absNorm_cpow_dvd_isPrincipal, tsum_const, torsionOrder, nsmul_eq_mul, mul_one]
    ring
  rw [hval]
  refine ((idealSetEquivPrincipal K J).hasSum_iff.mpr hprod).congr_fun fun a ↦ ?_
  simp only [Function.comp_apply, hF, mul_one, ← absNorm_idealSetEquivPrincipal_fst a,
    Complex.ofReal_natCast]

/-! ### The Dirichlet series of an ideal class -/

/-- **The Dirichlet series of an ideal class as a sum over ideals.** For `Re s > 1`, the
Dirichlet series of the class `c` of the trivial modulus, the ideal class of `J⁻¹`, is the sum of
`N(𝔟)^(-s)` over the nonzero integral ideals `𝔟` with `𝔟 J` principal. -/
theorem LSeries_rayClassCoeff_one_eq_tsum {c : RayClassGroup (Modulus.one K)}
    (J : (Ideal (𝓞 K))⁰) (hJ : idealClass (Modulus.one K) (integralIdealsPrimeToOneEquiv.symm J) =
      c⁻¹) {s : ℂ} (hs : 1 < s.re) :
    LSeries (normCoeff K (rayClassCoeff (Modulus.one K) c)) s =
      ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // IsPrincipal ((𝔟 : Ideal (𝓞 K)) * (J : Ideal (𝓞 K)))},
        (absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s) := by
  classical
  rw [LSeries_normCoeff K (summable_idealTerm_of_bounded_of_one_lt_re
    (norm_rayClassCoeff_le_one (Modulus.one K) c) hs)]
  refine Eq.symm ((tsum_subtype {𝔟 : (Ideal (𝓞 K))⁰ |
    IsPrincipal ((𝔟 : Ideal (𝓞 K)) * (J : Ideal (𝓞 K)))}
      fun 𝔟 ↦ (absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s)).trans (tsum_congr fun 𝔟 ↦ ?_))
  -- At the trivial modulus every nonzero ideal is prime to the modulus, and `𝔟` has class `c`
  -- exactly when `𝔟 J` has trivial class, that is, is principal.
  have hcop : (Modulus.one K).IsCoprimeTo (𝔟 : Ideal (𝓞 K)) :=
    Modulus.mem_integralIdealsPrimeTo.mp <| by
      simpa using (integralIdealsPrimeToOneEquiv.symm 𝔟).2
  have hclass : idealClass (Modulus.one K) ⟨𝔟, Modulus.mem_integralIdealsPrimeTo.mpr hcop⟩ = c ↔
      IsPrincipal ((𝔟 : Ideal (𝓞 K)) * (J : Ideal (𝓞 K))) := by
    rw [← mul_inv_eq_one, ← hJ, ← idealClass_mul, idealClass_one_eq_one_iff_isPrincipal,
      Submonoid.coe_mul, integralIdealsPrimeToOneEquiv_symm_apply_coe]
  rw [idealTerm_def, rayClassCoeff_apply_of_isCoprimeTo c hcop, Set.indicator_apply]
  by_cases h : IsPrincipal ((𝔟 : Ideal (𝓞 K)) * (J : Ideal (𝓞 K)))
  · simp [hclass.mpr h, h, Complex.cpow_neg]
  · simp [mt hclass.mp h, h]

/-- **The Dirichlet series of an ideal class as a sum over the fundamental cone**, Neukirch (5.3)
and (5.4). For a nonzero integral ideal `J` whose class is the inverse of the class `c` of the
trivial modulus, and `Re s > 1`,

`ζ(c, s) = N(J)^s / w · ∑_{x ∈ σ(J) ∩ cone} |N(x)|^(-s)`,

where the sum runs over the points of Mathlib's fundamental cone that are images of elements of `J`
and `w = #μ(K)` is `torsionOrder K`. -/
theorem LSeries_rayClassCoeff_one_eq_tsum_idealSet {c : RayClassGroup (Modulus.one K)}
    (J : (Ideal (𝓞 K))⁰) (hJ : idealClass (Modulus.one K) (integralIdealsPrimeToOneEquiv.symm J) =
      c⁻¹) {s : ℂ} (hs : 1 < s.re) :
    LSeries (normCoeff K (rayClassCoeff (Modulus.one K) c)) s =
      (absNorm (J : Ideal (𝓞 K)) : ℂ) ^ s / torsionOrder K *
        ∑' a : idealSet K J, ((mixedEmbedding.norm (a : mixedSpace K) : ℝ) : ℂ) ^ (-s) := by
  have hJ0 : (absNorm (J : Ideal (𝓞 K)) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (absNorm_pos_of_nonZeroDivisors J).ne'
  have hJs : (absNorm (J : Ideal (𝓞 K)) : ℂ) ^ s ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    exact fun h ↦ hJ0 h.1
  have hw : (torsionOrder K : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (torsionOrder_ne_zero K)
  rw [(hasSum_norm_cpow_idealSet J hs).tsum_eq, LSeries_rayClassCoeff_one_eq_tsum J hJ hs,
    Complex.cpow_neg]
  field_simp

/-! ### Fractional ideals in the fundamental cone -/

/-- Multiplying an invertible fractional ideal `I` by the positive integer norm of the principal
ideal of its denominator clears denominators into a nonzero integral ideal `J`. Using a positive
rational integer rather than an arbitrary algebraic integer ensures that the corresponding action
on `mixedSpace K` is a positive real dilation, which preserves `fundamentalCone K`. -/
private theorem exists_nat_spanSingleton_mul_eq_coeIdeal (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∃ (N : ℕ) (J : (Ideal (𝓞 K))⁰), 0 < N ∧
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (N : K) * (I : FractionalIdeal (𝓞 K)⁰ K) =
        (J : FractionalIdeal (𝓞 K)⁰ K) := by
  have hd : Ideal.span {(I.1.den : 𝓞 K)} ≠ ⊥ :=
    Ideal.span_singleton_eq_bot.not.mpr (nonZeroDivisors.coe_ne_zero I.1.den)
  set N : ℕ := absNorm (Ideal.span {(I.1.den : 𝓞 K)})
  have hN : 0 < N := Nat.pos_of_ne_zero (absNorm_eq_zero_iff.not.mpr hd)
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp (absNorm_mem (Ideal.span {(I.1.den : 𝓞 K)}))
  set J₀ : Ideal (𝓞 K) := Ideal.span {b} * I.1.num
  have hN_cast : (N : K) = (b : K) * ((I.1.den : 𝓞 K) : K) := by
    have := congrArg (algebraMap (𝓞 K) K) hb
    rw [map_natCast, map_mul, mul_comm] at this
    exact this
  have hJ₀ : FractionalIdeal.spanSingleton (𝓞 K)⁰ (N : K) * I.1 =
      (J₀ : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [hN_cast, map_mul (FractionalIdeal.spanSingleton (𝓞 K)⁰), mul_assoc,
      I.1.den_mul_self_eq_num', ← FractionalIdeal.coeIdeal_span_singleton,
      ← FractionalIdeal.coeIdeal_mul]
  have hJ₀_ne : J₀ ≠ ⊥ := FractionalIdeal.coeIdeal_ne_zero.mp <| by
    rw [← hJ₀]
    exact mul_ne_zero (FractionalIdeal.spanSingleton_eq_zero_iff.not.mpr
      (Nat.cast_ne_zero.mpr hN.ne')) I.ne_zero
  exact ⟨N, ⟨J₀, mem_nonZeroDivisors_of_ne_zero hJ₀_ne⟩, hN, hJ₀⟩

private theorem smul_mem_idealSet_iff {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ} {N : ℕ} (hN : 0 < N)
    {J : (Ideal (𝓞 K))⁰}
    (hJ : FractionalIdeal.spanSingleton (𝓞 K)⁰ (N : K) * (I : FractionalIdeal (𝓞 K)⁰ K) =
      (J : FractionalIdeal (𝓞 K)⁰ K)) (x : mixedSpace K) :
    (N : ℝ) • x ∈ idealSet K J ↔
      x ∈ fundamentalCone K ∩ (idealLattice K I : Set (mixedSpace K)) := by
  rw [idealSet, Set.mem_inter_iff, Set.mem_inter_iff,
    smul_mem_iff_mem (Nat.cast_ne_zero.mpr hN.ne')]
  refine and_congr_right fun _ ↦ ?_
  obtain ⟨h1, h2⟩ := FractionalIdeal.eq_spanSingleton_mul.mp hJ.symm
  simp only [SetLike.mem_coe, mem_idealLattice, FractionalIdeal.coe_mk0]
  constructor
  · rintro ⟨b, hb, hbx⟩
    obtain ⟨a, ha, rfl⟩ := h1 b hb
    refine ⟨a, ha, smul_right_injective (mixedSpace K)
      (Nat.cast_ne_zero.mpr hN.ne' : (N : ℝ) ≠ 0) ?_⟩
    dsimp only
    rw [← hbx, Nat.cast_smul_eq_nsmul ℝ, ← map_nsmul, nsmul_eq_mul]
  · rintro ⟨a, ha, rfl⟩
    refine ⟨(N : K) * a, h2 a ha, ?_⟩
    rw [Nat.cast_smul_eq_nsmul ℝ, ← map_nsmul, nsmul_eq_mul]

/-- Clearing denominators by a positive integer `N` identifies the points of `σ(I)` in the
fundamental cone with `idealSet K J` via the real dilation `(N : ℝ) • ·`. -/
private noncomputable def fundamentalConeInterIdealLatticeEquivIdealSet
    {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ} {N : ℕ} (hN : 0 < N) {J : (Ideal (𝓞 K))⁰}
    (hJ : FractionalIdeal.spanSingleton (𝓞 K)⁰ (N : K) * (I : FractionalIdeal (𝓞 K)⁰ K) =
      (J : FractionalIdeal (𝓞 K)⁰ K)) :
    ↑(fundamentalCone K ∩ (idealLattice K I : Set (mixedSpace K))) ≃ idealSet K J :=
  (MulAction.toPerm (Units.mk0 (N : ℝ) (Nat.cast_ne_zero.mpr hN.ne'))).subtypeEquiv
    fun x ↦ (smul_mem_idealSet_iff hN hJ x).symm

/-- Under `(J : FractionalIdeal (𝓞 K)⁰ K) = (N) * I`, a nonzero integral ideal `𝔟` lies in the
inverse class of `I` if and only if `𝔟 * J` is principal. -/
private theorem mk0_eq_inv_mk_iff_isPrincipal {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ} {N : ℕ}
    (hN : 0 < N) {J : (Ideal (𝓞 K))⁰}
    (hJ : FractionalIdeal.spanSingleton (𝓞 K)⁰ (N : K) * (I : FractionalIdeal (𝓞 K)⁰ K) =
      (J : FractionalIdeal (𝓞 K)⁰ K)) (𝔟 : (Ideal (𝓞 K))⁰) :
    ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹ ↔
      IsPrincipal ((𝔟 : Ideal (𝓞 K)) * (J : Ideal (𝓞 K))) := by
  have hJN : FractionalIdeal.mk0 K J =
      toPrincipalIdeal (𝓞 K) K (Units.mk0 (N : K) (Nat.cast_ne_zero.mpr hN.ne')) * I :=
    Units.ext (by simp [coe_toPrincipalIdeal, hJ])
  have hcls : ClassGroup.mk0 J = ClassGroup.mk K I := by
    rw [← ClassGroup.mk_mk0 K, hJN, map_mul, ClassGroup.mk_toPrincipalIdeal, one_mul]
  rw [← hcls, eq_inv_iff_mul_eq_one, ← map_mul, ClassGroup.mk0_eq_one_iff]
  rfl

/-- Unconditional `tsum` form of `hasSum_norm_cpow_idealSet`, valid for all `s : ℂ` (including
where neither family is summable). -/
private theorem tsum_norm_cpow_idealSet (J : (Ideal (𝓞 K))⁰) (s : ℂ) :
    ∑' a : idealSet K J, ((mixedEmbedding.norm (a : mixedSpace K) : ℝ) : ℂ) ^ (-s) =
      torsionOrder K * (absNorm (J : Ideal (𝓞 K)) : ℂ) ^ (-s) *
        ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // IsPrincipal ((𝔟 : Ideal (𝓞 K)) * (J : Ideal (𝓞 K)))},
          (absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s) := by
  set F : {I : (Ideal (𝓞 K))⁰ // (J : Ideal (𝓞 K)) ∣ I ∧ IsPrincipal (I : Ideal (𝓞 K))} → ℂ :=
    fun I ↦ (absNorm (I : Ideal (𝓞 K)) : ℂ) ^ (-s) with hF
  have ha (a : idealSet K J) :
      ((mixedEmbedding.norm (a : mixedSpace K) : ℝ) : ℂ) ^ (-s) =
        F (idealSetEquivPrincipal K J a).1 * 1 := by
    simp only [hF, mul_one, ← absNorm_idealSetEquivPrincipal_fst a, Complex.ofReal_natCast]
  simp_rw [ha]
  have hval : torsionOrder K * (absNorm (J : Ideal (𝓞 K)) : ℂ) ^ (-s) *
      ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // IsPrincipal ((𝔟 : Ideal (𝓞 K)) * (J : Ideal (𝓞 K)))},
        (absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s) = torsionOrder K * ∑' I, F I := by
    rw [hF, tsum_absNorm_cpow_dvd_isPrincipal, mul_assoc]
  rw [(idealSetEquivPrincipal K J).tsum_eq (fun p ↦ F p.1 * 1), hval]
  by_cases hFs : Summable F
  · have h1 : Summable fun _ : torsion K ↦ ‖(1 : ℂ)‖ := Summable.of_finite
    rw [← tsum_mul_tsum_of_summable_norm hFs.norm h1, tsum_const, torsionOrder, nsmul_eq_mul,
      mul_one, mul_comm]
  · have hp : ¬ Summable fun p : {I : (Ideal (𝓞 K))⁰ // (J : Ideal (𝓞 K)) ∣ I ∧
        IsPrincipal (I : Ideal (𝓞 K))} × torsion K ↦ F p.1 * 1 :=
      fun h ↦ hFs ((h.comp_injective (Prod.mk_left_injective 1)).congr fun _ ↦ mul_one _)
    rw [tsum_eq_zero_of_not_summable hp, tsum_eq_zero_of_not_summable hFs, mul_zero]

/-- **The `tsum` over the points of a fractional ideal in the fundamental cone.** For any
invertible fractional ideal `I` and all `s : ℂ` (including where neither side is summable), the
`tsum` of `|N(x)|^(-s)` over `fundamentalCone K ∩ σ(I)` is `w N(I)^(-s)` times the `tsum` of
`N(𝔟)^(-s)` over the nonzero integral ideals `𝔟` in `(ClassGroup.mk K I)⁻¹`. -/
theorem tsum_norm_cpow_fundamentalCone_inter_idealLattice
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (s : ℂ) :
    ∑' a : ↑(fundamentalCone K ∩ (idealLattice K I : Set (mixedSpace K))),
        ((mixedEmbedding.norm (a : mixedSpace K) : ℝ) : ℂ) ^ (-s) =
      torsionOrder K *
        ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) : ℂ) ^ (-s) *
        ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹},
          (absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s) := by
  obtain ⟨N, J, hN, hJ⟩ := exists_nat_spanSingleton_mul_eq_coeIdeal I
  have hNn_pos : (0 : ℝ) < (N : ℝ) ^ Module.finrank ℚ K := pow_pos (Nat.cast_pos.mpr hN) _
  have hNn_cpow_ne : (((N : ℝ) ^ Module.finrank ℚ K : ℝ) : ℂ) ^ (-s) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    exact fun h ↦ (Complex.ofReal_ne_zero.mpr hNn_pos.ne') h.1
  have hnormJ : (absNorm (J : Ideal (𝓞 K)) : ℝ) =
      (N : ℝ) ^ Module.finrank ℚ K * FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) := by
    have hq : (absNorm (J : Ideal (𝓞 K)) : ℚ) =
        (N : ℚ) ^ Module.finrank ℚ K * FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) := by
      rw [← FractionalIdeal.coeIdeal_absNorm (K := K), ← hJ, map_mul,
        FractionalIdeal.absNorm_span_singleton, ← map_natCast (algebraMap ℚ K) N,
        Algebra.norm_algebraMap, abs_of_nonneg (pow_nonneg (Nat.cast_nonneg N) _)]
    exact_mod_cast hq
  have hsumJ := ((fundamentalConeInterIdealLatticeEquivIdealSet hN hJ).tsum_eq
    (fun a : idealSet K J ↦ ((mixedEmbedding.norm (a : mixedSpace K) : ℝ) : ℂ) ^ (-s))).trans
    (tsum_norm_cpow_idealSet J s)
  have hterm (a : ↑(fundamentalCone K ∩ (idealLattice K I : Set (mixedSpace K)))) :
      ((mixedEmbedding.norm ((fundamentalConeInterIdealLatticeEquivIdealSet hN hJ a :
          idealSet K J) : mixedSpace K) : ℝ) : ℂ) ^ (-s) =
        (((N : ℝ) ^ Module.finrank ℚ K : ℝ) : ℂ) ^ (-s) *
          ((mixedEmbedding.norm (a : mixedSpace K) : ℝ) : ℂ) ^ (-s) := by
    have hcoe : ((fundamentalConeInterIdealLatticeEquivIdealSet hN hJ a : idealSet K J) :
        mixedSpace K) = (N : ℝ) • (a : mixedSpace K) := rfl
    rw [hcoe, mixedEmbedding.norm_smul, abs_of_nonneg (Nat.cast_nonneg N),
      Complex.ofReal_mul, TauCeti.ofReal_mul_cpow hNn_pos.le]
  simp_rw [hterm, tsum_mul_left] at hsumJ
  have hequiv :=
    (Equiv.subtypeEquivRight fun 𝔟 ↦ (mk0_eq_inv_mk_iff_isPrincipal hN hJ 𝔟).symm).tsum_eq
      fun 𝔟 ↦ (absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s)
  simp only [Equiv.subtypeEquivRight_apply] at hequiv
  refine mul_left_cancel₀ hNn_cpow_ne (hsumJ.trans ?_)
  rw [← Complex.ofReal_natCast (absNorm _), hnormJ, Complex.ofReal_mul,
    TauCeti.ofReal_mul_cpow hNn_pos.le, hequiv]
  ring

/-- **The sum over the points of a fractional ideal in the fundamental cone.** For an invertible
fractional ideal `I` and `Re s > 1`, the sum of `|N(x)|^(-s)` over the points `x` of `σ(I)` in
Mathlib's fundamental cone is `w N(I)^(-s)` times the sum of `N(𝔟)^(-s)` over the nonzero integral
ideals `𝔟` in the ideal class `(ClassGroup.mk K I)⁻¹`, where `w = #μ(K)` is `torsionOrder K`. -/
theorem hasSum_norm_cpow_fundamentalCone_inter_idealLattice
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ} (hs : 1 < s.re) :
    HasSum
      (fun a : ↑(fundamentalCone K ∩ (idealLattice K I : Set (mixedSpace K))) ↦
        ((mixedEmbedding.norm (a : mixedSpace K) : ℝ) : ℂ) ^ (-s))
      (torsionOrder K *
        ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) : ℂ) ^ (-s) *
        ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹},
          (absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s)) := by
  rw [← tsum_norm_cpow_fundamentalCone_inter_idealLattice I s]
  obtain ⟨N, J, hN, hJ⟩ := exists_nat_spanSingleton_mul_eq_coeIdeal I
  have hNn_pos : (0 : ℝ) < (N : ℝ) ^ Module.finrank ℚ K := pow_pos (Nat.cast_pos.mpr hN) _
  have hNn_cpow_ne : (((N : ℝ) ^ Module.finrank ℚ K : ℝ) : ℂ) ^ (-s) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    exact fun h ↦ (Complex.ofReal_ne_zero.mpr hNn_pos.ne') h.1
  have hsumJ := (fundamentalConeInterIdealLatticeEquivIdealSet hN hJ).summable_iff.mpr
    (hasSum_norm_cpow_idealSet J hs).summable
  have hcongr : (fun a : ↑(fundamentalCone K ∩ (idealLattice K I : Set (mixedSpace K))) ↦
      (((N : ℝ) ^ Module.finrank ℚ K : ℝ) : ℂ) ^ (-s) *
        ((mixedEmbedding.norm (a : mixedSpace K) : ℝ) : ℂ) ^ (-s)) =
      (fun a : idealSet K J ↦ ((mixedEmbedding.norm (a : mixedSpace K) : ℝ) : ℂ) ^ (-s)) ∘
        fundamentalConeInterIdealLatticeEquivIdealSet hN hJ := by
    ext a
    have hcoe : ((fundamentalConeInterIdealLatticeEquivIdealSet hN hJ a : idealSet K J) :
        mixedSpace K) = (N : ℝ) • (a : mixedSpace K) := rfl
    rw [Function.comp_apply, hcoe, mixedEmbedding.norm_smul, abs_of_nonneg (Nat.cast_nonneg N),
      Complex.ofReal_mul, TauCeti.ofReal_mul_cpow hNn_pos.le]
  rw [← hcongr] at hsumJ
  exact ((summable_mul_left_iff hNn_cpow_ne).mp hsumJ).hasSum

/-- **The Dirichlet series of an ideal class via `ClassGroup`.** For a class `c` of the trivial
modulus with `oneEquivClassGroup c = (ClassGroup.mk K I)⁻¹` and all `s : ℂ`, the Dirichlet series
of `c` equals the `tsum` of `N(𝔟)^(-s)` over the nonzero integral ideals `𝔟` in
`(ClassGroup.mk K I)⁻¹` (including where neither side is summable, by absence of cancellation in
norm fibres). -/
theorem LSeries_rayClassCoeff_one_eq_tsum_classGroup {c : RayClassGroup (Modulus.one K)}
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (hc : oneEquivClassGroup c = (ClassGroup.mk K I)⁻¹)
    (s : ℂ) :
    LSeries (normCoeff K (rayClassCoeff (Modulus.one K) c)) s =
      ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹},
        (absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s) := by
  classical
  set f := rayClassCoeff (Modulus.one K) c
  set S : Set (Ideal (𝓞 K))⁰ := {𝔟 | ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹}
  have hterm : idealTerm K f s =
      S.indicator fun 𝔟 ↦ (absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s) := by
    ext 𝔟
    have hcop : (Modulus.one K).IsCoprimeTo (𝔟 : Ideal (𝓞 K)) :=
      Modulus.mem_integralIdealsPrimeTo.mp (by simpa using (integralIdealsPrimeToOneEquiv.symm 𝔟).2)
    have haway : (NumberFieldArithmetic.integralIdealsAwayHom K (Modulus.one K).support
        ⟨𝔟, Modulus.mem_integralIdealsPrimeTo.mpr hcop⟩ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) =
        FractionalIdeal.mk0 K 𝔟 :=
      Units.ext (by simp [NumberFieldArithmetic.coe_integralIdealsAwayHom])
    have hclass : idealClass (Modulus.one K) ⟨𝔟, Modulus.mem_integralIdealsPrimeTo.mpr hcop⟩ = c ↔
        𝔟 ∈ S := by
      rw [← oneEquivClassGroup.injective.eq_iff, idealClass_apply, oneEquivClassGroup_rayClassMk,
        haway, ClassGroup.mk_mk0, hc]
      rfl
    rw [idealTerm_def]
    dsimp only [f]
    rw [rayClassCoeff_apply_of_isCoprimeTo c hcop, Set.indicator_apply]
    by_cases h : 𝔟 ∈ S
    · simp [hclass.mpr h, h, Complex.cpow_neg]
    · simp [mt hclass.mp h, h]
  by_cases hsum : Summable (idealTerm K f s)
  · rw [LSeries_normCoeff K hsum, hterm]
    exact (tsum_subtype S fun 𝔟 ↦ (absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s)).symm
  · have hf_nonneg : ∀ J, 0 ≤ f J := fun J ↦ by
      dsimp only [f]
      rw [rayClassCoeff_apply]
      split_ifs <;> simp
    have hLS : ¬ LSeriesSummable (normCoeff K f) s :=
      mt (summable_idealTerm_of_nonneg K f hf_nonneg) hsum
    rw [LSeries, tsum_eq_zero_of_not_summable hLS]
    exact ((tsum_subtype S fun 𝔟 ↦ (absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s)).trans
      (by rw [← hterm, tsum_eq_zero_of_not_summable hsum])).symm

/-- **The Dirichlet series of an ideal class as a sum over a fractional ideal in the fundamental
cone**, Neukirch (5.3) and (5.4). For an invertible fractional ideal `I`, a class `c` of the trivial
modulus with `oneEquivClassGroup c = (ClassGroup.mk K I)⁻¹`, and any `s : ℂ`,

`ζ(c, s) = N(I)^s / w · ∑_{x ∈ σ(I) ∩ cone} |N(x)|^(-s)`,

where `w = #μ(K)` is `torsionOrder K` (including where neither side is summable). -/
theorem LSeries_rayClassCoeff_one_eq_tsum_fundamentalCone_inter_idealLattice
    {c : RayClassGroup (Modulus.one K)} (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (hc : oneEquivClassGroup c = (ClassGroup.mk K I)⁻¹) (s : ℂ) :
    LSeries (normCoeff K (rayClassCoeff (Modulus.one K) c)) s =
      ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) : ℂ) ^ s / torsionOrder K *
        ∑' a : ↑(fundamentalCone K ∩ (idealLattice K I : Set (mixedSpace K))),
          ((mixedEmbedding.norm (a : mixedSpace K) : ℝ) : ℂ) ^ (-s) := by
  have hI0 : ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero, Rat.cast_ne_zero]
    exact FractionalIdeal.absNorm_eq_zero_iff.not.mpr I.ne_zero
  have hIs : ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) : ℂ) ^ s ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    exact fun h ↦ hI0 h.1
  have hw : (torsionOrder K : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (torsionOrder_ne_zero K)
  rw [tsum_norm_cpow_fundamentalCone_inter_idealLattice I s,
    LSeries_rayClassCoeff_one_eq_tsum_classGroup I hc s, Complex.cpow_neg]
  field_simp

end TauCeti.LFunctions
