/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
public import TauCeti.NumberTheory.LFunctions.DedekindZeta.PartialZeta
public import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.FundamentalCone
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Convergence
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Estimates
import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.IdealLattice
import TauCeti.NumberTheory.NumberField.Global.RayClass.Integral
import TauCeti.NumberTheory.NumberField.Units.Dirichlet
import TauCeti.RingTheory.FractionalIdeal.Norm

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
`NumberField.mixedEmbedding.fundamentalCone.idealSet K J`. This is Neukirch's (5.3)–(5.4): it turns
the Dirichlet series of an ideal class into a sum over the points of a lattice in a fundamental
domain for the units, which is the sum that the theta series of that lattice, integrated over a
fundamental domain on the norm-one hypersurface, produces in Hecke's proof of the functional
equation. Here `ζ(𝔎, s)` is the Dirichlet series of the class indicator
`rayClassCoeff (Modulus.one K) c`, the ray class `c` of the trivial modulus being the class of
`J⁻¹`.

The restriction to the cone, or to some other fundamental domain for the units, cannot be dropped.
In positive unit rank every nonzero element of an ideal has infinitely many distinct unit multiples
in that ideal, all generating the same principal ideal, so the sum of `N((a))^(-s)` over all
nonzero `a` of a nonzero ideal does not converge for any `s`
(`NumberField.Units.not_summable_absNorm_of_rank_pos`). A construction that sums over all the
points of the lattice, such as the radial Mellin transform of the theta series with a single
parameter, therefore cannot produce a partial zeta function once the unit rank is positive.

## Main results

* `TauCeti.LFunctions.hasSum_norm_cpow_idealLattice_fundamentalCone` and
  `TauCeti.LFunctions.tsum_absNorm_cpow_eq_mul_tsum_idealLattice_fundamentalCone`: for an
  invertible fractional ideal `I` and `Re s > 1`, the sum of `|N(x)|^(-s)` over the points of
  `idealLattice K I` in `fundamentalCone K` is `w N(I)^(-s)` times the sum of `N(𝔟)^(-s)` over the
  nonzero integral ideals `𝔟` of class `[I]⁻¹`.
* `TauCeti.LFunctions.hasSum_norm_cpow_idealSet`: the integral-ideal specialization over
  `idealSet K J`.
* `TauCeti.LFunctions.LSeries_rayClassCoeff_one_eq_tsum_oneEquivClassGroup` and
  `TauCeti.LFunctions.LSeries_rayClassCoeff_one_eq_tsum`: the Dirichlet series of a trivial-modulus
  ray class as a sum over ideals in its class.
* `TauCeti.LFunctions.LSeries_rayClassCoeff_one_eq_tsum_idealSet`: Neukirch's (5.3)–(5.4), the
  Dirichlet series of the class of `J⁻¹` as a sum over the points of `J` in the fundamental cone.
* `TauCeti.LFunctions.hasSum_norm_cpow_fundamentalCone_inter_idealLattice`: the same for an
  invertible fractional ideal `I`, as the sum of `|N(x)|^(-s)` over the points of the lattice of
  `I` in the fundamental cone.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, (5.3) and (5.4).
-/

public section

open NumberField NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
  NumberField.Units Ideal Submodule TauCeti.GlobalNumberFields
open scoped nonZeroDivisors

namespace TauCeti.LFunctions

variable {K : Type*} [Field K] [NumberField K]

/-! ### Sum over the fundamental-cone points of a fractional-ideal lattice -/

/-- **Sum of `|N(x)|^(-s)` over the points of an ideal lattice in `fundamentalCone K`.** For
`Re s > 1`, the fundamental-cone lattice sum of an invertible fractional ideal `I` is
`w N(I)^(-s)` times the ideal sum over `[I]⁻¹`. -/
theorem hasSum_norm_cpow_idealLattice_fundamentalCone (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun x : {x : idealLattice K I // (x : mixedSpace K) ∈ fundamentalCone K} ↦
        ((mixedEmbedding.norm (x : mixedSpace K) : ℝ) : ℂ) ^ (-s))
      ((torsionOrder K : ℂ) *
        ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℂ) ^ (-s) *
        ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹},
          (absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s)) := by
  let F : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹} → ℂ :=
    fun 𝔟 ↦ ((FractionalIdeal.absNorm I.val : ℚ) : ℂ) ^ (-s) *
      (absNorm (𝔟.val : Ideal (𝓞 K)) : ℂ) ^ (-s)
  have hFn : Summable fun 𝔟 ↦ ‖F 𝔟‖ := by
    have hsum : Summable fun 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹} ↦
        (absNorm (𝔟.val : Ideal (𝓞 K)) : ℝ) ^ (-s.re) :=
      ((summable_absNorm_rpow_ideal_iff (K := K)).mpr hs).subtype _
    refine (hsum.mul_left ‖((FractionalIdeal.absNorm I.val : ℚ) : ℂ) ^ (-s)‖).congr fun 𝔟 ↦ ?_
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos (absNorm_pos_of_nonZeroDivisors 𝔟.val),
      Complex.neg_re]
  have h1 : Summable fun _ : torsion K ↦ ‖(1 : ℂ)‖ := Summable.of_finite
  have hprod : HasSum
      (fun p : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹} × torsion K ↦
        F p.1 * 1)
      ((∑' 𝔟, F 𝔟) * ∑' _ : torsion K, (1 : ℂ)) := by
    rw [tsum_mul_tsum_of_summable_norm hFn h1]
    exact (summable_mul_of_summable_norm hFn h1).hasSum
  have hval : (torsionOrder K : ℂ) * ((FractionalIdeal.absNorm I.val : ℚ) : ℂ) ^ (-s) *
      (∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹},
        (absNorm (𝔟.val : Ideal (𝓞 K)) : ℂ) ^ (-s)) =
        (∑' 𝔟, F 𝔟) * ∑' _ : torsion K, (1 : ℂ) := by
    rw [tsum_const, torsionOrder, nsmul_eq_mul, mul_one, tsum_mul_left]
    ring
  rw [hval]
  refine (idealLatticeFundamentalConeEquiv I).hasSum_iff.mp (hprod.congr_fun fun p ↦ ?_)
  rw [Function.comp_apply, coe_idealLatticeFundamentalConeEquiv, norm_unit_smul,
    norm_mixedEmbedding_coneGen, Complex.ofReal_mul,
    Complex.ofReal_mul_cpow (Nat.cast_nonneg _), Complex.ofReal_natCast,
    Complex.ofReal_ratCast, mul_one]
  simp only [F, mul_comm]

/-- **Ideal-class sum in `[I]⁻¹` as a sum over `idealLattice K I ∩ fundamentalCone K`** for
`Re s > 1`, Neukirch (5.3)–(5.4). -/
theorem tsum_absNorm_cpow_eq_mul_tsum_idealLattice_fundamentalCone
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ} (hs : 1 < s.re) :
    (∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk K I)⁻¹},
        (absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s)) =
      ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℂ) ^ s /
        (torsionOrder K : ℂ) *
        ∑' x : {x : idealLattice K I // (x : mixedSpace K) ∈ fundamentalCone K},
          ((mixedEmbedding.norm (x : mixedSpace K) : ℝ) : ℂ) ^ (-s) := by
  have hI0 : ((FractionalIdeal.absNorm I.val : ℚ) : ℂ) ≠ 0 :=
    Rat.cast_ne_zero.mpr (FractionalIdeal.absNorm_pos I.ne_zero).ne'
  have hIs : ((FractionalIdeal.absNorm I.val : ℚ) : ℂ) ^ s ≠ 0 := by
    rw [ne_eq, Complex.cpow_eq_zero_iff]
    exact fun h ↦ hI0 h.1
  have hw : (torsionOrder K : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (torsionOrder_ne_zero K)
  rw [(hasSum_norm_cpow_idealLattice_fundamentalCone I hs).tsum_eq, Complex.cpow_neg]
  field_simp

/-! ### The ideals of the class of `J⁻¹` -/

private theorem tsum_mk0_eq_inv_mk0 (J : (Ideal (𝓞 K))⁰) (s : ℂ) :
    (∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = (ClassGroup.mk0 J)⁻¹},
        (absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s)) =
      ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // IsPrincipal ((𝔟 : Ideal (𝓞 K)) * (J : Ideal (𝓞 K)))},
        (absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s) := by
  have h (𝔟 : (Ideal (𝓞 K))⁰) :
      ClassGroup.mk0 𝔟 = (ClassGroup.mk0 J)⁻¹ ↔
        IsPrincipal ((𝔟 : Ideal (𝓞 K)) * (J : Ideal (𝓞 K))) := by
    rw [eq_inv_iff_mul_eq_one, ← map_mul, ClassGroup.mk0_eq_one_iff (𝔟 * J).property,
      Submonoid.coe_mul]
  exact (Equiv.subtypeEquivRight h).tsum_eq fun 𝔟 ↦ (absNorm (𝔟.val : Ideal (𝓞 K)) : ℂ) ^ (-s)

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
  have h := (idealSetEquivIdealLatticeFundamentalCone K J).hasSum_iff.mpr
    (hasSum_norm_cpow_idealLattice_fundamentalCone (FractionalIdeal.mk0 K J) hs)
  rw [FractionalIdeal.coe_mk0, FractionalIdeal.coeIdeal_absNorm, Rat.cast_natCast,
    ClassGroup.mk_mk0, tsum_mk0_eq_inv_mk0 J s] at h
  exact h.congr_fun fun a ↦ by simp

/-! ### The Dirichlet series of an ideal class -/

/-- **The Dirichlet series of a trivial-modulus ray class as a sum over its ideal class.** For
`Re s > 1`, the Dirichlet series of a class `c` of the trivial modulus is the sum of `N(𝔟)^(-s)`
over the nonzero integral ideals `𝔟` with `ClassGroup.mk0 𝔟 = oneEquivClassGroup c`. -/
theorem LSeries_rayClassCoeff_one_eq_tsum_oneEquivClassGroup (c : RayClassGroup (Modulus.one K))
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (normCoeff K (rayClassCoeff (Modulus.one K) c)) s =
      ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 𝔟 = oneEquivClassGroup c},
        (absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s) := by
  classical
  rw [LSeries_normCoeff K (summable_idealTerm_of_bounded_of_one_lt_re
    (norm_rayClassCoeff_le_one (Modulus.one K) c) hs)]
  refine Eq.symm ((tsum_subtype {𝔟 : (Ideal (𝓞 K))⁰ |
    ClassGroup.mk0 𝔟 = oneEquivClassGroup c}
      fun 𝔟 ↦ (absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s)).trans (tsum_congr fun 𝔟 ↦ ?_))
  have hcop : (Modulus.one K).IsCoprimeTo (𝔟 : Ideal (𝓞 K)) :=
    Modulus.mem_integralIdealsPrimeTo.mp <| by
      rw [← integralIdealsPrimeToOneEquiv_symm_apply_coe 𝔟]
      exact (integralIdealsPrimeToOneEquiv.symm 𝔟).property
  have hclass : idealClass (Modulus.one K) ⟨𝔟, Modulus.mem_integralIdealsPrimeTo.mpr hcop⟩ = c ↔
      ClassGroup.mk0 𝔟 = oneEquivClassGroup c := by
    rw [← oneEquivClassGroup.apply_eq_iff_eq, oneEquivClassGroup_idealClass]
    have heq : (⟨𝔟, Modulus.mem_integralIdealsPrimeTo.mpr hcop⟩ :
        integralIdealsPrimeTo (Modulus.one K)) = integralIdealsPrimeToOneEquiv.symm 𝔟 :=
      Subtype.ext (integralIdealsPrimeToOneEquiv_symm_apply_coe 𝔟).symm
    rw [heq, Equiv.apply_symm_apply]
  rw [idealTerm_def, rayClassCoeff_apply_of_isCoprimeTo c hcop, Set.indicator_apply]
  by_cases h : ClassGroup.mk0 𝔟 = oneEquivClassGroup c
  · simp [hclass.mpr h, h, Complex.cpow_neg]
  · simp [mt hclass.mp h, h]

/-- **The Dirichlet series of an ideal class as a sum over ideals.** For `Re s > 1`, the
Dirichlet series of the class `c` of the trivial modulus, the ideal class of `J⁻¹`, is the sum of
`N(𝔟)^(-s)` over the nonzero integral ideals `𝔟` with `𝔟 J` principal. -/
theorem LSeries_rayClassCoeff_one_eq_tsum {c : RayClassGroup (Modulus.one K)}
    (J : (Ideal (𝓞 K))⁰) (hJ : idealClass (Modulus.one K) (integralIdealsPrimeToOneEquiv.symm J) =
      c⁻¹) {s : ℂ} (hs : 1 < s.re) :
    LSeries (normCoeff K (rayClassCoeff (Modulus.one K) c)) s =
      ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // IsPrincipal ((𝔟 : Ideal (𝓞 K)) * (J : Ideal (𝓞 K)))},
        (absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s) := by
  have hc : oneEquivClassGroup c = (ClassGroup.mk0 J)⁻¹ := by
    rw [← inv_inv c, map_inv, ← hJ, oneEquivClassGroup_idealClass, Equiv.apply_symm_apply]
  rw [LSeries_rayClassCoeff_one_eq_tsum_oneEquivClassGroup c hs, hc, tsum_mk0_eq_inv_mk0 J s]

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
  rw [LSeries_rayClassCoeff_one_eq_tsum J hJ hs, ← tsum_mk0_eq_inv_mk0 J s,
    ← ClassGroup.mk_mk0 K J,
    tsum_absNorm_cpow_eq_mul_tsum_idealLattice_fundamentalCone (FractionalIdeal.mk0 K J) hs,
    FractionalIdeal.coe_mk0, FractionalIdeal.coeIdeal_absNorm, Rat.cast_natCast,
    ← (idealSetEquivIdealLatticeFundamentalCone K J).tsum_eq]
  simp only [coe_idealSetEquivIdealLatticeFundamentalCone]

/-! ### Fractional ideals -/

/-- An integral ideal `J = a I` differing from a fractional ideal `I` by a principal ideal `(a)`
has the class of `I`. -/
private theorem idealClass_eq_of_mk0_eq_toPrincipalIdeal_mul {c : RayClassGroup (Modulus.one K)}
    {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (hI : rayClassMk (Modulus.one K) ((idealsPrimeToEquiv Modulus.support_one).symm I) = c)
    {a : Kˣ} {J : (Ideal (𝓞 K))⁰} (hJ : FractionalIdeal.mk0 K J = toPrincipalIdeal (𝓞 K) K a * I) :
    idealClass (Modulus.one K) (integralIdealsPrimeToOneEquiv.symm J) = c := by
  have h : NumberFieldArithmetic.integralIdealsAwayHom K (Modulus.one K).support
      (integralIdealsPrimeToOneEquiv.symm J) =
        (idealsPrimeToEquiv Modulus.support_one).symm (toPrincipalIdeal (𝓞 K) K a) *
          (idealsPrimeToEquiv Modulus.support_one).symm I :=
    Subtype.ext (Units.ext (by simp [← hJ]))
  rw [← hI, idealClass_apply, h, map_mul,
    rayClassMk_eq_one_iff.mpr (mem_ray_iff.mpr ⟨_, isCongrOne_one _,
      (idealsPrimeToEquiv_symm_apply _ _).symm⟩), one_mul]

/-- **The sum over the points of a fractional ideal in the fundamental cone.** For an invertible
fractional ideal `I` whose class is the inverse of the class `c` of the trivial modulus, and
`Re s > 1`, the sum of `|N(x)|^(-s)` over the points `x` of the lattice of `I` in the fundamental
cone is `w N(I)^(-s) ζ(c, s)`, where `w = #μ(K)` is `torsionOrder K`. For a nonzero integral ideal
`LSeries_rayClassCoeff_one_eq_tsum_idealSet` is the corresponding `tsum` identity. -/
theorem hasSum_norm_cpow_fundamentalCone_inter_idealLattice {c : RayClassGroup (Modulus.one K)}
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (hI : rayClassMk (Modulus.one K) ((idealsPrimeToEquiv Modulus.support_one).symm I) = c⁻¹)
    {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun a : ↥(fundamentalCone K ∩ (idealLattice K I : Set (mixedSpace K))) ↦
        ((mixedEmbedding.norm (a : mixedSpace K) : ℝ) : ℂ) ^ (-s))
      (torsionOrder K * (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℂ) ^ (-s) *
        LSeries (normCoeff K (rayClassCoeff (Modulus.one K) c)) s) := by
  obtain ⟨n, hn, J, hJ⟩ := exists_mk0_eq_toPrincipalIdeal_natCast_mul I
  have hn' : n ≠ 0 := fun h ↦ hn (by simp [h])
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn'
  -- `J = n I` has the class of `I`, since `(n)` is principal
  have hJc := idealClass_eq_of_mk0_eq_toPrincipalIdeal_mul hI hJ
  -- multiplication by `n` carries the lattice of `I` onto the lattice of `J`
  have hmem (x : mixedSpace K) :
      (n : ℝ) • x ∈ idealLattice K (FractionalIdeal.mk0 K J) ↔ x ∈ idealLattice K I := by
    rw [hJ, Nat.cast_smul_eq_nsmul, nsmul_eq_mul, ← map_natCast (mixedEmbedding K)]
    exact mixedEmbedding_mul_mem_idealLattice_iff (Units.mk0 (n : K) hn) I
  let e : ↥(fundamentalCone K ∩ (idealLattice K I : Set (mixedSpace K))) ≃ idealSet K J :=
    { toFun a := ⟨(n : ℝ) • (a : mixedSpace K), (smul_mem_iff_mem hn0).mpr a.property.1,
        (hmem _).mpr a.property.2⟩
      invFun b := ⟨(n : ℝ)⁻¹ • (b : mixedSpace K), (smul_mem_iff_mem
          (inv_ne_zero hn0)).mpr b.property.1,
        (hmem _).mp (by rw [smul_inv_smul₀ hn0]; exact b.property.2)⟩
      left_inv a := Subtype.ext (inv_smul_smul₀ hn0 _)
      right_inv b := Subtype.ext (smul_inv_smul₀ hn0 _) }
  have hN : (absNorm (J : Ideal (𝓞 K)) : ℂ) =
      (n : ℂ) ^ Module.finrank ℚ K * FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) := by
    have h := congrArg (fun I : (FractionalIdeal (𝓞 K)⁰ K)ˣ ↦
      FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K)) hJ
    simp only [FractionalIdeal.coe_mk0, FractionalIdeal.coeIdeal_absNorm, Units.val_mul,
      coe_toPrincipalIdeal, Units.val_mk0, map_mul, FractionalIdeal.absNorm_span_singleton,
      ← map_natCast (algebraMap ℚ K), Algebra.norm_algebraMap] at h
    rw [abs_of_nonneg (by positivity)] at h
    exact_mod_cast h
  -- `(n^d)^s N(n^d x)^(-s) = N(x)^(-s)`, where `d = [K : ℚ]`
  have hscale (x : ℝ) :
      ((n : ℂ) ^ Module.finrank ℚ K) ^ s * ((n : ℂ) ^ Module.finrank ℚ K * x) ^ (-s) =
        (x : ℂ) ^ (-s) := by
    have hc : (n : ℂ) ^ Module.finrank ℚ K = (((n : ℝ) ^ Module.finrank ℚ K : ℝ) : ℂ) := by
      rw [Complex.ofReal_pow, Complex.ofReal_natCast]
    rw [hc, Complex.ofReal_mul_cpow (by positivity), ← mul_assoc, Complex.cpow_neg,
      mul_inv_cancel₀ (by simp [Complex.cpow_eq_zero_iff, hn']), one_mul]
  have h := (e.hasSum_iff.mpr (hasSum_norm_cpow_idealSet J hs)).mul_left
    (((n : ℂ) ^ Module.finrank ℚ K) ^ s)
  rw [← LSeries_rayClassCoeff_one_eq_tsum J hJc hs] at h
  convert h using 1
  · ext a
    simp only [Function.comp_apply, e, Equiv.coe_fn_mk, mixedEmbedding.norm_smul, Nat.abs_cast]
    push_cast
    rw [hscale]
  · rw [hN, ← Complex.ofReal_ratCast, ← mul_assoc, mul_left_comm _ (torsionOrder K : ℂ),
      hscale]

end TauCeti.LFunctions
