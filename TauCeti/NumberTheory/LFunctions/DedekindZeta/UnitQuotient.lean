/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
public import TauCeti.NumberTheory.LFunctions.DedekindZeta.PartialZeta
public import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.FundamentalCone
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Count.TrivialModulus
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Convergence
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Estimates
import TauCeti.NumberTheory.NumberField.FractionalIdeal
import TauCeti.NumberTheory.NumberField.Global.RayClass.Integral
import TauCeti.NumberTheory.NumberField.Units.Dirichlet
import TauCeti.RingTheory.ClassGroup.Basic

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

For an arbitrary invertible fractional ideal `I`, scaling `I` by a nonzero natural number into a
nonzero integral ideal `J` transports the fundamental-cone sum from `idealSet K J` to
`fundamentalCone K ∩ idealLattice K I` (`hasSum_norm_cpow_fundamentalCone`). The Dirichlet-series
identities (`LSeries_rayClassCoeff_one_eq_tsum_fractionalIdeal` and
`LSeries_rayClassCoeff_one_eq_tsum_fundamentalCone`) are proved directly for any invertible
fractional ideal `I`, with the integral-ideal identities following as specializations at
`I = FractionalIdeal.mk0 K J`.

## Main results

* `TauCeti.LFunctions.hasSum_norm_cpow_idealSet`,
  `TauCeti.LFunctions.hasSum_norm_cpow_fundamentalCone`: for `Re s > 1`, the sum of `|N(x)|^(-s)`
  over the points `x` of `J` (or of an invertible fractional ideal `I`) in the fundamental cone is
  `w N(I)^(-s)` times the sum of `N(𝔟)^(-s)` over the nonzero integral ideals `𝔟` with `𝔟 I`
  principal.
* `TauCeti.LFunctions.LSeries_rayClassCoeff_one_eq_tsum_fractionalIdeal`,
  `TauCeti.LFunctions.LSeries_rayClassCoeff_one_eq_tsum`: the Dirichlet series of an ideal class
  is that sum over ideals.
* `TauCeti.LFunctions.LSeries_rayClassCoeff_one_eq_tsum_fundamentalCone`,
  `TauCeti.LFunctions.LSeries_rayClassCoeff_one_eq_tsum_idealSet`: Neukirch's (5.3)–(5.4), the
  Dirichlet series of the class of `I⁻¹` as a sum over the points of `I` in the fundamental cone.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, (5.3) and (5.4).
-/

public section

open NumberField NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
  NumberField.Units Ideal Submodule TauCeti.GlobalNumberFields
open scoped nonZeroDivisors

namespace TauCeti.LFunctions

variable {K : Type*} [Field K] [NumberField K]

/-! ### The ideals of the class of `I⁻¹` -/

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

/-- **The sum over the points of a fractional ideal in the fundamental cone.** For `Re s > 1`,
the sum of `|N(x)|^(-s)` over the points `x` of `idealLattice K I` lying in Mathlib's fundamental
cone is `w N(I)^(-s)` times the sum of `N(𝔟)^(-s)` over the nonzero integral ideals `𝔟` whose
fractional-ideal product `𝔟 I` is principal; here `w = #μ(K)` is `torsionOrder K`. -/
theorem hasSum_norm_cpow_fundamentalCone (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s : ℂ}
    (hs : 1 < s.re) :
    HasSum (fun a : (fundamentalCone K ∩ idealLattice K I : Set (mixedSpace K)) ↦
        ((mixedEmbedding.norm (a : mixedSpace K) : ℝ) : ℂ) ^ (-s))
      (torsionOrder K * (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℂ) ^ (-s) *
        ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ //
            IsPrincipal (((𝔟 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) *
              (I : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)},
          (absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s)) := by
  obtain ⟨m, hm, J, hJ⟩ := exists_mk0_eq_toPrincipalIdeal_natCast_mul I
  set c : ℝ := (m : ℝ) ^ Module.finrank ℚ K
  have hc : 0 < c := pow_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)) _
  have hc0 : (c : ℂ) ^ (-s) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    exact fun h ↦ Complex.ofReal_ne_zero.mpr hc.ne' h.1
  have hnormJ : (absNorm (J : Ideal (𝓞 K)) : ℝ) =
      c * (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) := by
    have hq := congrArg (fun M : (FractionalIdeal (𝓞 K)⁰ K)ˣ ↦
      FractionalIdeal.absNorm (M : FractionalIdeal (𝓞 K)⁰ K)) hJ
    simp only [FractionalIdeal.coe_mk0, FractionalIdeal.coeIdeal_absNorm, Units.val_mul, map_mul,
      coe_toPrincipalIdeal, Units.val_mk0, FractionalIdeal.absNorm_span_singleton,
      Algebra.norm_natCast, abs_of_nonneg (pow_nonneg (Nat.cast_nonneg (α := ℚ) m) _)] at hq
    simpa [c] using congrArg ((↑) : ℚ → ℝ) hq
  have hmk : ClassGroup.mk0 J = ClassGroup.mk K I := by
    rw [← ClassGroup.mk_mk0 K, hJ, map_mul, ClassGroup.mk_toPrincipalIdeal, one_mul]
  have htsum : (∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // IsPrincipal ((𝔟 : Ideal (𝓞 K)) * (J : Ideal (𝓞 K)))},
      (absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s)) =
      ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ //
          IsPrincipal (((𝔟 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) *
            (I : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)},
        (absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s) :=
    (Equiv.subtypeEquivRight (ClassGroup.isPrincipal_mul_iff_of_mk0_eq hmk)).tsum_eq
      fun 𝔟 ↦ (absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s)
  have hval : (FractionalIdeal.mk0 K J : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ ((m : ℚ) : K) * (I : FractionalIdeal (𝓞 K)⁰ K) := by
    simpa [coe_toPrincipalIdeal] using congrArg Units.val hJ
  have hsumJ := (interIdealLatticeEquiv (Nat.cast_ne_zero.mpr hm) hval).hasSum_iff.mpr <| by
    simpa only [idealSet] using hasSum_norm_cpow_idealSet J hs
  rw [← Complex.ofReal_natCast (absNorm (J : Ideal (𝓞 K))), hnormJ, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg hc.le (Rat.cast_nonneg.mpr (FractionalIdeal.absNorm_nonneg _)),
    Complex.ofReal_ratCast, htsum] at hsumJ
  refine (hasSum_mul_left_iff hc0).mp ?_
  convert hsumJ using 1
  · ext a
    simp only [Function.comp_apply, interIdealLatticeEquiv_apply_coe, Rat.cast_natCast,
      mixedEmbedding.norm_smul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) m), Complex.ofReal_mul]
    exact (Complex.mul_cpow_ofReal_nonneg hc.le (mixedEmbedding.norm_nonneg _) (-s)).symm
  · ring

/-! ### The Dirichlet series of an ideal class -/

/-- Translates the trivial-modulus ray-class condition for a nonzero integral ideal `J` into the
class-group condition for `FractionalIdeal.mk0 K J`. -/
private theorem oneEquivClassGroup_eq_inv_mk_mk0 {c : RayClassGroup (Modulus.one K)}
    (J : (Ideal (𝓞 K))⁰)
    (hJ : idealClass (Modulus.one K) (integralIdealsPrimeToOneEquiv.symm J) = c⁻¹) :
    oneEquivClassGroup c = (ClassGroup.mk K (FractionalIdeal.mk0 K J))⁻¹ := by
  have hval : (NumberFieldArithmetic.integralIdealsAwayHom K (Modulus.one K).support
      (integralIdealsPrimeToOneEquiv.symm J) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) =
      FractionalIdeal.mk0 K J :=
    Units.ext <| (NumberFieldArithmetic.coe_integralIdealsAwayHom _ _).trans <| by
      rw [integralIdealsPrimeToOneEquiv_symm_apply_coe, FractionalIdeal.coe_mk0]
  have h := congrArg oneEquivClassGroup hJ
  rw [idealClass_apply, oneEquivClassGroup_rayClassMk, hval, map_inv] at h
  exact inv_eq_iff_eq_inv.mp h.symm

/-- **The Dirichlet series of an ideal class via a fractional ideal.** For an invertible fractional
ideal `I` and the ray class `c` of the trivial modulus corresponding to the ideal class `[I]⁻¹`,
and `Re s > 1`, `ζ(c, s)` is the sum of `N(𝔟)^(-s)` over the nonzero integral ideals `𝔟` whose
product `𝔟 I` is principal. -/
theorem LSeries_rayClassCoeff_one_eq_tsum_fractionalIdeal {c : RayClassGroup (Modulus.one K)}
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (hI : oneEquivClassGroup c = (ClassGroup.mk K I)⁻¹)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (normCoeff K (rayClassCoeff (Modulus.one K) c)) s =
      ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ //
          IsPrincipal (((𝔟 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) *
            (I : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)},
        (absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s) := by
  classical
  rw [LSeries_normCoeff K (summable_idealTerm_of_bounded_of_one_lt_re
    (norm_rayClassCoeff_le_one (Modulus.one K) c) hs)]
  set S : Set (Ideal (𝓞 K))⁰ := {𝔟 : (Ideal (𝓞 K))⁰ |
    IsPrincipal (((𝔟 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) *
      (I : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)}
  refine Eq.symm ((tsum_subtype S fun 𝔟 ↦ (absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s)).trans
    (tsum_congr fun 𝔟 ↦ ?_))
  -- At the trivial modulus every nonzero ideal is prime to the modulus, and `𝔟` has class `c`
  -- exactly when `𝔟 I` has trivial class, that is, is principal.
  have hcop : (Modulus.one K).IsCoprimeTo (𝔟 : Ideal (𝓞 K)) :=
    Modulus.mem_integralIdealsPrimeTo.mp <| by
      simpa using (integralIdealsPrimeToOneEquiv.symm 𝔟).2
  have hclass : idealClass (Modulus.one K) ⟨𝔟, Modulus.mem_integralIdealsPrimeTo.mpr hcop⟩ = c ↔
      𝔟 ∈ S := by
    rw [← oneEquivClassGroup.injective.eq_iff, idealClass_apply, oneEquivClassGroup_rayClassMk,
      hI, eq_inv_iff_mul_eq_one, ← map_mul, ClassGroup.mk_eq_one_iff, Units.val_mul,
      NumberFieldArithmetic.coe_integralIdealsAwayHom, FractionalIdeal.coeToSubmodule_mul]
    rfl
  rw [idealTerm_def, rayClassCoeff_apply_of_isCoprimeTo c hcop]
  by_cases h : 𝔟 ∈ S
  · simp [Set.indicator_of_mem h, hclass.mpr h, Complex.cpow_neg]
  · simp [Set.indicator_of_notMem h, mt hclass.mp h]

/-- **The Dirichlet series of an ideal class as a sum over ideals.** For `Re s > 1`, the
Dirichlet series of the class `c` of the trivial modulus, the ideal class of `J⁻¹`, is the sum of
`N(𝔟)^(-s)` over the nonzero integral ideals `𝔟` with `𝔟 J` principal. -/
theorem LSeries_rayClassCoeff_one_eq_tsum {c : RayClassGroup (Modulus.one K)}
    (J : (Ideal (𝓞 K))⁰) (hJ : idealClass (Modulus.one K) (integralIdealsPrimeToOneEquiv.symm J) =
      c⁻¹) {s : ℂ} (hs : 1 < s.re) :
    LSeries (normCoeff K (rayClassCoeff (Modulus.one K) c)) s =
      ∑' 𝔟 : {𝔟 : (Ideal (𝓞 K))⁰ // IsPrincipal ((𝔟 : Ideal (𝓞 K)) * (J : Ideal (𝓞 K)))},
        (absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s) := by
  rw [LSeries_rayClassCoeff_one_eq_tsum_fractionalIdeal (FractionalIdeal.mk0 K J)
    (oneEquivClassGroup_eq_inv_mk_mk0 J hJ) hs]
  exact (Equiv.subtypeEquivRight fun 𝔟 ↦
    (ClassGroup.isPrincipal_mul_iff_of_mk0_eq (ClassGroup.mk_mk0 K J).symm 𝔟).symm).tsum_eq
      fun 𝔟 ↦ (absNorm (𝔟 : Ideal (𝓞 K)) : ℂ) ^ (-s)

/-- **The Dirichlet series of an ideal class as a fundamental-cone sum for a fractional ideal**,
Neukirch (5.3) and (5.4). For an invertible fractional ideal `I` and the ray class `c` of the
trivial modulus corresponding to `[I]⁻¹`, and `Re s > 1`,

`ζ(c, s) = N(I)^s / w · ∑_{x ∈ σ(I) ∩ cone} |N(x)|^(-s)`,

where `w = #μ(K)` is `torsionOrder K`. -/
theorem LSeries_rayClassCoeff_one_eq_tsum_fundamentalCone {c : RayClassGroup (Modulus.one K)}
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (hI : oneEquivClassGroup c = (ClassGroup.mk K I)⁻¹)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (normCoeff K (rayClassCoeff (Modulus.one K) c)) s =
      (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℂ) ^ s / torsionOrder K *
        ∑' a : (fundamentalCone K ∩ idealLattice K I : Set (mixedSpace K)),
          ((mixedEmbedding.norm (a : mixedSpace K) : ℝ) : ℂ) ^ (-s) := by
  have hI0 : (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℂ) ≠ 0 :=
    Rat.cast_ne_zero.mpr (FractionalIdeal.absNorm_eq_zero_iff.not.mpr I.ne_zero)
  have hIs : (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℂ) ^ s ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    exact fun h ↦ hI0 h.1
  have hw : (torsionOrder K : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (torsionOrder_ne_zero K)
  rw [(hasSum_norm_cpow_fundamentalCone I hs).tsum_eq,
    LSeries_rayClassCoeff_one_eq_tsum_fractionalIdeal I hI hs, Complex.cpow_neg]
  field_simp

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
  simpa [idealSet, FractionalIdeal.coe_mk0, FractionalIdeal.coeIdeal_absNorm] using
    LSeries_rayClassCoeff_one_eq_tsum_fundamentalCone (FractionalIdeal.mk0 K J)
      (oneEquivClassGroup_eq_inv_mk_mk0 J hJ) hs

end TauCeti.LFunctions
