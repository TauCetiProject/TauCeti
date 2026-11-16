/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
public import Mathlib.Analysis.CStarAlgebra.Unitization

import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.UniformSpace.Compact
import TauCeti.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Polar

/-!
# Perturbation, similarity, and paths of projections in C⋆-algebras

This file develops the basic perturbation and homotopy theory of star projections and idempotents
in complex C⋆-algebras (both unital and non-unital):

1. **Exponentials of idempotents and projections.** For an idempotent `p` in any Banach algebra
   over a complete characteristic-zero nontrivially normed field `𝕜` (such as `ℝ` or `ℂ`),
   `exp (c • p) = 1 + (exp c - 1) • p`. In particular, for a star projection `r` in a complex
   Banach star algebra, `expUnitary ((t : ℂ) • r) = 1 + (exp (i t) - 1) • r`, and at `t = π`
   this equals `1 - 2 • r`. Any self-adjoint unitary `w` therefore satisfies
   `w = 1 - 2 • r = expUnitary ((π : ℂ) • r)` for the projection `r = (2 : ℂ)⁻¹ • (1 - w)`.
2. **Idempotents are similar to projections.** Every idempotent `e` in a C⋆-algebra (unital or
   non-unital, via its unitization) is similar to a star projection `p` satisfying `e * p = p` and
   `p * e = e`.
3. **Nearby projections are unitarily conjugate.** If `p` and `q` are star projections in a unital
   C⋆-algebra with `‖p - q‖ < 1`, the polar unitary `u` of `z = q * p + (1 - q) * (1 - p)`
   satisfies `u * p * star u = q`, `‖u - 1‖ ≤ √2 * ‖p - q‖ < 2`, and hence `Joined 1 u` in
   `unitary A`. Passing to the unitization `A⁺¹` extends this to arbitrary non-unital C⋆-algebras
   and produces a continuous path of projections inside `A` joining `p` to `q`.
4. **Paths of projections give unitary conjugacy.** By uniform continuity on `[0, 1]`, any
   norm-continuous path of star projections has endpoints conjugate by a unitary in the identity
   path component of `unitary A` (or `unitary A⁺¹` in the non-unital case).

## Main results

* `IsIdempotentElem.exp_smul`: `NormedSpace.exp (c • p) = 1 + (NormedSpace.exp c - 1) • p`.
* `IsStarProjection.coe_expUnitary_smul` and `IsStarProjection.coe_expUnitary_pi_smul`:
  explicit formula for `selfAdjoint.expUnitary` applied to a real multiple of a star projection.
* `IsStarProjection.half_one_sub_of_mul_self_eq_one` and `Unitary.expUnitary_pi_half_one_sub`:
  every self-adjoint unitary `w` satisfies `w = expUnitary ((π : ℂ) • ((2 : ℂ)⁻¹ • (1 - w)))`.
* `IsIdempotentElem.exists_isStarProjection_similar` and
  `IsIdempotentElem.exists_isStarProjection_similar_unitization`: every idempotent in a C⋆-algebra
  is similar to a star projection.
* `IsStarProjection.exists_unitary_conj_of_norm_sub_lt_one` and
  `IsStarProjection.exists_unitization_unitary_conj_of_norm_sub_lt_one`: projections at distance
  strictly less than `1` are conjugate by a unitary `u` with `‖u - 1‖ ≤ √2 * ‖p - q‖` and
  `Joined 1 u`.
* `IsStarProjection.exists_path_isStarProjection_of_norm_sub_lt_one`: projections at distance
  strictly less than `1` in a non-unital C⋆-algebra are joined by a path of projections in `A`.
* `IsStarProjection.exists_unitary_conj_of_path` and
  `IsStarProjection.exists_unitization_unitary_conj_of_path`: endpoints of a continuous path of
  star projections are conjugate by a unitary in the identity path component.

## References

* Bruce Blackadar, *K-Theory for Operator Algebras*, 2nd ed., MSRI Publications 5,
  Cambridge University Press, 1998, Section 4.6 (Propositions 4.6.2, 4.6.5, and 4.6.6).
-/

public section

open scoped CStarAlgebra ComplexOrder Nat NNReal Real unitInterval Ring

section Exponential

/-- The exponential of a scalar multiple of an idempotent in a Banach algebra is
`1 + (exp c - 1) • p`. -/
theorem IsIdempotentElem.exp_smul {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜]
    [ContinuousSMul ℚ 𝕜] [CompleteSpace 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A]
    {p : A} (hp : IsIdempotentElem p) (c : 𝕜) :
    NormedSpace.exp (c • p) = 1 + (NormedSpace.exp c - 1) • p := by
  have h1 : HasSum (fun n : ℕ => (n !⁻¹ : 𝕜) • (c • p) ^ n) (NormedSpace.exp (c • p)) :=
    NormedSpace.exp_series_hasSum_exp' (c • p)
  have h2 : HasSum (fun n : ℕ => (n !⁻¹ : 𝕜) • c ^ n) (NormedSpace.exp c) :=
    NormedSpace.exp_series_hasSum_exp' c
  have h2' : HasSum (fun n : ℕ => ((n + 1) !⁻¹ : 𝕜) • c ^ (n + 1)) (NormedSpace.exp c - 1) := by
    rw [← hasSum_nat_add_iff' 1] at h2
    simpa [Finset.sum_range_one] using h2
  have h3 : HasSum (fun n : ℕ => ((n + 1) !⁻¹ : 𝕜) • (c • p) ^ (n + 1))
      ((NormedSpace.exp c - 1) • p) := by
    convert h2'.smul_const p using 1
    ext n
    rw [smul_pow, hp.pow_succ_eq, smul_assoc]
  rw [← hasSum_nat_add_iff' 1] at h1
  have h4 := h1.unique h3
  simpa [Finset.sum_range_one, sub_eq_iff_eq_add', add_comm] using h4

/-- The exponential unitary `expUnitary ((t : ℂ) • r)` of a real multiple of a star projection `r`
evaluates to `1 + (Complex.exp (Complex.I * t) - 1) • r`. -/
theorem IsStarProjection.coe_expUnitary_smul {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    [StarRing A] [ContinuousStar A] [CompleteSpace A] [StarModule ℂ A]
    {r : A} (hr : IsStarProjection r) (t : ℝ) (ht : (t : ℂ) • r ∈ selfAdjoint A) :
    ((selfAdjoint.expUnitary ⟨(t : ℂ) • r, ht⟩ : unitary A) : A) =
      1 + (Complex.exp (Complex.I * t) - 1) • r := by
  simp only [selfAdjoint.expUnitary_coe]
  rw [smul_smul, hr.isIdempotentElem.exp_smul, Complex.exp_eq_exp_ℂ]

/-- Evaluating `expUnitary ((π : ℂ) • r)` for a star projection `r` gives the self-adjoint unitary
`1 - (2 : ℂ) • r`. -/
theorem IsStarProjection.coe_expUnitary_pi_smul {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    [StarRing A] [ContinuousStar A] [CompleteSpace A] [StarModule ℂ A]
    {r : A} (hr : IsStarProjection r) (hπ : (π : ℂ) • r ∈ selfAdjoint A) :
    ((selfAdjoint.expUnitary ⟨(π : ℂ) • r, hπ⟩ : unitary A) : A) = 1 - (2 : ℂ) • r := by
  rw [hr.coe_expUnitary_smul π hπ, mul_comm Complex.I (π : ℂ), Complex.exp_pi_mul_I]
  norm_num
  exact (sub_eq_add_neg 1 ((2 : ℂ) • r)).symm

/-- For a self-adjoint involution `w` (`w * w = 1`), the element `(2 : 𝕜)⁻¹ • (1 - w)` is a
star projection. -/
theorem IsStarProjection.half_one_sub_of_mul_self_eq_one {𝕜 A : Type*} [DivisionRing 𝕜]
    [CharZero 𝕜] [StarRing 𝕜] [Ring A] [StarRing A] [Module 𝕜 A] [IsScalarTower 𝕜 A A]
    [SMulCommClass 𝕜 A A] [StarModule 𝕜 A]
    {w : A} (hw : w * w = 1) (hsa : IsSelfAdjoint w) :
    IsStarProjection ((2 : 𝕜)⁻¹ • (1 - w)) where
  isIdempotentElem := by
    rw [IsIdempotentElem, smul_mul_smul_comm]
    have hmul : (1 - w) * (1 - w) = (2 : 𝕜) • (1 - w) := by
      calc (1 - w) * (1 - w) = 1 - w - w + w * w := by noncomm_ring
        _ = (2 : 𝕜) • (1 - w) := by rw [hw, two_smul]; abel
    rw [hmul, smul_smul, mul_assoc, inv_mul_cancel₀ (two_ne_zero), mul_one]
  isSelfAdjoint := by
    rw [isSelfAdjoint_iff, star_smul, star_inv₀, star_ofNat, star_sub, star_one, hsa.star_eq]

/-- Every self-adjoint unitary `u` equals `selfAdjoint.expUnitary ⟨(π : ℂ) • r, _⟩` for the star
projection `r = (2 : ℂ)⁻¹ • (1 - u)`. -/
theorem Unitary.expUnitary_pi_half_one_sub {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    [StarRing A] [ContinuousStar A] [CompleteSpace A] [StarModule ℂ A]
    (u : unitary A) (hu : IsSelfAdjoint (u : A))
    (hmem : (π : ℂ) • ((2 : ℂ)⁻¹ • (1 - (u : A))) ∈ selfAdjoint A) :
    selfAdjoint.expUnitary ⟨(π : ℂ) • ((2 : ℂ)⁻¹ • (1 - (u : A))), hmem⟩ = u := by
  have hu2 : (u : A) * (u : A) = 1 := by
    simpa [hu.star_eq] using Unitary.star_mul_self_of_mem u.2
  have hr : IsStarProjection ((2 : ℂ)⁻¹ • (1 - (u : A))) :=
    IsStarProjection.half_one_sub_of_mul_self_eq_one hu2 hu
  apply Subtype.ext
  rw [hr.coe_expUnitary_pi_smul hmem, smul_smul]
  norm_num

end Exponential

section IdempotentSimilar

private theorem commute_ring_inverse_left {A : Type*} [Semiring A] {a b : A}
    (ha : IsUnit a) (h : Commute a b) : Commute a⁻¹ʳ b := by
  obtain ⟨u, rfl⟩ := ha
  rw [Ring.inverse_unit]
  exact h.units_inv_left

private theorem exists_isStarProjection_similar_aux {A : Type*} [CStarAlgebra A]
    {e : A} (he : IsIdempotentElem e) :
    ∃ p : A, IsStarProjection p ∧ e * p = p ∧ p * e = e ∧
      ∃ s : Aˣ, (s : A) * e * ↑s⁻¹ = p := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  have hee : e * e = e := he.eq
  have hss : star e * star e = star e := by rw [← star_mul, hee]
  let z : A := 1 + star (e - star e) * (e - star e)
  have hz_pos : IsStrictlyPositive z := isStrictlyPositive_one.add_nonneg (star_mul_self_nonneg _)
  have hz_unit : IsUnit z := hz_pos.isUnit
  have hz_sa : IsSelfAdjoint z := hz_pos.isSelfAdjoint
  have hz_expand : z = 1 + star e * e - star e - e + e * star e := by
    simp only [z, star_sub, star_star]
    calc 1 + (star e - e) * (e - star e)
        = 1 + (star e * e - star e * star e - e * e + e * star e) := by noncomm_ring
      _ = 1 + star e * e - star e - e + e * star e := by rw [hss, hee]; abel
  have hez : e * z = e * star e * e := by
    rw [hz_expand]
    calc e * (1 + star e * e - star e - e + e * star e)
        = e + e * star e * e - e * star e - e * e + (e * e) * star e := by noncomm_ring
      _ = e * star e * e := by rw [hee]; abel
  have hze : z * e = e * star e * e := by
    rw [hz_expand]
    calc (1 + star e * e - star e - e + e * star e) * e
        = e + star e * (e * e) - star e * e - e * e + e * star e * e := by noncomm_ring
      _ = e * star e * e := by rw [hee]; abel
  have hcomm_e : Commute z e := hze.trans hez.symm
  have hcomm_se : Commute z (star e) := by
    rw [Commute, SemiconjBy]
    have h := congrArg star hcomm_e.eq
    simpa only [star_mul, hz_sa.star_eq] using h.symm
  have hcomm_ese : Commute z (e * star e) := hcomm_e.mul_right hcomm_se
  have hcomm_inv_e : Commute z⁻¹ʳ e := commute_ring_inverse_left hz_unit hcomm_e
  have hcomm_inv_ese : Commute z⁻¹ʳ (e * star e) := commute_ring_inverse_left hz_unit hcomm_ese
  let p : A := e * star e * z⁻¹ʳ
  have hep : e * p = p := by
    simp only [p, ← mul_assoc, hee]
  have hpe : p * e = e := by
    calc e * star e * z⁻¹ʳ * e
        = e * star e * (e * z⁻¹ʳ) := by rw [mul_assoc, hcomm_inv_e.eq, ← mul_assoc]
      _ = (e * star e * e) * z⁻¹ʳ := by noncomm_ring
      _ = (z * e) * z⁻¹ʳ := by rw [hze]
      _ = (e * z) * z⁻¹ʳ := by rw [hcomm_e.eq]
      _ = e * (z * z⁻¹ʳ) := mul_assoc _ _ _
      _ = e := by rw [Ring.mul_inverse_cancel _ hz_unit, mul_one]
  have hpp : IsIdempotentElem p := by
    rw [IsIdempotentElem]
    calc p * p = p * (e * p) := by nth_rw 2 [← hep]
      _ = (p * e) * p := (mul_assoc p e p).symm
      _ = p := by rw [hpe, hep]
  have hp_sa : IsSelfAdjoint p := by
    rw [isSelfAdjoint_iff]
    calc star p = star z⁻¹ʳ * star (e * star e) := star_mul _ _
      _ = z⁻¹ʳ * (e * star e) := by rw [← Ring.inverse_star, hz_sa.star_eq, star_mul, star_star]
      _ = e * star e * z⁻¹ʳ := hcomm_inv_ese.eq
  have hp : IsStarProjection p := ⟨hpp, hp_sa⟩
  let s : Aˣ :=
    { val := 1 - p + e
      inv := 1 + p - e
      val_inv := by
        calc (1 - p + e) * (1 + p - e)
            = 1 + p - e - p - p * p + p * e + e + e * p - e * e := by noncomm_ring
          _ = 1 := by rw [hpp.eq, hpe, hep, hee]; abel
      inv_val := by
        calc (1 + p - e) * (1 - p + e)
            = 1 - p + e + p - p * p + p * e - e + e * p - e * e := by noncomm_ring
          _ = 1 := by rw [hpp.eq, hpe, hep, hee]; abel }
  refine ⟨p, hp, hep, hpe, s, ?_⟩
  change (1 - p + e) * e * (1 + p - e) = p
  have hse : (1 - p + e) * e = e := by
    calc (1 - p + e) * e = e - p * e + e * e := by noncomm_ring
      _ = e := by rw [hpe, hee]; abel
  calc (1 - p + e) * e * (1 + p - e) = e * (1 + p - e) := by rw [hse]
    _ = e + e * p - e * e := by noncomm_ring
    _ = p := by rw [hep, hee]; abel

/-- Every idempotent in a unital C⋆-algebra is similar to a star projection with the same
range (`e * p = p` and `p * e = e`). -/
theorem IsIdempotentElem.exists_isStarProjection_similar {A : Type*} [CStarAlgebra A]
    {e : A} (he : IsIdempotentElem e) :
    ∃ p : A, IsStarProjection p ∧ e * p = p ∧ p * e = e ∧
      ∃ s : Aˣ, (s : A) * e * ↑s⁻¹ = p :=
  exists_isStarProjection_similar_aux he

/-- Every idempotent in a (possibly non-unital) C⋆-algebra is similar in the unitization `A⁺¹`
to a star projection in `A` with the same range (`e * p = p` and `p * e = e`). -/
theorem IsIdempotentElem.exists_isStarProjection_similar_unitization {A : Type*}
    [NonUnitalCStarAlgebra A] {e : A} (he : IsIdempotentElem e) :
    ∃ p : A, IsStarProjection p ∧ e * p = p ∧ p * e = e ∧
      ∃ s : (A⁺¹)ˣ, (s : A⁺¹) * (e : A⁺¹) * ↑s⁻¹ = (p : A⁺¹) := by
  have he' : IsIdempotentElem (e : A⁺¹) := by
    rw [IsIdempotentElem, ← Unitization.inr_mul, he.eq]
  obtain ⟨p', hp', hep', hpe', s, hs⟩ := he'.exists_isStarProjection_similar
  have hp'_fst : p'.fst = 0 := by
    have := congrArg (fun x : A⁺¹ => x.fst) hep'
    simpa [Unitization.fst_mul, Unitization.fst_inr] using this.symm
  have hp'_eq : (p'.snd : A⁺¹) = p' := Unitization.ext (by simp [hp'_fst]) rfl
  refine ⟨p'.snd, ?_, ?_, ?_, s, hp'_eq.symm ▸ hs⟩
  · exact IsStarProjection.of_inr (R := ℂ) (hp'_eq.symm ▸ hp')
  · exact Unitization.inr_injective (R := ℂ) (by simpa [Unitization.inr_mul, hp'_eq] using hep')
  · exact Unitization.inr_injective (R := ℂ) (by simpa [Unitization.inr_mul, hp'_eq] using hpe')

end IdempotentSimilar

section NearbyProjections

/-- **Nearby projections in a unital C⋆-algebra are unitarily conjugate.** If `p` and `q` are star
projections with `‖p - q‖ < 1`, there is a unitary `u` in the identity path component of
`unitary A` such that `u * p * star u = q` and `‖u - 1‖ ≤ √2 * ‖p - q‖`. -/
theorem IsStarProjection.exists_unitary_conj_of_norm_sub_lt_one {A : Type*} [CStarAlgebra A]
    {p q : A} (hp : IsStarProjection p) (hq : IsStarProjection q) (hpq : ‖p - q‖ < 1) :
    ∃ u : unitary A, (u : A) * p * star (u : A) = q ∧
      ‖(u : A) - 1‖ ≤ √2 * ‖p - q‖ ∧ Joined (1 : unitary A) u := by
  obtain _ | _ := subsingleton_or_nontrivial A
  · exact ⟨1, Subsingleton.elim _ _, by simp, Joined.refl 1⟩
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  have hpp : p * p = p := hp.isIdempotentElem.eq
  have hqq : q * q = q := hq.isIdempotentElem.eq
  have hps : star p = p := hp.isSelfAdjoint.star_eq
  have hqs : star q = q := hq.isSelfAdjoint.star_eq
  let z : A := q * p + (1 - q) * (1 - p)
  let d : A := (p - q) * (p - q)
  have hsz : star z = p * q + (1 - p) * (1 - q) := by
    simp only [z, star_add, star_mul, star_sub, star_one, hps, hqs]
  have hzp : z * p = q * z := by
    have h1 : z * p = q * p := by
      calc (q * p + (1 - q) * (1 - p)) * p
          = q * (p * p) + (1 - q) * (p - p * p) := by noncomm_ring
        _ = q * p := by rw [hpp]; noncomm_ring
    have h2 : q * z = q * p := by
      calc q * (q * p + (1 - q) * (1 - p))
          = (q * q) * p + (q - q * q) * (1 - p) := by noncomm_ring
        _ = q * p := by rw [hqq]; noncomm_ring
    exact h1.trans h2.symm
  have hpzs : p * star z = star z * q := by
    have := congrArg star hzp
    simpa only [star_mul, hps, hqs] using this
  have hd_eq : d = p + q - p * q - q * p := by
    calc (p - q) * (p - q) = p * p - p * q - q * p + q * q := by noncomm_ring
      _ = p + q - p * q - q * p := by rw [hpp, hqq]; abel
  have hzzs : z * star z = 1 - d := by
    rw [hsz, hd_eq]
    calc (q * p + (1 - q) * (1 - p)) * (p * q + (1 - p) * (1 - q))
        = q * (p * p) * q + q * (p - p * p) * (1 - q) +
            (1 - q) * (p - p * p) * q + (1 - q) * (1 - p - p + p * p) * (1 - q) := by noncomm_ring
      _ = q * p * q + (1 - q) * (1 - p) * (1 - q) := by rw [hpp]; noncomm_ring
      _ = q * p * q + (1 - q - q + q * q - p + q * p + p * q - q * p * q) := by noncomm_ring
      _ = 1 - (p + q - p * q - q * p) := by rw [hqq]; abel
  have hzsz : star z * z = 1 - d := by
    rw [hsz, hd_eq]
    calc (p * q + (1 - p) * (1 - q)) * (q * p + (1 - q) * (1 - p))
        = p * (q * q) * p + p * (q - q * q) * (1 - p) +
            (1 - p) * (q - q * q) * p + (1 - p) * (1 - q - q + q * q) * (1 - p) := by noncomm_ring
      _ = p * q * p + (1 - p) * (1 - q) * (1 - p) := by rw [hqq]; noncomm_ring
      _ = p * q * p + (1 - p - p + p * p - q + p * q + q * p - p * q * p) := by noncomm_ring
      _ = 1 - (p + q - p * q - q * p) := by rw [hpp]; abel
  have hz_add_sz : z + star z = (2 : ℝ) • (1 - d) := by
    rw [hsz, hd_eq, two_smul]
    simp only [z]
    noncomm_ring
  have hd_sa_prod : d = star (p - q) * (p - q) := by
    rw [star_sub, hps, hqs]
  have hd_nonneg : 0 ≤ d := hd_sa_prod ▸ star_mul_self_nonneg (p - q)
  have hd_norm : ‖d‖ = ‖p - q‖ * ‖p - q‖ := by
    rw [hd_sa_prod, CStarRing.norm_star_mul_self]
  have hd_norm_lt : ‖d‖ < 1 := by
    rw [hd_norm]
    nlinarith [norm_nonneg (p - q)]
  have h1d_unit : IsUnit (1 - d) := isUnit_one_sub_of_norm_lt_one hd_norm_lt
  have hcomm_1d_sz : Commute (1 - d) (star z) := by
    calc (1 - d) * star z = star z * z * star z := by rw [hzsz]
      _ = star z * (z * star z) := mul_assoc _ _ _
      _ = star z * (1 - d) := by rw [hzzs]
  have hz_unit : IsUnit z := by
    refine ⟨⟨z, star z * (1 - d)⁻¹ʳ, ?_, ?_⟩, rfl⟩
    · rw [← mul_assoc, hzzs, Ring.mul_inverse_cancel _ h1d_unit]
    · have hcomm_inv : Commute (1 - d)⁻¹ʳ (star z) :=
        commute_ring_inverse_left h1d_unit hcomm_1d_sz
      rw [← hcomm_inv.eq, mul_assoc, hzsz, Ring.inverse_mul_cancel _ h1d_unit]
  let zU : Aˣ := hz_unit.unit
  have hzU_val : (zU : A) = z := hz_unit.unit_spec
  let u : unitary A := zU.polarUnitary
  let s : A := CFC.sqrt (1 - d)
  have hu_eq : (u : A) = s⁻¹ʳ * z := by
    rw [Units.coe_polarUnitary, hzU_val, hzzs]
  have hs_unit : IsUnit s := by
    simpa only [s, hzU_val, hzzs] using zU.isStrictlyPositive_sqrt_mul_star.isUnit
  have h1d_nonneg : 0 ≤ 1 - d := hzzs ▸ mul_star_self_nonneg z
  have hss : s * s = 1 - d := CFC.sqrt_mul_sqrt_self (1 - d) h1d_nonneg
  have hs_sa : IsSelfAdjoint s := (CFC.sqrt_nonneg (1 - d)).isSelfAdjoint
  have hcomm_1d_q : Commute (1 - d) q := by
    calc (1 - d) * q = z * star z * q := by rw [hzzs]
      _ = z * (star z * q) := mul_assoc _ _ _
      _ = z * (p * star z) := by rw [hpzs]
      _ = (z * p) * star z := by rw [mul_assoc]
      _ = (q * z) * star z := by rw [hzp]
      _ = q * (z * star z) := mul_assoc _ _ _
      _ = q * (1 - d) := by rw [hzzs]
  have hcomm_s_q : Commute s q := hcomm_1d_q.cfcₙ_nnreal NNReal.sqrt
  have hcomm_sinv_q : Commute s⁻¹ʳ q := commute_ring_inverse_left hs_unit hcomm_s_q
  have hconj : (u : A) * p * star (u : A) = q := by
    have hup : (u : A) * p = q * (u : A) := by
      rw [hu_eq, mul_assoc, hzp, ← mul_assoc, hcomm_sinv_q.eq, mul_assoc]
    rw [hup, mul_assoc, Unitary.mul_star_self_of_mem u.2, mul_one]
  have hcomm_s_sz : Commute s (star z) := hcomm_1d_sz.cfcₙ_nnreal NNReal.sqrt
  have hcomm_sinv_sz : Commute s⁻¹ʳ (star z) := commute_ring_inverse_left hs_unit hcomm_s_sz
  have hu_add_star : (u : A) + star (u : A) = (2 : ℝ) • s := by
    have hsu : star (u : A) = s⁻¹ʳ * star z := by
      rw [hu_eq, star_mul, ← Ring.inverse_star, hs_sa.star_eq, hcomm_sinv_sz.eq]
    rw [hsu, hu_eq, ← mul_add, hz_add_sz, mul_smul_comm, ← hss, ← mul_assoc,
      Ring.inverse_mul_cancel _ hs_unit, one_mul]
  have hdiff_sq : star ((u : A) - 1) * ((u : A) - 1) = (2 : ℝ) • (1 - s) := by
    calc star ((u : A) - 1) * ((u : A) - 1)
        = (star (u : A) - 1) * ((u : A) - 1) := by rw [star_sub, star_one]
      _ = star (u : A) * (u : A) - ((u : A) + star (u : A)) + 1 := by noncomm_ring
      _ = 1 - (2 : ℝ) • s + 1 := by rw [Unitary.star_mul_self_of_mem u.2, hu_add_star]
      _ = (2 : ℝ) • (1 - s) := by rw [smul_sub, two_smul, two_smul]; abel
  have h1d_le_one : 1 - d ≤ 1 := sub_le_self 1 hd_nonneg
  have h1d_norm_le : ‖1 - d‖ ≤ 1 := by
    simpa only [norm_one] using CStarAlgebra.norm_le_norm_of_le_of_nonneg h1d_le_one h1d_nonneg
  have hs_le_one : s ≤ 1 := by
    calc s = CFC.sqrt (1 - d) := rfl
      _ ≤ CFC.sqrt 1 := CFC.sqrt_le_sqrt (1 - d) 1 h1d_le_one
      _ = 1 := CFC.sqrt_one
  have h1d_le_s : 1 - d ≤ s :=
    CStarAlgebra.self_le_sqrt_of_nonneg_of_norm_le_one h1d_nonneg h1d_norm_le
  have h1s_nonneg : 0 ≤ 1 - s := sub_nonneg.mpr hs_le_one
  have h1s_le_d : 1 - s ≤ d := sub_le_comm.mp h1d_le_s
  have h1s_norm : ‖1 - s‖ ≤ ‖d‖ :=
    CStarAlgebra.norm_le_norm_of_le_of_nonneg h1s_le_d h1s_nonneg
  have hu_norm : ‖(u : A) - 1‖ ≤ √2 * ‖p - q‖ := by
    have hsq : ‖(u : A) - 1‖ ^ 2 ≤ (√2 * ‖p - q‖) ^ 2 := by
      have hlhs : ‖(u : A) - 1‖ ^ 2 = 2 * ‖1 - s‖ := by
        rw [sq, ← CStarRing.norm_star_mul_self, hdiff_sq, norm_smul, Real.norm_ofNat]
      rw [hlhs, mul_pow, Real.sq_sqrt (by positivity), sq]
      rw [← hd_norm]
      nlinarith
    exact le_of_sq_le_sq hsq (by positivity)
  have hu_lt_two : ‖(u : A) - 1‖ < 2 := by
    have hsqrt2 : √2 < 2 := by
      rw [Real.sqrt_lt' (by norm_num)]
      norm_num
    calc ‖(u : A) - 1‖ ≤ √2 * ‖p - q‖ := hu_norm
      _ ≤ √2 * 1 := mul_le_mul_of_nonneg_left hpq.le (by positivity)
      _ = √2 := mul_one _
      _ < 2 := hsqrt2
  exact ⟨u, hconj, hu_norm, Unitary.joined 1 u hu_lt_two⟩

/-- **Nearby projections in a non-unital C⋆-algebra are unitarily conjugate in the unitization.**
If `p` and `q` are star projections in `A` with `‖p - q‖ < 1`, there is a unitary `u` in the
identity path component of `unitary A⁺¹` such that `u * p * star u = q` and
`‖u - 1‖ ≤ √2 * ‖p - q‖`. -/
theorem IsStarProjection.exists_unitization_unitary_conj_of_norm_sub_lt_one {A : Type*}
    [NonUnitalCStarAlgebra A] {p q : A} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hpq : ‖p - q‖ < 1) :
    ∃ u : unitary A⁺¹, (u : A⁺¹) * (p : A⁺¹) * star (u : A⁺¹) = (q : A⁺¹) ∧
      ‖(u : A⁺¹) - 1‖ ≤ √2 * ‖p - q‖ ∧ Joined (1 : unitary A⁺¹) u := by
  have hpq' : ‖(p : A⁺¹) - (q : A⁺¹)‖ < 1 := by
    rwa [← Unitization.inr_sub, Unitization.norm_inr]
  obtain ⟨u, hconj, hnorm, hjoin⟩ :=
    IsStarProjection.exists_unitary_conj_of_norm_sub_lt_one hp.inr hq.inr hpq'
  refine ⟨u, hconj, ?_, hjoin⟩
  simpa only [← Unitization.inr_sub, Unitization.norm_inr] using hnorm

/-- Conjugating a projection `p : A` by a unitary of the unitization `A⁺¹` yields an element
whose scalar part vanishes and whose `A`-component is a star projection in `A`. -/
theorem IsStarProjection.unitization_conj_snd {A : Type*} [NonUnitalSemiring A] [StarRing A]
    [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] [StarModule ℂ A]
    {p : A} (hp : IsStarProjection p) (u : unitary A⁺¹) :
    IsStarProjection (((u : A⁺¹) * (p : A⁺¹) * star (u : A⁺¹)).snd) ∧
      ((((u : A⁺¹) * (p : A⁺¹) * star (u : A⁺¹)).snd : A) : A⁺¹) =
        (u : A⁺¹) * (p : A⁺¹) * star (u : A⁺¹) := by
  have hfst : ((u : A⁺¹) * (p : A⁺¹) * star (u : A⁺¹)).fst = 0 := by
    simp [Unitization.fst_mul, Unitization.fst_inr]
  have hinr : ((((u : A⁺¹) * (p : A⁺¹) * star (u : A⁺¹)).snd : A) : A⁺¹) =
      (u : A⁺¹) * (p : A⁺¹) * star (u : A⁺¹) :=
    Unitization.ext (by simp [hfst]) rfl
  have hproj : IsStarProjection ((u : A⁺¹) * (p : A⁺¹) * star (u : A⁺¹)) := by
    simpa only [Unitary.conjStarAlgAut_apply] using hp.inr.map (Unitary.conjStarAlgAut ℂ A⁺¹ u)
  exact ⟨IsStarProjection.of_inr (R := ℂ) (hinr.symm ▸ hproj), hinr⟩

/-- Two star projections at distance strictly less than `1` in a (possibly non-unital) C⋆-algebra
are joined by a norm-continuous path of star projections in `A`. -/
theorem IsStarProjection.exists_path_isStarProjection_of_norm_sub_lt_one {A : Type*}
    [NonUnitalCStarAlgebra A] {p q : A} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hpq : ‖p - q‖ < 1) :
    ∃ γ : Path p q, ∀ t : I, IsStarProjection (γ t) := by
  obtain ⟨u, hconj, -, ⟨δ⟩⟩ :=
    hp.exists_unitization_unitary_conj_of_norm_sub_lt_one hq hpq
  refine ⟨⟨⟨fun t => ((δ t : A⁺¹) * (p : A⁺¹) * star (δ t : A⁺¹)).snd, ?_⟩, ?_, ?_⟩,
    fun t => (hp.unitization_conj_snd (δ t)).1⟩
  · have hδ : Continuous (fun t : I => ((δ t : unitary A⁺¹) : A⁺¹)) :=
      continuous_subtype_val.comp δ.continuous
    exact (Unitization.continuous_snd (𝕜 := ℂ) (A := A)).comp
      ((hδ.mul continuous_const).mul hδ.star)
  · simp [δ.source]
  · simp [δ.target, hconj]

end NearbyProjections

section ProjectionPath

/-- **Endpoints of a continuous path of projections are unitarily conjugate** in a unital
C⋆-algebra, by a unitary in the identity path component of `unitary A`. -/
theorem IsStarProjection.exists_unitary_conj_of_path {A : Type*} [CStarAlgebra A]
    {p q : A} (γ : Path p q) (hγ : ∀ t : I, IsStarProjection (γ t)) :
    ∃ u : unitary A, (u : A) * p * star (u : A) = q ∧ Joined (1 : unitary A) u := by
  have hunif : UniformContinuous γ := CompactSpace.uniformContinuous_of_continuous γ.continuous
  obtain ⟨δ, hδpos, hδ⟩ := Metric.uniformContinuous_iff.mp hunif 1 zero_lt_one
  obtain ⟨N, hNpos, hN⟩ : ∃ N : ℕ, 0 < N ∧ (1 : ℝ) / N < δ := by
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδpos
    exact ⟨n + 1, Nat.succ_pos n, by simpa using hn⟩
  have hNposR : (0 : ℝ) < N := Nat.cast_pos.mpr hNpos
  let grid : Fin (N + 1) → I := fun k =>
    ⟨(k : ℝ) / N, by positivity, (div_le_one hNposR).mpr (Nat.cast_le.mpr (Nat.le_of_lt_succ k.2))⟩
  have hstep : ∀ k : ℕ, (hk : k ≤ N) →
      ∃ u : unitary A, (u : A) * γ 0 * star (u : A) = γ (grid ⟨k, Nat.lt_succ_of_le hk⟩) ∧
        Joined (1 : unitary A) u := by
    intro k
    induction k with
    | zero =>
      intro _
      have h0 : grid ⟨0, Nat.lt_succ_of_le (Nat.zero_le N)⟩ = 0 := by
        ext
        simp [grid]
      refine ⟨1, ?_, Joined.refl 1⟩
      rw [h0]
      simp
    | succ k ih =>
      intro hk
      obtain ⟨u, hu_conj, hu_join⟩ := ih (Nat.le_of_succ_le hk)
      let t₁ : I := grid ⟨k, Nat.lt_succ_of_le (Nat.le_of_succ_le hk)⟩
      let t₂ : I := grid ⟨k + 1, Nat.lt_succ_of_le hk⟩
      have hdist : dist t₁ t₂ < δ := by
        have hsub : (t₁ : ℝ) - (t₂ : ℝ) = -((1 : ℝ) / N) := by
          simp only [t₁, t₂, grid, Nat.cast_add, Nat.cast_one]
          ring
        rw [Subtype.dist_eq, Real.dist_eq, hsub, abs_neg, abs_of_pos (one_div_pos.mpr hNposR)]
        exact hN
      have hnorm : ‖γ t₁ - γ t₂‖ < 1 := by
        rw [← dist_eq_norm]
        exact hδ hdist
      obtain ⟨v, hv_conj, -, hv_join⟩ :=
        IsStarProjection.exists_unitary_conj_of_norm_sub_lt_one (hγ t₁) (hγ t₂) hnorm
      refine ⟨v * u, ?_, ?_⟩
      · calc ((v * u : unitary A) : A) * γ 0 * star ((v * u : unitary A) : A)
            = (v : A) * ((u : A) * γ 0 * star (u : A)) * star (v : A) := by
              simp only [Submonoid.coe_mul, star_mul]
              noncomm_ring
          _ = (v : A) * γ t₁ * star (v : A) := by rw [hu_conj]
          _ = γ t₂ := hv_conj
      · simpa only [one_mul] using hv_join.mul hu_join
  obtain ⟨u, hu_conj, hu_join⟩ := hstep N le_rfl
  have hN1 : grid ⟨N, Nat.lt_succ_self N⟩ = 1 := by
    ext
    simp [grid, div_self hNposR.ne']
  refine ⟨u, ?_, hu_join⟩
  simpa only [γ.source, γ.target, hN1] using hu_conj

/-- **Endpoints of a continuous path of projections are unitarily conjugate in the unitization**
for any (possibly non-unital) C⋆-algebra, by a unitary in the identity path component of
`unitary A⁺¹`. -/
theorem IsStarProjection.exists_unitization_unitary_conj_of_path {A : Type*}
    [NonUnitalCStarAlgebra A] {p q : A} (γ : Path p q) (hγ : ∀ t : I, IsStarProjection (γ t)) :
    ∃ u : unitary A⁺¹, (u : A⁺¹) * (p : A⁺¹) * star (u : A⁺¹) = (q : A⁺¹) ∧
      Joined (1 : unitary A⁺¹) u :=
  IsStarProjection.exists_unitary_conj_of_path
    (γ.map (Unitization.continuous_inr (𝕜 := ℂ) (A := A))) (fun t => (hγ t).inr)

end ProjectionPath
