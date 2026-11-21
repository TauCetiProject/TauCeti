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
import TauCeti.Analysis.CStarAlgebra.Idempotent
import TauCeti.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Polar

/-!
# Perturbation, similarity, and paths of projections in C⋆-algebras

Perturbation and homotopy theory for star projections and idempotents in complex C⋆-algebras:

* `IsIdempotentElem.exp_smul`, `IsStarProjection.coe_expUnitary_smul`, `.coe_expUnitary_pi_smul`,
  `.half_one_sub_of_mul_self_eq_one`, `Unitary.expUnitary_pi_half_one_sub`: exponentials of
  idempotents, projections, and self-adjoint unitaries.
* `IsIdempotentElem.exists_isStarProjection_similar_unitization`: every idempotent is similar in
  the unitization to a star projection with the same range.
* `IsStarProjection.exists_unitary_conj_of_norm_sub_lt_one`,
  `.exists_unitization_unitary_conj_of_norm_sub_lt_one`,
  `.exists_path_isStarProjection_of_norm_sub_lt_one`, `.exists_unitary_conj_of_path`,
  `.exists_unitization_unitary_conj_of_path`: nearby projections (`‖p - q‖ < 1`) and endpoints of
  projection paths are unitarily conjugate in the identity path component.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., Cambridge University Press, 1998, §4.6
  (Propositions 4.6.2, 4.6.5, and 4.6.6).
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
  have h1 := (hasSum_nat_add_iff' 1).mpr (NormedSpace.exp_series_hasSum_exp' (𝕂 := 𝕜) (c • p))
  have h2 : HasSum (fun n : ℕ => ((n + 1) !⁻¹ : 𝕜) • c ^ (n + 1)) (NormedSpace.exp c - 1) := by
    simpa [Finset.sum_range_one] using
      (hasSum_nat_add_iff' 1).mpr (NormedSpace.exp_series_hasSum_exp' (𝕂 := 𝕜) c)
  have h3 : HasSum (fun n : ℕ => ((n + 1) !⁻¹ : 𝕜) • (c • p) ^ (n + 1))
      ((NormedSpace.exp c - 1) • p) := by
    convert h2.smul_const p using 1
    ext n; rw [smul_pow, hp.pow_succ_eq, smul_assoc]
  simpa [Finset.sum_range_one, sub_eq_iff_eq_add', add_comm] using h1.unique h3

/-- The exponential unitary `expUnitary ((t : ℂ) • r)` of a real multiple of a star projection `r`
evaluates to `1 + (Complex.exp (Complex.I * t) - 1) • r`. -/
theorem IsStarProjection.coe_expUnitary_smul {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    [StarRing A] [ContinuousStar A] [CompleteSpace A] [StarModule ℂ A]
    {r : A} (hr : IsStarProjection r) (t : ℝ) (ht : (t : ℂ) • r ∈ selfAdjoint A) :
    ((selfAdjoint.expUnitary ⟨(t : ℂ) • r, ht⟩ : unitary A) : A) =
      1 + (Complex.exp (Complex.I * t) - 1) • r := by
  simp only [selfAdjoint.expUnitary_coe]
  rw [smul_smul, hr.isIdempotentElem.exp_smul, Complex.exp_eq_exp_ℂ]

/-- Evaluating `expUnitary ((π : ℂ) • r)` for a star projection `r` gives `1 - (2 : ℂ) • r`. -/
theorem IsStarProjection.coe_expUnitary_pi_smul {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    [StarRing A] [ContinuousStar A] [CompleteSpace A] [StarModule ℂ A]
    {r : A} (hr : IsStarProjection r) (hπ : (π : ℂ) • r ∈ selfAdjoint A) :
    ((selfAdjoint.expUnitary ⟨(π : ℂ) • r, hπ⟩ : unitary A) : A) = 1 - (2 : ℂ) • r := by
  rw [hr.coe_expUnitary_smul π hπ, mul_comm Complex.I (π : ℂ), Complex.exp_pi_mul_I]
  norm_num; exact (sub_eq_add_neg 1 ((2 : ℂ) • r)).symm

/-- For a self-adjoint involution `w` (`w * w = 1`), `(2 : 𝕜)⁻¹ • (1 - w)` is a star projection. -/
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
    rw [hmul, smul_smul, mul_assoc, inv_mul_cancel₀ two_ne_zero, mul_one]
  isSelfAdjoint := by
    rw [isSelfAdjoint_iff, star_smul, star_inv₀, star_ofNat, star_sub, star_one, hsa.star_eq]

/-- Every self-adjoint unitary `u` equals `selfAdjoint.expUnitary ⟨(π : ℂ) • r, _⟩` for
`r = (2 : ℂ)⁻¹ • (1 - u)`. -/
theorem Unitary.expUnitary_pi_half_one_sub {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    [StarRing A] [ContinuousStar A] [CompleteSpace A] [StarModule ℂ A]
    (u : unitary A) (hu : IsSelfAdjoint (u : A))
    (hmem : (π : ℂ) • ((2 : ℂ)⁻¹ • (1 - (u : A))) ∈ selfAdjoint A) :
    selfAdjoint.expUnitary ⟨(π : ℂ) • ((2 : ℂ)⁻¹ • (1 - (u : A))), hmem⟩ = u := by
  have hu2 : (u : A) * (u : A) = 1 := by
    simpa [hu.star_eq] using Unitary.star_mul_self_of_mem u.property
  apply Subtype.ext
  rw [(IsStarProjection.half_one_sub_of_mul_self_eq_one hu2 hu).coe_expUnitary_pi_smul hmem,
    smul_smul]
  norm_num

end Exponential

section IdempotentSimilar

private theorem commute_ring_inverse_left {A : Type*} [Semiring A] {a b : A}
    (ha : IsUnit a) (h : Commute a b) : Commute a⁻¹ʳ b := by
  obtain ⟨u, rfl⟩ := ha; rw [Ring.inverse_unit]; exact h.units_inv_left

/-- Every idempotent in a (possibly non-unital) C⋆-algebra is similar in the unitization `A⁺¹`
to a star projection in `A` with the same range (`e * p = p` and `p * e = e`). -/
theorem IsIdempotentElem.exists_isStarProjection_similar_unitization {A : Type*}
    [NonUnitalCStarAlgebra A] {e : A} (he : IsIdempotentElem e) :
    ∃ p : A, IsStarProjection p ∧ e * p = p ∧ p * e = e ∧
      ∃ s : (A⁺¹)ˣ, (s : A⁺¹) * (e : A⁺¹) * ↑s⁻¹ = (p : A⁺¹) := by
  have he' : IsIdempotentElem (e : A⁺¹) := by rw [IsIdempotentElem, ← Unitization.inr_mul, he.eq]
  let p' : A⁺¹ := TauCeti.idempotentRangeProjection (e : A⁺¹)
  have hp' : IsStarProjection p' := he'.isStarProjection_idempotentRangeProjection
  have hep' : (e : A⁺¹) * p' = p' := he'.mul_idempotentRangeProjection
  have hpe' : p' * (e : A⁺¹) = (e : A⁺¹) := he'.idempotentRangeProjection_mul
  have hp'_fst : p'.fst = 0 := by
    simpa [Unitization.fst_mul, Unitization.fst_inr] using
      (congrArg (fun x : A⁺¹ => x.fst) hep').symm
  have hp'_eq : (p'.snd : A⁺¹) = p' := Unitization.ext (by simp [hp'_fst]) rfl
  refine ⟨p'.snd, IsStarProjection.of_inr (R := ℂ) (hp'_eq.symm ▸ hp'), ?_, ?_,
    TauCeti.idempotentConjUnit (e : A⁺¹) p' hep' hpe', ?_⟩
  · exact Unitization.inr_injective (R := ℂ) (by simpa [Unitization.inr_mul, hp'_eq] using hep')
  · exact Unitization.inr_injective (R := ℂ) (by simpa [Unitization.inr_mul, hp'_eq] using hpe')
  · simpa [hp'_eq] using TauCeti.idempotentConjUnit_mul_mul_inv (e : A⁺¹) p' hep' hpe'

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
  have hpp := hp.isIdempotentElem.eq; have hqq := hq.isIdempotentElem.eq
  have hps := hp.isSelfAdjoint.star_eq; have hqs := hq.isSelfAdjoint.star_eq
  let z : A := q * p + (1 - q) * (1 - p)
  let d : A := (p - q) * (p - q)
  have hsz : star z = p * q + (1 - p) * (1 - q) := by
    simp only [z, star_add, star_mul, star_sub, star_one, hps, hqs]
  have hzp : z * p = q * z := by
    calc z * p = q * p := by simp [z, add_mul, mul_assoc, hpp, sub_mul]
      _ = q * z := by simp [z, mul_add, ← mul_assoc, hqq, mul_sub]
  have hpzs : p * star z = star z * q := by
    simpa only [star_mul, hps, hqs] using congrArg star hzp
  have hd_eq : d = p + q - p * q - q * p := by
    calc (p - q) * (p - q) = p * p - p * q - q * p + q * q := by noncomm_ring
      _ = p + q - p * q - q * p := by rw [hpp, hqq]; abel
  have hmul_aux {a b : A} (ha : a * a = a) (hb : b * b = b) :
      (b * a + (1 - b) * (1 - a)) * (a * b + (1 - a) * (1 - b)) =
        1 - (a + b - a * b - b * a) := by
    calc (b * a + (1 - b) * (1 - a)) * (a * b + (1 - a) * (1 - b))
        = b * (a * a) * b + b * (a - a * a) * (1 - b) + (1 - b) * (a - a * a) * b +
            (1 - b) * (1 - a - a + a * a) * (1 - b) := by noncomm_ring
      _ = b * a * b + (1 - b - b + b * b - a + b * a + a * b - b * a * b) := by
            rw [ha]; noncomm_ring
      _ = 1 - (a + b - a * b - b * a) := by rw [hb]; abel
  have hzzs : z * star z = 1 - d := by rw [hsz, hd_eq]; exact hmul_aux hpp hqq
  have hzsz : star z * z = 1 - d := by rw [hsz, hd_eq]; convert hmul_aux hqq hpp using 2; abel
  have hz_add_sz : z + star z = (2 : ℝ) • (1 - d) := by
    rw [hsz, hd_eq, two_smul]; simp only [z]; noncomm_ring
  have hd_sa_prod : d = star (p - q) * (p - q) := by rw [star_sub, hps, hqs]
  have hd_norm : ‖d‖ = ‖p - q‖ * ‖p - q‖ := by rw [hd_sa_prod, CStarRing.norm_star_mul_self]
  have h1d_unit : IsUnit (1 - d) := isUnit_one_sub_of_norm_lt_one (by
    rw [hd_norm]; nlinarith [norm_nonneg (p - q)])
  have hcomm_1d_sz : Commute (1 - d) (star z) := by
    rw [Commute, SemiconjBy]; nth_rw 1 [← hzsz]; rw [mul_assoc, hzzs]
  have hz_unit : IsUnit z := ⟨⟨z, star z * (1 - d)⁻¹ʳ,
    by rw [← mul_assoc, hzzs, Ring.mul_inverse_cancel _ h1d_unit],
    by rw [← (commute_ring_inverse_left h1d_unit hcomm_1d_sz).eq, mul_assoc, hzsz,
      Ring.inverse_mul_cancel _ h1d_unit]⟩, rfl⟩
  let zU : Aˣ := hz_unit.unit
  have hzU_val : (zU : A) = z := hz_unit.unit_spec
  let u : unitary A := zU.polarUnitary
  let s : A := CFC.sqrt (1 - d)
  have hu_eq : (u : A) = s⁻¹ʳ * z := by rw [Units.coe_polarUnitary, hzU_val, hzzs]
  have hs_unit : IsUnit s := by
    simpa only [s, hzU_val, hzzs] using zU.isStrictlyPositive_sqrt_mul_star.isUnit
  have h1d_nonneg : 0 ≤ 1 - d := hzzs ▸ mul_star_self_nonneg z
  have hss : s * s = 1 - d := CFC.sqrt_mul_sqrt_self (1 - d) h1d_nonneg
  have hcomm_1d_q : Commute (1 - d) q := by
    rw [Commute, SemiconjBy, ← hzzs, mul_assoc, ← hpzs, ← mul_assoc, hzp, mul_assoc]
  have hconj : (u : A) * p * star (u : A) = q := by
    have hup : (u : A) * p = q * (u : A) := by
      rw [hu_eq, mul_assoc, hzp, ← mul_assoc,
        (commute_ring_inverse_left hs_unit (hcomm_1d_q.cfcₙ_nnreal NNReal.sqrt)).eq, mul_assoc]
    rw [hup, mul_assoc, Unitary.mul_star_self_of_mem u.property, mul_one]
  have hu_add_star : (u : A) + star (u : A) = (2 : ℝ) • s := by
    have hsu : star (u : A) = s⁻¹ʳ * star z := by
      rw [hu_eq, star_mul, ← Ring.inverse_star, (CFC.sqrt_nonneg (1 - d)).isSelfAdjoint.star_eq,
        (commute_ring_inverse_left hs_unit (hcomm_1d_sz.cfcₙ_nnreal NNReal.sqrt)).eq]
    rw [hsu, hu_eq, ← mul_add, hz_add_sz, mul_smul_comm, ← hss, ← mul_assoc,
      Ring.inverse_mul_cancel _ hs_unit, one_mul]
  have hdiff_sq : star ((u : A) - 1) * ((u : A) - 1) = (2 : ℝ) • (1 - s) := by
    calc star ((u : A) - 1) * ((u : A) - 1)
        = star (u : A) * (u : A) - ((u : A) + star (u : A)) + 1 := by
          rw [star_sub, star_one]; noncomm_ring
      _ = (2 : ℝ) • (1 - s) := by
          rw [Unitary.star_mul_self_of_mem u.property, hu_add_star, smul_sub, two_smul, two_smul]
          abel
  have h1d_le : 1 - d ≤ 1 := sub_le_self 1 (hd_sa_prod ▸ star_mul_self_nonneg (p - q))
  have h1d_norm_le : ‖1 - d‖ ≤ 1 := by
    simpa only [norm_one] using CStarAlgebra.norm_le_norm_of_le_of_nonneg h1d_le h1d_nonneg
  have h1s_norm : ‖1 - s‖ ≤ ‖d‖ :=
    CStarAlgebra.norm_le_norm_of_le_of_nonneg
      (sub_le_comm.mp (CStarAlgebra.self_le_sqrt_of_nonneg_of_norm_le_one h1d_nonneg h1d_norm_le))
      (sub_nonneg.mpr (CFC.sqrt_one (A := A) ▸ CFC.sqrt_le_sqrt (1 - d) 1 h1d_le))
  have hu_norm : ‖(u : A) - 1‖ ≤ √2 * ‖p - q‖ := by
    refine le_of_sq_le_sq ?_ (by positivity)
    have hlhs : ‖(u : A) - 1‖ ^ 2 = 2 * ‖1 - s‖ := by
      rw [sq, ← CStarRing.norm_star_mul_self, hdiff_sq, norm_smul, Real.norm_ofNat]
    rw [hlhs, mul_pow, Real.sq_sqrt (by positivity), sq, ← hd_norm]; nlinarith
  refine ⟨u, hconj, hu_norm, Unitary.joined 1 u ?_⟩
  have hsqrt2 : √2 < 2 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  exact (hu_norm.trans ((mul_le_mul_of_nonneg_left hpq.le (by positivity)).trans_eq
    (mul_one _))).trans_lt hsqrt2

/-- **Nearby projections in a non-unital C⋆-algebra are unitarily conjugate in the unitization.**
If `p` and `q` are star projections in `A` with `‖p - q‖ < 1`, there is a unitary `u` in the
identity path component of `unitary A⁺¹` such that `u * p * star u = q` and
`‖u - 1‖ ≤ √2 * ‖p - q‖`. -/
theorem IsStarProjection.exists_unitization_unitary_conj_of_norm_sub_lt_one {A : Type*}
    [NonUnitalCStarAlgebra A] {p q : A} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hpq : ‖p - q‖ < 1) :
    ∃ u : unitary A⁺¹, (u : A⁺¹) * (p : A⁺¹) * star (u : A⁺¹) = (q : A⁺¹) ∧
      ‖(u : A⁺¹) - 1‖ ≤ √2 * ‖p - q‖ ∧ Joined (1 : unitary A⁺¹) u := by
  have hpq' : ‖(p : A⁺¹) - (q : A⁺¹)‖ < 1 := by rwa [← Unitization.inr_sub, Unitization.norm_inr]
  obtain ⟨u, hconj, hnorm, hjoin⟩ :=
    IsStarProjection.exists_unitary_conj_of_norm_sub_lt_one hp.inr hq.inr hpq'
  exact ⟨u, hconj, by simpa only [← Unitization.inr_sub, Unitization.norm_inr] using hnorm, hjoin⟩

/-- Conjugating a projection `p : A` by a unitary of `A⁺¹` yields an element whose scalar part
vanishes and whose `A`-component is a star projection in `A`. -/
theorem IsStarProjection.unitization_conj_snd {A : Type*} [NonUnitalSemiring A] [StarRing A]
    [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] [StarModule ℂ A]
    {p : A} (hp : IsStarProjection p) (u : unitary A⁺¹) :
    IsStarProjection (((u : A⁺¹) * (p : A⁺¹) * star (u : A⁺¹)).snd) ∧
      ((((u : A⁺¹) * (p : A⁺¹) * star (u : A⁺¹)).snd : A) : A⁺¹) =
        (u : A⁺¹) * (p : A⁺¹) * star (u : A⁺¹) := by
  have hinr : ((((u : A⁺¹) * (p : A⁺¹) * star (u : A⁺¹)).snd : A) : A⁺¹) =
      (u : A⁺¹) * (p : A⁺¹) * star (u : A⁺¹) :=
    Unitization.ext (by simp [Unitization.fst_mul, Unitization.fst_inr]) rfl
  have hproj : IsStarProjection ((u : A⁺¹) * (p : A⁺¹) * star (u : A⁺¹)) := by
    simpa only [Unitary.conjStarAlgAut_apply] using hp.inr.map (Unitary.conjStarAlgAut ℂ A⁺¹ u)
  exact ⟨IsStarProjection.of_inr (R := ℂ) (hinr.symm ▸ hproj), hinr⟩

/-- Two star projections at distance strictly less than `1` in a (possibly non-unital) C⋆-algebra
are joined by a norm-continuous path of star projections in `A`. -/
theorem IsStarProjection.exists_path_isStarProjection_of_norm_sub_lt_one {A : Type*}
    [NonUnitalCStarAlgebra A] {p q : A} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hpq : ‖p - q‖ < 1) :
    ∃ γ : Path p q, ∀ t : I, IsStarProjection (γ t) := by
  obtain ⟨u, hconj, -, ⟨δ⟩⟩ := hp.exists_unitization_unitary_conj_of_norm_sub_lt_one hq hpq
  refine ⟨⟨⟨fun t => ((δ t : A⁺¹) * (p : A⁺¹) * star (δ t : A⁺¹)).snd, ?_⟩,
    by simp [δ.source], by simp [δ.target, hconj]⟩, fun t => (hp.unitization_conj_snd (δ t)).1⟩
  have hδ : Continuous (fun t : I => ((δ t : unitary A⁺¹) : A⁺¹)) :=
    continuous_subtypeVal.comp δ.continuous
  exact (Unitization.continuous_snd (𝕜 := ℂ) (A := A)).comp
    ((hδ.mul continuous_const).mul hδ.star)

end NearbyProjections

section ProjectionPath

/-- **Endpoints of a continuous path of projections are unitarily conjugate** in a unital
C⋆-algebra, by a unitary in the identity path component of `unitary A`. -/
theorem IsStarProjection.exists_unitary_conj_of_path {A : Type*} [CStarAlgebra A]
    {p q : A} (γ : Path p q) (hγ : ∀ t : I, IsStarProjection (γ t)) :
    ∃ u : unitary A, (u : A) * p * star (u : A) = q ∧ Joined (1 : unitary A) u := by
  obtain ⟨δ, hδpos, hδ⟩ :=
    Metric.uniformContinuous_iff.mp (CompactSpace.uniformContinuous_of_continuous γ.continuous)
      1 zero_lt_one
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδpos
  let N : ℕ := n + 1
  have hNposR : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.succ_pos n)
  let grid : Fin (N + 1) → I := fun k =>
    ⟨(k : ℝ) / N, by positivity,
      (div_le_one hNposR).mpr (Nat.cast_le.mpr (Nat.le_of_lt_succ k.isLt))⟩
  have hstep : ∀ k : ℕ, (hk : k ≤ N) →
      ∃ u : unitary A, (u : A) * γ 0 * star (u : A) = γ (grid ⟨k, Nat.lt_succ_of_le hk⟩) ∧
        Joined (1 : unitary A) u := fun k => by
    induction k with
    | zero =>
      exact fun _ => ⟨1, by rw [show grid ⟨0, _⟩ = 0 from Subtype.ext (by simp [grid])]; simp,
        Joined.refl 1⟩
    | succ k ih =>
      intro hk
      obtain ⟨u, hu_conj, hu_join⟩ := ih (Nat.le_of_succ_le hk)
      let t₁ : I := grid ⟨k, Nat.lt_succ_of_le (Nat.le_of_succ_le hk)⟩
      let t₂ : I := grid ⟨k + 1, Nat.lt_succ_of_le hk⟩
      have hnorm : ‖γ t₁ - γ t₂‖ < 1 := by
        rw [← dist_eq_norm]
        refine hδ ?_
        rw [Subtype.dist_eq, Real.dist_eq, show (t₁ : ℝ) - (t₂ : ℝ) = -((1 : ℝ) / N) by
          simp only [t₁, t₂, grid, Nat.cast_add, Nat.cast_one]; ring,
          abs_neg, abs_of_pos (one_div_pos.mpr hNposR)]
        simpa [N] using hn
      obtain ⟨v, hv_conj, -, hv_join⟩ :=
        IsStarProjection.exists_unitary_conj_of_norm_sub_lt_one (hγ t₁) (hγ t₂) hnorm
      refine ⟨v * u, ?_, by simpa only [one_mul] using hv_join.mul hu_join⟩
      calc ((v * u : unitary A) : A) * γ 0 * star ((v * u : unitary A) : A)
          = (v : A) * ((u : A) * γ 0 * star (u : A)) * star (v : A) := by
            simp only [Submonoid.coe_mul, star_mul]; noncomm_ring
        _ = γ t₂ := by rw [hu_conj, hv_conj]
  obtain ⟨u, hu_conj, hu_join⟩ := hstep N le_rfl
  exact ⟨u, by
    simpa only [γ.source, γ.target,
      show grid ⟨N, Nat.lt_succ_self N⟩ = 1 from Subtype.ext (by simp [grid])] using hu_conj,
    hu_join⟩

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
