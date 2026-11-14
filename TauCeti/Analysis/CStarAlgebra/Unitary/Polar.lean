/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
public import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
public import Mathlib.Analysis.CStarAlgebra.Unitization
public import TauCeti.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Polar

/-!
# Perturbation, subalgebra preservation, and intertwining for polar unitaries

In perturbation arguments for projections and matrix units in C⋆-algebras, one constructs an
algebraic intertwiner `a` satisfying `y * a = a * x` and `a⋆ * y = x * a⋆` that is close to `1`
(or has invertible `a⋆ * a`), and then passes to the unitary factor `a.polarUnitary` of its polar
decomposition to obtain a genuine unitary conjugating `x` to `y`.

This file supplies the analytic and functorial properties of `Units.polarUnitary` needed for such
arguments:
* the right-sided functional-calculus formula
  `(a.polarUnitary : A) = a * cfc (fun x : ℝ ↦ (√x)⁻¹) (star a * a)`, from which membership in any
  closed unital `⋆`-subalgebra containing `a` and transfer of adjoint-compatible intertwining
  relations follow;
* functoriality `((Units.map φ a).polarUnitary : B) = φ (a.polarUnitary : A)` along any unital
  `⋆`-ring homomorphism `φ`, deduced algebraically from uniqueness of the polar decomposition and
  yielding `(a.polarUnitary : Unitization ℂ A).fst = 1` whenever `(a : Unitization ℂ A).fst = 1`;
* the quantitative C⋆-algebra perturbation bound
  `‖(a.polarUnitary : A) - 1‖ ≤ ‖(a : A) - 1‖ ^ 2 + 3 * ‖(a : A) - 1‖` (hence `≤ 4 * ‖(a : A) - 1‖`
  for `‖(a : A) - 1‖ ≤ 1`), together with path-connectedness `Joined 1 a.polarUnitary` when
  `‖(a : A) - 1‖ ≤ 1 / 2`.

## Main results

* `Units.coe_polarUnitary_eq_mul_cfc_inv_sqrt`, `Units.polarUnitary_mem`, `Units.map_polarUnitary`.
* `Units.mul_polarUnitary_eq_polarUnitary_mul`, `Units.conjugate_polarUnitary`.
* `Units.norm_polarUnitary_sub_one_le_sq_add`, `Units.norm_polarUnitary_sub_one_le`,
  `Units.joined_one_polarUnitary`.
* `Units.fst_polarUnitary`.

## References

* B. Blackadar, *Operator Algebras*, Springer (2006), Sections II.3.2–II.3.3 and Proposition
  II.8.3.23.
* K. R. Davidson, *C⋆-Algebras by Example*, Fields Institute Monographs 6, Amer. Math. Soc. (1996),
  Section I.5 and Lemma III.3.2.
-/

public section

open Ring
open scoped ContinuousFunctionalCalculus NNReal

namespace Units

section SemitopologicalRing

variable {A B : Type*}
  [PartialOrder A] [Ring A] [StarRing A] [StarOrderedRing A]
  [TopologicalSpace A] [Algebra ℝ A] [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
  [NonnegSpectrumClass ℝ A] [IsSemitopologicalRing A] [T2Space A]
  [PartialOrder B] [Ring B] [StarRing B] [StarOrderedRing B]
  [TopologicalSpace B] [Algebra ℝ B] [ContinuousFunctionalCalculus ℝ B IsSelfAdjoint]
  [NonnegSpectrumClass ℝ B] [IsSemitopologicalRing B] [T2Space B]

private lemma sqrt_eq_cfc_real_sqrt {x : A} (hx : 0 ≤ x) :
    CFC.sqrt x = cfc Real.sqrt x := by
  rw [CFC.sqrt_eq_cfc, cfc_nnreal_eq_real NNReal.sqrt x hx]
  refine cfc_congr fun t ht ↦ ?_
  rw [Real.coe_sqrt, Real.coe_toNNReal t (spectrum_nonneg_of_nonneg hx ht)]

private lemma cfc_inv_sqrt_eq_ringInverse_sqrt {x : A} (hx : IsStrictlyPositive x) :
    cfc (fun t : ℝ ↦ (√t)⁻¹) x = (CFC.sqrt x)⁻¹ʳ := by
  have hx_nonneg : 0 ≤ x := hx.nonneg
  have hx_pos : ∀ t ∈ spectrum ℝ x, 0 < t :=
    (StarOrderedRing.isStrictlyPositive_iff_spectrum_pos x).mp hx
  rw [sqrt_eq_cfc_real_sqrt hx_nonneg,
    cfc_inv (f := Real.sqrt) (a := x) (fun t ht ↦ (Real.sqrt_pos.mpr (hx_pos t ht)).ne')
      Real.continuous_sqrt.continuousOn hx_nonneg.isSelfAdjoint]

/-- Left functional-calculus formula for `Units.polarUnitary`:
`(a.polarUnitary : A) = cfc (fun x : ℝ ↦ (√x)⁻¹) (a * star a) * a`. -/
theorem coe_polarUnitary_eq_cfc_inv_sqrt_mul (a : Aˣ) :
    (a.polarUnitary : A) = cfc (fun x : ℝ ↦ (√x)⁻¹) ((a : A) * star (a : A)) * a := by
  rw [a.coe_polarUnitary, cfc_inv_sqrt_eq_ringInverse_sqrt (isStrictlyPositive_mul_star a)]

/-- Right functional-calculus formula for `Units.polarUnitary`:
`(a.polarUnitary : A) = a * cfc (fun x : ℝ ↦ (√x)⁻¹) (star a * a)`. -/
theorem coe_polarUnitary_eq_mul_cfc_inv_sqrt (a : Aˣ) :
    (a.polarUnitary : A) = (a : A) * cfc (fun x : ℝ ↦ (√x)⁻¹) (star (a : A) * a) := by
  rw [cfc_inv_sqrt_eq_ringInverse_sqrt (isStrictlyPositive_star_mul a)]
  conv_lhs => rw [← mul_one (a.polarUnitary : A),
    ← mul_inverse_cancel _ (isStrictlyPositive_sqrt_star_mul a).isUnit]
  rw [← mul_assoc, a.polarUnitary_mul_sqrt_star_mul]

/-- Any unital `⋆`-ring homomorphism commutes with `Units.polarUnitary`. -/
theorem map_polarUnitary {F : Type*} [FunLike F A B] [RingHomClass F A B] [StarHomClass F A B]
    (a : Aˣ) (φ : F) :
    ((Units.map (φ : A →* B) a).polarUnitary : B) = φ (a.polarUnitary : A) := by
  set q : A := CFC.sqrt (star (a : A) * a)
  set r : A := CFC.sqrt q
  have hq_nonneg : 0 ≤ q := CFC.sqrt_nonneg _
  have hr_sa : IsSelfAdjoint r := (CFC.sqrt_nonneg q).isSelfAdjoint
  have hq_eq : q = star r * r := by
    rw [hr_sa.star_eq, CFC.sqrt_mul_sqrt_self q hq_nonneg]
  have hφq_nonneg : 0 ≤ φ q := by
    rw [hq_eq, map_mul, map_star]
    exact star_mul_self_nonneg (φ r)
  let v : unitary B := ⟨φ (a.polarUnitary : A), Unitary.mem_iff.mpr
    ⟨by rw [← map_star, ← map_mul, Unitary.star_mul_self_of_mem a.polarUnitary.2, map_one],
     by rw [← map_star, ← map_mul, Unitary.mul_star_self_of_mem a.polarUnitary.2, map_one]⟩⟩
  have hmul : (v : B) * φ q = (Units.map (φ : A →* B) a : B) := by
    dsimp only [v]
    rw [← map_mul, a.polarUnitary_mul_sqrt_star_mul]
    rfl
  exact congrArg Subtype.val ((Units.map (φ : A →* B) a).polarUnitary_eq_of_mul_eq' hφq_nonneg hmul)

end SemitopologicalRing

section TopologicalRing

variable {A : Type*}
  [PartialOrder A] [Ring A] [StarRing A] [StarOrderedRing A]
  [TopologicalSpace A] [Algebra ℝ A] [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
  [NonnegSpectrumClass ℝ A] [IsTopologicalRing A] [T2Space A]

/-- The polar unitary `a.polarUnitary` belongs to any closed unital `⋆`-subalgebra containing
`(a : A)`. -/
theorem polarUnitary_mem [ContinuousStar A] [StarModule ℝ A] {𝕜' S : Type*} [Monoid 𝕜']
    [MulAction 𝕜' A] [SetLike S A] [SubringClass S A] [SMul ℝ 𝕜'] [IsScalarTower ℝ 𝕜' A]
    [SMulMemClass S 𝕜' A] [StarMemClass S A] {s : S} [IsClosed (s : Set A)] (a : Aˣ)
    (ha : (a : A) ∈ s) : (a.polarUnitary : A) ∈ s := by
  rw [a.coe_polarUnitary_eq_mul_cfc_inv_sqrt]
  exact mul_mem ha (cfc_mem (𝕜 := ℝ) (𝕜' := 𝕜') _ (mul_mem (star_mem ha) ha))

/-- Adjoint-compatible intertwining relations `y * a = a * x` and `star a * y = x * star a` pass to
`a.polarUnitary`. -/
theorem mul_polarUnitary_eq_polarUnitary_mul (a : Aˣ) {x y : A}
    (h1 : y * (a : A) = (a : A) * x) (h2 : star (a : A) * y = x * star (a : A)) :
    y * (a.polarUnitary : A) = (a.polarUnitary : A) * x := by
  have hcomm : Commute (star (a : A) * a) x := by
    rw [Commute, SemiconjBy, mul_assoc, ← h1, ← mul_assoc, h2, mul_assoc]
  rw [a.coe_polarUnitary_eq_mul_cfc_inv_sqrt, ← mul_assoc, h1, mul_assoc,
    (hcomm.cfc_real (fun t : ℝ ↦ (√t)⁻¹)).symm.eq, ← mul_assoc]

/-- Adjoint-compatible intertwining relations `y * a = a * x` and `star a * y = x * star a` yield
exact unitary conjugation `(a.polarUnitary : A) * x * star (a.polarUnitary : A) = y`. -/
theorem conjugate_polarUnitary (a : Aˣ) {x y : A}
    (h1 : y * (a : A) = (a : A) * x) (h2 : star (a : A) * y = x * star (a : A)) :
    (a.polarUnitary : A) * x * star (a.polarUnitary : A) = y := by
  rw [← a.mul_polarUnitary_eq_polarUnitary_mul h1 h2, mul_assoc,
    Unitary.mul_star_self_of_mem a.polarUnitary.2, mul_one]

end TopologicalRing

section CStarAlgebra

variable {A : Type*} [CStarAlgebra A]

private lemma norm_star_mul_self_sub_one_le (z : A) :
    ‖star z * z - 1‖ ≤ ‖z - 1‖ ^ 2 + 2 * ‖z - 1‖ := by
  rw [show star z * z - 1 = star (z - 1) * (z - 1) + (star (z - 1) + (z - 1)) by
    simp only [star_sub, star_one, sub_mul, mul_sub, one_mul, mul_one]; abel]
  have h1 : ‖star (z - 1) * (z - 1)‖ = ‖z - 1‖ ^ 2 := by rw [CStarRing.norm_star_mul_self, sq]
  have h2 := norm_add_le (star (z - 1)) (z - 1)
  rw [norm_star] at h2
  linarith [norm_add_le (star (z - 1) * (z - 1)) (star (z - 1) + (z - 1))]

private lemma spectrum_sub_one_abs_le {h : A} (hh : IsSelfAdjoint h) {x : ℝ}
    (hx : x ∈ spectrum ℝ h) : |x - 1| ≤ ‖h - 1‖ := by
  have hcfc : cfc (fun t : ℝ ↦ t - 1) h = h - 1 := by
    rw [cfc_sub (fun t : ℝ ↦ t) _ h continuousOn_id continuousOn_const,
      cfc_id' ℝ h hh, cfc_const_one ℝ h hh]
  simpa [Real.norm_eq_abs, hcfc] using
    norm_apply_le_norm_cfc (fun t : ℝ ↦ t - 1) h hx (continuousOn_id.sub continuousOn_const) hh

variable [PartialOrder A] [StarOrderedRing A]

/-- For every unit `a` in a unital C⋆-algebra,
`‖(a.polarUnitary : A) - 1‖ ≤ ‖(a : A) - 1‖ ^ 2 + 3 * ‖(a : A) - 1‖`. -/
theorem norm_polarUnitary_sub_one_le_sq_add (a : Aˣ) :
    ‖(a.polarUnitary : A) - 1‖ ≤ ‖(a : A) - 1‖ ^ 2 + 3 * ‖(a : A) - 1‖ := by
  set h : A := star (a : A) * a
  have hh_nonneg : 0 ≤ h := star_mul_self_nonneg (a : A)
  have hs_sub_le : ‖CFC.sqrt h - 1‖ ≤ ‖h - 1‖ := by
    rw [show CFC.sqrt h - 1 = cfc (fun x : ℝ ↦ √x - 1) h by
      rw [sqrt_eq_cfc_real_sqrt hh_nonneg,
        cfc_sub Real.sqrt _ h Real.continuous_sqrt.continuousOn continuousOn_const,
        cfc_const_one ℝ h hh_nonneg.isSelfAdjoint]]
    refine norm_cfc_le (norm_nonneg _) fun x hx ↦ ?_
    rw [Real.norm_eq_abs]
    have hx_nonneg : 0 ≤ x := spectrum_nonneg_of_nonneg hh_nonneg hx
    have hsqrt_nonneg : 0 ≤ √x := Real.sqrt_nonneg x
    have habs := spectrum_sub_one_abs_le hh_nonneg.isSelfAdjoint hx
    have hprod : |x - 1| = |√x - 1| * (√x + 1) := by
      rw [show x - 1 = (√x - 1) * (√x + 1) by
        rw [show (√x - 1) * (√x + 1) = √x * √x - 1 by ring, Real.mul_self_sqrt hx_nonneg],
        abs_mul, abs_of_pos (a := √x + 1) (by linarith)]
    nlinarith [abs_nonneg (√x - 1)]
  have htri : ‖(a.polarUnitary : A) - 1‖ ≤ ‖(a : A) - 1‖ + ‖CFC.sqrt h - 1‖ := by
    rw [show (a.polarUnitary : A) - 1 =
        ((a : A) - 1) - (a.polarUnitary : A) * (CFC.sqrt h - 1) by
      rw [mul_sub, mul_one, a.polarUnitary_mul_sqrt_star_mul]; abel,
      ← CStarRing.norm_coe_unitary_mul a.polarUnitary (CFC.sqrt h - 1)]
    exact norm_sub_le _ _
  linarith [norm_star_mul_self_sub_one_le (a : A)]

/-- Linear distance bound `‖(a.polarUnitary : A) - 1‖ ≤ 4 * ‖(a : A) - 1‖` when
`‖(a : A) - 1‖ ≤ 1`. -/
theorem norm_polarUnitary_sub_one_le {a : Aˣ} (ha : ‖(a : A) - 1‖ ≤ 1) :
    ‖(a.polarUnitary : A) - 1‖ ≤ 4 * ‖(a : A) - 1‖ := by
  nlinarith [a.norm_polarUnitary_sub_one_le_sq_add, norm_nonneg ((a : A) - 1)]

/-- When `‖(a : A) - 1‖ ≤ 1 / 2`, `a.polarUnitary` lies in the path component of `1` in
`unitary A`. -/
theorem joined_one_polarUnitary {a : Aˣ} (ha : ‖(a : A) - 1‖ ≤ 1 / 2) :
    Joined 1 a.polarUnitary :=
  Unitary.joined 1 a.polarUnitary <|
    (a.norm_polarUnitary_sub_one_le_sq_add).trans_lt (by nlinarith [norm_nonneg ((a : A) - 1)])

end CStarAlgebra

section Unitization

/-- If a unit `a : (Unitization ℂ A)ˣ` has scalar part `1`, then so does `a.polarUnitary`. -/
theorem fst_polarUnitary {A : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder (Unitization ℂ A)] [StarOrderedRing (Unitization ℂ A)]
    {a : (Unitization ℂ A)ˣ} (ha : (a : Unitization ℂ A).fst = 1) :
    (a.polarUnitary : Unitization ℂ A).fst = 1 := by
  let _ := CStarAlgebra.spectralOrder ℂ
  let _ := CStarAlgebra.spectralOrderedRing ℂ
  let φ : Unitization ℂ A →⋆ₐ[ℂ] ℂ := Unitization.starLift 0
  have hφ (x : Unitization ℂ A) : φ x = x.fst := by
    conv_lhs => rw [← Unitization.inl_fst_add_inr_snd_eq x]
    rw [map_add, ← Unitization.algebraMap_eq_inl, AlgHomClass.commutes,
      ← Unitization.starLift_symm_apply_apply, Equiv.symm_apply_apply]
    simp
  have hmap : Units.map (φ : Unitization ℂ A →* ℂ) a = 1 := by
    ext
    simp [hφ, ha]
  have h := a.map_polarUnitary φ
  rw [hmap, polarUnitary_one, hφ] at h
  exact h.symm

end Unitization

end Units
