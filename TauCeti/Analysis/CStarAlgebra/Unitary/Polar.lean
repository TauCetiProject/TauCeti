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

In C⋆-algebra perturbation arguments for projections and matrix units, an invertible intertwiner `a`
with `y * a = a * x` and `star a * y = x * star a` normalizes to `a.polarUnitary` conjugating `x`
to `y`. This file establishes real CFC formulas, closed unital `⋆`-subalgebra preservation,
functoriality along unital `⋆`-ring homomorphisms (including `Unitization.fst`), intertwining
transfer, `‖(a.polarUnitary : A) - 1‖ ≤ ‖(a : A) - 1‖ ^ 2 + 3 * ‖(a : A) - 1‖`, and
`Joined 1 a.polarUnitary`.

## Main results

* `Units.coe_polarUnitary_eq_mul_cfc_inv_sqrt`, `Units.polarUnitary_mem`, `Units.map_polarUnitary`,
  `Units.fst_polarUnitary`, `Units.conjugate_polarUnitary`,
  `Units.norm_polarUnitary_sub_one_le_sq_add`, `Units.joined_one_polarUnitary`.

## References

* B. Blackadar, *Operator Algebras*, Springer (2006), Sections II.3.2–II.3.3, Proposition II.8.3.23.
* K. R. Davidson, *C⋆-Algebras by Example*, Amer. Math. Soc. (1996), Section I.5, Lemma III.3.2.
-/

public section

open Ring
open scoped ContinuousFunctionalCalculus NNReal

namespace Units
section
variable {A : Type*} [PartialOrder A] [Ring A] [StarRing A] [StarOrderedRing A]
  [TopologicalSpace A] [Algebra ℝ A] [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
  [NonnegSpectrumClass ℝ A] [T2Space A]

private lemma sqrt_eq_cfc_real_sqrt [IsSemitopologicalRing A] {x : A} (hx : 0 ≤ x) :
    CFC.sqrt x = cfc Real.sqrt x := by
  rw [CFC.sqrt_eq_cfc, cfc_nnreal_eq_real NNReal.sqrt x hx]
  exact cfc_congr fun t ht ↦ by
    rw [Real.coe_sqrt, Real.coe_toNNReal t (spectrum_nonneg_of_nonneg hx ht)]

/-- Right CFC formula `(a.polarUnitary : A) = a * cfc (fun x : ℝ ↦ (√x)⁻¹) (star a * a)`. -/
theorem coe_polarUnitary_eq_mul_cfc_inv_sqrt [IsSemitopologicalRing A] (a : Aˣ) :
    (a.polarUnitary : A) = (a : A) * cfc (fun x : ℝ ↦ (√x)⁻¹) (star (a : A) * a) := by
  have hx := isStrictlyPositive_star_mul a
  rw [show cfc (fun t : ℝ ↦ (√t)⁻¹) (star (a : A) * a) = (CFC.sqrt (star (a : A) * a))⁻¹ʳ by
    rw [sqrt_eq_cfc_real_sqrt hx.nonneg, cfc_inv (f := Real.sqrt) (a := star (a : A) * a)
      (fun _ ht ↦ (Real.sqrt_pos.mpr
        ((StarOrderedRing.isStrictlyPositive_iff_spectrum_pos _).mp hx _ ht)).ne')
      Real.continuous_sqrt.continuousOn hx.nonneg.isSelfAdjoint]]
  conv_lhs => rw [← mul_one (a.polarUnitary : A),
    ← mul_inverse_cancel _ (isStrictlyPositive_sqrt_star_mul a).isUnit]
  rw [← mul_assoc, a.polarUnitary_mul_sqrt_star_mul]

/-- Any unital `⋆`-ring homomorphism commutes with `Units.polarUnitary`. -/
theorem map_polarUnitary [IsSemitopologicalRing A] {B F : Type*} [PartialOrder B] [Ring B]
    [StarRing B] [StarOrderedRing B] [TopologicalSpace B] [Algebra ℝ B]
    [ContinuousFunctionalCalculus ℝ B IsSelfAdjoint] [NonnegSpectrumClass ℝ B]
    [IsSemitopologicalRing B] [T2Space B] [FunLike F A B] [RingHomClass F A B] [StarHomClass F A B]
    (a : Aˣ) (φ : F) : ((Units.map (φ : A →* B) a).polarUnitary : B) = φ (a.polarUnitary : A) := by
  set q : A := CFC.sqrt (star (a : A) * a)
  have hφq : 0 ≤ φ q := by
    rw [show q = star (CFC.sqrt q) * CFC.sqrt q by
      rw [(CFC.sqrt_nonneg q).isSelfAdjoint.star_eq, CFC.sqrt_mul_sqrt_self q (CFC.sqrt_nonneg _)],
      map_mul, map_star]; exact star_mul_self_nonneg _
  let v : unitary B := ⟨φ (a.polarUnitary : A), Unitary.mem_iff.mpr
    ⟨by rw [← map_star, ← map_mul, Unitary.star_mul_self_of_mem a.polarUnitary.2, map_one],
     by rw [← map_star, ← map_mul, Unitary.mul_star_self_of_mem a.polarUnitary.2, map_one]⟩⟩
  exact congrArg Subtype.val ((Units.map (φ : A →* B) a).polarUnitary_eq_of_mul_eq' (v := v) hφq <|
    by simp only [v, q, Units.coe_map, MonoidHom.coe_ofClass, ← map_mul,
      a.polarUnitary_mul_sqrt_star_mul])

/-- `a.polarUnitary` belongs to any closed unital `⋆`-subalgebra containing `(a : A)`. -/
theorem polarUnitary_mem [IsTopologicalRing A] [ContinuousStar A] [StarModule ℝ A] {𝕜' S : Type*}
    [Monoid 𝕜'] [MulAction 𝕜' A] [SetLike S A] [SubringClass S A] [SMul ℝ 𝕜']
    [IsScalarTower ℝ 𝕜' A] [SMulMemClass S 𝕜' A] [StarMemClass S A] {s : S} [IsClosed (s : Set A)]
    (a : Aˣ) (ha : (a : A) ∈ s) : (a.polarUnitary : A) ∈ s := by
  rw [a.coe_polarUnitary_eq_mul_cfc_inv_sqrt]
  exact mul_mem ha (cfc_mem (𝕜 := ℝ) (𝕜' := 𝕜') _ (mul_mem (star_mem ha) ha))

/-- Adjoint-compatible intertwining relations `y * a = a * x` and `star a * y = x * star a` pass to
`a.polarUnitary`. -/
theorem mul_polarUnitary_eq_polarUnitary_mul [IsTopologicalRing A] (a : Aˣ) {x y : A}
    (h1 : y * (a : A) = (a : A) * x) (h2 : star (a : A) * y = x * star (a : A)) :
    y * (a.polarUnitary : A) = (a.polarUnitary : A) * x := by
  have hcomm : Commute (star (a : A) * a) x := by
    rw [Commute, SemiconjBy, mul_assoc, ← h1, ← mul_assoc, h2, mul_assoc]
  rw [a.coe_polarUnitary_eq_mul_cfc_inv_sqrt, ← mul_assoc, h1, mul_assoc,
    (hcomm.cfc_real (fun t : ℝ ↦ (√t)⁻¹)).symm.eq, ← mul_assoc]

/-- Adjoint-compatible intertwining relations `y * a = a * x` and `star a * y = x * star a` yield
exact unitary conjugation `(a.polarUnitary : A) * x * star (a.polarUnitary : A) = y`. -/
theorem conjugate_polarUnitary [IsTopologicalRing A] (a : Aˣ) {x y : A}
    (h1 : y * (a : A) = (a : A) * x) (h2 : star (a : A) * y = x * star (a : A)) :
    (a.polarUnitary : A) * x * star (a.polarUnitary : A) = y := by
  rw [← a.mul_polarUnitary_eq_polarUnitary_mul h1 h2, mul_assoc,
    Unitary.mul_star_self_of_mem a.polarUnitary.2, mul_one]
end

section
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- For every unit `a` in a unital C⋆-algebra,
`‖(a.polarUnitary : A) - 1‖ ≤ ‖(a : A) - 1‖ ^ 2 + 3 * ‖(a : A) - 1‖`. -/
theorem norm_polarUnitary_sub_one_le_sq_add (a : Aˣ) :
    ‖(a.polarUnitary : A) - 1‖ ≤ ‖(a : A) - 1‖ ^ 2 + 3 * ‖(a : A) - 1‖ := by
  set h : A := star (a : A) * a; have hh0 : 0 ≤ h := star_mul_self_nonneg (a : A)
  have hh_sub : ‖h - 1‖ ≤ ‖(a : A) - 1‖ ^ 2 + 2 * ‖(a : A) - 1‖ := by
    rw [show h - 1 = star ((a : A) - 1) * ((a : A) - 1) + star ((a : A) - 1) + ((a : A) - 1) by
      dsimp [h]; simp only [star_sub, star_one, sub_mul, mul_sub, one_mul, mul_one]; abel]
    exact norm_add₃_le.trans (by rw [CStarRing.norm_star_mul_self, norm_star, sq]; linarith)
  have hs_sub : ‖CFC.sqrt h - 1‖ ≤ ‖h - 1‖ := by
    rw [show CFC.sqrt h - 1 = cfc (fun t : ℝ ↦ √t - 1) h by
      rw [cfc_sub Real.sqrt (fun _ ↦ 1) h, sqrt_eq_cfc_real_sqrt hh0,
        cfc_const_one ℝ h hh0.isSelfAdjoint]]
    refine norm_cfc_le (norm_nonneg _) fun x hx ↦ ?_
    have habs : |x - 1| ≤ ‖h - 1‖ := by
      simpa [Real.norm_eq_abs, cfc_sub (fun t : ℝ ↦ t) (fun _ : ℝ ↦ (1 : ℝ)) h,
        cfc_id' ℝ h hh0.isSelfAdjoint, cfc_const_one ℝ h hh0.isSelfAdjoint] using
        norm_apply_le_norm_cfc (fun t : ℝ ↦ t - 1) h hx (by fun_prop) hh0.isSelfAdjoint
    have hprod : |x - 1| = |√x - 1| * (√x + 1) := by
      rw [show x - 1 = (√x - 1) * (√x + 1) by
          nlinarith [Real.mul_self_sqrt (spectrum_nonneg_of_nonneg hh0 hx)],
        abs_mul, abs_of_pos (show 0 < √x + 1 by positivity)]
    rw [Real.norm_eq_abs]; nlinarith [abs_nonneg (√x - 1), Real.sqrt_nonneg x]
  refine (show ‖(a.polarUnitary : A) - 1‖ ≤ ‖(a : A) - 1‖ + ‖CFC.sqrt h - 1‖ by
    rw [show (a.polarUnitary : A) - 1 = ((a : A) - 1) - (a.polarUnitary : A) * (CFC.sqrt h - 1) by
        rw [mul_sub, mul_one, a.polarUnitary_mul_sqrt_star_mul]; abel,
      ← CStarRing.norm_coe_unitary_mul a.polarUnitary (CFC.sqrt h - 1)]
    exact norm_sub_le _ _).trans (by linarith)

/-- Distance bound `‖(a.polarUnitary : A) - 1‖ ≤ 4 * ‖(a : A) - 1‖` for `‖(a : A) - 1‖ ≤ 1`. -/
theorem norm_polarUnitary_sub_one_le {a : Aˣ} (ha : ‖(a : A) - 1‖ ≤ 1) :
    ‖(a.polarUnitary : A) - 1‖ ≤ 4 * ‖(a : A) - 1‖ := by
  nlinarith [a.norm_polarUnitary_sub_one_le_sq_add, norm_nonneg ((a : A) - 1)]

/-- When `‖(a : A) - 1‖ ≤ 1 / 2`, `a.polarUnitary` lies in the path component of `1`. -/
theorem joined_one_polarUnitary {a : Aˣ} (ha : ‖(a : A) - 1‖ ≤ 1 / 2) : Joined 1 a.polarUnitary :=
  Unitary.joined 1 a.polarUnitary <|
    a.norm_polarUnitary_sub_one_le_sq_add.trans_lt (by nlinarith [norm_nonneg ((a : A) - 1)])
end

/-- If a unit `a : (Unitization ℂ A)ˣ` has scalar part `1`, then so does `a.polarUnitary`. -/
theorem fst_polarUnitary {A : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder (Unitization ℂ A)] [StarOrderedRing (Unitization ℂ A)]
    {a : (Unitization ℂ A)ˣ} (ha : (a : Unitization ℂ A).fst = 1) :
    (a.polarUnitary : Unitization ℂ A).fst = 1 := by
  let _ := CStarAlgebra.spectralOrder ℂ; let _ := CStarAlgebra.spectralOrderedRing ℂ
  have hmap : Units.map (Unitization.fstHom ℂ A : Unitization ℂ A →* ℂ) a = 1 :=
    Units.ext <| by simp [ha]
  simpa [hmap, polarUnitary_one] using (a.map_polarUnitary (Unitization.fstHom ℂ A)).symm
end Units
