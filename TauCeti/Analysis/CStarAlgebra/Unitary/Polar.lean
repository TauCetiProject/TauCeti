/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
public import Mathlib.Analysis.CStarAlgebra.Unitization
public import TauCeti.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Polar

/-!
# Norm perturbation and unitization properties of polar unitaries in C⋆-algebras

For perturbation of projections and matrix units, an invertible intertwiner `a` normalizes to
`a.polarUnitary` (general real-CFC API in
`TauCeti/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Polar.lean`). Here we prove
`‖(a.polarUnitary : A) - 1‖ ≤ ‖(a : A) - 1‖ ^ 2 + 3 * ‖(a : A) - 1‖`, `Joined 1 a.polarUnitary`
when `‖(a : A) - 1‖ ≤ 1 / 2`, and scalar-part preservation `Units.fst_polarUnitary_eq_one`.

## Main results

* `Units.norm_polarUnitary_sub_one_le_sq_add`, `Units.norm_polarUnitary_sub_one_le`,
  `Units.joined_one_polarUnitary`, `Units.fst_polarUnitary_eq_one`.

## References

* B. Blackadar, *Operator Algebras*, Springer (2006), §§II.3.2–II.3.3, Prop. II.8.3.23.
* K. R. Davidson, *C⋆-Algebras by Example*, Amer. Math. Soc. (1996), §I.5, Lemma III.3.2.
-/

public section
open scoped ContinuousFunctionalCalculus NNReal
namespace Units
section
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
/-- `‖(a.polarUnitary : A) - 1‖ ≤ ‖(a : A) - 1‖ ^ 2 + 3 * ‖(a : A) - 1‖` in a C⋆-algebra. -/
theorem norm_polarUnitary_sub_one_le_sq_add (a : Aˣ) :
    ‖(a.polarUnitary : A) - 1‖ ≤ ‖(a : A) - 1‖ ^ 2 + 3 * ‖(a : A) - 1‖ := by
  set h : A := star (a : A) * a; have hh0 : 0 ≤ h := star_mul_self_nonneg (a : A)
  have hh_sub : ‖h - 1‖ ≤ ‖(a : A) - 1‖ ^ 2 + 2 * ‖(a : A) - 1‖ := by
    rw [show h - 1 = star ((a : A) - 1) * ((a : A) - 1) + star ((a : A) - 1) + ((a : A) - 1) by
      dsimp [h]; simp only [star_sub, star_one, sub_mul, mul_sub, one_mul, mul_one]; abel]
    exact norm_add₃_le.trans (by rw [CStarRing.norm_star_mul_self, norm_star, sq]; linarith)
  have hs_sub : ‖CFC.sqrt h - 1‖ ≤ ‖h - 1‖ := by
    rw [show CFC.sqrt h - 1 = cfc (fun t : ℝ ↦ √t - 1) h by
      rw [cfc_sub Real.sqrt (fun _ ↦ 1) h, CFC.sqrt_eq_real_sqrt _ hh0, cfcₙ_eq_cfc,
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
      ← CStarRing.norm_coe_unitary_mul a.polarUnitary (CFC.sqrt h - 1)]; exact norm_sub_le _ _
    ).trans (by linarith)
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
theorem fst_polarUnitary_eq_one {A : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder (Unitization ℂ A)] [StarOrderedRing (Unitization ℂ A)]
    {a : (Unitization ℂ A)ˣ} (ha : (a : Unitization ℂ A).fst = 1) :
    (a.polarUnitary : Unitization ℂ A).fst = 1 := by
  let _ := CStarAlgebra.spectralOrder ℂ; let _ := CStarAlgebra.spectralOrderedRing ℂ
  have hmap : Units.map (Unitization.fstHom ℂ A : Unitization ℂ A →* ℂ) a = 1 := by ext; simp [ha]
  simpa [hmap, polarUnitary_one] using a.map_polarUnitary (Unitization.fstHom ℂ A)
end Units
