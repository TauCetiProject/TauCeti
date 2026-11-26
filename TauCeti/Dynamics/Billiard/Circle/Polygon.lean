/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Billiard.Circle.Basic
public import TauCeti.Dynamics.Billiard.SpherePolygon
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Arccos
import TauCeti.Data.ZMod.Periodic

/-!
# Inscribed perimeter maximizers and reflection-law checks on a circle

This file studies explicit inscribed `N`-gons on the arclength-parametrized circle
`Orientation.circleCurve` for `N = 2, 3, 4`, characterizing global maximizers of
`TauCeti.inscribedPerimeter` and testing the equal-angle billiard reflection law on regular and
non-regular examples.

## Main definitions

* `TauCeti.circleDiameter`: the diameter `2`-gon on a circle of radius `R`.
* `TauCeti.circleDoubledDiameter`: the doubled-diameter `4`-gon traversing a diameter twice.
* `TauCeti.circleInscribedSquare`: the regular inscribed square with quarter-circle step
  `π R / 2`.
* `TauCeti.circleEquilateralTriangle`: the positively oriented regular inscribed equilateral
  triangle with step `2 π R / 3`.
* `TauCeti.circleRightTriangle`: the inscribed triangle at central angles `0`, `π / 2`, `π`.

## Main results

* `Orientation.isMaxOn_inscribedPerimeter_circleCurve_zmod_two_iff`: the `N = 2` perimeter
  maximizers on the circle are the diameters, of perimeter `4 R`.
* `Orientation.isMaxOn_inscribedPerimeter_circleCurve_zmod_four_iff`,
  `Orientation.circleCurve_add_two_of_isMaxOn_zmod_four`,
  `Orientation.not_isMaxOn_circleInscribedSquare`: for `N = 4` the perimeter maximizers on the
  circle are doubled diameters of perimeter `8 R` and period `2`, whereas the inscribed square has
  strictly smaller perimeter `4 √2 R` despite corresponding to a period-`4` circular billiard orbit.
* `Orientation.isMaxOn_inscribedPerimeter_circleCurve_zmod_three_iff`,
  `Orientation.inner_incoming_circleEquilateralTriangle`,
  `Orientation.inner_outgoing_circleEquilateralTriangle`: for `N = 3` the perimeter maximizers are
  the equilateral triangles of perimeter `3 √3 R`, where both sides of the equal-angle reflection
  law equal `1 / 2` at every vertex.
* `Orientation.inner_incoming_circleRightTriangle_zero`,
  `Orientation.inner_outgoing_circleRightTriangle_zero`,
  `Orientation.incoming_ne_outgoing_circleRightTriangle_zero`,
  `Orientation.not_isLocalExtr_circleRightTriangle`: the inscribed triangle at angles
  `0, π / 2, π` has incoming and outgoing unit-chord inner products `0` and `1 / √2` at angle `0`,
  fails the reflection law there, and is not a local extremum of `inscribedPerimeter`.

## References

* Ana Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 5.2.
* Serge Tabachnikov, *Geometry and Billiards*, Student Mathematical Library 30, American
  Mathematical Society, 2005, Chapter 6.
-/

public section

noncomputable section

open Set Module
open scoped RealInnerProductSpace

/-! ### Explicit inscribed polygons on a circle -/

namespace TauCeti

/-- The diameter `2`-gon on a circle of radius `R` starting at arclength parameter `s₀`. -/
def circleDiameter (R s₀ : ℝ) : ZMod 2 → ℝ := ![s₀, s₀ + Real.pi * R]

theorem circleDiameter_def (R s₀ : ℝ) :
    circleDiameter R s₀ = ![s₀, s₀ + Real.pi * R] :=
  (rfl)

/-- The doubled-diameter `4`-gon on a circle of radius `R`, traversing the diameter from `s₀` to
`s₀ + π R` twice. -/
def circleDoubledDiameter (R s₀ : ℝ) : ZMod 4 → ℝ :=
  ![s₀, s₀ + Real.pi * R, s₀, s₀ + Real.pi * R]

theorem circleDoubledDiameter_def (R s₀ : ℝ) :
    circleDoubledDiameter R s₀ = ![s₀, s₀ + Real.pi * R, s₀, s₀ + Real.pi * R] :=
  (rfl)

/-- The regular inscribed square on a circle of radius `R` starting at arclength parameter `s₀`,
with quarter-circle step `π R / 2`. -/
def circleInscribedSquare (R s₀ : ℝ) (k : ZMod 4) : ℝ :=
  s₀ + (k.val : ℝ) * (Real.pi * R / 2)

@[simp]
theorem circleInscribedSquare_apply (R s₀ : ℝ) (k : ZMod 4) :
    circleInscribedSquare R s₀ k = s₀ + (k.val : ℝ) * (Real.pi * R / 2) :=
  (rfl)

/-- The positively oriented inscribed equilateral triangle on a circle of radius `R` starting at
arclength parameter `s₀`, with one-third-turn step `2 π R / 3`. -/
def circleEquilateralTriangle (R s₀ : ℝ) (k : ZMod 3) : ℝ :=
  s₀ + (k.val : ℝ) * (2 * Real.pi * R / 3)

@[simp]
theorem circleEquilateralTriangle_apply (R s₀ : ℝ) (k : ZMod 3) :
    circleEquilateralTriangle R s₀ k = s₀ + (k.val : ℝ) * (2 * Real.pi * R / 3) :=
  (rfl)

/-- The right-angled inscribed triangle on a circle of radius `R` with vertices at central angles
`0`, `π / 2`, and `π` (arclength parameters `0`, `π R / 2`, `π R`). -/
def circleRightTriangle (R : ℝ) : ZMod 3 → ℝ :=
  ![0, Real.pi * R / 2, Real.pi * R]

theorem circleRightTriangle_def (R : ℝ) :
    circleRightTriangle R = ![0, Real.pi * R / 2, Real.pi * R] :=
  (rfl)

end TauCeti

/-! ### Perimeter maximizers and reflection-law checks on the circle (`N = 2, 3, 4`) -/

namespace Orientation

open TauCeti

attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fact (finrank ℝ E = 2)]

/-! #### `N = 2`: diameters -/

private theorem inscribedPerimeter_circleDiameter_eq (o : Orientation ℝ E (Fin 2)) (c e : E)
    (R s₀ : ℝ) :
    inscribedPerimeter (o.circleCurve c e R) (circleDiameter R s₀) = 4 * ‖R • e‖ := by
  refine (inscribedPerimeter_zmod_two_eq_iff_of_mem_sphere
    (fun k ↦ o.circleCurve_mem_sphere_norm_smul c e R _)).2 ?_
  simpa [circleDiameter] using o.circleCurve_add_pi_mul_sub_center c e R s₀

/-- A diameter `2`-gon on `o.circleCurve c e R` (`R ≥ 0`) has inscribed perimeter `4 R`. -/
@[simp]
theorem inscribedPerimeter_circleDiameter (o : Orientation ℝ E (Fin 2)) (c e : E) {R : ℝ}
    (he : ‖e‖ = 1) (hR : 0 ≤ R) (s₀ : ℝ) :
    inscribedPerimeter (o.circleCurve c e R) (circleDiameter R s₀) = 4 * R := by
  rw [o.inscribedPerimeter_circleDiameter_eq, norm_smul, he, mul_one, Real.norm_of_nonneg hR]

/-- A `2`-gon maximizes the inscribed perimeter on `o.circleCurve c e R` if and only if its two
vertices are antipodal across `c` (a diameter). -/
theorem isMaxOn_inscribedPerimeter_circleCurve_zmod_two_iff (o : Orientation ℝ E (Fin 2)) (c e : E)
    (R : ℝ) (s : ZMod 2 → ℝ) :
    IsMaxOn (inscribedPerimeter (o.circleCurve c e R)) univ s ↔
      o.circleCurve c e R (s 1) - c = -(o.circleCurve c e R (s 0) - c) := by
  rw [← inscribedPerimeter_zmod_two_eq_iff_of_mem_sphere
    (fun k ↦ o.circleCurve_mem_sphere_norm_smul c e R _)]
  constructor
  · intro hs
    refine le_antisymm
      (inscribedPerimeter_zmod_two_le_of_mem_sphere
        fun k ↦ o.circleCurve_mem_sphere_norm_smul c e R _) ?_
    simpa [o.inscribedPerimeter_circleDiameter_eq] using
      isMaxOn_iff.1 hs (circleDiameter R 0) (mem_univ _)
  · intro hs
    refine isMaxOn_iff.2 fun r _ ↦ ?_
    rw [hs]
    exact inscribedPerimeter_zmod_two_le_of_mem_sphere
      fun k ↦ o.circleCurve_mem_sphere_norm_smul c e R _

/-! #### `N = 4`: the doubled diameter maximizes perimeter, not the inscribed square -/

private theorem inscribedPerimeter_circleDoubledDiameter_eq (o : Orientation ℝ E (Fin 2)) (c e : E)
    (R s₀ : ℝ) :
    inscribedPerimeter (o.circleCurve c e R) (circleDoubledDiameter R s₀) = 8 * ‖R • e‖ := by
  refine (inscribedPerimeter_zmod_four_eq_iff_of_mem_sphere
    (fun k ↦ o.circleCurve_mem_sphere_norm_smul c e R _)).2 ?_
  have hant := o.circleCurve_add_pi_mul_sub_center c e R s₀
  have h0 : o.circleCurve c e R (circleDoubledDiameter R s₀ ((0 : ZMod 4) + 1)) - c =
      -(o.circleCurve c e R (circleDoubledDiameter R s₀ 0) - c) := hant
  have h1 : o.circleCurve c e R (circleDoubledDiameter R s₀ ((1 : ZMod 4) + 1)) - c =
      -(o.circleCurve c e R (circleDoubledDiameter R s₀ 1) - c) := by
    have hv2 : circleDoubledDiameter R s₀ ((1 : ZMod 4) + 1) = s₀ := rfl
    have hv1 : circleDoubledDiameter R s₀ 1 = s₀ + Real.pi * R := rfl
    rw [hv2, hv1, hant, neg_neg]
  have h2 : o.circleCurve c e R (circleDoubledDiameter R s₀ ((2 : ZMod 4) + 1)) - c =
      -(o.circleCurve c e R (circleDoubledDiameter R s₀ 2) - c) := hant
  have h3 : o.circleCurve c e R (circleDoubledDiameter R s₀ ((3 : ZMod 4) + 1)) - c =
      -(o.circleCurve c e R (circleDoubledDiameter R s₀ 3) - c) := by
    have hv0 : circleDoubledDiameter R s₀ ((3 : ZMod 4) + 1) = s₀ := rfl
    have hv3 : circleDoubledDiameter R s₀ 3 = s₀ + Real.pi * R := rfl
    rw [hv0, hv3, hant, neg_neg]
  intro k
  fin_cases k
  · exact h0
  · exact h1
  · exact h2
  · exact h3

/-- For `‖e‖ = 1` and `R ≥ 0`, the doubled diameter has inscribed perimeter `8 R`. -/
@[simp]
theorem inscribedPerimeter_circleDoubledDiameter (o : Orientation ℝ E (Fin 2)) (c e : E)
    {R : ℝ} (he : ‖e‖ = 1) (hR : 0 ≤ R) (s₀ : ℝ) :
    inscribedPerimeter (o.circleCurve c e R) (circleDoubledDiameter R s₀) = 8 * R := by
  rw [o.inscribedPerimeter_circleDoubledDiameter_eq, norm_smul, he, mul_one,
    Real.norm_of_nonneg hR]

/-- **For `N = 4`, perimeter maximizers on the circle are doubled diameters.** A `4`-gon maximizes
`inscribedPerimeter` on `o.circleCurve c e R` if and only if consecutive vertices are antipodal
across `c`. -/
theorem isMaxOn_inscribedPerimeter_circleCurve_zmod_four_iff (o : Orientation ℝ E (Fin 2))
    (c e : E) (R : ℝ) (s : ZMod 4 → ℝ) :
    IsMaxOn (inscribedPerimeter (o.circleCurve c e R)) univ s ↔
      ∀ k, o.circleCurve c e R (s (k + 1)) - c = -(o.circleCurve c e R (s k) - c) := by
  rw [← inscribedPerimeter_zmod_four_eq_iff_of_mem_sphere
    (fun k ↦ o.circleCurve_mem_sphere_norm_smul c e R _)]
  constructor
  · intro hs
    refine le_antisymm
      (inscribedPerimeter_zmod_four_le_of_mem_sphere
        fun k ↦ o.circleCurve_mem_sphere_norm_smul c e R _) ?_
    simpa [o.inscribedPerimeter_circleDoubledDiameter_eq] using
      isMaxOn_iff.1 hs (circleDoubledDiameter R 0) (mem_univ _)
  · intro hs
    refine isMaxOn_iff.2 fun r _ ↦ ?_
    rw [hs]
    exact inscribedPerimeter_zmod_four_le_of_mem_sphere
      fun k ↦ o.circleCurve_mem_sphere_norm_smul c e R _

/-- Every `N = 4` perimeter maximizer on `o.circleCurve c e R` repeats its vertices with period
`2`: `χ(s_(k+2)) = χ(s_k)`. -/
theorem circleCurve_add_two_of_isMaxOn_zmod_four (o : Orientation ℝ E (Fin 2)) (c e : E)
    (R : ℝ) {s : ZMod 4 → ℝ}
    (hs : IsMaxOn (inscribedPerimeter (o.circleCurve c e R)) univ s) (k : ZMod 4) :
    o.circleCurve c e R (s (k + 2)) = o.circleCurve c e R (s k) := by
  have h24 : (2 : ℝ) * (4 : ℕ) * ‖R • e‖ = 8 * ‖R • e‖ := by push_cast; ring
  have heq : inscribedPerimeter (o.circleCurve c e R) s = 2 * (4 : ℕ) * ‖R • e‖ := by
    rw [h24, inscribedPerimeter_zmod_four_eq_iff_of_mem_sphere
      (fun j ↦ o.circleCurve_mem_sphere_norm_smul c e R _)]
    exact (o.isMaxOn_inscribedPerimeter_circleCurve_zmod_four_iff c e R s).1 hs
  exact apply_add_two_eq_of_inscribedPerimeter_eq_two_mul
    (fun j ↦ o.circleCurve_mem_sphere_norm_smul c e R _) heq k

private theorem circleCurve_circleInscribedSquare_succ (o : Orientation ℝ E (Fin 2)) (c e : E)
    (R s₀ : ℝ) (k : ZMod 4) :
    o.circleCurve c e R (circleInscribedSquare R s₀ (k + 1)) =
      o.circleCurve c e R (circleInscribedSquare R s₀ k + Real.pi * R / 2) := by
  have hstep : 2 * Real.pi * R / (4 : ℕ) = Real.pi * R / 2 := by push_cast; ring
  simpa only [circleInscribedSquare_apply, hstep] using
    (o.periodic_circleCurve c e R).apply_add_val_add_one_mul_div s₀ k

/-- For `‖e‖ = 1` and `R ≥ 0`, each side of `circleInscribedSquare R s₀` has length `√2 R`, so the
inscribed square has perimeter `4 √2 R`. -/
@[simp]
theorem inscribedPerimeter_circleInscribedSquare (o : Orientation ℝ E (Fin 2)) (c e : E)
    {R : ℝ} (he : ‖e‖ = 1) (hR : 0 ≤ R) (s₀ : ℝ) :
    inscribedPerimeter (o.circleCurve c e R) (circleInscribedSquare R s₀) = 4 * √2 * R := by
  rcases hR.eq_or_lt with rfl | hR
  · simp [circleCurve_def, inscribedPerimeter_def]
  · have hv : √2 / 2 ∈ Ioo (-1 : ℝ) 1 :=
      ⟨by nlinarith [Real.sqrt_nonneg 2],
        by nlinarith [Real.sq_sqrt zero_le_two, Real.sqrt_nonneg 2]⟩
    have harc : Real.arccos (√2 / 2) = Real.pi / 4 :=
      Real.arccos_eq_of_eq_cos (by positivity) (by linarith [Real.pi_pos]) Real.cos_pi_div_four.symm
    have hstep (t : ℝ) : ‖o.circleCurve c e R (t + Real.pi * R / 2) - o.circleCurve c e R t‖ =
        √2 * R := by
      have hparam : t + Real.pi * R / 2 =
          (o.circleBilliardTable c e R he hR).nextParam t (√2 / 2) := by
        rw [o.circleBilliardTable_nextParam c e he hR hv, harc]
        ring
      have hlen := o.circleBilliardTable_norm_nextParam_sub c e he hR (s := t) hv
      rw [← hparam] at hlen
      have hsq : √(1 - (√2 / 2) ^ 2) = √2 / 2 := by
        have h1 : 1 - (√2 / 2) ^ 2 = (√2 / 2) ^ 2 := by
          rw [div_pow, Real.sq_sqrt (by norm_num)]
          norm_num
        rw [h1, Real.sqrt_sq (by positivity)]
      rw [hlen, hsq]
      ring
    rw [inscribedPerimeter_def]
    have hterms : ∀ k : ZMod 4,
        ‖o.circleCurve c e R (circleInscribedSquare R s₀ (k + 1)) -
            o.circleCurve c e R (circleInscribedSquare R s₀ k)‖ = √2 * R := fun k ↦ by
      rw [o.circleCurve_circleInscribedSquare_succ, hstep]
    simp only [hterms, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
    push_cast
    ring

/-- **The inscribed square does not maximize perimeter for `N = 4`.** Whenever `e ≠ 0` and `R ≠ 0`,
consecutive vertices of `circleInscribedSquare R s₀` differ by a quarter turn rather than being
antipodal. -/
theorem not_isMaxOn_circleInscribedSquare (o : Orientation ℝ E (Fin 2)) (c : E) {e : E} {R : ℝ}
    (he : e ≠ 0) (hR : R ≠ 0) (s₀ : ℝ) :
    ¬ IsMaxOn (inscribedPerimeter (o.circleCurve c e R)) univ (circleInscribedSquare R s₀) := by
  intro hmax
  have hant := (o.isMaxOn_inscribedPerimeter_circleCurve_zmod_four_iff c e R _).1 hmax 0
  have hv0 : circleInscribedSquare R s₀ 0 = s₀ := by simp
  have hv1 : circleInscribedSquare R s₀ (0 + 1) = s₀ + Real.pi * R / 2 := by
    have h1 : (0 + 1 : ZMod 4).val = 1 := rfl
    rw [circleInscribedSquare_apply, h1, Nat.cast_one, one_mul]
  have hdiv : (s₀ + Real.pi * R / 2) / R = Real.pi / 2 + s₀ / R := by field_simp; ring
  set u₀ := o.rotation (s₀ / R : ℝ) e
  have hu₁ : o.rotation ((s₀ + Real.pi * R / 2) / R : ℝ) e = o.rightAngleRotation u₀ := by
    rw [hdiv, Real.Angle.coe_add, ← o.rotation_rotation, o.rotation_apply, Real.Angle.cos_coe,
      Real.Angle.sin_coe, Real.cos_pi_div_two, Real.sin_pi_div_two, zero_smul, one_smul, zero_add]
  rw [hv1, hv0, circleCurve_eq_add_smul_rotation, circleCurve_eq_add_smul_rotation,
    add_sub_cancel_left, add_sub_cancel_left, ← smul_neg, smul_right_inj hR, hu₁] at hant
  have hin : ⟪u₀, o.rightAngleRotation u₀⟫ = 0 := by
    rw [real_inner_comm, o.inner_rightAngleRotation_self]
  rw [hant, inner_neg_right, real_inner_self_eq_norm_sq, LinearIsometryEquiv.norm_map,
    neg_eq_zero, sq_eq_zero_iff, norm_eq_zero] at hin
  exact he hin

/-! #### `N = 3`: the equilateral triangle versus the `0, π / 2, π` inscribed triangle -/

private theorem circleCurve_circleEquilateralTriangle_succ (o : Orientation ℝ E (Fin 2)) (c e : E)
    (R s₀ : ℝ) (k : ZMod 3) :
    o.circleCurve c e R (circleEquilateralTriangle R s₀ (k + 1)) =
      o.circleCurve c e R (circleEquilateralTriangle R s₀ k + 2 * Real.pi * R / 3) := by
  simpa using (o.periodic_circleCurve c e R).apply_add_val_add_one_mul_div s₀ k

private theorem circleCurve_circleEquilateralTriangle_pred (o : Orientation ℝ E (Fin 2)) (c e : E)
    (R s₀ : ℝ) (k : ZMod 3) :
    o.circleCurve c e R (circleEquilateralTriangle R s₀ (k - 1)) =
      o.circleCurve c e R (circleEquilateralTriangle R s₀ k - 2 * Real.pi * R / 3) := by
  simpa using (o.periodic_circleCurve c e R).apply_add_val_sub_one_mul_div s₀ k

/-- Stepping by `2 π R / 3` along `o.circleCurve c e R` (`R > 0`) traces the chord of `nextParam`
at tangential component `v = 1 / 2`, of length `√3 R` and direction `outgoingDir t (1 / 2)`. -/
private theorem circleCurve_step_third_eq (o : Orientation ℝ E (Fin 2)) (c e : E) {R : ℝ}
    (he : ‖e‖ = 1) (hR : 0 < R) (t : ℝ) :
    o.circleCurve c e R (t + 2 * Real.pi * R / 3) - o.circleCurve c e R t =
      (√3 * R) • (o.circleBilliardTable c e R he hR).outgoingDir t (1 / 2) := by
  have hv : (1 / 2 : ℝ) ∈ Ioo (-1) 1 := by norm_num
  have hparam : t + 2 * Real.pi * R / 3 =
      (o.circleBilliardTable c e R he hR).nextParam t (1 / 2) := by
    rw [o.circleBilliardTable_nextParam c e he hR hv, Real.arccos_one_half]
    ring
  have hlen : ‖o.circleCurve c e R (t + 2 * Real.pi * R / 3) - o.circleCurve c e R t‖ =
      √3 * R := by
    have hc := o.circleBilliardTable_norm_nextParam_sub c e he hR (s := t) hv
    rw [← hparam] at hc
    have hsqrt : √(1 - (1 / 2 : ℝ) ^ 2) = √3 / 2 := by
      have h34 : (1 : ℝ) - (1 / 2) ^ 2 = 3 / 2 ^ 2 := by norm_num
      rw [h34, Real.sqrt_div (by norm_num), Real.sqrt_sq (by norm_num)]
    rw [hc, hsqrt]
    ring
  have hsub := (o.circleBilliardTable c e R he hR).sub_eq_norm_smul_outgoingDir (s := t) hv
  simpa only [coe_circleBilliardTable, ← hparam, hlen] using hsub

/-- Every side of `circleEquilateralTriangle R s₀` (`R ≥ 0`) has length `√3 R`. -/
theorem norm_sub_circleEquilateralTriangle (o : Orientation ℝ E (Fin 2)) (c e : E) {R : ℝ}
    (he : ‖e‖ = 1) (hR : 0 ≤ R) (s₀ : ℝ) (k : ZMod 3) :
    ‖o.circleCurve c e R (circleEquilateralTriangle R s₀ (k + 1)) -
        o.circleCurve c e R (circleEquilateralTriangle R s₀ k)‖ = √3 * R := by
  rcases hR.eq_or_lt with rfl | hRpos
  · simp [circleCurve_def]
  · rw [o.circleCurve_circleEquilateralTriangle_succ, o.circleCurve_step_third_eq c e he hRpos,
      norm_smul, (o.circleBilliardTable c e R he hRpos).norm_outgoingDir (by norm_num),
      mul_one, Real.norm_of_nonneg (by positivity)]

/-- `circleEquilateralTriangle R s₀` (`R ≥ 0`) has inscribed perimeter `3 √3 R`. -/
@[simp]
theorem inscribedPerimeter_circleEquilateralTriangle (o : Orientation ℝ E (Fin 2)) (c e : E)
    {R : ℝ} (he : ‖e‖ = 1) (hR : 0 ≤ R) (s₀ : ℝ) :
    inscribedPerimeter (o.circleCurve c e R) (circleEquilateralTriangle R s₀) = 3 * √3 * R :=
  (inscribedPerimeter_zmod_three_eq_iff_norm_sub_eq
    fun _ ↦ o.circleCurve_mem_sphere c e he hR _).2
    (o.norm_sub_circleEquilateralTriangle c e he hR s₀)

/-- **For `N = 3`, perimeter maximizers on the circle are equilateral triangles.** A `3`-gon
maximizes `inscribedPerimeter` on `o.circleCurve c e R` (`R ≥ 0`) if and only if every side has
length `√3 R`. -/
theorem isMaxOn_inscribedPerimeter_circleCurve_zmod_three_iff (o : Orientation ℝ E (Fin 2))
    (c e : E) {R : ℝ} (he : ‖e‖ = 1) (hR : 0 ≤ R) (s : ZMod 3 → ℝ) :
    IsMaxOn (inscribedPerimeter (o.circleCurve c e R)) univ s ↔
      ∀ k, ‖o.circleCurve c e R (s (k + 1)) - o.circleCurve c e R (s k)‖ = √3 * R := by
  rw [← inscribedPerimeter_zmod_three_eq_iff_norm_sub_eq
    (fun k ↦ o.circleCurve_mem_sphere c e he hR _)]
  constructor
  · intro hs
    refine le_antisymm
      (inscribedPerimeter_zmod_three_le_of_mem_sphere
        fun k ↦ o.circleCurve_mem_sphere c e he hR _) ?_
    simpa [o.inscribedPerimeter_circleEquilateralTriangle c e he hR 0] using
      isMaxOn_iff.1 hs (circleEquilateralTriangle R 0) (mem_univ _)
  · intro hs
    refine isMaxOn_iff.2 fun r _ ↦ ?_
    rw [hs]
    exact inscribedPerimeter_zmod_three_le_of_mem_sphere
      fun k ↦ o.circleCurve_mem_sphere c e he hR _

/-- **Outgoing side of the reflection law on the equilateral triangle.** At every vertex `k` of
`circleEquilateralTriangle R s₀` (`R > 0`), the unit outgoing chord has inner product `1 / 2` with
the unit tangent `χ'(s_k)`. -/
theorem inner_outgoing_circleEquilateralTriangle (o : Orientation ℝ E (Fin 2)) (c e : E)
    {R : ℝ} (he : ‖e‖ = 1) (hR : 0 < R) (s₀ : ℝ) (k : ZMod 3) :
    ⟪‖o.circleCurve c e R (circleEquilateralTriangle R s₀ (k + 1)) -
          o.circleCurve c e R (circleEquilateralTriangle R s₀ k)‖⁻¹ •
        (o.circleCurve c e R (circleEquilateralTriangle R s₀ (k + 1)) -
          o.circleCurve c e R (circleEquilateralTriangle R s₀ k)),
      deriv (o.circleCurve c e R) (circleEquilateralTriangle R s₀ k)⟫ = 1 / 2 := by
  have hpos : √3 * R ≠ 0 := by positivity
  rw [o.norm_sub_circleEquilateralTriangle c e he hR.le s₀ k,
    o.circleCurve_circleEquilateralTriangle_succ, o.circleCurve_step_third_eq c e he hR,
    inv_smul_smul₀ hpos, real_inner_comm, ← o.coe_circleBilliardTable c e R he hR]
  exact (o.circleBilliardTable c e R he hR).inner_deriv_outgoingDir _ (1 / 2)

/-- **Incoming side of the reflection law on the equilateral triangle.** At every vertex `k` of
`circleEquilateralTriangle R s₀` (`R > 0`), the unit incoming chord also has inner product `1 / 2`
with the unit tangent `χ'(s_k)`. -/
theorem inner_incoming_circleEquilateralTriangle (o : Orientation ℝ E (Fin 2)) (c e : E)
    {R : ℝ} (he : ‖e‖ = 1) (hR : 0 < R) (s₀ : ℝ) (k : ZMod 3) :
    ⟪‖o.circleCurve c e R (circleEquilateralTriangle R s₀ k) -
          o.circleCurve c e R (circleEquilateralTriangle R s₀ (k - 1))‖⁻¹ •
        (o.circleCurve c e R (circleEquilateralTriangle R s₀ k) -
          o.circleCurve c e R (circleEquilateralTriangle R s₀ (k - 1))),
      deriv (o.circleCurve c e R) (circleEquilateralTriangle R s₀ k)⟫ = 1 / 2 := by
  set t := circleEquilateralTriangle R s₀ k - 2 * Real.pi * R / 3
  have ht : t + 2 * Real.pi * R / 3 = circleEquilateralTriangle R s₀ k := sub_add_cancel _ _
  have hv : (1 / 2 : ℝ) ∈ Ioo (-1) 1 := by norm_num
  have hparam : circleEquilateralTriangle R s₀ k =
      (o.circleBilliardTable c e R he hR).nextParam t (1 / 2) := by
    rw [o.circleBilliardTable_nextParam c e he hR hv, Real.arccos_one_half, ← ht]
    ring
  have hstep := o.circleCurve_step_third_eq c e he hR t
  rw [ht] at hstep
  have hnorm : ‖o.circleCurve c e R (circleEquilateralTriangle R s₀ k) -
      o.circleCurve c e R (circleEquilateralTriangle R s₀ (k - 1))‖ = √3 * R := by
    simpa only [sub_add_cancel] using o.norm_sub_circleEquilateralTriangle c e he hR.le s₀ (k - 1)
  have hpos : √3 * R ≠ 0 := by positivity
  rw [hnorm, o.circleCurve_circleEquilateralTriangle_pred, hstep, inv_smul_smul₀ hpos, hparam,
    ← o.coe_circleBilliardTable c e R he hR,
    ← StrictConvexBilliardTable.nextTangential_def]
  exact o.circleBilliardTable_nextTangential c e he hR hv

private theorem circleCurve_circleRightTriangle_one_sub_zero (o : Orientation ℝ E (Fin 2))
    (c e : E) (R : ℝ) :
    o.circleCurve c e R (circleRightTriangle R (0 + 1)) -
        o.circleCurve c e R (circleRightTriangle R 0) =
      R • (o.rightAngleRotation e - e) := by
  have hs0 : circleRightTriangle R 0 = 0 := rfl
  have hs1 : circleRightTriangle R (0 + 1) = Real.pi * R / 2 := rfl
  rw [hs1, hs0, o.circleCurve_pi_mul_div_two, o.circleCurve_zero]
  module

/-- Consecutive vertices of `circleRightTriangle R` (`e ≠ 0`, `R ≠ 0`) are distinct. -/
theorem apply_add_one_ne_circleRightTriangle (o : Orientation ℝ E (Fin 2)) (c : E) {e : E} {R : ℝ}
    (he : e ≠ 0) (hR : R ≠ 0) (k : ZMod 3) :
    o.circleCurve c e R (circleRightTriangle R (k + 1)) ≠
      o.circleCurve c e R (circleRightTriangle R k) := by
  have hne10 : o.rightAngleRotation e ≠ e := fun h ↦ he <| by
    simpa [h] using o.inner_rightAngleRotation_self e
  have hne21 : c - R • e ≠ c + R • o.rightAngleRotation e := fun h ↦
    he <| inner_self_eq_zero.1 <| by
      have h' : -e = o.rightAngleRotation e :=
        smul_right_injective E hR (by simpa [sub_eq_add_neg, ← smul_neg] using h)
      have hin := o.inner_rightAngleRotation_self e
      rw [← h', inner_neg_left, neg_eq_zero] at hin
      exact hin
  have hne02 : c + R • e ≠ c - R • e := fun h ↦ by
    have h2R : (2 * R) • e = 0 := by
      calc
        (2 * R) • e = (c + R • e) - (c - R • e) := by module
        _ = 0 := sub_eq_zero.2 h
    exact mul_ne_zero two_ne_zero hR ((smul_eq_zero.1 h2R).resolve_right he)
  have hs0 : circleRightTriangle R 0 = 0 := rfl
  have hs1 : circleRightTriangle R 1 = Real.pi * R / 2 := rfl
  have hs2 : circleRightTriangle R 2 = Real.pi * R := rfl
  have h01 : (0 : ZMod 3) + 1 = 1 := rfl
  have h12 : (1 : ZMod 3) + 1 = 2 := rfl
  have h20 : (2 : ZMod 3) + 1 = 0 := rfl
  have hk0 : o.circleCurve c e R (circleRightTriangle R ((0 : ZMod 3) + 1)) ≠
      o.circleCurve c e R (circleRightTriangle R 0) := by
    rw [h01, hs1, hs0, o.circleCurve_pi_mul_div_two, o.circleCurve_zero, ne_eq, add_right_inj,
      smul_right_inj hR]
    exact hne10
  have hk1 : o.circleCurve c e R (circleRightTriangle R ((1 : ZMod 3) + 1)) ≠
      o.circleCurve c e R (circleRightTriangle R 1) := by
    rw [h12, hs2, hs1, o.circleCurve_pi_mul, o.circleCurve_pi_mul_div_two]
    exact hne21
  have hk2 : o.circleCurve c e R (circleRightTriangle R ((2 : ZMod 3) + 1)) ≠
      o.circleCurve c e R (circleRightTriangle R 2) := by
    rw [h20, hs0, hs2, o.circleCurve_zero, o.circleCurve_pi_mul]
    exact hne02
  fin_cases k
  · exact hk0
  · exact hk1
  · exact hk2

/-- **Incoming inner product at angle `0` of the `0, π / 2, π` triangle.** At vertex `0` of
`circleRightTriangle R`, the incoming unit chord from angle `π` to angle `0` has inner product `0`
with the tangent `χ'(0)`. -/
theorem inner_incoming_circleRightTriangle_zero (o : Orientation ℝ E (Fin 2)) (c e : E) (R : ℝ) :
    ⟪‖o.circleCurve c e R (circleRightTriangle R 0) -
          o.circleCurve c e R (circleRightTriangle R (0 - 1))‖⁻¹ •
        (o.circleCurve c e R (circleRightTriangle R 0) -
          o.circleCurve c e R (circleRightTriangle R (0 - 1))),
      deriv (o.circleCurve c e R) (circleRightTriangle R 0)⟫ = 0 := by
  rcases eq_or_ne R 0 with rfl | hR
  · simp [circleCurve_def]
  · have hs0 : circleRightTriangle R 0 = 0 := rfl
    have hs2 : circleRightTriangle R (0 - 1) = Real.pi * R := rfl
    have hdiff : o.circleCurve c e R 0 - o.circleCurve c e R (Real.pi * R) = (2 * R) • e := by
      rw [o.circleCurve_zero, o.circleCurve_pi_mul]
      module
    rw [hs0, hs2, hdiff, o.deriv_circleCurve_zero c e hR, smul_smul, real_inner_smul_left,
      o.inner_rightAngleRotation_right, o.areaForm_apply_self, neg_zero, mul_zero]

/-- **Outgoing inner product at angle `0` of the `0, π / 2, π` triangle.** At vertex `0` of
`circleRightTriangle R` (`R > 0`), the outgoing unit chord from angle `0` to angle `π / 2` has
inner product `1 / √2` with the unit tangent `χ'(0)`. -/
theorem inner_outgoing_circleRightTriangle_zero (o : Orientation ℝ E (Fin 2)) (c e : E)
    {R : ℝ} (he : ‖e‖ = 1) (hR : 0 < R) :
    ⟪‖o.circleCurve c e R (circleRightTriangle R (0 + 1)) -
          o.circleCurve c e R (circleRightTriangle R 0)‖⁻¹ •
        (o.circleCurve c e R (circleRightTriangle R (0 + 1)) -
          o.circleCurve c e R (circleRightTriangle R 0)),
      deriv (o.circleCurve c e R) (circleRightTriangle R 0)⟫ = 1 / √2 := by
  have hs0 : circleRightTriangle R 0 = 0 := rfl
  have hnorm_orth : ‖o.rightAngleRotation e - e‖ = √2 := by
    have h := norm_sub_eq_sqrt_iff_real_inner_eq_zero.mpr (o.inner_rightAngleRotation_self e)
    rw [LinearIsometryEquiv.norm_map, he] at h
    norm_num at h
    exact h
  have hnorm : ‖R • (o.rightAngleRotation e - e)‖ = R * √2 := by
    rw [norm_smul, hnorm_orth, Real.norm_of_nonneg hR.le]
  have hJe2 : ⟪o.rightAngleRotation e, o.rightAngleRotation e⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, LinearIsometryEquiv.norm_map, he, one_pow]
  rw [o.circleCurve_circleRightTriangle_one_sub_zero, hs0, o.deriv_circleCurve_zero c e hR.ne',
    hnorm, smul_smul, mul_inv_rev, mul_assoc, inv_mul_cancel₀ hR.ne', mul_one,
    real_inner_smul_left, inner_sub_left, hJe2, o.inner_rightAngleRotation_right,
    o.areaForm_apply_self]
  ring

/-- **Failure of the reflection law at angle `0` for the `0, π / 2, π` triangle.** Whenever `e ≠ 0`
and `R ≠ 0`, the incoming and outgoing unit-chord inner products at vertex `0` differ. -/
theorem incoming_ne_outgoing_circleRightTriangle_zero (o : Orientation ℝ E (Fin 2)) (c : E) {e : E}
    {R : ℝ} (he : e ≠ 0) (hR : R ≠ 0) :
    ⟪‖o.circleCurve c e R (circleRightTriangle R 0) -
          o.circleCurve c e R (circleRightTriangle R (0 - 1))‖⁻¹ •
        (o.circleCurve c e R (circleRightTriangle R 0) -
          o.circleCurve c e R (circleRightTriangle R (0 - 1))),
      deriv (o.circleCurve c e R) (circleRightTriangle R 0)⟫ ≠
    ⟪‖o.circleCurve c e R (circleRightTriangle R (0 + 1)) -
          o.circleCurve c e R (circleRightTriangle R 0)‖⁻¹ •
        (o.circleCurve c e R (circleRightTriangle R (0 + 1)) -
          o.circleCurve c e R (circleRightTriangle R 0)),
      deriv (o.circleCurve c e R) (circleRightTriangle R 0)⟫ := by
  have hs0 : circleRightTriangle R 0 = 0 := rfl
  have hne : R • (o.rightAngleRotation e - e) ≠ 0 := by
    rw [← o.circleCurve_circleRightTriangle_one_sub_zero c e R]
    exact sub_ne_zero.2 (o.apply_add_one_ne_circleRightTriangle c he hR 0)
  have hJe2 : ⟪o.rightAngleRotation e, o.rightAngleRotation e⟫ = ‖e‖ ^ 2 := by
    rw [real_inner_self_eq_norm_sq, LinearIsometryEquiv.norm_map]
  rw [o.inner_incoming_circleRightTriangle_zero c e R,
    o.circleCurve_circleRightTriangle_one_sub_zero, hs0, o.deriv_circleCurve_zero c e hR,
    smul_smul, real_inner_smul_left, inner_sub_left, hJe2, o.inner_rightAngleRotation_right,
    o.areaForm_apply_self, neg_zero, sub_zero]
  exact (mul_ne_zero (mul_ne_zero (inv_ne_zero (norm_ne_zero_iff.2 hne)) hR)
    (pow_ne_zero 2 (norm_ne_zero_iff.2 he))).symm

/-- The `0, π / 2, π` inscribed triangle is not a local extremum of `inscribedPerimeter` on
`o.circleCurve c e R` (`e ≠ 0`, `R ≠ 0`). -/
theorem not_isLocalExtr_circleRightTriangle (o : Orientation ℝ E (Fin 2)) (c : E) {e : E} {R : ℝ}
    (he : e ≠ 0) (hR : R ≠ 0) :
    ¬ IsLocalExtr (inscribedPerimeter (o.circleCurve c e R)) (circleRightTriangle R) := by
  intro hloc
  have hd : DifferentiableAt ℝ (o.circleCurve c e R) (circleRightTriangle R 0) :=
    (o.hasDerivAt_circleCurve c e hR _).differentiableAt
  have h20 : (0 : ZMod 3) - 1 = 2 := rfl
  have h21 : (2 : ZMod 3) + 1 = 0 := rfl
  have hne1 : o.circleCurve c e R (circleRightTriangle R 0) ≠
      o.circleCurve c e R (circleRightTriangle R (0 - 1)) := by
    rw [h20, ← h21]
    exact o.apply_add_one_ne_circleRightTriangle c he hR 2
  have hne2 : o.circleCurve c e R (circleRightTriangle R (0 + 1)) ≠
      o.circleCurve c e R (circleRightTriangle R 0) :=
    o.apply_add_one_ne_circleRightTriangle c he hR 0
  exact o.incoming_ne_outgoing_circleRightTriangle_zero c he hR
    (inner_eq_inner_of_isLocalExtr_inscribedPerimeter hloc hd hne1 hne2)

end Orientation
