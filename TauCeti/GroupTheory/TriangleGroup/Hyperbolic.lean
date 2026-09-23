/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.TriangleGroup.Basic
import Mathlib.Analysis.SpecialFunctions.Arcosh
import TauCeti.Analysis.SpecialFunctions.Trigonometric.PiDiv
import TauCeti.Data.Nat.ReciprocalSum
import TauCeti.GroupTheory.TriangleGroup.Euclidean
import TauCeti.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup.OrderOf
import TauCeti.LinearAlgebra.Matrix.Trace.FinTwo

/-!
# Hyperbolic triangle groups are infinite

For nonzero natural parameters `a`, `b`, and `c`, the triangle group `Δ(a, b, c)` is
*hyperbolic* when `1/a + 1/b + 1/c < 1`. This file proves that such a group is infinite, by an
explicit representation in `PSL(2, ℝ)` in which the commutator of the generators `x` and `y`
goes to a hyperbolic element.

Write `θ₁ = π / a`, `θ₂ = π / b`, `θ₃ = π / c`. For real `t`, the matrices

`X = !![cos θ₁, sin θ₁; -sin θ₁, cos θ₁]`,
`Y = !![cos θ₂, exp t * sin θ₂; -(exp (-t) * sin θ₂), cos θ₂]`

lie in `SL(2, ℝ)`, and have traces `2 cos θ₁` and `2 cos θ₂`, so their classes in `PSL(2, ℝ)` have
orders dividing `a` and `b`. The trace of `Y * X` is `2 cos θ₁ cos θ₂ - 2 cosh t sin θ₁ sin θ₂`,
and the hyperbolicity of `(a, b, c)` is exactly what makes

`κ = (cos θ₁ cos θ₂ + cos θ₃) / (sin θ₁ sin θ₂)`

greater than `1`: as `cos θ₁ cos θ₂ - sin θ₁ sin θ₂ = -cos (π - θ₁ - θ₂)`, the inequality `κ > 1`
says `cos (π - θ₁ - θ₂) < cos θ₃`, that is `θ₃ < π - θ₁ - θ₂`. For `t = arcosh κ > 0` the trace of
`Y * X` is then `-2 cos θ₃`, so the class of `Y * X` has order dividing `c`, and the universal
property of the triangle group gives a homomorphism `Δ(a, b, c) →* PSL(2, ℝ)` sending `x` and `y`
to the classes of `X` and `Y`. Finally, by the Fricke trace identity, the commutator
`X * Y * X⁻¹ * Y⁻¹` has trace `2 + 4 (sin θ₁ sin θ₂ sinh t) ^ 2 > 2`, so its class is a hyperbolic
element of `PSL(2, ℝ)` and has infinite order.

Only the infiniteness of the image is proved; neither the faithfulness of the representation nor
the discreteness of its image is claimed.

## Main results

* `TauCeti.TriangleGroup.not_isOfFinOrder_commutator_x_y_of_inv_add_inv_add_inv_lt_one`: if
  `1/a + 1/b + 1/c < 1` with `a, b, c` nonzero, then the commutator of `x` and `y` has infinite
  order in `Δ(a, b, c)`.
* `TauCeti.TriangleGroup.infinite_of_inv_add_inv_add_inv_lt_one`: the hyperbolic triangle groups
  are infinite.
* `TauCeti.TriangleGroup.infinite_of_inv_add_inv_add_inv_le_one`: together with the Euclidean
  case, every triangle group with nonzero parameters and `1/a + 1/b + 1/c ≤ 1` is infinite.

## References

* E. Girondo, G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins d'Enfants*,
  LMS Student Texts 79, Cambridge University Press, 2012, §2.4 (hyperbolic triangle groups, there
  realized through reflections in the sides of a hyperbolic triangle rather than through the
  matrices used here).
* Svetlana Katok, *Fuchsian Groups*, Chicago Lectures in Mathematics, University of Chicago
  Press, 1992, §2.1 (hyperbolic elements of `PSL(2, ℝ)` and their traces).
-/

public section

noncomputable section

open Real Matrix
open scoped commutatorElement MatrixGroups

namespace TauCeti

namespace TriangleGroup

/-- The matrix `!![cos θ, exp t * sin θ; -(exp (-t) * sin θ), cos θ]` of `SL(2, ℝ)`, the conjugate
of the rotation matrix of trace `2 cos θ` by `diag (exp (t / 2), exp (-t / 2))`. -/
private def ellipticSL (θ t : ℝ) : SL(2, ℝ) :=
  ⟨!![cos θ, exp t * sin θ; -(exp (-t) * sin θ), cos θ], by
    rw [det_fin_two_of, exp_neg]
    field_simp
    linear_combination cos_sq_add_sin_sq θ⟩

private theorem coe_ellipticSL (θ t : ℝ) :
    (ellipticSL θ t : Matrix (Fin 2) (Fin 2) ℝ) =
      !![cos θ, exp t * sin θ; -(exp (-t) * sin θ), cos θ] := (rfl)

private theorem trace_ellipticSL (θ t : ℝ) :
    (ellipticSL θ t : Matrix (Fin 2) (Fin 2) ℝ).trace = 2 * cos θ := by
  rw [coe_ellipticSL, trace_fin_two_of]
  ring

private theorem trace_ellipticSL_mul_ellipticSL (θ₁ θ₂ t : ℝ) :
    ((ellipticSL θ₂ t * ellipticSL θ₁ 0 : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ).trace =
      2 * cos θ₁ * cos θ₂ - 2 * cosh t * (sin θ₁ * sin θ₂) := by
  rw [SpecialLinearGroup.coe_mul, coe_ellipticSL, coe_ellipticSL, mul_fin_two, trace_fin_two_of,
    cosh_eq]
  simp only [exp_zero, neg_zero, one_mul]
  ring

/-- The commutator of the two matrices has trace `2 + 4 (sin θ₁ sin θ₂ sinh t) ^ 2`, by the Fricke
trace identity. -/
private theorem trace_commutator_ellipticSL (θ₁ θ₂ t : ℝ) :
    ((⁅ellipticSL θ₁ 0, ellipticSL θ₂ t⁆ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ).trace =
      2 + 4 * (sin θ₁ * sin θ₂ * sinh t) ^ 2 := by
  rw [SpecialLinearGroup.trace_commutatorElement_fin_two, trace_ellipticSL, trace_ellipticSL,
    SpecialLinearGroup.coe_mul, trace_mul_comm, ← SpecialLinearGroup.coe_mul,
    trace_ellipticSL_mul_ellipticSL]
  linear_combination 4 * (1 - cos θ₂ ^ 2) * cos_sq_add_sin_sq θ₁ +
    4 * sin θ₁ ^ 2 * cos_sq_add_sin_sq θ₂ + 4 * (sin θ₁ * sin θ₂) ^ 2 * cosh_sq t

/-- For a hyperbolic parameter triple there is a nonzero `t` with
`cosh t * (sin θ₁ * sin θ₂) = cos θ₁ * cos θ₂ + cos θ₃`, namely `t = arcosh κ` in the notation of
the module docstring. -/
private theorem exists_cosh_mul_eq {a b c : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (h : (a : ℝ)⁻¹ + (b : ℝ)⁻¹ + (c : ℝ)⁻¹ < 1) :
    ∃ t : ℝ, t ≠ 0 ∧ cosh t * (sin (π / a) * sin (π / b)) =
      cos (π / a) * cos (π / b) + cos (π / c) := by
  have hs : 0 < sin (π / a) * sin (π / b) := mul_pos (sin_pi_div_pos ha) (sin_pi_div_pos hb)
  -- `cos (π - θ₁ - θ₂) < cos θ₃` because `0 ≤ θ₃ < π - θ₁ - θ₂ ≤ π`.
  have hcos : cos (π - (π / a + π / b)) < cos (π / c) := by
    have hθ : π / c < π - (π / a + π / b) := by
      have := mul_lt_mul_of_pos_left h pi_pos
      simp only [div_eq_mul_inv]
      linarith
    have hθ' : 0 ≤ π / a + π / b := by positivity
    exact cos_lt_cos_of_nonneg_of_le_pi (by positivity) (by linarith) hθ
  rw [cos_pi_sub, cos_add] at hcos
  set κ := (cos (π / a) * cos (π / b) + cos (π / c)) / (sin (π / a) * sin (π / b))
  have hκ : 1 < κ := by
    rw [one_lt_div hs]
    linarith
  refine ⟨arcosh κ, (arcosh_pos hκ).ne', ?_⟩
  rw [cosh_arcosh hκ.le, div_mul_cancel₀ _ hs.ne']

/-- **Hyperbolic triangle groups have elements of infinite order.** If `1/a + 1/b + 1/c < 1` with
`a, b, c` nonzero, then the commutator of the generators `x` and `y` of the triangle group
`Δ(a, b, c)` has infinite order. The witness is a representation of `Δ(a, b, c)` in `PSL(2, ℝ)`
sending `x` and `y` to elliptic elements whose commutator is hyperbolic. -/
theorem not_isOfFinOrder_commutator_x_y_of_inv_add_inv_add_inv_lt_one {a b c : ℕ} (ha : a ≠ 0)
    (hb : b ≠ 0) (hc : c ≠ 0) (h : (a : ℚ)⁻¹ + (b : ℚ)⁻¹ + (c : ℚ)⁻¹ < 1) :
    ¬ IsOfFinOrder ⁅x a b c, y a b c⁆ := by
  have ha₂ := two_le_of_inv_add_inv_add_inv_lt_one ha h
  have hb₂ := two_le_of_inv_add_inv_add_inv_lt_one (q := c) (r := a) hb (by linarith)
  have hc₂ := two_le_of_inv_add_inv_add_inv_lt_one (q := a) (r := b) hc (by linarith)
  have hR : (a : ℝ)⁻¹ + (b : ℝ)⁻¹ + (c : ℝ)⁻¹ < 1 := by
    have := (Rat.cast_lt (K := ℝ)).mpr h
    push_cast at this
    exact this
  obtain ⟨t, ht, hcosh⟩ := exists_cosh_mul_eq ha₂ hb₂ hR
  -- The images of `x`, `y` and `z` in `PSL(2, ℝ)` satisfy the triangle relations.
  set X := ellipticSL (π / a) 0
  set Y := ellipticSL (π / b) t
  have hX : (X : PSL(2, ℝ)) ^ a = 1 :=
    ProjectiveSpecialLinearGroup.mk_pow_eq_one_of_trace_sq_eq ha₂ (by rw [trace_ellipticSL])
  have hY : (Y : PSL(2, ℝ)) ^ b = 1 :=
    ProjectiveSpecialLinearGroup.mk_pow_eq_one_of_trace_sq_eq hb₂ (by rw [trace_ellipticSL])
  have hZ : ((Y : PSL(2, ℝ)) * X)⁻¹ ^ c = 1 := by
    rw [inv_pow, inv_eq_one, ← QuotientGroup.mk_mul]
    refine ProjectiveSpecialLinearGroup.mk_pow_eq_one_of_trace_sq_eq hc₂ ?_
    rw [trace_ellipticSL_mul_ellipticSL, mul_assoc 2 (cosh t), hcosh]
    ring
  let ρ := lift (X : PSL(2, ℝ)) Y ((Y : PSL(2, ℝ)) * X)⁻¹ hX hY hZ (by group)
  -- The image of the commutator is the class of a matrix of trace greater than `2`.
  have hcomm : ⁅(X : PSL(2, ℝ)), (Y : PSL(2, ℝ))⁆ = ((⁅X, Y⁆ : SL(2, ℝ)) : PSL(2, ℝ)) := by
    simp [commutatorElement_def]
  intro hfin
  have hρ := ρ.isOfFinOrder hfin
  rw [map_commutatorElement, lift_x, lift_y, hcomm] at hρ
  refine ProjectiveSpecialLinearGroup.not_isOfFinOrder_mk_of_two_lt_abs_trace ?_ hρ
  have hs : sin (π / a) * sin (π / b) * sinh t ≠ 0 :=
    mul_ne_zero (mul_ne_zero (sin_pi_div_pos ha₂).ne' (sin_pi_div_pos hb₂).ne') (sinh_ne_zero.2 ht)
  have hs₂ : 0 < (sin (π / a) * sin (π / b) * sinh t) ^ 2 := by positivity
  rw [trace_commutator_ellipticSL, abs_of_pos (by positivity)]
  linarith

/-- **Hyperbolic triangle groups are infinite.** If `1/a + 1/b + 1/c < 1` with `a, b, c` nonzero,
then the triangle group `Δ(a, b, c)` is infinite. -/
theorem infinite_of_inv_add_inv_add_inv_lt_one {a b c : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h : (a : ℚ)⁻¹ + (b : ℚ)⁻¹ + (c : ℚ)⁻¹ < 1) : Infinite (TriangleGroup a b c) := by
  rw [← not_finite_iff_infinite]
  intro
  exact not_isOfFinOrder_commutator_x_y_of_inv_add_inv_add_inv_lt_one ha hb hc h
    (isOfFinOrder_of_finite _)

/-- **Euclidean and hyperbolic triangle groups are infinite.** If `1/a + 1/b + 1/c ≤ 1` with
`a, b, c` nonzero, then the triangle group `Δ(a, b, c)` is infinite. -/
theorem infinite_of_inv_add_inv_add_inv_le_one {a b c : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h : (a : ℚ)⁻¹ + (b : ℚ)⁻¹ + (c : ℚ)⁻¹ ≤ 1) : Infinite (TriangleGroup a b c) :=
  h.lt_or_eq.elim (infinite_of_inv_add_inv_add_inv_lt_one ha hb hc)
    (infinite_of_inv_add_inv_add_inv_eq_one ha hb hc)

end TriangleGroup

end TauCeti
