/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Trigonometric.MatrixFinTwo
public import TauCeti.GroupTheory.TriangleGroup.Basic
import Mathlib.Analysis.SpecialFunctions.Arcosh
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Bounds
import TauCeti.Data.Nat.Cast.Order.Field
import TauCeti.GroupTheory.TriangleGroup.Euclidean
import TauCeti.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup.OrderOf

/-!
# Hyperbolic triangle groups are infinite

For nonzero natural parameters `a`, `b`, and `c`, the triangle group `Δ(a, b, c)` is
*hyperbolic* when `1/a + 1/b + 1/c < 1`. This file proves that such a group is infinite, by an
explicit representation in `PSL(2, ℝ)` in which the commutator of the generators `x` and `y`
goes to a hyperbolic element.

Write `θ₁ = π / a`, `θ₂ = π / b`, `θ₃ = π / c`. For real `t`, the matrices

`X = !![cos θ₁, sin θ₁; -sin θ₁, cos θ₁]`,
`Y = !![cos θ₂, exp t * sin θ₂; -(exp (-t) * sin θ₂), cos θ₂]`

(`Matrix.SpecialLinearGroup.conjRotation θ₁ 0` and `Matrix.SpecialLinearGroup.conjRotation θ₂ t`)
lie in `SL(2, ℝ)`, and have traces `2 cos θ₁` and `2 cos θ₂`, so their classes in `PSL(2, ℝ)` have
orders dividing `a` and `b`. The trace of `Y * X` is `2 cos θ₁ cos θ₂ - 2 cosh t sin θ₁ sin θ₂`,
and the hyperbolicity of `(a, b, c)` is exactly what makes

`κ = (cos θ₁ cos θ₂ + cos θ₃) / (sin θ₁ sin θ₂)`

greater than `1` (`TauCeti.one_lt_cos_mul_cos_add_cos_div_sin_mul_sin`): as
`cos θ₁ cos θ₂ - sin θ₁ sin θ₂ = -cos (π - θ₁ - θ₂)`, the inequality `κ > 1` says
`cos (π - θ₁ - θ₂) < cos θ₃`, that is `θ₃ < π - θ₁ - θ₂`. For `t = arcosh κ > 0` the trace of
`Y * X` is then `-2 cos θ₃`, so the class of `Y * X` has order dividing `c`, and the universal
property of the triangle group gives a homomorphism `pslRep : Δ(a, b, c) →* PSL(2, ℝ)` sending `x`
and `y` to the classes of `X` and `Y`. Finally, by the Fricke trace identity, the commutator
`X * Y * X⁻¹ * Y⁻¹` has trace `2 + 4 (sin θ₁ sin θ₂ sinh t) ^ 2 > 2`, so its class is a hyperbolic
element of `PSL(2, ℝ)` and has infinite order.

Only the infiniteness of the image is proved; neither the faithfulness of the representation nor
the discreteness of its image is claimed.

## Main results

* `TauCeti.TriangleGroup.pslRep`: for `2 ≤ a, b, c` and `t` with
  `cosh t sin θ₁ sin θ₂ = cos θ₁ cos θ₂ + cos θ₃`, the representation `Δ(a, b, c) →* PSL(2, ℝ)`;
  `pslRep_commutator_x_y` computes its value on the commutator of `x` and `y`.
* `TauCeti.TriangleGroup.not_isOfFinOrder_commutator_x_y_of_inv_add_inv_add_inv_lt_one`: if
  `1/a + 1/b + 1/c < 1` with `a, b, c` nonzero, then the commutator of `x` and `y` has infinite
  order in `Δ(a, b, c)`.
* `TauCeti.TriangleGroup.infinite_of_inv_add_inv_add_inv_lt_one`: the hyperbolic triangle groups
  are infinite.
* `TauCeti.TriangleGroup.infinite_of_inv_add_inv_add_inv_le_one`: together with the Euclidean
  case, every triangle group with nonzero parameters and `1/a + 1/b + 1/c ≤ 1` is infinite.

## References

* TauCetiRoadmap, `BelyiMaps`, milestone 4.5 (the five-step construction of the hyperbolic
  triangle-group representation used here).
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

variable {a b c : ℕ}

/-- The representation of the triangle group `Δ(a, b, c)` in `PSL(2, ℝ)` sending `x` and `y` to the
classes of the conjugated rotations `X = conjRotation (π / a) 0` and `Y = conjRotation (π / b) t`,
and `z` to the class of `(Y * X)⁻¹`. It requires `2 ≤ a, b, c` and
`cosh t * (sin (π / a) * sin (π / b)) = cos (π / a) * cos (π / b) + cos (π / c)`, which makes
`Y * X` of trace `-2 cos (π / c)`; a nonzero such `t` exists when `1/a + 1/b + 1/c < 1`. -/
def pslRep (t : ℝ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (ht : cosh t * (sin (π / a) * sin (π / b)) = cos (π / a) * cos (π / b) + cos (π / c)) :
    TriangleGroup a b c →* PSL(2, ℝ) :=
  lift (SpecialLinearGroup.conjRotation (π / a) 0 : PSL(2, ℝ))
    (SpecialLinearGroup.conjRotation (π / b) t)
    ((SpecialLinearGroup.conjRotation (π / b) t : PSL(2, ℝ)) *
      SpecialLinearGroup.conjRotation (π / a) 0)⁻¹
    (ProjectiveSpecialLinearGroup.mk_pow_eq_one_of_trace_sq_eq_two_mul_cos_pi_div_sq ha
      (by rw [SpecialLinearGroup.trace_conjRotation]))
    (ProjectiveSpecialLinearGroup.mk_pow_eq_one_of_trace_sq_eq_two_mul_cos_pi_div_sq hb
      (by rw [SpecialLinearGroup.trace_conjRotation]))
    (by
      rw [inv_pow, inv_eq_one, ← QuotientGroup.mk_mul]
      refine ProjectiveSpecialLinearGroup.mk_pow_eq_one_of_trace_sq_eq_two_mul_cos_pi_div_sq hc ?_
      rw [SpecialLinearGroup.trace_conjRotation_mul_conjRotation, mul_assoc 2 (cosh t), ht]
      ring)
    (by group)

variable (t : ℝ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
  (ht : cosh t * (sin (π / a) * sin (π / b)) = cos (π / a) * cos (π / b) + cos (π / c))

@[simp]
theorem pslRep_x :
    pslRep t ha hb hc ht (x a b c) = (SpecialLinearGroup.conjRotation (π / a) 0 : PSL(2, ℝ)) :=
  lift_x ..

@[simp]
theorem pslRep_y :
    pslRep t ha hb hc ht (y a b c) = (SpecialLinearGroup.conjRotation (π / b) t : PSL(2, ℝ)) :=
  lift_y ..

@[simp]
theorem pslRep_z :
    pslRep t ha hb hc ht (z a b c) =
      ((SpecialLinearGroup.conjRotation (π / b) t : PSL(2, ℝ)) *
        SpecialLinearGroup.conjRotation (π / a) 0)⁻¹ :=
  lift_z ..

/-- The commutator of `x` and `y` goes to the class of the commutator of the two conjugated
rotations, a matrix of trace `2 + 4 (sin (π / a) sin (π / b) sinh t) ^ 2`
(`Matrix.SpecialLinearGroup.trace_commutatorElement_conjRotation`). -/
@[simp]
theorem pslRep_commutator_x_y :
    pslRep t ha hb hc ht ⁅x a b c, y a b c⁆ =
      ((⁅SpecialLinearGroup.conjRotation (π / a) 0, SpecialLinearGroup.conjRotation (π / b) t⁆ :
        SL(2, ℝ)) : PSL(2, ℝ)) := by
  simp [commutatorElement_def]

/-- **Hyperbolic triangle groups have elements of infinite order.** If `1/a + 1/b + 1/c < 1` with
`a, b, c` nonzero, then the commutator of the generators `x` and `y` of the triangle group
`Δ(a, b, c)` has infinite order. The witness is a representation of `Δ(a, b, c)` in `PSL(2, ℝ)`
sending `x` and `y` to elliptic elements whose commutator is hyperbolic. -/
theorem not_isOfFinOrder_commutator_x_y_of_inv_add_inv_add_inv_lt_one {a b c : ℕ} (ha : a ≠ 0)
    (hb : b ≠ 0) (hc : c ≠ 0) (h : (a : ℚ)⁻¹ + (b : ℚ)⁻¹ + (c : ℚ)⁻¹ < 1) :
    ¬ IsOfFinOrder ⁅x a b c, y a b c⁆ := by
  have hR : (a : ℝ)⁻¹ + (b : ℝ)⁻¹ + (c : ℝ)⁻¹ < 1 := by
    have := (Rat.cast_lt (K := ℝ)).mpr h
    push_cast at this
    exact this
  have ha₀ : (0 : ℝ) ≤ (a : ℝ)⁻¹ := by positivity
  have hb₀ : (0 : ℝ) ≤ (b : ℝ)⁻¹ := by positivity
  have hc₀ : (0 : ℝ) ≤ (c : ℝ)⁻¹ := by positivity
  have ha₂ := two_le_of_cast_inv_lt_one (α := ℝ) ha (by linarith)
  have hb₂ := two_le_of_cast_inv_lt_one (α := ℝ) hb (by linarith)
  have hc₂ := two_le_of_cast_inv_lt_one (α := ℝ) hc (by linarith)
  obtain ⟨t, htpos, hcosh⟩ := exists_pos_cosh_mul_sin_mul_sin_eq
    (α := π / a) (β := π / b) (γ := π / c)
    (div_pos pi_pos (Nat.cast_pos.2 (by omega)))
    (div_pos pi_pos (Nat.cast_pos.2 (by omega))) (by positivity) (by
      have := mul_lt_mul_of_pos_left hR pi_pos
      simp only [div_eq_mul_inv]
      linarith)
  have ht : t ≠ 0 := htpos.ne'
  intro hfin
  have hρ := (pslRep t ha₂ hb₂ hc₂ hcosh).isOfFinOrder hfin
  rw [pslRep_commutator_x_y] at hρ
  -- The image of the commutator is the class of a matrix of trace greater than `2`.
  refine ProjectiveSpecialLinearGroup.not_isOfFinOrder_mk_of_two_lt_abs_trace ?_ hρ
  have hs : sin (π / a) * sin (π / b) * sinh t ≠ 0 :=
    mul_ne_zero (mul_ne_zero (sin_pi_div_pos (Nat.one_lt_cast.2 ha₂)).ne'
      (sin_pi_div_pos (Nat.one_lt_cast.2 hb₂)).ne') (sinh_ne_zero.2 ht)
  have hs₂ : 0 < (sin (π / a) * sin (π / b) * sinh t) ^ 2 := by positivity
  rw [SpecialLinearGroup.trace_commutatorElement_conjRotation, abs_of_pos (by positivity)]
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
