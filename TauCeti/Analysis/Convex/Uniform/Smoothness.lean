/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Operator.LinearIsometry

/-!
# The modulus of smoothness

The modulus of smoothness of a real seminormed space `E` is
`ρ_E(t) = sup {(‖x + t • y‖ + ‖x - t • y‖) / 2 - 1 : ‖x‖ = ‖y‖ = 1}`,
the largest average excess of the norm at the two points `x ± t • y`, for a unit vector `x` and a
unit direction `y`. It is the companion of the modulus of convexity
`TauCeti.modulusOfConvexity`: a space is *uniformly smooth* when `ρ_E(t) / t → 0` as `t → 0⁺`, and
a bound `ρ_E(t) ≤ C t ^ q` expresses smoothness of power type `q`, as a bound
`δ_E(ε) ≥ C ε ^ q` on the modulus of convexity expresses convexity of power type `q`. In the zero
space there is no unit vector, and the modulus is zero by convention.

`modulusOfSmoothness_le_iff` characterizes upper bounds without unfolding the supremum. Each
average excess is nonnegative by the triangle inequality, so the modulus is nonnegative; it is
even in `t`, vanishes at `0`, is at most `|t|`, and is monotone on `[0, ∞)`. Passing to a space
containing an isometric linear copy can only increase the modulus, and linearly isometric spaces
have the same modulus.

## Main declarations

* `TauCeti.modulusOfSmoothness`: the modulus of smoothness `ρ_E(t)`.
* `TauCeti.modulusOfSmoothness_le_iff`, `TauCeti.le_modulusOfSmoothness`: its upper and lower
  bounds.
* `TauCeti.modulusOfSmoothness_neg`, `TauCeti.modulusOfSmoothness_zero`,
  `TauCeti.modulusOfSmoothness_le_abs`, `TauCeti.monotoneOn_modulusOfSmoothness`: evenness, the
  value at zero, the trivial bound, and monotonicity.
* `LinearIsometry.modulusOfSmoothness_le`, `LinearIsometryEquiv.modulusOfSmoothness_eq`:
  comparison along linear isometries.

## References

* J. Lindenstrauss, *On the modulus of smoothness and divergent series in Banach spaces*,
  Michigan Math. J. 10 (1963), 241–252.
* J. Lindenstrauss and L. Tzafriri, *Classical Banach Spaces II*, Springer, 1979,
  Definition 1.e.1.
-/

public section

open Set

namespace TauCeti

variable (E : Type*) [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- The modulus of smoothness `ρ_E(t)`: the supremum of the average excess
`(‖x + t • y‖ + ‖x - t • y‖) / 2 - 1` over unit vectors `x` and `y`, with value zero if there is
no unit vector. -/
noncomputable def modulusOfSmoothness (t : ℝ) : ℝ :=
  sSup (insert 0 {r | ∃ x y : E, ‖x‖ = 1 ∧ ‖y‖ = 1 ∧
    r = (‖x + t • y‖ + ‖x - t • y‖) / 2 - 1})

/-- The defining supremum of average excesses, including the convention for the zero space. -/
theorem modulusOfSmoothness_def (t : ℝ) :
    modulusOfSmoothness E t =
      sSup (insert 0 {r | ∃ x y : E, ‖x‖ = 1 ∧ ‖y‖ = 1 ∧
        r = (‖x + t • y‖ + ‖x - t • y‖) / 2 - 1}) := (rfl)

private theorem excess_le_abs {t : ℝ} {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    (‖x + t • y‖ + ‖x - t • y‖) / 2 - 1 ≤ |t| := by
  have h₁ := norm_add_le x (t • y)
  have h₂ := norm_sub_le x (t • y)
  rw [norm_smul, Real.norm_eq_abs, hy, mul_one] at h₁ h₂
  linarith

private theorem smoothness_mem_upperBounds (t : ℝ) :
    |t| ∈ upperBounds (insert 0 {r | ∃ x y : E, ‖x‖ = 1 ∧ ‖y‖ = 1 ∧
      r = (‖x + t • y‖ + ‖x - t • y‖) / 2 - 1}) := by
  rintro r (rfl | ⟨x, y, hx, hy, rfl⟩)
  · exact abs_nonneg t
  · exact excess_le_abs E hx hy

private theorem smoothness_bddAbove (t : ℝ) :
    BddAbove (insert 0 {r | ∃ x y : E, ‖x‖ = 1 ∧ ‖y‖ = 1 ∧
      r = (‖x + t • y‖ + ‖x - t • y‖) / 2 - 1}) :=
  ⟨|t|, smoothness_mem_upperBounds E t⟩

/-- A number bounds the modulus from above exactly when it is nonnegative and bounds the average
excess of every pair of unit vectors. -/
theorem modulusOfSmoothness_le_iff {t a : ℝ} :
    modulusOfSmoothness E t ≤ a ↔ 0 ≤ a ∧
      ∀ x y : E, ‖x‖ = 1 → ‖y‖ = 1 → (‖x + t • y‖ + ‖x - t • y‖) / 2 - 1 ≤ a := by
  rw [modulusOfSmoothness, csSup_le_iff (smoothness_bddAbove E t) (insert_nonempty _ _)]
  constructor
  · intro h
    exact ⟨h _ (mem_insert _ _), fun x y hx hy ↦
      h _ (mem_insert_of_mem _ ⟨x, y, hx, hy, rfl⟩)⟩
  · rintro ⟨ha, h⟩ r (rfl | ⟨x, y, hx, hy, rfl⟩)
    · exact ha
    · exact h x y hx hy

/-- The modulus bounds the average excess of each pair of unit vectors. -/
theorem le_modulusOfSmoothness {t : ℝ} {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    (‖x + t • y‖ + ‖x - t • y‖) / 2 - 1 ≤ modulusOfSmoothness E t :=
  le_csSup (smoothness_bddAbove E t) (mem_insert_of_mem _ ⟨x, y, hx, hy, rfl⟩)

/-- The modulus of smoothness is nonnegative. -/
theorem modulusOfSmoothness_nonneg (t : ℝ) : 0 ≤ modulusOfSmoothness E t :=
  le_csSup (smoothness_bddAbove E t) (mem_insert _ _)

/-- The modulus of smoothness at `t` is at most `|t|`. -/
theorem modulusOfSmoothness_le_abs (t : ℝ) : modulusOfSmoothness E t ≤ |t| :=
  csSup_le (insert_nonempty _ _) (smoothness_mem_upperBounds E t)

/-- The modulus of smoothness is even. -/
@[simp]
theorem modulusOfSmoothness_neg (t : ℝ) : modulusOfSmoothness E (-t) = modulusOfSmoothness E t := by
  have key (s : ℝ) : modulusOfSmoothness E (-s) ≤ modulusOfSmoothness E s := by
    refine (modulusOfSmoothness_le_iff E).2 ⟨modulusOfSmoothness_nonneg E s, fun x y hx hy ↦ ?_⟩
    have := le_modulusOfSmoothness E (t := s) hx hy
    rw [neg_smul, sub_neg_eq_add, ← sub_eq_add_neg]
    linarith
  exact le_antisymm (key t) (by simpa using key (-t))

/-- The modulus of smoothness vanishes at zero. -/
@[simp]
theorem modulusOfSmoothness_zero : modulusOfSmoothness E 0 = 0 :=
  le_antisymm (by simpa using modulusOfSmoothness_le_abs E 0) (modulusOfSmoothness_nonneg E 0)

/-- In the zero space, the modulus of smoothness is zero at every `t`. -/
@[simp]
theorem modulusOfSmoothness_eq_zero_of_subsingleton [Subsingleton E] (t : ℝ) :
    modulusOfSmoothness E t = 0 := by
  refine le_antisymm ((modulusOfSmoothness_le_iff E).2 ⟨le_rfl, fun x y _ hy ↦ ?_⟩)
    (modulusOfSmoothness_nonneg E t)
  simp [Subsingleton.elim y 0] at hy

/-- The modulus of smoothness is monotone on `[0, ∞)`. -/
theorem monotoneOn_modulusOfSmoothness : MonotoneOn (modulusOfSmoothness E) (Ici 0) := by
  intro s hs t _ hst
  obtain h0 | ht := ((mem_Ici.1 hs).trans hst).eq_or_lt
  · rw [show s = t by linarith [mem_Ici.1 hs]]
  refine (modulusOfSmoothness_le_iff E).2 ⟨modulusOfSmoothness_nonneg E t, fun x y hx hy ↦ ?_⟩
  refine le_trans ?_ (le_modulusOfSmoothness E hx hy)
  -- `x ± s • y` are convex combinations of `x + t • y` and `x - t • y`, with weights
  -- `(t ± s) / (2 t)` and `(t ∓ s) / (2 t)`.
  have hts : 0 ≤ t - s := sub_nonneg.2 hst
  have hts' : 0 ≤ t + s := by linarith [mem_Ici.1 hs]
  have key (u v : E) (hu : (2 * t) • u = (t + s) • (x + t • y) + (t - s) • (x - t • y))
      (hv : (2 * t) • v = (t - s) • (x + t • y) + (t + s) • (x - t • y)) :
      2 * t * (‖u‖ + ‖v‖) ≤ 2 * t * (‖x + t • y‖ + ‖x - t • y‖) := by
    have h₁ := congrArg norm hu
    have h₂ := congrArg norm hv
    have h₁' := norm_add_le ((t + s) • (x + t • y)) ((t - s) • (x - t • y))
    have h₂' := norm_add_le ((t - s) • (x + t • y)) ((t + s) • (x - t • y))
    simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hts, abs_of_nonneg hts',
      abs_of_pos (mul_pos two_pos ht)] at h₁ h₂ h₁' h₂'
    nlinarith
  have := key (x + s • y) (x - s • y) (by module) (by module)
  have := le_of_mul_le_mul_left this (mul_pos two_pos ht)
  linarith

end TauCeti

namespace LinearIsometry

variable {E F : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [SeminormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- Passing to a space containing an isometric linear copy can only increase the modulus of
smoothness. -/
theorem modulusOfSmoothness_le (f : E →ₗᵢ[ℝ] F) (t : ℝ) :
    TauCeti.modulusOfSmoothness E t ≤ TauCeti.modulusOfSmoothness F t := by
  refine (TauCeti.modulusOfSmoothness_le_iff E).2
    ⟨TauCeti.modulusOfSmoothness_nonneg F t, fun x y hx hy ↦ ?_⟩
  simpa only [← map_smul, ← map_add, ← map_sub, f.norm_map] using
    TauCeti.le_modulusOfSmoothness F (t := t) (x := f x) (y := f y) (by simpa using hx)
      (by simpa using hy)

end LinearIsometry

namespace LinearIsometryEquiv

variable {E F : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [SeminormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- Linearly isometric spaces have the same modulus of smoothness. -/
theorem modulusOfSmoothness_eq (f : E ≃ₗᵢ[ℝ] F) (t : ℝ) :
    TauCeti.modulusOfSmoothness E t = TauCeti.modulusOfSmoothness F t :=
  le_antisymm (f.toLinearIsometry.modulusOfSmoothness_le t)
    (f.symm.toLinearIsometry.modulusOfSmoothness_le t)

end LinearIsometryEquiv
