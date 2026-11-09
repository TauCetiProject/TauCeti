/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.ClosedBall.CircleLift
public import TauCeti.KnotTheory.Slice.Basic

/-!
# Sliceness does not depend on a parametrization given by a lift

Smooth and topological sliceness (`TauCeti.IsSmoothlySlice`, `TauCeti.IsTopologicallySlice`) are
stated for a parametrized knot `K : S¹ → Sⁿ`, but they do not depend on the parametrization: if
`K' = K ∘ σ` for a diffeomorphism `σ` of the circle given by a lift (below), then `K'` is slice
exactly when `K` is. That every diffeomorphism of the circle is given by such a lift is not proved
here. A slice disc `Φ` for `K` is reparametrized along with the knot, by a
diffeomorphism `D` of the closed unit disc which is `σ` on the boundary circle: `Φ ∘ D` is a slice
disc for `K'` (`TauCeti.IsSmoothSliceDisc.comp_diffeomorph`), so `K'` is slice exactly when `K` is
(`TauCeti.isSmoothlySlice_congr_diffeomorph`).

For an orientation-preserving `σ`, given by a lift `F`, `σ (Circle.exp x) = Circle.exp (F x)` with
`F (x + 2π) = F x + 2π` and `F' > 0`, the disc diffeomorphism is
`TauCeti.circleLiftDiscDiffeomorph`, which interpolates radially between the identity near the
centre and `σ` near the boundary. An orientation-reversing `σ`, with a lift satisfying
`F (x + 2π) = F x - 2π` and `F' < 0`, is the reversal `z ↦ z⁻¹` followed by an
orientation-preserving diffeomorphism, and sliceness is invariant under reversal
(`TauCeti.isSmoothlySlice_reverse_iff`).

## Main results

* `TauCeti.isSmoothlySlice_congr_lift`, `TauCeti.isTopologicallySlice_congr_lift`: sliceness is
  invariant under reparametrization by an orientation-preserving diffeomorphism of the circle with
  a lift.
* `TauCeti.isSmoothlySlice_congr_lift_of_deriv_neg`,
  `TauCeti.isTopologicallySlice_congr_lift_of_deriv_neg`: the same for an orientation-reversing
  diffeomorphism of the circle with a lift.

## References

* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 8, for
  slice knots.
-/

public section

noncomputable section

open Complex Metric Set Real
open scoped Manifold ContDiff

namespace TauCeti

attribute [local instance] Complex.finrank_real_complex_fact

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (Module.finrank ℝ E = n + 1)]
  {K K' : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)} {σ : Circle → Circle}

/-! ### Reparametrization by a diffeomorphism of the circle -/

variable {F : ℝ → ℝ}

private theorem norm_circleLiftDiscDiffeomorph_eq_one_iff
    (hper : ∀ x, F (x + 2 * π) = F x + 2 * π) (hF : ContDiff ℝ ∞ F) (hpos : ∀ x, 0 < deriv F x)
    (x : closedBall (0 : ℂ) 1) :
    ‖(circleLiftDiscDiffeomorph hper hF hpos x : ℂ)‖ = 1 ↔ ‖(x : ℂ)‖ = 1 := by
  simp

/-- **Smooth sliceness does not depend on the parametrization.** If `σ` is an
orientation-preserving diffeomorphism of the circle with lift `F`, that is
`σ (Circle.exp x) = Circle.exp (F x)` with `F (x + 2π) = F x + 2π` and `F' > 0`, then `K ∘ σ` is
smoothly slice exactly when `K` is. -/
theorem isSmoothlySlice_congr_lift (hper : ∀ x, F (x + 2 * π) = F x + 2 * π)
    (hF : ContDiff ℝ ∞ F) (hpos : ∀ x, 0 < deriv F x)
    (hσ : ∀ x, σ (Circle.exp x) = Circle.exp (F x)) (hK' : ∀ z, K' z = K (σ z)) :
    IsSmoothlySlice K' ↔ IsSmoothlySlice K :=
  isSmoothlySlice_congr_diffeomorph (circleLiftDiscDiffeomorph hper hF hpos)
    (norm_circleLiftDiscDiffeomorph_eq_one_iff hper hF hpos)
    (circleLiftDiscDiffeomorph_inclusion hper hF hpos hσ) hK'

/-- **Topological sliceness does not depend on the parametrization.** If `σ` is an
orientation-preserving diffeomorphism of the circle with lift `F`, then `K ∘ σ` is topologically
slice exactly when `K` is. -/
theorem isTopologicallySlice_congr_lift (hper : ∀ x, F (x + 2 * π) = F x + 2 * π)
    (hF : ContDiff ℝ ∞ F) (hpos : ∀ x, 0 < deriv F x)
    (hσ : ∀ x, σ (Circle.exp x) = Circle.exp (F x)) (hK' : ∀ z, K' z = K (σ z)) :
    IsTopologicallySlice K' ↔ IsTopologicallySlice K :=
  isTopologicallySlice_congr_homeomorph (circleLiftDiscDiffeomorph hper hF hpos).toHomeomorph
    (norm_circleLiftDiscDiffeomorph_eq_one_iff hper hF hpos)
    (circleLiftDiscDiffeomorph_inclusion hper hF hpos hσ) hK'

/-- A lift of an orientation-reversing circle map, negated, is a lift of the map followed by the
reversal `z ↦ z⁻¹`. -/
private theorem neg_lift (hper : ∀ x, F (x + 2 * π) = F x - 2 * π) (hneg : ∀ x, deriv F x < 0)
    (hσ : ∀ x, σ (Circle.exp x) = Circle.exp (F x)) :
    (∀ x, -F (x + 2 * π) = -F x + 2 * π) ∧ (∀ x, 0 < deriv (fun y ↦ -F y) x) ∧
      ∀ x, (σ (Circle.exp x))⁻¹ = Circle.exp (-F x) :=
  ⟨fun x ↦ by rw [hper]; ring, fun x ↦ by simpa [deriv.neg] using hneg x,
    fun x ↦ by rw [hσ, Circle.exp_neg]⟩

/-- **Smooth sliceness does not depend on the parametrization, orientation-reversing case.** If
`σ` is a diffeomorphism of the circle with a lift `F` satisfying `F (x + 2π) = F x - 2π` and
`F' < 0`, then `K ∘ σ` is smoothly slice exactly when `K` is. -/
theorem isSmoothlySlice_congr_lift_of_deriv_neg (hper : ∀ x, F (x + 2 * π) = F x - 2 * π)
    (hF : ContDiff ℝ ∞ F) (hneg : ∀ x, deriv F x < 0)
    (hσ : ∀ x, σ (Circle.exp x) = Circle.exp (F x)) (hK' : ∀ z, K' z = K (σ z)) :
    IsSmoothlySlice K' ↔ IsSmoothlySlice K := by
  obtain ⟨hper', hpos, hσ'⟩ := neg_lift hper hneg hσ
  rw [← isSmoothlySlice_reverse_iff (K := K)]
  exact isSmoothlySlice_congr_lift (σ := fun z ↦ (σ z)⁻¹) hper' hF.neg hpos hσ'
    fun z ↦ by simp [hK']

/-- **Topological sliceness does not depend on the parametrization, orientation-reversing case.**
If `σ` is a diffeomorphism of the circle with a lift `F` satisfying `F (x + 2π) = F x - 2π` and
`F' < 0`, then `K ∘ σ` is topologically slice exactly when `K` is. -/
theorem isTopologicallySlice_congr_lift_of_deriv_neg (hper : ∀ x, F (x + 2 * π) = F x - 2 * π)
    (hF : ContDiff ℝ ∞ F) (hneg : ∀ x, deriv F x < 0)
    (hσ : ∀ x, σ (Circle.exp x) = Circle.exp (F x)) (hK' : ∀ z, K' z = K (σ z)) :
    IsTopologicallySlice K' ↔ IsTopologicallySlice K := by
  obtain ⟨hper', hpos, hσ'⟩ := neg_lift hper hneg hσ
  rw [← isTopologicallySlice_reverse_iff (K := K)]
  exact isTopologicallySlice_congr_lift (σ := fun z ↦ (σ z)⁻¹) hper' hF.neg hpos hσ'
    fun z ↦ by simp [hK']

end TauCeti
