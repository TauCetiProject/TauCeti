/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.TopForm
public import TauCeti.Geometry.Manifold.Orientation.Cover.Descent
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.ChangeOfVariables

/-!
# Integration of top forms on the orientation double cover

Let `π : M' → M` be the orientation double cover of a manifold `M`, and `τ` its deck involution,
which reverses the canonical orientation of `M'`. By the change of variables formula, the
integral of a `τ`-invariant top form on `M'` equals its own negative, so it vanishes. Pullbacks
along `π` are `τ`-invariant, so `∫_{M'} π^*φ = 0` for every top form `φ` on `M`.

## Main results

* `TauCeti.Manifold.OrientationCover.integralTopForm_eq_zero_of_mpullback_deck_eq`: a
  deck-invariant top form on the cover has integral zero.
* `TauCeti.Manifold.OrientationCover.integralTopForm_mpullback_proj_eq_zero`: the pullback of a
  top form on `M` to the cover has integral zero.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, proof of Theorem 17.34.
-/

public section

noncomputable section

open Set
open scoped Manifold

namespace TauCeti.Manifold.OrientationCover

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]

/-- A top form on the orientation double cover that is invariant under the deck involution has
integral zero for the canonical orientation, since the deck involution reverses it. -/
theorem integralTopForm_eq_zero_of_mpullback_deck_eq
    {φ : RoughForm I (OrientationCover I M) ℝ (Module.finrank ℝ E)}
    (hφ : mpullback I I VectorBundleOrientationCover.deck φ = φ) :
    integralTopForm canonicalOrientation φ = 0 := by
  have h := VectorBundleOrientationCover.deck.isOpenEmbedding
    |>.integralTopForm_mpullback_of_isOrientationReversingAt isOrientationReversingAt_deck
      (φ := φ) (by rw [VectorBundleOrientationCover.deck.range_coe]; exact subset_univ _)
  rw [hφ] at h
  linarith

/-- The pullback of every top form on `M` to the orientation double cover has integral zero for
the canonical orientation. -/
@[simp]
theorem integralTopForm_mpullback_proj_eq_zero (φ : RoughForm I M ℝ (Module.finrank ℝ E)) :
    integralTopForm canonicalOrientation (mpullback I I VectorBundleOrientationCover.proj φ) = 0 :=
  integralTopForm_eq_zero_of_mpullback_deck_eq (exists_mpullback_proj_eq_iff.mp ⟨φ, rfl⟩)

end TauCeti.Manifold.OrientationCover
