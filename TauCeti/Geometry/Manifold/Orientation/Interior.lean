/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Interior.Inclusion
public import TauCeti.Geometry.Manifold.Orientation.Pullback

/-!
# Orientations of the interior of a manifold with corners

An orientation `o` of a `C¹` manifold with corners `M`, modelled on a finite-dimensional real space
`E`, restricts to its interior `I.interior M`, the manifold without boundary modelled on `E`
(`ModelWithCorners.instChartedSpaceInterior`). The inclusion of the interior is smooth with the
identity of `E` as its manifold derivative (`ModelWithCorners.mfderiv_subtypeVal_interior`), so
the restricted orientation `o.manifoldInterior` is the pullback of `o` along it
(`TauCeti.Manifold.Orientation.pullback`), and its tangent orientation at every point is the
tangent orientation of `o` at the same point of `M`
(`TauCeti.Manifold.Orientation.orientationAt_manifoldInterior`).

## Main definitions

* `TauCeti.Manifold.Orientation.manifoldInterior`: the orientation of the interior induced by an
  orientation of `M`.

## Main results

* `TauCeti.Manifold.Orientation.orientationAt_manifoldInterior`: its tangent orientations are
  those of `M`.
* `TauCeti.Manifold.Orientation.isOrientationPreservingAt_manifoldInterior`: the inclusion of the
  interior preserves orientation.
* `TauCeti.Manifold.Orientation.eq_manifoldInterior_iff`,
  `TauCeti.Manifold.Orientation.eq_manifoldInterior_iff_isOrientationPreservingAt`: it is the only
  orientation of the interior with these tangent orientations, and the only one from which the
  inclusion preserves orientation.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Springer GTM 218 (2013),
  Proposition 15.15 (pullback orientations).
-/

public noncomputable section

open scoped Manifold

namespace TauCeti.Manifold.Orientation

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] {ι : Type*} [Fintype ι]

/-- The **orientation of the interior** of an oriented manifold with corners: the pullback of `o`
along the inclusion of the interior, whose tangent orientation at every point is that of `o`. -/
def manifoldInterior (o : Orientation I M ι) : Orientation 𝓘(ℝ, E) (I.interior M) ι :=
  o.pullback (I.contMDiff_subtypeVal_interior (M := M) (n := 1))
    ((I.isLocalDiffeomorph_subtypeVal_interior M 1).isInvertible_mfderiv one_ne_zero) o.card_eq

/-- The tangent orientation of the interior at `x` is the tangent orientation of `M` at `x`. -/
@[simp]
theorem orientationAt_manifoldInterior (o : Orientation I M ι) (x : I.interior M) :
    o.manifoldInterior.orientationAt x = o.orientationAt (x : M) := by
  have h := map_orientationAt_pullback o (I.contMDiff_subtypeVal_interior (M := M) (n := 1))
    ((I.isLocalDiffeomorph_subtypeVal_interior M 1).isInvertible_mfderiv one_ne_zero) o.card_eq x
    (ContinuousLinearEquiv.refl ℝ E)
    (ModelWithCorners.mfderiv_subtypeVal_interior x).symm
  have hrefl : (ContinuousLinearEquiv.refl ℝ E).toLinearEquiv = LinearEquiv.refl ℝ E :=
    LinearEquiv.ext fun v ↦ by simp
  rw [hrefl] at h
  exact (Equiv.ext_iff.mp (_root_.Orientation.map_refl (R := ℝ) (M := E) ι) _).symm.trans h

/-- The inclusion of the interior preserves orientation. -/
@[simp]
theorem isOrientationPreservingAt_manifoldInterior (o : Orientation I M ι)
    (x : I.interior M) :
    IsOrientationPreservingAt o.manifoldInterior o Subtype.val x :=
  isOrientationPreservingAt_pullback o _ _ _ x

/-- The orientation of the interior induced by `o` is the only orientation of the interior whose
tangent orientations are those of `o`. -/
theorem eq_manifoldInterior_iff {o : Orientation I M ι}
    {o' : Orientation 𝓘(ℝ, E) (I.interior M) ι} :
    o' = o.manifoldInterior ↔ ∀ x, o'.orientationAt x = o.orientationAt (x : M) := by
  refine ⟨fun h x ↦ h ▸ orientationAt_manifoldInterior o x, fun h ↦ ext fun x ↦ ?_⟩
  rw [h x, orientationAt_manifoldInterior]

/-- The orientation of the interior induced by `o` is the only orientation of the interior from
which the inclusion preserves orientation at every point. -/
theorem eq_manifoldInterior_iff_isOrientationPreservingAt {o : Orientation I M ι}
    {o' : Orientation 𝓘(ℝ, E) (I.interior M) ι} :
    o' = o.manifoldInterior ↔ ∀ x, IsOrientationPreservingAt o' o Subtype.val x :=
  eq_pullback_iff o _ _ _

/-- The interior of the opposite orientation carries the opposite orientation. -/
@[simp]
theorem manifoldInterior_neg (o : Orientation I M ι) :
    (-o).manifoldInterior = -o.manifoldInterior :=
  pullback_neg o _ _ _

end TauCeti.Manifold.Orientation
