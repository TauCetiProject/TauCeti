/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Orientation.OpenSubset
public import TauCeti.Geometry.Manifold.Orientation.Torus

/-!
# Orientations on open subsets of circles and tori

An open subset `U` of the circle `AddCircle p` or of a torus `∀ i, AddCircle (p i)` is a manifold
with the charts restricted from the ambient manifold, and the orientations restrict to `U` by
`TauCeti.Manifold.Orientation.restrict`. This file shows that these restrictions keep the laws of
the ambient orientations, for every open subset, including those that are not products of open
subsets of the factors.

* **The oriented atlas.** The coordinate changes of the circle are translations, so the atlas of
  `U`, made of the restricted local real lifts, is oriented, and its orientation is the restriction
  of the positive orientation of the circle
  (`AddCircle.restrict_orientation_eq_isOrientedAtlas_orientation`).
* **Restricted maps.** Let `A` be one of the maps between these manifolds and `f : U → V` its
  restriction to open subsets, `Subtype.val ∘ f = A ∘ Subtype.val`. Then `f` preserves or reverses
  the restricted orientations as `A` does
  (`TauCeti.Manifold.Orientation.isOrientationPreservingAt_restrict_iff_of_comp_eq`). This is
  recorded for the rescalings of circles and tori and for the reindexings of tori with their
  permutation sign. The corresponding time-form laws are in
  `TauCeti.Geometry.Manifold.DifferentialForm.Torus.Opens`.

Successive restrictions to open subsets `U ≤ W` are compatible
(`TauCeti.Manifold.Orientation.isOrientationPreservingAt_restrict_inclusion`), and restriction
commutes with products of orientations
(`TauCeti.Manifold.Orientation.isOrientationPreservingAt_prod_restrict_of_comp_eq`).

## Main results

* `AddCircle.restrict_orientation_eq_isOrientedAtlas_orientation`: the restricted orientation of
  the circle is the orientation of the oriented atlas of the open subset.
* `AddCircle.isOrientationPreservingAt_restrict_of_comp_eq_diffeomorphAddCircle`: restricted
  rescalings of circles.
* `TauCeti.orientationSign_restrict_torusOrientation_of_comp_eq_reindex`: restricted reindexings
  of tori.
* `TauCeti.isOrientationPreservingAt_restrict_torusOrientation_of_comp_eq_piMap`: restricted
  rescalings of tori.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapter 15 (restriction of orientations to open
  submanifolds).
-/

public section

noncomputable section

open TopologicalSpace TauCeti TauCeti.Manifold.Orientation
open scoped Manifold ContDiff

namespace AddCircle

variable {p q : ℝ} [Fact (0 < p)] [Fact (0 < q)]

variable (p) in
/-- **The oriented atlas of an open subset of a circle.** The charts of an open subset `U` of
`AddCircle p` are the restricted local real lifts, whose coordinate changes are translations. The
orientation of this oriented atlas, in which `1` is positive, is the restriction to `U` of the
positive orientation of the circle. -/
theorem restrict_orientation_eq_isOrientedAtlas_orientation {n : ℕ∞ω} [NeZero n]
    (U : Opens (AddCircle p)) :
    (AddCircle.orientation p).restrict U =
      (isOrientedAtlas_atlas 𝓘(ℝ) n U).orientation
        (Module.Basis.singleton (Fin 1) ℝ).orientation (by simp) := by
  rw [orientation_eq_isOrientedAtlas_orientation p (n := n), restrict_isOrientedAtlas_orientation]

/-- A restriction `f : U → V` of the rescaling `AddCircle p ≃ AddCircle q` to open subsets
preserves the restricted positive orientations. -/
theorem isOrientationPreservingAt_restrict_of_comp_eq_diffeomorphAddCircle {n : ℕ∞ω}
    {U : Opens (AddCircle p)} {V : Opens (AddCircle q)} {f : U → V}
    (hf : Subtype.val ∘ f = diffeomorphAddCircle p q n ∘ Subtype.val) (x : U) :
    IsOrientationPreservingAt ((AddCircle.orientation p).restrict U)
      ((AddCircle.orientation q).restrict V) f x :=
  (isOrientationPreservingAt_restrict_iff_of_comp_eq hf _ _ x).mpr
    (isOrientationPreservingAt_diffeomorphAddCircle p q n x)

end AddCircle

namespace TauCeti

/-! ### Tori -/

section Torus

/-- **The permutation sign law on open subsets.** A restriction `f : U → V` of the reordering
`x ↦ (j ↦ x (σ j))` of the factors of a torus to open subsets has orientation sign `sign σ`, for
the restricted torus orientations, at every point. -/
theorem orientationSign_restrict_torusOrientation_of_comp_eq_reindex {n : ℕ} (p : Fin n → ℝ)
    [∀ i, Fact (0 < p i)] (σ : Equiv.Perm (Fin n)) {U : Opens (∀ i, AddCircle (p i))}
    {V : Opens (∀ j, AddCircle (p (σ j)))} {f : U → V}
    (hf : Subtype.val ∘ f = (fun (x : ∀ i, AddCircle (p i)) (j : Fin n) ↦ x (σ j)) ∘ Subtype.val)
    (x : U) :
    orientationSign ((torusOrientation p).restrict U)
      ((torusOrientation fun j ↦ p (σ j)).restrict V) f x = Equiv.Perm.sign σ := by
  rw [orientationSign_restrict_of_comp_eq hf, orientationSign_torusOrientation_reindex]

/-- A restriction `f : U → V` of the diagonal rescaling of the periods of a torus to open subsets
preserves the restricted torus orientations. -/
theorem isOrientationPreservingAt_restrict_torusOrientation_of_comp_eq_piMap {n : ℕ}
    (p q : Fin n → ℝ) [∀ i, Fact (0 < p i)] [∀ i, Fact (0 < q i)]
    {U : Opens (∀ i, AddCircle (p i))} {V : Opens (∀ i, AddCircle (q i))} {f : U → V}
    (hf : Subtype.val ∘ f =
      (Pi.map fun j ↦ AddCircle.diffeomorphAddCircle (p j) (q j) ∞) ∘ Subtype.val) (x : U) :
    IsOrientationPreservingAt ((torusOrientation p).restrict U) ((torusOrientation q).restrict V)
      f x :=
  (isOrientationPreservingAt_restrict_iff_of_comp_eq hf _ _ x).mpr
    (isOrientationPreservingAt_piMap_diffeomorphAddCircle p q x)

end Torus

end TauCeti
