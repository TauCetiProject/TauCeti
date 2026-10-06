/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import TauCeti.AlgebraicGeometry.Modules.GlobalSections

/-!
# Standard smooth charts over an affine target

If `f : X ⟶ Y` is smooth of relative dimension `n` and `Y` is affine, then every point of `X`
has an affine open neighbourhood `W` on which the map `Γ(Y, ⊤) → Γ(X, W)` induced by `f` is
standard smooth of relative dimension `n`. The defining charts of `SmoothOfRelativeDimension n`
only provide this over some affine open of `Y`; shrinking them to basic opens and using that
standard smoothness is stable under localization away from an element brings the source of the
ring map up to all of `Y`.

## Main declarations

* `SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension_appLE_top`, in Mathlib's
  `AlgebraicGeometry` namespace: standard smooth charts whose ring map starts at the global
  sections of the affine target.

## References

The proof is adapted from Mathlib's proof of
`AlgebraicGeometry.SmoothOfRelativeDimension.smoothOfRelativeDimension_comp` in
`Mathlib.AlgebraicGeometry.Morphisms.Smooth` (Apache-2.0): the same shrinking of the charts to
basic opens via `exists_basicOpen_le_appLE_of_appLE_of_isAffine`, followed by composing with the
localization away from `r`, here taken from the global sections of the affine target rather
than from a chart of a second smooth morphism.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace RingHom

namespace AlgebraicGeometry.SmoothOfRelativeDimension

universe u

/-- If `f : X ⟶ Y` is smooth of relative dimension `n` and `Y` is affine, then around every point
of `X` there is an affine open `W` such that `Γ(Y, ⊤) → Γ(X, W)` is standard smooth of relative
dimension `n`. -/
theorem exists_isStandardSmoothOfRelativeDimension_appLE_top
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine Y] (n : ℕ) [SmoothOfRelativeDimension n f]
    (x : X) :
    ∃ W : X.affineOpens, x ∈ W.1 ∧ (f.appLE ⊤ W.1 le_top).hom.IsStandardSmoothOfRelativeDimension n
      := by
  obtain ⟨U, hU, V, hV, hx, e, hf⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := n) (f := f) x
  -- Shrink the charts to basic opens `D(r) ⊆ Y` and `D(s) ⊆ V`.
  obtain ⟨r, s, hxs, e₁, hf₁⟩ := exists_basicOpen_le_appLE_of_appLE_of_isAffine
    (isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway n).right
    (isStandardSmoothOfRelativeDimension_localizationPreserves n).away
    x ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ ⟨V, hV⟩ ⟨V, hV⟩ hx hx e hf (Opens.mem_top _)
  refine ⟨⟨X.basicOpen s, hV.basicOpen s⟩, hxs, ?_⟩
  -- Since `Γ(Y, D(r))` is the localization of `Γ(Y, ⊤)` away from `r`, the map out of `Γ(Y, ⊤)`
  -- is still standard smooth of relative dimension `n`.
  have : IsLocalization.Away r Γ(Y, Y.basicOpen r) :=
    (isAffineOpen_top _).isLocalization_basicOpen r
  have heq : f.appLE ⊤ (X.basicOpen s) le_top =
      CommRingCat.ofHom (algebraMap Γ(Y, ⊤) Γ(Y, Y.basicOpen r)) ≫ f.appLE _ _ e₁ := by
    rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom, Scheme.Hom.map_appLE]
  rw [heq, CommRingCat.hom_comp]
  exact (isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway n).left
    _ r _ hf₁

end AlgebraicGeometry.SmoothOfRelativeDimension

namespace TauCeti.AlgebraicGeometry

universe u

variable (R : Type u) [CommRing R] {X : Scheme.{u}} [X.Over (Spec (.of R))]

/-- Around every point of a scheme smooth of relative dimension `n` over `Spec R`, there is an
affine open whose ring of functions is standard smooth of relative dimension `n` over `R`. -/
lemma exists_isStandardSmoothOfRelativeDimension (n : ℕ)
    [SmoothOfRelativeDimension n (X ↘ Spec (.of R))] (x : X) :
    ∃ W : X.affineOpens, x ∈ W.1 ∧
      ((X.baseRingToStructurePresheaf R).app (op W.1)).hom.IsStandardSmoothOfRelativeDimension n
        := by
  obtain ⟨W, hxW, h⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension_appLE_top
      (X ↘ Spec (.of R)) n x
  refine ⟨W, hxW, ?_⟩
  rw [Scheme.baseRingToStructurePresheaf_app_eq_appLE, CommRingCat.hom_comp]
  exact (isStandardSmoothOfRelativeDimension_respectsIso (n := n)).right _
    (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv h

end TauCeti.AlgebraicGeometry
