/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.Node.LocalNormalForm
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.GeometricallyReduced
import TauCeti.AlgebraicGeometry.Morphisms.Flat.Reduced
import TauCeti.RingTheory.Node.Reduced

/-!
# Nodal curves have geometrically reduced fibres

A nodal relative curve over a reduced base is reduced. On the smooth locus this follows
from smoothness. At every remaining point, an étale neighbourhood maps étale to a standard
node `xy = a`; these charts are reduced over a reduced base, and reducedness descends to the
original stalk by faithful flatness. Base change to fields then shows that a nodal relative
curve over an arbitrary base has geometrically reduced fibres.

The standard node is geometrically reduced over any base ring. The general nodal result
requires no Noetherian or perfectness assumption on the base. Reducedness is needed when
passing from a nodal curve to its normalization and conductor sequence.

## References

* The Stacks Project, Section 53.20, *Families of nodal curves*, Tag 0C58.
* The Stacks Project, Section 53.19, *Nodal curves*, Tag 0C46.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry

private theorem isReduced_of_nodal_toSpec {R : Type u} [CommRing R] [_root_.IsReduced R]
    {X : Scheme.{u}} {f : X ⟶ Spec (.of R)}
    (h : AtWorstNodalOfRelativeDimensionOne f) : IsReduced X := by
  let _ : X.Over (Spec (.of R)) := ⟨f⟩
  have : SyntomicOfRelativeDimension 1 f := h.syntomic
  have (x : X) : _root_.IsReduced (X.presheaf.stalk x) := by
    by_cases hx : x ∈ f.smoothLocus
    · have : IsReduced (f.smoothLocus : Scheme) :=
        (f.smoothLocus.ι ≫ f).isReduced_of_smooth
      -- Stalk instance synthesis does not recover the smooth-locus scheme argument here.
      have := isReduced_stalk_of_isReduced (f.smoothLocus : Scheme) ⟨x, hx⟩
      exact f.smoothLocus.ι.isReduced_stalk_of_flat ⟨x, hx⟩
    · obtain ⟨R', _, _, _, T, _, a, g, ψ, y, hg, hψ, hy, -⟩ :=
        X.exists_etale_nodeAlgebra (R := R) h hx
      have : _root_.IsReduced R' := TauCeti.isReduced_of_smooth R R'
      have : IsReduced (Spec (.of T)) := ψ.isReduced_of_smooth
      exact hy ▸ g.isReduced_stalk_of_flat y
  exact isReduced_of_isReduced_stalk X

/-- A nodal relative curve over a reduced base is reduced. -/
theorem AtWorstNodalOfRelativeDimensionOne.isReduced
    {X Y : Scheme.{u}} [IsReduced Y] {f : X ⟶ Y}
    (h : AtWorstNodalOfRelativeDimensionOne f) : IsReduced X := by
  have hred (i : Y.affineCover.I₀) : IsReduced ((Y.affineCover.pullback₁ f).X i) := by
    have hi : AtWorstNodalOfRelativeDimensionOne (Y.affineCover.pullbackHom f i) :=
      MorphismProperty.pullback_snd _ _ h
    exact isReduced_of_nodal_toSpec (R := Γ(Y.affineCover.X i, ⊤))
      (f := Y.affineCover.pullbackHom f i ≫ (Y.affineCover.X i).isoSpec.hom)
      ((MorphismProperty.cancel_right_of_respectsIso
        (P := AtWorstNodalOfRelativeDimensionOne) _ _).mpr hi)
  exact @IsReduced.of_openCover X (Y.affineCover.pullback₁ f) hred

/-- A nodal relative curve has geometrically reduced fibres. -/
theorem AtWorstNodalOfRelativeDimensionOne.geometricallyReduced
    {X Y : Scheme.{u}} {f : X ⟶ Y} (h : AtWorstNodalOfRelativeDimensionOne f) :
    GeometricallyReduced f := by
  constructor
  intro K _ s Z fst snd H
  exact (MorphismProperty.of_isPullback H h).isReduced

end TauCeti.AlgebraicGeometry

namespace TauCeti.NodeAlgebra

/-- The standard node smoothing has geometrically reduced fibres over any coefficient ring. -/
instance geometricallyReduced_spec {R : Type u} [CommRing R] (a : R) :
    GeometricallyReduced (Spec.algebraMap R (NodeAlgebra R a)) :=
  (atWorstNodalOfRelativeDimensionOne a).geometricallyReduced

end TauCeti.NodeAlgebra
