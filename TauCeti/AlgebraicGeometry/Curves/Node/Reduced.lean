/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.Node.LocalNormalForm
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.GeometricallyReduced
import TauCeti.AlgebraicGeometry.Curves.Node.Basic
import TauCeti.AlgebraicGeometry.Morphisms.Flat.Reduced
import TauCeti.RingTheory.Node.Reduced

/-!
# Nodal curves have geometrically reduced fibres

The scheme-theoretic nodal criterion implies that every geometric fibre is reduced. On the
smooth locus this follows from smoothness. At every remaining point, an étale neighbourhood
maps étale to a standard node `xy = a`; these charts are reduced over a field, and reducedness
descends to the original stalk by faithful flatness.

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

/-- A nodal relative curve over a field is reduced. -/
theorem AtWorstNodalOfRelativeDimensionOne.isReduced_of_field {K : Type u} [Field K]
    {X : Scheme.{u}} {f : X ⟶ Spec (.of K)}
    (h : AtWorstNodalOfRelativeDimensionOne f) : IsReduced X := by
  let _ : X.Over (Spec (.of K)) := ⟨f⟩
  have : SyntomicOfRelativeDimension 1 f := h.syntomic
  have (x : X) : _root_.IsReduced (X.presheaf.stalk x) := by
    by_cases hx : x ∈ f.smoothLocus
    · have : IsReduced (f.smoothLocus : Scheme) :=
        GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian (f.smoothLocus.ι ≫ f)
      -- Stalk instance synthesis does not recover the smooth-locus scheme argument here.
      have := isReduced_stalk_of_isReduced (f.smoothLocus : Scheme) ⟨x, hx⟩
      exact f.smoothLocus.ι.isReduced_stalk_of_flat ⟨x, hx⟩
    · obtain ⟨R', _, _, _, T, _, a, g, ψ, y, hg, hψ, hy, -⟩ :=
        X.exists_etale_nodeAlgebra (R := K) h hx
      have : Etale (Spec.algebraMap K R') :=
        (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
          (RingHom.etale_algebraMap.mpr inferInstance)
      have : IsLocallyNoetherian (Spec (.of R')) :=
        LocallyOfFiniteType.isLocallyNoetherian (Spec.algebraMap K R')
      have : _root_.IsReduced R' := TauCeti.isReduced_of_smooth K R'
      have : IsReduced (Spec (.of (NodeAlgebra R' a))) := inferInstance
      have : IsLocallyNoetherian (Spec (.of (NodeAlgebra R' a))) :=
        LocallyOfFiniteType.isLocallyNoetherian (Spec.algebraMap R' (NodeAlgebra R' a))
      have : IsReduced (Spec (.of T)) :=
        GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian ψ
      exact hy ▸ g.isReduced_stalk_of_flat y
  exact isReduced_of_isReduced_stalk X

/-- A nodal relative curve has geometrically reduced fibres. -/
theorem AtWorstNodalOfRelativeDimensionOne.geometricallyReduced
    {X Y : Scheme.{u}} {f : X ⟶ Y} (h : AtWorstNodalOfRelativeDimensionOne f) :
    GeometricallyReduced f := by
  constructor
  intro K _ s Z fst snd H
  exact (MorphismProperty.of_isPullback H h).isReduced_of_field

end TauCeti.AlgebraicGeometry

namespace TauCeti.NodeAlgebra

/-- The standard node smoothing has geometrically reduced fibres over any coefficient ring. -/
instance geometricallyReduced_spec {R : Type u} [CommRing R] (a : R) :
    GeometricallyReduced (Spec.algebraMap R (NodeAlgebra R a)) :=
  (atWorstNodalOfRelativeDimensionOne a).geometricallyReduced

end TauCeti.NodeAlgebra
