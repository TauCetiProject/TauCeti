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
import TauCeti.RingTheory.Node.BaseChange

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
open scoped TensorProduct

universe u

namespace TauCeti.NodeAlgebra

/-- The standard node smoothing has geometrically reduced fibres over any coefficient ring. -/
instance geometricallyReduced_spec {R : Type u} [CommRing R] (a : R) :
    GeometricallyReduced (Spec.algebraMap R (NodeAlgebra R a)) := by
  rw [GeometricallyReduced.eq_geometrically,
    geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  intro K _ _
  have : _root_.IsReduced (K ⊗[R] NodeAlgebra R a) :=
    isReduced_of_injective (baseChange a) (baseChange a).injective
  have : _root_.IsReduced (NodeAlgebra R a ⊗[R] K) :=
    isReduced_of_injective (Algebra.TensorProduct.comm R (NodeAlgebra R a) K)
      (Algebra.TensorProduct.comm R (NodeAlgebra R a) K).injective
  exact isReduced_of_isOpenImmersion (pullbackSpecIso R (NodeAlgebra R a) K).hom

end TauCeti.NodeAlgebra

namespace TauCeti.AlgebraicGeometry

private theorem isReduced_of_nodal_toSpec_field {K : Type u} [Field K]
    (X : Scheme.{u}) [X.Over (Spec (.of K))]
    (h : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of K))) : IsReduced X := by
  have : SyntomicOfRelativeDimension 1 (X ↘ Spec (.of K)) := h.syntomic
  have : LocallyOfFinitePresentation (X ↘ Spec (.of K)) :=
    SyntomicOfRelativeDimension.locallyOfFinitePresentation 1 _
  have (x : X) : _root_.IsReduced (X.presheaf.stalk x) := by
    by_cases hx : x ∈ (X ↘ Spec (.of K)).smoothLocus
    · let U := (X ↘ Spec (.of K)).smoothLocus
      have : Smooth (U.ι ≫ (X ↘ Spec (.of K))) := by
        rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq]
        simp [U]
      have : IsReduced U.toScheme :=
        GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian
          (U.ι ≫ (X ↘ Spec (.of K)))
      let y : U.toScheme := ⟨x, hx⟩
      have : _root_.IsReduced (U.toScheme.presheaf.stalk y) :=
        isReduced_stalk_of_isReduced U.toScheme y
      exact U.ι.isReduced_stalk_of_flat y
    · obtain ⟨R', _, _, _, T, _, a, g, ψ, y, hg, hψ, hy, -⟩ :=
        X.exists_etale_nodeAlgebra h hx
      have : Etale (Spec.algebraMap K R') :=
        (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
          (RingHom.etale_algebraMap.mpr inferInstance)
      have : IsLocallyNoetherian (Spec (.of R')) :=
        LocallyOfFiniteType.isLocallyNoetherian (Spec.algebraMap K R')
      have : IsReduced (Spec (.of R')) :=
        GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian (Spec.algebraMap K R')
      have : IsReduced (Spec (.of (NodeAlgebra R' a))) :=
        GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian
          (Spec.algebraMap R' (NodeAlgebra R' a))
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
  let _ : Z.Over (Spec (.of K)) := ⟨snd⟩
  exact isReduced_of_nodal_toSpec_field (K := K) Z (MorphismProperty.of_isPullback H h)

end TauCeti.AlgebraicGeometry
