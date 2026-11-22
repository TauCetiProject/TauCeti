/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.GroupAction.ActionGroupoid.LieGroupoid
public import TauCeti.Geometry.Manifold.Groupoid.Examples
public import TauCeti.Geometry.Manifold.Groupoid.Prod
public import TauCeti.Topology.CategoryTheory.Etale
import TauCeti.Topology.Algebra.ProperAction.Basic

/-!
# Hausdorff proper étale Lie groupoids

`TauCeti.IsProperEtaleGroupoid I J C` singles out, among the Lie groupoids
`TauCeti.IsLieGroupoid I J C`, the groupoids presenting orbifolds: the total-arrow manifold is
Hausdorff, the source map `Quiver.Total.left` is a smooth local diffeomorphism (the groupoid is
étale), and the source-target map `a ↦ (a.left, a.right)` is proper in the sense of Mathlib's
`IsProperMap`. Object and arrow manifolds are then Hausdorff and second countable, modelled on the
fixed models `I` and `J`, which have the same dimension as soon as there is an object.

The class bundles the hypotheses under which the finite-chart theory of
`TauCeti.Topology.CategoryTheory.Etale` and `TauCeti.Geometry.Manifold.Etale.Basic` applies. From
it this file derives:

* the target map is also a smooth local diffeomorphism
  (`TauCeti.IsProperEtaleGroupoid.isLocalDiffeomorph_target`), and source and target are local
  homeomorphisms;
* on a nonempty object manifold, the arrow and object models have the same dimension
  (`TauCeti.IsProperEtaleGroupoid.finrank_eq`);
* there are finitely many arrows between any two objects, so every isotropy group is finite
  (`TauCeti.IsProperEtaleGroupoid.finite_hom`, `TauCeti.IsProperEtaleGroupoid.finite_aut`);
* the identity arrows form a clopen subset of the arrows
  (`TauCeti.IsProperEtaleGroupoid.isClopen_range_unit`);
* the product of two proper étale Lie groupoids is a proper étale Lie groupoid
  (`TauCeti.IsProperEtaleGroupoid.prod`), for the product Lie groupoid structure
  `TauCeti.IsLieGroupoid.prod`.

The class is a property of the native categorical groupoid with its given smooth structures: it
retains every arrow, including isotropy arrows acting trivially on objects, and introduces no
second groupoid carrier.

## Examples

* The unit groupoid `Discrete M` of a Hausdorff second-countable manifold
  (`TauCeti.UnitGroupoid.isProperEtaleGroupoid`).
* The action groupoid `ActionCategory G X` of a countable discrete group acting properly by smooth
  maps on a second-countable manifold (`TauCeti.ActionGroupoid.isProperEtaleGroupoid`), in
  particular of every finite group acting by smooth maps on a Hausdorff second-countable manifold
  (`TauCeti.ActionGroupoid.isProperEtaleGroupoid_of_finite`). These are the global quotient
  presentations `[X/G]`, with isotropy the full stabilizers, including the elements acting
  trivially on `X`.

## References

* I. Moerdijk, *Orbifolds as groupoids: an introduction*, Section 2.
* A. Adem, J. Leida and Y. Ruan, *Orbifolds and stringy topology*, Chapter 1.
-/

public section

open CategoryTheory Module Topology
open scoped Manifold ContDiff

namespace TauCeti

/-- A **Hausdorff proper étale Lie groupoid**: a Lie groupoid whose total-arrow manifold is
Hausdorff, whose source map is a smooth local diffeomorphism, and whose source-target map
`a ↦ (a.left, a.right)` is proper. These are the groupoids presenting orbifolds, with every arrow
retained. -/
class IsProperEtaleGroupoid {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [I.Boundaryless] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [FiniteDimensional ℝ E'] {H' : Type*} [TopologicalSpace H'] (J : ModelWithCorners ℝ E' H')
    [J.Boundaryless] (C : Type*) [Category C] [IsGroupoid C]
    [TopologicalSpace C] [ChartedSpace H C] [IsManifold I ∞ C]
    [TopologicalSpace (Quiver.Total C)] [ChartedSpace H' (Quiver.Total C)]
    [IsManifold J ∞ (Quiver.Total C)] : Prop extends IsLieGroupoid I J C where
  /-- The total-arrow manifold is Hausdorff. -/
  t2Space_arrows : T2Space (Quiver.Total C) := by infer_instance
  /-- The source map is a smooth local diffeomorphism. -/
  isLocalDiffeomorph_source :
    IsLocalDiffeomorph J I ∞ (Quiver.Total.left : Quiver.Total C → C)
  /-- The source-target map is proper. -/
  isProperMap_source_target : IsProperMap fun a : Quiver.Total C ↦ (a.left, a.right)

namespace IsProperEtaleGroupoid

variable {E H E' H' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) [I.Boundaryless]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [TopologicalSpace H']
  (J : ModelWithCorners ℝ E' H') [J.Boundaryless]
  {C : Type*} [Category C] [IsGroupoid C]
  [TopologicalSpace C] [ChartedSpace H C] [IsManifold I ∞ C]
  [TopologicalSpace (Quiver.Total C)] [ChartedSpace H' (Quiver.Total C)]
  [IsManifold J ∞ (Quiver.Total C)]
  [IsProperEtaleGroupoid I J C]

/-- The target map of a proper étale Lie groupoid is a smooth local diffeomorphism. -/
theorem isLocalDiffeomorph_target :
    IsLocalDiffeomorph J I ∞ (Quiver.Total.right : Quiver.Total C → C) :=
  (IsLieGroupoid.isLocalDiffeomorph_source_iff_target I J C).1 isLocalDiffeomorph_source

include I J in
/-- The source map of a proper étale Lie groupoid is a local homeomorphism. -/
theorem isLocalHomeomorph_source :
    IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C) :=
  (isLocalDiffeomorph_source (I := I) (J := J)).isLocalHomeomorph

include I J in
/-- The target map of a proper étale Lie groupoid is a local homeomorphism. -/
theorem isLocalHomeomorph_target :
    IsLocalHomeomorph (Quiver.Total.right : Quiver.Total C → C) :=
  (isLocalDiffeomorph_target I J).isLocalHomeomorph

include I J in
/-- On a nonempty object manifold, the arrow and object models of a proper étale Lie groupoid have
the same dimension. -/
theorem finrank_eq [Nonempty C] : finrank ℝ E' = finrank ℝ E :=
  (IsLieGroupoid.isLocalDiffeomorph_source_iff_finrank_eq I J C).1 isLocalDiffeomorph_source

include I J in
/-- A proper étale Lie groupoid has finitely many arrows between any two objects. -/
theorem finite_hom (x y : C) : Finite (x ⟶ y) :=
  finite_hom_of_proper_source_target (isProperMap_source_target (I := I) (J := J))
    (isLocalHomeomorph_source I J) x y

include I J in
/-- Every isotropy group of a proper étale Lie groupoid is finite. -/
theorem finite_aut (x : C) : Finite (Aut x) :=
  finite_aut_of_proper_source_target (isProperMap_source_target (I := I) (J := J))
    (isLocalHomeomorph_source I J) x

include I J in
/-- The identity arrows of a proper étale Lie groupoid form a clopen subset of the arrows. -/
theorem isClopen_range_unit :
    IsClopen (Set.range fun x : C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total C)) :=
  have := t2Space_arrows (I := I) (J := J) (C := C)
  TauCeti.isClopen_range_unit (IsLieGroupoid.contMDiff_unit (I := I) (J := J)).continuous
    (isLocalHomeomorph_source I J)

end IsProperEtaleGroupoid

/-! ### Products -/

namespace IsProperEtaleGroupoid

variable {E H E' H' F G F' G' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [J.Boundaryless]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [TopologicalSpace G]
  {I' : ModelWithCorners ℝ F G} [I'.Boundaryless]
  [NormedAddCommGroup F'] [NormedSpace ℝ F'] [FiniteDimensional ℝ F'] [TopologicalSpace G']
  {J' : ModelWithCorners ℝ F' G'} [J'.Boundaryless]
  {C : Type*} [Category C] [IsGroupoid C]
  [TopologicalSpace C] [ChartedSpace H C] [IsManifold I ∞ C]
  [TopologicalSpace (Quiver.Total C)] [ChartedSpace H' (Quiver.Total C)]
  [IsManifold J ∞ (Quiver.Total C)] [IsProperEtaleGroupoid I J C]
  {D : Type*} [Category D] [IsGroupoid D]
  [TopologicalSpace D] [ChartedSpace G D] [IsManifold I' ∞ D]
  [TopologicalSpace (Quiver.Total D)] [ChartedSpace G' (Quiver.Total D)]
  [IsManifold J' ∞ (Quiver.Total D)] [IsProperEtaleGroupoid I' J' D]

/-- **The product of two proper étale Lie groupoids is a proper étale Lie groupoid**, with the
product Lie groupoid structure `TauCeti.IsLieGroupoid.prod`. -/
instance prod : IsProperEtaleGroupoid (I.prod I') (J.prod J') (C × D) where
  t2Space_arrows :=
    have := t2Space_arrows (I := I) (J := J) (C := C)
    have := t2Space_arrows (I := I') (J := J') (C := D)
    inferInstance
  isLocalDiffeomorph_source := by
    -- The source of a product is `Prod.map` of the sources, read through `totalProdDiffeomorph`.
    have h : (Quiver.Total.left : Quiver.Total (C × D) → C × D) =
        Prod.map Quiver.Total.left Quiver.Total.left ∘ totalProdDiffeomorph C D J J' ∞ :=
      funext fun _ ↦ by simp
    rw [h]
    exact fun a ↦ ((totalProdDiffeomorph C D J J' ∞).isLocalDiffeomorph a).comp (I.prod I') (C × D)
      ((isLocalDiffeomorph_source (I := I) (J := J) (C := C)).prodMap
        (isLocalDiffeomorph_source (I := I') (J := J') (C := D)) _)
  isProperMap_source_target :=
    isProperMap_source_target_prod (isProperMap_source_target (I := I) (J := J))
      (isProperMap_source_target (I := I') (J := J'))

end IsProperEtaleGroupoid

/-! ### Examples -/

namespace UnitGroupoid

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SecondCountableTopology M]

/-- The unit groupoid of a Hausdorff second-countable smooth manifold is a proper étale Lie
groupoid. -/
instance isProperEtaleGroupoid : IsProperEtaleGroupoid I I (Discrete M) where
  isLocalDiffeomorph_source := isLocalDiffeomorph_source
  isProperMap_source_target := isProperMap_source_target M

end UnitGroupoid

namespace ActionGroupoid

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
  (G X : Type*) [Group G] [TopologicalSpace G] [DiscreteTopology G] [Countable G]
  [MulAction G X] [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
  [ContMDiffConstSMul I ∞ G X] [T2Space X] [SecondCountableTopology X]

omit [T2Space X] in
/-- The action groupoid of a countable discrete group acting properly by smooth maps on a
second-countable smooth manifold is a proper étale Lie groupoid. The manifold is Hausdorff because
the action is proper. -/
instance isProperEtaleGroupoid [ProperSMul G X] : IsProperEtaleGroupoid I I (ActionCategory G X) :=
  have := t2Space_of_properSMul_of_t1Group (G := G) (X := X)
  { isLocalDiffeomorph_source := isLocalDiffeomorph_source I ∞ G X
    isProperMap_source_target := (isProperMap_source_target_iff G X).2 ‹_› }

omit [Countable G] in
/-- The action groupoid `[X/G]` of a finite group acting by smooth maps on a Hausdorff
second-countable smooth manifold is a proper étale Lie groupoid. -/
instance isProperEtaleGroupoid_of_finite [Finite G] :
    IsProperEtaleGroupoid I I (ActionCategory G X) :=
  -- A discrete group acting by continuous maps acts continuously, and a continuous action of a
  -- finite group on a Hausdorff space is proper.
  have := ContMDiffConstSMul.continuousConstSMul (I := I) ∞ (Γ := G) (M := X)
  have : ContinuousSMul G X := ⟨continuous_prod_of_discrete_left.mpr continuous_const_smul⟩
  have := properSMul_of_compactSpace G X
  isProperEtaleGroupoid I G X

end ActionGroupoid

end TauCeti
