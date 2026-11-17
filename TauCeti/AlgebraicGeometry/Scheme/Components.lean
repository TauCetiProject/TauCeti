/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Geometrically.Irreducible
public import TauCeti.AlgebraicGeometry.Noetherian
public import TauCeti.AlgebraicGeometry.Scheme.ConnectedComponent
import TauCeti.AlgebraicGeometry.IrreducibleOfConnectedDomainStalk
import TauCeti.AlgebraicGeometry.Morphisms.OpenImmersion
import TauCeti.AlgebraicGeometry.Restrict

/-!
# Irreducible components of locally Noetherian schemes with integral-domain stalks

On a locally Noetherian scheme `X` whose stalks are integral domains (in particular, any regular
scheme or locally Noetherian normal scheme), local Noetherianity makes the underlying topological
space locally connected while every open subscheme inherits local Noetherianity and integral-domain
stalks (`AlgebraicGeometry.Scheme.Hom.isDomain_stalk_iff_of_isIso_stalkMap`). Each connected
component `X.connectedComponentOpen x` is therefore an open-and-closed connected subscheme that is
irreducible by `TauCeti.AlgebraicGeometry.irreducibleSpace_of_connected_of_isDomain_stalk` and
reduced, hence integral
(`TauCeti.AlgebraicGeometry.isIntegral_connectedComponentOpen_of_isDomain_stalk`, applying
`TauCeti.AlgebraicGeometry.isIntegral_of_connected_of_isDomain_stalk`).
Consequently the irreducible components of `X` coincide with its connected components: they are
pairwise disjoint clopen subsets partitioning `X`, and each `v : irreducibleComponents X` carries a
canonical clopen integral subscheme structure (`TauCeti.AlgebraicGeometry.componentOpen`).

For base change along a geometrically irreducible universally open morphism `h : S' ⟶ S` (for
instance `Spec M ⟶ Spec K` over a separably closed field `K` for any `K`-algebra `M` with
irreducible spectrum, via `TauCeti.AlgebraicGeometry.geometricallyIrreducible_Spec_of_isSepClosed`),
the bijection on irreducible components holds unconditionally for arbitrary schemes `X` and
pullbacks `X'` (`TauCeti.AlgebraicGeometry.irreducibleComponentsEquivOfIsPullback` and
`TauCeti.AlgebraicGeometry.bijOn_preimage_irreducibleComponents_of_isSepClosed` in
`TauCeti.AlgebraicGeometry.Geometrically.Irreducible`, built on Mathlib's
`AlgebraicGeometry.Scheme.Hom.irreducibleComponentsEquiv`).

Under the additional hypotheses that **both** `X` and the pullback `X'` are locally Noetherian with
integral-domain stalks, the projection `g : X' ⟶ X` is compatible with `componentOf`
(`TauCeti.AlgebraicGeometry.componentOf_apply_of_isPullback`), pulls back each `componentOpen` of
`X` to the corresponding `componentOpen` of `X'`
(`TauCeti.AlgebraicGeometry.preimage_componentOpen_of_isPullback`), and identifies each component
open of `X'` as the base change of the corresponding component open of `X`
(`TauCeti.AlgebraicGeometry.exists_isPullback_componentOpen`).

## References

* [The Stacks Project, Tag 033N](https://stacks.math.columbia.edu/tag/033N) (Lemma 28.7.7): normal
  schemes with locally finite irreducible components, in particular locally Noetherian normal
  schemes, are disjoint unions of integral normal schemes (see also
  [Tag 033M](https://stacks.math.columbia.edu/tag/033M)).
* The Stacks Project, Chapter *Varieties*, Section *Geometrically irreducible schemes*
  ([Tag 037A](https://stacks.math.columbia.edu/tag/037A)).
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry

/-- Each connected component of a locally Noetherian scheme with integral-domain stalks, equipped
with its open-subscheme structure, is integral. -/
instance isIntegral_connectedComponentOpen_of_isDomain_stalk (X : Scheme.{u})
    [IsLocallyNoetherian X] [∀ x : X, IsDomain (X.presheaf.stalk x)] (x : X) :
    IsIntegral (X.connectedComponentOpen x).toScheme :=
  have : ∀ u : (X.connectedComponentOpen x).toScheme,
      IsDomain ((X.connectedComponentOpen x).toScheme.presheaf.stalk u) := fun u ↦
    ((X.connectedComponentOpen x).ι.isDomain_stalk_iff_of_isIso_stalkMap u).mp inferInstance
  isIntegral_of_connected_of_isDomain_stalk (X.connectedComponentOpen x).toScheme

section Components

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [∀ x : X, IsDomain (X.presheaf.stalk x)]

/-- Every connected component of a locally Noetherian scheme with integral-domain stalks is
irreducible. -/
theorem isIrreducible_connectedComponent_of_isDomain_stalk (x : X) :
    IsIrreducible (connectedComponent x) := by
  have h := (IrreducibleSpace.isIrreducible_univ (X.connectedComponentOpen x).toScheme).image
    (X.connectedComponentOpen x).ι (X.connectedComponentOpen x).ι.continuous.continuousOn
  rwa [Set.image_univ, Scheme.Opens.range_ι, Scheme.coe_connectedComponentOpen] at h

/-- Every connected component of a locally Noetherian scheme with integral-domain stalks is an
irreducible component. -/
theorem connectedComponent_mem_irreducibleComponents_of_isDomain_stalk (x : X) :
    connectedComponent x ∈ irreducibleComponents X :=
  ⟨isIrreducible_connectedComponent_of_isDomain_stalk x, fun _ hs hsub ↦
    hs.isConnected.isPreconnected.subset_connectedComponent (hsub mem_connectedComponent)⟩

/-- An irreducible component of a locally Noetherian scheme with integral-domain stalks containing
`x` coincides with the connected component of `x`. -/
theorem eq_connectedComponent_of_mem_irreducibleComponents_of_isDomain_stalk {Z : Set X}
    (hZ : Z ∈ irreducibleComponents X) {x : X} (hx : x ∈ Z) :
    Z = connectedComponent x := by
  have hsub : Z ⊆ connectedComponent x :=
    hZ.1.isConnected.isPreconnected.subset_connectedComponent hx
  exact hsub.antisymm (hZ.2 (isIrreducible_connectedComponent_of_isDomain_stalk x) hsub)

/-- On a locally Noetherian scheme with integral-domain stalks, the irreducible component of a point
equals its connected component. -/
theorem irreducibleComponent_eq_connectedComponent_of_isDomain_stalk (x : X) :
    irreducibleComponent x = connectedComponent x :=
  eq_connectedComponent_of_mem_irreducibleComponents_of_isDomain_stalk
    (irreducibleComponent_mem_irreducibleComponents x) mem_irreducibleComponent

/-- Every irreducible component of a locally Noetherian scheme with integral-domain stalks is
open. -/
theorem isOpen_of_mem_irreducibleComponents_of_isDomain_stalk {Z : Set X}
    (hZ : Z ∈ irreducibleComponents X) :
    IsOpen Z := by
  obtain ⟨x, hx⟩ := hZ.1.nonempty
  rw [eq_connectedComponent_of_mem_irreducibleComponents_of_isDomain_stalk hZ hx]
  exact isOpen_connectedComponent

/-- Every irreducible component of a locally Noetherian scheme with integral-domain stalks is
clopen. -/
theorem isClopen_of_mem_irreducibleComponents_of_isDomain_stalk {Z : Set X}
    (hZ : Z ∈ irreducibleComponents X) :
    IsClopen Z :=
  ⟨isClosed_of_mem_irreducibleComponents Z hZ,
    isOpen_of_mem_irreducibleComponents_of_isDomain_stalk hZ⟩

/-- Distinct irreducible components of a locally Noetherian scheme with integral-domain stalks are
disjoint. -/
theorem disjoint_of_mem_irreducibleComponents_of_isDomain_stalk {Z W : Set X}
    (hZ : Z ∈ irreducibleComponents X) (hW : W ∈ irreducibleComponents X) (hne : Z ≠ W) :
    Disjoint Z W :=
  Set.disjoint_left.mpr fun _ hxZ hxW ↦ hne <|
    (eq_connectedComponent_of_mem_irreducibleComponents_of_isDomain_stalk hZ hxZ).trans
      (eq_connectedComponent_of_mem_irreducibleComponents_of_isDomain_stalk hW hxW).symm

variable (X) in
/-- The unique irreducible component of a locally Noetherian scheme with integral-domain stalks
containing a given point `x`. -/
def componentOf (x : X) : irreducibleComponents X :=
  ⟨connectedComponent x, connectedComponent_mem_irreducibleComponents_of_isDomain_stalk x⟩

@[simp]
theorem coe_componentOf (x : X) :
    (componentOf X x : Set X) = connectedComponent x :=
  (rfl)

theorem mem_componentOf (x : X) :
    x ∈ (componentOf X x : Set X) :=
  mem_connectedComponent

/-- A point `x` of a locally Noetherian scheme with integral-domain stalks lies in an irreducible
component `v` if and only if `v` is `componentOf X x`. -/
theorem componentOf_eq_iff {v : irreducibleComponents X} {x : X} :
    componentOf X x = v ↔ x ∈ (v : Set X) :=
  ⟨fun h ↦ h ▸ mem_componentOf x,
    fun hx ↦ Subtype.ext
      (eq_connectedComponent_of_mem_irreducibleComponents_of_isDomain_stalk v.2 hx).symm⟩

/-- Every point of a locally Noetherian scheme with integral-domain stalks belongs to a unique
irreducible component. -/
theorem existsUnique_mem_irreducibleComponents_of_isDomain_stalk (x : X) :
    ∃! v : irreducibleComponents X, x ∈ (v : Set X) :=
  ⟨componentOf X x, mem_componentOf x, fun _ hv ↦ (componentOf_eq_iff.mpr hv).symm⟩

variable (X) in
/-- **Open-subscheme structure on an irreducible component of a locally Noetherian scheme with
integral-domain stalks.** Because the irreducible components of `X` coincide with its connected
components, each `v` is clopen in `X`. -/
def componentOpen (v : irreducibleComponents X) : X.Opens :=
  ⟨v.1, isOpen_of_mem_irreducibleComponents_of_isDomain_stalk v.2⟩

@[simp]
theorem coe_componentOpen (v : irreducibleComponents X) :
    ((componentOpen X v : X.Opens) : Set X) = v.1 :=
  (rfl)

@[simp]
theorem mem_componentOpen {v : irreducibleComponents X} {x : X} :
    x ∈ componentOpen X v ↔ x ∈ (v : Set X) :=
  Iff.rfl

@[simp]
theorem componentOpen_componentOf (x : X) :
    componentOpen X (componentOf X x) = X.connectedComponentOpen x :=
  TopologicalSpace.Opens.ext (by simp)

instance connectedSpace_componentOpen (v : irreducibleComponents X) :
    ConnectedSpace (componentOpen X v).toScheme :=
  isConnected_iff_connectedSpace.mp v.2.1.isConnected

instance isIntegral_componentOpen (v : irreducibleComponents X) :
    IsIntegral (componentOpen X v).toScheme :=
  have : ∀ u : (componentOpen X v).toScheme,
      IsDomain ((componentOpen X v).toScheme.presheaf.stalk u) := fun u ↦
    ((componentOpen X v).ι.isDomain_stalk_iff_of_isIso_stalkMap u).mp inferInstance
  isIntegral_of_connected_of_isDomain_stalk (componentOpen X v).toScheme

instance isClosedImmersion_componentOpen_ι (v : irreducibleComponents X) :
    IsClosedImmersion (componentOpen X v).ι :=
  IsClosedImmersion.of_isPreimmersion _ (by
    simpa only [Scheme.Opens.range_ι, coe_componentOpen] using
      isClosed_of_mem_irreducibleComponents v.1 v.2)

end Components

section BaseChange

/-- Under pullback along a geometrically irreducible universally open morphism, the unique
component containing `g x'` corresponds to the unique component containing `x'`. -/
theorem componentOf_apply_of_isPullback
    {S S' X X' : Scheme.{u}}
    [IsLocallyNoetherian X] [∀ x : X, IsDomain (X.presheaf.stalk x)]
    [IsLocallyNoetherian X'] [∀ x' : X', IsDomain (X'.presheaf.stalk x')]
    {f : X ⟶ S} {f' : X' ⟶ S'} {g : X' ⟶ X} {h : S' ⟶ S}
    [GeometricallyIrreducible h] [UniversallyOpen h]
    (H : IsPullback g f' f h) (x' : X') :
    componentOf X (g x') = irreducibleComponentsEquivOfIsPullback H (componentOf X' x') := by
  rw [componentOf_eq_iff, ← Set.mem_preimage, preimage_coe_irreducibleComponentsEquivOfIsPullback]
  exact mem_componentOf x'

/-- Under pullback along a geometrically irreducible universally open morphism, the preimage of a
component open of `X` is the corresponding component open of `X'`. -/
theorem preimage_componentOpen_of_isPullback
    {S S' X X' : Scheme.{u}}
    [IsLocallyNoetherian X] [∀ x : X, IsDomain (X.presheaf.stalk x)]
    [IsLocallyNoetherian X'] [∀ x' : X', IsDomain (X'.presheaf.stalk x')]
    {f : X ⟶ S} {f' : X' ⟶ S'} {g : X' ⟶ X} {h : S' ⟶ S}
    [GeometricallyIrreducible h] [UniversallyOpen h]
    (H : IsPullback g f' f h) (v' : irreducibleComponents X') :
    g ⁻¹ᵁ componentOpen X (irreducibleComponentsEquivOfIsPullback H v') =
      componentOpen X' v' :=
  TopologicalSpace.Opens.ext (preimage_coe_irreducibleComponentsEquivOfIsPullback H v')

/-- **Each component open of a pullback along a geometrically irreducible universally open morphism
is the pullback of the corresponding component open.** -/
theorem exists_isPullback_componentOpen
    {S S' X X' : Scheme.{u}}
    [IsLocallyNoetherian X] [∀ x : X, IsDomain (X.presheaf.stalk x)]
    [IsLocallyNoetherian X'] [∀ x' : X', IsDomain (X'.presheaf.stalk x')]
    {f : X ⟶ S} {f' : X' ⟶ S'} {g : X' ⟶ X} {h : S' ⟶ S}
    [GeometricallyIrreducible h] [UniversallyOpen h]
    (H : IsPullback g f' f h) (v' : irreducibleComponents X') :
    ∃ g_v : (componentOpen X' v').toScheme ⟶
        (componentOpen X (irreducibleComponentsEquivOfIsPullback H v')).toScheme,
      g_v ≫ (componentOpen X (irreducibleComponentsEquivOfIsPullback H v')).ι =
        (componentOpen X' v').ι ≫ g ∧
      IsPullback g_v ((componentOpen X' v').ι ≫ f')
        ((componentOpen X (irreducibleComponentsEquivOfIsPullback H v')).ι ≫ f) h := by
  have hpre := (preimage_componentOpen_of_isPullback H v').symm
  have hpb := g.isPullback_resLE_of_eq
    (componentOpen X (irreducibleComponentsEquivOfIsPullback H v')) hpre
  exact ⟨g.resLE _ _ hpre.le, hpb.w, hpb.paste_vert H⟩

end BaseChange

end TauCeti.AlgebraicGeometry
