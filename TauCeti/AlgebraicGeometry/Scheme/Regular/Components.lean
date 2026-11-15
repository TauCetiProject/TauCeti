/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import TauCeti.AlgebraicGeometry.Noetherian
public import TauCeti.AlgebraicGeometry.Scheme.ConnectedComponent
public import TauCeti.AlgebraicGeometry.Scheme.Regular.Scheme
import TauCeti.AlgebraicGeometry.Geometrically.Irreducible
import TauCeti.AlgebraicGeometry.IrreducibleOfConnectedDomainStalk
import TauCeti.AlgebraicGeometry.Restrict

/-!
# Irreducible components of regular schemes

On a regular scheme `X`, every stalk is a regular local ring and in particular an integral domain,
while local Noetherianity makes the underlying topological space locally connected. Each connected
component `X.connectedComponentOpen x` is therefore an open-and-closed connected regular subscheme,
hence integral (`TauCeti.AlgebraicGeometry.isIntegral_connectedComponentOpen`). Consequently the
irreducible components of `X` coincide with its connected components: they are pairwise disjoint
clopen subsets partitioning `X`, and each `v : irreducibleComponents X` carries a canonical clopen
integral regular subscheme structure (`TauCeti.AlgebraicGeometry.IsRegular.componentOpen`).

When `X` is a regular scheme over a separably closed field `K` and `X'` is a regular base change of
`X` along `Spec M ⟶ Spec K` for a `K`-algebra `M` with irreducible spectrum (such as any field
extension `L / K`), the projection `g : X' ⟶ X` induces a bijection on irreducible components and
identifies each component open of `X'` as the base change of the corresponding component open of `X`
(`TauCeti.AlgebraicGeometry.IsRegular.exists_isPullback_componentOpen`).

## References

* [The Stacks Project, Tag 0355](https://stacks.math.columbia.edu/tag/0355): normal schemes are
  disjoint unions of integral normal schemes.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry

/-- Each connected component of a regular scheme, equipped with its open-subscheme structure, is
integral. -/
instance isIntegral_connectedComponentOpen (X : Scheme.{u}) [IsRegular X] (x : X) :
    IsIntegral (X.connectedComponentOpen x).toScheme :=
  isIntegral_of_connected_of_isRegularLocalRing_stalk (X.connectedComponentOpen x).toScheme

namespace IsRegular

variable {X : Scheme.{u}} [IsRegular X]

/-- Every connected component of a regular scheme is irreducible. -/
theorem isIrreducible_connectedComponent (x : X) :
    IsIrreducible (connectedComponent x) := by
  have h := (IrreducibleSpace.isIrreducible_univ (X.connectedComponentOpen x).toScheme).image
    (X.connectedComponentOpen x).ι (X.connectedComponentOpen x).ι.continuous.continuousOn
  rwa [Set.image_univ, Scheme.Opens.range_ι, Scheme.coe_connectedComponentOpen] at h

/-- Every connected component of a regular scheme is an irreducible component. -/
theorem connectedComponent_mem_irreducibleComponents (x : X) :
    connectedComponent x ∈ irreducibleComponents X :=
  ⟨isIrreducible_connectedComponent x, fun _ hs hsub ↦
    hs.isConnected.isPreconnected.subset_connectedComponent (hsub mem_connectedComponent)⟩

/-- An irreducible component of a regular scheme containing `x` coincides with the connected
component of `x`. -/
theorem eq_connectedComponent_of_mem_irreducibleComponents {Z : Set X}
    (hZ : Z ∈ irreducibleComponents X) {x : X} (hx : x ∈ Z) :
    Z = connectedComponent x := by
  have hsub : Z ⊆ connectedComponent x :=
    hZ.1.isConnected.isPreconnected.subset_connectedComponent hx
  exact hsub.antisymm (hZ.2 (isIrreducible_connectedComponent x) hsub)

/-- On a regular scheme, the irreducible component of a point equals its connected component. -/
theorem irreducibleComponent_eq_connectedComponent (x : X) :
    irreducibleComponent x = connectedComponent x :=
  eq_connectedComponent_of_mem_irreducibleComponents
    (irreducibleComponent_mem_irreducibleComponents x) mem_irreducibleComponent

/-- Every irreducible component of a regular scheme is open. -/
theorem isOpen_of_mem_irreducibleComponents {Z : Set X} (hZ : Z ∈ irreducibleComponents X) :
    IsOpen Z := by
  obtain ⟨x, hx⟩ := hZ.1.nonempty
  rw [eq_connectedComponent_of_mem_irreducibleComponents hZ hx]
  exact isOpen_connectedComponent

/-- Every irreducible component of a regular scheme is clopen. -/
theorem isClopen_of_mem_irreducibleComponents {Z : Set X} (hZ : Z ∈ irreducibleComponents X) :
    IsClopen Z :=
  ⟨isClosed_of_mem_irreducibleComponents Z hZ, isOpen_of_mem_irreducibleComponents hZ⟩

/-- Distinct irreducible components of a regular scheme are disjoint. -/
theorem disjoint_of_mem_irreducibleComponents {Z W : Set X}
    (hZ : Z ∈ irreducibleComponents X) (hW : W ∈ irreducibleComponents X) (hne : Z ≠ W) :
    Disjoint Z W :=
  Set.disjoint_left.mpr fun _ hxZ hxW ↦ hne <|
    (eq_connectedComponent_of_mem_irreducibleComponents hZ hxZ).trans
      (eq_connectedComponent_of_mem_irreducibleComponents hW hxW).symm

variable (X) in
/-- The unique irreducible component of a regular scheme containing a given point `x`. -/
def componentOf (x : X) : irreducibleComponents X :=
  ⟨connectedComponent x, connectedComponent_mem_irreducibleComponents x⟩

@[simp]
theorem coe_componentOf (x : X) :
    (componentOf X x : Set X) = connectedComponent x :=
  (rfl)

theorem mem_componentOf (x : X) :
    x ∈ (componentOf X x : Set X) :=
  mem_connectedComponent

/-- A point `x` of a regular scheme lies in an irreducible component `v` if and only if `v` is
`componentOf X x`. -/
theorem componentOf_eq_iff {v : irreducibleComponents X} {x : X} :
    componentOf X x = v ↔ x ∈ (v : Set X) :=
  ⟨fun h ↦ h ▸ mem_componentOf x,
    fun hx ↦ Subtype.ext (eq_connectedComponent_of_mem_irreducibleComponents v.2 hx).symm⟩

/-- Every point of a regular scheme belongs to a unique irreducible component. -/
theorem existsUnique_mem_irreducibleComponents (x : X) :
    ∃! v : irreducibleComponents X, x ∈ (v : Set X) :=
  ⟨componentOf X x, mem_componentOf x, fun _ hv ↦ (componentOf_eq_iff.mpr hv).symm⟩

variable (X) in
/-- **Open-subscheme structure on an irreducible component of a regular scheme.** Because the
irreducible components of `X` coincide with its connected components, each `v` is clopen in `X`. -/
def componentOpen (v : irreducibleComponents X) : X.Opens :=
  ⟨v.1, isOpen_of_mem_irreducibleComponents v.2⟩

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
  isIntegral_of_connected_of_isRegularLocalRing_stalk (componentOpen X v).toScheme

instance isClosedImmersion_componentOpen_ι (v : irreducibleComponents X) :
    IsClosedImmersion (componentOpen X v).ι :=
  IsClosedImmersion.of_isPreimmersion _ (by
    simpa only [Scheme.Opens.range_ι, coe_componentOpen] using
      isClosed_of_mem_irreducibleComponents v.1 v.2)

end IsRegular

section BaseChange

/-- Base change along `Spec M ⟶ Spec K` over a separably closed field `K`, for a `K`-algebra `M`
with irreducible spectrum, induces an equivalence on irreducible components. -/
noncomputable def irreducibleComponentsEquivOfIsPullback {K M : Type u} [Field K] [IsSepClosed K]
    [CommRing M] [Algebra K M] [IrreducibleSpace (PrimeSpectrum M)]
    {X X' : Scheme.{u}} {f : X ⟶ Spec (.of K)} {f' : X' ⟶ Spec (.of M)} {g : X' ⟶ X}
    (H : IsPullback g f' f (Spec.map (CommRingCat.ofHom (algebraMap K M)))) :
    irreducibleComponents X' ≃ irreducibleComponents X :=
  have : GeometricallyIrreducible g := MorphismProperty.of_isPullback H.flip inferInstance
  have : UniversallyOpen g := MorphismProperty.of_isPullback H.flip inferInstance
  g.irreducibleComponentsEquiv g.isOpenMap

@[simp]
theorem coe_irreducibleComponentsEquivOfIsPullback_symm {K M : Type u} [Field K] [IsSepClosed K]
    [CommRing M] [Algebra K M] [IrreducibleSpace (PrimeSpectrum M)]
    {X X' : Scheme.{u}} {f : X ⟶ Spec (.of K)} {f' : X' ⟶ Spec (.of M)} {g : X' ⟶ X}
    (H : IsPullback g f' f (Spec.map (CommRingCat.ofHom (algebraMap K M))))
    (v : irreducibleComponents X) :
    ((irreducibleComponentsEquivOfIsPullback H).symm v : Set X') = g ⁻¹' (v : Set X) := by
  have : GeometricallyIrreducible g := MorphismProperty.of_isPullback H.flip inferInstance
  have : UniversallyOpen g := MorphismProperty.of_isPullback H.flip inferInstance
  exact g.irreducibleComponentsEquiv_symm_apply_coe g.isOpenMap v

theorem coe_irreducibleComponentsEquivOfIsPullback_preimage {K M : Type u} [Field K]
    [IsSepClosed K] [CommRing M] [Algebra K M] [IrreducibleSpace (PrimeSpectrum M)]
    {X X' : Scheme.{u}} {f : X ⟶ Spec (.of K)} {f' : X' ⟶ Spec (.of M)} {g : X' ⟶ X}
    (H : IsPullback g f' f (Spec.map (CommRingCat.ofHom (algebraMap K M))))
    (v' : irreducibleComponents X') :
    g ⁻¹' (irreducibleComponentsEquivOfIsPullback H v' : Set X) = (v' : Set X') := by
  rw [← coe_irreducibleComponentsEquivOfIsPullback_symm H, Equiv.symm_apply_apply]

namespace IsRegular

/-- Under base change from a separably closed field `K` to a `K`-algebra `M` with irreducible
spectrum, the unique component of a regular scheme containing `g x'` corresponds to the unique
component containing `x'`. -/
theorem componentOf_apply_of_isPullback {K M : Type u} [Field K] [IsSepClosed K]
    [CommRing M] [Algebra K M] [IrreducibleSpace (PrimeSpectrum M)]
    {X X' : Scheme.{u}} [IsRegular X] [IsRegular X']
    {f : X ⟶ Spec (.of K)} {f' : X' ⟶ Spec (.of M)} {g : X' ⟶ X}
    (H : IsPullback g f' f (Spec.map (CommRingCat.ofHom (algebraMap K M)))) (x' : X') :
    componentOf X (g x') = irreducibleComponentsEquivOfIsPullback H (componentOf X' x') := by
  rw [componentOf_eq_iff, ← Set.mem_preimage, coe_irreducibleComponentsEquivOfIsPullback_preimage]
  exact mem_componentOf x'

/-- Under base change from a separably closed field `K`, the preimage of a component open of `X` is
the corresponding component open of `X'`. -/
theorem preimage_componentOpen_of_isPullback {K M : Type u} [Field K] [IsSepClosed K]
    [CommRing M] [Algebra K M] [IrreducibleSpace (PrimeSpectrum M)]
    {X X' : Scheme.{u}} [IsRegular X] [IsRegular X']
    {f : X ⟶ Spec (.of K)} {f' : X' ⟶ Spec (.of M)} {g : X' ⟶ X}
    (H : IsPullback g f' f (Spec.map (CommRingCat.ofHom (algebraMap K M))))
    (v' : irreducibleComponents X') :
    g ⁻¹ᵁ componentOpen X (irreducibleComponentsEquivOfIsPullback H v') =
      componentOpen X' v' :=
  TopologicalSpace.Opens.ext (coe_irreducibleComponentsEquivOfIsPullback_preimage H v')

/-- **Each component open of a regular base change over a separably closed field is the base change
of the corresponding component open.** -/
theorem exists_isPullback_componentOpen {K M : Type u} [Field K] [IsSepClosed K]
    [CommRing M] [Algebra K M] [IrreducibleSpace (PrimeSpectrum M)]
    {X X' : Scheme.{u}} [IsRegular X] [IsRegular X']
    {f : X ⟶ Spec (.of K)} {f' : X' ⟶ Spec (.of M)} {g : X' ⟶ X}
    (H : IsPullback g f' f (Spec.map (CommRingCat.ofHom (algebraMap K M))))
    (v' : irreducibleComponents X') :
    ∃ g_v : (componentOpen X' v').toScheme ⟶
        (componentOpen X (irreducibleComponentsEquivOfIsPullback H v')).toScheme,
      g_v ≫ (componentOpen X (irreducibleComponentsEquivOfIsPullback H v')).ι =
        (componentOpen X' v').ι ≫ g ∧
      IsPullback g_v ((componentOpen X' v').ι ≫ f')
        ((componentOpen X (irreducibleComponentsEquivOfIsPullback H v')).ι ≫ f)
        (Spec.map (CommRingCat.ofHom (algebraMap K M))) := by
  have hpre := (preimage_componentOpen_of_isPullback H v').symm
  have hpb := g.isPullback_resLE_of_eq
    (componentOpen X (irreducibleComponentsEquivOfIsPullback H v')) hpre
  exact ⟨g.resLE _ _ hpre.le, hpb.w, hpb.paste_vert H⟩

end IsRegular

end BaseChange

end TauCeti.AlgebraicGeometry
