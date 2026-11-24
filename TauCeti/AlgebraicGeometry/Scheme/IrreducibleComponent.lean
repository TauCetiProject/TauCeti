/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.IrreducibleOfConnectedDomainStalk
public import TauCeti.AlgebraicGeometry.Noetherian
public import TauCeti.AlgebraicGeometry.Scheme.Connected.Component

/-!
# Irreducible and connected components of schemes with domain stalks

Let `X` be a locally Noetherian scheme whose local rings are integral domains (for instance a
locally Noetherian normal scheme or a regular scheme). Each connected component open subscheme
`X.connectedComponentOpen x` is connected, locally Noetherian, and has domain stalks, hence is an
integral scheme (`TauCeti.AlgebraicGeometry.irreducibleSpace_of_connected_of_isDomain_stalk`).

Consequently, the irreducible components of `X` coincide with its connected components: every
irreducible component is clopen, distinct irreducible components are disjoint, and each irreducible
component `v : irreducibleComponents X` carries an integral clopen-subscheme structure
`X.componentOpens v`.

## Main definitions

* `AlgebraicGeometry.Scheme.componentOpens`: an irreducible component of `X` equipped with its
  clopen-subscheme structure.

## Main results

* `AlgebraicGeometry.Scheme.isIntegral_connectedComponentOpen`: each connected component open
  subscheme of `X` is integral.
* `AlgebraicGeometry.Scheme.irreducibleComponent_eq_connectedComponent` and
  `AlgebraicGeometry.Scheme.irreducibleComponents_eq_range_connectedComponent`: the irreducible
  components of `X` coincide with its connected components.
* `AlgebraicGeometry.Scheme.isClopen_of_mem_irreducibleComponents` and
  `AlgebraicGeometry.Scheme.pairwiseDisjoint_irreducibleComponents`: irreducible components of `X`
  are clopen and pairwise disjoint.
* `AlgebraicGeometry.Scheme.isIntegral_componentOpens` and
  `AlgebraicGeometry.Scheme.isClosedImmersion_componentOpens_ι`: each `X.componentOpens v` is an
  integral clopen subscheme of `X`.

## References

* [The Stacks Project, Lemma 28.7.4, Tag 033M](https://stacks.math.columbia.edu/tag/033M)
-/

public section

open CategoryTheory Set TopologicalSpace TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

universe u

variable (X : Scheme.{u}) [IsLocallyNoetherian X] [∀ x : X, IsDomain (X.presheaf.stalk x)]

/-- Each connected component open of a locally Noetherian scheme with domain stalks is integral. -/
instance isIntegral_connectedComponentOpen (x : X) :
    IsIntegral (X.connectedComponentOpen x).toScheme := by
  let U := X.connectedComponentOpen x
  have : IsLocallyNoetherian U.toScheme := isLocallyNoetherian_of_isOpenImmersion U.ι
  have : IrreducibleSpace U.toScheme := irreducibleSpace_of_connected_of_isDomain_stalk _ fun y ↦
    (asIso (U.ι.stalkMap y)).symm.commRingCatIsoToRingEquiv.toMulEquiv.isDomain _
  have : IsReduced X := isReduced_of_isReduced_stalk X
  have : IsReduced U.toScheme := isReduced_of_isOpenImmersion U.ι
  exact isIntegral_of_irreducibleSpace_of_isReduced U.toScheme

/-- Every connected component of a locally Noetherian scheme with domain stalks is irreducible. -/
theorem isIrreducible_connectedComponent (x : X) : IsIrreducible (connectedComponent x) := by
  let U := X.connectedComponentOpen x
  have h := (IrreducibleSpace.isIrreducible_univ U.toScheme).image U.ι U.ι.continuous.continuousOn
  rwa [Set.image_univ, Opens.range_ι, coe_connectedComponentOpen] at h

/-- Every connected component of a locally Noetherian scheme with domain stalks is an irreducible
component. -/
theorem connectedComponent_mem_irreducibleComponents (x : X) :
    connectedComponent x ∈ irreducibleComponents X :=
  ⟨X.isIrreducible_connectedComponent x, fun _ ht hsub ↦
    ht.isPreirreducible.isPreconnected.subset_connectedComponent (hsub mem_connectedComponent)⟩

variable {X} in
/-- An irreducible component containing `x` equals the connected component of `x`. -/
theorem eq_connectedComponent_of_mem_irreducibleComponents {C : Set X}
    (hC : C ∈ irreducibleComponents X) {x : X} (hx : x ∈ C) : C = connectedComponent x :=
  have hsub := hC.1.isPreirreducible.isPreconnected.subset_connectedComponent hx
  hsub.antisymm (hC.2 (X.isIrreducible_connectedComponent x) hsub)

/-- At every point of `X`, `irreducibleComponent x` agrees with `connectedComponent x`. -/
theorem irreducibleComponent_eq_connectedComponent (x : X) :
    irreducibleComponent x = connectedComponent x :=
  eq_connectedComponent_of_mem_irreducibleComponents
    (irreducibleComponent_mem_irreducibleComponents x) mem_irreducibleComponent

/-- The irreducible components of `X` are its connected components. -/
theorem irreducibleComponents_eq_range_connectedComponent :
    irreducibleComponents X = range (connectedComponent : X → Set X) :=
  Subset.antisymm
    (fun _ hC ↦ let ⟨x, hx⟩ := hC.1.nonempty
      ⟨x, (eq_connectedComponent_of_mem_irreducibleComponents hC hx).symm⟩)
    (by rintro _ ⟨x, rfl⟩; exact X.connectedComponent_mem_irreducibleComponents x)

variable {X} in
/-- Every irreducible component of a locally Noetherian scheme with domain stalks is clopen. -/
theorem isClopen_of_mem_irreducibleComponents {C : Set X} (hC : C ∈ irreducibleComponents X) :
    IsClopen C := by
  obtain ⟨x, hx⟩ := hC.1.nonempty
  exact eq_connectedComponent_of_mem_irreducibleComponents hC hx ▸ isClopen_connectedComponent

/-- Distinct irreducible components of a locally Noetherian scheme with domain stalks are
disjoint. -/
theorem pairwiseDisjoint_irreducibleComponents : (irreducibleComponents X).PairwiseDisjoint id :=
  fun _ hC _ hD hne ↦ disjoint_left.mpr fun _ hxC hxD ↦ hne <|
    (eq_connectedComponent_of_mem_irreducibleComponents hC hxC).trans
      (eq_connectedComponent_of_mem_irreducibleComponents hD hxD).symm

/-- An irreducible component of `X` equipped with its clopen-subscheme structure. -/
def componentOpens (v : irreducibleComponents X) : X.Opens :=
  ⟨v.val, (isClopen_of_mem_irreducibleComponents v.property).isOpen⟩

@[simp]
theorem coe_componentOpens (v : irreducibleComponents X) :
    (X.componentOpens v : Set X) = (v : Set X) := (rfl)

@[simp]
theorem mem_componentOpens {v : irreducibleComponents X} {x : X} :
    x ∈ X.componentOpens v ↔ x ∈ (v : Set X) := Iff.rfl

/-- `componentOpens v` agrees with `connectedComponentOpen` at any point of `v`. -/
theorem componentOpens_eq_connectedComponentOpen {v : irreducibleComponents X} {x : X}
    (hx : x ∈ (v : Set X)) : X.componentOpens v = X.connectedComponentOpen x := by
  ext1; simpa using eq_connectedComponent_of_mem_irreducibleComponents v.property hx

/-- Each irreducible component open subscheme is an integral scheme. -/
instance isIntegral_componentOpens (v : irreducibleComponents X) :
    IsIntegral (X.componentOpens v).toScheme := by
  obtain ⟨x, hx⟩ := v.property.1.nonempty
  rw [X.componentOpens_eq_connectedComponentOpen hx]; infer_instance

/-- The inclusion of an irreducible component open subscheme is also a closed immersion. -/
instance isClosedImmersion_componentOpens_ι (v : irreducibleComponents X) :
    IsClosedImmersion (X.componentOpens v).ι :=
  IsClosedImmersion.of_isPreimmersion _ (by
    simpa [Opens.range_ι] using (isClopen_of_mem_irreducibleComponents v.property).isClosed)

end AlgebraicGeometry.Scheme
