/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.IrreducibleOfConnectedDomainStalk
public import TauCeti.AlgebraicGeometry.Noetherian
public import TauCeti.AlgebraicGeometry.Scheme.ConnectedComponent

/-!
# Irreducible and connected components of schemes with domain stalks

Let `X` be a locally Noetherian scheme whose local rings are integral domains, for instance a
locally Noetherian normal scheme or a regular scheme. Because `X` is locally Noetherian, its
underlying space is locally connected, so each connected component `connectedComponent x` is open
and closed. Equipped with its open-subscheme structure
(`AlgebraicGeometry.Scheme.connectedComponentOpen`), that connected component is connected, locally
Noetherian, and has domain stalks, so it is an integral scheme
(`TauCeti.AlgebraicGeometry.irreducibleSpace_of_connected_of_isDomain_stalk`).

Consequently, the irreducible components of `X` are precisely its connected components: every
irreducible component is clopen, distinct irreducible components are disjoint, every point lies on
a unique irreducible component, and each irreducible component `v : irreducibleComponents X` carries
an integral clopen-subscheme structure `X.componentOpens v`.

## Main definitions

* `AlgebraicGeometry.Scheme.componentOf X x`: the unique irreducible component of `X` containing
  `x`.
* `AlgebraicGeometry.Scheme.componentOpens X v`: an irreducible component `v` of `X` as an open
  subscheme whose inclusion is also a closed immersion.

## Main results

* `AlgebraicGeometry.Scheme.isIntegral_connectedComponentOpen`: each connected component open of `X`
  is an integral scheme.
* `AlgebraicGeometry.Scheme.irreducibleComponents_eq_range_connectedComponent`: the irreducible
  components of `X` coincide with its connected components.
* `AlgebraicGeometry.Scheme.isClopen_of_mem_irreducibleComponents` and
  `AlgebraicGeometry.Scheme.pairwiseDisjoint_irreducibleComponents`: the irreducible components of
  `X` are clopen and pairwise disjoint.
* `AlgebraicGeometry.Scheme.existsUnique_mem_irreducibleComponents`: every point of `X` belongs to a
  unique irreducible component.

## References

* [The Stacks Project, Lemma 28.7.4, Tag 033M](https://stacks.math.columbia.edu/tag/033M):
  connected and irreducible components of a locally Noetherian normal scheme.
-/

public section

open CategoryTheory Set TopologicalSpace TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

universe u

variable (X : Scheme.{u}) [IsLocallyNoetherian X] [∀ x : X, IsDomain (X.presheaf.stalk x)]

/-- Each connected component open of a locally Noetherian scheme with domain stalks is an integral
scheme. -/
instance isIntegral_connectedComponentOpen (x : X) :
    IsIntegral (X.connectedComponentOpen x).toScheme := by
  let U := X.connectedComponentOpen x
  have : IsLocallyNoetherian U.toScheme := isLocallyNoetherian_of_isOpenImmersion U.ι
  have hdom (y : U.toScheme) : IsDomain (U.toScheme.presheaf.stalk y) :=
    (asIso (U.ι.stalkMap y)).symm.commRingCatIsoToRingEquiv.toMulEquiv.isDomain
      (X.presheaf.stalk (U.ι y))
  have : IrreducibleSpace U.toScheme :=
    irreducibleSpace_of_connected_of_isDomain_stalk U.toScheme hdom
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
    (hC : C ∈ irreducibleComponents X) {x : X} (hx : x ∈ C) :
    C = connectedComponent x := by
  have hsub : C ⊆ connectedComponent x :=
    hC.1.isPreirreducible.isPreconnected.subset_connectedComponent hx
  exact hsub.antisymm (hC.2 (X.isIrreducible_connectedComponent x) hsub)

/-- At every point of a locally Noetherian scheme with domain stalks, `irreducibleComponent x`
agrees with `connectedComponent x`. -/
@[simp]
theorem irreducibleComponent_eq_connectedComponent (x : X) :
    irreducibleComponent x = connectedComponent x :=
  eq_connectedComponent_of_mem_irreducibleComponents
    (irreducibleComponent_mem_irreducibleComponents x) mem_irreducibleComponent

/-- **The irreducible components of a locally Noetherian scheme with domain stalks are its
connected components.** -/
theorem irreducibleComponents_eq_range_connectedComponent :
    irreducibleComponents X = range (connectedComponent : X → Set X) := by
  refine Subset.antisymm (fun C hC ↦ ?_) ?_
  · obtain ⟨x, hx⟩ := hC.1.nonempty
    exact ⟨x, (eq_connectedComponent_of_mem_irreducibleComponents hC hx).symm⟩
  · rintro _ ⟨x, rfl⟩
    exact X.connectedComponent_mem_irreducibleComponents x

variable {X} in
/-- Every irreducible component of a locally Noetherian scheme with domain stalks is clopen. -/
theorem isClopen_of_mem_irreducibleComponents {C : Set X} (hC : C ∈ irreducibleComponents X) :
    IsClopen C := by
  obtain ⟨x, hx⟩ := hC.1.nonempty
  rw [eq_connectedComponent_of_mem_irreducibleComponents hC hx]
  exact isClopen_connectedComponent

/-- Distinct irreducible components of a locally Noetherian scheme with domain stalks are
disjoint. -/
theorem pairwiseDisjoint_irreducibleComponents :
    (irreducibleComponents X).PairwiseDisjoint id := by
  intro C hC D hD hne
  refine disjoint_left.mpr fun x hxC hxD ↦ hne ?_
  rw [eq_connectedComponent_of_mem_irreducibleComponents hC hxC,
    eq_connectedComponent_of_mem_irreducibleComponents hD hxD]

/-- The unique irreducible component of a locally Noetherian scheme with domain stalks containing a
given point `x`, defined constructively as its connected component. -/
def componentOf (x : X) : irreducibleComponents X :=
  ⟨connectedComponent x, X.connectedComponent_mem_irreducibleComponents x⟩

@[simp]
theorem coe_componentOf (x : X) : (X.componentOf x : Set X) = connectedComponent x :=
  (rfl)

theorem mem_componentOf_self (x : X) : x ∈ (X.componentOf x : Set X) :=
  mem_connectedComponent

theorem componentOf_eq_iff {x : X} {v : irreducibleComponents X} :
    X.componentOf x = v ↔ x ∈ (v : Set X) :=
  ⟨fun h ↦ h ▸ X.mem_componentOf_self x,
    fun hx ↦ Subtype.ext (eq_connectedComponent_of_mem_irreducibleComponents v.2 hx).symm⟩

theorem eq_componentOf_iff {v : irreducibleComponents X} {x : X} :
    v = X.componentOf x ↔ x ∈ (v : Set X) :=
  eq_comm.trans (X.componentOf_eq_iff)

/-- Every point of a locally Noetherian scheme with domain stalks belongs to a unique irreducible
component. -/
theorem existsUnique_mem_irreducibleComponents (x : X) :
    ∃! C : irreducibleComponents X, x ∈ (C : Set X) :=
  ⟨X.componentOf x, X.mem_componentOf_self x, fun _ hxC ↦ (X.eq_componentOf_iff).mpr hxC⟩

/-- An irreducible component of a locally Noetherian scheme with domain stalks, equipped with its
open-subscheme structure. Because the component is also closed, its inclusion is both an open and a
closed immersion. -/
def componentOpens (v : irreducibleComponents X) : X.Opens :=
  ⟨v.1, (isClopen_of_mem_irreducibleComponents v.2).2⟩

@[simp]
theorem coe_componentOpens (v : irreducibleComponents X) :
    (X.componentOpens v : Set X) = (v : Set X) :=
  (rfl)

@[simp]
theorem mem_componentOpens {v : irreducibleComponents X} {x : X} :
    x ∈ X.componentOpens v ↔ x ∈ (v : Set X) :=
  Iff.rfl

/-- Adding the open-subscheme structure to an irreducible component agrees with
`connectedComponentOpen` at any point of the component. -/
theorem componentOpens_eq_connectedComponentOpen {v : irreducibleComponents X} {x : X}
    (hx : x ∈ (v : Set X)) :
    X.componentOpens v = X.connectedComponentOpen x := by
  ext1
  rw [coe_componentOpens, coe_connectedComponentOpen]
  exact eq_connectedComponent_of_mem_irreducibleComponents v.2 hx

/-- Each irreducible component open subscheme is an integral scheme. -/
instance isIntegral_componentOpens (v : irreducibleComponents X) :
    IsIntegral (X.componentOpens v).toScheme := by
  obtain ⟨x, hx⟩ := v.2.1.nonempty
  rw [X.componentOpens_eq_connectedComponentOpen hx]
  infer_instance

/-- The inclusion of an irreducible component open subscheme is also a closed immersion. -/
instance isClosedImmersion_componentOpens_ι (v : irreducibleComponents X) :
    IsClosedImmersion (X.componentOpens v).ι :=
  IsClosedImmersion.of_isPreimmersion _ (by
    simpa only [Opens.range_ι, coe_componentOpens] using
      (isClopen_of_mem_irreducibleComponents v.2).1)

end AlgebraicGeometry.Scheme
