/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Generation

/-!
# Determination by signed simple root subgroups

Homomorphisms from the root-and-torus-generated group of a Chevalley datum are determined
by their values on the positive and negative simple root subgroups and the actual torus.
The torus condition can be omitted if restriction from the full weight lattice is surjective
on torus parameters. This includes data with full weight lattice over every commutative ring,
and arbitrary Chevalley data over a ring with divisible units, in particular an algebraically
closed field.

These uniqueness statements apply to abstract homomorphisms into any monoid. They do not
assert that the root-and-torus-generated group contains all points of the group scheme.
For a proper weight lattice over a general field the actual torus condition is essential;
agreement on the image of the full-weight parametrization is not a substitute.

The generation inputs are `ChevalleyDatum.rootSubgroupPoints_mem_closure` and
`ChevalleyDatum.torusPoints_mem_closure_rootSubgroup_of_mem_range`. The equalizer argument
uses Mathlib's `MonoidHom.eqLocus` and `Subgroup.mem_map_iff_mem`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemmas 19 and 28(c), and
  Corollary 5 to Theorem 4′.
* R. W. Carter, *Simple Groups of Lie Type*, §§6.4 and 7.2.
-/

public section

namespace TauCeti.DynkinType.ChevalleyDatum

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)
  {A : Type*} [CommRing A] {H : Type*} [Monoid H]
  (f g : D.rootTorusSubgroup A →* H)
  (hpos : ∀ i u,
    f ⟨D.rootSubgroupPoints (t.simpleIndex ht i) A u,
        D.rootSubgroupPoints_mem_rootTorusSubgroup _ A u⟩ =
      g ⟨D.rootSubgroupPoints (t.simpleIndex ht i) A u,
        D.rootSubgroupPoints_mem_rootTorusSubgroup _ A u⟩)
  (hneg : ∀ i u,
    f ⟨D.rootSubgroupPoints ((t.simplyConnectedRootDatum ht).reflectionPerm
          (t.simpleIndex ht i) (t.simpleIndex ht i)) A u,
        D.rootSubgroupPoints_mem_rootTorusSubgroup _ A u⟩ =
      g ⟨D.rootSubgroupPoints ((t.simplyConnectedRootDatum ht).reflectionPerm
          (t.simpleIndex ht i) (t.simpleIndex ht i)) A u,
        D.rootSubgroupPoints_mem_rootTorusSubgroup _ A u⟩)

include hpos hneg

private theorem closure_simpleRootPair_le_map_eqLocus :
    Subgroup.closure (⋃ i : Fin t.rank,
      Set.range (D.rootSubgroupPoints (t.simpleIndex ht i) A) ∪
        Set.range (D.rootSubgroupPoints ((t.simplyConnectedRootDatum ht).reflectionPerm
          (t.simpleIndex ht i) (t.simpleIndex ht i)) A)) ≤
      (f.eqLocus g).map (D.rootTorusSubgroup A).subtype := by
  apply (Subgroup.closure_le _).mpr
  rintro x hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  rcases hi with ⟨u, rfl⟩ | ⟨u, rfl⟩
  · exact ⟨_, hpos i u, rfl⟩
  · exact ⟨_, hneg i u, rfl⟩

/-- Homomorphisms from the root-and-torus-generated group are determined by both signs of
the simple root subgroups and the actual weight-lattice torus, over every commutative ring.
No point-generation theorem for the ambient scheme is required. -/
@[ext]
theorem rootTorusSubgroup_hom_ext
    (htorus : ∀ s,
      f ⟨D.torusPoints A s, D.torusPoints_mem_rootTorusSubgroup A s⟩ =
        g ⟨D.torusPoints A s, D.torusPoints_mem_rootTorusSubgroup A s⟩) : f = g := by
  have hsimple := D.closure_simpleRootPair_le_map_eqLocus f g hpos hneg
  have hE : D.rootTorusSubgroup A ≤ (f.eqLocus g).map (D.rootTorusSubgroup A).subtype :=
    (D.rootTorusSubgroup_le_iff A _).mpr
      ⟨fun γ u => hsimple (D.rootSubgroupPoints_mem_closure γ A u),
        fun s => ⟨_, htorus s, rfl⟩⟩
  apply MonoidHom.ext
  intro x
  exact (Subgroup.mem_map_iff_mem (D.rootTorusSubgroup A).subtype_injective).mp (hE x.property)

/-- If every actual torus parameter extends to the full weight lattice, agreement on the
positive and negative simple root subgroups determines a homomorphism on the generated group.
This isolates exactly the torus-extension condition used by root-only determination. -/
theorem rootTorusSubgroup_hom_ext_of_surjective
    (hs : Function.Surjective (D.fullWeightTorusRestriction A)) : f = g := by
  apply D.rootTorusSubgroup_hom_ext f g hpos hneg
  intro s
  exact (Subgroup.mem_map_iff_mem (D.rootTorusSubgroup A).subtype_injective
    (K := f.eqLocus g)
    (x := ⟨D.torusPoints A s, D.torusPoints_mem_rootTorusSubgroup A s⟩)).mp
      (D.closure_simpleRootPair_le_map_eqLocus f g hpos hneg
        (D.torusPoints_mem_closure_rootSubgroup_of_mem_range A s (hs s)))

/-- For a datum with full weight lattice, both signs of the simple root subgroups determine
homomorphisms on the root-and-torus-generated group over every commutative ring. -/
theorem rootTorusSubgroup_hom_ext_of_weightLattice_eq_top
    (hD : D.weightLattice = ⊤) : f = g :=
  D.rootTorusSubgroup_hom_ext_of_surjective f g hpos hneg
    (D.fullWeightTorusRestriction_surjective_of_weightLattice_eq_top A hD)

/-- Over a ring with divisible units, homomorphisms on the generated group are determined by
both signs of the simple root subgroups, even for a proper weight lattice. In particular this
applies over algebraically closed fields. -/
theorem rootTorusSubgroup_hom_ext_of_rootable [RootableBy Aˣ ℕ] : f = g :=
  D.rootTorusSubgroup_hom_ext_of_surjective f g hpos hneg
    (D.fullWeightTorusRestriction_surjective A)

end TauCeti.DynkinType.ChevalleyDatum
