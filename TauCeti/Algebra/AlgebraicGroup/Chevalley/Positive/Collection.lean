/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Positive.Basic
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Collection

/-!
# Positive-root products

For every Chevalley datum, every element of the positive-root subgroup is a product
with one factor from each positive root subgroup, in any enumeration without repetition.
This works on the admissible lattice over every commutative value ring. It is the existence
part of positive-root coordinates, not their uniqueness or a point-generation theorem for the
whole Chevalley group.

The formal input is the arbitrary Kostant-lattice collection theorem
`DynkinType.mem_iSup_posRoots_chevalleyRootSubgroup_iff_exists_list_prod`.
Its height bounds outside G₂ and native table-index grading in G₂ collect the factors without
dividing by structure constants.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 17.
* R. W. Carter, *Simple Groups of Lie Type*, §5.3.
-/

public section

open TensorProduct TauCeti.UniversalEnvelopingAlgebra

namespace TauCeti.DynkinType.ChevalleyDatum

universe v

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

attribute [local instance high] Algebra.toModule

/-- Every positive lattice operator has a root-product expression in any enumeration of all
positive roots without repetition. This holds in every valid type over any commutative ring,
including in bad characteristic. -/
theorem mem_positiveSubgroup_iff_exists_prod
    (l : List (Fin t.numRoots)) (hl : l.Nodup)
    (hcover : ∀ γ, γ ∈ l ↔ γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht))
    (A : CommAlgCat.{v} ℤ)
    (g : LinearMap.GeneralLinearGroup A (A ⊗[ℤ] D.lattice)) :
    g ∈ D.positiveSubgroup A ↔ ∃ u : Fin t.numRoots → Multiplicative A,
      (l.map fun γ => chevalleyRootSubgroup D.representation D.lattice
        D.representation_mem_lattice D.isNilpotent_representation_rootGenerator γ A (u γ)).prod =
        g := by
  rw [D.positiveSubgroup_eq_iSup,
    mem_iSup_posRoots_chevalleyRootSubgroup_iff_exists_list_prod D.representation D.lattice
      D.representation_mem_lattice D.isNilpotent_representation_rootGenerator A l hl hcover g]
  exact ⟨fun ⟨u, hu⟩ => ⟨fun γ => Multiplicative.ofAdd (u γ), hu⟩,
    fun ⟨u, hu⟩ => ⟨fun γ => (u γ).toAdd, by simpa only [ofAdd_toAdd] using hu⟩⟩

/-- A positive datum point has a root-product expression in any enumeration of all positive
roots without repetition, over every commutative ring. -/
theorem mem_positivePoints_iff_exists_prod
    (l : List (Fin t.numRoots)) (hl : l.Nodup)
    (hcover : ∀ γ, γ ∈ l ↔ γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht))
    (A : Type v) [CommRing A] (x : D.points A) :
    x ∈ D.positivePoints A ↔ ∃ u : Fin t.numRoots → Multiplicative A,
      (l.map fun γ => D.rootSubgroupPoints γ A (u γ)).prod = x := by
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := D.mem_positivePoints_iff.mp hx
    obtain ⟨u, hu⟩ := (D.mem_positiveSubgroup_iff_exists_prod
      l hl hcover (CommAlgCat.of ℤ A) y).mp hy
    refine ⟨u, (D.points A).subtype_injective ?_⟩
    have hmat := congrArg
      (Units.map (LinearMap.toMatrixAlgEquiv (D.basis.baseChange A)).toMonoidHom) hu
    simpa only [map_list_prod, List.map_map, Function.comp_def, Subgroup.subtype_apply,
      D.coe_rootSubgroupPoints, MulEquiv.toMonoidHom_eq_coe] using hmat.trans hyx
  · rintro ⟨u, rfl⟩
    apply Subgroup.list_prod_mem
    intro z hz
    obtain ⟨γ, hγ, rfl⟩ := List.mem_map.mp hz
    exact D.rootSubgroupPoints_mem_positivePoints A ((hcover γ).mp hγ) (u γ)

end TauCeti.DynkinType.ChevalleyDatum
