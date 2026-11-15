/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Positive.Basic
import TauCeti.Algebra.Group.Subgroup.OrderedProduct
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Collection.NotG2
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Collection.G2

/-!
# Positive-root products

For every Chevalley datum, every element of the positive-root subgroup is a product
with one factor from each positive root subgroup, in any enumeration without repetition.
This works on the admissible lattice over every commutative value ring. It is the existence
part of positive-root coordinates, not their uniqueness or a point-generation theorem for the
whole Chevalley group.

The native collection bounds outside G₂ put commutators in root groups of strictly greater
height. In G₂ the existing positive-root table
indices supply the grading instead. The formal inputs are
`DynkinType.commutator_range_chevalleyRootSubgroup_le` and
`DynkinType.commutator_range_chevalleyRootSubgroup_g2_le`.
Thus `TauCeti.mem_biSup_iff_exists_list_prod_map` collects the factors in any chosen order,
without dividing by structure constants.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 17.
* R. W. Carter, *Simple Groups of Lie Type*, §5.3.
-/

public section

open scoped commutatorElement
open TensorProduct TauCeti.UniversalEnvelopingAlgebra

namespace TauCeti.DynkinType.ChevalleyDatum

universe v

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

attribute [local instance high] Algebra.toModule

private theorem exists_collection_degree (A : CommAlgCat.{v} ℤ) :
    ∃ degree : Fin t.numRoots → ℤ,
      ∀ i ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht),
        ∀ j ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht), i ≠ j →
          ⁅(chevalleyRootSubgroup D.representation D.lattice D.representation_mem_lattice
              D.isNilpotent_representation_rootGenerator i A).range,
            (chevalleyRootSubgroup D.representation D.lattice D.representation_mem_lattice
              D.isNilpotent_representation_rootGenerator j A).range⁆ ≤
            ⨆ k ∈ {k ∈ posRootsFinset (t.rationalRootSystem ht) (t.rationalBase ht) |
              max (degree i) (degree j) < degree k},
              (chevalleyRootSubgroup D.representation D.lattice D.representation_mem_lattice
                D.isNilpotent_representation_rootGenerator k A).range := by
  classical
  by_cases hG2 : t = G2
  · subst t
    dsimp +instances only [numRoots] at *
    refine ⟨fun i => i.val, fun i hi j hj hij => ?_⟩
    let a : Fin 6 := ⟨i.val, (mem_posRoots_rational_g2_iff ht i).mp hi⟩
    let b : Fin 6 := ⟨j.val, (mem_posRoots_rational_g2_iff ht j).mp hj⟩
    have hab : a ≠ b := fun h => hij (Fin.ext (congrArg (fun k : Fin 6 => k.val) h))
    have h := commutator_range_chevalleyRootSubgroup_g2_le D.representation D.lattice
      D.representation_mem_lattice D.isNilpotent_representation_rootGenerator A a b hab
    -- Reconstructing a native positive root changes only its bound proof.
    apply h.trans
    refine iSup₂_le fun k hk => le_iSup₂
      (f := fun γ _ => (chevalleyRootSubgroup D.representation D.lattice
        D.representation_mem_lattice D.isNilpotent_representation_rootGenerator γ A).range)
      (Fin.castAdd 6 k) ?_
    dsimp +instances only [numRoots]
    simp only [Finset.mem_filter]
    refine ⟨(mem_posRootsFinset _ _ _).mpr
      ((mem_posRoots_rational_g2_iff ht _).mpr k.isLt), ?_⟩
    have hak : a < k := lt_of_le_of_lt (le_max_left _ _) hk
    have hbk : b < k := lt_of_le_of_lt (le_max_right _ _) hk
    rw [max_lt_iff]
    exact ⟨by exact_mod_cast hak, by exact_mod_cast hbk⟩
  · let := isNotG2_rationalRootSystem_of_ne_G2 (ht := ht) hG2
    exact ⟨(t.rationalBase ht).height, fun _ hi _ hj _ =>
      commutator_range_chevalleyRootSubgroup_le D.representation D.lattice
        D.representation_mem_lattice D.isNilpotent_representation_rootGenerator hi hj A⟩

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
  classical
  let X := fun γ => chevalleyRootSubgroup D.representation D.lattice
    D.representation_mem_lattice D.isNilpotent_representation_rootGenerator γ A
  let S := posRootsFinset (t.rationalRootSystem ht) (t.rationalBase ht)
  obtain ⟨degree, hdegree⟩ := D.exists_collection_degree A
  have hcomm : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      ⁅(X i).range, (X j).range⁆ ≤
        ⨆ k ∈ {k ∈ S | max (degree i) (degree j) < degree k}, (X k).range := by
    intro i hi j hj hij
    exact hdegree i ((mem_posRootsFinset _ _ i).mp hi)
      j ((mem_posRootsFinset _ _ j).mp hj) hij
  have hwhole : D.positiveSubgroup A = ⨆ γ ∈ S, (X γ).range := by
    have hjoin : (⨆ γ ∈ S, (X γ).range) =
        Subgroup.closure (⋃ γ ∈ S, Set.range (X γ)) := by
      simp only [← MonoidHom.coe_range, Subgroup.closure_iUnion, Subgroup.closure_eq]
    rw [hjoin, D.positiveSubgroup_eq_closure]
    congr 1
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_range, S, mem_posRootsFinset, X,
      exists_prop]
  have hlS : ∀ γ, γ ∈ l ↔ γ ∈ S := by simpa only [S, mem_posRootsFinset] using hcover
  rw [hwhole, TauCeti.mem_biSup_iff_exists_list_prod_map hcomm hl hlS]
  constructor
  · rintro ⟨f, hf, hprod⟩
    choose u hu using hf
    refine ⟨u, ?_⟩
    calc
      _ = (l.map f).prod := congrArg List.prod (List.map_congr_left fun γ _ => hu γ)
      _ = g := hprod
  · rintro ⟨u, hu⟩
    exact ⟨fun γ => X γ (u γ), fun γ => ⟨u γ, rfl⟩, hu⟩

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
