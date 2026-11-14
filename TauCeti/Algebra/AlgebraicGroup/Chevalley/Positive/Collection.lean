/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Positive.Basic
import TauCeti.Algebra.Group.Subgroup.OrderedProduct
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Commutator.SimplyLaced
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Commutator.Basic
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.WeightDegree
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Collection.NotG2
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Collection.G2

/-!
# Positive-root products

For every Chevalley datum, every element of the positive-root subgroup is a product
with one factor from each positive root subgroup, in any enumeration without repetition.
This works on the admissible lattice over every commutative value ring. It is the existence
part of positive-root coordinates, not their uniqueness or a point-generation theorem for the
whole Chevalley group.

The simply laced commutator formula and the native collection bounds outside G₂ put
commutators in root groups of strictly greater height. In G₂ the existing positive-root table
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

private theorem commutator_range_root_le_iSup_height (hs : t.IsSimplyLaced)
    (A : CommAlgCat.{v} ℤ) (i j : Fin t.numRoots)
    (hi : i ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht))
    (hj : j ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht)) :
    ⁅(chevalleyRootSubgroup D.representation D.lattice D.representation_mem_lattice
        D.isNilpotent_representation_rootGenerator i A).range,
      (chevalleyRootSubgroup D.representation D.lattice D.representation_mem_lattice
        D.isNilpotent_representation_rootGenerator j A).range⁆ ≤
      ⨆ k ∈ {k ∈ posRootsFinset (t.rationalRootSystem ht) (t.rationalBase ht) |
        max ((t.rationalBase ht).height i) ((t.rationalBase ht).height j) <
          (t.rationalBase ht).height k},
        (chevalleyRootSubgroup D.representation D.lattice D.representation_mem_lattice
          D.isNilpotent_representation_rootGenerator k A).range := by
  classical
  let X := fun γ => chevalleyRootSubgroup D.representation D.lattice
    D.representation_mem_lattice D.isNilpotent_representation_rootGenerator γ A
  apply Subgroup.commutator_le.mpr
  rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
  by_cases hadd : (t.simplyConnectedRootDatum ht).root i +
      (t.simplyConnectedRootDatum ht).root j ∈ Set.range (t.simplyConnectedRootDatum ht).root
  · obtain ⟨k, hk⟩ := hadd
    have hheight : (t.rationalBase ht).height k =
        (t.rationalBase ht).height i + (t.rationalBase ht).height j := by
      have h := congrArg (t.weightDegree ht) hk
      simp only [map_add, weightDegree_root] at h
      exact_mod_cast h
    have hhi := one_le_height_of_mem_posRoots _ _ hi
    have hhj := one_le_height_of_mem_posRoots _ _ hj
    have hkpos : k ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht) := by
      rw [mem_posRoots, RootPairing.Base.isPos_iff]
      omega
    have hkS : k ∈ {k ∈ posRootsFinset (t.rationalRootSystem ht) (t.rationalBase ht) |
        max ((t.rationalBase ht).height i) ((t.rationalBase ht).height j) <
          (t.rationalBase ht).height k} := by
      simp only [Finset.mem_filter, mem_posRootsFinset]
      exact ⟨hkpos, by omega⟩
    have heq := commutatorElement_chevalleyRootSubgroup_of_isSimplyLaced D.representation
      D.lattice D.representation_mem_lattice D.isNilpotent_representation_rootGenerator
      hs hk A u.toAdd v.toAdd
    simp only [ofAdd_toAdd] at heq
    rw [heq]
    exact le_iSup₂ (f := fun k _ => (X k).range) k hkS ⟨_, rfl⟩
  · have hzero : (t.simplyConnectedRootDatum ht).root i +
        (t.simplyConnectedRootDatum ht).root j ≠ 0 := by
      intro hz
      have h := congrArg (t.weightDegree ht) hz
      have hdi := t.weightDegree_root_pos ht hi
      have hdj := t.weightDegree_root_pos ht hj
      simp only [map_add, map_zero] at h
      linarith
    have heq := (commute_chevalleyRootSubgroup D.representation D.lattice
      D.representation_mem_lattice D.isNilpotent_representation_rootGenerator
      hadd hzero A u.toAdd v.toAdd).commutator_eq
    simp only [ofAdd_toAdd] at heq
    rw [heq]
    exact Subgroup.one_mem _

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
  by_cases hs : t.IsSimplyLaced
  · exact ⟨(t.rationalBase ht).height,
      fun i hi j hj _ => D.commutator_range_root_le_iSup_height hs A i j hi hj⟩
  have outsideG2 [(t.rationalRootSystem ht).IsNotG2] (i j : Fin t.numRoots)
      (hi : i ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht))
      (hj : j ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht)) :=
    commutator_range_chevalleyRootSubgroup_le D.representation D.lattice
      D.representation_mem_lattice D.isNilpotent_representation_rootGenerator hi hj A
  cases t with
  | A n => exact (hs (isSimplyLaced_A n)).elim
  | D n => exact (hs (isSimplyLaced_D n)).elim
  | E6 => exact (hs (by trivial)).elim
  | E7 => exact (hs (by trivial)).elim
  | E8 => exact (hs (by trivial)).elim
  | B n => exact ⟨_, fun i hi j hj _ => outsideG2 i j hi hj⟩
  | C n => exact ⟨_, fun i hi j hj _ => outsideG2 i j hi hj⟩
  | F4 => exact ⟨_, fun i hi j hj _ => outsideG2 i j hi hj⟩
  | G2 =>
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

end TauCeti.DynkinType.ChevalleyDatum
