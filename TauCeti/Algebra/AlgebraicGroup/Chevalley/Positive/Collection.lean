/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Positive.Basic
import TauCeti.Algebra.Group.Subgroup.OrderedProduct
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.NotG2
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Collection.NotG2
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Collection.G2
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.WeightDegree

/-!
# Collecting positive-root products across all Dynkin types

For any Chevalley datum of any valid Dynkin type, commutators of positive root subgroups lie in
the join of positive root subgroups of strictly larger root height, over every commutative ring.
Consequently, every element of the positive subgroup — and more generally of any upper height
ideal `{γ ∈ Φ⁺ | H ≤ height γ}` — is a product with one factor from each root subgroup in that
set, in any duplicate-free enumeration. No simply laced, full-weight, field, or characteristic
hypothesis is needed.

Outside `G₂`, `DynkinType.isNotG2_rationalRootSystem_of_ne_G2` supplies the `IsNotG2` bound
consumed by `DynkinType.commutator_range_chevalleyRootSubgroup_le`. In `G₂`, the native six-root
commutator filtration `DynkinType.commutator_range_chevalleyRootSubgroup_g2_le` refines the pinned
root height `1, 1, 2, 3, 4, 5`, so the same height bound holds uniformly across all types.

## Main results

* `TauCeti.DynkinType.ChevalleyDatum.commutator_range_root_le_iSup_height` and
  `TauCeti.DynkinType.ChevalleyDatum.commutator_range_rootSubgroupPoints_le_iSup_height`:
  commutators of positive root subgroups strictly raise root height.
* `TauCeti.DynkinType.ChevalleyDatum.mem_iSup_height_le_rootSubgroupPoints_iff_exists_prod`:
  ordered-product collection for any height-upper-set of positive root subgroups.
* `TauCeti.DynkinType.ChevalleyDatum.mem_positiveSubgroup_iff_exists_prod` and
  `TauCeti.DynkinType.ChevalleyDatum.mem_positivePoints_iff_exists_prod`: ordered-product
  collection for the positive subgroup of any Chevalley datum over any commutative ring.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemmas 15 and 17.
* R. W. Carter, *Simple Groups of Lie Type*, Theorems 5.2.2 and 5.3.3.
-/

public section

open scoped commutatorElement
open TensorProduct TauCeti.UniversalEnvelopingAlgebra

namespace TauCeti.DynkinType.ChevalleyDatum

universe v

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

attribute [local instance high] Algebra.toModule

private abbrev g2PosIdx (k : Fin 6) : Fin G2.numRoots :=
  ⟨k.val, lt_trans k.isLt (by decide : 6 < G2.numRoots)⟩

private theorem height_g2PosIdx (htG2 : G2.Valid) (k : Fin 6) :
    (G2.rationalBase htG2).height (g2PosIdx k) = max (k : ℤ) 1 := by
  have hadd (a b c : Fin 6)
      (hr : (G2.simplyConnectedRootDatum htG2).root (g2PosIdx c) =
        (G2.simplyConnectedRootDatum htG2).root (g2PosIdx a) +
          (G2.simplyConnectedRootDatum htG2).root (g2PosIdx b) := by
        ext r
        simp +instances only [g2PosIdx, simplyConnectedRootDatum_G2,
          g2SimplyConnectedRootDatum_root, numRoots, rank, Pi.add_apply, g2Root_apply]
        fin_cases r <;> decide) :
      (G2.rationalBase htG2).height (g2PosIdx c) =
        (G2.rationalBase htG2).height (g2PosIdx a) +
          (G2.rationalBase htG2).height (g2PosIdx b) := by
    have h := congrArg (G2.weightDegree htG2) hr
    rw [map_add, G2.weightDegree_root htG2, G2.weightDegree_root htG2,
      G2.weightDegree_root htG2] at h
    exact_mod_cast h
  have h0 : (G2.rationalBase htG2).height (g2PosIdx 0) = 1 := by
    have heq : g2PosIdx 0 = G2.simpleIndex htG2 ⟨0, by decide⟩ := Fin.ext (by simp)
    rw [heq]
    exact (G2.rationalBase htG2).height_one_of_mem_support (G2.simpleIndex_mem_support _)
  have h1 : (G2.rationalBase htG2).height (g2PosIdx 1) = 1 := by
    have heq : g2PosIdx 1 = G2.simpleIndex htG2 ⟨1, by decide⟩ := Fin.ext (by simp)
    rw [heq]
    exact (G2.rationalBase htG2).height_one_of_mem_support (G2.simpleIndex_mem_support _)
  have h2 : (G2.rationalBase htG2).height (g2PosIdx 2) = 2 := by rw [hadd 0 1 2, h0, h1]; rfl
  have h3 : (G2.rationalBase htG2).height (g2PosIdx 3) = 3 := by rw [hadd 0 2 3, h0, h2]; rfl
  have h4 : (G2.rationalBase htG2).height (g2PosIdx 4) = 4 := by rw [hadd 0 3 4, h0, h3]; rfl
  have h5 : (G2.rationalBase htG2).height (g2PosIdx 5) = 5 := by rw [hadd 1 4 5, h1, h4]; rfl
  fin_cases k
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5

/-- Commutators of positive root subgroups on a Chevalley datum's lattice lie in the join of
positive root subgroups of strictly greater root height, across all valid Dynkin types and
commutative value rings. -/
theorem commutator_range_root_le_iSup_height
    (A : CommAlgCat.{v} ℤ) {i j : Fin t.numRoots}
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
  by_cases hij : i = j
  · subst j
    refine Subgroup.commutator_le.mpr ?_
    rintro _ ⟨u, rfl⟩ _ ⟨w, rfl⟩
    have hcomm : Commute
        (chevalleyRootSubgroup D.representation D.lattice D.representation_mem_lattice
          D.isNilpotent_representation_rootGenerator i A u)
        (chevalleyRootSubgroup D.representation D.lattice D.representation_mem_lattice
          D.isNilpotent_representation_rootGenerator i A w) := by
      rw [Commute, SemiconjBy, ← map_mul, ← map_mul, mul_comm]
    rw [hcomm.commutator_eq]
    exact Subgroup.one_mem _
  · by_cases htG2 : t = G2
    · subst t
      let i₆ : Fin 6 := ⟨i.val, (mem_posRoots_rational_g2_iff ht i).mp hi⟩
      let j₆ : Fin 6 := ⟨j.val, (mem_posRoots_rational_g2_iff ht j).mp hj⟩
      have hij₆ : i₆ ≠ j₆ := fun h => hij (Fin.ext (congrArg (fun x : Fin 6 => x.val) h))
      have hi_cast : (Fin.castAdd 6 i₆ : Fin G2.numRoots) = i := Fin.ext rfl
      have hj_cast : (Fin.castAdd 6 j₆ : Fin G2.numRoots) = j := Fin.ext rfl
      have hi_pos : g2PosIdx i₆ = i := Fin.ext rfl
      have hj_pos : g2PosIdx j₆ = j := Fin.ext rfl
      have hcomm := commutator_range_chevalleyRootSubgroup_g2_le D.representation D.lattice
        D.representation_mem_lattice D.isNilpotent_representation_rootGenerator A i₆ j₆ hij₆
      rw [hi_cast, hj_cast] at hcomm
      refine hcomm.trans ?_
      refine iSup₂_le fun k hk => le_iSup₂_of_le (g2PosIdx k) ?_ le_rfl
      rw [Finset.mem_filter, mem_posRootsFinset]
      refine ⟨(mem_posRoots_rational_g2_iff ht _).mpr k.isLt, ?_⟩
      rw [← hi_pos, ← hj_pos, height_g2PosIdx ht i₆, height_g2PosIdx ht j₆, height_g2PosIdx ht k]
      have hne : (i₆ : ℕ) ≠ (j₆ : ℕ) := Fin.val_ne_of_ne hij₆
      have hlt1 : (i₆ : ℕ) < (k : ℕ) := lt_of_le_of_lt (le_max_left i₆ j₆) hk
      have hlt2 : (j₆ : ℕ) < (k : ℕ) := lt_of_le_of_lt (le_max_right i₆ j₆) hk
      omega
    · have := isNotG2_rationalRootSystem_of_ne_G2 (ht := ht) htG2
      exact commutator_range_chevalleyRootSubgroup_le D.representation D.lattice
        D.representation_mem_lattice D.isNilpotent_representation_rootGenerator hi hj A

/-- Commutators of positive root-subgroup homomorphisms in the datum point group lie in the join
of positive root subgroups of strictly greater root height. -/
theorem commutator_range_rootSubgroupPoints_le_iSup_height
    (A : Type v) [CommRing A] {i j : Fin t.numRoots}
    (hi : i ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht))
    (hj : j ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht)) :
    ⁅(D.rootSubgroupPoints i A).range, (D.rootSubgroupPoints j A).range⁆ ≤
      ⨆ k ∈ {k ∈ posRootsFinset (t.rationalRootSystem ht) (t.rationalBase ht) |
        max ((t.rationalBase ht).height i) ((t.rationalBase ht).height j) <
          (t.rationalBase ht).height k},
        (D.rootSubgroupPoints k A).range := by
  classical
  let m := Units.map (LinearMap.toMatrixAlgEquiv (D.basis.baseChange A)).toMonoidHom
  let X := fun γ => chevalleyRootSubgroup D.representation D.lattice
    D.representation_mem_lattice D.isNilpotent_representation_rootGenerator γ (CommAlgCat.of ℤ A)
  let P := ⨆ k ∈ {k ∈ posRootsFinset (t.rationalRootSystem ht) (t.rationalBase ht) |
    max ((t.rationalBase ht).height i) ((t.rationalBase ht).height j) <
      (t.rationalBase ht).height k}, (D.rootSubgroupPoints k A).range
  have hle : (⨆ k ∈ {k ∈ posRootsFinset (t.rationalRootSystem ht) (t.rationalBase ht) |
      max ((t.rationalBase ht).height i) ((t.rationalBase ht).height j) <
        (t.rationalBase ht).height k}, (X k).range) ≤
      (P.map (D.points A).subtype).comap m := by
    refine iSup₂_le fun k hk => ?_
    rintro _ ⟨u, rfl⟩
    refine Subgroup.mem_comap.mpr ⟨D.rootSubgroupPoints k A u, ?_, D.coe_rootSubgroupPoints k A u⟩
    exact le_iSup₂ (f := fun k _ => (D.rootSubgroupPoints k A).range) k hk ⟨u, rfl⟩
  refine Subgroup.commutator_le.mpr ?_
  rintro _ ⟨u, rfl⟩ _ ⟨w, rfl⟩
  have hmem := hle (D.commutator_range_root_le_iSup_height (CommAlgCat.of ℤ A) hi hj
    (Subgroup.commutator_mem_commutator ⟨u, rfl⟩ ⟨w, rfl⟩))
  obtain ⟨g, hg, hgm⟩ := Subgroup.mem_map.mp (Subgroup.mem_comap.mp hmem)
  have heq : g = ⁅D.rootSubgroupPoints i A u, D.rootSubgroupPoints j A w⁆ := by
    apply (D.points A).subtype_injective
    rw [hgm, map_commutatorElement, map_commutatorElement (D.points A).subtype,
      Subgroup.coe_subtype, D.coe_rootSubgroupPoints, D.coe_rootSubgroupPoints]
    rfl
  exact heq ▸ hg

/-- Every element in the join of positive root subgroups of height at least `H` has an ordered
product expression in any duplicate-free enumeration of those roots. -/
theorem mem_iSup_height_le_rootSubgroupPoints_iff_exists_prod
    (H : ℤ) (l : List (Fin t.numRoots)) (hl : l.Nodup)
    (hcover : ∀ γ, γ ∈ l ↔
      γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht) ∧
        H ≤ (t.rationalBase ht).height γ)
    (A : Type v) [CommRing A] (g : D.points A) :
    g ∈ (⨆ γ ∈ {γ ∈ posRootsFinset (t.rationalRootSystem ht) (t.rationalBase ht) |
        H ≤ (t.rationalBase ht).height γ},
          (D.rootSubgroupPoints γ A).range) ↔
      ∃ u : Fin t.numRoots → Multiplicative A,
        (l.map fun γ => D.rootSubgroupPoints γ A (u γ)).prod = g := by
  classical
  let S := {γ ∈ posRootsFinset (t.rationalRootSystem ht) (t.rationalBase ht) |
    H ≤ (t.rationalBase ht).height γ}
  have hcomm : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      ⁅(D.rootSubgroupPoints i A).range, (D.rootSubgroupPoints j A).range⁆ ≤
        ⨆ k ∈ {k ∈ S | max ((t.rationalBase ht).height i) ((t.rationalBase ht).height j) <
          (t.rationalBase ht).height k}, (D.rootSubgroupPoints k A).range := by
    intro i hi j hj _
    have hi' := Finset.mem_filter.mp hi
    have hj' := Finset.mem_filter.mp hj
    refine (D.commutator_range_rootSubgroupPoints_le_iSup_height A
      ((mem_posRootsFinset _ _ i).mp hi'.1) ((mem_posRootsFinset _ _ j).mp hj'.1)).trans ?_
    refine iSup₂_le fun k hk => le_iSup₂_of_le k ?_ le_rfl
    have hk' := Finset.mem_filter.mp hk
    have _ := hi'.2
    have hlt := hk'.2
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hk'.1, by omega⟩, hlt⟩
  have hlS : ∀ γ, γ ∈ l ↔ γ ∈ S := fun γ => by
    simp only [S, Finset.mem_filter, mem_posRootsFinset, hcover]
  rw [TauCeti.mem_biSup_iff_exists_list_prod_map hcomm hl hlS]
  constructor
  · rintro ⟨f, hf, hprod⟩
    choose u hu using hf
    refine ⟨u, ?_⟩
    calc
      _ = (l.map f).prod := congrArg List.prod (List.map_congr_left fun γ _ => hu γ)
      _ = g := hprod
  · rintro ⟨u, hu⟩
    exact ⟨fun γ => D.rootSubgroupPoints γ A (u γ), fun γ => ⟨u γ, rfl⟩, hu⟩

/-- Every element of the positive lattice subgroup of a Chevalley datum has an ordered root-product
expression in any duplicate-free enumeration of the positive roots, across all valid Dynkin types
and commutative value rings. -/
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
  have hcomm : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      ⁅(X i).range, (X j).range⁆ ≤
        ⨆ k ∈ {k ∈ S | max ((t.rationalBase ht).height i) ((t.rationalBase ht).height j) <
          (t.rationalBase ht).height k}, (X k).range := by
    intro i hi j hj _
    exact D.commutator_range_root_le_iSup_height A
      ((mem_posRootsFinset _ _ i).mp hi) ((mem_posRootsFinset _ _ j).mp hj)
  have hwhole : D.positiveSubgroup A = ⨆ γ ∈ S, (X γ).range := by
    rw [D.positiveSubgroup_eq_iSup]
    simp only [S, mem_posRootsFinset, X]
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

/-- Every element of the positive point subgroup of a Chevalley datum is an ordered product of
positive root elements in any duplicate-free enumeration of the positive roots, over any
commutative value ring. -/
theorem mem_positivePoints_iff_exists_prod
    (l : List (Fin t.numRoots)) (hl : l.Nodup)
    (hcover : ∀ γ, γ ∈ l ↔ γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht))
    (A : Type v) [CommRing A] (g : D.points A) :
    g ∈ D.positivePoints A ↔ ∃ u : Fin t.numRoots → Multiplicative A,
      (l.map fun γ => D.rootSubgroupPoints γ A (u γ)).prod = g := by
  have hwhole : D.positivePoints A =
      ⨆ γ ∈ {γ ∈ posRootsFinset (t.rationalRootSystem ht) (t.rationalBase ht) |
        1 ≤ (t.rationalBase ht).height γ},
        (D.rootSubgroupPoints γ A).range := by
    rw [D.positivePoints_eq_iSup]
    apply le_antisymm
    · refine iSup₂_le fun γ hγ => le_iSup₂_of_le γ ?_ le_rfl
      exact Finset.mem_filter.mpr ⟨(mem_posRootsFinset _ _ γ).mpr hγ,
        one_le_height_of_mem_posRoots _ _ hγ⟩
    · refine iSup₂_le fun γ hγ => le_iSup₂_of_le γ ?_ le_rfl
      exact (mem_posRootsFinset _ _ γ).mp (Finset.mem_filter.mp hγ).1
  rw [hwhole]
  exact D.mem_iSup_height_le_rootSubgroupPoints_iff_exists_prod 1 l hl
    (fun γ => (hcover γ).trans
      ⟨fun hγ => ⟨hγ, one_le_height_of_mem_posRoots _ _ hγ⟩, fun h => h.1⟩) A g

end TauCeti.DynkinType.ChevalleyDatum
