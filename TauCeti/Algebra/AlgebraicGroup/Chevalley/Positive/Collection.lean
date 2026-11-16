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
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Collection.NotG2
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.G2.Rational
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.WeightDegree
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Positive.Coordinates.G2

/-!
# Positive-root ordered products for Chevalley data

For any valid Dynkin type and any Chevalley datum over any commutative ring, every element of
the positive-root subgroup is a product with one factor from each positive root subgroup, in
any prescribed enumeration without repetition. This is the existence part of positive-root
coordinates, not their uniqueness or a point-generation theorem for the whole Chevalley group.

In simply laced types, the commutator formula puts the commutator of two positive root
elements in the root group at their sum, whose height is strictly greater, so
`TauCeti.mem_biSup_iff_exists_list_prod_map` collects the factors directly on the admissible
lattice. Combining the non-`G₂` collection theorem with the `G₂` ordered-product theorem
yields `ChevalleyDatum.mem_positivePoints_iff_exists_list_prod` uniformly for every valid
Dynkin type and hence `ChevalleyDatum.exists_mul_eq_of_mem_positivePoints`, which factors any
positive point across an arbitrary partition of the positive roots.

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

/-- In simply laced types every element of the positive subgroup has a root-product expression.
The list enumerates all positive roots without repetition, in any order; no field or
characteristic restriction is needed. -/
theorem mem_positiveSubgroup_iff_exists_prod_of_isSimplyLaced (hs : t.IsSimplyLaced)
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
    exact D.commutator_range_root_le_iSup_height hs A i j
      ((mem_posRootsFinset _ _ i).mp hi) ((mem_posRootsFinset _ _ j).mp hj)
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

/-- For every valid Dynkin type and every commutative ring, an element of `D.points A` lies
in the positive subgroup if and only if it is an ordered product with one factor per positive
root in any prescribed duplicate-free enumeration. -/
theorem mem_positivePoints_iff_exists_list_prod (A : Type v) [CommRing A]
    (l : List (Fin t.numRoots)) (hl : l.Nodup)
    (hcover : ∀ γ, γ ∈ l ↔ γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht))
    (g : D.points A) :
    g ∈ D.positivePoints A ↔ ∃ u : Fin t.numRoots → A,
      (l.map fun γ => D.rootSubgroupPoints γ A (Multiplicative.ofAdd (u γ))).prod = g := by
  classical
  by_cases htG2 : t = G2
  · subst t
    let cast6 : Fin 6 → Fin G2.numRoots := Fin.castAdd 6
    let l₆ : List (Fin 6) := l.attach.map fun ⟨γ, hγ⟩ =>
      ⟨γ.val, (mem_posRoots_rational_g2_iff ht γ).mp ((hcover γ).mp hγ)⟩
    have hl₆_map : l₆.map cast6 = l := by
      dsimp only [l₆]
      rw [List.map_map]
      have hcomp : (cast6 ∘ fun x : {γ // γ ∈ l} => ⟨x.1.val,
          (mem_posRoots_rational_g2_iff ht x.1).mp ((hcover x.1).mp x.2)⟩) = Subtype.val := by
        funext x
        apply Fin.ext
        rfl
      rw [hcomp, List.attach_map_subtype_val]
    have hl₆ : l₆.Nodup := (hl₆_map.symm ▸ hl).of_map cast6
    have hcover₆ : ∀ i : Fin 6, i ∈ l₆ := by
      intro i
      have hmem : cast6 i ∈ l :=
        (hcover (cast6 i)).mpr ((mem_posRoots_rational_g2_iff ht _).mpr i.isLt)
      rw [← hl₆_map, List.mem_map] at hmem
      obtain ⟨j, hj, hij⟩ := hmem
      exact (Fin.castAdd_injective 6 6 hij) ▸ hj
    rw [D.mem_positivePoints_iff_exists_prod_G2 A l₆ hl₆ hcover₆ g]
    have hmap_prod (f : Fin G2.numRoots → D.points A) :
        (l.map f).prod = (l₆.map fun i => f (cast6 i)).prod := by
      rw [← hl₆_map, List.map_map]
      rfl
    constructor
    · rintro ⟨u, hu⟩
      refine ⟨fun γ => if h : γ.val < 6 then u ⟨γ.val, h⟩ else 0, ?_⟩
      rw [hmap_prod]
      simpa only [cast6, Fin.val_castAdd, Fin.is_lt, ↓reduceDIte, Fin.eta] using hu
    · rintro ⟨u, hu⟩
      refine ⟨fun i => u (cast6 i), ?_⟩
      exact (hmap_prod (fun γ => D.rootSubgroupPoints γ A (Multiplicative.ofAdd (u γ)))).symm.trans
        hu
  · have := isNotG2_rationalRootSystem_of_ne_G2 (ht := ht) htG2
    constructor
    · intro hg
      obtain ⟨v, hv, hvg⟩ := Subgroup.mem_map.mp (D.mem_positivePoints_iff.mp hg)
      rw [D.positiveSubgroup_eq_iSup] at hv
      obtain ⟨u, hu⟩ := (mem_iSup_posRoots_chevalleyRootSubgroup_iff_exists_list_prod
        D.representation D.lattice D.representation_mem_lattice
        D.isNilpotent_representation_rootGenerator (CommAlgCat.of ℤ A) l hl hcover v).mp hv
      refine ⟨u, (D.points A).subtype_injective ?_⟩
      let m := Units.map (LinearMap.toMatrixAlgEquiv (D.basis.baseChange A)).toMonoidHom
      calc
        _ = m ((l.map fun γ => chevalleyRootSubgroup D.representation D.lattice
            D.representation_mem_lattice D.isNilpotent_representation_rootGenerator
            γ (CommAlgCat.of ℤ A) (Multiplicative.ofAdd (u γ))).prod) := by
          simp only [map_list_prod, List.map_map, Function.comp_def, Subgroup.subtype_apply]
          exact congrArg List.prod (List.map_congr_left fun γ _ =>
            D.coe_rootSubgroupPoints γ A (Multiplicative.ofAdd (u γ)))
        _ = m v := congrArg m hu
        _ = _ := hvg
    · rintro ⟨u, rfl⟩
      apply Subgroup.list_prod_mem
      intro x hx
      obtain ⟨γ, hγ, rfl⟩ := List.mem_map.mp hx
      exact D.rootSubgroupPoints_mem_positivePoints A ((hcover γ).mp hγ) _

/-- Any partition of the positive roots by a predicate factors every positive point as a
product of an element generated by the roots satisfying the predicate and an element
generated by the remaining positive roots. -/
theorem exists_mul_eq_of_mem_positivePoints (A : Type v) [CommRing A]
    (p : Fin t.numRoots → Prop) {g : D.points A} (hg : g ∈ D.positivePoints A) :
    ∃ u₁ ∈ (⨆ γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht) ∩ {γ | p γ},
        (D.rootSubgroupPoints γ A).range : Subgroup (D.points A)),
      ∃ u₂ ∈ (⨆ γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht) ∩ {γ | ¬ p γ},
        (D.rootSubgroupPoints γ A).range : Subgroup (D.points A)),
        u₁ * u₂ = g := by
  classical
  let S := posRootsFinset (t.rationalRootSystem ht) (t.rationalBase ht)
  let l₁ := (S.filter p).toList
  let l₂ := (S.filter fun γ => ¬ p γ).toList
  have hl : (l₁ ++ l₂).Nodup := by
    rw [List.nodup_append]
    refine ⟨Finset.nodup_toList _, Finset.nodup_toList _, fun a ha b hb hab => ?_⟩
    subst hab
    have h1 := (Finset.mem_filter.mp (Finset.mem_toList.mp ha)).2
    have h2 := (Finset.mem_filter.mp (Finset.mem_toList.mp hb)).2
    exact h2 h1
  have hcover : ∀ γ, γ ∈ l₁ ++ l₂ ↔
      γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht) := by
    intro γ
    simp only [l₁, l₂, List.mem_append, Finset.mem_toList, Finset.mem_filter, S,
      mem_posRootsFinset]
    by_cases hp : p γ <;> simp [hp]
  obtain ⟨u, hu⟩ := (D.mem_positivePoints_iff_exists_list_prod A (l₁ ++ l₂) hl hcover g).mp hg
  rw [List.map_append, List.prod_append] at hu
  refine ⟨_, Subgroup.list_prod_mem _ fun x hx => ?_,
    _, Subgroup.list_prod_mem _ fun x hx => ?_, hu⟩
  · obtain ⟨γ, hγ, rfl⟩ := List.mem_map.mp hx
    have hγ' := Finset.mem_filter.mp (Finset.mem_toList.mp hγ)
    exact (le_iSup₂ (f := fun γ _ => (D.rootSubgroupPoints γ A).range) γ
      ⟨(mem_posRootsFinset _ _ γ).mp hγ'.1, hγ'.2⟩) ⟨_, rfl⟩
  · obtain ⟨γ, hγ, rfl⟩ := List.mem_map.mp hx
    have hγ' := Finset.mem_filter.mp (Finset.mem_toList.mp hγ)
    exact (le_iSup₂ (f := fun γ _ => (D.rootSubgroupPoints γ A).range) γ
      ⟨(mem_posRootsFinset _ _ γ).mp hγ'.1, hγ'.2⟩) ⟨_, rfl⟩

end TauCeti.DynkinType.ChevalleyDatum
