/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Commutator.Basic
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.B.RankTwo.Positive
import TauCeti.Algebra.Group.Subgroup.OrderedProduct

/-!
# Ordered products of positive B₂ root subgroups

The four positive root subgroups of the pinned B₂ datum admit product expressions in any
prescribed order, on every Kostant-stable lattice with nilpotent simple root operators and over
every commutative value ring. The indices are the first four entries of the native `b2Index`
table: the long simple root, the short simple root, their sum, and the highest root.

The two nontrivial positive-root commutators land in later entries of this table. The two-factor
formula is used integrally, so no division by two in the value ring is needed. In particular,
the result includes characteristic two and nonreduced rings. This is existence of root
coordinates, not uniqueness or generation by the two positive simple root groups.

We apply the graded collection theorem `TauCeti.mem_biSup_iff_exists_list_prod_map` to the
native Chevalley root homomorphisms. These product coordinates supply the positive unipotent
part of Bruhat normal forms.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemmas 15 and 17.
* R. W. Carter, *Simple Groups of Lie Type*, Theorems 5.2.2 and 5.3.3.
-/

public section

namespace TauCeti.DynkinType

open TensorProduct TauCeti.UniversalEnvelopingAlgebra
open scoped commutatorElement

noncomputable section

variable {ht : (B 2).Valid} {V : Type*} [AddCommGroup V] [Module ℚ V]
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ ((B 2).lieAlgebra ht) →ₐ[ℚ] Module.End ℚ V)
  (M : AddSubgroup V)
  (hM : ∀ u ∈ kostantForm ((B 2).lieBasis ht).rootGenerator ((B 2).lieBasis ht).h,
    ∀ v ∈ M, ρ u v ∈ M)
  (hnil : ∀ i, IsNilpotent
    (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (((B 2).lieBasis ht).rootGenerator i))))

attribute [local instance high] Algebra.toModule

private lemma b2_root_eq_nsmul_add (a b c : Fin 8) (n : ℕ)
    (h : b2Root c = n • b2Root a + b2Root b) :
    ((B 2).simplyConnectedRootDatum ht).root (b2Index c) =
      n • ((B 2).simplyConnectedRootDatum ht).root (b2Index a) +
        ((B 2).simplyConnectedRootDatum ht).root (b2Index b) := by
  simpa +instances only [simplyConnectedRootDatum_B, rank, numRoots, root_b2Index] using h

private lemma b2_nsmul_add_nsmul_not_mem_range (a b : Fin 8) (m n : ℕ)
    (h : m • b2Root a + n • b2Root b ∉ Set.range b2Root) :
    m • ((B 2).simplyConnectedRootDatum ht).root (b2Index a) +
        n • ((B 2).simplyConnectedRootDatum ht).root (b2Index b) ∉
      Set.range ((B 2).simplyConnectedRootDatum ht).root := by
  simpa +instances only [simplyConnectedRootDatum_B, rank, numRoots, root_b2Index,
    range_root_typeBSimplyConnectedRootDatum_two] using h

private theorem b2_positive_commutator_mem (A : CommAlgCat ℤ) (P : Subgroup
    (LinearMap.GeneralLinearGroup A (A ⊗[ℤ] M)))
    (i j : Fin 4) (hij : i < j)
    (hP : ∀ k : Fin 4, j < k →
      (chevalleyRootSubgroup ρ M hM hnil (b2Index (Fin.castAdd 4 k)) A).range ≤ P)
    (u v : A) :
    ⁅chevalleyRootSubgroup ρ M hM hnil (b2Index (Fin.castAdd 4 j)) A
        (Multiplicative.ofAdd u),
      chevalleyRootSubgroup ρ M hM hnil (b2Index (Fin.castAdd 4 i)) A
        (Multiplicative.ofAdd v)⁆ ∈ P := by
  by_cases h01 : i = 0 ∧ j = 1
  · rcases h01 with ⟨rfl, rfl⟩
    have hc := commutatorElement_chevalleyRootSubgroup_of_root_eq_two_nsmul_add
      (t := B 2) (ht := ht) (α := b2Index 1) (β := b2Index 0) ρ M hM hnil
      (γ := b2Index 2) (δ := b2Index 3)
      (by simpa only [one_smul] using b2_root_eq_nsmul_add (ht := ht) 1 0 2 1 (by decide))
      (b2_root_eq_nsmul_add 1 0 3 2 (by decide))
      (by simpa only [one_smul] using
        b2_nsmul_add_nsmul_not_mem_range (ht := ht) 1 0 3 1 (by decide))
      (by simpa only [one_smul] using
        b2_nsmul_add_nsmul_not_mem_range (ht := ht) 1 0 1 2 (by decide)) A u v
    exact hc.symm ▸ P.mul_mem (hP 2 (by decide) ⟨_, rfl⟩) (hP 3 (by decide) ⟨_, rfl⟩)
  by_cases h12 : i = 1 ∧ j = 2
  · rcases h12 with ⟨rfl, rfl⟩
    have hc := commutatorElement_chevalleyRootSubgroup_of_root_eq_add
      (t := B 2) (ht := ht) (α := b2Index 2) (β := b2Index 1) ρ M hM hnil
      (γ := b2Index 3)
      (by simpa only [one_smul] using b2_root_eq_nsmul_add (ht := ht) 2 1 3 1 (by decide))
      (by simpa only [one_smul] using
        b2_nsmul_add_nsmul_not_mem_range (ht := ht) 2 1 2 1 (by decide))
      (by simpa only [one_smul] using
        b2_nsmul_add_nsmul_not_mem_range (ht := ht) 2 1 1 2 (by decide)) A u v
    exact hc.symm ▸ hP 3 (by decide) ⟨_, rfl⟩
  have hz : b2Root (Fin.castAdd 4 j) + b2Root (Fin.castAdd 4 i) ∉ Set.range b2Root ∧
      b2Root (Fin.castAdd 4 j) + b2Root (Fin.castAdd 4 i) ≠ 0 := by
    revert hij h01 h12
    fin_cases i <;> fin_cases j <;> decide
  have hc := commutatorElement_eq_one_iff_commute.mpr
    (commute_chevalleyRootSubgroup ρ M hM hnil
      (by simpa only [one_smul] using
        (b2_nsmul_add_nsmul_not_mem_range (ht := ht) (Fin.castAdd 4 j) (Fin.castAdd 4 i)
          1 1 (by simpa only [one_smul] using hz.1)))
      (by
        simp +instances only [simplyConnectedRootDatum_B, rank, numRoots, root_b2Index]
        intro hzero
        apply hz.2
        funext k
        exact congrFun hzero k)
      A u v)
  exact hc.symm ▸ P.one_mem

/-- Commutators of distinct positive B₂ root groups lie in the group generated by roots later
than both inputs in the native positive-root table. This holds in every value ring. -/
theorem commutator_range_chevalleyRootSubgroup_b2_le (A : CommAlgCat ℤ)
    (i j : Fin 4) (hij : i ≠ j) :
    ⁅(chevalleyRootSubgroup ρ M hM hnil (b2Index (Fin.castAdd 4 i)) A).range,
      (chevalleyRootSubgroup ρ M hM hnil (b2Index (Fin.castAdd 4 j)) A).range⁆ ≤
    ⨆ k ∈ {k : Fin 4 | max i j < k},
      (chevalleyRootSubgroup ρ M hM hnil (b2Index (Fin.castAdd 4 k)) A).range := by
  have hordered (i j : Fin 4) (hij : i < j) :
      ⁅(chevalleyRootSubgroup ρ M hM hnil (b2Index (Fin.castAdd 4 j)) A).range,
        (chevalleyRootSubgroup ρ M hM hnil (b2Index (Fin.castAdd 4 i)) A).range⁆ ≤
      ⨆ k ∈ {k : Fin 4 | max i j < k},
        (chevalleyRootSubgroup ρ M hM hnil (b2Index (Fin.castAdd 4 k)) A).range := by
    apply Subgroup.commutator_le.mpr
    rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
    exact b2_positive_commutator_mem ρ M hM hnil A _ i j hij
      (fun k hk => le_iSup₂ (f := fun k (_ : max i j < k) =>
        (chevalleyRootSubgroup ρ M hM hnil (b2Index (Fin.castAdd 4 k)) A).range)
        k (by simpa only [max_eq_right hij.le] using hk)) u.toAdd v.toAdd
  rcases lt_or_gt_of_ne hij with h | h
  · rw [Subgroup.commutator_comm]
    exact hordered i j h
  · simpa only [max_comm j i] using hordered j i h

/-- Every element generated by the four positive B₂ root groups has an expression with one
additive parameter per root, in any duplicate-free enumeration of the native positive table.
Neither faithfulness of the representation nor a restriction on the characteristic is needed. -/
theorem mem_biSup_posRoots_b2_iff_exists_list_prod_map (A : CommAlgCat ℤ)
    {l : List (Fin 4)} (hl : l.Nodup) (hlall : ∀ i, i ∈ l)
    {g : LinearMap.GeneralLinearGroup A (A ⊗[ℤ] M)} :
    g ∈ (⨆ γ ∈ posRoots ((B 2).rationalRootSystem ht) ((B 2).rationalBase ht),
      (chevalleyRootSubgroup ρ M hM hnil γ A).range) ↔
    ∃ u : Fin 4 → A, (l.map fun i =>
      chevalleyRootSubgroup ρ M hM hnil (b2Index (Fin.castAdd 4 i)) A
        (Multiplicative.ofAdd (u i))).prod = g := by
  classical
  have hjoin :
      (⨆ γ ∈ posRoots (typeBSimplyConnectedRootDatum 2) (typeBSimplyConnectedBase 2),
        (chevalleyRootSubgroup ρ M hM hnil γ A).range) =
      ⨆ i : Fin 4,
        (chevalleyRootSubgroup ρ M hM hnil (b2Index (Fin.castAdd 4 i)) A).range := by
    apply le_antisymm
    · refine iSup₂_le fun γ hγ => ?_
      obtain ⟨k, rfl⟩ := b2Index_bijective.surjective γ
      have hk := (b2Index_mem_posRoots_iff k).mp hγ
      exact le_iSup_of_le ⟨k.val, hk⟩ le_rfl
    · exact iSup_le fun i => le_iSup₂_of_le _
        ((b2Index_mem_posRoots_iff _).mpr i.isLt) le_rfl
  have hpos : posRoots ((B 2).rationalRootSystem ht) ((B 2).rationalBase ht) =
      posRoots (typeBSimplyConnectedRootDatum 2) (typeBSimplyConnectedBase 2) := by
    rw [posRoots_rationalRootSystem]
    congr 1
    · exact simplyConnectedRootDatum_B 2 ht
    · exact eqRec_heq_iff.mp (heq_of_eq (simplyConnectedBase_B 2 ht))
  have hjoin' := (congrArg (fun S : Set (Fin (B 2).numRoots) =>
    ⨆ γ ∈ S, (chevalleyRootSubgroup ρ M hM hnil γ A).range) hpos).trans hjoin
  rw [hjoin']
  let X := fun i : Fin 4 =>
    chevalleyRootSubgroup ρ M hM hnil (b2Index (Fin.castAdd 4 i)) A
  have hc := mem_biSup_range_iff_exists_list_prod_map (X := X) (ht := id)
    (S := Finset.univ)
    (fun i _ j _ hij => by
      simpa only [Finset.mem_univ, iSup_true, Finset.mem_filter,
        true_and, id_eq, Set.mem_ofPred_eq] using
          commutator_range_chevalleyRootSubgroup_b2_le ρ M hM hnil A i j hij)
    hl (fun i => by simp [hlall i]) (g := g)
  simpa only [Finset.mem_univ, iSup_true] using hc

end

end TauCeti.DynkinType
