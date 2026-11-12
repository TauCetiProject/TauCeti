/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Subgroup
public import TauCeti.Algebra.Group.Subgroup.OrderedProduct
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.G2.Rational
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Commutator.Basic
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Commutator.G2.ShortLong
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Commutator.G2.ShortPair

/-!
# Collecting the positive root subgroups in type G₂

On any Kostant-stable lattice with nilpotent simple root operators, the six positive root
subgroups of type G₂ admit an ordered-product expression in any order, over every commutative
ring. The indices are the first six entries of the native root table: the two simple roots,
then their sum, then the roots of heights three, four and five. The generated subgroup is
identified with the supremum indexed by `posRoots` of the rational system. No coordinate
uniqueness or scheme-theoretic point-generation assertion is made.

The commutator formulas for the short–long and short–short pairs, together with the one-factor
formula and commuting pairs, show that commutators strictly increase this table index. Thus
`TauCeti.mem_biSup_iff_exists_list_prod_map` applies. In particular, neither two nor three has
to be inverted in the value ring. The root formulas used here are those of the imported native
Chevalley commutator development; the collection argument is the graded-subgroup construction
in `TauCeti.Algebra.Group.Subgroup.OrderedProduct`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemmas 15 and 17.
* R. W. Carter, *Simple Groups of Lie Type*, Theorems 5.2.2 and 5.3.3.
-/

public section

namespace TauCeti.DynkinType

open TensorProduct TauCeti.UniversalEnvelopingAlgebra
open scoped commutatorElement

noncomputable section

variable {ht : G2.Valid} {V : Type*} [AddCommGroup V] [Module ℚ V]
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ (G2.lieAlgebra ht) →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ z ∈ kostantForm (G2.lieBasis ht).rootGenerator (G2.lieBasis ht).h,
  ∀ v ∈ M, ρ z v ∈ M)
variable (hnil : ∀ r, IsNilpotent
  (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ ((G2.lieBasis ht).rootGenerator r))))

attribute [local instance high] Algebra.toModule

-- The finite certificates repeatedly expose the same opaque root and length tables.
local macro "g2_table" : tactic => `(tactic|
  (try simp only [simplyConnectedRootDatum_G2, g2SimplyConnectedRootDatum_root, Set.mem_range]
   try dsimp +instances only [numRoots, rank]
   simp only [g2Root_apply, g2Length_apply]
   try dsimp +instances only [numRoots, rank]
   decide))

private theorem g2_positive_root_sum_pairs : ∀ i j : Fin 6, i < j →
    (G2.simplyConnectedRootDatum ht).root (Fin.castAdd 6 i) +
      (G2.simplyConnectedRootDatum ht).root (Fin.castAdd 6 j) ∈
        Set.range (G2.simplyConnectedRootDatum ht).root →
    (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨
      (i = 1 ∧ j = 4) ∨ (i = 2 ∧ j = 3) := by
  g2_table

private theorem g2_positive_root_add_ne_zero : ∀ i j : Fin 6,
    (G2.simplyConnectedRootDatum ht).root (Fin.castAdd 6 i) +
      (G2.simplyConnectedRootDatum ht).root (Fin.castAdd 6 j) ≠ 0 := by
  simp only [ne_eq, funext_iff, Pi.add_apply, Pi.zero_apply]
  g2_table

private theorem g2_positive_commutator_mem (A : CommAlgCat ℤ) (i j : Fin 6) (hij : i < j)
    (u v : A) :
    ⁅chevalleyRootSubgroup ρ M hM hnil (Fin.castAdd 6 i) A (Multiplicative.ofAdd u),
      chevalleyRootSubgroup ρ M hM hnil (Fin.castAdd 6 j) A (Multiplicative.ofAdd v)⁆ ∈
      ⨆ k : Fin 6, ⨆ (_ : j < k),
        (chevalleyRootSubgroup ρ M hM hnil (Fin.castAdd 6 k) A).range := by
  let X (k : Fin 6) := chevalleyRootSubgroup ρ M hM hnil (Fin.castAdd 6 k) A
  let P := ⨆ k : Fin 6, ⨆ (_ : j < k), (X k).range
  have mem (k : Fin 6) (hk : j < k) (a : A) : X k (Multiplicative.ofAdd a) ∈ P :=
    (le_iSup₂ (f := fun k _ => (X k).range) k hk) ⟨_, rfl⟩
  have one_factor (k : Fin 6) (hk : j < k)
      (hsum : (G2.simplyConnectedRootDatum ht).root (Fin.castAdd 6 k) =
        (G2.simplyConnectedRootDatum ht).root (Fin.castAdd 6 i) +
          (G2.simplyConnectedRootDatum ht).root (Fin.castAdd 6 j))
      (hleft : 2 • (G2.simplyConnectedRootDatum ht).root (Fin.castAdd 6 i) +
        (G2.simplyConnectedRootDatum ht).root (Fin.castAdd 6 j) ∉
          Set.range (G2.simplyConnectedRootDatum ht).root)
      (hright : (G2.simplyConnectedRootDatum ht).root (Fin.castAdd 6 i) +
        2 • (G2.simplyConnectedRootDatum ht).root (Fin.castAdd 6 j) ∉
          Set.range (G2.simplyConnectedRootDatum ht).root) :
      ⁅X i (Multiplicative.ofAdd u), X j (Multiplicative.ofAdd v)⁆ ∈ P := by
    rw [commutatorElement_chevalleyRootSubgroup_of_root_eq_add ρ M hM hnil
      hsum hleft hright]
    exact mem k hk _
  -- Three sum pairs use the one-factor formula, (0,1) the short–long formula,
  -- (0,2) the short–short formula; all other pairs commute.
  by_cases hsum : (G2.simplyConnectedRootDatum ht).root (Fin.castAdd 6 i) +
      (G2.simplyConnectedRootDatum ht).root (Fin.castAdd 6 j) ∈
        Set.range (G2.simplyConnectedRootDatum ht).root
  · rcases g2_positive_root_sum_pairs i j hij hsum with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · -- State the equality through X: elaboration normalizes both the formula's coefficient/
      -- function lets and its Fin G2.numRoots indices to the concrete Fin (6 + 6) indices.
      have h : ⁅X 0 (Multiplicative.ofAdd u), X 1 (Multiplicative.ofAdd v)⁆ = _ :=
        commutatorElement_chevalleyRootSubgroup_of_g2_short_long ρ M hM hnil
        (α := Fin.castAdd 6 (0 : Fin 6)) (β := Fin.castAdd 6 (1 : Fin 6))
        (γ := Fin.castAdd 6 (2 : Fin 6)) (δ := Fin.castAdd 6 (3 : Fin 6))
        (ε := Fin.castAdd 6 (4 : Fin 6)) (ζ := Fin.castAdd 6 (5 : Fin 6))
        (by g2_table) (by g2_table) (by g2_table) (by g2_table) A u v
      rw [h]
      exact P.mul_mem (P.mul_mem (P.mul_mem (mem 2 (by decide) _) (mem 3 (by decide) _))
        (mem 4 (by decide) _)) (mem 5 (by decide) _)
    · -- As above, normalize the coefficient lets and root-count indices in the equality's type.
      have h : ⁅X 0 (Multiplicative.ofAdd u), X 2 (Multiplicative.ofAdd v)⁆ = _ :=
        commutatorElement_chevalleyRootSubgroup_of_g2_short_pair ρ M hM hnil
        (i := Fin.castAdd 6 (0 : Fin 6)) (j := Fin.castAdd 6 (2 : Fin 6))
        (k := Fin.castAdd 6 (3 : Fin 6)) (l := Fin.castAdd 6 (4 : Fin 6))
        (m := Fin.castAdd 6 (5 : Fin 6))
        (by g2_table) (by g2_table) (by g2_table)
        (by g2_table) (by g2_table) (by g2_table) A u v
      rw [h]
      exact P.mul_mem (P.mul_mem (mem 3 (by decide) _) (mem 4 (by decide) _))
        (mem 5 (by decide) _)
    · exact one_factor 4 (by decide) (by g2_table) (by g2_table) (by g2_table)
    · exact one_factor 5 (by decide) (by g2_table) (by g2_table) (by g2_table)
    · exact one_factor 5 (by decide) (by g2_table) (by g2_table) (by g2_table)
  · have hc := commute_chevalleyRootSubgroup ρ M hM hnil hsum
      (g2_positive_root_add_ne_zero i j) A u v
    rw [commutatorElement_def, hc]
    simp

/-- Commutators of distinct positive G₂ root groups lie in root groups with strictly larger
native table indices. This grading works also in characteristics two and three. -/
theorem commutator_range_chevalleyRootSubgroup_g2_le
    (A : CommAlgCat ℤ) (i j : Fin 6) (hij : i ≠ j) :
    ⁅(chevalleyRootSubgroup ρ M hM hnil (Fin.castAdd 6 i) A).range,
      (chevalleyRootSubgroup ρ M hM hnil (Fin.castAdd 6 j) A).range⁆ ≤
      ⨆ k : Fin 6, ⨆ (_ : max i j < k),
        (chevalleyRootSubgroup ρ M hM hnil (Fin.castAdd 6 k) A).range := by
  have ordered (i j : Fin 6) (hij : i < j) :
      ⁅(chevalleyRootSubgroup ρ M hM hnil (Fin.castAdd 6 i) A).range,
        (chevalleyRootSubgroup ρ M hM hnil (Fin.castAdd 6 j) A).range⁆ ≤
        ⨆ k : Fin 6, ⨆ (_ : j < k),
          (chevalleyRootSubgroup ρ M hM hnil (Fin.castAdd 6 k) A).range := by
    apply Subgroup.commutator_le.mpr
    rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
    exact g2_positive_commutator_mem ρ M hM hnil A i j hij
      (Multiplicative.toAdd u) (Multiplicative.toAdd v)
  rcases lt_or_gt_of_ne hij with h | h
  · simpa only [max_eq_right (le_of_lt h)] using ordered i j h
  · rw [Subgroup.commutator_comm]
    simpa only [max_eq_left (le_of_lt h)] using ordered j i h

/-- The subgroup generated by the first six native `G₂` root groups is precisely the subgroup
indexed by the positive roots of the rational root system. -/
theorem iSup_range_chevalleyRootSubgroup_g2_eq_iSup_posRoots (A : CommAlgCat ℤ) :
    (⨆ i : Fin 6, (chevalleyRootSubgroup ρ M hM hnil (Fin.castAdd 6 i) A).range) =
      ⨆ γ ∈ posRoots (G2.rationalRootSystem ht) (G2.rationalBase ht),
        (chevalleyRootSubgroup ρ M hM hnil γ A).range := by
  apply le_antisymm
  · refine iSup_le fun i => le_iSup_of_le (Fin.castAdd 6 i) (le_iSup_of_le ?_ le_rfl)
    exact (mem_posRoots_rational_g2_iff ht _).mpr i.isLt
  · refine iSup₂_le fun γ hγ => ?_
    -- Rebuilding a Fin index from its value changes only its bound proof.
    exact le_iSup (fun i : Fin 6 =>
      (chevalleyRootSubgroup ρ M hM hnil (Fin.castAdd 6 i) A).range)
      ⟨γ, (mem_posRoots_rational_g2_iff ht γ).mp hγ⟩

/-- Every element generated by the six positive G₂ root groups is a product with one parameter
per positive root, in any prescribed duplicate-free enumeration. The six indices refer to the
existing root table, not a new enumeration of the root datum. -/
theorem mem_biSup_posRoots_g2_iff_exists_list_prod_map (A : CommAlgCat ℤ)
    (l : List (Fin 6)) (hl : l.Nodup) (hlall : ∀ i, i ∈ l)
    (g : LinearMap.GeneralLinearGroup A (A ⊗[ℤ] M)) :
    g ∈ (⨆ γ ∈ posRoots (G2.rationalRootSystem ht) (G2.rationalBase ht),
      (chevalleyRootSubgroup ρ M hM hnil γ A).range) ↔
      ∃ f : Fin 6 → A, (l.map fun i =>
        chevalleyRootSubgroup ρ M hM hnil (Fin.castAdd 6 i) A
          (Multiplicative.ofAdd (f i))).prod = g := by
  classical
  rw [← iSup_range_chevalleyRootSubgroup_g2_eq_iSup_posRoots ρ M hM hnil A]
  let X (i : Fin 6) := chevalleyRootSubgroup ρ M hM hnil (Fin.castAdd 6 i) A
  have hcomm (i : Fin 6) (_ : i ∈ (Finset.univ : Finset (Fin 6)))
      (j : Fin 6) (_ : j ∈ (Finset.univ : Finset (Fin 6))) (hij : i ≠ j) :
      ⁅(X i).range, (X j).range⁆ ≤
        ⨆ k ∈ {k ∈ (Finset.univ : Finset (Fin 6)) | max i j < k}, (X k).range := by
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
      commutator_range_chevalleyRootSubgroup_g2_le ρ M hM hnil A i j hij
  simpa only [Finset.mem_univ, iSup_true] using
    mem_biSup_range_iff_exists_list_prod_map (X := X) (ht := id) hcomm hl
      (fun i => by simp [hlall i]) (g := g)

end

end TauCeti.DynkinType
