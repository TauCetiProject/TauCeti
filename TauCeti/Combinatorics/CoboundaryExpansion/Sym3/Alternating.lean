/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.CoboundaryExpansion.FinFour
public import Mathlib.GroupTheory.SpecificGroups.Alternating
import TauCeti.Combinatorics.CoboundaryExpansion.StarBound
import Mathlib.Tactic.Linarith

/-!
# The four-vertex coboundary constant with alternating coefficients

The alternating subgroup of the permutations of three points has counting coboundary
constant `3 / 2` on the complete complex on four vertices. After applying a star gauge
at vertex `0`, only the three edges opposite that vertex can have nonidentity values.
A cochain carrying a three-cycle and its inverse on two of those edges attains the bound.

## References

* Jeromie Beasley, *The Permutation Coboundary Constant of the Complete Complex Is k/3
  for Every k≥4*, version 7, doi:10.5281/zenodo.23245792, Proposition 5 and §3.1.
-/

public section

open Equiv Equiv.Perm

namespace TauCeti

open TwoComplex Cochain

local notation "A₃" => alternatingGroup (Fin 3)
local notation "ℓ₃" => GroupNorm.comp (movedNorm (Fin 3)) (Subgroup.subtype_injective A₃)

/-- The finite gauge bound after the three edges incident to vertex zero have been trivialized.
Here `a, b, c` label the edges `12, 13, 23`, and `x, y, z` are the gauge values at `1, 2, 3`. -/
private theorem exists_alternating_gauge_labels :
    ∀ a b c : A₃, ∃ x y z : A₃,
      3 * ((x : Perm (Fin 3)).support.card + (y : Perm (Fin 3)).support.card +
        (z : Perm (Fin 3)).support.card + ((x⁻¹ * a * y : A₃) : Perm (Fin 3)).support.card +
        ((x⁻¹ * b * z : A₃) : Perm (Fin 3)).support.card +
        ((y⁻¹ * c * z : A₃) : Perm (Fin 3)).support.card) ≤
      2 * ((a : Perm (Fin 3)).support.card + (b : Perm (Fin 3)).support.card +
        (c : Perm (Fin 3)).support.card + ((a * c * b⁻¹ : A₃) : Perm (Fin 3)).support.card) := by
  decide +kernel

private theorem three_mul_gaugeDist_le_two_mul_defect_alternating
    (α : Cochain (complete (Fin 4)) A₃) :
    3 * α.gaugeDist ℓ₃ ≤ 2 * α.defect ℓ₃ := by
  let γ := α.starGauge 0
  let η := γ • α
  have hzero (v : Fin 4) : η 0 v = 1 :=
    (α.starGauge_smul_apply_complete 0 0 v).trans (α.holonomy_self_left 0 v)
  obtain ⟨x, y, z, h⟩ := exists_alternating_gauge_labels (η 1 2) (η 1 3) (η 2 3)
  let β : Fin 4 → A₃ := ![1, x, y, z]
  have hcost : 3 * η.cost ℓ₃ β ≤ 2 * η.defect ℓ₃ := by
    rw [cost_complete_fin_four, defect_complete_fin_four]
    simp only [β, Matrix.cons_val, holonomy_def, η.apply_swap 0 2, η.apply_swap 0 3,
      η.apply_swap 1 3, hzero, inv_one, one_mul, mul_one, GroupNorm.comp_apply,
      Subgroup.subtype_apply, movedNorm_apply]
    exact_mod_cast h
  rw [← gaugeDist_smul ℓ₃ α γ,
    ← defect_smul (GroupNorm.isConjInvariant_comp isConjInvariant_movedNorm _) α γ]
  exact (mul_le_mul_of_nonneg_left (η.gaugeDist_le_cost ℓ₃ β) (by norm_num)).trans hcost

local notation "c₃" =>
  (Subtype.mk (finRotate 3) (finRotate_bit1_mem_alternatingGroup (n := 1)) : A₃)

/-- The alternating cochain with opposite three-cycles on edges `13` and `23`. -/
private noncomputable def alternatingWitness : Cochain (complete (Fin 4)) A₃ :=
  .ofLt _ fun u v =>
    if u = 1 ∧ v = 3 then c₃ else if u = 2 ∧ v = 3 then c₃⁻¹ else 1

private theorem defect_alternatingWitness : alternatingWitness.defect ℓ₃ = 9 := by
  rw [defect_complete_fin_four]
  simp only [holonomy_def, alternatingWitness.apply_swap 0 2, alternatingWitness.apply_swap 0 3,
    alternatingWitness.apply_swap 1 3]
  norm_num [alternatingWitness, ofLt_apply_of_lt, adj_complete, GroupNorm.comp_apply,
    movedNorm_apply]
  norm_cast

private theorem cost_alternatingWitness_one : alternatingWitness.cost ℓ₃ 1 = 6 := by
  rw [cost_complete_fin_four]
  norm_num [alternatingWitness, ofLt_apply_of_lt, adj_complete, GroupNorm.comp_apply,
    movedNorm_apply]

/-- A gauge pinned at vertex zero leaves at least six moved points on the witness. -/
private theorem six_le_cost_alternatingWitness (β : Fin 4 → A₃) (hβ : β 0 = 1) :
    6 ≤ alternatingWitness.cost ℓ₃ β := by
  have h : ∀ x y z : A₃,
      6 ≤ (x : Perm (Fin 3)).support.card + (y : Perm (Fin 3)).support.card +
        (z : Perm (Fin 3)).support.card + ((x⁻¹ * y : A₃) : Perm (Fin 3)).support.card +
        ((x⁻¹ * c₃ * z : A₃) : Perm (Fin 3)).support.card +
        ((y⁻¹ * c₃⁻¹ * z : A₃) : Perm (Fin 3)).support.card := by decide
  rw [cost_complete_fin_four]
  norm_num [hβ, alternatingWitness, ofLt_apply_of_lt, adj_complete, GroupNorm.comp_apply,
    movedNorm_apply]
  exact_mod_cast h (β 1) (β 2) (β 3)

private theorem gaugeDist_alternatingWitness : alternatingWitness.gaugeDist ℓ₃ = 6 :=
  le_antisymm ((alternatingWitness.gaugeDist_le_cost ℓ₃ 1).trans_eq cost_alternatingWitness_one)
    ((alternatingWitness.le_gaugeDist_iff_apply_eq_one
      (GroupNorm.isConjInvariant_comp isConjInvariant_movedNorm _) 0).mpr
      six_le_cost_alternatingWitness)

/-- The alternating subgroup of `Equiv.Perm (Fin 3)`, with the restricted moved-point norm,
has counting coboundary constant `3 / 2` on the complete complex on four vertices. -/
theorem h1_complete_fin_four_alternating_group :
    h1 (complete (Fin 4)) ((movedNorm (Fin 3)).comp (alternatingGroup (Fin 3)).subtype_injective) =
      3 / 2 := by
  have hpos : 0 < alternatingWitness.gaugeDist ℓ₃ := by
    rw [gaugeDist_alternatingWitness]
    norm_num
  refine le_antisymm ((h1_le_div hpos).trans_eq ?_) (le_h1_of_forall ⟨alternatingWitness, hpos⟩ ?_)
  · rw [defect_alternatingWitness, gaugeDist_alternatingWitness]
    norm_num
  · intro α hα
    rw [le_div_iff₀ hα]
    linarith [three_mul_gaugeDist_le_two_mul_defect_alternating α]

end TauCeti
