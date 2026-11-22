/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.CoboundaryExpansion.CheegerConstant
public import TauCeti.Combinatorics.CoboundaryExpansion.Cochain.SimpleGraph
public import TauCeti.GroupTheory.Perm.Basic
import TauCeti.Combinatorics.CoboundaryExpansion.SwapGauge
import TauCeti.Combinatorics.SimpleGraph.CutMinimal.OddTriple
import TauCeti.Combinatorics.SimpleGraph.OddTriple.Switching

/-!
# Binary and transposition-subgroup exactness and Cheeger constants on at most four vertices

On the complete complex `TauCeti.TwoComplex.complete V` with `Fintype.card V ≤ 4`, cut-switching
invariance of `oddTripleFinset` combined with the degree-`1` bound on cut-minimal graphs gives
`defect = (Fintype.card V - 2) * gaugeDist` for transposition graph cochains, `Subgroup.zpowers t`
cochains, and `Equiv.Perm (Fin 2)` cochains. Consequently, both the binary Cheeger constant
`TauCeti.h1 (TwoComplex.complete V) (Equiv.Perm.movedNorm (Fin 2))` and the Cheeger constant of
any transposition subgroup `Subgroup.zpowers t` equal `(Fintype.card V - 2 : ℕ)`. In particular, on
four vertices both evaluate to `2` (`TauCeti.h1_complete_movedNorm_fin_two_of_card_eq_four`,
`TauCeti.h1_complete_zpowers_swap_of_card_eq_four`).

## References

* D. N. Kozlov, *The first Cheeger constant of a simplex*, arXiv:1610.07136v2, Section 2.
* Jeromie Beasley, *The Permutation Coboundary Constant of the Complete Complex Is k/3 for Every
  k≥4*, version 7, doi:10.5281/zenodo.23245792, Corollary 7 and Theorem 8.
-/

public section

open scoped symmDiff

namespace SimpleGraph

/-- **Transposition exactness on at most four vertices**: on a vertex type of size at most four,
every graph `G` and every transposition `t` satisfy
`(G.toCochain ht.mul_self).defect (Equiv.Perm.movedNorm α) =
  ((Fintype.card V - 2 : ℕ) : ℝ) * (G.toCochain ht.mul_self).gaugeDist (Equiv.Perm.movedNorm α)`. -/
theorem defect_movedNorm_toCochain_eq_card_sub_two_mul_gaugeDist_of_card_le_four
    {V α : Type*} [Fintype V] [LinearOrder V] [Fintype α] [DecidableEq α]
    (G : SimpleGraph V) (hV : Fintype.card V ≤ 4) {t : Equiv.Perm α} (ht : t.IsSwap) :
    (G.toCochain ht.mul_self).defect (Equiv.Perm.movedNorm α) =
      ((Fintype.card V - 2 : ℕ) : ℝ) *
        (G.toCochain ht.mul_self).gaugeDist (Equiv.Perm.movedNorm α) := by
  classical
  obtain ⟨s, hs, hval⟩ := G.exists_finset_isCutMinimal_and_gaugeDist_movedNorm_toCochain_eq ht
  rw [G.defect_movedNorm_toCochain ht, hval, ← G.oddTripleFinset_symmDiff_top_between (s : Set V),
    hs.card_oddTripleFinset_of_card_le_four hV]
  push_cast
  ring

end SimpleGraph

namespace TauCeti

namespace Cochain

/-- **Subgroup cochain exactness on at most four vertices**: on a vertex type of size at most four,
every `Subgroup.zpowers t`-valued `1`-cochain `γ` on `TwoComplex.complete V` for a transposition `t`
satisfies `γ.defect ℓ = ((Fintype.card V - 2 : ℕ) : ℝ) * γ.gaugeDist ℓ` under the restricted
moved-point norm `ℓ := (Equiv.Perm.movedNorm α).comp (Subgroup.zpowers t).subtype_injective`. -/
theorem defect_zpowers_swap_eq_card_sub_two_mul_gaugeDist_of_card_le_four
    {V α : Type*} [Fintype V] [LinearOrder V] [Fintype α] [DecidableEq α]
    (hV : Fintype.card V ≤ 4) {t : Equiv.Perm α} (ht : t.IsSwap)
    (γ : Cochain (TwoComplex.complete V) (Subgroup.zpowers t)) :
    γ.defect ((Equiv.Perm.movedNorm α).comp (Subgroup.zpowers t).subtype_injective) =
      ((Fintype.card V - 2 : ℕ) : ℝ) *
        γ.gaugeDist ((Equiv.Perm.movedNorm α).comp (Subgroup.zpowers t).subtype_injective) := by
  obtain ⟨G, hmap⟩ := γ.exists_map_zpowers_subtype_eq_toCochain ht.mul_self
  rw [← γ.defect_map_subtype (Equiv.Perm.movedNorm α) (Subgroup.zpowers t),
    ← γ.gaugeDist_map_zpowers_subtype ht, hmap]
  exact G.defect_movedNorm_toCochain_eq_card_sub_two_mul_gaugeDist_of_card_le_four hV ht

/-- **Binary cochain exactness on at most four vertices**: on a vertex type of size at most four,
every `α : Cochain (TwoComplex.complete V) (Equiv.Perm (Fin 2))` satisfies
`α.defect (Equiv.Perm.movedNorm (Fin 2)) =
  ((Fintype.card V - 2 : ℕ) : ℝ) * α.gaugeDist (Equiv.Perm.movedNorm (Fin 2))`. -/
theorem defect_movedNorm_fin_two_eq_card_sub_two_mul_gaugeDist_of_card_le_four
    {V : Type*} [Fintype V] [LinearOrder V] (hV : Fintype.card V ≤ 4)
    (α : Cochain (TwoComplex.complete V) (Equiv.Perm (Fin 2))) :
    α.defect (Equiv.Perm.movedNorm (Fin 2)) =
      ((Fintype.card V - 2 : ℕ) : ℝ) * α.gaugeDist (Equiv.Perm.movedNorm (Fin 2)) := by
  let G := (simpleGraphEquivPermFinTwo V).symm α
  rw [← (simpleGraphEquivPermFinTwo V).apply_symm_apply α, simpleGraphEquivPermFinTwo_eq_toCochain]
  exact G.defect_movedNorm_toCochain_eq_card_sub_two_mul_gaugeDist_of_card_le_four hV
    (Equiv.Perm.swap_isSwap_iff.mpr Fin.zero_ne_one)

end Cochain

/-- On `TwoComplex.complete V` with `Fintype.card V ≤ 4`, the binary Cheeger constant
`h1 (TwoComplex.complete V) (Equiv.Perm.movedNorm (Fin 2))` equals `(Fintype.card V - 2 : ℕ)`. -/
theorem h1_complete_movedNorm_fin_two_of_card_le_four {V : Type*} [Fintype V] [LinearOrder V]
    (hV : Fintype.card V ≤ 4) :
    h1 (TwoComplex.complete V) (Equiv.Perm.movedNorm (Fin 2)) = (Fintype.card V - 2 : ℕ) := by
  by_cases hV3 : 3 ≤ Fintype.card V
  · have : Nontrivial (Equiv.Perm (Fin 2)) := ⟨⟨1, Equiv.swap 0 1, by decide⟩⟩
    exact h1_eq_of_forall_defect_eq_mul_gaugeDist
      (exists_gaugeDist_pos_complete hV3 (Equiv.Perm.movedNorm (Fin 2)))
      fun α _ ↦ α.defect_movedNorm_fin_two_eq_card_sub_two_mul_gaugeDist_of_card_le_four hV
  · have hsub : Fintype.card V - 2 = 0 := by omega
    rw [hsub, Nat.cast_zero]
    exact h1_complete_of_card_le_two (by omega) _

/-- **Four-vertex binary Cheeger constant**: when `Fintype.card V = 4`,
`h1 (TwoComplex.complete V) (Equiv.Perm.movedNorm (Fin 2)) = 2`. -/
theorem h1_complete_movedNorm_fin_two_of_card_eq_four {V : Type*} [Fintype V] [LinearOrder V]
    (hV : Fintype.card V = 4) :
    h1 (TwoComplex.complete V) (Equiv.Perm.movedNorm (Fin 2)) = 2 := by
  rw [h1_complete_movedNorm_fin_two_of_card_le_four hV.le, hV]
  norm_cast

/-- On `TwoComplex.complete V` with `Fintype.card V ≤ 4`, the Cheeger constant of the two-element
subgroup `Subgroup.zpowers t` generated by a transposition `t` under the restricted moved-point norm
equals `(Fintype.card V - 2 : ℕ)`. -/
theorem h1_complete_zpowers_swap_of_card_le_four {V α : Type*} [Fintype V] [LinearOrder V]
    [Fintype α] [DecidableEq α] (hV : Fintype.card V ≤ 4) {t : Equiv.Perm α} (ht : t.IsSwap) :
    h1 (TwoComplex.complete V)
        ((Equiv.Perm.movedNorm α).comp (Subgroup.zpowers t).subtype_injective) =
      (Fintype.card V - 2 : ℕ) := by
  by_cases hV3 : 3 ≤ Fintype.card V
  · have : Nontrivial (Subgroup.zpowers t) :=
      ⟨⟨1, ⟨t, Subgroup.mem_zpowers t⟩, fun h ↦
        ht.isCycle.ne_one (congrArg Subtype.val h).symm⟩⟩
    exact h1_eq_of_forall_defect_eq_mul_gaugeDist
      (exists_gaugeDist_pos_complete hV3 _)
      fun γ _ ↦ γ.defect_zpowers_swap_eq_card_sub_two_mul_gaugeDist_of_card_le_four hV ht
  · have hsub : Fintype.card V - 2 = 0 := by omega
    rw [hsub, Nat.cast_zero]
    exact h1_complete_of_card_le_two (by omega) _

/-- **Four-vertex transposition-subgroup Cheeger constant**: when `Fintype.card V = 4`, the Cheeger
constant of `Subgroup.zpowers t` under the restricted moved-point norm equals `2`. -/
theorem h1_complete_zpowers_swap_of_card_eq_four {V α : Type*} [Fintype V] [LinearOrder V]
    [Fintype α] [DecidableEq α] (hV : Fintype.card V = 4) {t : Equiv.Perm α} (ht : t.IsSwap) :
    h1 (TwoComplex.complete V)
        ((Equiv.Perm.movedNorm α).comp (Subgroup.zpowers t).subtype_injective) = 2 := by
  rw [h1_complete_zpowers_swap_of_card_le_four hV.le ht, hV]
  norm_cast

end TauCeti
