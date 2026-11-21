/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.F4.RootString
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.F4.ShortRootWeight.Basic

/-!
# Short-root neighbours of long roots in type F4

The F4 length bounds and root strings give each long root a short neighbour one step away in a
descending-free root string.
-/

public section

namespace TauCeti.DynkinType

/-- Every long F₄ root pairs to `-1` with some short root: a short root pairing nontrivially with
it pairs to `±1`, and reflecting it in itself flips the sign. -/
theorem exists_f4Length_eq_one_pairing_eq_neg_one (α : Fin 48) (hα : f4Length α = 2) :
    ∃ β : Fin 48, f4Length β = 1 ∧ f4SimplyConnectedRootDatum.pairing β α = -1 := by
  let P := f4SimplyConnectedRootDatum
  obtain ⟨β₀, hβ₀, hp₀_ne⟩ := exists_f4Length_eq_one_pairing_ne_zero α
  have hsym := f4Length_mul_pairing_comm α β₀
  rw [hα, hβ₀] at hsym
  simp only [one_mul] at hsym
  -- Restate through the local abbreviation `P`, so that `omega` below sees the same atoms
  -- in the hypotheses and in the goal.
  change 2 * P.pairing β₀ α = P.pairing α β₀ at hsym
  have hbound := abs_pairing_f4SimplyConnectedRootDatum_le_two α β₀
  have hp₀ : P.pairing β₀ α = -1 ∨ P.pairing β₀ α = 1 := by
    -- Again only a restatement through the local abbreviation `P`.
    change |P.pairing α β₀| ≤ 2 at hbound
    have hb := abs_le.mp hbound
    change P.pairing β₀ α ≠ 0 at hp₀_ne
    omega
  rcases hp₀ with hp₀ | hp₀
  · exact ⟨β₀, hβ₀, hp₀⟩
  · let β := f4OppositeRootIndex β₀
    have hβ : f4Length β = 1 := (f4Length_opposite β₀).trans hβ₀
    have hβpair : P.pairing β α = -1 := by
      -- Unfold the local abbreviation `β` so that the reflection lemma below applies.
      change P.pairing (f4OppositeRootIndex β₀) α = -1
      rw [f4OppositeRootIndex_eq_reflectionPerm, P.pairing_reflectionPerm_self_left, hp₀]
    exact ⟨β, hβ, hβpair⟩

/-- Every long F₄ root has a short neighbour one step away in a descending-free root string.
Concretely, for a long root `α` there is a short root `β` with `⟨β, α∨⟩ = -1`; then `β + α`
is a short root and the root string through `β` in the `α` direction has bottom coefficient zero.
-/
theorem exists_f4_short_neighbor_of_long (α : Fin 48) (hα : f4Length α = 2) :
    ∃ β γ : Fin 48,
      f4Length β = 1 ∧
      f4SimplyConnectedRootDatum.pairing β α = -1 ∧
      f4SimplyConnectedRootDatum.root γ =
        f4SimplyConnectedRootDatum.root β + f4SimplyConnectedRootDatum.root α ∧
      f4Length γ = 1 ∧
      f4SimplyConnectedRootDatum.chainBotCoeff α β = 0 := by
  let P := f4SimplyConnectedRootDatum
  obtain ⟨β, hβ, hp⟩ := exists_f4Length_eq_one_pairing_eq_neg_one α hα
  let γ := P.reflectionPerm α β
  have hγroot : P.root γ = P.root β + P.root α := by
    rw [← P.reflectionPerm_root, P.root_coroot_eq_pairing, hp]
    module
  have hγ : f4Length γ = 1 := by
    exact (f4_n_eq_one_and_pairing_eq_neg_one_and_length_eq_one_of_short_add_nsmul_long
      α β γ 1 hα hβ (by omega) (by simpa only [P, Nat.cast_one, one_zsmul] using hγroot)).2.2
  have hbot : P.chainBotCoeff α β = 0 :=
    f4_chainBotCoeff_eq_zero_of_add_of_length_eq α β γ (hβ.trans hγ.symm) hγroot
  exact ⟨β, γ, hβ, hp, hγroot, hγ, hbot⟩

end TauCeti.DynkinType
