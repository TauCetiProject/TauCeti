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

The integral span of the short-root weights detects every coroot. Together with the F4 length
bounds, this supplies a descending-free root string through each long root.
-/

public section

namespace TauCeti.DynkinType

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
  -- Short-root spanning makes every coroot visible on some short root.
  let P := f4SimplyConnectedRootDatum
  have hexists : ∃ β : Fin 48, f4Length β = 1 ∧ P.pairing β α ≠ 0 := by
    by_contra h
    push Not at h
    have hzero : ∀ x ∈ Submodule.span ℤ (Set.range f4ShortRootWeight),
        P.toLinearMap x (P.coroot α) = 0 := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
          obtain ⟨a, rfl⟩ := hx
          by_cases ha : f4ShortRootWeight a = 0
          · simp [ha]
          · obtain ⟨β, hβ, hroot⟩ :=
              (f4ShortRootWeight_ne_zero_iff_exists_shortRoot a).mp ha
            have hroot' : P.root β = f4ShortRootWeight a := by
              simpa only [P, f4SimplyConnectedRootDatum_root] using hroot
            rw [← hroot', P.root_coroot_eq_pairing, h β hβ]
      | zero => simp
      | add x y hx hy ihx ihy => simp [ihx, ihy]
      | smul a x hx ih =>
          simp only [map_smul, LinearMap.smul_apply, ih, smul_zero]
    have hmem : P.root α ∈ Submodule.span ℤ (Set.range f4ShortRootWeight) := by
      rw [span_range_f4ShortRootWeight_eq_top]
      exact Submodule.mem_top
    have hbad := hzero (P.root α) hmem
    rw [P.root_coroot_eq_pairing, P.pairing_same] at hbad
    norm_num at hbad
  obtain ⟨β₀, hβ₀, hp₀_ne⟩ := hexists
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
    omega
  obtain ⟨β, hβ, hp⟩ : ∃ β : Fin 48, f4Length β = 1 ∧ P.pairing β α = -1 := by
    rcases hp₀ with hp₀ | hp₀
    · exact ⟨β₀, hβ₀, hp₀⟩
    · let β := P.reflectionPerm β₀ β₀
      have hβroot : P.root β = P.root β₀ + (-2 : ℤ) • P.root β₀ := by
        rw [P.root_reflectionPerm, P.reflection_apply_self]
        module
      have hβlen := f4Length_of_root_eq_add_zsmul β₀ β₀ β (-2) hβroot
      have hβ : f4Length β = 1 := by
        rw [hβ₀, P.pairing_same] at hβlen
        norm_num at hβlen
        exact hβlen
      have hβpair : P.pairing β α = -1 := by
        -- Unfold the local abbreviation `β` so that the reflection lemma below applies.
        change P.pairing (P.reflectionPerm β₀ β₀) α = -1
        rw [P.pairing_reflectionPerm_self_left, hp₀]
      exact ⟨β, hβ, hβpair⟩
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
