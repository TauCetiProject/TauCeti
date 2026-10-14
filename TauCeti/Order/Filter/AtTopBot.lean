/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Find
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.Finite

/-!
# Diagonal indices along `atTop`

If for every `k` a property `P k n` holds for all large `n`, then an index `κ n` tending to
infinity can be chosen so slowly that `P (κ n) n` holds for all large `n`
(`TauCeti.exists_tendsto_atTop_of_forall_eventually`). This is the diagonal step of constructions
that must meet countably many eventual requirements at once with a single sequence, such as a
recovery sequence built from a countable neighbourhood basis. It complements Mathlib's
`Filter.extraction_forall_of_eventually`, which meets the requirements along a subsequence
instead.

The second statement is the diagonal extraction of a subsequence along which countably many
sequences converge at once (`TauCeti.extraction_forall_exists_tendsto`): if every subsequence of
each of the sequences `x j` has a convergent further subsequence, a single subsequence makes all of
them converge. It is the compactness step of the Arzelà–Ascoli theorem.
-/

public section

open Filter

namespace TauCeti

/-- If for every `k` the property `P k n` holds for all large `n`, then there is an index `κ n`
tending to infinity with `P (κ n) n` for all large `n`. -/
theorem exists_tendsto_atTop_of_forall_eventually {P : ℕ → ℕ → Prop}
    (h : ∀ k, ∀ᶠ n in atTop, P k n) :
    ∃ κ : ℕ → ℕ, Tendsto κ atTop atTop ∧ ∀ᶠ n in atTop, P (κ n) n := by
  classical
  choose N hN using fun k ↦ eventually_atTop.1 (h k)
  -- `κ n` is the largest `k ≤ n` such that `N j ≤ n` for every `j ≤ k`.
  refine ⟨fun n ↦ Nat.findGreatest (fun k ↦ ∀ j ≤ k, N j ≤ n) n, tendsto_atTop.2 fun k ↦ ?_, ?_⟩
  · filter_upwards [eventually_ge_atTop k, (eventually_all_finset (Finset.range (k + 1))).2
      fun j _ ↦ eventually_ge_atTop (N j)] with n hkn hn
    exact Nat.le_findGreatest hkn fun j hj ↦ hn j (Finset.mem_range.2 (Nat.lt_succ_of_le hj))
  · filter_upwards [eventually_ge_atTop (N 0)] with n hn
    refine hN _ _ (Nat.findGreatest_spec (P := fun k ↦ ∀ j ≤ k, N j ≤ n) (Nat.zero_le n)
      (fun j hj ↦ ?_) _ le_rfl)
    rwa [Nat.le_zero.1 hj]

/-- **Diagonal extraction.** Let `x j : ℕ → X` be countably many sequences and `l y` the filter of
a convergence to `y` on `X`. If every subsequence of every `x j` has a further subsequence
converging to some point, then one subsequence makes every `x j` converge. -/
theorem extraction_forall_exists_tendsto {X : Type*} {l : X → Filter X} {x : ℕ → ℕ → X}
    (h : ∀ j (ψ : ℕ → ℕ), StrictMono ψ →
      ∃ y, ∃ ψ' : ℕ → ℕ, StrictMono ψ' ∧ Tendsto (fun n ↦ x j (ψ (ψ' n))) atTop (l y)) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ j, ∃ y, Tendsto (fun n ↦ x j (ψ n)) atTop (l y) := by
  choose y ψ' hψ' hy using h
  -- `θ j` is the subsequence along which `x 0, …, x j` converge, each refining the previous one.
  let θ : ℕ → {ψ : ℕ → ℕ // StrictMono ψ} := fun j ↦ Nat.rec
    ⟨ψ' 0 id strictMono_id, hψ' 0 id strictMono_id⟩
    (fun j θj ↦ ⟨θj.1 ∘ ψ' (j + 1) θj.1 θj.2, θj.2.comp (hψ' (j + 1) θj.1 θj.2)⟩) j
  have hθ0 : (θ 0).1 = ψ' 0 id strictMono_id := rfl
  have hθsucc j : (θ (j + 1)).1 = (θ j).1 ∘ ψ' (j + 1) (θ j).1 (θ j).2 := rfl
  have hθ j : ∃ z, Tendsto (fun n ↦ x j ((θ j).1 n)) atTop (l z) := by
    cases j with
    | zero => exact ⟨_, by simpa only [hθ0, id] using hy 0 id strictMono_id⟩
    | succ j =>
      exact ⟨_, by simpa only [hθsucc, Function.comp_apply] using hy (j + 1) (θ j).1 (θ j).2⟩
  -- Every later `θ n` is a subsequence of `θ j`.
  have hsub j n (hjn : j ≤ n) a : ∃ b, a ≤ b ∧ (θ n).1 a = (θ j).1 b := by
    induction n, hjn using Nat.le_induction generalizing a with
    | base => exact ⟨a, le_rfl, rfl⟩
    | succ n _ ih =>
      obtain ⟨b, hab, hb⟩ := ih (ψ' (n + 1) (θ n).1 (θ n).2 a)
      exact ⟨b, ((hψ' _ _ _).id_le a).trans hab, by rw [hθsucc]; exact hb⟩
  -- The diagonal subsequence `n ↦ θ n n`.
  refine ⟨fun n ↦ (θ n).1 n, strictMono_nat_of_lt_succ fun n ↦ ?_, fun j ↦ ?_⟩
  · rw [hθsucc]
    exact (θ n).2.monotone ((hψ' _ _ _).id_le _) |>.trans_lt' ((θ n).2 n.lt_succ_self)
  · obtain ⟨z, hz⟩ := hθ j
    choose m hm using fun n ↦ hsub j (max j n) (le_max_left _ _) (max j n)
    refine ⟨z, (hz.comp (tendsto_atTop_mono (fun n ↦ (le_max_right j n).trans (hm n).1)
      tendsto_id)).congr' ?_⟩
    filter_upwards [eventually_ge_atTop j] with n hn
    simp only [Function.comp_apply, ← (hm n).2, max_eq_right hn]

end TauCeti
