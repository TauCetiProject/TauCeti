/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Constructions
import Mathlib.Basic.Finite.Prod
import Mathlib.Basic.Finite.Sigma

/-!
# Shrinking open sets into dense open sets of finite products

Given nonempty open sets `V i` in a topological space `X` and a dense open set `U ⊆ κ → X` for a
finite type `κ`, the sets `V i` can be shrunk to nonempty open subsets so that the box
`∏ j, W (t j)` along one given injective tuple `t : κ → I` lies in `U`. When the index type `I`
is also finite, iterating this shrinks the `V i` so that, for finitely many dense open sets
`U c ⊆ κ c → X` with each `κ c` finite, every box along every injective tuple `t : κ c → I` lies
in `U c`. Such shrinking steps are the
basic move in Baire category constructions of perfect sets of independent points, such as the
proof of Mycielski's theorem.

## Main results

* `TauCeti.exists_univ_pi_subset`: shrinking along one injective tuple.
* `TauCeti.exists_forall_univ_pi_subset`: when the index type is finite, shrinking along all
  injective tuples for finitely many dense open sets at once.
-/

public section

open Set Function

namespace TauCeti

variable {X : Type*} [TopologicalSpace X]

/-- Shrinking along one injective tuple: nonempty open sets `V i` can be shrunk to nonempty open
sets `W i ⊆ V i` so that the box `∏ j, W (t j)` along an injective finite tuple `t` of indices
lies in a given dense open set. This is the inductive step of `exists_forall_univ_pi_subset`. -/
theorem exists_univ_pi_subset {I κ : Type*} [Finite κ] {V : I → Set X}
    (hVo : ∀ i, IsOpen (V i)) (hVne : ∀ i, (V i).Nonempty) {t : κ → I} (ht : Injective t)
    {U : Set (κ → X)} (hUo : IsOpen U) (hUd : Dense U) :
    ∃ W : I → Set X, (∀ i, IsOpen (W i)) ∧ (∀ i, (W i).Nonempty) ∧ (∀ i, W i ⊆ V i) ∧
      univ.pi (fun j => W (t j)) ⊆ U := by
  classical
  -- a point of `U` in the box `∏ j, V (t j)`, and an open box around it inside `U`
  obtain ⟨y, hyV, hyU⟩ := hUd.inter_open_nonempty (univ.pi fun j => V (t j))
    (isOpen_set_pi finite_univ fun j _ => hVo (t j)) (univ_pi_nonempty_iff.2 fun j => hVne (t j))
  obtain ⟨u, hu, huU⟩ := isOpen_pi_iff'.1 hUo y hyU
  -- cut `V (t j)` down by `u j`, leaving the other sets alone
  let u' : I → Set X := extend t u fun _ => univ
  have hu'o (i : I) : IsOpen (u' i) := by
    by_cases hi : ∃ j, t j = i
    · obtain ⟨j, rfl⟩ := hi
      simpa [u', ht.extend_apply] using (hu j).1
    · simp [u', extend_apply' _ _ _ hi]
  refine ⟨fun i => V i ∩ u' i, fun i => (hVo i).inter (hu'o i), fun i => ?_,
    fun i => inter_subset_left, fun x hx => huU fun j _ => ?_⟩
  · by_cases hi : ∃ j, t j = i
    · obtain ⟨j, rfl⟩ := hi
      exact ⟨y j, hyV j (mem_univ j), by simpa [u', ht.extend_apply] using (hu j).2⟩
    · simpa [u', extend_apply' _ _ _ hi] using hVne i
  · simpa [u', ht.extend_apply] using (hx j (mem_univ j)).2

/-- **Shrinking along all injective tuples.** Nonempty open sets `V i`, indexed by a finite type,
can be shrunk to nonempty open sets `W i ⊆ V i` so that for each of finitely many dense open sets
`U c ⊆ κ c → X`, every box `∏ j, W (t j)` along an injective tuple `t : κ c → I` lies in `U c`. -/
theorem exists_forall_univ_pi_subset {I C : Type*} [Finite I] [Finite C] {κ : C → Type*}
    [∀ c, Finite (κ c)] {V : I → Set X} (hVo : ∀ i, IsOpen (V i)) (hVne : ∀ i, (V i).Nonempty)
    {U : ∀ c, Set (κ c → X)} (hUo : ∀ c, IsOpen (U c)) (hUd : ∀ c, Dense (U c)) :
    ∃ W : I → Set X, (∀ i, IsOpen (W i)) ∧ (∀ i, (W i).Nonempty) ∧ (∀ i, W i ⊆ V i) ∧
      ∀ c (t : κ c → I), Injective t → univ.pi (fun j => W (t j)) ⊆ U c := by
  classical
  -- treat the finitely many pairs of a set `U c` and an injective tuple one at a time
  let Q := Σ c, {t : κ c → I // Injective t}
  have : Fintype Q := Fintype.ofFinite Q
  suffices h : ∀ s : Finset Q, ∃ W : I → Set X, (∀ i, IsOpen (W i)) ∧ (∀ i, (W i).Nonempty) ∧
      (∀ i, W i ⊆ V i) ∧ ∀ q ∈ s, univ.pi (fun j => W (q.2.1 j)) ⊆ U q.1 by
    obtain ⟨W, hWo, hWne, hWV, hW⟩ := h Finset.univ
    exact ⟨W, hWo, hWne, hWV, fun c t ht => hW ⟨c, t, ht⟩ (Finset.mem_univ _)⟩
  intro s
  induction s using Finset.induction_on with
  | empty => exact ⟨V, hVo, hVne, fun _ => subset_rfl, by simp⟩
  | insert q s _ ih =>
    obtain ⟨W, hWo, hWne, hWV, hW⟩ := ih
    obtain ⟨W', hW'o, hW'ne, hW'W, hW'⟩ :=
      exists_univ_pi_subset hWo hWne q.2.2 (hUo q.1) (hUd q.1)
    refine ⟨W', hW'o, hW'ne, fun i => (hW'W i).trans (hWV i), fun q' hq' => ?_⟩
    rcases Finset.mem_insert.1 hq' with rfl | hq'
    · exact hW'
    · exact (pi_mono fun j _ => hW'W _).trans (hW q' hq')

end TauCeti
