/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Meromorphic.Order

/-!
# Lower bounds on the order of a finite sum

A common lower bound on the orders of finitely many meromorphic summands is a lower bound on
the order of their sum. In particular, a finite sum cannot acquire a pole of higher order
than those of its summands.
-/

public section

namespace TauCeti

/-- A common lower bound on the meromorphic orders of the summands also bounds the order of
the sum from below. -/
theorem le_meromorphicOrderAt_sum {𝕜 E ι : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {s : Finset ι} {f : ι → 𝕜 → E} {z : 𝕜}
    {m : WithTop ℤ} (hf : ∀ i ∈ s, MeromorphicAt (f i) z)
    (hm : ∀ i ∈ s, m ≤ meromorphicOrderAt (f i) z) :
    m ≤ meromorphicOrderAt (∑ i ∈ s, f i) z := by
  classical
  induction s using Finset.cons_induction with
  | empty =>
    rw [Finset.sum_empty, Pi.zero_def, meromorphicOrderAt_const]
    simp
  | cons i s hi ih =>
    have hf' j (hj : j ∈ s) := hf j (Finset.mem_cons_of_mem hj)
    rw [Finset.sum_cons]
    exact (le_min (hm i (Finset.mem_cons_self i s))
      (ih hf' fun j hj ↦ hm j (Finset.mem_cons_of_mem hj))).trans
        (meromorphicOrderAt_add (hf i (Finset.mem_cons_self i s)) (MeromorphicAt.sum hf'))

end TauCeti
