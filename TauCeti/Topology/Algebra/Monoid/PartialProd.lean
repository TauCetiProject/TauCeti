/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Topology.Algebra.Monoid.Defs

/-!
# Continuity of partial products

The partial products `Fin.partialProd` of a tuple of continuous functions into a topological monoid
are continuous (`Continuous.finPartialProd`), and so are the partial sums `Fin.partialSum` into a
topological additive monoid (`Continuous.finPartialSum`), next to Mathlib's
`continuous_list_prod`.
-/

public section

/-- **The partial products of continuous functions are continuous.** -/
@[to_additive /-- **The partial sums of continuous functions are continuous.** -/]
theorem Continuous.finPartialProd {X M : Type*} [TopologicalSpace X] [Monoid M]
    [TopologicalSpace M] [ContinuousMul M] {n : ℕ} {f : Fin n → X → M}
    (hf : ∀ i, Continuous (f i)) (i : Fin (n + 1)) :
    Continuous fun x ↦ Fin.partialProd (fun j ↦ f j x) i := by
  induction i using Fin.induction with
  | zero => simpa only [Fin.partialProd_zero] using continuous_const
  | succ i ih =>
    simp only [Fin.partialProd_succ]
    exact ih.mul (hf i)
