/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.RingTheory.Artinian.Defs
import Mathlib.RingTheory.Artinian.Module

/-!
# Restricting independent functions to finitely many points

A finite family of functions `f i : X → K` that is linearly independent over an Artinian ring `K`
(for instance a field) stays linearly independent after restriction to some finite set of points
of `X`. Equivalently, a linear relation `∑ i, c i * f i x = 0` that holds at the points of this
finite set holds everywhere, and so has `c = 0`. This lets an argument that produces, for each
point `x`, a relation valid only for parameters near some limit (a neighbourhood depending on `x`)
produce a single relation valid for all `x` at once.

The proof takes a finite set of points whose relation module is minimal, which exists since the
relation modules are submodules of the Artinian module `ι → K`.

## Main results

* `LinearIndependent.exists_finset_linearIndependent_restrict`: a linearly independent finite
  family of functions with values in an Artinian ring stays linearly independent on some finite
  set of points.
-/

public section

variable {ι X K : Type*} [Finite ι] [Ring K] [IsArtinianRing K]

/-- Over an Artinian ring `K` (for instance a field), a linearly independent finite family of
functions `X → K` stays linearly independent after restriction to some finite set of points of
`X`. -/
theorem LinearIndependent.exists_finset_linearIndependent_restrict {f : ι → X → K}
    (hf : LinearIndependent K f) : ∃ s : Finset X, LinearIndependent K fun i (x : s) ↦ f i x := by
  classical
  cases nonempty_fintype ι
  -- The relations among the restrictions to `s`, a submodule of the Artinian module `ι → K`.
  let N : Finset X → Submodule K (ι → K) := fun s ↦
    LinearMap.ker (Fintype.linearCombination K fun i (x : s) ↦ f i x)
  obtain ⟨_, ⟨s, rfl⟩, hs⟩ := wellFounded_lt.has_min (Set.range N) ⟨_, ∅, rfl⟩
  refine ⟨s, Fintype.linearIndependent_iff.2 fun c hc ↦ ?_⟩
  by_contra! hc0
  obtain ⟨i, hi⟩ := hc0
  -- A nonzero relation on `s` fails at some point `x`, so adding `x` shrinks the relations.
  have hfc : ∑ i, c i • f i ≠ 0 := fun h ↦ hi (Fintype.linearIndependent_iff.1 hf c h i)
  obtain ⟨x, hx⟩ := Function.ne_iff.1 hfc
  refine hs (N (insert x s)) ⟨_, rfl⟩ (lt_of_le_of_ne (fun d hd ↦ ?_) fun h ↦ hx ?_)
  · ext ⟨y, hy⟩
    simpa [N, Fintype.linearCombination_apply] using
      congrFun (LinearMap.mem_ker.1 hd) ⟨y, Finset.mem_insert_of_mem hy⟩
  · have hcN : c ∈ N (insert x s) := h ▸ by simpa [N, Fintype.linearCombination_apply] using hc
    simpa [N, Fintype.linearCombination_apply] using
      congrFun (LinearMap.mem_ker.1 hcN) ⟨x, Finset.mem_insert_self x s⟩
