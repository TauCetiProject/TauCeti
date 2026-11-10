/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Regrouping a series along finite fibres

Mathlib's `HasSum.sigma` regroups a series over a sigma type into the sums of its fibres, which
needs a regular topology and continuous addition to take the fibre sums. When every fibre is
finite the fibre sums are finite sums, and the regrouping holds in any topological additive monoid.

## Main results

* `HasSum.sigma_of_finite`: a series over `Σ b, γ b` with finite fibres sums to the same value
  when grouped by `b`.
-/

public section

open Finset Filter

/-- **Regrouping along finite fibres.** If a family over a sigma type with finite fibres sums to
`a`, then so does the family of its fibre sums. No regularity of the topology is needed. -/
@[to_additive]
theorem HasProd.sigma_of_finite {α β : Type*} {γ : β → Type*} [CommMonoid α] [TopologicalSpace α]
    [∀ b, Fintype (γ b)] {f : (Σ b, γ b) → α} {a : α} (ha : HasProd f a) :
    HasProd (fun b ↦ ∏ c, f ⟨b, c⟩) a := by
  classical
  -- the partial products over finite sets of `b` are partial products of `ha`
  have hT : Tendsto (fun s : Finset β ↦ s.sigma fun b ↦ (Finset.univ : Finset (γ b))) atTop
      atTop := by
    refine tendsto_atTop_atTop.2 fun T ↦ ⟨T.image Sigma.fst, fun s hs x hx ↦ ?_⟩
    exact Finset.mem_sigma.2 ⟨hs (Finset.mem_image_of_mem _ hx), Finset.mem_univ _⟩
  exact (ha.comp hT).congr fun s ↦ by simp [Finset.prod_sigma]
