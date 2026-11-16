/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finsupp.Basic

/-!
# Filtering sums of functions supported on disjoint sets

Filtering by `(· ∈ s)` recovers the summand supported on `s` from a sum of functions supported on
disjoint sets `s` and `t`, so addition is injective on such pairs. This holds over any
`AddZeroClass`, with no cancellation. For instance, the exponents of two monomials in disjoint
sets of variables are determined by the exponent of their product.

## Main results

* `Finsupp.injOn_add_of_disjoint`: functions supported on disjoint sets `s` and `t` are
  determined by their sum, each being its restriction to its own set.
-/

public section

namespace Finsupp

variable {α M : Type*}

/-- **Sums of functions supported on disjoint sets.** If `s` and `t` are disjoint, a function
supported on `s` and a function supported on `t` are determined by their sum: each is the
restriction of the sum to its own set. -/
theorem injOn_add_of_disjoint [AddZeroClass M] {s t : Set α} (h : Disjoint s t) :
    Set.InjOn (fun p : (α →₀ M) × (α →₀ M) ↦ p.1 + p.2)
      {p | ↑p.1.support ⊆ s ∧ ↑p.2.support ⊆ t} := by
  classical
  -- Restricting to `u` keeps a function supported on `u` and kills one supported off `u`.
  have keep {u : Set α} {f : α →₀ M} (hf : ↑f.support ⊆ u) : f.filter (· ∈ u) = f :=
    (filter_eq_self_iff _ _).2 fun x hx ↦ hf (mem_support_iff.2 hx)
  have kill {u v : Set α} (huv : Disjoint u v) {f : α →₀ M} (hf : ↑f.support ⊆ v) :
      f.filter (· ∈ u) = 0 :=
    (filter_eq_zero_iff _ _).2 fun x hx ↦ notMem_support_iff.1 fun hx' ↦
      Set.disjoint_left.1 huv hx (hf hx')
  -- So each summand is the restriction of the sum to its own set.
  have fst {f g : α →₀ M} (hf : ↑f.support ⊆ s) (hg : ↑g.support ⊆ t) :
      (f + g).filter (· ∈ s) = f := by
    rw [filter_add, keep hf, kill h hg, add_zero]
  have snd {f g : α →₀ M} (hf : ↑f.support ⊆ s) (hg : ↑g.support ⊆ t) :
      (f + g).filter (· ∈ t) = g := by
    rw [filter_add, kill h.symm hf, keep hg, zero_add]
  rintro ⟨a, b⟩ ⟨ha, hb⟩ ⟨c, d⟩ ⟨hc, hd⟩ (he : a + b = c + d)
  exact Prod.ext (by rw [← fst ha hb, he, fst hc hd]) (by rw [← snd ha hb, he, snd hc hd])

end Finsupp
