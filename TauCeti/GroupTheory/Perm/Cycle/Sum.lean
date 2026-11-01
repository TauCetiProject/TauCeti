/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Dynamics.PeriodicPts.Lemmas
public import Mathlib.GroupTheory.Perm.Cycle.Basic

/-!
# Products over the orbits of a permutation

Let `σ` be a permutation of a finite type. Every element lies in exactly one orbit (one class of
`Equiv.Perm.SameCycle σ`), and within the orbit of a chosen representative `x` it is
`σ^[i] x` for exactly one `i` below the minimal period of `x`. Hence a product over the whole
type can be computed orbit by orbit, running through each orbit from its representative.

This is how a permutation of the edges of a finite directed graph, sending each edge to an edge
starting where it ends, decomposes the edge set into closed walks.

## Main results

* `Equiv.Perm.prod_quotient_sameCycle_prod_iterate`: a product over a finite type is the product
  over the orbits of `σ` of the products along the orbits;
  `Equiv.Perm.sum_quotient_sameCycle_sum_iterate` is the additive version.
-/

public section

open Function

namespace Equiv.Perm

variable {α M : Type*} [Fintype α] [CommMonoid M]

/-- **Products over the orbits of a permutation.** For a permutation `σ` of a finite type, a
product over the type is the product over the orbits `q` of `σ` of the products of the values at
`σ^[i] q.out` for `i` below the minimal period of the representative `q.out`. -/
@[to_additive /-- **Sums over the orbits of a permutation.** For a permutation `σ` of a finite
type, a sum over the type is the sum over the orbits `q` of `σ` of the sums of the values at
`σ^[i] q.out` for `i` below the minimal period of the representative `q.out`. -/]
theorem prod_quotient_sameCycle_prod_iterate (σ : Perm α)
    [Fintype (Quotient (SameCycle.setoid σ))] (f : α → M) :
    ∏ q : Quotient (SameCycle.setoid σ), ∏ i ∈ Finset.range (minimalPeriod σ q.out),
      f (σ^[i] q.out) = ∏ x, f x := by
  have hsame (x : α) (i : ℕ) : SameCycle σ x (σ^[i] x) := by
    rw [iterate_eq_pow]
    exact sameCycle_pow_right.2 (SameCycle.refl σ x)
  rw [Finset.prod_sigma']
  refine Finset.prod_bij (fun x _ ↦ σ^[x.2] x.1.out) (fun _ _ ↦ Finset.mem_univ _) ?_ ?_
    fun _ _ ↦ rfl
  · -- Distinct orbit positions give distinct elements.
    rintro ⟨q, i⟩ hi ⟨q', i'⟩ hi' h
    simp only [Finset.mem_sigma, Finset.mem_range] at hi hi' h
    have hq : q = q' := by
      rw [← Quotient.out_eq q, ← Quotient.out_eq q']
      exact Quotient.sound ((hsame _ i).trans (h ▸ (hsame _ i').symm))
    subst hq
    rw [iterate_injOn_Iio_minimalPeriod hi.2 hi'.2 h]
  · -- Every element is reached from the representative of its orbit.
    intro y _
    let q : Quotient (SameCycle.setoid σ) := ⟦y⟧
    obtain ⟨n, hn⟩ := (Quotient.mk_out (s := SameCycle.setoid σ) y).exists_nat_pow_eq
    have hpos : 0 < minimalPeriod σ q.out :=
      minimalPeriod_pos_of_mem_periodicPts (σ.injective.mem_periodicPts _)
    refine ⟨⟨q, n % minimalPeriod σ q.out⟩, Finset.mem_sigma.2 ⟨Finset.mem_univ _,
      Finset.mem_range.2 (Nat.mod_lt _ hpos)⟩, ?_⟩
    simp only
    rw [iterate_mod_minimalPeriod_eq, iterate_eq_pow]
    exact hn

end Equiv.Perm
