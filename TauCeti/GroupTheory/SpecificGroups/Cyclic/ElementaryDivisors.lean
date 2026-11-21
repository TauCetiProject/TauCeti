/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic

import TauCeti.Algebra.Order.BigOperators.Sum.Min

/-!
# Uniqueness of elementary divisors with a fixed base

An additive equivalence between finite products of `ZMod (b ^ e i)`, with `b > 1` and positive
exponents, determines the exponents up to reindexing. For a prime `b = p` the exponents are the
elementary divisors of a finite abelian `p`-group, so this is the uniqueness clause of the
classification of finite abelian `p`-groups; it also identifies the finite factor of a topologically
finitely generated abelian pro-`p` group up to reindexing of its cyclic summands.

The exponents are required to be positive because a factor `ZMod (b ^ 0)` is trivial and leaves
the product unchanged.

## Main results

* `ZMod.exists_equiv_exponents_of_pi_pow_addEquiv`: two such products have the same exponents
  after a bijection of their finite index types.
-/

public section

namespace ZMod

open Finset

private theorem card_nsmul_ker_pi_pow {b : ℕ} [NeZero b] {ι : Type*} [Fintype ι]
    (e : ι → ℕ) (k : ℕ) :
    Nat.card (nsmulAddMonoidHom (b ^ k) :
      ((i : ι) → ZMod (b ^ e i)) →+ ((i : ι) → ZMod (b ^ e i))).ker =
        b ^ (∑ i, min k (e i)) := by
  classical
  calc
    _ = Nat.card ((i : ι) →
        (nsmulAddMonoidHom (b ^ k) : ZMod (b ^ e i) →+ ZMod (b ^ e i)).ker) := by
      apply Nat.card_congr
      exact (Equiv.subtypeEquivRight fun x ↦ by
        simp only [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply, funext_iff, Pi.smul_apply,
          Pi.zero_apply]).trans Equiv.subtypePiEquivPi
    _ = ∏ i, Nat.card
        (nsmulAddMonoidHom (b ^ k) : ZMod (b ^ e i) →+ ZMod (b ^ e i)).ker := Nat.card_pi
    _ = ∏ i, b ^ min k (e i) := by
      apply prod_congr rfl
      intro i _
      rw [IsAddCyclic.card_nsmulAddMonoidHom_ker, Nat.card_zmod]
      rcases le_total (e i) k with h | h
      · simp [Nat.gcd_eq_left (pow_dvd_pow b h), h]
      · simp [Nat.gcd_eq_right (pow_dvd_pow b h), h]
    _ = _ := prod_pow_eq_pow_sum _ _ _

private theorem sum_min_eq_of_pi_pow_addEquiv {b : ℕ} (hb : 1 < b)
    {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι → ℕ) (e' : κ → ℕ)
    (f : ((i : ι) → ZMod (b ^ e i)) ≃+ ((j : κ) → ZMod (b ^ e' j))) (k : ℕ) :
    (∑ i, min k (e i)) = ∑ j, min k (e' j) := by
  have : NeZero b := ⟨by omega⟩
  apply Nat.pow_right_injective hb
  dsimp only
  rw [← card_nsmul_ker_pi_pow (b := b) e k, ← card_nsmul_ker_pi_pow (b := b) e' k]
  apply Nat.card_congr
  refine f.toEquiv.subtypeEquiv fun x ↦ ?_
  simp only [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply, AddEquiv.toEquiv_eq_coe,
    EquivLike.coe_coe, ← map_nsmul f, map_eq_zero_iff f f.injective]

/-- Finite products of nontrivial cyclic groups with orders powers of the same base `b > 1`
have uniquely determined exponents up to reindexing. Primality of the base is not needed, and the
second index type is finite as soon as the first one is. -/
theorem exists_equiv_exponents_of_pi_pow_addEquiv {b : ℕ} (hb : 1 < b)
    {ι κ : Type*} [Finite ι] (e : ι → ℕ) (e' : κ → ℕ)
    (he : ∀ i, 0 < e i) (he' : ∀ j, 0 < e' j)
    (f : ((i : ι) → ZMod (b ^ e i)) ≃+ ((j : κ) → ZMod (b ^ e' j))) :
    ∃ σ : ι ≃ κ, ∀ i, e i = e' (σ i) := by
  classical
  have : NeZero b := ⟨by omega⟩
  have : Finite κ := by
    -- Each factor `ZMod (b ^ e' j)` is nontrivial, so an infinite `κ` gives an infinite product.
    have (j : κ) : Fact (1 < b ^ e' j) := ⟨Nat.one_lt_pow (he' j).ne' hb⟩
    have := Finite.of_equiv _ f.toEquiv
    exact not_infinite_iff_finite.mp fun _ ↦ not_finite ((j : κ) → ZMod (b ^ e' j))
  let := Fintype.ofFinite ι
  let := Fintype.ofFinite κ
  exact Fintype.exists_equiv_of_forall_sum_min_eq he he' (sum_min_eq_of_pi_pow_addEquiv hb e e' f)

end ZMod
