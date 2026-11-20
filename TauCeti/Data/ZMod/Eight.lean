/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Diagonal residue families modulo eight

The units of `ℤ/8` are `1, 3, 5, 7`, each squaring to `1`. Fix a unit `y`. Suppose two families `dᵢ`
and `vᵢ` of the same nonzero length `N` have residues in `{y, 5y}` and `{-y, -5y}` respectively.
Their products and sums agree only when `N ≥ 4`. A unit diagonal of a dyadic form is read modulo `8`
through its product (the determinant square class) and its sum (the oddity). So this counting
statement shows that a target diagonal whose entries all have the opposite residue modulo `4` forces
rank at least four.

## Main results

* `ZMod.four_le_of_forall_eq_or_eq`: nonempty families in `{y, 5y}` and `{-y, -5y}` modulo `8`
  with the same product and the same sum have at least four members.
* `ZMod.add_add_eq_neg_or_eq_neg_five_mul`: the sum of three residues from `{y, 5y}` lies in
  `{-y, -5y}` modulo `8`.
-/

public section

namespace ZMod

/-- **The determinant class and oddity of a diagonal determine at least four entries.** Let the
residues `dᵢ` all lie in `{y, 5y}` and the residues `vᵢ` all lie in `{-y, -5y}` modulo `8`, for a
nonzero number `N` of indices. If the two families have the same product and the same sum, then
there are at least four of them. -/
theorem four_le_of_forall_eq_or_eq {N : ℕ} (hN : N ≠ 0) {y : ZMod (2 ^ 3)}
    (hy : y * y = 1) {d v : Fin N → ZMod (2 ^ 3)} (hd : ∀ i, d i = y ∨ d i = 5 * y)
    (hv : ∀ i, v i = -y ∨ v i = -(5 * y)) (hP : ∏ i, d i = ∏ i, v i)
    (hS : ∑ i, d i = ∑ i, v i) : 4 ≤ N := by
  -- A product of factors `1 + e` with `2 e = 0` is `1` plus the sum of the `e`.
  have hprod (e : Fin N → ZMod (2 ^ 3)) (he : ∀ i, 2 * e i = 0) (s : Finset (Fin N)) :
      ∏ i ∈ s, (1 + e i) = 1 + ∑ i ∈ s, e i ∧ 2 * ∑ i ∈ s, e i = 0 := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, ih.1]
      have key : ∀ x z : ZMod (2 ^ 3), 2 * x = 0 → 2 * z = 0 →
          (1 + x) * (1 + z) = 1 + (x + z) ∧ 2 * (x + z) = 0 := by decide
      exact key _ _ (he a) ih.2
  -- Write `y dᵢ = 1 + eᵢ` and `-y vᵢ = 1 + fᵢ`, where `eᵢ` and `fᵢ` are `0` or `4`.
  let e : Fin N → ZMod (2 ^ 3) := fun i ↦ y * d i - 1
  let f : Fin N → ZMod (2 ^ 3) := fun i ↦ -y * v i - 1
  have he (i : Fin N) : 2 * e i = 0 := by
    have key : ∀ y a : ZMod (2 ^ 3), y * y = 1 → (a = y ∨ a = 5 * y) → 2 * (y * a - 1) = 0 := by
      decide
    exact key y (d i) hy (hd i)
  have hf (i : Fin N) : 2 * f i = 0 := by
    have key : ∀ y a : ZMod (2 ^ 3), y * y = 1 → (a = -y ∨ a = -(5 * y)) →
        2 * (-y * a - 1) = 0 := by decide
    exact key y (v i) hy (hv i)
  obtain ⟨hpe, hE⟩ := hprod e he Finset.univ
  obtain ⟨hpf, hF⟩ := hprod f hf Finset.univ
  have h1e (i : Fin N) : 1 + e i = y * d i := by simp [e]
  have h1f (i : Fin N) : 1 + f i = -y * v i := by simp [f]
  simp only [h1e, h1f, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin] at hpe hpf
  have hse : y * ∑ i, d i = N + ∑ i, e i := by
    simp [Finset.mul_sum, ← h1e, Finset.sum_add_distrib]
  have hsf : -y * ∑ i, v i = N + ∑ i, f i := by
    simp [Finset.mul_sum, ← h1f, Finset.sum_add_distrib]
  rcases Nat.even_or_odd N with hN2 | hN2
  · -- For even `N`, the products force `∑ e = ∑ f`, and then the sums force `8 ∣ 2N`.
    rw [hN2.neg_pow, ← hP, hpe] at hpf
    have hef : ∑ i, e i = ∑ i, f i := add_left_cancel hpf
    have h2N : ((2 * N : ℕ) : ZMod (2 ^ 3)) = 0 := by
      have := congrArg₂ (· + ·) hse hsf
      simp only [← hS, ← hef] at this
      push_cast
      linear_combination -this - hE
    have := (ZMod.natCast_eq_zero_iff _ _).mp h2N
    omega
  · -- For odd `N`, the products force `-(1 + ∑ e) = 1 + ∑ f`, which is impossible.
    rw [hN2.neg_pow, ← hP, neg_mul, hpe] at hpf
    have key : ∀ x z : ZMod (2 ^ 3), 2 * x = 0 → 2 * z = 0 → -(1 + x) ≠ 1 + z := by decide
    exact (key _ _ hE hF hpf).elim

/-- Modulo `8`, the sum of three residues from `{y, 5 y}` lies in `{-y, -5 y}`. -/
theorem add_add_eq_neg_or_eq_neg_five_mul {y a b c : ZMod (2 ^ 3)}
    (ha : a = y ∨ a = 5 * y) (hb : b = y ∨ b = 5 * y) (hc : c = y ∨ c = 5 * y) :
    a + b + c = -y ∨ a + b + c = -(5 * y) := by
  have key₂ : ∀ y a b : ZMod (2 ^ 3), (a = y ∨ a = 5 * y) → (b = y ∨ b = 5 * y) →
      (a + b = 2 * y ∨ a + b = 6 * y) := by decide
  have key₃ : ∀ y s c : ZMod (2 ^ 3), (s = 2 * y ∨ s = 6 * y) →
      (c = y ∨ c = 5 * y) → (s + c = -y ∨ s + c = -(5 * y)) := by decide
  exact key₃ y _ _ (key₂ y _ _ ha hb) hc

end ZMod
