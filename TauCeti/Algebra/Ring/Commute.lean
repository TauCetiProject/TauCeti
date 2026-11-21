/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Commute
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NoncommRing

/-!
# Commutation with homotopy projectors, `1 - a • u` and finite sums

An element of a ring commuting with `u` also commutes with `1 - a • u`, for any scalar `a` acting
compatibly with the multiplication. For an operator `u`, `1 - a • u` is the operator whose
generalised kernel at a zero `a` of the Fredholm determinant of `u` carries the Riesz projector.

Each member of a pairwise commuting finite family commutes with the family's sum, so it preserves
the eigenvalue equations of that sum.

A square-zero differential commutes with any element `e` satisfying a homotopy identity
`d * h + h * d = 1 - e`.

For pairwise commuting `x`, `y` and `z`, annihilation by powers of `x - y` and `x - z` and
`y - z` on parts of a vector combines to annihilation by a power of `y - z`, by expanding
`y - z = (x - z) + (y - x)`. This is the combinatorial step of Dong's lemma on locality of
residue products of fields.

## Main results

* `Commute.one_sub_smul_left`, `Commute.one_sub_smul_right`: commutation with `1 - a • u`.
* `Commute.add_pow_smul_add_eq_zero`: if `v ^ a` kills `m₁ + m₂`, `u ^ b` kills `m₂` and
  `(u + v) ^ c` kills `m₁`, then `(u + v) ^ (a + b + c)` kills `m₁ + m₂`.
* `Commute.sub_pow_smul_add_eq_zero`: if `(x - y) ^ a` kills `m₁ + m₂`, `(x - z) ^ b` kills
  `m₂` and `(y - z) ^ c` kills `m₁`, then `(y - z) ^ (a + b + c)` kills `m₁ + m₂`.
* `TauCeti.commute_of_sq_zero_of_homotopy`: commutation of a square-zero differential with its
  homotopy projector.
* `Finset.sum_smul_smul_eq_smul_smul`: if the sum of a pairwise commuting family scales `x` by
  `μ`, it scales `p a • x` by `μ` for each member `p a`. The vector `p a • x` may be zero.
-/

public section

namespace Commute

variable {R A : Type*} [Ring A] [SMul R A] [IsScalarTower R A A] [SMulCommClass R A A] {u x : A}

/-- An element commuting with `u` commutes with `1 - a • u`, on the left. -/
theorem one_sub_smul_left (h : Commute u x) (a : R) : Commute (1 - a • u) x :=
  (Commute.one_left x).sub_left (h.smul_left a)

/-- An element commuting with `u` commutes with `1 - a • u`, on the right. -/
theorem one_sub_smul_right (h : Commute x u) (a : R) : Commute x (1 - a • u) :=
  (h.symm.one_sub_smul_left a).symm

/-- Let `u` and `v` commute. If `v ^ a` kills `m₁ + m₂`, `u ^ b` kills `m₂` and `(u + v) ^ c`
kills `m₁`, then `(u + v) ^ (a + b + c)` kills `m₁ + m₂`.

Expanding `(u + v) ^ (a + b)`, each term has a factor `u ^ b` or `v ^ a`. -/
theorem add_pow_smul_add_eq_zero {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    {u v : R} (huv : Commute u v) {m₁ m₂ : M} {a b c : ℕ} (ha : v ^ a • (m₁ + m₂) = 0)
    (hb : u ^ b • m₂ = 0) (hc : (u + v) ^ c • m₁ = 0) :
    (u + v) ^ (a + b + c) • (m₁ + m₂) = 0 := by
  have hwu : Commute (u + v) u := (Commute.refl u).add_left huv.symm
  have hwv : Commute (u + v) v := huv.add_left (Commute.refl v)
  rw [show a + b + c = c + (a + b) by omega, pow_add, mul_smul]
  nth_rw 2 [huv.add_pow']
  rw [Finset.sum_smul, Finset.smul_sum]
  refine Finset.sum_eq_zero fun ij hij ↦ ?_
  suffices h : (u + v) ^ c • (u ^ ij.1 * v ^ ij.2) • (m₁ + m₂) = 0 by
    rw [smul_assoc, smul_comm, h, smul_zero]
  rw [Finset.mem_antidiagonal] at hij
  by_cases hi : b ≤ ij.1
  · -- The term is killed on `m₁` by `(u + v) ^ c`, and on `m₂` by `u ^ b`.
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hi
    have h₁ : (u + v) ^ c • (u ^ ij.1 * v ^ ij.2) • m₁ = 0 := by
      rw [smul_smul, ((hwu.pow_pow _ _).mul_right (hwv.pow_pow _ _)).eq, mul_smul, hc,
        smul_zero]
    have h₂ : (u ^ ij.1 * v ^ ij.2) • m₂ = 0 := by
      rw [hk, pow_add, mul_assoc, ((Commute.pow_pow_self u b k).mul_right
        (huv.pow_pow b ij.2)).eq, mul_smul, hb, smul_zero]
    rw [smul_add, h₂, add_zero, h₁]
  · -- The term is killed by `v ^ a`.
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' (show a ≤ ij.2 by omega)
    rw [hk, pow_add, ← mul_assoc, mul_smul, ha, smul_zero, smul_zero]

/-- Let `x`, `y` and `z` be pairwise commuting. If `(x - y) ^ a` kills `m₁ + m₂`, `(x - z) ^ b`
kills `m₂` and `(y - z) ^ c` kills `m₁`, then `(y - z) ^ (a + b + c)` kills `m₁ + m₂`.

This is `Commute.add_pow_smul_add_eq_zero` for `y - z = (x - z) + (y - x)`. -/
theorem sub_pow_smul_add_eq_zero {R M : Type*} [Ring R] [AddCommMonoid M] [Module R M]
    {x y z : R} (hxy : Commute x y) (hxz : Commute x z) (hyz : Commute y z) {m₁ m₂ : M}
    {a b c : ℕ} (ha : (x - y) ^ a • (m₁ + m₂) = 0) (hb : (x - z) ^ b • m₂ = 0)
    (hc : (y - z) ^ c • m₁ = 0) : (y - z) ^ (a + b + c) • (m₁ + m₂) = 0 := by
  have hw : y - z = (x - z) + (y - x) := by abel
  have hva : (y - x) ^ a • (m₁ + m₂) = 0 := by
    rw [← neg_sub, neg_pow, mul_smul, ha, smul_zero]
  rw [hw] at hc ⊢
  exact ((hxy.sub_right (Commute.refl x)).sub_left (hyz.symm.sub_right hxz.symm)
    ).add_pow_smul_add_eq_zero hva hb hc

end Commute

namespace TauCeti

/-- A square-zero differential commutes with an element satisfying its contracting homotopy
identity. Thus contraction constructions can derive this compatibility rather than requiring
it separately from callers. No idempotence assumption on that element is needed. -/
theorem commute_of_sq_zero_of_homotopy {A : Type*} [Ring A] {d h e : A}
    (hd : d * d = 0) (hdh : d * h + h * d = 1 - e) : Commute d e := by
  have he : e = 1 - (d * h + h * d) := by rw [hdh, sub_sub_cancel]
  have hddh : d * (d * h) = 0 := by
    simpa only [mul_assoc, zero_mul] using congrArg (· * h) hd
  rw [commute_iff_eq, he]
  noncomm_ring [hd, hddh]

end TauCeti

namespace Finset

/-- If the sum of a pairwise commuting family scales `x` by `μ`, it also scales `p a • x` by `μ`
for each member `p a` of the family, since `p a` commutes with the sum. -/
theorem sum_smul_smul_eq_smul_smul {K A M ι : Type*} [Semiring A] [MulAction A M] [SMul K M]
    [SMulCommClass A K M] (s : Finset ι) (p : ι → A)
    (hcomm : (s : Set ι).Pairwise fun i j => Commute (p i) (p j)) {a : ι} (ha : a ∈ s)
    {x : M} {μ : K} (heigen : (∑ i ∈ s, p i) • x = μ • x) :
    (∑ i ∈ s, p i) • p a • x = μ • p a • x := by
  have hsumcomm : Commute (∑ i ∈ s, p i) (p a) := .sum_left _ _ _ fun i hi =>
    (eq_or_ne i a).elim (fun hia => hia ▸ .refl _) (hcomm hi ha)
  rw [smul_smul, hsumcomm.eq, mul_smul, heigen, smul_comm]

end Finset
