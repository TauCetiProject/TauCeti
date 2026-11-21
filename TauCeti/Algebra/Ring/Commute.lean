/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Algebra.Ring.Commute
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.NoncommRing

/-!
# Commutation with homotopy projectors, `1 - a • u` and finite sums

An element of a ring commuting with `u` also commutes with `1 - a • u`, for any scalar `a` acting
compatibly with the multiplication. For an operator `u`, `1 - a • u` is the operator whose
generalised kernel at a zero `a` of the Fredholm determinant of `u` carries the Riesz projector.

Each member of a pairwise commuting finite family commutes with the family's sum, so it preserves
the eigenvalue equations of that sum. Commuting elements annihilating a vector of a module in
degrees `r₁` and `r₀` have sum and difference annihilating it in every degree `k` with
`r₁ + r₀ ≤ k + 1`.

The product of two elements which anticommute with `b` commutes with `b`.

A square-zero differential commutes with any element `e` satisfying a homotopy identity
`d * h + h * d = 1 - e`.

## Main results

* `Commute.one_sub_smul_left`, `Commute.one_sub_smul_right`: commutation with `1 - a • u`.
* `Commute.add_pow_smul_eq_zero_of_add_le_succ_of_pow_smul_eq_zero`,
  `Commute.sub_pow_smul_eq_zero_of_add_le_succ_of_pow_smul_eq_zero`: nilpotent action of `x + y`
  and `x - y` at each degree `k` with `r₁ + r₀ ≤ k + 1` when commuting `x`, `y` kill `u` at
  degrees `r₁`, `r₀`.
* `TauCeti.commute_of_sq_zero_of_homotopy`: commutation of a square-zero differential with its
  homotopy projector.
* `TauCeti.commute_mul_of_mul_eq_neg_mul`: a product of two elements anticommuting with `b`
  commutes with `b`.
* `Finset.sum_smul_smul_eq_smul_smul`: if the sum of a pairwise commuting family scales `x` by
  `μ`, it scales `p a • x` by `μ` for each member `p a`. The vector `p a • x` may be zero.
-/

public section

namespace Commute

section OneSubSmul

variable {R A : Type*} [Ring A] [SMul R A] [IsScalarTower R A A] [SMulCommClass R A A] {u x : A}

/-- An element commuting with `u` commutes with `1 - a • u`, on the left. -/
theorem one_sub_smul_left (h : Commute u x) (a : R) : Commute (1 - a • u) x :=
  (Commute.one_left x).sub_left (h.smul_left a)

/-- An element commuting with `u` commutes with `1 - a • u`, on the right. -/
theorem one_sub_smul_right (h : Commute x u) (a : R) : Commute x (1 - a • u) :=
  (h.symm.one_sub_smul_left a).symm

end OneSubSmul

section PowSmul

variable {A M : Type*} [AddCommMonoid M] {x y : A} {r₁ r₀ k : ℕ} {u : M}

/-- If commuting elements `x` and `y` of a semiring satisfy `x ^ r₁ • u = 0` and `y ^ r₀ • u = 0`,
then `(x + y) ^ k • u = 0` whenever `r₁ + r₀ ≤ k + 1`. This is the pointwise form of
`Commute.add_pow_eq_zero_of_add_le_succ_of_pow_eq_zero`. -/
theorem add_pow_smul_eq_zero_of_add_le_succ_of_pow_smul_eq_zero [Semiring A] [Module A M]
    (hxy : Commute x y) (hx : x ^ r₁ • u = 0) (hy : y ^ r₀ • u = 0) (hk : r₁ + r₀ ≤ k + 1) :
    (x + y) ^ k • u = 0 := by
  rw [hxy.add_pow', Finset.sum_smul]
  refine Finset.sum_eq_zero fun ij hij ↦ ?_
  rw [smul_assoc]
  -- Each term `x ^ i * y ^ j` has `i ≥ r₁` or `j ≥ r₀`, so it ends in `x ^ r₁` or `y ^ r₀`.
  rcases le_or_gt r₁ ij.1 with h₁ | h₁
  · rw [(hxy.pow_pow ij.1 ij.2).eq, ← pow_sub_mul_pow x h₁, ← mul_assoc, mul_smul, hx, smul_zero,
      smul_zero]
  · have h₂ : r₀ ≤ ij.2 := by have := Finset.mem_antidiagonal.1 hij; omega
    rw [← pow_sub_mul_pow y h₂, ← mul_assoc, mul_smul, hy, smul_zero, smul_zero]

/-- If commuting elements `x` and `y` of a ring satisfy `x ^ r₁ • u = 0` and `y ^ r₀ • u = 0`,
then `(x - y) ^ k • u = 0` whenever `r₁ + r₀ ≤ k + 1`. -/
theorem sub_pow_smul_eq_zero_of_add_le_succ_of_pow_smul_eq_zero [Ring A] [Module A M]
    (hxy : Commute x y) (hx : x ^ r₁ • u = 0) (hy : y ^ r₀ • u = 0) (hk : r₁ + r₀ ≤ k + 1) :
    (x - y) ^ k • u = 0 := by
  rw [sub_eq_add_neg]
  refine hxy.neg_right.add_pow_smul_eq_zero_of_add_le_succ_of_pow_smul_eq_zero hx ?_ hk
  rw [neg_pow, mul_smul, hy, smul_zero]

end PowSmul

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

/-- If `a` and `w` both anticommute with `b`, then their product `a * w` commutes with `b`. -/
theorem commute_mul_of_mul_eq_neg_mul {A : Type*} [Semigroup A] [HasDistribNeg A] {a w b : A}
    (ha : a * b = -(b * a)) (hw : w * b = -(b * w)) : Commute (a * w) b := by
  rw [commute_iff_eq, mul_assoc, hw, mul_neg, ← mul_assoc, ha, neg_mul, neg_neg, mul_assoc]

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
