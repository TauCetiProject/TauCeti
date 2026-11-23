/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Hom.End
public import Mathlib.Algebra.Ring.Commute
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.NoncommRing

/-!
# Commutation with homotopy projectors, `1 - a • u` and finite sums

An element of a ring commuting with `u` also commutes with `1 - a • u`, for any scalar `a` acting
compatibly with the multiplication. For an operator `u`, `1 - a • u` is the operator whose
generalised kernel at a zero `a` of the Fredholm determinant of `u` carries the Riesz projector.

Each member of a pairwise commuting finite family commutes with the family's sum, so it preserves
the eigenvalue equations of that sum. Commuting additive endomorphisms annihilating a vector in
degrees `r₁` and `r₀` have sum and difference annihilating it in degree `r₁ + r₀`.

The product of two elements which anticommute with `b` commutes with `b`.

Powers of an element against an inhomogeneous recurrence: in a semiring, not necessarily
commutative, let `C` commute with `u` and let `Wₖ` satisfy `C W₀ = d₀` and
`C Wₖ₊₁ = dₖ₊₁ + u Wₖ` for `k < h`. If `dⱼ = 0` for `j < h`, then `C ^ (h + 1) W_h = C ^ h d_h`.
For `C = 1 - a • u`, `Wₖ` the values at `a` of the Hasse derivatives of the Fredholm resolvent of
`u` and `dₖ` the corresponding scalar multiples of `1`, this is the identity behind the Riesz
projector at a good zero `a` of order `h` of the Fredholm determinant: one where the order-`h`
Hasse derivative of the determinant at `a` is moreover a unit, so that `C ^ h d_h` can be
normalised to `C ^ h`.

A square-zero differential commutes with any element `e` satisfying a homotopy identity
`d * h + h * d = 1 - e`.

## Main results

* `Commute.one_sub_smul_left`, `Commute.one_sub_smul_right`: commutation with `1 - a • u`.
* `Commute.pow_succ_mul_eq_pow_mul_of_mul_eq`: `C ^ (h + 1) W_h = C ^ h d_h` when `C` commutes
  with `u` and `Wₖ` satisfies the inhomogeneous recurrence `C W₀ = d₀`, `C Wₖ₊₁ = dₖ₊₁ + u Wₖ`
  for `k < h`, with `dⱼ = 0` for `j < h`.
* `Commute.add_pow_apply_eq_zero`, `Commute.sub_pow_apply_eq_zero`: nilpotent action of `x + y`
  and `x - y` at degree `r₁ + r₀` when commuting additive endomorphisms `x`, `y` kill `u` at
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

/-- Let `C` commute with `u`, and let `Wₖ` satisfy `C W₀ = d₀` and `C Wₖ₊₁ = dₖ₊₁ + u Wₖ` for
`k < h`. If `dⱼ = 0` for `j < h`, then `C ^ (h + 1) W_h = C ^ h d_h`. -/
theorem pow_succ_mul_eq_pow_mul_of_mul_eq {A : Type*} [Semiring A] {C u : A} {W d : ℕ → A}
    (hu : Commute u C) (h0 : C * W 0 = d 0) {h : ℕ}
    (hsucc : ∀ k < h, C * W (k + 1) = d (k + 1) + u * W k) (hd : ∀ j < h, d j = 0) :
    C ^ (h + 1) * W h = C ^ h * d h := by
  induction h with
  | zero => simpa using h0
  | succ h ih =>
    -- `C ^ (h + 1) W_h = 0` by induction, and `u` commutes past `C ^ (h + 1)`
    have hz : C ^ (h + 1) * W h = 0 := by
      rw [ih (fun k hk ↦ hsucc k (by omega)) fun j hj ↦ hd j (by omega), hd h (by omega),
        mul_zero]
    calc C ^ (h + 1 + 1) * W (h + 1) = C ^ (h + 1) * (d (h + 1) + u * W h) := by
          rw [pow_succ, mul_assoc, hsucc h (by omega)]
      _ = C ^ (h + 1) * d (h + 1) + u * (C ^ (h + 1) * W h) := by
          rw [mul_add, (hu.pow_right (h + 1)).symm.left_comm]
      _ = C ^ (h + 1) * d (h + 1) := by rw [hz, mul_zero, add_zero]

/-- If commuting additive endomorphisms `x` and `y` satisfy `(x ^ r₁) u = 0` and `(y ^ r₀) u = 0`,
then `((x + y) ^ (r₁ + r₀)) u = 0`. -/
theorem add_pow_apply_eq_zero {M : Type*} [AddCommMonoid M] {x y : AddMonoid.End M}
    (hxy : Commute x y) {r₁ r₀ : ℕ} {u : M} (hx : (x ^ r₁) u = 0) (hy : (y ^ r₀) u = 0) :
    ((x + y) ^ (r₁ + r₀)) u = 0 := by
  rw [hxy.add_pow']
  refine Finset.sum_induction _ (fun f : AddMonoid.End M ↦ f u = 0)
    (fun f g hf hg ↦ by rw [show (f + g) u = f u + g u from rfl, hf, hg, add_zero]) rfl
    fun ij hij ↦ ?_
  rw [nsmul_eq_mul, AddMonoid.End.coe_mul, Function.comp_apply]
  rcases le_or_gt r₁ ij.1 with h₁ | h₁
  · rw [← Nat.sub_add_cancel h₁, pow_add, mul_assoc, AddMonoid.End.coe_mul, Function.comp_apply,
      ((hxy.pow_left r₁).pow_right ij.2).eq, AddMonoid.End.coe_mul, Function.comp_apply, hx,
      map_zero, map_zero, map_zero]
  · have h₂ : r₀ ≤ ij.2 := by have := Finset.mem_antidiagonal.1 hij; omega
    rw [← Nat.sub_add_cancel h₂, pow_add, ← mul_assoc, AddMonoid.End.coe_mul,
      Function.comp_apply, hy, map_zero, map_zero]

/-- If commuting additive endomorphisms `x` and `y` satisfy `(x ^ r₁) u = 0` and `(y ^ r₀) u = 0`,
then `((x - y) ^ (r₁ + r₀)) u = 0`. -/
theorem sub_pow_apply_eq_zero {M : Type*} [AddCommGroup M] {x y : AddMonoid.End M}
    (hxy : Commute x y) {r₁ r₀ : ℕ} {u : M} (hx : (x ^ r₁) u = 0) (hy : (y ^ r₀) u = 0) :
    ((x - y) ^ (r₁ + r₀)) u = 0 := by
  rw [sub_eq_add_neg]
  refine hxy.neg_right.add_pow_apply_eq_zero hx ?_
  rw [neg_pow, AddMonoid.End.coe_mul, Function.comp_apply, hy, map_zero]

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
