/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Ring.Commute
import Mathlib.Tactic.NoncommRing

/-!
# Commutation with homotopy projectors, `1 - a • u` and finite sums

An element of a ring commuting with `u` also commutes with `1 - a • u`, for any scalar `a` acting
compatibly with the multiplication. For an operator `u`, `1 - a • u` is the operator whose
generalised kernel at a zero `a` of the Fredholm determinant of `u` carries the Riesz projector.

Each member of a pairwise commuting finite family commutes with the family's sum, so it preserves
the eigenvalue equations of that sum.

The product of two elements which anticommute with `b` commutes with `b`. If `F * F = 1`, the
commutator `F * X - X * F` anticommutes with `F`; an element `γ` anticommuting with `F` turns the
anticommutator `F * X + X * F` into minus the commutator of `F` with `γ * X`; and if `η`
anticommutes with `F`, the anticommutator of `X * η` with `F` is `(F * X - X * F) * η`. These are
the algebraic steps behind the commutator identities of the conditional trace of a Fredholm module.

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
* `TauCeti.commute_of_sq_zero_of_homotopy`: commutation of a square-zero differential with its
  homotopy projector.
* `TauCeti.commute_mul_of_mul_eq_neg_mul`: a product of two elements anticommuting with `b`
  commutes with `b`.
* `TauCeti.mul_mul_sub_mul_eq_neg_of_mul_self_eq_one`: if `F * F = 1`, the commutator
  `F * X - X * F` anticommutes with `F`.
* `TauCeti.mul_mul_add_mul_eq_neg_of_mul_eq_neg_mul`: if `γ` anticommutes with `F`, then
  `γ * (F * X + X * F) = -(F * (γ * X) - γ * X * F)`.
* `TauCeti.mul_mul_add_mul_mul_eq_of_mul_eq_neg_mul`: if `η` anticommutes with `F`, then
  `F * (X * η) + X * η * F = (F * X - X * F) * η`.
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

/-- If `F * F = 1`, the commutator `F * X - X * F` anticommutes with `F`. -/
theorem mul_mul_sub_mul_eq_neg_of_mul_self_eq_one {A : Type*} [Ring A] {F : A} (hF : F * F = 1)
    (X : A) : F * (F * X - X * F) = -((F * X - X * F) * F) := by
  have h : F * (F * X - X * F) + (F * X - X * F) * F = F * F * X - X * (F * F) := by
    noncomm_ring
  rw [eq_neg_iff_add_eq_zero, h, hF, one_mul, mul_one, sub_self]

/-- If `γ` anticommutes with `F`, then `γ (F X + X F)` is minus the commutator of `F` with
`γ X`. -/
theorem mul_mul_add_mul_eq_neg_of_mul_eq_neg_mul {A : Type*} [Ring A] {F γ : A}
    (hγ : γ * F = -(F * γ)) (X : A) :
    γ * (F * X + X * F) = -(F * (γ * X) - γ * X * F) := by
  calc γ * (F * X + X * F) = γ * F * X + γ * X * F := by noncomm_ring
    _ = -(F * γ) * X + γ * X * F := by rw [hγ]
    _ = _ := by noncomm_ring

/-- If `η` anticommutes with `F`, the anticommutator of `X η` with `F` is `(F X - X F) η`. -/
theorem mul_mul_add_mul_mul_eq_of_mul_eq_neg_mul {A : Type*} [Ring A] {F η : A}
    (hη : F * η = -(η * F)) (X : A) :
    F * (X * η) + X * η * F = (F * X - X * F) * η := by
  have h : η * F = -(F * η) := by rw [hη, neg_neg]
  calc F * (X * η) + X * η * F = F * X * η + X * (η * F) := by noncomm_ring
    _ = _ := by rw [h]; noncomm_ring

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
