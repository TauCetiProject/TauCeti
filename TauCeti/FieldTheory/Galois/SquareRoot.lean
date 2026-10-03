/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.SetTheory.Cardinal.Finite
import TauCeti.Algebra.Algebra.Equiv
import Mathlib.Algebra.Ring.Commute
import Mathlib.Data.Fintype.Pi
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.IntervalCases

/-!
# Automorphisms acting on square roots

An automorphism `σ` of a commutative `F`-algebra `L` without zero divisors sends a square root `x`
of an element of `F` to another square root of it, so `σ x = x` or `σ x = -x`. An algebra tower
also allows the radicands to come from a smaller semiring. Consequently an automorphism is
known on such roots once its signs on them are, and a group of automorphisms in which only the
identity fixes each of `n` square roots has at most `2ⁿ` elements.

## Main results

* `AlgEquiv.apply_eq_or_eq_neg_of_sq_eq`: `σ x = ± x` when `x ^ 2` comes from the base.
* `Subgroup.card_le_two_pow_of_forall_apply_eq_self`: a subgroup in which only the identity fixes
  each of `n` square roots has at most `2ⁿ` elements.
* `Subgroup.card_eq_four_of_exists_apply_eq_neg`: a finite subgroup of order at most four
  that negates two elements and their nonzero product has order four when multiplication by
  `2` is injective.
-/

public section

namespace AlgEquiv

variable {R F L : Type*} [CommSemiring R] [CommSemiring F] [CommRing L] [NoZeroDivisors L]
  [Algebra R F] [Algebra R L] [Algebra F L] [IsScalarTower R F L]

/-- An automorphism sends a square root of an element of the base semiring `R` to plus or minus
itself. -/
theorem apply_eq_or_eq_neg_of_sq_eq (σ : L ≃ₐ[F] L) {x : L} {c : R}
    (hx : x ^ 2 = algebraMap R L c) : σ x = x ∨ σ x = -x :=
  sq_eq_sq_iff_eq_or_eq_neg.mp (by
    rw [← map_pow, hx, IsScalarTower.algebraMap_apply R F L, AlgEquiv.commutes])

end AlgEquiv

namespace Subgroup

variable {R F L : Type*} [CommSemiring R] [CommSemiring F] [CommRing L] [NoZeroDivisors L]
  [Algebra R F] [Algebra R L] [Algebra F L] [IsScalarTower R F L]

/-- A subgroup of `L ≃ₐ[F] L` in which only the identity fixes each of `n` square roots of elements
of `R` has at most `2ⁿ` elements: an element is determined by the signs by which it acts on
them. -/
theorem card_le_two_pow_of_forall_apply_eq_self (H : Subgroup (L ≃ₐ[F] L))
    {n : ℕ} {y : Fin n → L} {c : Fin n → R} (hy : ∀ k, y k ^ 2 = algebraMap R L (c k))
    (h : ∀ τ ∈ H, (∀ k, τ (y k) = y k) → τ = 1) : Nat.card H ≤ 2 ^ n := by
  classical
  let f : H → Fin n → Bool := fun τ k => decide ((τ : L ≃ₐ[F] L) (y k) = y k)
  have hf : Function.Injective f := by
    intro σ τ hστ
    have hk (k : Fin n) : (σ : L ≃ₐ[F] L) (y k) = (τ : L ≃ₐ[F] L) (y k) := by
      have h := congrFun hστ k
      simp only [f, decide_eq_decide] at h
      rcases AlgEquiv.apply_eq_or_eq_neg_of_sq_eq (σ : L ≃ₐ[F] L) (hy k) with h1 | h1
      · rw [h1, h.mp h1]
      · rcases AlgEquiv.apply_eq_or_eq_neg_of_sq_eq (τ : L ≃ₐ[F] L) (hy k) with h2 | h2
        · rw [h.mpr h2, h2]
        · rw [h1, h2]
    have h1 := h ((τ : L ≃ₐ[F] L)⁻¹ * σ) (mul_mem (inv_mem τ.2) σ.2) fun k => by
      simp only [AlgEquiv.mul_apply, hk k, AlgEquiv.coe_inv, AlgEquiv.symm_apply_apply]
    exact Subtype.ext (inv_mul_eq_one.mp h1).symm
  simpa using Nat.card_le_card_of_injective f hf

/-- A finite subgroup of `L ≃ₐ[F] L` with at most four elements, containing elements that negate
`y`, `z`, and their nonzero product, has exactly four elements when multiplication by `2` is
injective. -/
theorem card_eq_four_of_exists_apply_eq_neg {F L : Type*} [CommSemiring F] [Ring L]
    [Algebra F L] (H : Subgroup (L ≃ₐ[F] L)) [Finite H] (h2 : IsLeftRegular (2 : L))
    (hle : Nat.card H ≤ 4) {y z : L} (hyz : y * z ≠ 0)
    (h₁ : ∃ τ ∈ H, τ y = -y) (h₂ : ∃ τ ∈ H, τ z = -z)
    (h₃ : ∃ τ ∈ H, τ (y * z) = -(y * z)) : Nat.card H = 4 := by
  have hy := left_ne_zero_of_mul hyz
  have hz := right_ne_zero_of_mul hyz
  obtain ⟨τ₁, hτ₁, hτ₁y⟩ := h₁
  obtain ⟨τ₂, hτ₂, hτ₂z⟩ := h₂
  obtain ⟨τ₃, hτ₃, hτ₃yz⟩ := h₃
  have hpos : 0 < Nat.card H := Nat.card_pos
  interval_cases hc : Nat.card H
  · have : Subsingleton H := (Nat.card_eq_one_iff_unique.mp hc).1
    exact absurd (congrArg Subtype.val (Subsingleton.elim (⟨τ₁, hτ₁⟩ : H) 1))
      (AlgEquiv.ne_one_of_apply_eq_neg τ₁ h2 hy hτ₁y)
  · obtain ⟨u, -, hu⟩ := (Nat.card_eq_two_iff' (1 : H)).mp hc
    have heq {τ : L ≃ₐ[F] L} (hτ : τ ∈ H) (hτ1 : τ ≠ 1) : τ = u :=
      congrArg Subtype.val (hu ⟨τ, hτ⟩ fun h => hτ1 (congrArg Subtype.val h))
    have h12 : τ₃ = τ₁ :=
      (heq hτ₃ (AlgEquiv.ne_one_of_apply_eq_neg τ₃ h2 hyz hτ₃yz)).trans
        (heq hτ₁ (AlgEquiv.ne_one_of_apply_eq_neg τ₁ h2 hy hτ₁y)).symm
    have h22 : τ₃ = τ₂ :=
      (heq hτ₃ (AlgEquiv.ne_one_of_apply_eq_neg τ₃ h2 hyz hτ₃yz)).trans
        (heq hτ₂ (AlgEquiv.ne_one_of_apply_eq_neg τ₂ h2 hz hτ₂z)).symm
    rw [h12, map_mul, hτ₁y, h12.symm.trans h22, hτ₂z, neg_mul_neg] at hτ₃yz
    exact False.elim
      (AlgEquiv.ne_one_of_apply_eq_neg (1 : L ≃ₐ[F] L) h2 hyz hτ₃yz rfl)
  · have hpow : τ₁ ^ 3 = 1 := by
      simpa only [hc, Subgroup.coe_pow, Subgroup.coe_one] using
        congrArg Subtype.val (pow_card_eq_one' (x := (⟨τ₁, hτ₁⟩ : H)))
    have hneg := congrArg (fun σ : L ≃ₐ[F] L => σ y) hpow
    simp only [pow_succ, pow_zero, AlgEquiv.mul_apply, AlgEquiv.one_apply, hτ₁y,
      map_neg, neg_neg] at hneg
    exact False.elim (AlgEquiv.ne_one_of_apply_eq_neg (1 : L ≃ₐ[F] L) h2 hy hneg.symm rfl)
  · rfl

end Subgroup
