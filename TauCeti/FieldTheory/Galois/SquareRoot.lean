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
import Mathlib.Algebra.Ring.Commute
import Mathlib.Data.Fintype.Pi

/-!
# Automorphisms acting on square roots

An automorphism `σ` of an `F`-algebra `L` that is a domain sends a square root `x` of an element
of `F` to another square root of it, so `σ x = x` or `σ x = -x`. Consequently an automorphism is
known on such roots once its signs on them are, and a group of automorphisms in which only the
identity fixes each of `n` square roots has at most `2ⁿ` elements.

## Main results

* `TauCeti.apply_eq_or_eq_neg_of_sq_eq`: `σ x = ± x` when `x ^ 2` comes from the base.
* `TauCeti.card_le_two_pow_of_forall_apply_eq_self`: a subgroup in which only the identity fixes
  each of `n` square roots has at most `2ⁿ` elements.
-/

public section

namespace TauCeti

variable {R F L : Type*} [CommRing R] [CommRing F] [CommRing L] [IsDomain L] [Algebra R F]
  [Algebra R L] [Algebra F L] [IsScalarTower R F L]

/-- An automorphism sends a square root of an element of the base ring `R` to plus or minus
itself. -/
theorem apply_eq_or_eq_neg_of_sq_eq (σ : L ≃ₐ[F] L) {x : L} {c : R}
    (hx : x ^ 2 = algebraMap R L c) : σ x = x ∨ σ x = -x :=
  sq_eq_sq_iff_eq_or_eq_neg.mp (by
    rw [← map_pow, hx, IsScalarTower.algebraMap_apply R F L, AlgEquiv.commutes])

/-- A subgroup of `L ≃ₐ[F] L` in which only the identity fixes each of `n` square roots of elements
of `R` has at most `2ⁿ` elements: an element is determined by the signs by which it acts on
them. -/
theorem card_le_two_pow_of_forall_apply_eq_self {n : ℕ} {y : Fin n → L} {c : Fin n → R}
    (hy : ∀ k, y k ^ 2 = algebraMap R L (c k)) (H : Subgroup (L ≃ₐ[F] L))
    (h : ∀ τ ∈ H, (∀ k, τ (y k) = y k) → τ = 1) : Nat.card H ≤ 2 ^ n := by
  classical
  let f : H → Fin n → Bool := fun τ k => decide ((τ : L ≃ₐ[F] L) (y k) = y k)
  have hf : Function.Injective f := by
    intro σ τ hστ
    have hk (k : Fin n) : (σ : L ≃ₐ[F] L) (y k) = (τ : L ≃ₐ[F] L) (y k) := by
      have h := congrFun hστ k
      simp only [f, decide_eq_decide] at h
      rcases apply_eq_or_eq_neg_of_sq_eq (σ : L ≃ₐ[F] L) (hy k) with h1 | h1
      · rw [h1, h.mp h1]
      · rcases apply_eq_or_eq_neg_of_sq_eq (τ : L ≃ₐ[F] L) (hy k) with h2 | h2
        · rw [h.mpr h2, h2]
        · rw [h1, h2]
    have h1 := h ((τ : L ≃ₐ[F] L)⁻¹ * σ) (mul_mem (inv_mem τ.2) σ.2) fun k => by
      rw [AlgEquiv.mul_apply, hk k, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
    exact Subtype.ext (inv_mul_eq_one.mp h1).symm
  simpa using Nat.card_le_card_of_injective f hf

end TauCeti
