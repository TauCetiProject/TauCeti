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
import Mathlib.Algebra.Algebra.Field
import Mathlib.Algebra.Ring.Commute
import Mathlib.Data.Fintype.Pi
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Tactic.IntervalCases

/-!
# Automorphisms acting on square roots

An automorphism `σ` of an `F`-algebra `L` that is a domain sends a square root `x` of an element
of `F` to another square root of it, so `σ x = x` or `σ x = -x`. Consequently an automorphism is
known on such roots once its signs on them are, and a group of automorphisms in which only the
identity fixes each of `n` square roots has at most `2ⁿ` elements.

## Main results

* `AlgEquiv.apply_eq_or_eq_neg_of_sq_eq`: `σ x = ± x` when `x ^ 2` comes from the base.
* `AlgEquiv.ne_one_of_apply_eq_neg`: an automorphism negating a nonzero element is not
  the identity.
* `TauCeti.card_le_two_pow_of_forall_apply_eq_self`: a subgroup in which only the identity fixes
  each of `n` square roots has at most `2ⁿ` elements.
* `TauCeti.card_eq_four_of_exists_apply_eq_neg`: an exponent-two subgroup of order at most four
  that negates two nonzero elements and their product has order four.
-/

public section

namespace AlgEquiv

variable {R F L : Type*} [CommRing R] [CommRing F] [CommRing L] [IsDomain L] [Algebra R F]
  [Algebra R L] [Algebra F L] [IsScalarTower R F L]

/-- An automorphism sends a square root of an element of the base ring `R` to plus or minus
itself. -/
theorem apply_eq_or_eq_neg_of_sq_eq (σ : L ≃ₐ[F] L) {x : L} {c : R}
    (hx : x ^ 2 = algebraMap R L c) : σ x = x ∨ σ x = -x :=
  sq_eq_sq_iff_eq_or_eq_neg.mp (by
    rw [← map_pow, hx, IsScalarTower.algebraMap_apply R F L, AlgEquiv.commutes])

/-- Cancel a fixed nonzero factor to show that an automorphism fixes the other factor. -/
theorem apply_eq_self_of_apply_mul_eq_mul (σ : L ≃ₐ[F] L) {x y : L} (hx : x ≠ 0)
    (hσx : σ x = x) (h : σ (x * y) = x * y) : σ y = y := by
  rw [map_mul, hσx] at h
  exact mul_left_cancel₀ hx h

/-- An automorphism that negates a nonzero element is not the identity. -/
theorem ne_one_of_apply_eq_neg [CharZero L] (σ : L ≃ₐ[F] L) {x : L} (hx : x ≠ 0)
    (h : σ x = -x) : σ ≠ 1 := by
  rintro rfl
  exact hx (CharZero.eq_neg_self_iff.mp h)

variable {F L : Type*} [CommRing F] [Field L] [Algebra F L]

/-- An automorphism negating `x / e` negates `x` when it fixes the nonzero element `e`. -/
theorem apply_eq_neg_of_apply_div_eq_neg (σ : L ≃ₐ[F] L) {x e : L} (he : e ≠ 0)
    (hσe : σ e = e) (h : σ (x / e) = -(x / e)) : σ x = -x := by
  rw [map_div₀, hσe, div_eq_iff he] at h
  rw [h, neg_mul, div_mul_cancel₀ _ he]

end AlgEquiv

namespace TauCeti

variable {R F L : Type*} [CommRing R] [CommRing F] [CommRing L] [IsDomain L] [Algebra R F]
  [Algebra R L] [Algebra F L] [IsScalarTower R F L]

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
      rcases AlgEquiv.apply_eq_or_eq_neg_of_sq_eq (σ : L ≃ₐ[F] L) (hy k) with h1 | h1
      · rw [h1, h.mp h1]
      · rcases AlgEquiv.apply_eq_or_eq_neg_of_sq_eq (τ : L ≃ₐ[F] L) (hy k) with h2 | h2
        · rw [h.mpr h2, h2]
        · rw [h1, h2]
    have h1 := h ((τ : L ≃ₐ[F] L)⁻¹ * σ) (mul_mem (inv_mem τ.2) σ.2) fun k => by
      rw [AlgEquiv.mul_apply, hk k, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
    exact Subtype.ext (inv_mul_eq_one.mp h1).symm
  simpa using Nat.card_le_card_of_injective f hf

/-- A finite subgroup of `L ≃ₐ[F] L` of exponent `2` with at most four elements, containing
elements that negate nonzero `y`, nonzero `z`, and `y * z`, has exactly four elements. -/
theorem card_eq_four_of_exists_apply_eq_neg {F L : Type*} [CommRing F] [CommRing L] [IsDomain L]
    [CharZero L] [Algebra F L] (H : Subgroup (L ≃ₐ[F] L)) [Finite H]
    (hexp : ∀ σ ∈ H, σ ^ 2 = 1) (hle : Nat.card H ≤ 4) {y z : L} (hy : y ≠ 0)
    (hz : z ≠ 0) (h₁ : ∃ τ ∈ H, τ y = -y) (h₂ : ∃ τ ∈ H, τ z = -z)
    (h₃ : ∃ τ ∈ H, τ (y * z) = -(y * z)) : Nat.card H = 4 := by
  obtain ⟨τ₁, hτ₁, hτ₁y⟩ := h₁
  obtain ⟨τ₂, hτ₂, hτ₂z⟩ := h₂
  obtain ⟨τ₃, hτ₃, hτ₃yz⟩ := h₃
  have hpos : 0 < Nat.card H := Nat.card_pos
  interval_cases hc : Nat.card H
  · have : Subsingleton H := (Nat.card_eq_one_iff_unique.mp hc).1
    exact absurd (congrArg Subtype.val (Subsingleton.elim (⟨τ₁, hτ₁⟩ : H) 1))
      (AlgEquiv.ne_one_of_apply_eq_neg τ₁ hy hτ₁y)
  · obtain ⟨u, -, hu⟩ := (Nat.card_eq_two_iff' (1 : H)).mp hc
    have heq {τ : L ≃ₐ[F] L} (hτ : τ ∈ H) (hτ1 : τ ≠ 1) : τ = u :=
      congrArg Subtype.val (hu ⟨τ, hτ⟩ fun h => hτ1 (congrArg Subtype.val h))
    have h12 : τ₃ = τ₁ :=
      (heq hτ₃ (AlgEquiv.ne_one_of_apply_eq_neg τ₃ (mul_ne_zero hy hz) hτ₃yz)).trans
        (heq hτ₁ (AlgEquiv.ne_one_of_apply_eq_neg τ₁ hy hτ₁y)).symm
    have h22 : τ₃ = τ₂ :=
      (heq hτ₃ (AlgEquiv.ne_one_of_apply_eq_neg τ₃ (mul_ne_zero hy hz) hτ₃yz)).trans
        (heq hτ₂ (AlgEquiv.ne_one_of_apply_eq_neg τ₂ hz hτ₂z)).symm
    rw [h12, map_mul, hτ₁y, h12.symm.trans h22, hτ₂z, neg_mul_neg,
      CharZero.eq_neg_self_iff] at hτ₃yz
    exact absurd hτ₃yz (mul_ne_zero hy hz)
  · obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := H) 3 (hp := ⟨Nat.prime_three⟩)
      (by simp [hc])
    have h2 : g ^ 2 = 1 := Subtype.ext (hexp g g.2)
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hg] at this
    norm_num at this
  · rfl

end TauCeti
