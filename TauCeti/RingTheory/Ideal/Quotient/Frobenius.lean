/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import TauCeti.Algebra.CharP.Frobenius.PowRingHom

/-!
# The Frobenius map between quotients of a commutative ring

Let `A` be a commutative ring, `p` a prime and `I, J` ideals of `A` with `p ∈ J` and `x ^ p ∈ J`
for every `x ∈ I`. Then `x mod I ↦ x ^ p mod J` is a well-defined ring homomorphism
`A ⧸ I →+* A ⧸ J`: additivity holds because `p` vanishes in `A ⧸ J`. This is the map
`Φ : R°/ϖ → R°/ϖ^p` in the definition of a perfectoid Tate ring, where `ϖ^p ∣ p`, and the
Frobenius of `A ⧸ p` when `I = J = (p)`.

## Main definitions

* `Ideal.quotientFrobenius I J p hpJ hIJ`: the ring homomorphism `A ⧸ I →+* A ⧸ J`,
  `[x] ↦ [x ^ p]`.

## Main results

* `Ideal.quotientFrobenius_surjective_iff`: it is surjective iff every element of `A` is a
  `p`-th power modulo `J`.
* `Ideal.quotientFrobenius_injective_iff`: it is injective iff `y ^ p ∈ J` forces `y ∈ I`.
-/

public section

namespace Ideal

variable {A : Type*} [CommRing A] (I J : Ideal A) (p : ℕ) [Fact p.Prime]

/-- The Frobenius map `A ⧸ I →+* A ⧸ J`, `[x] ↦ [x ^ p]`, for a prime `p` lying in `J` and ideals
with `x ^ p ∈ J` for every `x ∈ I`. It is the `p`-th power map `TauCeti.powRingHom` of `A ⧸ J`,
in which `p` vanishes, composed with the quotient map and descended to `A ⧸ I`. -/
def quotientFrobenius (hpJ : (p : A) ∈ J) (hIJ : ∀ x ∈ I, x ^ p ∈ J) : A ⧸ I →+* A ⧸ J :=
  Quotient.lift I
    ((TauCeti.powRingHom (A ⧸ J) p
      (by rw [← map_natCast (Quotient.mk J), Quotient.eq_zero_iff_mem]; exact hpJ)).comp
      (Quotient.mk J))
    fun x hx ↦ by
      rw [RingHom.comp_apply, TauCeti.powRingHom_apply, ← map_pow, Quotient.eq_zero_iff_mem]
      exact hIJ x hx

variable {I J p}

@[simp]
theorem quotientFrobenius_mk (hpJ : (p : A) ∈ J) (hIJ : ∀ x ∈ I, x ^ p ∈ J) (x : A) :
    quotientFrobenius I J p hpJ hIJ (Quotient.mk I x) = Quotient.mk J (x ^ p) := by
  rw [quotientFrobenius, Quotient.lift_mk, RingHom.comp_apply, TauCeti.powRingHom_apply, map_pow]

/-- The Frobenius `A ⧸ I → A ⧸ J` is surjective exactly when every element of `A` is a `p`-th
power modulo `J`. -/
theorem quotientFrobenius_surjective_iff (hpJ : (p : A) ∈ J) (hIJ : ∀ x ∈ I, x ^ p ∈ J) :
    Function.Surjective (quotientFrobenius I J p hpJ hIJ) ↔ ∀ x : A, ∃ y : A, x - y ^ p ∈ J := by
  refine ⟨fun h x ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨y, hy⟩ := h (Quotient.mk J x)
    obtain ⟨y, rfl⟩ := Quotient.mk_surjective y
    rw [quotientFrobenius_mk, eq_comm, Quotient.eq] at hy
    exact ⟨y, hy⟩
  · intro x
    obtain ⟨x, rfl⟩ := Quotient.mk_surjective x
    obtain ⟨y, hy⟩ := h x
    exact ⟨Quotient.mk I y, by rw [quotientFrobenius_mk, eq_comm, Quotient.eq]; exact hy⟩

/-- The Frobenius `A ⧸ I → A ⧸ J` is injective exactly when `y ^ p ∈ J` forces `y ∈ I`. -/
theorem quotientFrobenius_injective_iff (hpJ : (p : A) ∈ J) (hIJ : ∀ x ∈ I, x ^ p ∈ J) :
    Function.Injective (quotientFrobenius I J p hpJ hIJ) ↔ ∀ y : A, y ^ p ∈ J → y ∈ I := by
  rw [injective_iff_map_eq_zero]
  refine ⟨fun h y hy ↦ ?_, fun h y hy ↦ ?_⟩
  · rw [← Quotient.eq_zero_iff_mem]
    exact h _ (by rw [quotientFrobenius_mk, Quotient.eq_zero_iff_mem]; exact hy)
  · obtain ⟨y, rfl⟩ := Quotient.mk_surjective y
    rw [quotientFrobenius_mk, Quotient.eq_zero_iff_mem] at hy
    exact Quotient.eq_zero_iff_mem.mpr (h y hy)

end Ideal
