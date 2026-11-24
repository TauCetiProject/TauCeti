/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Colon ideals and residue classes

For a two-sided ideal `I` of a ring `R` and `c : R`, the annihilator of the class of `c` in the
`R`-module `R ⧸ I`, written as the colon ideal
`(⊥ : Submodule R (R ⧸ I)).colon {Ideal.Quotient.mk I c}`, is `{r | r * c ∈ I}`; for commutative
`R` this is the ideal quotient `(I : c)`. This is the form in which associated primes of `R ⧸ I`
appear (`isAssociatedPrime_iff`).

For an ideal `J` of a commutative ring `B` and `b : B`, multiplication by `b` gives the exact
sequence `B ⧸ (J : b) → B ⧸ J → B ⧸ (J + (b))`, without regularity of `b`, and its first map is
injective.

## Main results

* `TauCeti.Ideal.Quotient.mem_colon_singleton_mk`: `r` annihilates the class of `c` in
  `R ⧸ I` exactly when `r * c ∈ I`.
* `TauCeti.ColonQuotient.mulColon`: multiplication by `b` from `B ⧸ (J : b)` to `B ⧸ J`.
* `TauCeti.ColonQuotient.mulColon_injective`: this map is injective.
* `TauCeti.ColonQuotient.exact_mulColon_factorₐ`: the sequence
  `B ⧸ (J : b) → B ⧸ J → B ⧸ (J + (b))` is exact.
-/

public section

open Ideal.Quotient

namespace TauCeti.Ideal.Quotient

variable {R : Type*} [Ring R] {I : Ideal R} [I.IsTwoSided]

/-- An element `r` annihilates the class of `c` in `R ⧸ I` exactly when `r * c ∈ I`. -/
theorem mem_colon_singleton_mk {c r : R} :
    r ∈ (⊥ : Submodule R (R ⧸ I)).colon {mk I c} ↔ r * c ∈ I := by
  -- `R ⧸ I` is an `R`-module as a submodule quotient, so `r • mk I c = mk I (r * c)` is
  -- `Submodule.Quotient.mk_smul` once `mk I` is written as `Submodule.Quotient.mk`.
  rw [Submodule.mem_colon_singleton, ← mk_eq_mk, ← Submodule.Quotient.mk_smul, smul_eq_mul,
    Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]

end TauCeti.Ideal.Quotient

namespace TauCeti.ColonQuotient

variable (R : Type*) {B : Type*} [CommSemiring R] [CommRing B] [Algebra R B]

/-- Multiplication by `b` embeds the quotient by `(J : b)` into the quotient by `J`. -/
def mulColon (J : Ideal B) (b : B) : (B ⧸ J.colon {b}) →ₗ[R] B ⧸ J :=
  (Submodule.mapQ (J.colon {b}) J (LinearMap.mulLeft B b) (by
    intro x hx
    -- Membership in the comap is evaluation of the multiplication map.
    change b * x ∈ J
    simpa only [Submodule.mem_colon_singleton, smul_eq_mul, mul_comm] using hx)).restrictScalars R

/-- On residue classes, `mulColon R J b` is multiplication by `b`. -/
@[simp]
theorem mulColon_mk (J : Ideal B) (b x : B) :
    mulColon R J b (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (b * x) := by
  simp [mulColon, ← Ideal.Quotient.mk_eq_mk]

/-- Multiplication from the quotient by a colon ideal is injective without regularity. -/
theorem mulColon_injective (J : Ideal B) (b : B) : Function.Injective (mulColon R J b) := by
  rw [injective_iff_map_eq_zero]
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  intro hx
  rw [mulColon_mk, Ideal.Quotient.eq_zero_iff_mem] at hx
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  simpa only [Submodule.mem_colon_singleton, smul_eq_mul, mul_comm] using hx

/-- Multiplication followed by quotienting is the exact sequence
`B/(J : b) → B/J → B/(J + (b))`. -/
theorem exact_mulColon_factorₐ (J : Ideal B) (b : B) :
    Function.Exact (mulColon R J b)
      (Ideal.Quotient.factorₐ R (show J ≤ J ⊔ Ideal.span {b} from le_sup_left)).toLinearMap := by
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [AlgHom.toLinearMap_apply, Ideal.Quotient.factorₐ_apply_mk,
    Ideal.Quotient.eq_zero_iff_mem]
  constructor
  · intro hx
    obtain ⟨j, hj, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hz
    refine ⟨Ideal.Quotient.mk _ c, ?_⟩
    rw [mulColon_mk, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hj, zero_add, mul_comm]
  · rintro ⟨y, hy⟩
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [mulColon_mk, Ideal.Quotient.eq] at hy
    have hby : b * y ∈ J ⊔ Ideal.span {b} :=
      Submodule.mem_sup_right (Ideal.mul_mem_right y _ (Ideal.mem_span_singleton_self b))
    exact (Submodule.sub_mem_iff_right _ hby).mp (Submodule.mem_sup_left hy)

end TauCeti.ColonQuotient
