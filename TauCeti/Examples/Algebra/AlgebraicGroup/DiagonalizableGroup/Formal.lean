/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Formal
import TauCeti.RingTheory.Ideal.Operations

/-!
# Checks for the points of the formal diagonalizable group

* The formal points of `D(ℤ)` with values in a local ring `A` are the principal units `1 + 𝔪_A`.
* `(1 + X) ^ 2 - 1 ∈ (2, X) ^ 2` in `ℤ[X]`: the case `p = 2`, `m = 1` of the congruence
  behind the truncation isomorphism.
* For an Artinian local ring `A` of residue characteristic `p` and a prime `ℓ ≠ p`, the formal
  diagonalizable group of `ℤ / ℓ` has only the trivial point: `1 + 𝔪_A` is a `p`-group.
* On coefficients with `𝔪_A ^ 2 = 0` and residue characteristic `2`, the formal points of
  `μ₂ = D̂(ℤ / 2)` and of the formal multiplicative group `D̂(ℤ)` agree.
-/

public section

open IsLocalRing Polynomial

namespace TauCeti.Examples

open DiagonalizableGroup

/-- The formal points of `D(ℤ)` with values in a local ring are the principal units `1 + 𝔪_A`. -/
noncomputable example (R A : Type*) [CommSemiring R] [CommRing A] [Algebra R A] [IsLocalRing A] :
    formalPoints R (Multiplicative ℤ) (maximalIdeal A) ≃* (maximalIdeal A).principalUnitGroup :=
  formalPointsIntMulEquiv R (maximalIdeal A)

/-- `(1 + X) ^ 2 - 1 ∈ (2, X) ^ 2` in `ℤ[X]`. -/
example : (1 + X : ℤ[X]) ^ 2 - 1 ∈ Ideal.span {(2 : ℤ[X]), X} ^ 2 := by
  have h := Ideal.pow_pow_sub_pow_pow_mem_pow_succ (I := Ideal.span {(2 : ℤ[X]), X}) (n := 2)
    (a := 1 + X) (b := 1) (by exact_mod_cast Ideal.subset_span (Set.mem_insert _ _))
    (by simpa using Ideal.subset_span (Set.mem_insert_of_mem _ rfl)) 1
  simpa using h

/-- For an Artinian local ring `A` of residue characteristic `p` and a prime `ℓ ≠ p`, the formal
diagonalizable group of `ℤ / ℓ` has only the trivial point. -/
example (R A : Type*) [CommSemiring R] [CommRing A] [Algebra R A] [IsLocalRing A]
    [IsArtinianRing A] {p ℓ : ℕ} (hp : p.Prime) (hℓ : ℓ.Prime) (hpℓ : p ≠ ℓ)
    [CharP (ResidueField A) p] :
    formalPoints R (Multiplicative (ZMod ℓ)) (maximalIdeal A) = ⊥ := by
  obtain ⟨m, hm⟩ := (isArtinianRing_iff_isNilpotent_maximalIdeal A).mp inferInstance
  refine formalPoints_eq_bot_of_coprime (k := ℓ) (m := m) _ (n := p) ?_ ?_ ?_
    ((Nat.coprime_primes hℓ hp).mpr hpℓ.symm)
  · rw [← residue_eq_zero_iff, map_natCast, CharP.cast_eq_zero]
  · rw [pow_succ, hm, Ideal.zero_eq_bot, Ideal.bot_mul]
  · intro g
    apply Multiplicative.toAdd.injective
    simp

/-- On coefficients with `𝔪_A ^ 2 = 0` and residue characteristic `2`, the formal points of
`μ₂ = D̂(ℤ / 2)` and of the formal multiplicative group `D̂(ℤ)` agree. -/
noncomputable example (R A : Type*) [CommSemiring R] [CommRing A] [Algebra R A] [IsLocalRing A]
    [CharP (ResidueField A) 2] (hA : maximalIdeal A ^ 2 = ⊥) :
    formalPoints R (Multiplicative (Unit → ZMod (2 ^ 1))) (maximalIdeal A) ≃*
      formalPoints R (Multiplicative (Unit → ℤ)) (maximalIdeal A) :=
  formalPointsTorusTruncationMulEquiv R Unit (maximalIdeal A)
    (by rw [← residue_eq_zero_iff, map_natCast, CharP.cast_eq_zero]) hA

end TauCeti.Examples
