/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Different.Complementary
public import TauCeti.FieldTheory.FunctionField.Different.Divisor
public import TauCeti.FieldTheory.FunctionField.Divisor.Automorphism

/-!
# The different exponent under the Galois action

Let `F / k` be a field extension and `F' / F` a finite separable extension.  An
`F`-automorphism `σ` of `F'` moves the places of `F' / k` (`TauCeti.Place.instMulActionAlgEquiv`)
without moving the places of `F / k` below them.  This file proves that it also preserves the
different exponent: `d(σ • P' ∣ P) = d(P' ∣ P)`.  Together with the transitivity of the Galois
action on the places over a place, this gives the remaining part of Stichtenoth's Corollary 3.7.2:
in a finite Galois extension `F' / F` all places over a given place of `F` share one different
exponent, as they share one ramification index and one relative degree
(`TauCeti.Place.ramificationIdx_eq_of_restrict_eq`,
`TauCeti.Place.relativeDegree_eq_of_restrict_eq`).  At the level of divisors, the different
divisor `Diff(F' / F)` is fixed by every `F`-automorphism of `F'`.

The different exponent is read off the different ideal of the local model `𝒪_P ⊆ 𝒪'_P`, where
`𝒪'_P` is the integral closure in `F'` of the valuation ring `𝒪_P` of `P`.  Since `σ` fixes `F`, it
maps `𝒪'_P` onto itself and preserves the trace of `F' / F`, so it preserves the complementary
module `C_P = {z ∣ Tr_{F'/F} (z · 𝒪'_P) ⊆ 𝒪_P}` and hence the different ideal, the inverse of
`C_P` (`TauCeti.galRestrict_apply_mem_differentIdeal_iff`).  An element of the different ideal of
order exactly `d(P' ∣ P)` at `P'` (`TauCeti.Place.exists_mem_differentIdeal_ord_eq`) is carried to
an element of the different ideal of the same order at `σ • P'`, which bounds `d(σ • P' ∣ P)` from
above; applying this to `σ⁻¹` gives the reverse bound.

## Main results

* `TauCeti.Place.differentExponent_smul`: an `F`-automorphism of `F'` preserves the different
  exponent.
* `TauCeti.Place.differentExponent_eq_of_restrict_eq`: **the different exponent is constant on the
  places over a place** in a finite Galois extension (Stichtenoth, Corollary 3.7.2).
* `TauCeti.Divisor.smul_different`: an `F`-automorphism of `F'` fixes the different divisor.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Theorem 3.7.1 and Corollary 3.7.2.
-/

public section

namespace TauCeti

universe u v v'

variable {k : Type u} {F : Type v} {F' : Type v'}
variable [Field k] [Field F] [Field F']
variable [Algebra k F] [Algebra k F'] [Algebra F F'] [IsScalarTower k F F']
variable [FiniteDimensional F F']

namespace Place

attribute [local instance 10] algebraIntegersExtension isScalarTowerIntegersExtension

section Action

variable [Algebra.IsSeparable F F']

/-- The different exponent at `σ • P'` is at most the different exponent at `P'`; the reverse
inequality is this one for `σ⁻¹`. -/
private theorem differentExponent_smul_le (σ : F' ≃ₐ[F] F') (P' : Place k F') :
    differentExponent k F (σ • P') ≤ differentExponent k F P' := by
  -- An element `y` of the different ideal has order `d(P' ∣ P)` at `P'`, and its image under `σ`
  -- lies in the different ideal and has the same order at `σ • P'`.
  obtain ⟨y, hy, hy0, hord⟩ := exists_mem_differentIdeal_ord_eq k F P'
  set y' := galRestrict (P'.restrict k F).integers F F' _ σ y
  have hy' : y' ∈ differentIdeal _ _ := galRestrict_apply_mem_differentIdeal_iff.mpr hy
  have hyy' : algebraMap _ F' y' = σ (algebraMap _ F' y) := algebraMap_galRestrict_apply _ σ y
  have hy'0 : y' ≠ 0 := by simpa [y'] using hy0
  -- the local model at `σ • P'` is the one at `P'`, as the two places lie over the same place
  have key : ∀ P : Place k F, (σ • P').restrict k F = P →
      ∀ z ∈ differentIdeal P.integers (integralClosure P.integers F'), z ≠ 0 →
        (differentExponent k F (σ • P') : ℤ) ≤ (σ • P').ord (algebraMap _ F' z) := by
    rintro P rfl z hz hz0
    exact differentExponent_le_ord_of_mem_differentIdeal k F (σ • P') hz hz0
  have hle := key _ (restrict_smul σ P') y' hy' hy'0
  rw [hyy', ord_smul_apply, hord] at hle
  exact_mod_cast hle

/-- **An `F`-automorphism of `F'` preserves the different exponent**: `d(σ • P' ∣ P) = d(P' ∣ P)`
for every place `P'` of `F' / k` over the place `P` of `F / k`. -/
@[simp]
theorem differentExponent_smul (σ : F' ≃ₐ[F] F') (P' : Place k F') :
    differentExponent k F (σ • P') = differentExponent k F P' := by
  refine le_antisymm (differentExponent_smul_le σ P') ?_
  simpa using differentExponent_smul_le σ⁻¹ (σ • P')

end Action

/-- **The different exponent is constant on a fibre** (Stichtenoth, Corollary 3.7.2): in a finite
Galois extension `F' / F`, two places of `F' / k` over the same place of `F / k` have the same
different exponent. -/
theorem differentExponent_eq_of_restrict_eq [IsGalois F F'] {P Q : Place k F'}
    (h : P.restrict k F = Q.restrict k F) :
    differentExponent k F P = differentExponent k F Q := by
  obtain ⟨σ, rfl⟩ := exists_smul_eq_of_restrict_eq h
  rw [differentExponent_smul]

end Place

namespace Divisor

variable [Algebra.IsSeparable F F']

/-- **An `F`-automorphism of `F'` fixes the different divisor** `Diff(F' / F)`, as it preserves the
different exponent at every place. -/
@[simp]
theorem smul_different (hF : IsFunctionField k F) (σ : F' ≃ₐ[F] F') :
    σ • different k F' hF = different k F' hF := by
  ext P'
  rw [AlgebraicGeometry.WeilDivisor.coeff_smul, coeff_different, coeff_different,
    Place.differentExponent_smul]

end Divisor

end TauCeti
