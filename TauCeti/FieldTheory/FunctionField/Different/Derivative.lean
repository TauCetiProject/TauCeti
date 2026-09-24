/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Different.Complementary

/-!
# The different exponent is bounded by the derivative of a generating equation

Let `F' / k'` be an extension of the field extension `F / k` with `F' / F` finite and separable,
let `P'` be a place of `F'` over the place `P` of `F`, and suppose `F' = F(y)`. If `y` is a root
of a monic polynomial `ψ` with coefficients in the valuation ring `𝒪_P`, then

`d(P' ∣ P) ≤ ord_{P'} (ψ'(y))`

provided `ψ'(y) ≠ 0` (Stichtenoth, Theorem 3.5.10(a), where `ψ` is the minimal polynomial of
`y`). This is the tool that computes different exponents from an explicit equation: a place at
which `ψ'(y)` is a unit is unramified, with `d(P' ∣ P) = 0`.

The bound comes from Mathlib's conductor formula for the different ideal: the value `φ'(y)` of
the derivative of the minimal polynomial `φ` of `y` over `𝒪_P` lies in the different ideal of the
local model `𝒪_P ⊆ 𝒪'_P` (`aeval_derivative_mem_differentIdeal`). Since `𝒪_P` is integrally
closed, `φ` divides `ψ` in `𝒪_P[X]`, so `ψ'(y)` is a multiple of `φ'(y)` in `𝒪'_P` and lies in the
different ideal too. Allowing any monic `ψ` rather than only the minimal polynomial means that no
irreducibility has to be checked: for a radical extension one may take `ψ = X ^ n - u` whatever
the degree of `F' / F`.

## Main results

* `TauCeti.Place.differentExponent_le_ord_aeval_derivative`: `d(P' ∣ P) ≤ ord_{P'} (ψ'(y))`.
* `TauCeti.Place.differentExponent_eq_zero_of_valuation_aeval_derivative_eq_one`: if `ψ'(y)` is a
  unit at `P'`, then `d(P' ∣ P) = 0`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Theorem 3.5.10.
-/

public section

open Polynomial

open scoped IntermediateField

namespace TauCeti

namespace Place

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k' F'] [Algebra F F'] [Algebra k F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']
variable [FiniteDimensional F F'] [Algebra.IsSeparable F F']

attribute [local instance 10] algebraIntegersExtension isScalarTowerIntegersExtension

variable (k F) {P' : Place k' F'}

/-- **The different exponent is bounded by the derivative of a generating equation**
(Stichtenoth, Theorem 3.5.10(a)): if `F' = F(y)` and `y` is a root of a monic `ψ ∈ F[X]` whose
coefficients are regular at the place `P` below `P'`, then `d(P' ∣ P) ≤ ord_{P'} (ψ'(y))`, as
long as `ψ'(y) ≠ 0`. Stichtenoth takes `ψ` to be the minimal polynomial of `y`; any monic multiple
of it with coefficients in `𝒪_P` works as well. -/
theorem differentExponent_le_ord_aeval_derivative {y : F'} (hgen : F⟮y⟯ = ⊤) {ψ : F[X]}
    (hψ : ψ.Monic) (hcoeff : ∀ i, ψ.coeff i ∈ (P'.restrict k F).integers)
    (hy : aeval y ψ = 0) (hψ' : aeval y (derivative ψ) ≠ 0) :
    (differentExponent k F P' : ℤ) ≤ P'.ord (aeval y (derivative ψ)) := by
  set A := (P'.restrict k F).integers
  -- Lift `ψ` to a monic polynomial `q` over `𝒪_P`.
  obtain ⟨q, hq, -, hqm⟩ := lifts_and_degree_eq_and_monic
    ((lifts_iff_coeff_lifts (f := algebraMap A F) ψ).mpr fun i ↦ ⟨⟨_, hcoeff i⟩, rfl⟩) hψ
  have hqy : aeval y q = 0 := by rw [← aeval_map_algebraMap F, hq, hy]
  -- So `y` is integral over `𝒪_P`: it is an element `x` of the local model `𝒪'_P`.
  have hint : IsIntegral A y := ⟨q, hqm, by rwa [← aeval_def]⟩
  set x : integralClosure A F' := ⟨y, hint⟩
  have hx : algebraMap (integralClosure A F') F' x = y := rfl
  have hgen' : Algebra.adjoin F {algebraMap (integralClosure A F') F' x} = ⊤ := by
    rw [hx, ← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic y), hgen, IntermediateField.top_toSubalgebra]
  have hinj : Function.Injective (algebraMap (integralClosure A F') F') :=
    FaithfulSMul.algebraMap_injective _ _
  have hqx : aeval x q = 0 := hinj (by rw [← aeval_algebraMap_apply, hx, hqy, map_zero])
  -- The minimal polynomial of `x` over the integrally closed `𝒪_P` divides `q`, so `q'(x)` is a
  -- multiple of the element `φ'(x)` of the different ideal.
  obtain ⟨h, hh⟩ := minpoly.isIntegrallyClosed_dvd (integralClosure.isIntegral x) hqx
  have hmem : aeval x (derivative q) ∈
      differentIdeal A (integralClosure A F') := by
    rw [hh, derivative_mul, map_add, map_mul, map_mul, minpoly.aeval, zero_mul, add_zero]
    exact Ideal.mul_mem_right _ _ (aeval_derivative_mem_differentIdeal A F F' x hgen')
  have hval : algebraMap (integralClosure A F') F' (aeval x (derivative q)) =
      aeval y (derivative ψ) := by
    rw [← aeval_algebraMap_apply, hx, ← hq, derivative_map, aeval_map_algebraMap]
  have hne : aeval x (derivative q) ≠ 0 := by
    rintro h0
    rw [h0, map_zero] at hval
    exact hψ' hval.symm
  rw [← hval]
  exact differentExponent_le_ord_of_mem_differentIdeal k F P' hmem hne

/-- **A place at which the derivative of a generating equation is a unit is unramified**
(Stichtenoth, Theorem 3.5.10(a)): if `F' = F(y)`, `y` is a root of a monic `ψ ∈ F[X]` whose
coefficients are regular at the place `P` below `P'`, and `ψ'(y)` is a unit at `P'`, then
`d(P' ∣ P) = 0`. -/
theorem differentExponent_eq_zero_of_valuation_aeval_derivative_eq_one {y : F'}
    (hgen : F⟮y⟯ = ⊤) {ψ : F[X]} (hψ : ψ.Monic)
    (hcoeff : ∀ i, ψ.coeff i ∈ (P'.restrict k F).integers) (hy : aeval y ψ = 0)
    (hψ' : P'.valuation (aeval y (derivative ψ)) = 1) :
    differentExponent k F P' = 0 := by
  have hne : aeval y (derivative ψ) ≠ 0 := fun h0 ↦ by simp [h0] at hψ'
  have hord : P'.ord (aeval y (derivative ψ)) = 0 := by
    rw [P'.ord_eq_iff_valuation_eq_exp_neg hne, neg_zero, WithZero.exp_zero, hψ']
  have := differentExponent_le_ord_aeval_derivative k F hgen hψ hcoeff hy hne
  omega

end Place

end TauCeti
