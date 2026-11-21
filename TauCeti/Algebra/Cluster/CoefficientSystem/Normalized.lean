/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.CoefficientSemifield.WithZero
public import TauCeti.Algebra.Cluster.CoefficientSystem.Basic

/-!
# Normalized binomials

Let `S` be a semifield in which a sum vanishes only when every summand does, such as `WithZero P`
for a coefficient semifield `P`, and let `φ : S →*₀ C` realize its elements as scalars in a
commutative semiring `C`. The normalized coefficient system `CoefficientSystem.ofSemifield φ` has
coefficients in `S` and normalizer `ν H = (h₀ + ⋯ + h_r)⁻¹`; this file studies its normalized
binomials. In degree one the normalized polynomials are exactly the binomials `(y + 1)⁻¹ (1 + y T)`
for units `y`, and `y` is recovered as the ratio of the two coefficients
(`CoefficientSystem.ofSemifieldBinomialEquiv`). Reversal replaces `y` by `y⁻¹`, and the dilation
factor of the normalized binomial at the divided matrix entry `b` is `y ^ [b]₊ (y + 1) ^ (-b)`.
These are the coefficient formulas of Fomin–Zelevinsky `Y`-seed mutation, written in the coefficient
semifield `Sˣ`. Since `φ` need neither preserve addition nor be injective, the coefficients cannot
be recovered from their scalar realizations, which is why they live in `S` rather than in `C`.

For a coefficient semifield `P` and a group map `ψ : P →* Cˣ`, the normalized system of
`WithZero P` whose scalar map extends `ψ` by zero is `CoefficientSystem.ofCoefficientSemifield ψ`.

## References

* S. Fomin and A. Zelevinsky, *Cluster algebras I: Foundations*, J. Amer. Math. Soc. 15 (2002),
  §5.
* T. Nakanishi, *Structure of seeds in generalized cluster algebras*, Pacific J. Math. 277
  (2015), §2.
-/

public section

namespace TauCeti

namespace CoefficientSystem

open ExchangePolynomial

variable {S C : Type*} [Semifield S] [Subsingleton (AddUnits S)] [CommSemiring C]
  (φ : S →*₀ C)

/-- The normalizer of the binomial `1 + y T` is `(y + 1)⁻¹`, where the sum is formed in the
coefficient semifield `Sˣ`. -/
@[simp] theorem ofSemifield_normalizer_binomial (y : Sˣ) :
    (ofSemifield φ).normalizer (binomial y) = (y + 1)⁻¹ := by
  ext
  simp [Finset.sum_range_succ, add_comm]

/-- Reversing the normalized binomial with coefficient `y` gives the normalized binomial with
coefficient `y⁻¹`. -/
@[simp] theorem reverse_normalize_ofSemifield_binomial (y : Sˣ) :
    ((ofSemifield φ).normalize (binomial y)).reverse =
      (ofSemifield φ).normalize (binomial y⁻¹) := by
  rw [← normalize_reverse, reverse_binomial, ofSemifield_normalize_scale]

/-- Dilating the normalized binomial with coefficient `y` by `κ` and normalizing again gives the
normalized binomial with coefficient `κ y`. -/
@[simp] theorem normalize_dilate_normalize_ofSemifield_binomial (y κ : Sˣ) :
    (ofSemifield φ).normalize (((ofSemifield φ).normalize (binomial y)).dilate κ) =
      (ofSemifield φ).normalize (binomial (κ * y)) := by
  rw [normalize_def (H := binomial y), dilate_scale, ofSemifield_normalize_scale, dilate_binomial]

/-- The dilation factor of the normalized binomial with coefficient `y` at the divided matrix
entry `b` is `y ^ [b]₊ (y + 1) ^ (-b)`, the factor of Fomin–Zelevinsky `Y`-seed mutation
(`TauCeti.YSeed.mutation`). -/
@[simp] theorem dilationFactor_normalize_ofSemifield_binomial (y : Sˣ) (b : ℤ) :
    ((ofSemifield φ).normalize (binomial y)).dilationFactor b = y ^ (b⁺ : ℤ) * (y + 1) ^ (-b) := by
  rw [normalize_def, dilationFactor_scale, ofSemifield_normalizer_binomial,
    dilationFactor_binomial, inv_zpow', mul_comm]

/-- In degree one, the polynomials normalized in the normalized system are exactly the normalized
binomials `(y + 1)⁻¹ (1 + y T)`, with `y` the ratio of the linear and constant coefficients. -/
noncomputable def ofSemifieldBinomialEquiv :
    Sˣ ≃ {H : ExchangePolynomial S // (ofSemifield φ).IsNormalized H ∧ H.degree = 1} where
  toFun y := ⟨(ofSemifield φ).normalize (binomial y), isNormalized_normalize _ _, by simp⟩
  invFun H := H.val.leadingUnit / H.val.constantUnit
  left_inv y := by simp [normalize_def]
  right_inv H := by
    obtain ⟨H, hN, hd⟩ := H
    refine Subtype.ext ?_
    dsimp only
    rw [← ofSemifield_normalize_scale φ H.constantUnit, ← eq_scale_binomial_of_degree_eq_one hd,
      hN.normalize_eq]

@[simp] theorem coe_ofSemifieldBinomialEquiv_apply (y : Sˣ) :
    (ofSemifieldBinomialEquiv φ y : ExchangePolynomial S) =
      (ofSemifield φ).normalize (binomial y) :=
  (rfl)

@[simp] theorem ofSemifieldBinomialEquiv_symm_apply
    (H : {H : ExchangePolynomial S // (ofSemifield φ).IsNormalized H ∧ H.degree = 1}) :
    (ofSemifieldBinomialEquiv φ).symm H = H.val.leadingUnit / H.val.constantUnit :=
  (rfl)

section CoefficientSemifield

open CoefficientSemifield

variable {P : Type*} [CoefficientSemifield P] (ψ : P →* Cˣ)

/-- The normalized coefficient system of a coefficient semifield `P` and a group map
`ψ : P →* Cˣ`: its coefficients lie in `WithZero P` and its scalar map extends `ψ` by zero. It is
an abbreviation, so the lemmas about `ofSemifield` apply to it; `unitsWithZeroRingEquiv`
identifies its coefficient units `(WithZero P)ˣ` with `P`. -/
noncomputable abbrev ofCoefficientSemifield : CoefficientSystem (WithZero P) C :=
  ofSemifield (WithZero.lift' ((Units.coeHom C).comp ψ))

/-- The normalizer of the binomial `1 + y T` with coefficient `y ∈ P` is `(y + 1)⁻¹`, where the
sum is formed in the coefficient semifield `P`. -/
theorem normalizer_ofCoefficientSemifield_binomial (y : P) :
    (ofCoefficientSemifield ψ).normalizer (binomial (unitsWithZeroRingEquiv.symm y)) =
      unitsWithZeroRingEquiv.symm (y + 1)⁻¹ := by
  rw [ofSemifield_normalizer_binomial, map_inv, map_add, map_one]

/-- The dilation factor of the normalized binomial with coefficient `y ∈ P` at the divided matrix
entry `b` is `y ^ [b]₊ (y + 1) ^ (-b)`, computed in the coefficient semifield `P`. -/
theorem dilationFactor_normalize_ofCoefficientSemifield_binomial (y : P) (b : ℤ) :
    ((ofCoefficientSemifield ψ).normalize
        (binomial (unitsWithZeroRingEquiv.symm y))).dilationFactor b =
      unitsWithZeroRingEquiv.symm (y ^ (b⁺ : ℤ) * (y + 1) ^ (-b)) := by
  rw [dilationFactor_normalize_ofSemifield_binomial, map_mul, map_zpow, map_zpow, map_add, map_one]

end CoefficientSemifield

end CoefficientSystem

end TauCeti
