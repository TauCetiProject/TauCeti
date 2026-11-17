/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.CoefficientSemifield.Basic
public import TauCeti.Algebra.Cluster.CoefficientSystem.Basic
public import TauCeti.Algebra.Cluster.ExchangePolynomial.Polynomial
import TauCeti.Algebra.Cluster.CoefficientSemifield.WithZero

/-!
# The normalized coefficient system

Let `S` be a semifield in which a sum vanishes only when every summand does, such as
`WithZero P` for a coefficient semifield `P`, and let `φ : S →*₀ C` realize its elements as
scalars in a commutative semiring `C`. The normalized coefficient system
`CoefficientSystem.normalized φ` has coefficients in `S` and normalizer
`ν H = (h₀ + ⋯ + h_r)⁻¹`, the inverse of the value of `H` at one; this sum is nonzero because the
constant coefficient is. An exchange polynomial is normalized exactly when its coefficients sum
to one (Fomin and Zelevinsky, Definition 5.3, in degree one; Nakanishi, (2.14)).

This normalizer is homogeneous for all units of `S`, so the normalized multiple of `H` depends
only on `H` up to a unit. In degree one the normalized polynomials are exactly the binomials
`(y + 1)⁻¹ (1 + y T)` for units `y`, and `y` is recovered as the ratio of the two coefficients
(`CoefficientSystem.normalizedBinomialEquiv`). Reversal replaces `y` by `y⁻¹`, and the dilation
factor of the normalized binomial at the divided matrix entry `b` is `y ^ [b]₊ (y + 1) ^ (-b)`.
These are the coefficient formulas of Fomin–Zelevinsky `Y`-seed mutation, written in the
coefficient semifield `Sˣ`. Since `φ` need neither preserve addition nor be injective, the
coefficients cannot be recovered from their scalar realizations, which is why they live in `S`
rather than in `C`.

Semiring maps between such semifields compatible with the scalar maps are maps of normalized
coefficient systems (`CoefficientSystem.Hom.ofRingHom`); for coefficient semifields these come
from `CoefficientSemifieldHom.withZeroMap`.

## References

* S. Fomin and A. Zelevinsky, *Cluster algebras I: Foundations*, J. Amer. Math. Soc. 15 (2002),
  §5.
* T. Nakanishi, *Structure of seeds in generalized cluster algebras*, Pacific J. Math. 277
  (2015), §2.
-/

public section

namespace TauCeti

namespace CoefficientSystem

open ExchangePolynomial Polynomial

variable {S S' C : Type*} [Semifield S] [Subsingleton (AddUnits S)] [Semifield S']
  [Subsingleton (AddUnits S')] [CommSemiring C]

/-- The normalized coefficient system of a semifield `S` in which sums vanish only when every
summand does: the normalizer of `H` is the inverse of the sum `H(1)` of its coefficients. -/
noncomputable def normalized (φ : S →*₀ C) : CoefficientSystem S C where
  toScalar := φ
  normalizer H := (Units.mk0 (H.toPolynomial.eval 1) (H.eval_toPolynomial_ne_zero 1))⁻¹
  normalizer_reverse H := by
    ext
    simp
  normalizer_scale_normalizer_mul H H' := by
    have hH' := H'.eval_toPolynomial_ne_zero 1
    ext
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, toPolynomial_scale, eval_mul,
      eval_C, mul_inv, inv_inv]
    rw [mul_right_comm, mul_inv_cancel₀ hH', one_mul]

variable (φ : S →*₀ C)

@[simp] theorem toScalar_normalized : (normalized φ).toScalar = φ := (rfl)

/-- The normalizer of the normalized system is the inverse of the coefficient sum `H(1)`. -/
@[simp] theorem val_normalizer_normalized (H : ExchangePolynomial S) :
    ((normalized φ).normalizer H : S) = (H.toPolynomial.eval 1)⁻¹ :=
  (rfl)

/-- An exchange polynomial is normalized in the normalized system exactly when its coefficients
sum to one. -/
theorem isNormalized_normalized_iff (H : ExchangePolynomial S) :
    (normalized φ).IsNormalized H ↔ H.toPolynomial.eval 1 = 1 := by
  rw [isNormalized_iff, ← Units.val_eq_one, val_normalizer_normalized, inv_eq_one]

/-- The normalizer of the normalized system is homogeneous of degree `-1` for every unit. -/
theorem normalizer_normalized_scale (H : ExchangePolynomial S) (e : Sˣ) :
    (normalized φ).normalizer (H.scale e) = e⁻¹ * (normalized φ).normalizer H := by
  ext
  simp [mul_comm]

/-- Every unit is a normalizer value of the normalized system. -/
@[simp] theorem normalizerSubgroup_normalized : (normalized φ).normalizerSubgroup = ⊤ := by
  refine eq_top_iff.mpr fun e _ ↦
    (mem_normalizerSubgroup _).mpr ⟨((normalized φ).normalize binary).scale e⁻¹, ?_⟩
  rw [normalizer_normalized_scale, normalizer_normalize, inv_inv, mul_one]

/-- In the normalized system, the normalized multiple of `H` depends on `H` only up to a unit. -/
@[simp] theorem normalize_normalized_scale (H : ExchangePolynomial S) (e : Sˣ) :
    (normalized φ).normalize (H.scale e) = (normalized φ).normalize H :=
  normalize_scale _ (by simp) H

/-- The normalizer of the binomial `1 + y T` is `(y + 1)⁻¹`, where the sum is formed in the
coefficient semifield `Sˣ`. -/
@[simp] theorem normalizer_normalized_binomial (y : Sˣ) :
    (normalized φ).normalizer (binomial y) = (y + 1)⁻¹ := by
  ext
  simp [add_comm]

/-- Reversing the normalized binomial with coefficient `y` gives the normalized binomial with
coefficient `y⁻¹`. -/
theorem reverse_normalize_normalized_binomial (y : Sˣ) :
    ((normalized φ).normalize (binomial y)).reverse = (normalized φ).normalize (binomial y⁻¹) := by
  rw [← normalize_reverse, reverse_binomial, normalize_normalized_scale]

/-- Dilating the normalized binomial with coefficient `y` by `κ` and normalizing again gives the
normalized binomial with coefficient `κ y`. -/
theorem normalize_dilate_normalize_normalized_binomial (y κ : Sˣ) :
    (normalized φ).normalize (((normalized φ).normalize (binomial y)).dilate κ) =
      (normalized φ).normalize (binomial (κ * y)) := by
  rw [normalize_def (H := binomial y), dilate_scale, normalize_normalized_scale, dilate_binomial]

/-- The dilation factor of the normalized binomial with coefficient `y` at the divided matrix
entry `b` is `y ^ [b]₊ (y + 1) ^ (-b)`, the factor of Fomin–Zelevinsky `Y`-seed mutation
(`TauCeti.YSeed.mutation`). -/
theorem dilationFactor_normalize_normalized_binomial (y : Sˣ) (b : ℤ) :
    ((normalized φ).normalize (binomial y)).dilationFactor b = y ^ (b⁺ : ℤ) * (y + 1) ^ (-b) := by
  rw [normalize_def, dilationFactor_scale, normalizer_normalized_binomial, dilationFactor_binomial,
    inv_zpow', mul_comm]

/-- In degree one, the polynomials normalized in the normalized system are exactly the normalized
binomials `(y + 1)⁻¹ (1 + y T)`, with `y` the ratio of the linear and constant coefficients. -/
noncomputable def normalizedBinomialEquiv :
    Sˣ ≃ {H : ExchangePolynomial S // (normalized φ).IsNormalized H ∧ H.degree = 1} where
  toFun y := ⟨(normalized φ).normalize (binomial y), isNormalized_normalize _ _, by simp⟩
  invFun H := H.1.leadingUnit / H.1.constantUnit
  left_inv y := by simp [normalize_def]
  right_inv H := by
    obtain ⟨H, hN, hd⟩ := H
    refine Subtype.ext ?_
    dsimp only
    rw [← normalize_normalized_scale φ _ H.constantUnit, ← eq_scale_binomial_of_degree_eq_one hd,
      hN.normalize_eq]

@[simp] theorem coe_normalizedBinomialEquiv_apply (y : Sˣ) :
    (normalizedBinomialEquiv φ y : ExchangePolynomial S) =
      (normalized φ).normalize (binomial y) :=
  (rfl)

@[simp] theorem normalizedBinomialEquiv_symm_apply
    (H : {H : ExchangePolynomial S // (normalized φ).IsNormalized H ∧ H.degree = 1}) :
    (normalizedBinomialEquiv φ).symm H = H.1.leadingUnit / H.1.constantUnit :=
  (rfl)

/-- Normalized systems are built in particular from a group map `P →* Cˣ` out of a coefficient
semifield `P`, extended by zero to the semifield `WithZero P`. -/
noncomputable example {P : Type*} [CoefficientSemifield P] (ψ : P →* Cˣ) :
    CoefficientSystem (WithZero P) C :=
  normalized (WithZero.lift' ((Units.coeHom C).comp ψ))

namespace Hom

variable {φ} {φ' : S' →*₀ C}

/-- A semiring map between semifields in which sums vanish only when every summand does, and
compatible with the scalar maps, is a map of normalized coefficient systems. -/
noncomputable def ofRingHom (g : S →+* S') (h : φ'.comp g.toMonoidWithZeroHom = φ) :
    Hom (normalized φ) (normalized φ') where
  toMonoidWithZeroHom := g.toMonoidWithZeroHom
  toScalar_comp := h
  normalizer_map H := by
    ext
    simp [toPolynomial_map, Polynomial.eval_one_map]

@[simp] theorem ofRingHom_apply (g : S →+* S') (h : φ'.comp g.toMonoidWithZeroHom = φ) (a : S) :
    ofRingHom g h a = g a :=
  (rfl)

end Hom

end CoefficientSystem

end TauCeti
