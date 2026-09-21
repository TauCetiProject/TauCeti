/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.LocalDiscriminant
public import TauCeti.RingTheory.DedekindDomain.LocalizationAtPrime
public import TauCeti.RingTheory.Valuation.Discrete.Order

/-!
# The valuation of the local minimal discriminant

Let `R` be a discrete valuation ring with fraction field `K`, and let `W` be an elliptic
Weierstrass curve over `K`. The local minimal discriminant ideal is a nonzero power of the maximal
ideal of `R`. This file defines its exponent as
`WeierstrassCurve.localMinimalDiscriminantValuation` and identifies it with the additive valuation
of the discriminant of any minimal equation in the variable-change orbit of `W`.

The exponent is the local quantity usually written `v(Delta_min)`. It is the input used when local
minimal discriminants are assembled into the minimal discriminant ideal over a Dedekind domain,
and it is the baseline from which the obstruction exponent of an arbitrary integral equation is
measured.

## Main definitions

* `WeierstrassCurve.localMinimalDiscriminantValuation`: the nonnegative valuation of a local
  minimal discriminant.

## Main results

* `WeierstrassCurve.localMinimalDiscriminantValuation_eq_addVal_of_isMinimal_smul`: any minimal
  equation in the orbit computes the valuation.
* `WeierstrassCurve.valuation_Δ_eq_exp_neg_of_isMinimal_smul`: the multiplicative valuation of the
  discriminant of such an equation is `exp (-v (Δ_min))`.
* `WeierstrassCurve.localMinimalDiscriminant_eq_maximalIdeal_pow`: the local minimal discriminant
  ideal is the corresponding power of the maximal ideal.
* `WeierstrassCurve.localMinimalDiscriminantValuation_smul`: the valuation is invariant under a
  change of variables.
* `WeierstrassCurve.localMinimalDiscriminantValuation_eq_zero_iff`: the valuation vanishes exactly
  at good reduction.
* `WeierstrassCurve.ord_Δ_eq_localMinimalDiscriminantValuation`: a minimal equation computes the
  local minimal discriminant valuation in additive height-one valuation notation.
* `WeierstrassCurve.ord_Δ_eq_localMinimalDiscriminantValuation_iff_isMinimal`: an integral
  equation has the minimal discriminant order exactly when it is minimal.

The mathematics is Silverman, *The Arithmetic of Elliptic Curves*, VII.1.
-/

public section

namespace WeierstrassCurve

open IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- **The integral discriminant of the chosen minimal equation is nonzero.** This is the
element-level form of `localMinimalDiscriminant_ne_bot`, useful for removing the `∞` value from
the additive valuation. -/
private theorem integralModel_minimal_Δ_ne_zero (W : WeierstrassCurve K) [W.IsElliptic] :
    ((W.minimal R).integralModel R).Δ ≠ 0 := by
  obtain ⟨C, hC⟩ := W.exists_smul_eq_minimal R
  simpa [W.localMinimalDiscriminant_eq_span_Δ R C hC] using W.localMinimalDiscriminant_ne_bot R

/-- **The valuation of the local minimal discriminant.** This is the exponent of the maximal
ideal of `R` in `W.localMinimalDiscriminant R`, equivalently the additive valuation of the
discriminant of a minimal integral equation in the variable-change orbit of `W`.

The ellipticity hypothesis ensures that this discriminant is nonzero, so the extended-natural
additive valuation is finite and has an honest natural-number value. -/
noncomputable def localMinimalDiscriminantValuation (W : WeierstrassCurve K) [W.IsElliptic] :
    ℕ :=
  (addVal R ((W.minimal R).integralModel R).Δ).untop
    (addVal_eq_top_iff.not.mpr <| integralModel_minimal_Δ_ne_zero R W)

/-- **The chosen minimal equation computes the local minimal discriminant valuation.** The cast
to `ℕ∞` records explicitly that the additive valuation is finite. -/
theorem localMinimalDiscriminantValuation_eq_addVal (W : WeierstrassCurve K) [W.IsElliptic] :
    (W.localMinimalDiscriminantValuation R : ENat) =
      addVal R ((W.minimal R).integralModel R).Δ := by
  rw [localMinimalDiscriminantValuation]
  exact WithTop.coe_untop _ _

/-- **Any minimal equation in the variable-change orbit computes the local minimal discriminant
valuation.** Thus the number does not depend on Mathlib's chosen minimal equation. -/
theorem localMinimalDiscriminantValuation_eq_addVal_of_isMinimal_smul
    (W : WeierstrassCurve K) [W.IsElliptic]
    {W' : WeierstrassCurve K} [IsMinimal R W']
    (D : VariableChange K) (hD : D • W = W') :
    (W.localMinimalDiscriminantValuation R : ENat) =
      addVal R (W'.integralModel R).Δ := by
  obtain ⟨C, hC⟩ := W.exists_smul_eq_minimal R
  have hminimal : (D * C⁻¹) • W.minimal R = W' := by
    rw [← hC, mul_smul, inv_smul_smul, hD]
  rw [localMinimalDiscriminantValuation_eq_addVal]
  exact (addVal_eq_iff_associated _ _).mpr
    (associated_integralModel_Δ_of_isMinimal_smul R _ hminimal)

/-- **A minimal model has discriminant of valuation `exp (-v (Δ_min))`.** This reads the
local minimal discriminant valuation off the multiplicative valuation that Mathlib's minimality
API is phrased in, and is the form in which the exponent is compared with the `v`-adic
factorisation of a discriminant over a Dedekind domain. -/
theorem valuation_Δ_eq_exp_neg_of_isMinimal_smul (W : WeierstrassCurve K) [W.IsElliptic]
    {W' : WeierstrassCurve K} [IsMinimal R W'] (D : VariableChange K) (hD : D • W = W') :
    valuation K (maximalIdeal R) W'.Δ =
      WithZero.exp (-(W.localMinimalDiscriminantValuation R : ℤ)) := by
  have h : (W.localMinimalDiscriminantValuation R : ℕ∞) = addVal R (W'.integralModel R).Δ :=
    W.localMinimalDiscriminantValuation_eq_addVal_of_isMinimal_smul R D hD
  rw [← integralModel_Δ_eq R W', valuation_of_algebraMap, intValuation_maximalIdeal, ← h,
    ENat.recTopCoe_natCast, WithZero.exp_neg, WithZero.exp_eq_coe_ofAdd]

/-- **The local minimal discriminant is the indicated power of the maximal ideal.** This
characterizes `localMinimalDiscriminantValuation` intrinsically at the ideal level and is the form
used to assemble local factors over a Dedekind domain. -/
theorem localMinimalDiscriminant_eq_maximalIdeal_pow (W : WeierstrassCurve K) [W.IsElliptic] :
    W.localMinimalDiscriminant R =
      IsLocalRing.maximalIdeal R ^ W.localMinimalDiscriminantValuation R := by
  obtain ⟨C, hC⟩ := W.exists_smul_eq_minimal R
  have h : idealOrderIsoENat R (W.localMinimalDiscriminant R) =
      .toDual (W.localMinimalDiscriminantValuation R : ENat) := by
    rw [idealOrderIsoENat_apply, localMinimalDiscriminantValuation_eq_addVal,
      W.localMinimalDiscriminant_eq_span_Δ R C hC, OrderDual.toDual_inj, addVal_eq_iff_associated]
    exact Submodule.IsPrincipal.associated_generator_span_self _
  rw [← (idealOrderIsoENat R).symm_apply_apply (W.localMinimalDiscriminant R), h]
  exact idealOrderIsoENat_symm_apply_coe R _

/-- **The local minimal discriminant valuation is invariant under a change of variables.** -/
@[simp]
theorem localMinimalDiscriminantValuation_smul (D : VariableChange K)
    (W : WeierstrassCurve K) [W.IsElliptic] :
    (D • W).localMinimalDiscriminantValuation R = W.localMinimalDiscriminantValuation R := by
  have h := congrArg Order.coheight (W.localMinimalDiscriminant_smul R D)
  rw [localMinimalDiscriminant_eq_maximalIdeal_pow R,
    localMinimalDiscriminant_eq_maximalIdeal_pow R,
    coheight_pow_maximalIdeal, coheight_pow_maximalIdeal] at h
  exact ENat.natCast_inj.mp h

/-- **The local minimal discriminant valuation vanishes exactly at good reduction.** -/
@[simp]
theorem localMinimalDiscriminantValuation_eq_zero_iff (W : WeierstrassCurve K) [W.IsElliptic] :
    W.localMinimalDiscriminantValuation R = 0 ↔
      (W.minimal R).HasGoodReduction R := by
  rw [← W.localMinimalDiscriminant_eq_top_iff R,
    localMinimalDiscriminant_eq_maximalIdeal_pow R]
  constructor
  · intro h
    rw [h]
    simp
  · intro h
    have := congrArg Order.coheight h
    simpa [coheight_pow_maximalIdeal] using this

/-- **The local minimal discriminant valuation is positive exactly at bad reduction.** -/
@[simp]
theorem localMinimalDiscriminantValuation_pos_iff (W : WeierstrassCurve K) [W.IsElliptic] :
    0 < W.localMinimalDiscriminantValuation R ↔
      ¬(W.minimal R).HasGoodReduction R := by
  rw [Nat.pos_iff_ne_zero, ne_eq, localMinimalDiscriminantValuation_eq_zero_iff]

section Ord

open scoped WithZero

variable {K : Type*} [Field K]

/-- **A change of variables subtracts twelve times the order of its scaling parameter from the
order of the discriminant.** This is a statement about an arbitrary `ℤᵐ⁰`-valued valuation of
`K`; the discrete valuation of a local minimal model plays no role. -/
theorem ord_Δ_smul (w : Valuation K ℤᵐ⁰) (C : VariableChange K)
    (W : WeierstrassCurve K) [W.IsElliptic] :
    w.ord (C • W).Δ = w.ord W.Δ - 12 * w.ord (C.u : K) := by
  rw [variableChange_Δ,
    Valuation.ord_mul _ (pow_ne_zero _ C.u⁻¹.ne_zero) W.isUnit_Δ.ne_zero,
    Valuation.ord_pow, Units.val_inv_eq_inv_val, Valuation.ord_inv]
  ring

end Ord

section HeightOneSpectrum

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable (O : Type*) [CommRing O] [IsDedekindDomain O]
  {K : Type*} [Field K] [Algebra O K] [IsFractionRing O K]

/-- **A minimal equation computes the local minimal discriminant valuation in additive
notation.** -/
theorem ord_Δ_eq_localMinimalDiscriminantValuation (v : HeightOneSpectrum O)
    (W : WeierstrassCurve K) [W.IsElliptic] {W' : WeierstrassCurve K}
    [IsMinimal (Localization.AtPrime v.asIdeal) W'] (D : VariableChange K) (hD : D • W = W') :
    (v.valuation K).ord W'.Δ =
      W.localMinimalDiscriminantValuation (Localization.AtPrime v.asIdeal) := by
  have hΔ : W'.Δ ≠ 0 := by
    rw [← hD, variableChange_Δ]
    exact mul_ne_zero (pow_ne_zero _ D.u⁻¹.ne_zero) W.isUnit_Δ.ne_zero
  apply (Valuation.ord_eq_iff_valuation_eq_exp_neg _ hΔ).2
  rw [← v.valuation_maximalIdeal_localizationAtPrime W'.Δ]
  exact W.valuation_Δ_eq_exp_neg_of_isMinimal_smul _ D hD

/-- **The local minimal discriminant valuation bounds the order of the discriminant of every
integral equation.** -/
theorem localMinimalDiscriminantValuation_le_ord_Δ (v : HeightOneSpectrum O)
    (W : WeierstrassCurve K) [W.IsElliptic]
    [IsIntegral (Localization.AtPrime v.asIdeal) W] :
    W.localMinimalDiscriminantValuation (Localization.AtPrime v.asIdeal) ≤
      (v.valuation K).ord W.Δ := by
  obtain ⟨C, hC⟩ := W.exists_smul_eq_minimal (Localization.AtPrime v.asIdeal)
  have hCinv : C⁻¹ • W.minimal (Localization.AtPrime v.asIdeal) = W := by
    rw [← hC, inv_smul_smul]
  have hle := valuation_Δ_le_of_isMinimal_smul
    (Localization.AtPrime v.asIdeal) C⁻¹ hCinv
  have hmin := W.valuation_Δ_eq_exp_neg_of_isMinimal_smul
    (Localization.AtPrime v.asIdeal) C hC
  simp only [v.valuation_maximalIdeal_localizationAtPrime] at hle hmin
  rw [Valuation.valuation_eq_exp_neg_ord _ W.isUnit_Δ.ne_zero, hmin,
    WithZero.exp_le_exp] at hle
  omega

/-- **An integral equation attains the local minimal discriminant valuation exactly when it is
minimal.** -/
theorem ord_Δ_eq_localMinimalDiscriminantValuation_iff_isMinimal (v : HeightOneSpectrum O)
    (W : WeierstrassCurve K) [W.IsElliptic]
    [IsIntegral (Localization.AtPrime v.asIdeal) W] :
    (v.valuation K).ord W.Δ =
        W.localMinimalDiscriminantValuation (Localization.AtPrime v.asIdeal) ↔
      IsMinimal (Localization.AtPrime v.asIdeal) W := by
  constructor
  · intro h
    obtain ⟨C, hC⟩ := W.exists_smul_eq_minimal (Localization.AtPrime v.asIdeal)
    have hCinv : C⁻¹ • W.minimal (Localization.AtPrime v.asIdeal) = W := by
      rw [← hC, inv_smul_smul]
    apply isMinimal_of_valuation_Δ_eq_of_isMinimal_smul
      (Localization.AtPrime v.asIdeal) C⁻¹ hCinv
    have hmin := W.valuation_Δ_eq_exp_neg_of_isMinimal_smul
      (Localization.AtPrime v.asIdeal) C hC
    simp only [v.valuation_maximalIdeal_localizationAtPrime] at hmin
    simp only [v.valuation_maximalIdeal_localizationAtPrime]
    rw [Valuation.valuation_eq_exp_neg_ord _ W.isUnit_Δ.ne_zero, hmin, WithZero.exp_inj]
    exact congrArg Neg.neg h
  · intro hmin
    have := hmin -- expose minimality to instance synthesis for the ord-level comparison
    exact ord_Δ_eq_localMinimalDiscriminantValuation O v W (1 : VariableChange K) (one_smul _ W)

end HeightOneSpectrum

end WeierstrassCurve

end
