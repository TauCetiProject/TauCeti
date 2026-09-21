/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.DiscriminantIdeal
public import TauCeti.RingTheory.Valuation.Discrete.Order
import TauCeti.AlgebraicGeometry.EllipticCurve.IntegralModel

/-!
# Local obstruction exponents of Weierstrass equations

Let `O` be a Dedekind domain with fraction field `K`, let `v` be a height-one prime of `O`, and
let `W` be an elliptic Weierstrass equation over `K`. The **local obstruction exponent** is

`f_v(W) = (v(Delta W) - v(Delta_min,v)) / 12`.

The numerator is divisible by twelve because an admissible change of variables scales the
discriminant by the inverse twelfth power of its `u`-parameter. It is useful to define the
exponent for every rational equation, with values in `ℤ`: local integrality is a sufficient
hypothesis for nonnegativity, while a nonintegral equation may have negative defect.

These exponents are the local data assembled by the defect ideal of an integral equation. The
reconstruction formula in this file is the interface that construction needs; it avoids relying
on integer division or unfolding the definition.

## Main definitions

* `WeierstrassCurve.obstructionExponentAt`: the local discriminant defect divided by twelve.
* `WeierstrassCurve.IsSharpSemiGlobalMinimalAt`: an integral equation minimal away from one
  prime and having obstruction exponent exactly one there.

## Main results

* `WeierstrassCurve.twelve_dvd_ord_Δ_sub_localMinimalDiscriminantValuation`: the discriminant
  defect of every rational equation is divisible by twelve.
* `WeierstrassCurve.twelve_mul_obstructionExponentAt`: the exact reconstruction formula.
* `WeierstrassCurve.obstructionExponentAt_smul`: the change-of-variables formula.
* `WeierstrassCurve.obstructionExponentAt_nonneg_of_isIntegral`: local integrality makes the
  obstruction exponent nonnegative.
* `WeierstrassCurve.obstructionExponentAt_eq_zero_iff_isMinimal`: for a locally integral
  equation, vanishing of the obstruction exponent is equivalent to local minimality.
* `WeierstrassCurve.isGlobalMinimal_iff_obstructionExponentAt_eq_zero`: an integral equation is
  globally minimal exactly when all its local obstruction exponents vanish.
* `WeierstrassCurve.IsSharpSemiGlobalMinimalAt.isSemiGlobalMinimal`: sharp semi-global minimality
  implies the weak semi-global predicate.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VIII.8.
-/

public section

namespace WeierstrassCurve

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable (O : Type*) [CommRing O] [IsDedekindDomain O]
  {K : Type*} [Field K] [Algebra O K] [IsFractionRing O K]

/-- **A change of variables subtracts twelve times the order of its scaling parameter from the
order of the discriminant.** -/
theorem ord_Δ_smul (v : HeightOneSpectrum O) (C : VariableChange K)
    (W : WeierstrassCurve K) [W.IsElliptic] :
    (v.valuation K).ord (C • W).Δ =
      (v.valuation K).ord W.Δ - 12 * (v.valuation K).ord (C.u : K) := by
  rw [variableChange_Δ,
    Valuation.ord_mul _ (pow_ne_zero _ C.u⁻¹.ne_zero) W.isUnit_Δ.ne_zero,
    Valuation.ord_pow, Units.val_inv_eq_inv_val, Valuation.ord_inv]
  ring

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
  exact valuation_Δ_eq_exp_neg_localMinimalDiscriminantValuation O W v D hD

/-- **The difference between the discriminant valuation of an equation and the local minimal
valuation is divisible by twelve.** An admissible change of variables scales the discriminant by
the inverse twelfth power of its `u`-parameter. -/
theorem twelve_dvd_ord_Δ_sub_localMinimalDiscriminantValuation
    (v : HeightOneSpectrum O)
    (W : WeierstrassCurve K) [W.IsElliptic] :
    (12 : ℤ) ∣ (v.valuation K).ord W.Δ -
      W.localMinimalDiscriminantValuation (Localization.AtPrime v.asIdeal) := by
  obtain ⟨C, hC⟩ := W.exists_smul_eq_minimal (Localization.AtPrime v.asIdeal)
  have hmin := ord_Δ_eq_localMinimalDiscriminantValuation O v W C hC
  have hord := ord_Δ_smul O v C W
  rw [hC] at hord
  refine ⟨(v.valuation K).ord (C.u : K), ?_⟩
  omega

/-- **The local obstruction exponent**
`f_v(W) = (v(Delta W) - v(Delta_min,v)) / 12`.

It is integer-valued for every rational equation. Local integrality is not part of the definition:
it is the hypothesis that makes the exponent nonnegative, as proved by
`obstructionExponentAt_nonneg_of_isIntegral`. -/
noncomputable def obstructionExponentAt (v : HeightOneSpectrum O)
    (W : WeierstrassCurve K) [W.IsElliptic] : ℤ :=
  ((v.valuation K).ord W.Δ -
    W.localMinimalDiscriminantValuation (Localization.AtPrime v.asIdeal)) / 12

/-- The defining quotient for the local obstruction exponent. The reconstruction theorem below
is usually a more convenient interface because the numerator is known to be divisible by twelve. -/
theorem obstructionExponentAt_def (v : HeightOneSpectrum O)
    (W : WeierstrassCurve K) [W.IsElliptic] :
    obstructionExponentAt O v W = ((v.valuation K).ord W.Δ -
      W.localMinimalDiscriminantValuation (Localization.AtPrime v.asIdeal)) / 12 :=
  (rfl)

/-- **Twelve times the local obstruction exponent is the discriminant defect.** This is the
characteristic elimination lemma for `obstructionExponentAt`; consumers need not reason about
integer division. -/
@[simp]
theorem twelve_mul_obstructionExponentAt (v : HeightOneSpectrum O)
    (W : WeierstrassCurve K) [W.IsElliptic] :
    12 * obstructionExponentAt O v W = (v.valuation K).ord W.Δ -
      W.localMinimalDiscriminantValuation (Localization.AtPrime v.asIdeal) := by
  rw [obstructionExponentAt_def, mul_comm]
  exact Int.ediv_mul_cancel
    (twelve_dvd_ord_Δ_sub_localMinimalDiscriminantValuation O v W)

/-- **Changing variables subtracts the order of the scaling parameter from the local obstruction
exponent.** -/
@[simp]
theorem obstructionExponentAt_smul (v : HeightOneSpectrum O) (C : VariableChange K)
    (W : WeierstrassCurve K) [W.IsElliptic] :
    obstructionExponentAt O v (C • W) =
      obstructionExponentAt O v W - (v.valuation K).ord (C.u : K) := by
  have hC := twelve_mul_obstructionExponentAt O v (C • W)
  have hW := twelve_mul_obstructionExponentAt O v W
  rw [ord_Δ_smul, localMinimalDiscriminantValuation_smul] at hC
  omega

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
  simp only [v.valuation_maximalIdeal_localizationAtPrime] at hle
  rw [Valuation.valuation_eq_exp_neg_ord _ W.isUnit_Δ.ne_zero,
    valuation_Δ_eq_exp_neg_localMinimalDiscriminantValuation O W v C hC,
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
    simp only [v.valuation_maximalIdeal_localizationAtPrime]
    rw [Valuation.valuation_eq_exp_neg_ord _ W.isUnit_Δ.ne_zero,
      valuation_Δ_eq_exp_neg_localMinimalDiscriminantValuation O W v C hC, WithZero.exp_inj]
    exact congrArg Neg.neg h
  · intro hmin
    have := hmin -- expose minimality to instance synthesis for the ord-level comparison
    exact ord_Δ_eq_localMinimalDiscriminantValuation O v W (1 : VariableChange K) (one_smul _ W)

/-- **Local integrality makes the local obstruction exponent nonnegative.** Without integrality
the exponent remains defined but may be negative. -/
theorem obstructionExponentAt_nonneg_of_isIntegral (v : HeightOneSpectrum O)
    (W : WeierstrassCurve K) [W.IsElliptic]
    [IsIntegral (Localization.AtPrime v.asIdeal) W] :
    0 ≤ obstructionExponentAt O v W := by
  have hle := localMinimalDiscriminantValuation_le_ord_Δ O v W
  have hdef := twelve_mul_obstructionExponentAt O v W
  omega

/-- **For a locally integral equation, the obstruction exponent vanishes exactly when the
equation is minimal at that prime.** -/
@[simp]
theorem obstructionExponentAt_eq_zero_iff_isMinimal (v : HeightOneSpectrum O)
    (W : WeierstrassCurve K) [W.IsElliptic]
    [IsIntegral (Localization.AtPrime v.asIdeal) W] :
    obstructionExponentAt O v W = 0 ↔
      IsMinimal (Localization.AtPrime v.asIdeal) W := by
  rw [← ord_Δ_eq_localMinimalDiscriminantValuation_iff_isMinimal O v W]
  have hdef := twelve_mul_obstructionExponentAt O v W
  omega

/-- **An integral equation is globally minimal exactly when all of its local obstruction
exponents vanish.** -/
theorem isGlobalMinimal_iff_obstructionExponentAt_eq_zero
    (W : WeierstrassCurve K) [W.IsElliptic] [IsIntegral O W] :
    IsGlobalMinimal O W ↔ ∀ v : HeightOneSpectrum O, obstructionExponentAt O v W = 0 := by
  rw [isGlobalMinimal_iff]
  refine forall_congr' fun v ↦ ?_
  let hW : IsIntegral (Localization.AtPrime v.asIdeal) W :=
    IsIntegral.of_isScalarTower (R := O) W
  have := hW -- expose local integrality to instance synthesis for the local criterion
  exact (obstructionExponentAt_eq_zero_iff_isMinimal O v W).symm

/-- **A sharply semi-global model at `v₀`** is integral at `v₀`, minimal at every other
height-one prime, and has discriminant defect exactly twelve at `v₀`. Unlike weak semi-global
minimality, which permits any defect at its exceptional prime, this pins the defect to the
smallest positive value, so the model's defect ideal is exactly `𝔭_{v₀}`. -/
def IsSharpSemiGlobalMinimalAt (v₀ : HeightOneSpectrum O)
    (W : WeierstrassCurve K) [W.IsElliptic] : Prop :=
  IsIntegral (Localization.AtPrime v₀.asIdeal) W ∧
    (∀ v : HeightOneSpectrum O, v ≠ v₀ →
      IsMinimal (Localization.AtPrime v.asIdeal) W) ∧
    obstructionExponentAt O v₀ W = 1

/-- Sharp semi-global minimality, unfolded. -/
@[simp]
theorem isSharpSemiGlobalMinimalAt_iff (v₀ : HeightOneSpectrum O)
    (W : WeierstrassCurve K) [W.IsElliptic] :
    IsSharpSemiGlobalMinimalAt O v₀ W ↔
      IsIntegral (Localization.AtPrime v₀.asIdeal) W ∧
        (∀ v : HeightOneSpectrum O, v ≠ v₀ →
          IsMinimal (Localization.AtPrime v.asIdeal) W) ∧
        obstructionExponentAt O v₀ W = 1 :=
  (Iff.rfl)

variable {O} in
/-- A sharply semi-global model is integral at its exceptional prime. -/
theorem IsSharpSemiGlobalMinimalAt.isIntegral {v₀ : HeightOneSpectrum O}
    {W : WeierstrassCurve K} [W.IsElliptic]
    (hW : IsSharpSemiGlobalMinimalAt O v₀ W) :
    IsIntegral (Localization.AtPrime v₀.asIdeal) W :=
  hW.1

variable {O} in
/-- A sharply semi-global model is minimal away from its exceptional prime. -/
theorem IsSharpSemiGlobalMinimalAt.isMinimal {v₀ v : HeightOneSpectrum O}
    {W : WeierstrassCurve K} [W.IsElliptic]
    (hW : IsSharpSemiGlobalMinimalAt O v₀ W) (hv : v ≠ v₀) :
    IsMinimal (Localization.AtPrime v.asIdeal) W :=
  hW.2.1 v hv

variable {O} in
/-- The obstruction exponent of a sharply semi-global model at its exceptional prime is one. -/
theorem IsSharpSemiGlobalMinimalAt.obstructionExponentAt_eq_one {v₀ : HeightOneSpectrum O}
    {W : WeierstrassCurve K} [W.IsElliptic]
    (hW : IsSharpSemiGlobalMinimalAt O v₀ W) :
    obstructionExponentAt O v₀ W = 1 :=
  hW.2.2

variable {O} in
/-- An equation integral at `v₀`, minimal away from `v₀`, and with obstruction exponent one at
`v₀` is sharply semi-global there. -/
theorem IsSharpSemiGlobalMinimalAt.of_isIntegral_of_isMinimal
    {v₀ : HeightOneSpectrum O} {W : WeierstrassCurve K} [W.IsElliptic]
    (h₀ : IsIntegral (Localization.AtPrime v₀.asIdeal) W)
    (hmin : ∀ v : HeightOneSpectrum O, v ≠ v₀ →
      IsMinimal (Localization.AtPrime v.asIdeal) W)
    (hobs : obstructionExponentAt O v₀ W = 1) :
    IsSharpSemiGlobalMinimalAt O v₀ W :=
  ⟨h₀, hmin, hobs⟩

variable {O} in
/-- Every sharply semi-global model is semi-global in the weak, consumer-facing sense. -/
theorem IsSharpSemiGlobalMinimalAt.isSemiGlobalMinimal {v₀ : HeightOneSpectrum O}
    {W : WeierstrassCurve K} [W.IsElliptic]
    (hW : IsSharpSemiGlobalMinimalAt O v₀ W) : IsSemiGlobalMinimal O W :=
  IsSemiGlobalMinimal.of_isIntegral_of_isMinimal
    (IsSharpSemiGlobalMinimalAt.isIntegral hW) fun _ hv =>
      IsSharpSemiGlobalMinimalAt.isMinimal hW hv

end WeierstrassCurve

end
