/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.LocalDiscriminant

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
* `WeierstrassCurve.localMinimalDiscriminant_eq_maximalIdeal_pow`: the local minimal discriminant
  ideal is the corresponding power of the maximal ideal.
* `WeierstrassCurve.localMinimalDiscriminantValuation_smul`: the valuation is invariant under a
  change of variables.
* `WeierstrassCurve.localMinimalDiscriminantValuation_eq_zero_iff`: the valuation vanishes exactly
  at good reduction.

The mathematics is Silverman, *The Arithmetic of Elliptic Curves*, VII.1.
-/

public section

namespace WeierstrassCurve

open IsDiscreteValuationRing

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- **The valuation of the local minimal discriminant.** This is the exponent of the maximal
ideal of `R` in `W.localMinimalDiscriminant R`, equivalently the additive valuation of the
discriminant of a minimal integral equation in the variable-change orbit of `W`.

For an elliptic curve, the discriminant is nonzero, so the theorems below show that the
extended-natural additive valuation is finite and this natural-number value recovers it. -/
noncomputable def localMinimalDiscriminantValuation (W : WeierstrassCurve K) : ℕ :=
  ENat.toNat (addVal R ((W.minimal R).integralModel R).Δ)

/-- **The integral discriminant of the chosen minimal equation is nonzero.** This is the
element-level form of `localMinimalDiscriminant_ne_bot`, useful for removing the `∞` value from
the additive valuation. -/
private theorem integralModel_minimal_Δ_ne_zero (W : WeierstrassCurve K) [W.IsElliptic] :
    ((W.minimal R).integralModel R).Δ ≠ 0 := by
  intro hΔ
  apply W.localMinimalDiscriminant_ne_bot R
  obtain ⟨C, hC⟩ := W.exists_smul_eq_minimal R
  rw [W.localMinimalDiscriminant_eq_span_Δ R C hC, hΔ]
  simp

/-- **The chosen minimal equation computes the local minimal discriminant valuation.** The cast
to `ℕ∞` records explicitly that the additive valuation is finite. -/
theorem localMinimalDiscriminantValuation_eq_addVal (W : WeierstrassCurve K) [W.IsElliptic] :
    (W.localMinimalDiscriminantValuation R : ENat) =
      addVal R ((W.minimal R).integralModel R).Δ := by
  rw [localMinimalDiscriminantValuation]
  exact ENat.natCast_toNat <| (addVal_eq_top_iff.not.mpr <| integralModel_minimal_Δ_ne_zero R W)

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

/-- **The local minimal discriminant is the indicated power of the maximal ideal.** This
characterizes `localMinimalDiscriminantValuation` intrinsically at the ideal level and is the form
used to assemble local factors over a Dedekind domain. -/
theorem localMinimalDiscriminant_eq_maximalIdeal_pow (W : WeierstrassCurve K) [W.IsElliptic] :
    W.localMinimalDiscriminant R =
      IsLocalRing.maximalIdeal R ^ W.localMinimalDiscriminantValuation R := by
  let δ : R := ((W.minimal R).integralModel R).Δ
  have hδ : δ ≠ 0 := integralModel_minimal_Δ_ne_zero R W
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
  obtain ⟨n, u, hu⟩ := eq_unit_mul_pow_irreducible hδ hϖ
  have hv : W.localMinimalDiscriminantValuation R = n := by
    simp [localMinimalDiscriminantValuation, δ, hu, addVal_def' u hϖ]
  obtain ⟨C, hC⟩ := W.exists_smul_eq_minimal R
  rw [W.localMinimalDiscriminant_eq_span_Δ R C hC,
    show ((W.minimal R).integralModel R).Δ = δ from rfl, hu,
    Ideal.span_singleton_mul_left_unit u.isUnit, hv, hϖ.maximalIdeal_eq,
    Ideal.span_singleton_pow]

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
theorem localMinimalDiscriminantValuation_pos_iff (W : WeierstrassCurve K) [W.IsElliptic] :
    0 < W.localMinimalDiscriminantValuation R ↔
      ¬(W.minimal R).HasGoodReduction R := by
  rw [Nat.pos_iff_ne_zero, ne_eq, localMinimalDiscriminantValuation_eq_zero_iff]

end WeierstrassCurve

end
