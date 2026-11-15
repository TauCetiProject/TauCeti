/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.Curve.Basic
import TauCeti.RingTheory.PowerSeries.Expand

/-!
# Arithmetic of curves

For the additive formal group, forgetting a curve preserves addition of power series.
For any commutative formal group, multiplication by an invertible natural number is an
additive automorphism of curves. Its inverse supplies division by that number even when the
formal group law does not give a scalar action of the coefficient ring. These arithmetic maps
support normalized Cartier operators on curves. Verschiebung `Vₙ` (the substitution of `X^n`
for the curve parameter `X`) is injective for every nonzero index `n`, without commutativity of
the formal group law or a unit assumption on the index.
-/

public section

namespace FormalGroup

variable {R S : Type*} [CommRing R] [CommRing S]

namespace Curve

/-- Forgetting a curve on the additive formal group preserves addition of power series. -/
noncomputable def additiveToPowerSeriesHom : (𝔾ₐ (R := R)).Curve →+ PowerSeries R where
  toFun := toPowerSeries
  map_zero' := toPowerSeries_zero
  map_add' := toPowerSeries_add_𝔾ₐ

@[simp]
theorem additiveToPowerSeriesHom_apply (γ : (𝔾ₐ (R := R)).Curve) :
    additiveToPowerSeriesHom γ = γ.toPowerSeries := (rfl)

end Curve

/-! ### Division by invertible natural numbers -/

section CurveDivision

variable (F : FormalGroup R) [F.IsComm]

/-- Multiplication by an invertible natural number is an automorphism of the group of curves
on a commutative formal group law. -/
noncomputable def nsmulCurveEquiv (n : ℕ) (hunit : IsUnit (n : R)) : F.Curve ≃+ F.Curve :=
  ((F.nsmulHom n).toIso (by simpa using hunit)).curveEquiv

@[simp]
theorem nsmulCurveEquiv_apply (n : ℕ) (hunit : IsUnit (n : R)) (γ : F.Curve) :
    F.nsmulCurveEquiv n hunit γ = n • γ := by
  simp [nsmulCurveEquiv]

@[simp]
theorem nsmulCurveEquiv_one (hunit : IsUnit ((1 : ℕ) : R)) :
    F.nsmulCurveEquiv 1 hunit = AddEquiv.refl F.Curve := by
  ext γ
  simp

@[simp]
theorem nsmul_nsmulCurveEquiv_symm (n : ℕ) (hunit : IsUnit (n : R)) (γ : F.Curve) :
    n • (F.nsmulCurveEquiv n hunit).symm γ = γ := by
  simpa only [nsmulCurveEquiv_apply] using (F.nsmulCurveEquiv n hunit).apply_symm_apply γ

@[simp]
theorem nsmulCurveEquiv_symm_nsmul (n : ℕ) (hunit : IsUnit (n : R)) (γ : F.Curve) :
    (F.nsmulCurveEquiv n hunit).symm (n • γ) = γ := by
  simpa only [nsmulCurveEquiv_apply] using (F.nsmulCurveEquiv n hunit).symm_apply_apply γ

/-- An additive map between groups of curves on commutative formal group laws commutes with
division by an invertible natural number. The source and target coefficient rings may differ. -/
theorem map_nsmulCurveEquiv_symm {G : FormalGroup S} [G.IsComm]
    (f : F.Curve →+ G.Curve) (n : ℕ) (hR : IsUnit (n : R)) (hS : IsUnit (n : S))
    (γ : F.Curve) :
    f ((F.nsmulCurveEquiv n hR).symm γ) =
      (G.nsmulCurveEquiv n hS).symm (f γ) := by
  apply (G.nsmulCurveEquiv n hS).injective
  rw [nsmulCurveEquiv_apply, nsmulCurveEquiv_apply, ← map_nsmul,
    nsmul_nsmulCurveEquiv_symm, nsmul_nsmulCurveEquiv_symm]

end CurveDivision

/-- Verschiebung of any nonzero index is injective on curves. -/
theorem verschiebungCurve_injective (F : FormalGroup R) (n : ℕ) (hn : n ≠ 0) :
    Function.Injective (F.verschiebungCurve n hn) := by
  intro γ δ h
  apply Curve.ext
  apply PowerSeries.expand_injective n hn
  simpa only [toPowerSeries_verschiebungCurve] using congrArg Curve.toPowerSeries h

end FormalGroup
