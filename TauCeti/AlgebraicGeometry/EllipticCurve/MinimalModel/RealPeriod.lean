/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.Reduced
public import TauCeti.AlgebraicGeometry.EllipticCurve.RealPeriod
import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.GlobalExistence
import TauCeti.AlgebraicGeometry.EllipticCurve.VariableChange.Basic

/-!
# The real period of an elliptic curve over `ℚ`

The real period `Ω(W) = 2 ∫_{Ψ₂Sq(x) > 0} dx / √Ψ₂Sq(x)` of a Weierstrass curve `W` over `ℝ`
(`WeierstrassCurve.realPeriod`) is a property of the equation, not of the curve: a change of
variables with scaling factor `u` multiplies it by `|u|`
(`WeierstrassCurve.realPeriod_variableChange`). For an elliptic curve `E` over `ℚ`, the period that
enters the Birch–Swinnerton-Dyer quotient is the real period of a **global minimal equation** of
`E`. It is well defined: between two globally minimal equations every change of variables is
defined over `ℤ` (`WeierstrassCurve.IsGlobalMinimal.exists_baseChange_eq_of_smul_eq`), so `u = ±1`,
and the absolute value in `|ω|` erases the sign.

Here `WeierstrassCurve.minimalRealPeriod E` is the real period of the base change to `ℝ` of the
reduced minimal model `WeierstrassCurve.reducedMinimalModel E`, and the results below show that it
is the real period of *every* global minimal equation of `E`, so the choice of the reduced one is
only a normalisation. Among equations with integer coefficients the global minimal ones are
exactly those of largest real period: if `E` is integral and `C • E` is globally minimal, then
`u` is a nonzero integer up to sign, since `Δ(E) = u¹² Δ(C • E)` and the minimal discriminant
divides `Δ(E)`.

## Main definitions

* `WeierstrassCurve.minimalRealPeriod E`: the real period of the reduced minimal model of an
  elliptic curve `E` over `ℚ`.

## Main results

* `WeierstrassCurve.minimalRealPeriod_pos`: the real period of `E` is positive.
* `WeierstrassCurve.VariableChange.minimalRealPeriod_smul`: it depends only on the
  `ℚ`-isomorphism class of `E`.
* `WeierstrassCurve.minimalRealPeriod_eq_abs_mul`: if `C • E` is globally minimal, the real period
  of `E` is `|u| Ω(E_ℝ)`, with `u` the scaling factor of `C` and `Ω(E_ℝ)` the real period of the
  equation `E` over `ℝ`.
* `WeierstrassCurve.IsGlobalMinimal.minimalRealPeriod_eq`: every global minimal equation computes
  the real period of `E`.
* `WeierstrassCurve.realPeriod_baseChange_le_minimalRealPeriod` and
  `WeierstrassCurve.realPeriod_baseChange_eq_minimalRealPeriod_iff`: an integral equation has real
  period at most that of `E`, with equality exactly when it is globally minimal.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.1, VIII.8 and
  Appendix C, §16.
* J. E. Cremona, *Algorithms for Modular Elliptic Curves*, 2nd ed., Cambridge University Press,
  1997: the real period of a curve over `ℚ`, computed from a minimal equation.
-/

public section

namespace WeierstrassCurve

variable (E : WeierstrassCurve ℚ) [E.IsElliptic]

/-- **The real period of an elliptic curve over `ℚ`**: the real period `Ω` of the base change to
`ℝ` of its reduced minimal model. Every global minimal equation of `E` has this real period
(`WeierstrassCurve.IsGlobalMinimal.minimalRealPeriod_eq`), and it depends only on the
`ℚ`-isomorphism class of `E` (`WeierstrassCurve.VariableChange.minimalRealPeriod_smul`). -/
noncomputable def minimalRealPeriod : ℝ :=
  ((reducedMinimalModel E).baseChange ℝ).realPeriod

/-- The real period of `E` is that of the base change to `ℝ` of its reduced minimal model. -/
theorem minimalRealPeriod_def :
    E.minimalRealPeriod = ((reducedMinimalModel E).baseChange ℝ).realPeriod :=
  (rfl)

/-- **The real period of an elliptic curve over `ℚ` is positive.** -/
theorem minimalRealPeriod_pos : 0 < E.minimalRealPeriod :=
  realPeriod_pos _

/-- **The real period of an elliptic curve over `ℚ`, from any global minimal equation**: if a
change of variables `C` carries `E` to a globally minimal equation, the real period of `E` is
`|u| Ω(E_ℝ)`, with `u` the scaling factor of `C` and `Ω(E_ℝ)` the real period of the base change
`E.baseChange ℝ` of the equation `E`. -/
theorem minimalRealPeriod_eq_abs_mul {C : VariableChange ℚ} (hC : IsGlobalMinimal ℤ (C • E)) :
    E.minimalRealPeriod = |((C.u : ℚ) : ℝ)| * (E.baseChange ℝ).realPeriod := by
  obtain ⟨D, hD⟩ := exists_smul_eq_reducedMinimalModel E
  -- The change of variables `D * C⁻¹` carries the globally minimal equation `C • E` to the reduced
  -- minimal model, so its scaling factor `D.u / C.u` is `±1`.
  have := hC.isIntegral
  have h := (abs_u_eq_one_iff_isGlobalMinimal (C • E) (D := D * C⁻¹)
    (by simpa [mul_smul, hD] using (isReducedMinimal_reducedMinimalModel E).isGlobalMinimal)).mpr hC
  have hu : |(D.u : ℚ)| = |(C.u : ℚ)| := by
    simpa [abs_mul, abs_inv, mul_inv_eq_one₀, C.u.ne_zero] using h
  rw [minimalRealPeriod, ← hD, realPeriod_baseChange_variableChange, eq_ratCast, ← Rat.cast_abs,
    hu, Rat.cast_abs]

/-- **Every global minimal equation computes the real period** of an elliptic curve over `ℚ`. -/
theorem IsGlobalMinimal.minimalRealPeriod_eq {E : WeierstrassCurve ℚ} [E.IsElliptic]
    (h : IsGlobalMinimal ℤ E) : E.minimalRealPeriod = (E.baseChange ℝ).realPeriod := by
  have h1 : IsGlobalMinimal ℤ ((1 : VariableChange ℚ) • E) := by
    simpa only [one_smul] using h
  rw [E.minimalRealPeriod_eq_abs_mul h1, VariableChange.one_def]
  simp

/-- **An integral equation has real period at most that of the curve**: the real period of an
equation of `E` with integer coefficients is at most the real period of `E`, which is that of a
global minimal equation. -/
theorem realPeriod_baseChange_le_minimalRealPeriod [IsIntegral ℤ E] :
    (E.baseChange ℝ).realPeriod ≤ E.minimalRealPeriod := by
  obtain ⟨D, hD⟩ := exists_isGlobalMinimal_smul ℤ E
  rw [minimalRealPeriod_eq_abs_mul E hD]
  exact le_mul_of_one_le_left (realPeriod_pos _).le
    (by exact_mod_cast one_le_abs_u_of_isGlobalMinimal_smul E hD)

/-- **Among integral equations, the global minimal ones are those of largest real period**: an
equation of `E` with integer coefficients has the real period of `E` exactly when it is globally
minimal. -/
theorem realPeriod_baseChange_eq_minimalRealPeriod_iff [IsIntegral ℤ E] :
    (E.baseChange ℝ).realPeriod = E.minimalRealPeriod ↔ IsGlobalMinimal ℤ E := by
  obtain ⟨D, hD⟩ := exists_isGlobalMinimal_smul ℤ E
  -- Since `Ω_min = |u| Ω(E_ℝ)`, equality says `|u| = 1` for the scaling factor `u` of `D`.
  rw [← abs_u_eq_one_iff_isGlobalMinimal E hD, minimalRealPeriod_eq_abs_mul E hD, eq_comm,
    mul_eq_right₀ (realPeriod_pos _).ne']
  norm_cast

namespace VariableChange

/-- **The real period of an elliptic curve over `ℚ` is an isomorphism invariant**: it is unchanged
by a change of variables. -/
@[simp]
theorem minimalRealPeriod_smul (C : VariableChange ℚ) (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    (C • E).minimalRealPeriod = E.minimalRealPeriod := by
  rw [minimalRealPeriod, minimalRealPeriod, reducedMinimalModel_smul]

end VariableChange

end WeierstrassCurve

end
