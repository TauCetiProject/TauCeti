/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import TauCeti.Algebra.Field.CrossRatio
import TauCeti.Analysis.Calculus.Deriv.CrossRatio
import TauCeti.Analysis.Calculus.Deriv.Second
import TauCeti.Analysis.SpecialFunctions.Pow.Complex

/-!
# Riemann's equation from the hypergeometric equation (DLMF 15.11.7)

Riemann's differential equation (DLMF 15.11.1) with distinct finite singular points `α, β, γ` and
exponent pairs `{a₁, a₂}`, `{b₁, b₂}`, `{c₁, c₂}` subject to Fuchs's relation
`a₁ + a₂ + b₁ + b₂ + c₁ + c₂ = 1` (DLMF 15.11.2) is

`w′′ + (Σ (1 − a₁ − a₂)/(z − α)) w′ + (Σ (α − β)(α − γ) a₁ a₂/(z − α)) w / ((z − α)(z − β)(z − γ))
= 0`,

the sums running cyclically over the three singular points. If `u` solves the hypergeometric
equation (DLMF 15.10.1) with `a = a₁ + b₁ + c₁`, `b = a₁ + b₁ + c₂`, `c = 1 + a₁ − a₂`, then
`w(z) = ((z − α)/(z − γ))^{a₁} ((z − β)/(z − γ))^{b₁} u(ζ)`, with the Möbius variable
`ζ = (z − α)(β − γ)/((z − γ)(β − α))`, solves Riemann's equation (DLMF 15.11.7).

The Möbius variable is the cross-ratio `crossRatio z β α γ`.

## Main results

* `TauCeti.riemannEquation_residual_eq_mul_hypergeometricEquation_residual`: the operator
  identity behind 15.11.7: at each admissible point, the left side of Riemann's equation for `w`
  is an explicit multiple of the left side of the hypergeometric equation for `u` at `ζ`, with
  neither assumed to vanish.
* `TauCeti.analyticOnNhd_and_riemannEquation_of_hypergeometricEquation`: DLMF 15.11.7, from an
  analytic solution of the hypergeometric equation to an analytic solution of Riemann's equation.
* `TauCeti.riemannEquation_of_hypergeometricEquation`: DLMF 15.11.7 for `u` differentiable on an
  open set, with the Möbius variable written out.

## Implementation notes

Write `w = P · (u ∘ T)` with the prefactor `P` and the Möbius variable `T`. The second-order
product and chain rule `AnalyticAt.hasDerivAt_deriv_mul_comp` expresses `w′′` and `w′` through
`P, P′, P′′`, `T′, T′′` and `u, u′, u′′` at `T z`. The prefactor has logarithmic derivative
`L = a₁ (1/(z − α) − 1/(z − γ)) + b₁ (1/(z − β) − 1/(z − γ))`, so `P′ = P L` and
`P′′ = P (L ^ 2 + L′)` (`TauCeti.hasDerivAt_sub_div_sub_cpow`,
`TauCeti.hasDerivAt_deriv_of_eventually_hasDerivAt_mul`), and `T` is the cross-ratio in its
first point (`TauCeti.hasDerivAt_crossRatio_first`, `TauCeti.hasDerivAt_deriv_crossRatio_first`).
After these substitutions Riemann's operator at `z` is a multiple of the hypergeometric operator
at `T z`, which clearing denominators verifies.

## References

* [DLMF] *NIST Digital Library of Mathematical Functions*, §15.11, <https://dlmf.nist.gov/15.11>.

The proof is adapted from the lean-DLMF project (<https://github.com/bjbraams/lean-DLMF>), files
`DLMF/Hypergeometric/Riemann.lean` and `DLMF/Hypergeometric/FurtherTransformations/Quadratic.lean`,
where it is stated for the Gauss series itself.
-/

public section

open Complex Filter
open scoped Topology

namespace TauCeti

/-! ### The prefactor and the Möbius variable of DLMF 15.11.7 -/

/-- The prefactor `P(w) = ((w − α)/(w − γ))^{a₁} ((w − β)/(w − γ))^{b₁}` of DLMF 15.11.7 is
analytic where both quotients lie in the slit plane. -/
private theorem analyticAt_riemannPrefactor {α β γ a₁ b₁ z : ℂ}
    (hA : (z - α) / (z - γ) ∈ slitPlane) (hB : (z - β) / (z - γ) ∈ slitPlane) :
    AnalyticAt ℂ (fun w => ((w - α) / (w - γ)) ^ a₁ * ((w - β) / (w - γ)) ^ b₁) z := by
  have hzγ : z - γ ≠ 0 := (div_ne_zero_iff.mp (slitPlane_ne_zero hA)).2
  exact ((analyticAt_id.sub analyticAt_const).div (analyticAt_id.sub analyticAt_const) hzγ
    |>.cpow analyticAt_const hA).mul
    (((analyticAt_id.sub analyticAt_const).div (analyticAt_id.sub analyticAt_const) hzγ).cpow
      analyticAt_const hB)

/-- The prefactor `P` of DLMF 15.11.7 satisfies `P′ = P L` with its logarithmic derivative
`L(w) = a₁ ((w − α)⁻¹ − (w − γ)⁻¹) + b₁ ((w − β)⁻¹ − (w − γ)⁻¹)`. -/
private theorem hasDerivAt_riemannPrefactor {α β γ a₁ b₁ z : ℂ}
    (hA : (z - α) / (z - γ) ∈ slitPlane) (hB : (z - β) / (z - γ) ∈ slitPlane) :
    HasDerivAt (fun w => ((w - α) / (w - γ)) ^ a₁ * ((w - β) / (w - γ)) ^ b₁)
      (((z - α) / (z - γ)) ^ a₁ * ((z - β) / (z - γ)) ^ b₁ *
        (a₁ * ((z - α)⁻¹ - (z - γ)⁻¹) + b₁ * ((z - β)⁻¹ - (z - γ)⁻¹))) z :=
  ((hasDerivAt_sub_div_sub_cpow hA).mul (hasDerivAt_sub_div_sub_cpow hB)).congr_deriv (by ring)

/-- The derivative `P′` of the prefactor `P` of DLMF 15.11.7 has derivative `P (L ^ 2 + L′)`,
where `L` is the logarithmic derivative of `P`. -/
private theorem hasDerivAt_deriv_riemannPrefactor {α β γ a₁ b₁ z : ℂ}
    (hA : (z - α) / (z - γ) ∈ slitPlane) (hB : (z - β) / (z - γ) ∈ slitPlane) :
    HasDerivAt (deriv fun w => ((w - α) / (w - γ)) ^ a₁ * ((w - β) / (w - γ)) ^ b₁)
      (((z - α) / (z - γ)) ^ a₁ * ((z - β) / (z - γ)) ^ b₁ *
        ((a₁ * ((z - α)⁻¹ - (z - γ)⁻¹) + b₁ * ((z - β)⁻¹ - (z - γ)⁻¹)) ^ 2 +
          (a₁ * (-((z - α) ^ 2)⁻¹ + ((z - γ) ^ 2)⁻¹) +
            b₁ * (-((z - β) ^ 2)⁻¹ + ((z - γ) ^ 2)⁻¹)))) z := by
  obtain ⟨hzα, hzγ⟩ := div_ne_zero_iff.mp (slitPlane_ne_zero hA)
  have hzβ : z - β ≠ 0 := (div_ne_zero_iff.mp (slitPlane_ne_zero hB)).1
  -- Both quotients stay in the open slit plane near `z`, so `P′ = P L` near `z`.
  have hc : ∀ δ : ℂ, ContinuousAt (fun w : ℂ => (w - δ) / (w - γ)) z := fun δ =>
    (continuousAt_id.sub continuousAt_const).div (continuousAt_id.sub continuousAt_const) hzγ
  have hev := ((hc α).eventually_mem (isOpen_slitPlane.mem_nhds hA)).and
    ((hc β).eventually_mem (isOpen_slitPlane.mem_nhds hB))
  refine hasDerivAt_deriv_of_eventually_hasDerivAt_mul
    (ℓ := fun w => a₁ * ((w - α)⁻¹ - (w - γ)⁻¹) + b₁ * ((w - β)⁻¹ - (w - γ)⁻¹))
    (hev.mono fun w hw => hasDerivAt_riemannPrefactor hw.1 hw.2) ?_
  -- The derivative of the logarithmic derivative `L`.
  refine (((((hasDerivAt_id z).sub_const α).inv hzα).sub
    (((hasDerivAt_id z).sub_const γ).inv hzγ)).const_mul a₁ |>.add
    (((((hasDerivAt_id z).sub_const β).inv hzβ).sub
    (((hasDerivAt_id z).sub_const γ).inv hzγ)).const_mul b₁)).congr_deriv ?_
  simp only [id]
  ring

/-- **The operator identity behind DLMF 15.11.7.** Let
`w(x) = ((x − α)/(x − γ))^{a₁} ((x − β)/(x − γ))^{b₁} u(ζ(x))` with the Möbius variable
`ζ(x) = (x − α)(β − γ)/((x − γ)(β − α))`, the cross-ratio `crossRatio x β α γ`. At a point `z`
where both quotients lie in the slit plane and `u` is analytic at `ζ(z)`, and for `α ≠ β` and
exponents under Fuchs's relation (DLMF 15.11.2), the left side of Riemann's equation
(DLMF 15.11.1) for `w` at `z` is the multiplier
`−((z − α)/(z − γ))^{a₁} ((z − β)/(z − γ))^{b₁} (β − γ)(α − γ)/((z − α)(z − β)(z − γ)²)` times
the left side of the hypergeometric equation (DLMF 15.10.1) for `u` at `ζ(z)`, with
`a = a₁ + b₁ + c₁`, `b = a₁ + b₁ + c₂`, `c = 1 + a₁ − a₂`. Neither side is assumed to vanish. -/
theorem riemannEquation_residual_eq_mul_hypergeometricEquation_residual
    {α β γ a₁ a₂ b₁ b₂ c₁ c₂ : ℂ} (hαβ : α ≠ β) (hsum : a₁ + a₂ + b₁ + b₂ + c₁ + c₂ = 1)
    {u : ℂ → ℂ} {z : ℂ} (hA : (z - α) / (z - γ) ∈ slitPlane) (hB : (z - β) / (z - γ) ∈ slitPlane)
    (hu : AnalyticAt ℂ u (crossRatio z β α γ)) :
    let w : ℂ → ℂ := fun x => ((x - α) / (x - γ)) ^ a₁ * ((x - β) / (x - γ)) ^ b₁ *
      u (crossRatio x β α γ)
    deriv (deriv w) z +
      ((1 - a₁ - a₂) / (z - α) + (1 - b₁ - b₂) / (z - β) + (1 - c₁ - c₂) / (z - γ)) * deriv w z +
        ((α - β) * (α - γ) * a₁ * a₂ / (z - α) + (β - α) * (β - γ) * b₁ * b₂ / (z - β) +
          (γ - α) * (γ - β) * c₁ * c₂ / (z - γ)) / ((z - α) * (z - β) * (z - γ)) * w z =
      -(((z - α) / (z - γ)) ^ a₁ * ((z - β) / (z - γ)) ^ b₁) * (β - γ) * (α - γ) /
          ((z - α) * (z - β) * (z - γ) ^ 2) *
        (crossRatio z β α γ * (1 - crossRatio z β α γ) * deriv (deriv u) (crossRatio z β α γ) +
          (1 + a₁ - a₂ - ((a₁ + b₁ + c₁) + (a₁ + b₁ + c₂) + 1) * crossRatio z β α γ) *
            deriv u (crossRatio z β α γ) -
          (a₁ + b₁ + c₁) * (a₁ + b₁ + c₂) * u (crossRatio z β α γ)) := by
  intro w
  -- `w = P · (u ∘ T)`, with the Möbius variable `T` and the prefactor `P`.
  set T : ℂ → ℂ := fun x => crossRatio x β α γ with hTdef
  set P : ℂ → ℂ := fun x => ((x - α) / (x - γ)) ^ a₁ * ((x - β) / (x - γ)) ^ b₁ with hPdef
  have hw : w = fun x => P x * u (T x) := rfl
  obtain ⟨hzα, hzγ⟩ := div_ne_zero_iff.mp (slitPlane_ne_zero hA)
  have hzβ : z - β ≠ 0 := (div_ne_zero_iff.mp (slitPlane_ne_zero hB)).1
  -- Analyticity of the prefactor and of the Möbius variable, for the product and chain rules.
  have hPa : AnalyticAt ℂ P z := analyticAt_riemannPrefactor hA hB
  have hTa : AnalyticAt ℂ T z := analyticAt_crossRatio_first (sub_ne_zero.mp hzγ)
  -- Expand `w′′` and `w′` by the product and chain rules, and insert the derivatives of `P` and
  -- `T`.
  set L : ℂ := a₁ * ((z - α)⁻¹ - (z - γ)⁻¹) + b₁ * ((z - β)⁻¹ - (z - γ)⁻¹) with hL
  -- State the derivatives of `P` with the value `P z` kept folded.
  have hPd : deriv P z = P z * L := (hasDerivAt_riemannPrefactor hA hB).deriv
  have hPdd : deriv (deriv P) z = P z * (L ^ 2 + (a₁ * (-((z - α) ^ 2)⁻¹ + ((z - γ) ^ 2)⁻¹) +
      b₁ * (-((z - β) ^ 2)⁻¹ + ((z - γ) ^ 2)⁻¹))) :=
    (hasDerivAt_deriv_riemannPrefactor hA hB).deriv
  rw [hw, (hPa.hasDerivAt_deriv_mul_comp hTa hu).deriv,
    (hPa.deriv_mul_comp_eventuallyEq hTa hu).eq_of_nhds, hPdd, hPd,
    (hasDerivAt_deriv_crossRatio_first (sub_ne_zero.mp hzγ)).deriv,
    (hasDerivAt_crossRatio_first (sub_ne_zero.mp hzγ)).deriv]
  beta_reduce
  -- Riemann's operator at `z` is now the multiplier times the hypergeometric operator at `T z`,
  -- which clearing denominators verifies.
  have hc2 : c₂ = 1 - a₁ - a₂ - b₁ - b₂ - c₁ := by linear_combination hsum
  subst hc2
  have hTz : crossRatio z β α γ = T z := by rw [hTdef]
  have hPz : ((z - α) / (z - γ)) ^ a₁ * ((z - β) / (z - γ)) ^ b₁ = P z := by rw [hPdef]
  rw [hTz, hPz]
  generalize u (T z) = F0
  generalize deriv u (T z) = F1
  generalize deriv (deriv u) (T z) = F2
  generalize P z = P0
  simp only [hTdef, hL, crossRatio_def]
  rw [← sub_eq_zero]
  have hβα : β - α ≠ 0 := sub_ne_zero.mpr hαβ.symm
  field_simp
  ring

/-- **DLMF 15.11.7**, analytic form: if `u` is analytic on a set `V` and solves the
hypergeometric equation (DLMF 15.10.1) with `a = a₁ + b₁ + c₁`, `b = a₁ + b₁ + c₂`,
`c = 1 + a₁ − a₂` there, then
`w(z) = ((z − α)/(z − γ))^{a₁} ((z − β)/(z − γ))^{b₁} u(crossRatio z β α γ)` is analytic on, and
solves Riemann's equation (DLMF 15.11.1) with singular points `α, β, γ` and exponents `{a₁, a₂}`,
`{b₁, b₂}`, `{c₁, c₂}` under Fuchs's relation (DLMF 15.11.2) on, every set `U` where the two
quotients lie in the slit plane and the Möbius variable `crossRatio z β α γ` lies in `V`. -/
theorem analyticOnNhd_and_riemannEquation_of_hypergeometricEquation
    {α β γ a₁ a₂ b₁ b₂ c₁ c₂ : ℂ} (hαβ : α ≠ β) (hsum : a₁ + a₂ + b₁ + b₂ + c₁ + c₂ = 1)
    {U V : Set ℂ}
    (hUs : ∀ z ∈ U, (z - α) / (z - γ) ∈ slitPlane ∧ (z - β) / (z - γ) ∈ slitPlane)
    (hUV : ∀ z ∈ U, crossRatio z β α γ ∈ V) {u : ℂ → ℂ} (hu : AnalyticOnNhd ℂ u V)
    (hu' : ∀ ζ ∈ V, ζ * (1 - ζ) * deriv (deriv u) ζ +
      (1 + a₁ - a₂ - ((a₁ + b₁ + c₁) + (a₁ + b₁ + c₂) + 1) * ζ) * deriv u ζ -
        (a₁ + b₁ + c₁) * (a₁ + b₁ + c₂) * u ζ = 0) :
    let w : ℂ → ℂ := fun z => ((z - α) / (z - γ)) ^ a₁ * ((z - β) / (z - γ)) ^ b₁ *
      u (crossRatio z β α γ)
    AnalyticOnNhd ℂ w U ∧ ∀ z ∈ U, deriv (deriv w) z +
      ((1 - a₁ - a₂) / (z - α) + (1 - b₁ - b₂) / (z - β) + (1 - c₁ - c₂) / (z - γ)) * deriv w z +
        ((α - β) * (α - γ) * a₁ * a₂ / (z - α) + (β - α) * (β - γ) * b₁ * b₂ / (z - β) +
          (γ - α) * (γ - β) * c₁ * c₂ / (z - γ)) / ((z - α) * (z - β) * (z - γ)) * w z = 0 := by
  intro w
  refine ⟨fun z hz => ?_, fun z hz => ?_⟩
  · have hzγ : z - γ ≠ 0 := (div_ne_zero_iff.mp (slitPlane_ne_zero (hUs z hz).1)).2
    exact (analyticAt_riemannPrefactor (hUs z hz).1 (hUs z hz).2).mul
      (AnalyticAt.comp (f := fun x => crossRatio x β α γ) (hu _ (hUV z hz))
        (analyticAt_crossRatio_first (sub_ne_zero.mp hzγ)))
  -- The operator identity, with the hypergeometric operator vanishing at the Möbius variable.
  have h := riemannEquation_residual_eq_mul_hypergeometricEquation_residual hαβ hsum
    (hUs z hz).1 (hUs z hz).2 (hu _ (hUV z hz))
  rw [hu' _ (hUV z hz), mul_zero] at h
  exact h

/-- **DLMF 15.11.7**: if `u` solves the hypergeometric equation (DLMF 15.10.1) with
`a = a₁ + b₁ + c₁`, `b = a₁ + b₁ + c₂`, `c = 1 + a₁ − a₂` on an open set `V`, then
`w(z) = ((z − α)/(z − γ))^{a₁} ((z − β)/(z − γ))^{b₁} u((z − α)(β − γ)/((z − γ)(β − α)))` solves
Riemann's equation (DLMF 15.11.1) with singular points `α, β, γ` and exponents `{a₁, a₂}`,
`{b₁, b₂}`, `{c₁, c₂}` under Fuchs's relation (DLMF 15.11.2), on every set `U` where the two
quotients lie in the slit plane and the Möbius variable lies in `V`. The singular points need only
`α ≠ β`; the slit-plane condition already forces `z ≠ α, β, γ` on `U`. See
`TauCeti.analyticOnNhd_and_riemannEquation_of_hypergeometricEquation` for the form with `u`
analytic on an arbitrary `V` and `w` analytic on `U`. -/
theorem riemannEquation_of_hypergeometricEquation {α β γ a₁ a₂ b₁ b₂ c₁ c₂ : ℂ} (hαβ : α ≠ β)
    (hsum : a₁ + a₂ + b₁ + b₂ + c₁ + c₂ = 1) {U V : Set ℂ} (hV : IsOpen V)
    (hUs : ∀ z ∈ U, (z - α) / (z - γ) ∈ slitPlane ∧ (z - β) / (z - γ) ∈ slitPlane)
    (hUV : ∀ z ∈ U, (z - α) * (β - γ) / ((z - γ) * (β - α)) ∈ V) {u : ℂ → ℂ}
    (hu : DifferentiableOn ℂ u V)
    (hu' : ∀ ζ ∈ V, ζ * (1 - ζ) * deriv (deriv u) ζ +
      (1 + a₁ - a₂ - ((a₁ + b₁ + c₁) + (a₁ + b₁ + c₂) + 1) * ζ) * deriv u ζ -
        (a₁ + b₁ + c₁) * (a₁ + b₁ + c₂) * u ζ = 0) :
    let w : ℂ → ℂ := fun z => ((z - α) / (z - γ)) ^ a₁ * ((z - β) / (z - γ)) ^ b₁ *
      u ((z - α) * (β - γ) / ((z - γ) * (β - α)))
    DifferentiableOn ℂ w U ∧ ∀ z ∈ U, deriv (deriv w) z +
      ((1 - a₁ - a₂) / (z - α) + (1 - b₁ - b₂) / (z - β) + (1 - c₁ - c₂) / (z - γ)) * deriv w z +
        ((α - β) * (α - γ) * a₁ * a₂ / (z - α) + (β - α) * (β - γ) * b₁ * b₂ / (z - β) +
          (γ - α) * (γ - β) * c₁ * c₂ / (z - γ)) / ((z - α) * (z - β) * (z - γ)) * w z = 0 := by
  -- Translate the expanded Möbius variable into the cross-ratio, and analyticity back.
  have h := analyticOnNhd_and_riemannEquation_of_hypergeometricEquation hαβ hsum hUs
    (fun z hz => crossRatio_def z β α γ ▸ hUV z hz) (hu.analyticOnNhd hV) hu'
  simp only [crossRatio_def] at h
  exact ⟨h.1.differentiableOn, h.2⟩

end TauCeti
