/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import TauCeti.Analysis.Calculus.Deriv.Second
import TauCeti.Analysis.Complex.SlitPlane
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

## Main result

* `TauCeti.riemannEquation_of_hypergeometricEquation`: DLMF 15.11.7, from a solution of the
  hypergeometric equation to a solution of Riemann's equation.

## Implementation notes

Write `w = P · (u ∘ T)` with the prefactor `P` and the Möbius variable `T`. The second-order
product and chain rule `AnalyticAt.hasDerivAt_deriv_mul_comp` expresses `w′′` and `w′` through
`P, P′, P′′`, `T′, T′′` and `u, u′, u′′` at `T z`. The prefactor has logarithmic derivative
`L = a₁ (1/(z − α) − 1/(z − γ)) + b₁ (1/(z − β) − 1/(z − γ))`, so `P′ = P L` and
`P′′ = P (L ^ 2 + L′)` (`TauCeti.hasDerivAt_sub_div_sub_cpow`,
`TauCeti.hasDerivAt_deriv_of_eventually_hasDerivAt_mul`), and `T` is a fractional-linear map
(`TauCeti.hasDerivAt_mul_add_div_mul_add`, `TauCeti.hasDerivAt_deriv_mul_add_div_mul_add`).
After these substitutions Riemann's equation at `z` is a multiple of the hypergeometric equation
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
  have hzγ : z - γ ≠ 0 := (ne_zero_and_ne_zero_of_div_mem_slitPlane hA).2
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
  obtain ⟨hzα, hzγ⟩ := ne_zero_and_ne_zero_of_div_mem_slitPlane hA
  have hzβ : z - β ≠ 0 := (ne_zero_and_ne_zero_of_div_mem_slitPlane hB).1
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

/-- The first and second derivatives of the Möbius variable
`T(w) = (w − α)(β − γ)/((w − γ)(β − α))` of DLMF 15.11.7 at `z ≠ γ`, for `α ≠ β`, from those of
the fractional-linear map `w ↦ ((β − γ) w − α (β − γ)) / ((β − α) w − γ (β − α))`. -/
private theorem derivs_riemannMobius {α β γ z : ℂ} (hαβ : α ≠ β) (hz : z ≠ γ) :
    deriv (fun w => (w - α) * (β - γ) / ((w - γ) * (β - α))) z =
        (β - γ) * (α - γ) / (β - α) * ((z - γ) ^ 2)⁻¹ ∧
      deriv (deriv fun w => (w - α) * (β - γ) / ((w - γ) * (β - α))) z =
        -2 * ((β - γ) * (α - γ) / (β - α)) * ((z - γ) ^ 3)⁻¹ := by
  have hβα : β - α ≠ 0 := sub_ne_zero.mpr hαβ.symm
  have hzγ : z - γ ≠ 0 := sub_ne_zero.mpr hz
  have hT : (fun w => (w - α) * (β - γ) / ((w - γ) * (β - α))) =
      fun w => ((β - γ) * w + -(α * (β - γ))) / ((β - α) * w + -(γ * (β - α))) := by
    funext w
    ring
  have hden : (β - α) * z + -(γ * (β - α)) = (β - α) * (z - γ) := by ring
  have hne : (β - α) * z + -(γ * (β - α)) ≠ 0 := hden ▸ mul_ne_zero hβα hzγ
  rw [hT, (hasDerivAt_mul_add_div_mul_add hne).deriv,
    (hasDerivAt_deriv_mul_add_div_mul_add hne).deriv, hden]
  constructor
  · field_simp
    ring
  · field_simp
    ring

/-- **DLMF 15.11.7**: if `u` solves the hypergeometric equation (DLMF 15.10.1) with
`a = a₁ + b₁ + c₁`, `b = a₁ + b₁ + c₂`, `c = 1 + a₁ − a₂` on an open set `V`, then
`w(z) = ((z − α)/(z − γ))^{a₁} ((z − β)/(z − γ))^{b₁} u((z − α)(β − γ)/((z − γ)(β − α)))` solves
Riemann's equation (DLMF 15.11.1) with singular points `α, β, γ` and exponents `{a₁, a₂}`,
`{b₁, b₂}`, `{c₁, c₂}` under Fuchs's relation (DLMF 15.11.2), on every set `U` where the two
quotients lie in the slit plane and the Möbius variable lies in `V`. The singular points need only
`α ≠ β`; the slit-plane condition already forces `z ≠ α, β, γ` on `U`. -/
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
  intro w
  -- `w = P · (u ∘ T)`, with the Möbius variable `T` and the prefactor `P`.
  set T : ℂ → ℂ := fun w => (w - α) * (β - γ) / ((w - γ) * (β - α))
  set P : ℂ → ℂ := fun w => ((w - α) / (w - γ)) ^ a₁ * ((w - β) / (w - γ)) ^ b₁
  have hw : w = fun z => P z * u (T z) := rfl
  have hne : ∀ z ∈ U, z - α ≠ 0 ∧ z - β ≠ 0 ∧ z - γ ≠ 0 := by
    intro z hz
    obtain ⟨hzα, hzγ⟩ := ne_zero_and_ne_zero_of_div_mem_slitPlane (hUs z hz).1
    exact ⟨hzα, (ne_zero_and_ne_zero_of_div_mem_slitPlane (hUs z hz).2).1, hzγ⟩
  -- Analyticity of the three ingredients, for the product and chain rules.
  have hPa : ∀ z ∈ U, AnalyticAt ℂ P z := fun z hz =>
    analyticAt_riemannPrefactor (hUs z hz).1 (hUs z hz).2
  have hTa : ∀ z ∈ U, AnalyticAt ℂ T z := fun z hz =>
    ((analyticAt_id.sub analyticAt_const).mul analyticAt_const).div
      ((analyticAt_id.sub analyticAt_const).mul analyticAt_const)
      (mul_ne_zero (hne z hz).2.2 (sub_ne_zero.mpr hαβ.symm))
  have hFa : ∀ z ∈ U, AnalyticAt ℂ u (T z) := fun z hz =>
    hu.analyticAt (hV.mem_nhds (hUV z hz))
  refine ⟨fun z hz => ?_, fun z hz => ?_⟩
  · rw [hw]
    exact ((hPa z hz).mul ((hFa z hz).comp (hTa z hz))).differentiableAt.differentiableWithinAt
  obtain ⟨hzα, hzβ, hzγ⟩ := hne z hz
  -- Expand `w′′` and `w′` by the product and chain rules, and insert the derivatives of `P` and
  -- `T`.
  have hode := hu' (T z) (hUV z hz)
  obtain ⟨hTd, hTdd⟩ := derivs_riemannMobius (α := α) (β := β) hαβ (sub_ne_zero.mp hzγ)
  set L : ℂ := a₁ * ((z - α)⁻¹ - (z - γ)⁻¹) + b₁ * ((z - β)⁻¹ - (z - γ)⁻¹) with hL
  -- State the derivatives of `P` with the value `P z` kept folded.
  have hPd : deriv P z = P z * L := (hasDerivAt_riemannPrefactor (hUs z hz).1 (hUs z hz).2).deriv
  have hPdd : deriv (deriv P) z = P z * (L ^ 2 + (a₁ * (-((z - α) ^ 2)⁻¹ + ((z - γ) ^ 2)⁻¹) +
      b₁ * (-((z - β) ^ 2)⁻¹ + ((z - γ) ^ 2)⁻¹))) :=
    (hasDerivAt_deriv_riemannPrefactor (hUs z hz).1 (hUs z hz).2).deriv
  rw [hw, ((hPa z hz).hasDerivAt_deriv_mul_comp (hTa z hz) (hFa z hz)).deriv,
    ((hPa z hz).deriv_mul_comp_eventuallyEq (hTa z hz) (hFa z hz)).eq_of_nhds, hPdd, hPd, hTdd,
    hTd]
  beta_reduce
  -- Riemann's equation at `z` is now a multiple of the hypergeometric equation at `T z`, which
  -- clearing denominators verifies.
  have hc2 : c₂ = 1 - a₁ - a₂ - b₁ - b₂ - c₁ := by linear_combination hsum
  subst hc2
  generalize u (T z) = F0 at *
  generalize deriv u (T z) = F1 at *
  generalize deriv (deriv u) (T z) = F2 at *
  generalize P z = P0
  simp only [T, hL] at hode ⊢
  -- The multiplier is `P T′ ^ 2 / (T (1 − T))`, which matches the `u′′` terms. With
  -- `T′ = k / (z − γ) ^ 2`, `k = (β − γ)(α − γ)/(β − α)`, and
  -- `T (1 − T) = (z − α)(z − β)(β − γ)(γ − α) / ((z − γ)(β − α)) ^ 2`
  -- it reduces to the factor below.
  linear_combination (norm := skip)
    (-P0 * (β - γ) * (α - γ) / ((z - α) * (z - β) * (z - γ) ^ 2)) * hode
  have hβα : β - α ≠ 0 := sub_ne_zero.mpr hαβ.symm
  field_simp
  ring

end TauCeti
