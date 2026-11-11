/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Abel's identity for the hypergeometric equation

For solutions `f`, `g` of the hypergeometric equation (DLMF 15.10.1)

`z (1 − z) w″ + (c − (a + b + 1) z) w′ − a b w = 0`

on an open set avoiding `0` and `1`, the Wronskian `𝒲{f, g} = f g′ − f′ g` satisfies Abel's
identity `𝒲′ = −((c − (a + b + 1) z)/(z (1 − z))) 𝒲`. Consequently, on a connected open subset of
`slitPlane ∩ {1 − z ∈ slitPlane}` the Wronskian is a constant multiple of
`z^{−c} (1 − z)^{c−a−b−1}`, and two solutions with nowhere vanishing Wronskian span all solutions.

The statements are about arbitrary solutions, so they do not need a definition of the Gauss
function. The Wronskian is written out as `f z * deriv g z - deriv f z * g z`.

## Main results

* `TauCeti.hasDerivAt_wronskian_of_hypergeometricEquation`: Abel's identity.
* `TauCeti.exists_wronskian_eq_mul_cpow_of_hypergeometricEquation`: the Wronskian is a constant
  multiple of `z^{−c} (1 − z)^{c−a−b−1}` on a connected open set in the cut plane.
* `TauCeti.exists_eq_add_of_hypergeometricEquation`: the span criterion.

## References

* [DLMF] *NIST Digital Library of Mathematical Functions*, §15.10, <https://dlmf.nist.gov/15.10>.
-/

@[expose] public section

open Complex Filter Set
open scoped Topology

namespace TauCeti

variable {a b c : ℂ} {U : Set ℂ}

/-- A function holomorphic on an open set has a holomorphic derivative there. -/
private theorem hasDerivAt_deriv_of_differentiableOn {f : ℂ → ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) {z : ℂ} (hz : z ∈ U) :
    HasDerivAt f (deriv f z) z ∧ HasDerivAt (deriv f) (deriv (deriv f) z) z := by
  have ha := hf.analyticAt (hU.mem_nhds hz)
  exact ⟨ha.differentiableAt.hasDerivAt, ha.deriv.differentiableAt.hasDerivAt⟩

/-- **Abel's identity** for the hypergeometric equation (DLMF 15.10.1): if `f` and `g` solve
15.10.1 on an open set `U`, then at every `z ∈ U` with `z ≠ 0, 1` the Wronskian
`𝒲{f, g} = f g′ − f′ g` has derivative `−((c − (a + b + 1) z)/(z (1 − z))) 𝒲{f, g}`. -/
theorem hasDerivAt_wronskian_of_hypergeometricEquation {f g : ℂ → ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    (hf' : ∀ z ∈ U, z * (1 - z) * deriv (deriv f) z + (c - (a + b + 1) * z) * deriv f z -
      a * b * f z = 0)
    (hg' : ∀ z ∈ U, z * (1 - z) * deriv (deriv g) z + (c - (a + b + 1) * z) * deriv g z -
      a * b * g z = 0)
    {z : ℂ} (hz : z ∈ U) (hz₀ : z ≠ 0) (hz₁ : z ≠ 1) :
    HasDerivAt (fun ζ => f ζ * deriv g ζ - deriv f ζ * g ζ)
      (-((c - (a + b + 1) * z) / (z * (1 - z))) * (f z * deriv g z - deriv f z * g z)) z := by
  obtain ⟨hf₁, hf₂⟩ := hasDerivAt_deriv_of_differentiableOn hU hf hz
  obtain ⟨hg₁, hg₂⟩ := hasDerivAt_deriv_of_differentiableOn hU hg hz
  refine ((hf₁.mul hg₂).sub (hf₂.mul hg₁)).congr_deriv ?_
  have h1 : 1 - z ≠ 0 := sub_ne_zero.mpr hz₁.symm
  have ef : deriv (deriv f) z =
      (a * b * f z - (c - (a + b + 1) * z) * deriv f z) / (z * (1 - z)) := by
    rw [eq_div_iff (mul_ne_zero hz₀ h1)]
    linear_combination hf' z hz
  have eg : deriv (deriv g) z =
      (a * b * g z - (c - (a + b + 1) * z) * deriv g z) / (z * (1 - z)) := by
    rw [eq_div_iff (mul_ne_zero hz₀ h1)]
    linear_combination hg' z hz
  rw [ef, eg]
  field_simp
  ring

/-- **The Wronskian in the cut plane** (DLMF 15.10.1, Abel's identity integrated): if `f` and `g`
solve 15.10.1 on a connected open set `U ⊆ slitPlane ∩ {1 − z ∈ slitPlane}`, then
`𝒲{f, g} = C z^{−c} (1 − z)^{c−a−b−1}` on `U` for a constant `C`. -/
theorem exists_wronskian_eq_mul_cpow_of_hypergeometricEquation {f g : ℂ → ℂ} (hU : IsOpen U)
    (hUc : IsPreconnected U) (hUs : ∀ z ∈ U, z ∈ slitPlane ∧ 1 - z ∈ slitPlane)
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    (hf' : ∀ z ∈ U, z * (1 - z) * deriv (deriv f) z + (c - (a + b + 1) * z) * deriv f z -
      a * b * f z = 0)
    (hg' : ∀ z ∈ U, z * (1 - z) * deriv (deriv g) z + (c - (a + b + 1) * z) * deriv g z -
      a * b * g z = 0) :
    ∃ C : ℂ, ∀ z ∈ U, f z * deriv g z - deriv f z * g z =
      C * z ^ (-c) * (1 - z) ^ (c - a - b - 1) := by
  set W : ℂ → ℂ := fun ζ => f ζ * deriv g ζ - deriv f ζ * g ζ with hW
  set q : ℂ → ℂ := fun ζ => W ζ * ζ ^ c * (1 - ζ) ^ (a + b + 1 - c) with hq
  have hne (z : ℂ) (hz : z ∈ U) : z ≠ 0 ∧ 1 - z ≠ 0 :=
    ⟨slitPlane_ne_zero (hUs z hz).1, slitPlane_ne_zero (hUs z hz).2⟩
  have hqd (z : ℂ) (hz : z ∈ U) : HasDerivAt q 0 z := by
    obtain ⟨hz₀, hz₁⟩ := hne z hz
    have hWd := hasDerivAt_wronskian_of_hypergeometricEquation hU hf hg hf' hg' hz hz₀
      (fun h => hz₁ (by rw [h, sub_self]))
    have hp := (hasDerivAt_id z).cpow_const (c := c) (hUs z hz).1
    have hr := ((hasDerivAt_id z).const_sub 1).cpow_const (c := a + b + 1 - c) (hUs z hz).2
    refine ((hWd.mul hp).mul hr).congr_deriv ?_
    simp only [id, Pi.mul_apply]
    rw [cpow_sub c 1 hz₀, cpow_sub (a + b + 1 - c) 1 hz₁, cpow_one, cpow_one]
    field_simp
    ring
  have hqU : DifferentiableOn ℂ q U := fun z hz =>
    (hqd z hz).differentiableAt.differentiableWithinAt
  obtain ⟨C, hC⟩ := hU.exists_is_const_of_deriv_eq_zero hUc hqU fun z hz => (hqd z hz).deriv
  refine ⟨C, fun z hz => ?_⟩
  obtain ⟨hz₀, hz₁⟩ := hne z hz
  have h := hC z hz
  simp only [hq, hW] at h
  have h₀ : z ^ c ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hz₀)
  have h₁ : (1 - z) ^ (a + b + 1 - c) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hz₁)
  rw [show c - a - b - 1 = -(a + b + 1 - c) by ring, cpow_neg, cpow_neg, ← h]
  field_simp

/-- **The span criterion** for the hypergeometric equation: if `f₁` and `f₂` solve 15.10.1 on a
connected open set `U` avoiding `0` and `1`, and `𝒲{f₁, f₂}` has no zero on `U`, then every
solution `w` on `U` is `A f₁ + B f₂` with constants `A`, `B`. -/
theorem exists_eq_add_of_hypergeometricEquation {f₁ f₂ w : ℂ → ℂ} (hU : IsOpen U)
    (hUc : IsPreconnected U) (hU₀₁ : ∀ z ∈ U, z ≠ 0 ∧ z ≠ 1)
    (hf₁ : DifferentiableOn ℂ f₁ U) (hf₂ : DifferentiableOn ℂ f₂ U)
    (hw : DifferentiableOn ℂ w U)
    (hf₁' : ∀ z ∈ U, z * (1 - z) * deriv (deriv f₁) z + (c - (a + b + 1) * z) * deriv f₁ z -
      a * b * f₁ z = 0)
    (hf₂' : ∀ z ∈ U, z * (1 - z) * deriv (deriv f₂) z + (c - (a + b + 1) * z) * deriv f₂ z -
      a * b * f₂ z = 0)
    (hw' : ∀ z ∈ U, z * (1 - z) * deriv (deriv w) z + (c - (a + b + 1) * z) * deriv w z -
      a * b * w z = 0)
    (hW : ∀ z ∈ U, f₁ z * deriv f₂ z - deriv f₁ z * f₂ z ≠ 0) :
    ∃ A B : ℂ, ∀ z ∈ U, w z = A * f₁ z + B * f₂ z := by
  -- A ratio of two Wronskians of solutions is constant on `U`.
  have hratio {g₁ g₂ : ℂ → ℂ} (hg₁ : DifferentiableOn ℂ g₁ U) (hg₂ : DifferentiableOn ℂ g₂ U)
      (hg₁' : ∀ z ∈ U, z * (1 - z) * deriv (deriv g₁) z + (c - (a + b + 1) * z) * deriv g₁ z -
        a * b * g₁ z = 0)
      (hg₂' : ∀ z ∈ U, z * (1 - z) * deriv (deriv g₂) z + (c - (a + b + 1) * z) * deriv g₂ z -
        a * b * g₂ z = 0) :
      ∃ K : ℂ, ∀ z ∈ U, (g₁ z * deriv g₂ z - deriv g₁ z * g₂ z) /
        (f₁ z * deriv f₂ z - deriv f₁ z * f₂ z) = K := by
    have hd (z : ℂ) (hz : z ∈ U) : HasDerivAt (fun ζ => (g₁ ζ * deriv g₂ ζ - deriv g₁ ζ * g₂ ζ) /
        (f₁ ζ * deriv f₂ ζ - deriv f₁ ζ * f₂ ζ)) 0 z := by
      have h₁ := hasDerivAt_wronskian_of_hypergeometricEquation hU hg₁ hg₂ hg₁' hg₂' hz
        (hU₀₁ z hz).1 (hU₀₁ z hz).2
      have h₂ := hasDerivAt_wronskian_of_hypergeometricEquation hU hf₁ hf₂ hf₁' hf₂' hz
        (hU₀₁ z hz).1 (hU₀₁ z hz).2
      refine (h₁.div h₂ (hW z hz)).congr_deriv ?_
      ring
    exact hU.exists_is_const_of_deriv_eq_zero hUc
      (fun z hz => (hd z hz).differentiableAt.differentiableWithinAt) fun z hz => (hd z hz).deriv
  obtain ⟨A, hA⟩ := hratio hw hf₂ hw' hf₂'
  obtain ⟨B, hB⟩ := hratio hf₁ hw hf₁' hw'
  refine ⟨A, B, fun z hz => ?_⟩
  have hWz := hW z hz
  have hA' := hA z hz
  have hB' := hB z hz
  rw [div_eq_iff hWz] at hA' hB'
  apply mul_right_cancel₀ hWz
  linear_combination f₁ z * hA' + f₂ z * hB'

end TauCeti
