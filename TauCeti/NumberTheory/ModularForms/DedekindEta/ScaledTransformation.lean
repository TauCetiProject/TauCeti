/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.DedekindEta.Transformation
public import TauCeti.NumberTheory.ModularForms.Degeneracy
import TauCeti.Analysis.Complex.UpperHalfPlane.MoebiusAction

/-!
# The transformation of `η(δ τ)`

For a positive integer `δ` and `γ = (a b; c d) ∈ SL(2, ℤ)` with `δ ∣ c`, the matrix
`γ_δ = (a, δ b; c / δ, d)` is the conjugate `TauCeti.conjScale δ γ (c / δ)` of `γ` by
`diag(δ, 1)`. It sends `δ τ` to `δ · γ τ` (`TauCeti.conjScale_smul_scaleGL_smul`) and has the same
automorphy factor `c τ + d` at `δ τ` as `γ` at `τ` (`TauCeti.denom_conjScale_scaleGL_smul`), so
the transformation law of `η` at `γ_δ` gives `η(δ · γ τ) = ε(γ_δ) √(c τ + d) η(δ τ)`.

## Main results

* `TauCeti.ModularForm.eta_natCast_mul_smul`: `η(δ · γ τ) = ε(γ_δ) √(c τ + d) η(δ τ)` when
  `δ ∣ c`.

## References

* T. M. Apostol, *Modular Functions and Dirichlet Series in Number Theory*, 2nd ed., GTM 41,
  Theorem 3.4, for the transformation law of `η`.
-/

public section

open UpperHalfPlane

open scoped MatrixGroups ModularForm

namespace TauCeti.ModularForm

/-- **The transformation of `η(δ τ)`**: if `δ > 0` divides the lower-left entry `c = δ c'` of
`γ = (a b; c d) ∈ SL(2, ℤ)`, then `η(δ · γ τ) = ε(γ_δ) √(c τ + d) η(δ τ)` on the upper half-plane,
where `γ_δ = (a, δ b; c', d)` is the conjugate `conjScale δ γ c'` of `γ` by `diag(δ, 1)`. -/
theorem eta_natCast_mul_smul {δ : ℕ} (hδ : 0 < δ) (γ : SL(2, ℤ)) {c : ℤ} (hc : γ 1 0 = δ * c)
    (τ : ℍ) :
    η (δ * (γ • τ : ℍ)) =
      etaMultiplier (conjScale δ γ c hc) * Complex.sqrt ((γ 1 0 : ℂ) * τ + γ 1 1) * η (δ * τ) := by
  have : NeZero δ := ⟨hδ.ne'⟩
  have hden : ((conjScale δ γ c hc 1 0 : ℤ) : ℂ) * (scaleGL δ • τ : ℍ) + conjScale δ γ c hc 1 1 =
      (γ 1 0 : ℂ) * τ + γ 1 1 := by
    rw [← ModularGroup.denom_mapGL, ← ModularGroup.denom_mapGL, denom_conjScale_scaleGL_smul]
  have h := eta_smul (conjScale δ γ c hc) (scaleGL δ • τ)
  rwa [conjScale_smul_scaleGL_smul, hden, coe_scaleGL_smul, coe_scaleGL_smul] at h

end TauCeti.ModularForm
