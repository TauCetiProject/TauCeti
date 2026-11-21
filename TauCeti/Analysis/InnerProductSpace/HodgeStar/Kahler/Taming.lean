/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Kahler.PositiveCone
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Mass control of approximately positive fields by a taming form

Let `ξ` be a field of two-vectors on a measure space `X`, for instance the density of a current
of degree two on a four-manifold, and let `J x` be an orthogonal almost complex structure at each
point. If a two-form `Ω` tames every `J x`, `Ω(v, J v) ≥ c₀ ‖v‖²`, and is bounded by `B`, then the
pointwise estimate `TauCeti.AlmostComplexStructure.mul_norm_le_inner_add_mul_infDist_positiveCone`
integrates to

`c₀ ∫ ‖ξ‖ ≤ ∫ ⟪Ω, ξ⟫ + (B + c₀) ∫ dist(ξ, positiveCone)`

(`TauCeti.AlmostComplexStructure.mul_integral_norm_le_integral_inner_add_mul_integral_infDist`):
the total norm is controlled by the pairing with `Ω` and the integrated distance to the cone of
positive `(1,1)`-forms of `J`.

In Taubes's analysis of Seiberg–Witten solutions near a pseudoholomorphic curve, the pairing of
the dilated curvature current with a taming form `Ω = K π^*ω_C + dλ` is a topological quantity,
`K m area(C)` for a current of transverse flux `m`. Its product-chart form is
`TauCeti.integral_wedge_smul_compContinuousLinearMap_fst_add_extDeriv`, and its global form over a
σ-compact preconnected surface with trivial normal line is
`TauCeti.integralTopForm_wedge_smul_mpullback_fst_add_mextDerivₗ`. Applying the theorems
below to a current also requires identifying `ξ` with its two-vector density, so that
`∫ ⟪Ω, ξ⟫` equals the wedge pairing `∫ T ∧ Ω`; that identification is not done here.
The cone defect is
bounded by a small error plus a small multiple of the mass itself. The second theorem absorbs that
multiple: if `∫ dist(ξ, positiveCone) ≤ ε + δ ∫ ‖ξ‖` with `(B + c₀) δ < c₀`, then

`∫ ‖ξ‖ ≤ (∫ ⟪Ω, ξ⟫ + (B + c₀) ε) / (c₀ - (B + c₀) δ)`

(`TauCeti.AlmostComplexStructure.integral_norm_le_div_of_integral_infDist_le`).

The norm here is the inner product norm of two-vectors, which bounds the mass norm of the
corresponding current up to a constant depending only on the dimension.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
-/

public section

noncomputable section

open MeasureTheory Metric exteriorPower
open scoped RealInnerProductSpace

namespace TauCeti.AlmostComplexStructure

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {X : Type*} [MeasurableSpace X] {μ : Measure X} {J : X → AlmostComplexStructure V}
  {Ω ξ : X → ⋀[ℝ]^2 V} {c₀ B : ℝ}

/-- **Mass control by a taming form and the cone defect.** If, almost everywhere, `J x` is
orthogonal, `Ω x` tames it with constant `c₀ ≥ 0` and `‖Ω x‖ ≤ B`, then a field `ξ` of two-vectors
satisfies `c₀ ∫ ‖ξ‖ ≤ ∫ ⟪Ω, ξ⟫ + (B + c₀) ∫ dist(ξ, positiveCone)`. -/
theorem mul_integral_norm_le_integral_inner_add_mul_integral_infDist
    (hJ : ∀ᵐ x ∂μ, ∀ v w, ⟪J x v, J x w⟫ = ⟪v, w⟫) (hc₀ : 0 ≤ c₀)
    (hΩ : ∀ᵐ x ∂μ, ∀ v, c₀ * ‖v‖ ^ 2 ≤ ⟪Ω x, ιMulti ℝ 2 ![v, J x v]⟫)
    (hB : ∀ᵐ x ∂μ, ‖Ω x‖ ≤ B) (hξ : Integrable (fun x ↦ ‖ξ x‖) μ)
    (hP : Integrable (fun x ↦ ⟪Ω x, ξ x⟫) μ)
    (hD : Integrable (fun x ↦ infDist (ξ x) ((J x).positiveCone : Set (⋀[ℝ]^2 V))) μ) :
    c₀ * ∫ x, ‖ξ x‖ ∂μ ≤ ∫ x, ⟪Ω x, ξ x⟫ ∂μ +
      (B + c₀) * ∫ x, infDist (ξ x) ((J x).positiveCone : Set (⋀[ℝ]^2 V)) ∂μ := by
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add hP (hD.const_mul _)]
  refine integral_mono_ae (hξ.const_mul _) (hP.add (hD.const_mul _)) ?_
  filter_upwards [hJ, hΩ, hB] with x hJx hΩx hBx
  have h := mul_norm_le_inner_add_mul_infDist_positiveCone hJx hc₀ hΩx (ξ x)
  have hd := infDist_nonneg (x := ξ x) (s := ((J x).positiveCone : Set (⋀[ℝ]^2 V)))
  nlinarith

/-- **Absorption of a small multiple of the mass.** Under the hypotheses of
`TauCeti.AlmostComplexStructure.mul_integral_norm_le_integral_inner_add_mul_integral_infDist`, with
`0 ≤ B`, suppose the cone defect is at most `ε` plus a small multiple `δ` of the total norm,
`∫ dist(ξ, positiveCone) ≤ ε + δ ∫ ‖ξ‖`, where `(B + c₀) δ < c₀`. Then
`∫ ‖ξ‖ ≤ (∫ ⟪Ω, ξ⟫ + (B + c₀) ε) / (c₀ - (B + c₀) δ)`. -/
theorem integral_norm_le_div_of_integral_infDist_le
    (hJ : ∀ᵐ x ∂μ, ∀ v w, ⟪J x v, J x w⟫ = ⟪v, w⟫) (hc₀ : 0 ≤ c₀)
    (hΩ : ∀ᵐ x ∂μ, ∀ v, c₀ * ‖v‖ ^ 2 ≤ ⟪Ω x, ιMulti ℝ 2 ![v, J x v]⟫)
    (hB₀ : 0 ≤ B) (hB : ∀ᵐ x ∂μ, ‖Ω x‖ ≤ B) (hξ : Integrable (fun x ↦ ‖ξ x‖) μ)
    (hP : Integrable (fun x ↦ ⟪Ω x, ξ x⟫) μ)
    (hD : Integrable (fun x ↦ infDist (ξ x) ((J x).positiveCone : Set (⋀[ℝ]^2 V))) μ)
    {ε δ : ℝ}
    (hDle : ∫ x, infDist (ξ x) ((J x).positiveCone : Set (⋀[ℝ]^2 V)) ∂μ ≤
      ε + δ * ∫ x, ‖ξ x‖ ∂μ)
    (hδ : (B + c₀) * δ < c₀) :
    ∫ x, ‖ξ x‖ ∂μ ≤ (∫ x, ⟪Ω x, ξ x⟫ ∂μ + (B + c₀) * ε) / (c₀ - (B + c₀) * δ) := by
  have h := mul_integral_norm_le_integral_inner_add_mul_integral_infDist hJ hc₀ hΩ hB hξ hP hD
  have hA : 0 ≤ B + c₀ := add_nonneg hB₀ hc₀
  have h' := mul_le_mul_of_nonneg_left hDle hA
  rw [le_div_iff₀ (by linarith)]
  nlinarith

end TauCeti.AlmostComplexStructure
