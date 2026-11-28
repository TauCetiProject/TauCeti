/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.MeasureTheory.ApproximateTangentSpace

/-!
# Check: the blow-ups of a subspace

If `P` is a `k`-dimensional subspace of a real inner product space `V` and `x ∈ P`, then for
every `r > 0` and every `φ`,

`r⁻ᵏ ∫_P φ((y − x)/r) dHᵏ(y) = ∫_P φ dHᵏ`

(`integral_dilation_euclideanHausdorffMeasure_restrict`), by the scaling `Hᵏ(rA) = rᵏ Hᵏ(A)`; so
`P` is its own approximate tangent plane in the integral formulation. The exponent matters: with
the normalisation `r^{1−k}` the same integrals are `r ∫_P φ dHᵏ`
(`integral_dilation_euclideanHausdorffMeasure_restrict_smul`), which tend to `0` as `r → 0⁺`
(`tendsto_integral_dilation_euclideanHausdorffMeasure_restrict_smul`).

## References

* L. Simon, *Lectures on Geometric Measure Theory*, §11 (approximate tangent spaces, in the
  integral formulation).
-/

open MeasureTheory Measure Filter Topology Module

public section

namespace TauCeti.Examples.SubspaceBlowUp

variable {V G : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
  [BorelSpace V] [NormedAddCommGroup G] [NormedSpace ℝ G] {P : Submodule ℝ V} {x : V} {r : ℝ}

/-- **The blow-ups of a subspace are the subspace.** For a `k`-dimensional subspace `P`, `x ∈ P`
and `r > 0`, `r⁻ᵏ ∫_P φ((y − x)/r) dHᵏ(y) = ∫_P φ dHᵏ`. -/
theorem integral_dilation_euclideanHausdorffMeasure_restrict (hx : x ∈ P) (hr : 0 < r)
    (φ : V → G) :
    (r ^ finrank ℝ P)⁻¹ • ∫ y in (P : Set V), φ (r⁻¹ • (y - x)) ∂μHE[finrank ℝ P] =
      ∫ y in (P : Set V), φ y ∂μHE[finrank ℝ P] := by
  have h := P.toAffineSubspace.blowUp_euclideanHausdorffMeasure_restrict
    (k := finrank ℝ P) (by simpa using hx) hr
  rw [Submodule.toAffineSubspace_direction, Submodule.coe_toAffineSubspace] at h
  rw [← integral_blowUp hr, h]

/-- With the normalisation `r^{1−k}` instead of `r⁻ᵏ`, the dilated integrals over a subspace are
`r ∫_P φ dHᵏ`. -/
theorem integral_dilation_euclideanHausdorffMeasure_restrict_smul (hx : x ∈ P) (hr : 0 < r)
    (φ : V → G) :
    (r ^ finrank ℝ P)⁻¹ • r • ∫ y in (P : Set V), φ (r⁻¹ • (y - x)) ∂μHE[finrank ℝ P] =
      r • ∫ y in (P : Set V), φ y ∂μHE[finrank ℝ P] := by
  rw [smul_comm, integral_dilation_euclideanHausdorffMeasure_restrict hx hr]

/-- With the normalisation `r^{1−k}` the dilated integrals over a subspace tend to `0`, not to
`∫_P φ dHᵏ`. -/
theorem tendsto_integral_dilation_euclideanHausdorffMeasure_restrict_smul (hx : x ∈ P)
    (φ : V → G) :
    Tendsto (fun r : ℝ ↦
        (r ^ finrank ℝ P)⁻¹ • r • ∫ y in (P : Set V), φ (r⁻¹ • (y - x)) ∂μHE[finrank ℝ P])
      (𝓝[>] 0) (𝓝 0) := by
  have h : Tendsto (fun r : ℝ ↦ r • ∫ y in (P : Set V), φ y ∂μHE[finrank ℝ P]) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous fun r : ℝ ↦ r • ∫ y in (P : Set V), φ y ∂μHE[finrank ℝ P] := by
      fun_prop
    exact (hc.tendsto' 0 0 (zero_smul ℝ _)).mono_left nhdsWithin_le_nhds
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  rw [integral_dilation_euclideanHausdorffMeasure_restrict_smul hx hr]

end TauCeti.Examples.SubspaceBlowUp
