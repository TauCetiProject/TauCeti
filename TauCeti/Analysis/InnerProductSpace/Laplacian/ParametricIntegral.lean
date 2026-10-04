/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import TauCeti.Analysis.Calculus.ParametricIntegral
public import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic

/-!
# The Laplacian of an integral over a compact parameter space

For a function `F` that is `C²` on an open set `W ⊆ E × P` of a finite-dimensional real inner
product space `E` times a parameter space `P`, a continuous map `ι : α → P` from a compact space,
and an integrable weight `g` on `α`, the Laplacian in `x` commutes with integration:

`Δ (x ↦ ∫ g(y) F(x, ι y) dμ(y)) = ∫ g(y) Δ (F(·, ι y)) dμ(y)`

on any open set `U` with `U × ι(α) ⊆ W`.  In particular the integral is harmonic there as soon as
each `F(·, ι y)` is, which is how the Poisson integral of integrable boundary data on a sphere is
shown to be harmonic.

## Main declarations

* `TauCeti.laplacian_integral_smul_of_contDiffOn`: the Laplacian of the integral is the integral
  of the Laplacians.
* `TauCeti.harmonicOnNhd_integral_smul_of_contDiffOn`: an integral of harmonic functions against
  an integrable weight is harmonic.
-/

public section

noncomputable section

namespace TauCeti

open InnerProductSpace Laplacian MeasureTheory Filter
open scoped Topology

variable {E P G α : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [CompleteSpace G]
  [TopologicalSpace α] [CompactSpace α] [SecondCountableTopology α] [MeasurableSpace α]
  [OpensMeasurableSpace α] {μ : Measure α} {ι : α → P} {g : α → ℝ} {W : Set (E × P)}
  {U : Set E}

/-- **The Laplacian commutes with integration over a compact parameter space.** If `F` is `C²`
on an open set `W ⊆ E × P` and `U × ι(α) ⊆ W` for an open set `U`, then at every point of `U` the
Laplacian of `x ↦ ∫ g(y) F(x, ι y) dμ(y)` is the integral of the Laplacians of the slices
`F(·, ι y)`. -/
theorem laplacian_integral_smul_of_contDiffOn {F : E × P → G} (hg : Integrable g μ)
    (hι : Continuous ι) (hW : IsOpen W) (hF : ContDiffOn ℝ 2 F W) (hU : IsOpen U)
    (hUW : ∀ x ∈ U, ∀ y, (x, ι y) ∈ W) {x₀ : E} (hx₀ : x₀ ∈ U) :
    Δ (fun x ↦ ∫ y, g y • F (x, ι y) ∂μ) x₀ = ∫ y, g y • Δ (fun x ↦ F (x, ι y)) x₀ ∂μ := by
  set D : E × P → E →L[ℝ] G := fun p ↦ fderiv ℝ (fun x ↦ F (x, p.2)) p.1
  have hD : ContDiffOn ℝ 1 D W := ContDiffOn.fderiv_partial_of_isOpen (m := 1) hF hW
  -- The first derivative of the integral is the integral of the partial derivatives near `x₀`.
  have hfd : fderiv ℝ (fun x ↦ ∫ y, g y • F (x, ι y) ∂μ) =ᶠ[𝓝 x₀]
      fun x ↦ ∫ y, g y • D (x, ι y) ∂μ := by
    filter_upwards [hU.mem_nhds hx₀] with x hx
    exact (hasFDerivAt_integral_smul_of_contDiffOn hg hι hW (hF.of_le (by norm_num))
      (hUW x hx)).fderiv
  -- Differentiating once more gives the integral of the second partial derivatives.
  -- The second partial derivatives are stated without a type ascription: elaborating
  -- `Integrable` at the nested type `E →L[ℝ] E →L[ℝ] G` directly fails to find its
  -- `ContinuousENorm` instance, while instantiating the general lemma does not.
  have hint := integrable_smul_of_continuousOn hg hι
    (ContDiffOn.fderiv_partial_of_isOpen (m := 0) (by simpa using hD) hW).continuousOn
    (hUW x₀ hx₀)
  rw [laplacian_eq_traceL, hfd.fderiv_eq,
    (hasFDerivAt_integral_smul_of_contDiffOn hg hι hW hD (hUW x₀ hx₀)).fderiv,
    ← ContinuousLinearMap.integral_comp_comm _ hint]
  simp only [map_smul, laplacian_eq_traceL, D]

/-- **Integrals of harmonic functions are harmonic.** If `F` is `C²` on an open set
`W ⊆ E × P`, `U × ι(α) ⊆ W` for an open set `U`, and each slice `F(·, ι y)` is harmonic on `U`,
then `x ↦ ∫ g(y) F(x, ι y) dμ(y)` is harmonic on `U` for every integrable weight `g`. -/
theorem harmonicOnNhd_integral_smul_of_contDiffOn {F : E × P → G} (hg : Integrable g μ)
    (hι : Continuous ι) (hW : IsOpen W) (hF : ContDiffOn ℝ 2 F W) (hU : IsOpen U)
    (hUW : ∀ x ∈ U, ∀ y, (x, ι y) ∈ W) (hharm : ∀ y, HarmonicOnNhd (fun x ↦ F (x, ι y)) U) :
    HarmonicOnNhd (fun x ↦ ∫ y, g y • F (x, ι y) ∂μ) U := by
  intro x hx
  refine ⟨(contDiffOn_integral_smul_of_contDiffOn (n := 2) hg hι hW hF hU hUW).contDiffAt
    (hU.mem_nhds hx), ?_⟩
  filter_upwards [hU.mem_nhds hx] with x' hx'
  rw [laplacian_integral_smul_of_contDiffOn hg hι hW hF hU hUW hx']
  have h0 : ∀ y, Δ (fun x ↦ F (x, ι y)) x' = 0 := fun y ↦ (hharm y x' hx').2.self_of_nhds
  simp [h0]

end TauCeti
