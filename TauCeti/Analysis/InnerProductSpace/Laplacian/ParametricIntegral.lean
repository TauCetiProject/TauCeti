/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import TauCeti.Analysis.Calculus.ParametricIntegral.Basic
public import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.Calculus.IteratedFDeriv.Prod

/-!
# The Laplacian of an integral over a compact parameter space

For a function `F` that is `C²` on an open set `W ⊆ E × P` of a finite-dimensional real inner
product space `E` times a parameter space `P`, a continuous map `ι : α → P` from a compact space,
and an integrable weight `g` on `α`, the Laplacian in `x` commutes with integration:

`Δ (x ↦ ∫ g(y) F(x, ι y) dμ(y)) = ∫ g(y) Δ (F(·, ι y)) dμ(y)`

at every `x₀` with `{x₀} × ι(α) ⊆ W`.  In particular the integral is harmonic on an open set `U`
with `U × ι(α) ⊆ W` as soon as each `F(·, ι y)` is, which is how the Poisson integral of
integrable boundary data on a sphere is shown to be harmonic.

## Main declarations

* `TauCeti.laplacian_integral_smul_of_contDiffOn`: the Laplacian of the integral is the integral
  of the Laplacians.
* `TauCeti.harmonicOnNhd_integral_smul_of_contDiffOn`: an integral of harmonic functions against
  an integrable weight is harmonic.
* `TauCeti.harmonicOnNhd_integral_mul_of_contDiffOn`: the same for a continuous weight with
  compact support on the parameter space itself, integrated against a measure that is finite on
  compact sets.
-/

public section

noncomputable section

namespace TauCeti

open InnerProductSpace Laplacian MeasureTheory Filter
open scoped Topology

variable {E P G α : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [CompleteSpace G]
  [TopologicalSpace α] [CompactSpace α] [MeasurableSpace α]
  [OpensMeasurableSpace α] {μ : Measure α} {ι : α → P} {g : α → ℝ} {W : Set (E × P)}
  {U : Set E}

/-- **The Laplacian commutes with integration over a compact parameter space.** If `F` is `C²`
on an open set `W ⊆ E × P` and `{x₀} × ι(α) ⊆ W`, then the Laplacian at `x₀` of
`x ↦ ∫ g(y) F(x, ι y) dμ(y)` is the integral of the Laplacians of the slices `F(·, ι y)`. -/
theorem laplacian_integral_smul_of_contDiffOn {F : E × P → G} (hg : Integrable g μ)
    (hι : Continuous ι) (hW : IsOpen W) (hF : ContDiffOn ℝ 2 F W) {x₀ : E}
    (hx₀ : ∀ y, (x₀, ι y) ∈ W) :
    Δ (fun x ↦ ∫ y, g y • F (x, ι y) ∂μ) x₀ = ∫ y, g y • Δ (fun x ↦ F (x, ι y)) x₀ ∂μ := by
  set D : E × P → E →L[ℝ] G := fun p ↦ fderiv ℝ (fun x ↦ F (x, p.2)) p.1
  have hD : ContDiffOn ℝ 1 D W := ContDiffOn.fderiv_partial_of_isOpen (m := 1) hF hW
  -- The first derivative of the integral is the integral of the partial derivatives near `x₀`.
  have hfd : fderiv ℝ (fun x ↦ ∫ y, g y • F (x, ι y) ∂μ) =ᶠ[𝓝 x₀]
      fun x ↦ ∫ y, g y • D (x, ι y) ∂μ := by
    filter_upwards [(isOpen_forall_prodMk_mem hι hW).mem_nhds hx₀] with x hx
    exact (hasFDerivAt_integral_smul_of_contDiffOn hg hι hW (hF.of_le (by norm_num))
      hx).fderiv
  -- Differentiating once more gives the integral of the second partial derivatives.
  -- The second partial derivatives are stated without a type ascription: elaborating
  -- `Integrable` at the nested type `E →L[ℝ] E →L[ℝ] G` directly fails to find its
  -- `ContinuousENorm` instance, while instantiating the general lemma does not.
  have hint := integrable_smul_of_continuousOn hg hι
    (ContDiffOn.fderiv_partial_of_isOpen (m := 0) (by simpa using hD) hW).continuousOn
    hx₀
  rw [laplacian_eq_traceL, hfd.fderiv_eq,
    (hasFDerivAt_integral_smul_of_contDiffOn hg hι hW hD hx₀).fderiv,
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
  refine ⟨(contDiffOn_integral_smul_of_contDiffOn (n := 2) hg hι hW hF hUW).contDiffAt
    (hU.mem_nhds hx), ?_⟩
  filter_upwards [hU.mem_nhds hx] with x' hx'
  rw [laplacian_integral_smul_of_contDiffOn hg hι hW hF (hUW x' hx')]
  have h0 : ∀ y, Δ (fun x ↦ F (x, ι y)) x' = 0 := fun y ↦ (hharm y x' hx').2.self_of_nhds
  simp [h0]

/-- **Integrals of harmonic functions against compactly supported weights.** Let `f` be continuous
with compact support on `P`. If `F` is `C²` on an open set `W ⊆ E × P` containing
`U × tsupport f` for an open set `U`, and each slice `F(·, y)`, `y ∈ tsupport f`, is harmonic on
`U`, then `x ↦ ∫ F(x, y) f(y) dν(y)` is harmonic on `U`. This is how potentials of compactly
supported data against kernels harmonic in one variable are shown to be harmonic. -/
theorem harmonicOnNhd_integral_mul_of_contDiffOn [MeasurableSpace P] [BorelSpace P]
    {ν : Measure P} [IsFiniteMeasureOnCompacts ν] {F : E × P → ℝ} {f : P → ℝ}
    (hf : Continuous f) (hc : HasCompactSupport f) (hW : IsOpen W) (hF : ContDiffOn ℝ 2 F W)
    (hU : IsOpen U) (hUW : ∀ x ∈ U, ∀ y ∈ tsupport f, (x, y) ∈ W)
    (hharm : ∀ y ∈ tsupport f, HarmonicOnNhd (fun x ↦ F (x, y)) U) :
    HarmonicOnNhd (fun x ↦ ∫ y, F (x, y) * f y ∂ν) U := by
  have hKm : MeasurableSet (tsupport f) := (isClosed_tsupport f).measurableSet
  have : CompactSpace (tsupport f) := isCompact_iff_compactSpace.1 hc
  -- The integral over `P` is an integral over the compact parameter space `tsupport f`.
  have hrestr : ∀ x, ∫ y, F (x, y) * f y ∂ν =
      ∫ y : tsupport f, f y • F (x, y) ∂ν.comap Subtype.val := fun x ↦ by
    rw [integral_subtype_comap hKm fun y ↦ f y • F (x, y),
      ← setIntegral_eq_integral_of_forall_compl_eq_zero fun _ hy ↦ by
        rw [image_eq_zero_of_notMem_tsupport (f := f) hy, mul_zero]]
    simp only [smul_eq_mul, mul_comm (f _)]
  have hg : Integrable (fun y : tsupport f ↦ f y) (ν.comap Subtype.val) :=
    (MeasurableEmbedding.subtypeVal hKm).integrable_map_iff.1
      (by rw [map_comap_subtypeVal hKm]; exact hf.continuousOn.integrableOn_compact hc)
  simp_rw [hrestr]
  exact harmonicOnNhd_integral_smul_of_contDiffOn hg continuous_subtypeVal hW hF hU
    (fun x hx y ↦ hUW x hx y y.property) fun y ↦ hharm y y.property

end TauCeti
