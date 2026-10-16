/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic

/-!
# The Laplacian against test functions

For a `C²` function `u` on an open set `Ω` of a finite-dimensional real inner product space and a
test function `φ ∈ 𝓓(Ω)`, integrating by parts twice in each coordinate direction gives Green's
second identity in the boundary-free form

`∫ Δφ • u ∂μ = ∫ φ • Δu ∂μ`,

for any additive Haar measure `μ`: the classical Laplacian of a `C²` function is its distributional
Laplacian on `Ω`. In particular a function harmonic on `Ω` is *weakly harmonic*: `∫ Δφ • u = 0` for
every test function `φ` on `Ω`. This is the form in which harmonicity enters integral arguments
such as the mean-value property, where the test functions are radial.

The two integrations by parts are the defining identities of the weak derivative
`TauCeti.HasWeakLineDerivOn`, applied to `u` and to its first directional derivative, both of
which are classical derivatives and hence weak ones
(`TauCeti.hasWeakLineDerivOn_of_hasLineDerivAt`). No boundary term appears because the test
function is compactly supported in `Ω`, and no regularity of `∂Ω` is used.

## Main declarations

* `ContDiffOn.integral_fderiv_fderiv_smul_eq_integral_smul_fderiv_fderiv`: second-order
  integration by parts in one direction, `∫ ∂ᵥ∂ᵥφ • u = ∫ φ • ∂ᵥ∂ᵥu`.
* `ContDiffOn.integral_laplacian_smul_eq_integral_smul_laplacian`: Green's second identity
  against a test function, `∫ Δφ • u = ∫ φ • Δu`.
* `InnerProductSpace.HarmonicOnNhd.integral_laplacian_smul_eq_zero`: a harmonic function is
  weakly harmonic.
* `MeasureTheory.LocallyIntegrable.integral_laplacian_mul_eq_neg_integral_sum`: for a locally
  integrable `K` with a locally integrable gradient `K'` in the integration-by-parts sense,
  `∫ Δf · K = -∫ K' · ∇f`
  for `C²` functions `f` with compact support. This is the first half of the computation of the
  distributional Laplacian of a fundamental solution.
* `TauCeti.HasWeakFDerivOn.integral_laplacian_smul_eq_neg_integral_inner`: for `u` with weak
  gradient `g` on `Ω`, `∫ Δφ • u = -∫ ⟪∇φ, g⟫` for every test function `φ` on `Ω`.
-/

public section

namespace TauCeti

open InnerProductSpace Laplacian MeasureTheory TopologicalSpace
open scoped Distributions Gradient

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F] {Ω : Opens E} {u : E → F}

section NormedSpace

variable [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

/-- **Second-order integration by parts against a test function**, in one direction `v`. For
`u` of class `C²` on the open set `Ω` in a finite-dimensional real normed space and a test
function `φ` on `Ω`,
`∫ ∂ᵥ∂ᵥφ • u = ∫ φ • ∂ᵥ∂ᵥu`. -/
theorem _root_.ContDiffOn.integral_fderiv_fderiv_smul_eq_integral_smul_fderiv_fderiv
    (hu : ContDiffOn ℝ 2 u Ω) (φ : 𝓓(Ω, ℝ)) (v : E) :
    ∫ x, fderiv ℝ (fun y ↦ fderiv ℝ (φ : E → ℝ) y v) x v • u x ∂μ =
      ∫ x, (φ : E → ℝ) x • fderiv ℝ (fun y ↦ fderiv ℝ u y v) x v ∂μ := by
  have hΩ : IsOpen (Ω : Set E) := Ω.isOpen
  set g : E → F := fun y ↦ fderiv ℝ u y v with _
  have hu1 : ContDiffOn ℝ 1 (fderiv ℝ u) Ω := hu.fderiv_of_isOpen hΩ (by norm_num)
  have hg : ContDiffOn ℝ 1 g Ω := hu1.clm_apply contDiffOn_const
  have hu_loc : LocallyIntegrableOn u Ω μ := hu.continuousOn.locallyIntegrableOn hΩ.measurableSet
  have hg_loc : LocallyIntegrableOn g Ω μ := hg.continuousOn.locallyIntegrableOn hΩ.measurableSet
  have hg'_loc : LocallyIntegrableOn (fun x ↦ fderiv ℝ g x v) Ω μ :=
    (hu.continuousOn_fderiv_fderiv_apply hΩ v).locallyIntegrableOn hΩ.measurableSet
  -- Both `u` and `∂ᵥu` are classically, hence weakly, differentiable on `Ω`.
  have h1 : HasWeakLineDerivOn μ Ω u g v :=
    hasWeakLineDerivOn_of_hasLineDerivAt hu_loc hg_loc fun x hx ↦
      ((hu.differentiableOn (by norm_num)).differentiableAt
        (hΩ.mem_nhds hx)).hasFDerivAt.hasLineDerivAt v
  have h2 : HasWeakLineDerivOn μ Ω g (fun x ↦ fderiv ℝ g x v) v :=
    hasWeakLineDerivOn_of_hasLineDerivAt hg_loc hg'_loc fun x hx ↦
      ((hg.differentiableOn one_ne_zero).differentiableAt
        (hΩ.mem_nhds hx)).hasFDerivAt.hasLineDerivAt v
  have e1 := h1.integral_lineDeriv_smul_eq_neg_integral_smul (TestFunction.lineDerivCLM ℝ v φ)
  have e2 := h2.integral_lineDeriv_smul_eq_neg_integral_smul φ
  rw [TestFunction.coe_lineDerivCLM] at e1
  simp_rw [TestFunction.lineDeriv_lineDeriv_eq_fderiv_fderiv] at e1
  have hφ1 : ∀ y, lineDeriv ℝ (φ : E → ℝ) y v = fderiv ℝ (φ : E → ℝ) y v := fun y ↦
    (φ.contDiff.differentiable (by simp) y).lineDeriv_eq_fderiv
  simp_rw [hφ1] at e1 e2
  rw [e1, e2, neg_neg]

end NormedSpace

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

/-- **Green's second identity against a test function.** For `u` of class `C²` on the open set
`Ω` and a test function `φ` on `Ω`, `∫ Δφ • u ∂μ = ∫ φ • Δu ∂μ`: the classical Laplacian of a `C²`
function is its distributional Laplacian. -/
theorem _root_.ContDiffOn.integral_laplacian_smul_eq_integral_smul_laplacian
    (hu : ContDiffOn ℝ 2 u Ω) (φ : 𝓓(Ω, ℝ)) :
    ∫ x, Δ (φ : E → ℝ) x • u x ∂μ = ∫ x, (φ : E → ℝ) x • Δ u x ∂μ := by
  have hΩ : IsOpen (Ω : Set E) := Ω.isOpen
  set b := stdOrthonormalBasis ℝ E
  have hφ1 : ContDiff ℝ 1 (fderiv ℝ (φ : E → ℝ)) := φ.contDiff.fderiv_right (by simp)
  have hu1 : ContDiffOn ℝ 1 (fderiv ℝ u) Ω := hu.fderiv_of_isOpen hΩ (by norm_num)
  have hu_loc : LocallyIntegrableOn u Ω μ := hu.continuousOn.locallyIntegrableOn hΩ.measurableSet
  -- The Laplacians as sums of iterated directional derivatives over an orthonormal basis.
  have hΔφ : ∀ x, Δ (φ : E → ℝ) x =
      ∑ i, fderiv ℝ (fun y ↦ fderiv ℝ (φ : E → ℝ) y (b i)) x (b i) := fun x ↦
    laplacian_eq_sum_fderiv_fderiv_apply b (hφ1.differentiable one_ne_zero x)
  have hΔu : ∀ x ∈ (Ω : Set E), Δ u x =
      ∑ i, fderiv ℝ (fun y ↦ fderiv ℝ u y (b i)) x (b i) := fun x hx ↦
    laplacian_eq_sum_fderiv_fderiv_apply b
      ((hu1.differentiableOn one_ne_zero).differentiableAt (hΩ.mem_nhds hx))
  -- Integrability of the summands.
  have hint₁ : ∀ i,
      Integrable (fun x ↦ fderiv ℝ (fun y ↦ fderiv ℝ (φ : E → ℝ) y (b i)) x (b i) • u x) μ := by
    intro i
    have := integrable_lineDeriv_smul_of_locallyIntegrableOn hu_loc
      (TestFunction.lineDerivCLM ℝ (b i) φ) (b i)
    rw [TestFunction.coe_lineDerivCLM] at this
    simpa only [TestFunction.lineDeriv_lineDeriv_eq_fderiv_fderiv] using this
  have hint₂ : ∀ i,
      Integrable (fun x ↦ (φ : E → ℝ) x • fderiv ℝ (fun y ↦ fderiv ℝ u y (b i)) x (b i)) μ :=
    fun i ↦ integrable_smul_of_locallyIntegrableOn
      ((hu.continuousOn_fderiv_fderiv_apply hΩ (b i)).locallyIntegrableOn hΩ.measurableSet) φ
  calc ∫ x, Δ (φ : E → ℝ) x • u x ∂μ
      = ∑ i, ∫ x, fderiv ℝ (fun y ↦ fderiv ℝ (φ : E → ℝ) y (b i)) x (b i) • u x ∂μ := by
        simp_rw [hΔφ, Finset.sum_smul]
        exact integral_finsetSum _ fun i _ ↦ hint₁ i
    _ = ∑ i, ∫ x, (φ : E → ℝ) x • fderiv ℝ (fun y ↦ fderiv ℝ u y (b i)) x (b i) ∂μ :=
        Finset.sum_congr rfl fun i _ ↦
          hu.integral_fderiv_fderiv_smul_eq_integral_smul_fderiv_fderiv φ (b i)
    _ = ∫ x, (φ : E → ℝ) x • Δ u x ∂μ := by
        rw [← integral_finsetSum _ fun i _ ↦ hint₂ i]
        refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
        beta_reduce
        by_cases hx : x ∈ (Ω : Set E)
        · rw [hΔu x hx, Finset.smul_sum]
        · simp [φ.zero_on_compl hx]

/-- **A harmonic function is weakly harmonic.** If `u` is harmonic on the open set `Ω`, then
`∫ Δφ • u ∂μ = 0` for every test function `φ` on `Ω`. -/
theorem _root_.InnerProductSpace.HarmonicOnNhd.integral_laplacian_smul_eq_zero
    (hu : HarmonicOnNhd u Ω) (φ : 𝓓(Ω, ℝ)) :
    ∫ x, Δ (φ : E → ℝ) x • u x ∂μ = 0 := by
  rw [hu.contDiffOn.integral_laplacian_smul_eq_integral_smul_laplacian φ]
  refine integral_eq_zero_of_ae (ae_of_all _ fun x ↦ ?_)
  beta_reduce
  by_cases hx : x ∈ (Ω : Set E)
  · rw [(hu x hx).2.eq_of_nhds, Pi.zero_apply, smul_zero]
  · simp [φ.zero_on_compl hx]

omit [CompleteSpace F] [μ.IsAddHaarMeasure] [BorelSpace E] in
/-- **Integration by parts against a kernel with an integrable gradient.** Let `K` and `K'` be
locally integrable and satisfy `∫ K ∂ᵥg = -∫ (K' · v) g` for every `C¹` function `g` with compact
support. Then for every `C²` function `f` with compact support and every orthonormal basis `b`,
`∫ Δf · K = -∫ ∑ᵢ K'(bᵢ) ∂_{bᵢ}f`. -/
theorem _root_.MeasureTheory.LocallyIntegrable.integral_laplacian_mul_eq_neg_integral_sum
    [OpensMeasurableSpace E]
    {K : E → ℝ} {K' : E → E →L[ℝ] ℝ}
    (hK : LocallyIntegrable K μ) (hK' : LocallyIntegrable K' μ)
    (hibp : ∀ g : E → ℝ, ContDiff ℝ 1 g → HasCompactSupport g → ∀ v,
      ∫ x, K x * fderiv ℝ g x v ∂μ = -∫ x, K' x v * g x ∂μ)
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) :
    ∫ x, Δ f x * K x ∂μ = -∫ x, ∑ i, K' x (b i) * fderiv ℝ f x (b i) ∂μ := by
  have hf1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hgi : ∀ i, ContDiff ℝ 1 fun y ↦ fderiv ℝ f y (b i) := fun i ↦
    hf1.clm_apply contDiff_const
  have hci : ∀ i, HasCompactSupport fun y ↦ fderiv ℝ f y (b i) := fun i ↦
    (hc.fderiv ℝ).comp_left (g := fun L : E →L[ℝ] ℝ ↦ L (b i)) rfl
  -- The Laplacian as a sum of iterated directional derivatives.
  have hΔ : ∀ x, Δ f x = ∑ i, fderiv ℝ (fun y ↦ fderiv ℝ f y (b i)) x (b i) := fun x ↦
    laplacian_eq_sum_fderiv_fderiv_apply b ((hf1.differentiable one_ne_zero) x)
  simp_rw [hΔ, Finset.sum_mul]
  rw [integral_finsetSum _ fun i _ ↦ ?_, integral_finsetSum _ fun i _ ↦ ?_,
    ← Finset.sum_neg_distrib]
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← hibp _ (hgi i) (hci i) (b i)]
    simp_rw [mul_comm]
  · simpa [mul_comm] using (hK'.integrable_smul_left_of_hasCompactSupport (hgi i).continuous
      (hci i)).apply_continuousLinearMap (b i)
  · simpa [mul_comm] using hK.integrable_smul_right_of_hasCompactSupport
      (((hgi i).continuous_fderiv one_ne_zero).clm_apply continuous_const)
      (((hci i).fderiv ℝ).comp_left (g := fun L : E →L[ℝ] ℝ ↦ L (b i)) rfl)

omit [μ.IsAddHaarMeasure] [BorelSpace E] in
/-- **The Laplacian identity for a weak gradient relative to `μ`.** If `u` has weak gradient
`g` on `Ω`, then for every test function `φ` on `Ω`, `∫ Δφ • u ∂μ = -∫ ⟪∇φ, g⟫ ∂μ`.
For an additive Haar measure, this gives the distributional Laplacian of `u`: it vanishes
precisely when the gradient pairing vanishes for all test functions. -/
theorem HasWeakFDerivOn.integral_laplacian_smul_eq_neg_integral_inner [OpensMeasurableSpace E]
    {u : E → ℝ} {g : E → E}
    (h : HasWeakFDerivOn μ Ω u fun x ↦ innerSL ℝ (g x)) (φ : 𝓓(Ω, ℝ)) :
    ∫ x, Δ (φ : E → ℝ) x • u x ∂μ = -∫ x, ⟪∇ (φ : E → ℝ) x, g x⟫_ℝ ∂μ := by
  set b := stdOrthonormalBasis ℝ E
  have hφ1 : ContDiff ℝ 1 (fderiv ℝ (φ : E → ℝ)) := φ.contDiff.fderiv_right (by simp)
  have hline : ∀ y v, lineDeriv ℝ (φ : E → ℝ) y v = fderiv ℝ (φ : E → ℝ) y v := fun y v ↦
    (φ.contDiff.differentiable (by simp) y).lineDeriv_eq_fderiv
  -- The Laplacian as a sum of iterated directional derivatives over an orthonormal basis.
  have hΔφ : ∀ x, Δ (φ : E → ℝ) x =
      ∑ i, fderiv ℝ (fun y ↦ fderiv ℝ (φ : E → ℝ) y (b i)) x (b i) := fun x ↦
    laplacian_eq_sum_fderiv_fderiv_apply b (hφ1.differentiable one_ne_zero x)
  -- In each direction, the weak derivative identity against the test function `∂ᵢφ`.
  have hdir : ∀ i, ∫ x, fderiv ℝ (fun y ↦ fderiv ℝ (φ : E → ℝ) y (b i)) x (b i) • u x ∂μ =
      -∫ x, fderiv ℝ (φ : E → ℝ) x (b i) • ⟪g x, b i⟫_ℝ ∂μ := fun i ↦ by
    have e := (h.hasWeakLineDerivOn (b i)).integral_lineDeriv_smul_eq_neg_integral_smul
      (TestFunction.lineDerivCLM ℝ (b i) φ)
    rw [TestFunction.coe_lineDerivCLM] at e
    simp_rw [TestFunction.lineDeriv_lineDeriv_eq_fderiv_fderiv, hline, innerSL_apply_apply] at e
    exact e
  have hint₁ : ∀ i,
      Integrable (fun x ↦ fderiv ℝ (fun y ↦ fderiv ℝ (φ : E → ℝ) y (b i)) x (b i) • u x) μ := by
    intro i
    have := integrable_lineDeriv_smul_of_locallyIntegrableOn h.locallyIntegrableOn
      (TestFunction.lineDerivCLM ℝ (b i) φ) (b i)
    rw [TestFunction.coe_lineDerivCLM] at this
    simpa only [TestFunction.lineDeriv_lineDeriv_eq_fderiv_fderiv] using this
  have hint₂ : ∀ i,
      Integrable (fun x ↦ fderiv ℝ (φ : E → ℝ) x (b i) • ⟪g x, b i⟫_ℝ) μ := by
    intro i
    have := integrable_smul_of_locallyIntegrableOn
      (h.hasWeakLineDerivOn (b i)).locallyIntegrableOn_deriv (TestFunction.lineDerivCLM ℝ (b i) φ)
    rw [TestFunction.coe_lineDerivCLM] at this
    simpa only [hline, innerSL_apply_apply] using this
  calc ∫ x, Δ (φ : E → ℝ) x • u x ∂μ
      = ∑ i, ∫ x, fderiv ℝ (fun y ↦ fderiv ℝ (φ : E → ℝ) y (b i)) x (b i) • u x ∂μ := by
        simp_rw [hΔφ, Finset.sum_smul]
        exact integral_finsetSum _ fun i _ ↦ hint₁ i
    _ = -∑ i, ∫ x, fderiv ℝ (φ : E → ℝ) x (b i) • ⟪g x, b i⟫_ℝ ∂μ := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun i _ ↦ hdir i
    _ = -∫ x, ⟪∇ (φ : E → ℝ) x, g x⟫_ℝ ∂μ := by
        rw [← integral_finsetSum _ fun i _ ↦ hint₂ i]
        congr 1
        refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
        simp only [smul_eq_mul, ← toDual_gradient, toDual_apply_apply]
        rw [← b.sum_inner_mul_inner]
        exact Finset.sum_congr rfl fun i _ ↦ by rw [real_inner_comm (g x)]

end TauCeti
