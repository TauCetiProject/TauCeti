/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
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
* `TestFunction.laplacianCLM_apply`: the test-function Laplacian agrees pointwise with the
  classical Laplacian.
-/

public section

namespace TauCeti

open InnerProductSpace Laplacian MeasureTheory TopologicalSpace
open scoped Distributions

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E} {u : E → F}

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The directional derivative of a test function, as a test function, is its classical
directional derivative. -/
private lemma coe_lineDerivCLM (φ : 𝓓(Ω, ℝ)) (v : E) :
    ((TestFunction.lineDerivCLM ℝ v φ : 𝓓(Ω, ℝ)) : E → ℝ) =
      fun x ↦ lineDeriv ℝ (φ : E → ℝ) x v :=
  funext fun _ ↦ TestFunction.lineDerivCLM_apply_of_le le_top

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
/-- The iterated line derivative of a smooth test function in a fixed direction is the iterated
Fréchet derivative applied to that direction. -/
private lemma lineDeriv_lineDeriv_testFunction (φ : 𝓓(Ω, F)) (v x : E) :
    lineDeriv ℝ (fun y ↦ lineDeriv ℝ (φ : E → F) y v) x v =
      fderiv ℝ (fun y ↦ fderiv ℝ (φ : E → F) y v) x v := by
  have hφ1 : ∀ y, lineDeriv ℝ (φ : E → F) y v = fderiv ℝ (φ : E → F) y v := fun y ↦
    (φ.contDiff.differentiable (by simp) y).lineDeriv_eq_fderiv
  simp_rw [hφ1]
  exact (((φ.contDiff.fderiv_right (by simp)).clm_apply contDiff_const).differentiable
    one_ne_zero x).lineDeriv_eq_fderiv

/-- **Second-order integration by parts against a test function**, in one direction `v`. For
`u` of class `C²` on the open set `Ω` and a test function `φ` on `Ω`,
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
  rw [coe_lineDerivCLM] at e1
  simp_rw [lineDeriv_lineDeriv_testFunction] at e1
  have hφ1 : ∀ y, lineDeriv ℝ (φ : E → ℝ) y v = fderiv ℝ (φ : E → ℝ) y v := fun y ↦
    (φ.contDiff.differentiable (by simp) y).lineDeriv_eq_fderiv
  simp_rw [hφ1] at e1 e2
  rw [e1, e2, neg_neg]

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
    rw [coe_lineDerivCLM] at this
    simpa only [lineDeriv_lineDeriv_testFunction] using this
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

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
/-- Applying the test-function Laplacian operator agrees pointwise with the classical
Laplacian of the underlying smooth function. -/
@[simp]
theorem _root_.TestFunction.laplacianCLM_apply (φ : 𝓓(Ω, F)) (y : E) :
    (LineDeriv.laplacianCLM ℝ E (𝓓(Ω, F)) φ) y = Δ (φ : E → F) y := by
  simp only [LineDeriv.laplacianCLM]
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  simp only [iteratedFDeriv_two_apply, sum_apply, ContinuousLinearMap.comp_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp only [TestFunction.lineDerivOpCLM_eq_lineDerivCLM]
  rw [TestFunction.lineDerivCLM_apply_of_le le_top]
  have hinner :
      ((TestFunction.lineDerivCLM ℝ ((stdOrthonormalBasis ℝ E) i) φ : 𝓓(Ω, F)) : E → F) =
      fun z => lineDeriv ℝ (φ : E → F) z ((stdOrthonormalBasis ℝ E) i) :=
    funext fun z => TestFunction.lineDerivCLM_apply_of_le le_top
  rw [hinner]
  rw [lineDeriv_lineDeriv_testFunction φ ((stdOrthonormalBasis ℝ E) i) y]
  rw [fderiv_clm_apply
    ((φ.contDiff.fderiv_right (by simp)).differentiable one_ne_zero y)
    (differentiableAt_const _)]
  simp

end TauCeti
