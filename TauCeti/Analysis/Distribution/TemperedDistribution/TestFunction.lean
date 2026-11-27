/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.Distribution
public import Mathlib.Analysis.Distribution.Support
public import Mathlib.Analysis.Distribution.TemperedDistribution
public import TauCeti.Analysis.Distribution.Restriction
public import TauCeti.Analysis.Distribution.TestFunction.Schwartz
import Mathlib.Analysis.Distribution.SchwartzSpace.CompactSupport
import TauCeti.Analysis.Distribution.SchwartzSpace.Basic
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv

/-!
# Tempered distributions and test functions

Two complex-linear tempered distributions agree if they agree on real-valued smooth,
compactly supported functions, embedded in complex Schwartz space. This connects the real
test functions used to define weak derivatives with the complex tests used in Fourier analysis.
On the Fourier side, they agree if they agree on the band-limited Schwartz functions, those whose
Fourier transform has compact support, since these are the inverse Fourier transforms of the
compactly supported ones.

Since test functions are Schwartz functions (`TestFunction.toSchwartzMapCLM`), a tempered
distribution `u` restricts to a distribution on every open set `Ω`, whose value on a real test
function `φ` is `u φ` (`TemperedDistribution.toDistribution`). On `Ω = E` the restriction loses
nothing (`TemperedDistribution.toDistribution_injective`), so `𝓢'(E, F)` is a space of
distributions, and the local notions defined for distributions on open sets, such as supports,
singular supports and wave front sets, apply to tempered distributions through it.

The density input is Mathlib's `SchwartzMap.dense_hasCompactSupport`.

## Main declarations

* `TemperedDistribution.ext_real`: tempered distributions are determined by their values on real
  compactly supported Schwartz functions.
* `TemperedDistribution.eq_zero_of_forall_hasCompactSupport_fourier`: dually, a tempered
  distribution vanishing on every Schwartz function whose Fourier transform has compact support is
  zero.
* `TemperedDistribution.toDistribution`: the restriction of a tempered distribution to the test
  functions on an open set, as a complex-linear map `𝓢'(E, F) →ₗ[ℂ] 𝓓'(Ω, F)`.
* `TemperedDistribution.toDistribution_injective`: the restriction to all of `E` is injective.
* `TemperedDistribution.restrictCLM_toDistribution`: restricting further to an open subset with
  `Distribution.restrictCLM` gives the restriction to that subset.
* `TemperedDistribution.dsupport_toDistribution_subset`: restriction does not enlarge the support.
* `TemperedDistribution.toDistribution_lineDerivOp`,
  `TemperedDistribution.toDistribution_toTemperedDistribution`: restriction commutes with
  directional derivatives, and sends the tempered distribution of an `Lᵖ` function to its
  distribution.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, Section 7.1.
-/

public section

noncomputable section

namespace TemperedDistribution

open scoped SchwartzMap Distributions LineDeriv
open TopologicalSpace MeasureTheory

section Ext

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [T2Space F]

/-- Real-valued compactly supported Schwartz functions determine a complex-linear tempered
distribution with values in a Hausdorff complex module. The real functions are embedded in
complex Schwartz space by `Complex.ofRealCLM`.
-/
theorem ext_real {u v : 𝓢'(E, F)}
    (h : ∀ φ : 𝓢(E, ℝ), HasCompactSupport φ →
      u (φ.postcompCLM Complex.ofRealCLM) = v (φ.postcompCLM Complex.ofRealCLM)) : u = v := by
  have hreal : ∀ φ : 𝓢(E, ℝ),
      u (φ.postcompCLM Complex.ofRealCLM) = v (φ.postcompCLM Complex.ofRealCLM) := by
    exact (SchwartzMap.dense_hasCompactSupport (E := E) (F := ℝ)).induction h
      (isClosed_eq
        (u.continuous.comp (SchwartzMap.postcompCLM Complex.ofRealCLM).continuous)
        (v.continuous.comp (SchwartzMap.postcompCLM Complex.ofRealCLM).continuous))
  ext φ
  rw [← SchwartzMap.postcompCLM_re_add_I_smul_im φ]
  simp only [map_add, map_smul, hreal]

end Ext

section Fourier

open scoped FourierTransform

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- **Band-limited Schwartz functions determine a tempered distribution.** A tempered distribution
that vanishes on every Schwartz function whose Fourier transform has compact support is zero: its
inverse Fourier transform vanishes on the compactly supported Schwartz functions. -/
theorem eq_zero_of_forall_hasCompactSupport_fourier {u : 𝓢'(E, F)}
    (hu : ∀ φ : 𝓢(E, ℂ), HasCompactSupport ((𝓕 φ : 𝓢(E, ℂ)) : E → ℂ) → u φ = 0) : u = 0 := by
  have h : (𝓕⁻ u : 𝓢'(E, F)) = 0 := ext_real fun φ hφ ↦ by
    rw [fourierInv_apply, zero_apply]
    refine hu _ ?_
    rw [FourierTransform.fourier_fourierInv_eq, SchwartzMap.coe_postcompCLM]
    exact hφ.comp_left Complex.ofRealCLM.map_zero
  calc u = 𝓕 (𝓕⁻ u : 𝓢'(E, F)) := (FourierTransform.fourier_fourierInv_eq u).symm
    _ = 0 := by rw [h, FourierTransform.fourier_zero]

end Fourier

/-! ### Tempered distributions as distributions -/

section ToDistribution

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousConstSMul ℂ F]

variable (Ω : Opens E) in
/-- **A tempered distribution is a distribution.** The restriction of a tempered distribution `u`
to the real test functions on an open set `Ω`, embedded in complex Schwartz space: its value on a
test function `φ` is `u φ` (`TemperedDistribution.toDistribution_apply`). -/
def toDistribution : 𝓢'(E, F) →ₗ[ℂ] 𝓓'(Ω, F) where
  -- `𝓢'(E, F)` is `𝓢(E, ℂ) →L[ℂ] F` with the topology of pointwise convergence, a type synonym
  -- with the same underlying continuous linear maps.
  toFun u := ((u : 𝓢(E, ℂ) →L[ℂ] F).restrictScalars ℝ).comp
    ((TestFunction.toSchwartzMapCLM ℝ).comp (TestFunction.postcompCLM Complex.ofRealCLM))
  map_add' _ _ := (rfl)
  map_smul' _ _ := (rfl)

/-- The value of the restriction of a tempered distribution `u` on a real test function `φ` is the
value of `u` on `φ`, viewed as a complex Schwartz function. -/
@[simp]
theorem toDistribution_apply {Ω : Opens E} (u : 𝓢'(E, F)) (φ : 𝓓(Ω, ℝ)) :
    toDistribution Ω u φ =
      u (TestFunction.toSchwartzMapCLM ℝ (TestFunction.postcompCLM Complex.ofRealCLM φ)) :=
  (rfl)

/-- **Tempered distributions are distributions.** A tempered distribution is determined by its
restriction to the test functions on all of `E`. -/
theorem toDistribution_injective [FiniteDimensional ℝ E] [T2Space F] :
    Function.Injective (toDistribution (⊤ : Opens E) : 𝓢'(E, F) → 𝓓'(⊤, F)) := by
  intro u v h
  refine ext_real fun φ hφ ↦ ?_
  simpa using DFunLike.congr_fun h (φ.toTestFunction hφ (Set.subset_univ _))

/-- Restricting a tempered distribution to `Ω` and then to an open subset `Ω'` is the restriction
to `Ω'`. -/
@[simp]
theorem restrictCLM_toDistribution [ContinuousSMul ℝ F] {Ω Ω' : Opens E} (h : Ω' ≤ Ω)
    (u : 𝓢'(E, F)) :
    (Distribution.restrictCLM (toDistribution Ω u) : 𝓓'(Ω', F)) = toDistribution Ω' u := by
  ext φ
  simp only [Distribution.restrictCLM_apply, toDistribution_apply]
  congr 1
  ext x
  simp [TestFunction.monoCLM_apply, h]

/-- Restriction to `Ω` commutes with directional derivatives. -/
@[simp]
theorem toDistribution_lineDerivOp [ContinuousSMul ℝ F] {Ω : Opens E} (u : 𝓢'(E, F)) (v : E) :
    toDistribution Ω (∂_{v} u) = ∂_{v} (toDistribution Ω u) := by
  ext φ
  simp only [toDistribution_apply, lineDerivOp_apply_apply, Distribution.lineDerivOp_apply_apply,
    map_neg, ← TestFunction.toSchwartzMapCLM_lineDerivOp,
    TestFunction.lineDerivOp_eq_lineDerivCLM ℝ, TestFunction.lineDerivCLM_postcompCLM]

/-- **Functions as distributions.** The restriction of the tempered distribution given by an `Lᵖ`
function `f` is the distribution of `f` on `Ω`. -/
@[simp]
theorem toDistribution_toTemperedDistribution {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℂ G] [CompleteSpace G] [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
    [μ.HasTemperateGrowth] [IsLocallyFiniteMeasure μ] {p : ENNReal} [Fact (1 ≤ p)]
    {Ω : Opens E} (f : Lp G p μ) :
    toDistribution Ω (f : 𝓢'(E, G)) = Distribution.ofFun Ω f μ ⊤ := by
  ext φ
  rw [toDistribution_apply, Lp.toTemperedDistribution_apply,
    Distribution.ofFun_apply (((Lp.memLp f).locallyIntegrable Fact.out).locallyIntegrableOn _)]
  simp [Complex.coe_smul]

/-- The support of the restriction of a tempered distribution to `Ω` lies in the support of the
tempered distribution. -/
theorem dsupport_toDistribution_subset {Ω : Opens E} (u : 𝓢'(E, F)) :
    Distribution.dsupport (toDistribution Ω u) ⊆ Distribution.dsupport u := by
  intro x hx
  contrapose hx
  obtain ⟨s, hs, hso, hxs⟩ := (Distribution.notMem_dsupport_iff x).1 hx
  refine (Distribution.notMem_dsupport_iff x).2 ⟨s, fun φ hφ ↦ ?_, hso, hxs⟩
  rw [toDistribution_apply]
  refine hs _ (Set.Subset.trans ?_ hφ)
  rw [TestFunction.coe_toSchwartzMapCLM, TestFunction.postcompCLM_apply]
  exact tsupport_comp_subset (map_zero Complex.ofRealCLM) (φ : E → ℝ)

end ToDistribution

end TemperedDistribution
