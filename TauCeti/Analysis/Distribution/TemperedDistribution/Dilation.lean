/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TemperedDistribution
public import TauCeti.Analysis.Distribution.SchwartzSpace.Dilation
public import TauCeti.MeasureTheory.Measure.Haar.DistribChar

/-!
# The dilation action on tempered distributions

Let `𝕜` be a commutative ring acting continuously and `ℝ`-linearly on a real normed space `E`,
for instance `ℝ` or `ℂ` acting on a normed space over it. The units of `𝕜` act on Schwartz
functions by `r(a) f (x) = f (a • x)` (`SchwartzMap.compSMulCLM`). The **contragredient action**
on tempered distributions is the transpose of `r(a⁻¹)`,

`⟨r'(a) T, f⟩ = ⟨T, r(a⁻¹) f⟩`,

a homomorphism from `𝕜ˣ` to the monoid of continuous linear endomorphisms of `𝓢'(E, F)`
(`TemperedDistribution.contragredientSMul`). The inverse makes `r'` a homomorphism rather than an
antihomomorphism, and is the normalization under which, for a quasi-character `ω` of `Fˣ`, the
distribution `f ↦ ∫ f(x) ω(x) d^×x` satisfies `r'(a) T = ω(a) T`: these eigendistributions are
the subject of Tate's local theory.

The action fixes the Dirac distribution at the origin, and moves the Dirac distribution at `x` to
the one at `a⁻¹ • x` (`TemperedDistribution.contragredientSMul_delta`). On the distribution defined
by a Schwartz function `g` and an additive Haar measure it is the dilation `r(a) g`, multiplied by
the factor `distribHaarChar E a` by which `a` scales Haar measure
(`TemperedDistribution.contragredientSMul_toTemperedDistributionCLM`). Unlike the pullback
`TemperedDistribution.compCLM`, which extends composition of functions with a change of variables
and therefore carries the Jacobian, `r'` is the plain transpose.

## Main definitions

* `TemperedDistribution.contragredientSMul`: the action `⟨r'(a) T, f⟩ = ⟨T, r(a⁻¹) f⟩`.

## Main results

* `TemperedDistribution.contragredientSMul_delta`: `r'(a) δₓ = δ_{a⁻¹ • x}`, so `r'(a) δ₀ = δ₀`.
* `TemperedDistribution.contragredientSMul_toTemperedDistributionCLM`: on the distribution of a
  Schwartz function `g`, `r'(a) g = |a| • r(a) g` with `|a| = distribHaarChar E a`.

## References

* J. Tate, *Fourier analysis in number fields and Hecke's zeta-functions*, §2.2.
* S. S. Kudla, *Tate's thesis*, in *An introduction to the Langlands program*, §3.
-/

public noncomputable section

open MeasureTheory
open scoped SchwartzMap

namespace TemperedDistribution

variable {𝕜 E : Type*} [CommRing 𝕜] [NormedAddCommGroup E] [NormedSpace ℝ E] [Module 𝕜 E]
  [ContinuousConstSMul 𝕜 E] [SMulCommClass 𝕜 ℝ E]

section TVS

variable (F : Type*) [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousConstSMul ℂ F]

/-- The **contragredient dilation action** of `𝕜ˣ` on tempered distributions,
`⟨r'(a) T, f⟩ = ⟨T, r(a⁻¹) f⟩`, where `r(a) f = f (a • ·)` is `SchwartzMap.compSMulCLM`. -/
def contragredientSMul : 𝕜ˣ →* (𝓢'(E, F) →L[ℂ] 𝓢'(E, F)) where
  toFun a := PointwiseConvergenceCLM.precomp F (SchwartzMap.compSMulCLM ℂ a⁻¹)
  -- Evaluating a precomposition on the type synonym `→Lₚₜ` is definitional; the
  -- `ContinuousLinearMap` evaluation lemmas do not fire through the synonym.
  map_one' := by
    ext T f
    simp only [inv_one, map_one]
    rfl
  map_mul' a b := by
    ext T f
    simp only [mul_inv_rev, map_mul]
    rfl

variable {F}

/-- The contragredient action evaluates as `⟨r'(a) T, f⟩ = ⟨T, r(a⁻¹) f⟩`. -/
@[simp]
theorem contragredientSMul_apply_apply (a : 𝕜ˣ) (T : 𝓢'(E, F)) (f : 𝓢(E, ℂ)) :
    contragredientSMul F a T f = T (SchwartzMap.compSMulCLM ℂ a⁻¹ f) :=
  (rfl)

end TVS

/-- The contragredient action moves the Dirac distribution at `x` to the one at `a⁻¹ • x`. In
particular it fixes the Dirac distribution at the origin. -/
@[simp]
theorem contragredientSMul_delta (a : 𝕜ˣ) (x : E) :
    contragredientSMul ℂ a (delta x) = delta (a⁻¹ • x) := by
  ext f
  simp

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- On the tempered distribution `f ↦ ∫ f • g ∂μ` of a Schwartz function `g` and an additive Haar
measure `μ`, the contragredient action is dilation of `g` times the module of `a`:
`r'(a) g = distribHaarChar E a • r(a) g`. -/
theorem contragredientSMul_toTemperedDistributionCLM (μ : Measure E) [μ.IsAddHaarMeasure]
    (a : 𝕜ˣ) (g : 𝓢(E, F)) :
    contragredientSMul F a (SchwartzMap.toTemperedDistributionCLM E F μ g) =
      ((distribHaarChar E a : ℝ) : ℂ) •
        SchwartzMap.toTemperedDistributionCLM E F μ (SchwartzMap.compSMulCLM ℂ a g) := by
  ext f
  have h := integral_comp_smul_eq_inv_distribHaarChar_smul μ
    (fun x ↦ f (a⁻¹ • x) • g x) a
  simp only [inv_smul_smul] at h
  rw [smul_apply]
  simp only [contragredientSMul_apply_apply, SchwartzMap.toTemperedDistributionCLM_apply_apply,
    SchwartzMap.compSMulCLM_apply, h, Complex.coe_smul]
  rw [smul_inv_smul₀ (NNReal.coe_ne_zero.2 distribHaarChar_pos.ne')]

end TemperedDistribution
