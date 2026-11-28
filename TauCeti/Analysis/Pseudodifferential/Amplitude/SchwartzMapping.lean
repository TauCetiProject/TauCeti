/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TestFunction.Schwartz
public import TauCeti.Analysis.Pseudodifferential.Amplitude.LeftSymbol
public import TauCeti.Analysis.Pseudodifferential.Amplitude.ProperSupport

/-!
# Mapping properties of properly supported amplitudes on Schwartz and test functions

Combining smoothness for input-proper amplitudes
(`TauCeti.Amplitude.HasProperInputSupport.contDiff_quantizeAmplitudeValue`) with compact support
preservation for output-proper amplitudes
(`TauCeti.Amplitude.HasProperOutputSupport.hasCompactSupport_quantizeAmplitudeValue`), properly
supported amplitudes act linearly on test functions `𝓓(ℝⁿ, V) →ₗ[ℂ] 𝓓(ℝⁿ, W)`
(`TauCeti.Amplitude.HasProperSupport.quantizeTestFunction`) and preserve compactly supported
Schwartz functions unconditionally on the target normed spaces.

## Main declarations

* `TauCeti.Amplitude.HasProperSupport.quantizeTestFunction`,
  `TauCeti.Amplitude.HasProperSupport.quantizeTestFunction_apply`.
* `TauCeti.Amplitude.HasProperSupport.exists_schwartzMap_quantizeAmplitudeValue`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1, pp. 68–72.
* M. E. Taylor, *Pseudodifferential Operators*, Princeton University Press, 1981, Chapter II,
  §§1–2.
-/

public section

noncomputable section

open TopologicalSpace
open scoped Distributions SchwartzMap

namespace TauCeti

namespace Amplitude

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {m : ℝ}

/-- **Properly supported amplitudes act linearly on test functions.** Unconditional on completeness
of `V` and `W`: if `a` is properly supported, quantization sends `C_c^∞(ℝⁿ, V)` linearly to
`C_c^∞(ℝⁿ, W)`, allowing direct composition on the canonical test-function space without spatial
cutoffs. -/
def HasProperSupport.quantizeTestFunction {a : Amplitude n V W m} (ha : a.HasProperSupport) :
    𝓓((⊤ : Opens (CoordinateSpace n)), V) →ₗ[ℂ] 𝓓((⊤ : Opens (CoordinateSpace n)), W) where
  toFun u :=
    let su := TestFunction.toSchwartzMapCLM ℂ u
    let hsupp := ha.hasProperOutputSupport.hasCompactSupport_quantizeAmplitudeValue
      (TestFunction.hasCompactSupport_toSchwartzMapCLM u)
    let hsmooth := ha.hasProperInputSupport.contDiff_quantizeAmplitudeValue su
    (hsupp.toSchwartzMap hsmooth).toTestFunction
      (by
        rw [funext (HasCompactSupport.toSchwartzMap_toFun hsupp hsmooth)]
        exact hsupp)
      (Set.subset_univ _)
  map_add' u v := by
    refine TestFunction.ext fun x ↦ ?_
    simp only [FunLike.coe_add, Pi.add_apply, SchwartzMap.coe_toTestFunction]
    rw [HasCompactSupport.toSchwartzMap_toFun, map_add,
      ha.hasProperInputSupport.quantizeAmplitudeValue_add_right,
      HasCompactSupport.toSchwartzMap_toFun, HasCompactSupport.toSchwartzMap_toFun]
  map_smul' c u := by
    refine TestFunction.ext fun x ↦ ?_
    simp only [FunLike.coe_smul, Pi.smul_apply, RingHom.id_apply, SchwartzMap.coe_toTestFunction]
    rw [HasCompactSupport.toSchwartzMap_toFun, map_smul, quantizeAmplitudeValue_smul_right,
      HasCompactSupport.toSchwartzMap_toFun]

/-- Pointwise evaluation of a properly supported amplitude acting on test functions. -/
@[simp]
theorem HasProperSupport.quantizeTestFunction_apply {a : Amplitude n V W m}
    (ha : a.HasProperSupport) (u : 𝓓((⊤ : Opens (CoordinateSpace n)), V))
    (x : CoordinateSpace n) :
    ha.quantizeTestFunction u x =
      quantizeAmplitudeValue a.coefficient (TestFunction.toSchwartzMapCLM ℂ u) x := by
  dsimp [HasProperSupport.quantizeTestFunction]
  rw [SchwartzMap.coe_toTestFunction, HasCompactSupport.toSchwartzMap_toFun]

/-- **Properly supported amplitudes preserve `C_c^∞` inside Schwartz space.** Unconditional on
completeness of `V` and `W`: if `a` is properly supported and `u : 𝓢(ℝⁿ, V)` has compact support,
then `Op(a) u` is the underlying function of a compactly supported Schwartz map `v : 𝓢(ℝⁿ, W)`, so
properly supported amplitude operators can be composed directly without spatial cutoffs. -/
theorem HasProperSupport.exists_schwartzMap_quantizeAmplitudeValue
    {a : Amplitude n V W m} (ha : a.HasProperSupport) {u : 𝓢(CoordinateSpace n, V)}
    (hu : HasCompactSupport (u : CoordinateSpace n → V)) :
    ∃ v : 𝓢(CoordinateSpace n, W),
      (v : CoordinateSpace n → W) = quantizeAmplitudeValue a.coefficient u ∧
      HasCompactSupport (v : CoordinateSpace n → W) := by
  let w := ha.quantizeTestFunction (u.toTestFunction hu (Set.subset_univ _))
  refine ⟨TestFunction.toSchwartzMapCLM ℂ w, funext fun x ↦ ?_,
    TestFunction.hasCompactSupport_toSchwartzMapCLM w⟩
  rw [TestFunction.toSchwartzMapCLM_apply, ha.quantizeTestFunction_apply,
    SchwartzMap.toSchwartzMapCLM_toTestFunction]

end Amplitude

end TauCeti
