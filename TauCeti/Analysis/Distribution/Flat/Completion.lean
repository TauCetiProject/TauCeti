/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Flat.Basic
public import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Completion of real normal currents in flat norm

`TauCeti.FlatNormedCurrent Ω k` is the space of real normal currents, with norm given by
`ContinuousLinearMap.normalFlatMass`. Its wrapper keeps this norm topology distinct from the
compact-convergence topology on distributions. Neither compact support nor integrality is imposed.

The native completion carries a contractive boundary and continuous evaluation at each smooth
test form. Each completed chain still defines a continuous functional on the original LF test
space. Boundary commutes with this comparison and squares to zero. We do not assert injectivity
of the comparison, or identify finite-mass elements of the completion with integral currents.

## References

* H. Federer, *Geometric Measure Theory*, §4.1.12 (real flat chains).
* L. Simon, *Introduction to Geometric Measure Theory*, Chapter 6, §2.
-/

public section

noncomputable section

open Distribution TestFunction TopologicalSpace UniformSpace
open scoped Distributions ENNReal NNReal BoundedContinuousFunction Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Opens E} {k : ℕ}

/-- A real normal current equipped below with flat norm, not the distribution topology.
There is no compact-support condition. -/
structure FlatNormedCurrent (Ω : Opens E) (k : ℕ) where
  /-- The underlying continuous real-linear functional on smooth test forms. -/
  toCurrent : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ
  /-- Both the current and its boundary have finite mass. -/
  isNormal : IsNormal toCurrent

namespace FlatNormedCurrent

@[ext]
theorem ext {T S : FlatNormedCurrent Ω k} (h : T.toCurrent = S.toCurrent) : T = S := by
  cases T
  cases S
  congr

instance : Zero (FlatNormedCurrent Ω k) := ⟨⟨0, isNormal_zero⟩⟩
instance : Add (FlatNormedCurrent Ω k) := ⟨fun T S => ⟨T.toCurrent + S.toCurrent,
  T.isNormal.add S.isNormal⟩⟩
instance : Neg (FlatNormedCurrent Ω k) := ⟨fun T => ⟨-T.toCurrent, T.isNormal.neg⟩⟩
instance : Sub (FlatNormedCurrent Ω k) := ⟨fun T S => ⟨T.toCurrent - S.toCurrent,
  T.isNormal.sub S.isNormal⟩⟩
instance : SMul ℝ (FlatNormedCurrent Ω k) := ⟨fun a T => ⟨a • T.toCurrent, T.isNormal.smul a⟩⟩
instance : SMul ℕ (FlatNormedCurrent Ω k) := ⟨fun a T => ⟨a • T.toCurrent,
  by simpa only [Nat.cast_smul_eq_nsmul] using T.isNormal.smul (a : ℝ)⟩⟩
instance : SMul ℤ (FlatNormedCurrent Ω k) := ⟨fun a T => ⟨a • T.toCurrent,
  by simpa only [Int.cast_smul_eq_zsmul] using T.isNormal.smul (a : ℝ)⟩⟩

@[simp] theorem toCurrent_zero : (0 : FlatNormedCurrent Ω k).toCurrent = 0 := (rfl)
@[simp] theorem toCurrent_add (T S : FlatNormedCurrent Ω k) :
    (T + S).toCurrent = T.toCurrent + S.toCurrent := (rfl)
@[simp] theorem toCurrent_neg (T : FlatNormedCurrent Ω k) :
    (-T).toCurrent = -T.toCurrent := (rfl)
@[simp] theorem toCurrent_sub (T S : FlatNormedCurrent Ω k) :
    (T - S).toCurrent = T.toCurrent - S.toCurrent := (rfl)
@[simp] theorem toCurrent_smul (a : ℝ) (T : FlatNormedCurrent Ω k) :
    (a • T).toCurrent = a • T.toCurrent := (rfl)
@[simp] theorem toCurrent_nsmul (a : ℕ) (T : FlatNormedCurrent Ω k) :
    (a • T).toCurrent = a • T.toCurrent := (rfl)
@[simp] theorem toCurrent_zsmul (a : ℤ) (T : FlatNormedCurrent Ω k) :
    (a • T).toCurrent = a • T.toCurrent := (rfl)

instance : AddCommGroup (FlatNormedCurrent Ω k) :=
  Function.Injective.addCommGroup toCurrent (fun _ _ => ext) toCurrent_zero toCurrent_add
    toCurrent_neg toCurrent_sub (fun T a => toCurrent_nsmul a T)
    (fun T a => toCurrent_zsmul a T)

instance : Module ℝ (FlatNormedCurrent Ω k) :=
  Function.Injective.module ℝ
    ({ toFun := toCurrent, map_zero' := toCurrent_zero, map_add' := toCurrent_add } :
      FlatNormedCurrent Ω k →+ _) (fun _ _ => ext) toCurrent_smul

instance : Norm (FlatNormedCurrent Ω k) := ⟨fun T => T.toCurrent.normalFlatMass.toReal⟩

/-- The flat norm is the real value of the finite extended normal flat mass. -/
theorem norm_def (T : FlatNormedCurrent Ω k) :
    ‖T‖ = T.toCurrent.normalFlatMass.toReal := (rfl)

/-- The extended flat mass of a normal current is finite. -/
theorem normalFlatMass_ne_top (T : FlatNormedCurrent Ω k) :
    T.toCurrent.normalFlatMass ≠ ⊤ :=
  T.toCurrent.normalFlatMass_ne_top_iff.mpr T.isNormal

private theorem norm_smul_eq (a : ℝ) (T : FlatNormedCurrent Ω k) :
    ‖a • T‖ = ‖a‖ * ‖T‖ := by
  simp [norm_def, ENNReal.toReal_mul]

/-- The normal flat mass is a genuine norm on real normal currents. -/
instance : NormedAddCommGroup (FlatNormedCurrent Ω k) :=
  let core : NormedSpace.Core ℝ (FlatNormedCurrent Ω k) := {
    norm_nonneg _ := ENNReal.toReal_nonneg
    norm_smul a T := by exact norm_smul_eq a T
    norm_triangle T S := by
      have h := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
        ⟨T.normalFlatMass_ne_top, S.normalFlatMass_ne_top⟩)
        (T.toCurrent.normalFlatMass_add_le S.toCurrent)
      simpa [norm_def,
        ENNReal.toReal_add T.normalFlatMass_ne_top S.normalFlatMass_ne_top] using h
    norm_eq_zero_iff T := by
      rw [norm_def, ENNReal.toReal_eq_zero_iff]
      simp only [T.normalFlatMass_ne_top, or_false, ContinuousLinearMap.normalFlatMass_eq_zero_iff]
      exact ⟨fun h => ext h, fun h => h ▸ toCurrent_zero⟩ }
  NormedAddCommGroup.ofCore core

instance : NormedSpace ℝ (FlatNormedCurrent Ω k) where
  norm_smul_le a T := by exact (norm_smul_eq a T).le

/-- Flat norm bounds evaluation using the maximum of the sup norms of a test and its derivative. -/
theorem norm_apply_le (T : FlatNormedCurrent Ω k)
    (ω : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] ℝ)) :
    ‖T.toCurrent ω‖ ≤ ‖T‖ * max ‖(ω : E →ᵇ E [⋀^Fin k]→L[ℝ] ℝ)‖
      ‖(extDerivCLM ω : E →ᵇ E [⋀^Fin (k + 1)]→L[ℝ] ℝ)‖ := by
  have h := ENNReal.toReal_mono
    (ENNReal.mul_ne_top T.normalFlatMass_ne_top (by finiteness))
    (T.toCurrent.enorm_apply_le_normalFlatMass_mul ω)
  simpa [norm_def, ENNReal.toReal_mul, ENNReal.toReal_max] using h

/-- Evaluation at a fixed test form is continuous in flat norm. -/
def evalCLM (ω : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] ℝ)) : FlatNormedCurrent Ω k →L[ℝ] ℝ :=
  ({ toFun := fun T => T.toCurrent ω, map_add' := by simp, map_smul' := by simp } :
    FlatNormedCurrent Ω k →ₗ[ℝ] ℝ).mkContinuous
      (max ‖(ω : E →ᵇ E [⋀^Fin k]→L[ℝ] ℝ)‖
        ‖(extDerivCLM ω : E →ᵇ E [⋀^Fin (k + 1)]→L[ℝ] ℝ)‖)
      (fun T => by simpa [mul_comm] using T.norm_apply_le ω)

@[simp]
theorem evalCLM_apply (ω : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] ℝ)) (T : FlatNormedCurrent Ω k) :
    evalCLM ω T = T.toCurrent ω := (rfl)

/-- Boundary is a contraction in flat norm. The ordinary degree-zero boundary is zero and
is not replaced by an augmentation. -/
def boundaryCLM : FlatNormedCurrent Ω (k + 1) →L[ℝ] FlatNormedCurrent Ω k :=
  ({ toFun := fun T => ⟨T.toCurrent ∘L extDerivCLM, T.isNormal.comp_extDerivCLM⟩
     map_add' := fun _ _ => ext (by simp)
     map_smul' := fun _ _ => ext (by simp) } :
    FlatNormedCurrent Ω (k + 1) →ₗ[ℝ] FlatNormedCurrent Ω k).mkContinuous 1 (fun T => by
      simpa [norm_def] using ENNReal.toReal_mono T.normalFlatMass_ne_top
        (T.toCurrent.normalFlatMass_comp_extDerivCLM_le))

@[simp]
theorem toCurrent_boundaryCLM (T : FlatNormedCurrent Ω (k + 1)) :
    (boundaryCLM T).toCurrent = T.toCurrent ∘L extDerivCLM := (rfl)

/-- Taking boundary does not increase the flat norm. -/
theorem norm_boundaryCLM_le (T : FlatNormedCurrent Ω (k + 1)) : ‖boundaryCLM T‖ ≤ ‖T‖ := by
  simpa only [norm_def, toCurrent_boundaryCLM] using
    ENNReal.toReal_mono T.normalFlatMass_ne_top
      T.toCurrent.normalFlatMass_comp_extDerivCLM_le

/-- Two successive boundaries of a real normal current vanish. -/
@[simp]
theorem boundaryCLM_boundaryCLM (T : FlatNormedCurrent Ω (k + 2)) :
    boundaryCLM (boundaryCLM T) = 0 := by
  apply ext
  simp [ContinuousLinearMap.comp_assoc, extDerivCLM_comp_extDerivCLM]

end FlatNormedCurrent

/-- The real normal flat completion, using the native uniform-space completion.
This is not the integral-decomposition flat completion. -/
abbrev RealFlatChain (Ω : Opens E) (k : ℕ) := Completion (FlatNormedCurrent Ω k)

namespace RealFlatChain

/-- Evaluation on a test form, extended continuously from normal currents to flat chains. -/
def evalCLM (ω : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] ℝ)) : RealFlatChain Ω k →L[ℝ] ℝ :=
  (FlatNormedCurrent.evalCLM ω).toLinearMap.extendOfNorm Completion.toComplₗᵢ.toLinearMap

@[simp]
theorem evalCLM_coe (ω : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] ℝ)) (T : FlatNormedCurrent Ω k) :
    evalCLM ω (T : RealFlatChain Ω k) = T.toCurrent ω := by
  apply LinearMap.extendOfNorm_eq Completion.denseRange_coe
  exact ⟨max ‖(ω : E →ᵇ E [⋀^Fin k]→L[ℝ] ℝ)‖
    ‖(extDerivCLM ω : E →ᵇ E [⋀^Fin (k + 1)]→L[ℝ] ℝ)‖,
    fun T => by simpa [mul_comm] using T.norm_apply_le ω⟩

/-- The test-form estimate persists in the completion. -/
theorem norm_evalCLM_le (T : RealFlatChain Ω k)
    (ω : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] ℝ)) :
    ‖evalCLM ω T‖ ≤ ‖T‖ * max ‖(ω : E →ᵇ E [⋀^Fin k]→L[ℝ] ℝ)‖
      ‖(extDerivCLM ω : E →ᵇ E [⋀^Fin (k + 1)]→L[ℝ] ℝ)‖ := by
  induction T using Completion.induction_on with
  | hp => exact isClosed_le (by fun_prop) (by fun_prop)
  | ih T => simpa using T.norm_apply_le ω

/-- Boundary extends to a continuous map between the real flat completions. -/
def boundaryCLM : RealFlatChain Ω (k + 1) →L[ℝ] RealFlatChain Ω k :=
  FlatNormedCurrent.boundaryCLM.completion

@[simp]
theorem boundaryCLM_coe (T : FlatNormedCurrent Ω (k + 1)) :
    boundaryCLM (T : RealFlatChain Ω (k + 1)) =
      (FlatNormedCurrent.boundaryCLM T : RealFlatChain Ω k) :=
  ContinuousLinearMap.completion_apply_coe _ _

/-- Boundary remains a contraction after completion. -/
theorem norm_boundaryCLM_le (T : RealFlatChain Ω (k + 1)) : ‖boundaryCLM T‖ ≤ ‖T‖ := by
  induction T using Completion.induction_on with
  | hp => exact isClosed_le (by fun_prop) (by fun_prop)
  | ih T => simpa using T.norm_boundaryCLM_le

/-- Two successive boundaries of a completed real flat chain vanish. -/
@[simp]
theorem boundaryCLM_boundaryCLM (T : RealFlatChain Ω (k + 2)) :
    boundaryCLM (boundaryCLM T) = 0 := by
  induction T using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) continuous_const
  | ih T => simp

/-- Evaluation of the boundary agrees with evaluation on the exterior derivative. -/
theorem evalCLM_boundaryCLM (T : RealFlatChain Ω (k + 1))
    (ω : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] ℝ)) :
    evalCLM ω (boundaryCLM T) = evalCLM (extDerivCLM ω) T := by
  induction T using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih T => simp

private def evalLinearMap (T : RealFlatChain Ω k) :
    𝓓(Ω, E [⋀^Fin k]→L[ℝ] ℝ) →ₗ[ℝ] ℝ where
  toFun ω := evalCLM ω T
  map_add' ω η := by
    induction T using Completion.induction_on with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih T => simp
  map_smul' a ω := by
    induction T using Completion.induction_on with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih T => simp

/-- A completed real flat chain acts continuously on the original LF space of smooth tests.
This comparison does not assert that the completed chain has finite mass. -/
def toCurrent (T : RealFlatChain Ω k) : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ :=
  { evalLinearMap T with
    cont := by
      apply continuous_of_tendsto_nhds_zero (evalLinearMap T)
      apply squeeze_zero_norm (fun ω => norm_evalCLM_le T ω)
      have h : Continuous (fun ω : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] ℝ) =>
          ‖T‖ * max ‖toBoundedContinuousFunctionCLM ℝ ω‖
            ‖toBoundedContinuousFunctionCLM ℝ (extDerivCLM ω)‖) := by fun_prop
      simpa only [map_zero, norm_zero, max_self, mul_zero,
        toBoundedContinuousFunctionCLM_apply] using
        (h.continuousAt (x := 0)).tendsto }

@[simp]
theorem toCurrent_apply (T : RealFlatChain Ω k) (ω : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] ℝ)) :
    toCurrent T ω = evalCLM ω T := (rfl)

@[simp]
theorem toCurrent_coe (T : FlatNormedCurrent Ω k) :
    toCurrent (T : RealFlatChain Ω k) = T.toCurrent := by
  ext ω
  simp

/-- The comparison from the real flat completion to currents is real-linear. -/
def toCurrentLinearMap : RealFlatChain Ω k →ₗ[ℝ] (𝓓(Ω, E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ) where
  toFun := toCurrent
  map_add' _ _ := by ext ω; simp
  map_smul' _ _ := by ext ω; simp

@[simp]
theorem toCurrentLinearMap_apply (T : RealFlatChain Ω k) :
    toCurrentLinearMap T = toCurrent T := (rfl)

/-- The current comparison intertwines completed boundary with the original current boundary. -/
@[simp]
theorem toCurrent_boundaryCLM (T : RealFlatChain Ω (k + 1)) :
    toCurrent (boundaryCLM T) = toCurrent T ∘L extDerivCLM := by
  ext ω
  exact evalCLM_boundaryCLM T ω

/-- Norm convergence of completed chains implies evaluation convergence on every fixed test.
The topology asserted here is weak test evaluation, not compact convergence on test families. -/
theorem tendsto_toCurrent_apply {ι : Type*} {l : Filter ι} {Ts : ι → RealFlatChain Ω k}
    {T : RealFlatChain Ω k} (h : Filter.Tendsto Ts l (𝓝 T))
    (ω : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] ℝ)) :
    Filter.Tendsto (fun i => toCurrent (Ts i) ω) l (𝓝 (toCurrent T ω)) :=
  (evalCLM ω).continuous.continuousAt.tendsto.comp h

end RealFlatChain
end TauCeti
