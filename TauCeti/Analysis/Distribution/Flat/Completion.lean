/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Flat.Basic
public import Mathlib.Analysis.Normed.Module.Completion

/-!
# The real normal flat completion

Normal currents on an open subset of a real normed space carry the real normal flat norm.
`TauCeti.NormalCurrent` bundles the existing continuous-linear test-form functional with its
normality proof and equips it with this norm, rather than the topology inherited from the dual.
Its native uniform completion is `TauCeti.FlatChain`. Evaluation on a fixed smooth test
form extends continuously to this completion, as does the boundary, which is a contraction.
The resulting evaluation is a continuous-linear test-form functional and agrees with the
original current on normal currents. No injectivity of this comparison is asserted here.

No support condition or integral multiplicity is imposed. In particular this completion is not
an integral flat-chain completion, and its elements are not asserted to be normal currents.

## References

* H. Federer, *Geometric Measure Theory*, §4.1.12 (real flat chains).
-/

public section

noncomputable section

open Distribution TestFunction TopologicalSpace UniformSpace
open scoped Distributions ENNReal BoundedContinuousFunction

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Normal real currents with the real normal flat norm. There is no compact-support condition.
This is a normed version of the existing test-form dual, not a new model of currents. -/
def NormalCurrent (Ω : Opens E) (k : ℕ) : Type _ := ↥(normalCurrentSubmodule Ω k)

namespace NormalCurrent

variable {Ω : Opens E} {k : ℕ}

instance : AddCommGroup (NormalCurrent Ω k) :=
  inferInstanceAs (AddCommGroup (normalCurrentSubmodule Ω k))

instance : Module ℝ (NormalCurrent Ω k) :=
  inferInstanceAs (Module ℝ (normalCurrentSubmodule Ω k))

/-- The underlying current, forgetting only its normality proof. -/
def toCurrent : NormalCurrent Ω k →ₗ[ℝ] (𝓓(Ω, E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ) :=
  (normalCurrentSubmodule Ω k).subtype

/-- Bundle a normal current for the flat norm. -/
def ofCurrent (T : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ) (hT : IsNormal T) :
    NormalCurrent Ω k := ⟨T, mem_normalCurrentSubmodule.2 hT⟩

@[simp] theorem toCurrent_ofCurrent (T : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ)
    (hT : IsNormal T) : (ofCurrent T hT).toCurrent = T := (rfl)

/-- The underlying current is normal. -/
theorem isNormal (T : NormalCurrent Ω k) : IsNormal T.toCurrent :=
  mem_normalCurrentSubmodule.1 T.property

@[ext] theorem ext {T S : NormalCurrent Ω k} (h : T.toCurrent = S.toCurrent) : T = S :=
  Subtype.ext h

@[simp] theorem ofCurrent_toCurrent (T : NormalCurrent Ω k) :
    ofCurrent T.toCurrent T.isNormal = T := (rfl)

instance : Norm (NormalCurrent Ω k) := ⟨fun T => T.toCurrent.normalFlatMass.toReal⟩

/-- The norm is the finite real value of the normal flat mass. -/
theorem norm_eq (T : NormalCurrent Ω k) : ‖T‖ = T.toCurrent.normalFlatMass.toReal := (rfl)

/-- The flat mass is finite on the normal-current space. -/
theorem normalFlatMass_ne_top (T : NormalCurrent Ω k) : T.toCurrent.normalFlatMass ≠ ⊤ :=
  T.toCurrent.normalFlatMass_ne_top_iff.2 T.isNormal

private theorem normCore : NormedSpace.Core ℝ (NormalCurrent Ω k) where
  norm_nonneg _ := ENNReal.toReal_nonneg
  norm_smul a T := by
    simp [norm_eq, ← ofReal_norm]
  norm_triangle T S := by
    exact (ENNReal.toReal_mono (ENNReal.add_ne_top.2
      ⟨T.normalFlatMass_ne_top, S.normalFlatMass_ne_top⟩)
      (T.toCurrent.normalFlatMass_add_le S.toCurrent)).trans_eq
        (ENNReal.toReal_add T.normalFlatMass_ne_top S.normalFlatMass_ne_top)
  norm_eq_zero_iff T := by
    rw [norm_eq, ENNReal.toReal_eq_zero_iff, or_iff_left T.normalFlatMass_ne_top,
      ContinuousLinearMap.normalFlatMass_eq_zero_iff]
    exact ⟨fun h => ext (by simpa using h), fun h => by simp [h]⟩

/-- The metric on normal currents is induced by the real normal flat norm. -/
instance : NormedAddCommGroup (NormalCurrent Ω k) :=
  NormedAddCommGroup.ofCore (𝕜 := ℝ) (by exact normCore (Ω := Ω) (k := k))

instance : NormedSpace ℝ (NormalCurrent Ω k) :=
  NormedSpace.ofCore (by exact normCore (Ω := Ω) (k := k))

/-- Recovering the extended flat mass from the norm does not lose information. -/
@[simp] theorem enorm_eq (T : NormalCurrent Ω k) : ‖T‖ₑ = T.toCurrent.normalFlatMass := by
  rw [← _root_.ofReal_norm, norm_eq, ENNReal.ofReal_toReal T.normalFlatMass_ne_top]

/-- Evaluation is bounded by the flat norm times the larger of the sup norms of `ω` and `dω`. -/
theorem norm_apply_le (T : NormalCurrent Ω k) (ω : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] ℝ)) :
    ‖T.toCurrent ω‖ ≤ ‖T‖ * max ‖(ω : E →ᵇ E [⋀^Fin k]→L[ℝ] ℝ)‖
      ‖(extDerivCLM ω : E →ᵇ E [⋀^Fin (k + 1)]→L[ℝ] ℝ)‖ := by
  apply (ENNReal.ofReal_le_ofReal_iff (by positivity)).1
  rw [ENNReal.ofReal_mul (norm_nonneg T), _root_.ofReal_norm T, enorm_eq]
  simpa only [ENNReal.ofReal_max, _root_.ofReal_norm] using
    T.toCurrent.enorm_apply_le_normalFlatMass_mul ω

/-- Evaluation on a fixed smooth test form is continuous in the flat norm. -/
def evalCLM (ω : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] ℝ)) : NormalCurrent Ω k →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun T => T.toCurrent ω
      map_add' := by intros; simp
      map_smul' := by intros; simp }
    (max ‖(ω : E →ᵇ E [⋀^Fin k]→L[ℝ] ℝ)‖
      ‖(extDerivCLM ω : E →ᵇ E [⋀^Fin (k + 1)]→L[ℝ] ℝ)‖)
    (fun T => by simpa [mul_comm] using T.norm_apply_le ω)

@[simp] theorem evalCLM_apply (ω : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] ℝ)) (T : NormalCurrent Ω k) :
    evalCLM ω T = T.toCurrent ω := (rfl)

/-- Boundary on normal currents, a contraction for the flat norm. Defined only from positive
degrees `k + 1`; degree-zero currents get no boundary, since there are no negative-degree
currents. -/
def boundary : NormalCurrent Ω (k + 1) →L[ℝ] NormalCurrent Ω k :=
  LinearMap.mkContinuous
    { toFun := fun T => ofCurrent (T.toCurrent ∘L extDerivCLM) T.isNormal.comp_extDerivCLM
      map_add' := fun T S => ext (by simp [ContinuousLinearMap.add_comp])
      map_smul' := fun a T => ext (by simp [ContinuousLinearMap.smul_comp]) }
    1 (fun T => by
      simpa [norm_eq] using ENNReal.toReal_mono T.normalFlatMass_ne_top
        T.toCurrent.normalFlatMass_comp_extDerivCLM_le)

@[simp] theorem toCurrent_boundary (T : NormalCurrent Ω (k + 1)) :
    (boundary T).toCurrent = T.toCurrent ∘L extDerivCLM := (rfl)

/-- Boundary does not increase the normal flat norm. -/
theorem norm_boundary_le (T : NormalCurrent Ω (k + 1)) : ‖boundary T‖ ≤ ‖T‖ := by
  have h : ‖(boundary : NormalCurrent Ω (k + 1) →L[ℝ] NormalCurrent Ω k)‖ ≤ 1 :=
    LinearMap.mkContinuous_norm_le _ zero_le_one _
  simpa using boundary.le_of_opNorm_le h T

@[simp] theorem boundary_boundary (T : NormalCurrent Ω (k + 2)) :
    boundary (boundary T) = 0 := by
  apply ext
  simp [ContinuousLinearMap.comp_assoc, extDerivCLM_comp_extDerivCLM]

end NormalCurrent

/-- The native completion of normal real currents in the normal flat norm. It carries the native
complete real normed-space structure. No integrality or normality of completion elements
is asserted. -/
abbrev FlatChain (Ω : Opens E) (k : ℕ) := Completion (NormalCurrent Ω k)

namespace FlatChain

variable {Ω : Opens E} {k : ℕ}

/-- Continuous evaluation of a real flat chain on a fixed smooth test form. -/
def evalCLM (ω : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] ℝ)) : FlatChain Ω k →L[ℝ] ℝ :=
  (NormalCurrent.evalCLM ω).fromCompletion

@[simp] theorem evalCLM_coe (ω : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] ℝ)) (T : NormalCurrent Ω k) :
    evalCLM ω (T : FlatChain Ω k) = T.toCurrent ω := by simp [evalCLM]

/-- Boundary extends to a continuous linear map between the real normal flat completions. -/
def boundary : FlatChain Ω (k + 1) →L[ℝ] FlatChain Ω k :=
  NormalCurrent.boundary.completion

@[simp] theorem boundary_coe (T : NormalCurrent Ω (k + 1)) :
    boundary (T : FlatChain Ω (k + 1)) =
      (NormalCurrent.boundary T : FlatChain Ω k) := by simp [boundary]

/-- The boundary on the completion is still a contraction. -/
theorem norm_boundary_le (T : FlatChain Ω (k + 1)) : ‖boundary T‖ ≤ ‖T‖ := by
  induction T using Completion.induction_on with
  | hp => exact isClosed_le (by fun_prop) (by fun_prop)
  | ih T => simpa using NormalCurrent.norm_boundary_le T

@[simp] theorem boundary_boundary (T : FlatChain Ω (k + 2)) :
    boundary (boundary T) = 0 := by
  induction T using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) continuous_const
  | ih T => simp

/-- The flat evaluation bound survives passage to the completion. -/
theorem norm_evalCLM_le (T : FlatChain Ω k) (ω : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] ℝ)) :
    ‖evalCLM ω T‖ ≤ ‖T‖ * max ‖(ω : E →ᵇ E [⋀^Fin k]→L[ℝ] ℝ)‖
      ‖(extDerivCLM ω : E →ᵇ E [⋀^Fin (k + 1)]→L[ℝ] ℝ)‖ := by
  induction T using Completion.induction_on with
  | hp => exact isClosed_le (by fun_prop) (by fun_prop)
  | ih T => simpa using T.norm_apply_le ω

@[simp] theorem evalCLM_add (ω η : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] ℝ)) (T : FlatChain Ω k) :
    evalCLM (ω + η) T = evalCLM ω T + evalCLM η T := by
  induction T using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih T => simp

@[simp] theorem evalCLM_sub (ω η : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] ℝ)) (T : FlatChain Ω k) :
    evalCLM (ω - η) T = evalCLM ω T - evalCLM η T := by
  induction T using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih T => simp

@[simp] theorem evalCLM_smul (a : ℝ) (ω : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] ℝ))
    (T : FlatChain Ω k) : evalCLM (a • ω) T = a • evalCLM ω T := by
  induction T using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih T => simp

/-- Evaluation of a flat chain is continuous in the test-form topology. -/
theorem continuous_evalCLM_left (T : FlatChain Ω k) : Continuous fun ω => evalCLM ω T := by
  refine continuous_iff_continuousAt.2 fun ω => tendsto_iff_norm_sub_tendsto_zero.2 ?_
  have hc : Continuous fun η : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] ℝ) => ‖T‖ *
      max ‖toBoundedContinuousFunctionCLM ℝ (η - ω)‖
        ‖toBoundedContinuousFunctionCLM ℝ (extDerivCLM (η - ω))‖ := by
    fun_prop
  refine squeeze_zero (fun _ => norm_nonneg _) (fun η => ?_)
    (by simpa only [sub_self, map_zero, norm_zero, max_self, mul_zero] using hc.tendsto ω)
  simpa only [evalCLM_sub, toBoundedContinuousFunctionCLM_apply] using norm_evalCLM_le T (η - ω)

/-- A real flat chain acts continuously and real-linearly on smooth test forms.
This map does not claim that its image has finite mass or finite boundary mass. -/
def toCurrent : FlatChain Ω k →ₗ[ℝ] (𝓓(Ω, E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ) where
  toFun T :=
    { toFun := fun ω => evalCLM ω T
      map_add' ω η := evalCLM_add ω η T
      map_smul' a ω := evalCLM_smul a ω T
      cont := continuous_evalCLM_left T }
  map_add' T S := by ext ω; exact (evalCLM ω).map_add T S
  map_smul' a T := by ext ω; exact (evalCLM ω).map_smul a T

@[simp] theorem toCurrent_apply (T : FlatChain Ω k)
    (ω : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] ℝ)) : T.toCurrent ω = evalCLM ω T := (rfl)

/-- The completion-to-current map agrees with the original normal current on the dense subspace. -/
@[simp] theorem toCurrent_coe (T : NormalCurrent Ω k) :
    toCurrent (T : FlatChain Ω k) = T.toCurrent := by
  ext ω
  simp

/-- The boundary is the transpose of exterior differentiation, with no extra sign. -/
@[simp] theorem toCurrent_boundary (T : FlatChain Ω (k + 1)) :
    (boundary T).toCurrent = T.toCurrent ∘L extDerivCLM := by
  ext ω
  induction T using Completion.induction_on with
  | hp =>
    simp only [toCurrent_apply, ContinuousLinearMap.comp_apply]
    exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih T => simp

/-- Flat convergence in the native completion implies convergence on every fixed test form. -/
theorem tendsto_apply {ι : Type*} {l : Filter ι} {Ts : ι → FlatChain Ω k}
    {T : FlatChain Ω k} (h : Filter.Tendsto Ts l (nhds T))
    (ω : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] ℝ)) :
    Filter.Tendsto (fun i => (Ts i).toCurrent ω) l (nhds (T.toCurrent ω)) :=
  (evalCLM ω).continuous.continuousAt.tendsto.comp h

end FlatChain
end TauCeti
