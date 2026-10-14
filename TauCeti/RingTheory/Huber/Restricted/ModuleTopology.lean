/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Restricted.PowerSeries
public import TauCeti.Topology.UniformSpace.UniformConvergence.Limit
public import Mathlib.Topology.Algebra.UniformConvergence

/-!
# Uniform coefficient topology on restricted series with module coefficients

The topology on `M⟨T₁, …, Tₖ⟩` has basic zero neighbourhoods consisting of series all of whose
coefficients lie in a prescribed zero neighbourhood of `M`. This is the topology of uniform
convergence of coefficients. It inherits completeness and Hausdorffness separately from the
coefficient module, and finite-support series are dense. Continuous linear maps act
continuously coefficientwise.

`restrictedMvPowerSeriesModuleUniformSpace` supplies this uniform structure on the existing
carrier `restrictedMvPowerSeriesSubmodule`. It is installed locally with `letI`: the ambient
power-series module already has the product topology, and its subtype topology is a different
topology. The algebraic restricted-series API therefore stays available under either choice.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, §5.6 and Remark 8.29.
-/

public section

open Filter Topology

namespace TauCeti.Huber

variable {k : ℕ} {A M : Type*} [Semiring A] [AddCommMonoid M] [UniformSpace M]
  [ContinuousAdd M] [Module A M] [ContinuousConstSMul A M]

/-- The uniform structure of uniform convergence of coefficients on restricted series with
module coefficients. Use it locally to distinguish it from the product subtype uniformity. -/
@[instance_reducible]
def restrictedMvPowerSeriesModuleUniformSpace (k : ℕ) (A M : Type*) [Semiring A]
    [AddCommMonoid M] [UniformSpace M] [ContinuousAdd M] [Module A M]
    [ContinuousConstSMul A M] : UniformSpace (restrictedMvPowerSeriesSubmodule k A M) :=
  UniformSpace.comap (fun f ↦ UniformFun.ofFun (f.1 : (Fin k →₀ ℕ) → M)) inferInstance

section Uniform

/-- Use uniform convergence of coefficients for the completeness and density results. -/
local instance : UniformSpace (restrictedMvPowerSeriesSubmodule k A M) :=
  restrictedMvPowerSeriesModuleUniformSpace k A M

/-- The coefficient map into the space of uniformly convergent functions induces the
restricted-module uniformity. -/
theorem isUniformInducing_restrictedMvPowerSeriesModule_coefficients :
    IsUniformInducing (fun f : restrictedMvPowerSeriesSubmodule k A M ↦
      UniformFun.ofFun (f.1 : (Fin k →₀ ℕ) → M)) := ⟨rfl⟩

/-- Every coefficient is uniformly continuous for the uniform coefficient structure. -/
theorem uniformContinuous_restrictedMvPowerSeriesModule_coeff (s : Fin k →₀ ℕ) :
    UniformContinuous (fun f : restrictedMvPowerSeriesSubmodule k A M ↦
      (f.1 : (Fin k →₀ ℕ) → M) s) :=
  (UniformFun.uniformContinuous_eval M s).comp
    isUniformInducing_restrictedMvPowerSeriesModule_coefficients.uniformContinuous

/-- Restricted series with coefficients in a Hausdorff module are Hausdorff. -/
theorem t2Space_restrictedMvPowerSeriesModule [T2Space M] :
    T2Space (restrictedMvPowerSeriesSubmodule k A M) :=
  (⟨isUniformInducing_restrictedMvPowerSeriesModule_coefficients.isInducing,
    fun _ _ h ↦ Subtype.ext (UniformFun.ofFun.injective h)⟩ :
      IsEmbedding (fun f : restrictedMvPowerSeriesSubmodule k A M ↦
        UniformFun.ofFun (f.1 : (Fin k →₀ ℕ) → M))).t2Space

/-- Restricted series with coefficients in a complete module are complete for uniform
convergence of coefficients. -/
theorem completeSpace_restrictedMvPowerSeriesModule [CompleteSpace M] :
    CompleteSpace (restrictedMvPowerSeriesSubmodule k A M) := by
  apply isUniformInducing_restrictedMvPowerSeriesModule_coefficients.completeSpace
  have hr : Set.range (fun f : restrictedMvPowerSeriesSubmodule k A M ↦
      UniformFun.ofFun (f.1 : (Fin k →₀ ℕ) → M)) =
      {f : UniformFun (Fin k →₀ ℕ) M | Tendsto (UniformFun.toFun f) cofinite (𝓝 0)} := by
    ext f
    constructor
    · rintro ⟨g, rfl⟩
      exact isRestricted_iff.mp (mem_restrictedMvPowerSeriesSubmodule.mp g.2)
    · intro hf
      exact ⟨⟨UniformFun.toFun f, mem_restrictedMvPowerSeriesSubmodule.mpr
        (isRestricted_iff.mpr hf)⟩, UniformFun.ofFun_toFun f⟩
  rw [hr]
  exact UniformFun.isClosed_setOfPred_tendsto.isComplete

/-- Finite-support series are dense for uniform convergence of coefficients. -/
theorem dense_finite_support_restrictedMvPowerSeriesModule :
    Dense {f : restrictedMvPowerSeriesSubmodule k A M |
      (Function.support (f.1 : (Fin k →₀ ℕ) → M)).Finite} := by
  classical
  refine dense_iff_inter_open.mpr fun U hU ⟨f, hf⟩ ↦ ?_
  let c := fun g : restrictedMvPowerSeriesSubmodule k A M ↦
    UniformFun.ofFun (g.1 : (Fin k →₀ ℕ) → M)
  have hb := (UniformFun.hasBasis_nhds (Fin k →₀ ℕ) M (c f)).comap c
  rw [← isUniformInducing_restrictedMvPowerSeriesModule_coefficients.isInducing.nhds_eq_comap]
    at hb
  obtain ⟨V, hV, hVU⟩ := hb.mem_iff.mp (hU.mem_nhds hf)
  -- Keep the coefficient function at its function type while rewriting indicators.
  let a : (Fin k →₀ ℕ) → M := f.1
  have hfinite : {s | (a s, 0) ∉ V}.Finite :=
    eventually_cofinite.mp (Uniform.tendsto_nhds_left.mp
      (isRestricted_iff.mp (mem_restrictedMvPowerSeriesSubmodule.mp f.2)) hV)
  let S := hfinite.toFinset
  let g := (S : Set (Fin k →₀ ℕ)).indicator a
  have hg : (Function.support g).Finite :=
    S.finite_toSet.subset Set.support_indicator_subset
  let q : restrictedMvPowerSeriesSubmodule k A M :=
    ⟨g, mem_restrictedMvPowerSeriesSubmodule.mpr (isRestricted_of_hasFiniteSupport hg)⟩
  have happrox : ∀ s, (a s, g s) ∈ V := by
    intro s
    by_cases hs : s ∈ S
    · simp only [g, Set.indicator_of_mem hs]
      exact refl_mem_uniformity hV
    · have h : (a s, 0) ∈ V := by
        simpa [S] using hs
      simpa only [g, Set.indicator_of_notMem hs] using h
  -- Membership in the pulled-back entourage is exactly the coefficientwise approximation.
  exact ⟨q, hVU happrox, hg⟩

end Uniform

section Group

variable {k : ℕ} {A M : Type*} [Ring A] [AddCommGroup M] [UniformSpace M]
  [IsUniformAddGroup M] [Module A M] [ContinuousConstSMul A M]

/-- Use uniform convergence of coefficients for the additive-group compatibility results. -/
local instance : UniformSpace (restrictedMvPowerSeriesSubmodule k A M) :=
  restrictedMvPowerSeriesModuleUniformSpace k A M

/-- The uniform coefficient structure is compatible with addition. -/
theorem isUniformAddGroup_restrictedMvPowerSeriesModule :
    IsUniformAddGroup (restrictedMvPowerSeriesSubmodule k A M) := by
  let c : restrictedMvPowerSeriesSubmodule k A M →+ UniformFun (Fin k →₀ ℕ) M :=
    { toFun := fun f ↦ UniformFun.ofFun (f.1 : (Fin k →₀ ℕ) → M)
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  exact IsUniformInducing.isUniformAddGroup c
    isUniformInducing_restrictedMvPowerSeriesModule_coefficients

local instance : IsUniformAddGroup (restrictedMvPowerSeriesSubmodule k A M) :=
  isUniformAddGroup_restrictedMvPowerSeriesModule

/-- A basis of zero neighbourhoods: every coefficient lies in the same zero neighbourhood. -/
theorem hasBasis_nhds_zero_restrictedMvPowerSeriesModule :
    (𝓝 (0 : restrictedMvPowerSeriesSubmodule k A M)).HasBasis
      (fun U : Set M ↦ U ∈ 𝓝 (0 : M))
      (fun U ↦ {f | ∀ s, (f.1 : (Fin k →₀ ℕ) → M) s ∈ U}) := by
  rw [isUniformInducing_restrictedMvPowerSeriesModule_coefficients.isInducing.nhds_eq_comap]
  exact UniformFun.hasBasis_nhds_zero.comap _

/-- Each fixed scalar acts uniformly continuously on the restricted module. -/
theorem uniformContinuousConstSMul_restrictedMvPowerSeriesModule :
    UniformContinuousConstSMul A (restrictedMvPowerSeriesSubmodule k A M) := by
  have : UniformContinuousConstSMul A M :=
    uniformContinuousConstSMul_of_continuousConstSMul A M
  exact isUniformInducing_restrictedMvPowerSeriesModule_coefficients.uniformContinuousConstSMul
    (fun _ _ ↦ rfl)

section Map

variable {N : Type*} [AddCommGroup N] [UniformSpace N] [IsUniformAddGroup N]
  [Module A N] [ContinuousConstSMul A N]

/-- Give the target restricted module the uniform coefficient structure for linear maps. -/
local instance : UniformSpace (restrictedMvPowerSeriesSubmodule k A N) :=
  restrictedMvPowerSeriesModuleUniformSpace k A N

/-- A linear map continuous at zero induces a uniformly continuous coefficientwise map on
restricted series with the uniform coefficient structures. -/
theorem uniformContinuous_restrictedMvPowerSeriesSubmoduleMap {φ : M →ₗ[A] N}
    (hφ : ContinuousAt φ 0) :
    UniformContinuous (restrictedMvPowerSeriesSubmoduleMap (k := k) φ hφ) := by
  rw [(isUniformInducing_restrictedMvPowerSeriesModule_coefficients
    (k := k) (A := A) (M := N)).uniformContinuous_iff]
  have h := (UniformFun.postcomp_uniformContinuous
    (uniformContinuous_of_continuousAt_zero φ.toAddMonoidHom hφ)).comp
      (isUniformInducing_restrictedMvPowerSeriesModule_coefficients
        (k := k) (A := A) (M := M)).uniformContinuous
  convert h using 1
  funext f
  apply UniformFun.toFun.injective
  funext s
  exact coeff_restrictedMvPowerSeriesSubmoduleMap φ hφ f s

end Map

end Group

end TauCeti.Huber
