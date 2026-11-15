/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.HeatKernel.UniformContinuous
public import TauCeti.Analysis.Semigroups.Basic

/-!
# The heat semigroup on bounded uniformly continuous functions

Convolution with the heat kernel defines a strongly continuous contraction semigroup on the
closed subspace `BoundedContinuousFunction.uniformContinuousSubmodule ℝ E F` of bounded uniformly
continuous functions. Its time-zero value is the identity. This is the supremum-norm setting for
the heat Cauchy problem with uniformly continuous initial data, rather than the `Lᵖ` setting.

`heatSemigroupBUC` bundles the heat regularizations `heatCauchyPotentialBUC` in the semigroup
interface. The semigroup law follows from convolution associativity and the heat-kernel identity;
strong continuity follows from uniform attainment of the initial trace. The general semigroup
API then gives continuity of the orbit at every time, generators and Laplace resolvents.

## References

* K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
  Chapter II, 2.12 (diffusion on bounded uniformly continuous functions).
-/

public section

noncomputable section

namespace TauCeti

open BoundedContinuousFunction Filter MeasureTheory Semigroups Topology
open scoped Convolution NNReal

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The heat semigroup on bounded uniformly continuous functions, with the supremum norm.
At positive times it is convolution with the heat kernel, and at zero it is the identity. -/
def heatSemigroupBUC : ContractionSemigroup (uniformContinuousSubmodule ℝ E F) where
  toFun t := heatCauchyPotentialBUC t
  map_zero' := heatCauchyPotentialBUC_of_nonpos (by simp)
  map_add' s t := by
    ext g : 1
    apply Subtype.ext
    simp only [coe_heatCauchyPotentialBUC, ContinuousLinearMap.comp_apply]
    exact congrArg (fun L : (E →ᵇ F) →L[ℝ] (E →ᵇ F) ↦ L g.val)
      (heatCauchyPotentialBCF_add s.coe_nonneg t.coe_nonneg)
  continuousAt_zero' g := by
    have hright : ContinuousWithinAt (fun t : ℝ ↦ heatCauchyPotentialBUC t g) (Set.Ioi 0) 0 := by
      simpa only [ContinuousWithinAt, heatCauchyPotentialBUC_of_nonpos (le_refl 0),
        ContinuousLinearMap.id_apply] using tendsto_heatCauchyPotentialBUC g
    have hcoe : Tendsto ((↑) : ℝ≥0 → ℝ) (𝓝 0) (𝓝[≥] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨by
        simpa only [NNReal.coe_zero] using NNReal.continuous_coe.tendsto (0 : ℝ≥0),
        .of_forall NNReal.coe_nonneg⟩
    exact (continuousWithinAt_Ioi_iff_Ici.mp hright).tendsto.comp hcoe
  contracting t := norm_heatCauchyPotentialBUC_le t

/-- The nonnegative-time semigroup operator is the existing bounded heat regularization. -/
@[simp]
theorem heatSemigroupBUC_apply (t : ℝ≥0) :
    heatSemigroupBUC (E := E) (F := F) t = heatCauchyPotentialBUC t := (rfl)

/-- The real-time extension of the semigroup agrees with heat regularization, also at negative
times, where both act as the identity. -/
@[simp]
theorem heatSemigroupBUC_realOperator (t : ℝ) :
    (heatSemigroupBUC (E := E) (F := F)).realOperator t = heatCauchyPotentialBUC t := by
  rw [StronglyContinuousSemigroup.realOperator_def,
    ContractionSemigroup.toStronglyContinuousSemigroup_apply, heatSemigroupBUC_apply]
  rcases le_or_gt t 0 with ht | ht
  · simp [Real.toNNReal_of_nonpos ht, heatCauchyPotentialBUC_of_nonpos ht]
  · rw [Real.coe_toNNReal t ht.le]

/-- At positive time the semigroup is pointwise convolution with the heat kernel. -/
theorem coe_heatSemigroupBUC_of_pos {t : ℝ≥0} (ht : 0 < t)
    (g : uniformContinuousSubmodule ℝ E F) :
    ((heatSemigroupBUC t g).val : E → F) = heatKernel t ⋆ (g.val : E → F) := by
  rw [heatSemigroupBUC_apply, coe_heatCauchyPotentialBUC,
    coe_heatCauchyPotentialBCF_of_pos (by exact_mod_cast ht)]

end TauCeti
