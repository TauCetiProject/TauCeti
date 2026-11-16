/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.Iterated
public import TauCeti.Topology.ContinuousMap.Bounded.UniformContinuous
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import TauCeti.Analysis.Holder.MeanValue
import TauCeti.Analysis.PDE.HeatKernel.UniformContinuous

/-!
# Bounded `C^{k+1,α}` maps are bounded and uniformly continuous

A bounded `C^{k+1,α}` map is Lipschitz (`TauCeti.CkHolderSpace.lipschitzWith`), so forgetting its
derivatives lands in the closed subspace `BUC(E, F)` of bounded uniformly continuous functions.
This file records that inclusion as the continuous linear map `TauCeti.CkHolderSpace.toBUC`.

On a finite-dimensional real inner product space, with `α ≤ 1` and complete target, the inclusion
has dense range (`TauCeti.CkHolderSpace.denseRange_toBUC`): heat regularizations of a bounded
uniformly continuous function are smooth with bounded derivatives of every order
(`TauCeti.exists_contDiff_bounded_derivatives_approximation`), and a bounded derivative field
with a bounded derivative is `α`-Hölder. This is the density used to extend solution operators of
parabolic problems from smooth to uniformly continuous initial data.
-/

public section
noncomputable section

namespace TauCeti.CkHolderSpace

open BoundedContinuousFunction
open scoped NNReal ContDiff

variable {k : ℕ} {α : ℝ≥0} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The inclusion of `C_b^{k+1,α}(E, F)` in the bounded uniformly continuous functions
`BUC(E, F)`, forgetting the derivatives. -/
def toBUC : CkHolderSpace (k + 1) α E F →L[ℝ] uniformContinuousSubmodule ℝ E F :=
  toBoundedContinuousFunctionCLM.codRestrict (uniformContinuousSubmodule ℝ E F).toSubmodule
    fun f ↦ (mem_uniformContinuousSubmodule _).2 <| by
      simpa using f.lipschitzWith.uniformContinuous

/-- The inclusion `toBUC` does not change values. -/
@[simp]
theorem toBUC_apply (f : CkHolderSpace (k + 1) α E F) (x : E) :
    ((toBUC f : uniformContinuousSubmodule ℝ E F) : E →ᵇ F) x = f x := by
  rw [toBUC, ContinuousLinearMap.coe_codRestrict_apply, toBoundedContinuousFunctionCLM_apply,
    coe_toBoundedContinuousFunction]

section Density

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace F]

/-- **Density of `C_b^{k+1,α}` in `BUC`.** On a finite-dimensional real inner product space, every
bounded uniformly continuous function is a uniform limit of bounded `C^{k+1,α}` functions, for
`α ≤ 1`. -/
theorem denseRange_toBUC (hα : α ≤ 1) :
    DenseRange (toBUC (k := k) (α := α) (E := E) (F := F)) := by
  intro w
  refine Metric.mem_closure_iff.2 fun ε hε ↦ ?_
  obtain ⟨h, hsmooth, hdist, -, hbdd⟩ := exists_contDiff_bounded_derivatives_approximation w hε
  choose C hC using hbdd
  have hle (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ := mod_cast le_top
  have hholder : MemHolder α (_root_.iteratedFDeriv ℝ (k + 1) (h.val : E → F)) :=
    ⟨_, holderWith_of_norm_le_of_norm_fderiv_le (N₀ := (C (k + 1)).toNNReal)
      (N₁ := (C (k + 2)).toNNReal) hα
      ((hsmooth.of_le (hle (k + 2))).differentiable_iteratedFDeriv
        (mod_cast (by omega : k + 1 < k + 2)))
      (fun x ↦ (hC (k + 1) x).trans (Real.le_coe_toNNReal _))
      (fun x ↦ by
        rw [norm_fderiv_iteratedFDeriv]
        exact (hC (k + 2) x).trans (Real.le_coe_toNNReal _))⟩
  have hk : ContDiff ℝ (k + 1 : ℕ) (h.val : E → F) := hsmooth.of_le (hle (k + 1))
  refine ⟨toBUC (ofContDiff (h.val : E → F) hk (fun i _ ↦ ⟨C i, hC i⟩) hholder), ⟨_, rfl⟩, ?_⟩
  have heq : toBUC (ofContDiff (h.val : E → F) hk (fun i _ ↦ ⟨C i, hC i⟩) hholder) = h :=
    Subtype.ext <| BoundedContinuousFunction.ext fun x ↦ by
      rw [toBUC_apply, coe_ofContDiff]
  rw [heq, dist_comm, dist_eq_norm]
  exact hdist

end Density

end TauCeti.CkHolderSpace
