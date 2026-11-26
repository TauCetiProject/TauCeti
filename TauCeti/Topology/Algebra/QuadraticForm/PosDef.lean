/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import TauCeti.Analysis.Matrix.PosDef

/-!
# Positive definiteness of a family of bilinear forms is an open condition

A family of real bilinear forms on a module with a finite basis, whose entries on the basis are
continuous at `x₀` and which is positive definite at `x₀`, stays positive definite near `x₀`.
The Gram matrices of the family move continuously, so this is
`TauCeti.isOpen_setOfPred_re_dotProduct_pos` read through the basis.

## Main results

* `LinearMap.BilinForm.eventually_posDef_of_continuousAt`: positive definiteness of a family of
  bilinear forms with entries continuous at `x₀` persists near `x₀`.
-/

public section

open Filter Matrix Topology

namespace LinearMap.BilinForm

/-- **Positive definiteness is an open condition.** Let `B x` be bilinear forms on a real module
`E` with a finite basis `b`, depending on a parameter `x`, whose entries `B x (b i) (b j)` are
continuous at `x₀`. If `B x₀` is positive definite, then so is `B x` for every `x` near `x₀`. -/
theorem eventually_posDef_of_continuousAt {X ι E : Type*} [TopologicalSpace X] [Finite ι]
    [AddCommGroup E] [Module ℝ E] (b : Module.Basis ι ℝ E)
    {B : X → LinearMap.BilinForm ℝ E} {x₀ : X}
    (hB : ∀ i j, ContinuousAt (fun x ↦ B x (b i) (b j)) x₀)
    (h₀ : (B x₀).toQuadraticMap.PosDef) :
    ∀ᶠ x in 𝓝 x₀, (B x).toQuadraticMap.PosDef := by
  classical
  have := Fintype.ofFinite ι
  have hA : ContinuousAt (fun x ↦ (B x).toMatrix b) x₀ :=
    continuousAt_pi.2 fun i ↦ continuousAt_pi.2 fun j ↦ by
      simpa only [toMatrix_apply] using hB i j
  have hA₀ : ∀ v : ι → ℝ, v ≠ 0 → 0 < RCLike.re (star v ⬝ᵥ (B x₀).toMatrix b *ᵥ v) := by
    intro v hv
    simpa only [BilinMap.toQuadraticMap_apply, star_trivial, RCLike.re_to_real,
      dotProduct_toMatrix_mulVec] using
      h₀ _ (b.equivFun.symm.map_ne_zero_iff.2 hv)
  filter_upwards [hA.eventually
    ((TauCeti.isOpen_setOfPred_re_dotProduct_pos (𝕜 := ℝ)).mem_nhds hA₀)] with x hx v hv
  simpa only [BilinMap.toQuadraticMap_apply, star_trivial, RCLike.re_to_real,
    dotProduct_toMatrix_mulVec, LinearEquiv.symm_apply_apply] using
    hx (b.equivFun v) (by simpa using hv)

end LinearMap.BilinForm
