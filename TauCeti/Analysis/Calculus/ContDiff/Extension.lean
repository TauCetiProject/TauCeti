/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import TauCeti.Topology.UniformSpace.Extension
import Mathlib.Analysis.Calculus.FDeriv.Extend

/-!
# Smooth extension from uniformly continuous derivatives

`IsOpen.exists_contDiffOn_closure_eqOn_of_uniformContinuousOn_iteratedFDeriv` extends a smooth
map on a convex open set to a map smooth within its closure, provided every iterated derivative
is uniformly continuous. Continuous extensions of the jets form a Taylor series by
`hasFDerivWithinAt_closure_of_tendsto_fderiv`.
-/

public section

open Set
open scoped ContDiff Topology

/-- A smooth map on a convex open set, all of whose iterated derivatives are uniformly
continuous there, extends to a map smooth within the closure. -/
theorem IsOpen.exists_contDiffOn_closure_eqOn_of_uniformContinuousOn_iteratedFDeriv
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U)
    {f : E → F} (hf : ContDiffOn ℝ ∞ f U)
    (hderiv : ∀ n, UniformContinuousOn (iteratedFDeriv ℝ n f) U) :
    ∃ g : E → F, ContDiffOn ℝ ∞ g (closure U) ∧ EqOn g f U := by
  choose p hp hpeq using fun n ↦ (hderiv n).exists_continuousOn_closure_eqOn
  let g (x : E) := (p 0 x).curry0
  refine ⟨g, HasFTaylorSeriesUpToOn.contDiffOn (f' := fun x n ↦ p n x)
    ⟨fun _ _ ↦ rfl, ?_, fun n _ ↦ hp n⟩, ?_⟩
  · intro n _ x hx
    let d (y : E) :=
      continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) ↦ E) F (p (n + 1) y)
    have hd : ContinuousOn d (closure U) :=
      Continuous.comp_continuousOn
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) ↦ E) F).continuous (hp (n + 1))
    have hp_diff (y : E) (hy : y ∈ U) : DifferentiableAt ℝ (p n) y :=
      ((hf.contDiffAt (hU.mem_nhds hy)).differentiableAt_iteratedFDeriv (m := n)
        (WithTop.coe_lt_coe.2 (ENat.natCast_lt_top n))).congr_of_eventuallyEq
          ((hpeq n).eventuallyEq_of_mem (hU.mem_nhds hy))
    have hfd : EqOn (fderiv ℝ (p n)) d U := by
      intro y hy
      rw [((hpeq n).eventuallyEq_of_mem (hU.mem_nhds hy)).fderiv_eq,
        fderiv_iteratedFDeriv]
      simp only [d, Function.comp_apply, hpeq (n + 1) hy]
    exact hasFDerivWithinAt_closure_of_tendsto_fderiv
      (fun y hy ↦ (hp_diff y hy).differentiableWithinAt) hconv hU
      (fun y hy ↦ (hp n y hy).mono subset_closure)
      (((hd x hx).mono subset_closure).tendsto.congr'
        ((hfd.eventuallyEq_of_mem self_mem_nhdsWithin).symm))
  · intro x hx
    simp [g, hpeq 0 hx, iteratedFDeriv_zero_eq_comp]
