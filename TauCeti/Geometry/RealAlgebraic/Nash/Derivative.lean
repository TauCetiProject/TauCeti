/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Nash.Graph
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Derivative

/-!
# Differentiation of Nash germs

Every scalar directional derivative of a Nash germ is again a Nash germ. In particular
all coordinate partial derivatives are Nash, including on the singular locus of any
chosen polynomial relation for the original function. The derivative is the native
Fréchet derivative evaluated at a fixed vector.

Analyticity follows from analyticity of the Fréchet derivative. Semialgebraicity of
its graph follows from the difference-quotient limit formula, without choosing a
polynomial relation or excluding its discriminant locus. The local Nash graph
criterion then gives a polynomial relation for the derivative on a full neighborhood.

Iterating, every iterated derivative of a Nash germ evaluated at fixed directions is again a
Nash germ (`TauCeti.IsNashAt.iteratedFDeriv_apply`). This lets one describe the order of
vanishing of a Nash germ, for instance the multiplicity of a root along a line, through its
successive derivatives.

## References

* J. Bochnak, M. Coste, M.-F. Roy, *Real Algebraic Geometry*, Springer, 1998,
  Section 8.1 (Nash functions).
-/

public section

open Filter Metric Set Topology

namespace TauCeti

/-- Differentiation in any fixed direction preserves Nash germs. This applies at every
point of the germ, not just where a chosen algebraic relation has a simple root. -/
theorem IsNashAt.fderiv_apply {σ : Type*} [Fintype σ] {f : (σ → ℝ) → ℝ} {x : σ → ℝ}
    (hf : IsNashAt f x) (v : σ → ℝ) : IsNashAt (fun y ↦ fderiv ℝ f y v) x := by
  obtain ⟨_, U, hUo, hxU, _, hG⟩ := isNashAt_iff_exists_isSemialgebraicOn.mp hf
  obtain ⟨r, hr, hB⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (hUo.mem_nhds hxU) hf.analyticAt.eventually_analyticAt)
  have hsemi := isSemialgebraic_ball x r
  have hgraph := hG.mono hsemi (fun y hy ↦ (hB hy).1)
  refine isNashAt_iff_exists_isSemialgebraicOn.mpr ⟨?_, ball x r, isOpen_ball,
    mem_ball_self hr, hsemi, hgraph.fderiv_apply isOpen_ball ?_ v⟩
  · exact ((ContinuousLinearMap.apply ℝ ℝ v).analyticAt _).comp hf.analyticAt.fderiv
  · exact fun y hy ↦ (hB hy).2.differentiableWithinAt

/-- The `n`-th derivative of a Nash germ, evaluated at fixed directions `m`, is a Nash germ. -/
theorem IsNashAt.iteratedFDeriv_apply {σ : Type*} [Fintype σ] {f : (σ → ℝ) → ℝ} {x : σ → ℝ}
    (hf : IsNashAt f x) (n : ℕ) (m : Fin n → σ → ℝ) :
    IsNashAt (fun y ↦ iteratedFDeriv ℝ n f y m) x := by
  induction n with
  | zero => simpa using hf
  | succ n ih =>
    refine ((ih (Fin.tail m)).fderiv_apply (m 0)).congr ?_
    filter_upwards [hf.analyticAt.eventually_analyticAt] with y hy
    obtain ⟨U, hU, hfU⟩ := hy.exists_mem_nhds_analyticOnNhd
    have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ n f) y :=
      ((hfU.iteratedFDeriv n) y (mem_of_mem_nhds hU)).differentiableAt
    rw [iteratedFDeriv_succ_apply_left, fderiv_continuousMultilinear_apply_const_apply hd]

end TauCeti
