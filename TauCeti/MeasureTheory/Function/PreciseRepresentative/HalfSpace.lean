/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import TauCeti.MeasureTheory.Function.PreciseRepresentative
import TauCeti.Analysis.InnerProductSpace.HyperplaneReflection
import TauCeti.MeasureTheory.Measure.Haar.HalfSpace
import TauCeti.MeasureTheory.Measure.OpenPos

/-!
# The precise representative up to the boundary of a half-space

Let `H = {y | c < ⟪y, ν⟫}` be an open half-space of a finite-dimensional real inner product space
with an additive Haar measure `μ`. A function `f` defined on `H` has, for the restricted measure
`μ.restrict H`, a precise representative at every point of the closed half-space, since `H` fills
at least half of every closed ball centred there. If `f` agrees almost everywhere on `B ∩ H`, for a
ball `B` centred on the boundary hyperplane, with a function `g` continuous on the closed half-ball
`B ∩ {y | c ≤ ⟪y, ν⟫}`, then this precise representative is `g` at every point of that closed
half-ball, boundary points included.

## Main declarations

* `TauCeti.MeasureTheory.preciseRepresentative_restrict_setOf_lt_inner_eq_of_continuousOn`: the
  precise representative of `f` for `μ.restrict H` is `g` on the closed half-ball.
-/

public section

open Metric Set
open scoped RealInnerProductSpace

namespace TauCeti

namespace MeasureTheory

open _root_.MeasureTheory

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- **The precise representative of a function continuous up to a flat boundary.** Let `μ` be an
additive Haar measure and `H = {y | c < ⟪y, ν⟫}` an open half-space. If `f` is locally integrable
on `H` and agrees almost everywhere on `B(y₀, ρ) ∩ H`, where `y₀` lies on the boundary hyperplane,
with a function `g` continuous on the closed half-ball `B(y₀, ρ) ∩ {c ≤ ⟪y, ν⟫}`, then at each
point of that closed half-ball the precise representative of `f` for `μ.restrict H` is the value
of `g`. Composed with the fold across the boundary hyperplane, `g` is continuous on the whole
ball and agrees with `f` on `H`, and `H` fills at least half of every closed ball centred in the
closed half-space. -/
theorem preciseRepresentative_restrict_setOf_lt_inner_eq_of_continuousOn (μ : Measure E)
    [μ.IsAddHaarMeasure] {ν : E} {c : ℝ} (hν : ν ≠ 0) {y₀ : E} (hy₀ : ⟪y₀, ν⟫ = c) {ρ : ℝ}
    {f g : E → F} (hf : LocallyIntegrable f (μ.restrict {y | c < ⟪y, ν⟫}))
    (hfg : f =ᵐ[μ.restrict (ball y₀ ρ ∩ {y | c < ⟪y, ν⟫})] g)
    (hg : ContinuousOn g (ball y₀ ρ ∩ {y | c ≤ ⟪y, ν⟫})) {x : E}
    (hx : x ∈ ball y₀ ρ ∩ {y | c ≤ ⟪y, ν⟫}) :
    preciseRepresentative (μ.restrict {y | c < ⟪y, ν⟫}) f x = g x := by
  have hmaps : MapsTo (fun y => if c ≤ ⟪y, ν⟫ then y else hyperplaneReflection ν c y)
      (ball y₀ ρ) (ball y₀ ρ ∩ {y | c ≤ ⟪y, ν⟫}) := fun y hy =>
    ⟨mapsTo_ite_hyperplaneReflection_ball hy₀ ρ hy, le_inner_ite_hyperplaneReflection hν c y⟩
  have hcont := hg.comp (lipschitzWith_one_ite_hyperplaneReflection ν c).continuous.continuousOn
    hmaps
  -- `H` fills at least half of every closed ball around a point of the closed half-space.
  have hpos (ε : ℝ) (hε : 0 < ε) : μ.restrict {y | c < ⟪y, ν⟫} (closedBall x ε) ≠ 0 :=
    μ.restrict_closedBall_ne_zero_of_mul_le (c := 2⁻¹) (by norm_num) hε
      (μ.inv_two_mul_addHaar_closedBall_le_addHaar_closedBall_inter_setOf_lt_inner hν hx.2.out)
  refine (preciseRepresentative_eq_of_continuousAt_of_measure_closedBall_ne_zero hpos
    (isOpen_ball.mem_nhds hx.1) (hf x) ?_ (hcont.continuousAt (isOpen_ball.mem_nhds hx.1))).trans ?_
  · -- On `H` the fold is the identity.
    rw [Measure.restrict_restrict isOpen_ball.measurableSet]
    filter_upwards [hfg, ae_restrict_mem (isOpen_ball.measurableSet.inter
      (isOpen_lt continuous_const (continuous_id.inner continuous_const)).measurableSet)]
      with y hy hyB
    simp only [Function.comp_apply, hyB.2.out.le, ↓reduceIte, hy]
  · simp only [Function.comp_apply, hx.2.out, ↓reduceIte]

end MeasureTheory

end TauCeti
