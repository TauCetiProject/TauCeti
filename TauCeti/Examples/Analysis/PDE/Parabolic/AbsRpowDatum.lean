/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.HeatEquation
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Holder.Localization
import TauCeti.Analysis.InnerProductSpace.NormPow
import TauCeti.Analysis.SpecialFunctions.Pow.Regularity

/-!
# The initial datum `|x| ^ (3 + β)`: the data space of the order-one Cauchy problem is sharp

For `0 < α < 1` the heat operator of order one is an isomorphism

`u ↦ (∂ₜu - Δu, u(·, 0)) : C_{par,b}^{3+α}(ℝⁿ × [0, T]) ≃ C_{par,b}^{1+α}(ℝⁿ × [0, T]) × C_b^{3,α}`

(`TauCeti.ParabolicCkHolderSpace.heatInitialDataCLE`, the case `k = 1`). This file shows on the line
`ℝ` that the initial data space `C_b^{3,α}` cannot be enlarged: an initial datum of class
`C_b^{3,β}` with `β < α` has a solution of order `3 + β`, given by the solution operator
`TauCeti.ParabolicCkHolderSpace.heatSolutionL` at exponent `β`, but none of order `3 + α`.

The datum is `u₀(x) = χ(x) |x| ^ (3 + β)` (`TauCeti.Examples.ParabolicAbsRpowDatum.datum`), the
power `|x| ^ (3 + β)` cut off at infinity by a smooth bump `χ` equal to `1` on `[-1, 1]`. Its third
derivative near the origin is `(3 + β) (2 + β) (1 + β) |x| ^ (β - 1) x`, which is `β`-Hölder and
`α`-Hölder for no `α > β`.

* `u₀ ∈ C_b^{3,β}` for `0 < β ≤ 1`
  (`TauCeti.Examples.ParabolicAbsRpowDatum.exists_ckHolderSpace_coe_eq_datum`).
* `u₀ ∉ C_b^{3,α}` for `α > β`
  (`TauCeti.Examples.ParabolicAbsRpowDatum.not_exists_ckHolderSpace_coe_eq_datum`).
* No map of order `3 + α` on a slab `ℝ × [a, b]` has `u₀` as a time slice, since its spatial trace
  at that time would lie in `C_b^{3,α}`
  (`TauCeti.Examples.ParabolicAbsRpowDatum.not_exists_parabolicCkHolderSpace_slice_eq_datum`).
* For `0 < β < 1` the heat equation `∂ₜu = Δu`, `u(·, 0) = u₀`, has a solution of order `3 + β`,
  and it is not a map of order `3 + α` for any `α > β`
  (`TauCeti.Examples.ParabolicAbsRpowDatum.exists_heatInitialDataL_eq_and_not_exists_coe_eq`).

## References

* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes, 2004, Chapter 4.
* N. V. Krylov, *Lectures on elliptic and parabolic equations in Hölder spaces*, AMS, 1996,
  Chapter 8.
-/

public section

noncomputable section

namespace TauCeti.Examples.ParabolicAbsRpowDatum

open Set Filter Topology ParabolicSpaceTime
open scoped NNReal

/-- The bump `χ`: a smooth bump on `ℝ`, equal to `1` on `[-1, 1]` and supported in
`[-3/2, 3/2]`. -/
def bump : ContDiffBump (0 : ℝ) :=
  ⟨1, 3 / 2, one_pos, by norm_num⟩

/-- The initial datum `u₀(x) = χ(x) |x| ^ (3 + β)`: the power `|x| ^ (3 + β)` near the origin, cut
off at infinity. -/
def datum (β : ℝ≥0) (x : ℝ) : ℝ :=
  bump x * |x| ^ (3 + (β : ℝ))

/-- On `[-1, 1]` the datum is the power `|x| ^ (3 + β)`. -/
theorem datum_eq_of_abs_le_one (β : ℝ≥0) {x : ℝ} (hx : |x| ≤ 1) :
    datum β x = |x| ^ (3 + (β : ℝ)) := by
  rw [datum, bump.one_of_mem_closedBall (by rwa [mem_closedBall_zero_iff, Real.norm_eq_abs]),
    one_mul]

/-- **The datum lies in `C_b^{3,β}`.** For `0 < β ≤ 1` the datum is a bounded `C³` function with
bounded derivatives through order three and `β`-Hölder third derivative. -/
theorem exists_ckHolderSpace_coe_eq_datum {β : ℝ≥0} (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    ∃ u : CkHolderSpace 3 β ℝ ℝ, ⇑u = datum β := by
  set f : ℝ → ℝ := fun x ↦ |x| ^ (3 + (β : ℝ))
  have hf : ContDiff ℝ (3 : ℕ) f := by
    have h := contDiff_norm_rpow_of_lt (E := ℝ) (k := 3) (p := 3 + β)
      (by norm_num; exact_mod_cast hβ0)
    simpa only [Real.norm_eq_abs] using h
  -- The derivatives of `|x| ^ (3 + β)` through order three are bounded on `(-2, 2)`, and those of
  -- the bump through order four are bounded everywhere.
  obtain ⟨M, -, hM⟩ := ContDiffOn.exists_nonneg_bound_iteratedFDeriv_of_isOpen
    hf.contDiffOn isOpen_univ isCompact_Icc (subset_univ (Icc (-2 : ℝ) 2))
  obtain ⟨N, -, hN⟩ :=
    bump.hasCompactSupport.exists_bound_iteratedFDeriv bump.contDiff (3 + 1)
  have hsupp : tsupport bump ⊆ Ioo (-2 : ℝ) 2 := by
    intro x hx
    rw [bump.tsupport_eq, mem_closedBall_zero_iff, Real.norm_eq_abs] at hx
    have hx' : |x| ≤ 3 / 2 := hx
    rw [abs_le] at hx'
    exact ⟨by linarith, by linarith⟩
  refine ⟨CkHolderSpace.cutoff hf.contDiffOn
    ((bump.contDiff (n := ⊤)).of_le (WithTop.coe_le_coe.2 le_top)) isOpen_Ioo
    (convex_Ioo _ _) hsupp hβ1 (M := M.toNNReal)
    (fun i hi x hx ↦ (hM i hi x (Ioo_subset_Icc_self hx)).trans (Real.le_coe_toNNReal M))
    (N := N.toNNReal) (fun i hi x ↦ (hN i hi x).trans (Real.le_coe_toNNReal N))
    ((holderWith_iteratedFDeriv_three_abs_rpow_three_add hβ0 hβ1).holderOnWith _), ?_⟩
  rw [CkHolderSpace.coe_cutoff]
  funext x
  rw [smul_eq_mul, datum]

/-- Near the origin the third derivative of the datum is that of `|x| ^ (3 + β)`. -/
private theorem iteratedFDeriv_datum_eq {β : ℝ≥0} {x : ℝ} (hx : x ∈ Metric.ball (0 : ℝ) 1) :
    iteratedFDeriv ℝ 3 (datum β) x = iteratedFDeriv ℝ 3 (fun y : ℝ ↦ |y| ^ (3 + (β : ℝ))) x := by
  have he : datum β =ᶠ[𝓝 x] fun y : ℝ ↦ |y| ^ (3 + (β : ℝ)) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hx] with y hy
    rw [mem_ball_zero_iff, Real.norm_eq_abs] at hy
    exact datum_eq_of_abs_le_one β hy.le
  exact (he.iteratedFDeriv ℝ 3).eq_of_nhds

/-- **The datum does not lie in `C_b^{3,α}` for `α > β`.** Near the origin its third derivative is
`(3 + β) (2 + β) (1 + β) |x| ^ (β - 1) x`, which is `α`-Hölder for no `α > β`. -/
theorem not_exists_ckHolderSpace_coe_eq_datum {α β : ℝ≥0} (hβ0 : 0 < β) (hβα : β < α) :
    ¬ ∃ u : CkHolderSpace 3 α ℝ ℝ, ⇑u = datum β := by
  rintro ⟨u, hu⟩
  obtain ⟨C, hC⟩ := u.memHolder_iteratedFDeriv
  rw [hu] at hC
  refine not_holderOnWith_iteratedFDeriv_three_abs_rpow_three_add hβ0 hβα (C := C)
    (Metric.ball_mem_nhds 0 one_pos) fun x hx y hy ↦ ?_
  rw [← iteratedFDeriv_datum_eq hx, ← iteratedFDeriv_datum_eq hy]
  exact hC x y

/-- **No map of order `3 + α` has the datum as a time slice**, for `0 < β < α`. On a slab
`ℝ × [a, b]`, a map `u ∈ C_{par,b}^{3+α}` with `u(·, t) = u₀` would have its spatial trace at `t`
in `C_b^{3,α}`. In particular `u₀` is the initial trace of no map of order `3 + α`, so it is not
initial data for the order-one isomorphism at exponent `α`. -/
theorem not_exists_parabolicCkHolderSpace_slice_eq_datum {α β : ℝ≥0} (hβ0 : 0 < β)
    (hβα : β < α) {a b : ℝ} (hab : a < b) (t : Icc a b) :
    ¬ ∃ u : ParabolicCkHolderSpace 3 α ℝ ℝ hab, ∀ x, u (slabMk x t) = datum β x := by
  rintro ⟨u, hu⟩
  exact not_exists_ckHolderSpace_coe_eq_datum hβ0 hβα
    ⟨u.spatialTrace t, funext fun x ↦ by rw [ParabolicCkHolderSpace.spatialTrace_apply, hu]⟩

/-- **The heat flow of the datum has order `3 + β` and not `3 + α`.** For `0 < β < 1` and
`α > β`, there is a solution `u ∈ C_{par,b}^{3+β}(ℝ × [0, T])` of the heat equation `∂ₜu = Δu`
with initial value `u(·, 0) = u₀`, and it is not a map of order `3 + α`. -/
theorem exists_heatInitialDataL_eq_and_not_exists_coe_eq {α β : ℝ≥0} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hβα : β < α) {T : ℝ≥0} (hT : (0 : ℝ) < T) :
    ∃ u : ParabolicCkHolderSpace (1 + 2) β ℝ ℝ hT,
      (ParabolicCkHolderSpace.heatInitialDataL 1 hβ1.le hT u).1 = 0 ∧
        ⇑(ParabolicCkHolderSpace.heatInitialDataL 1 hβ1.le hT u).2 = datum β ∧
        ¬ ∃ v : ParabolicCkHolderSpace (1 + 2) α ℝ ℝ hT, ⇑v = ⇑u := by
  obtain ⟨g, hg⟩ := exists_ckHolderSpace_coe_eq_datum hβ0 hβ1.le
  have hu := ParabolicCkHolderSpace.heatInitialDataL_heatSolutionL (k := 1) (E := ℝ) (F := ℝ)
    hβ0 hβ1 (hT := hT) (0, g)
  refine ⟨ParabolicCkHolderSpace.heatSolutionL 1 hβ0 hβ1 hT (0, g), by rw [hu], by rw [hu, hg], ?_⟩
  rintro ⟨v, hv⟩
  refine not_exists_parabolicCkHolderSpace_slice_eq_datum hβ0 hβα hT ⟨0, left_mem_Icc.2 hT.le⟩
    ⟨v, fun x ↦ ?_⟩
  rw [hv, ← ParabolicCkHolderSpace.spatialTrace_apply,
    ← ParabolicCkHolderSpace.heatInitialDataL_snd hβ1.le, hu, hg]

end TauCeti.Examples.ParabolicAbsRpowDatum
