/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.LevelSet.Basic
public import TauCeti.Analysis.PDE.Vortex.FramedGauge.LocalModuli
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Index

/-!
# The vortex operator is Fredholm of index `2m` on `H^(k+1)`, and the Coulomb slice chart

Let `k ≥ 2` and let `x₀` be a continuous framed degree-`m` plane vortex of
`A_m^(k+1) = x_m + H^(k+1)(ℂ; ℝ⁴)` lying in every `A_m^j`. In the real chart of `A_m^(k+1)`, whose
coordinates are the real Hilbert space `(H^(k+1)_ℝ)⁴`, the gauge-fixed operator

`L_{x₀} = realSobolevGaugeFixedOperator f m hk u₀ : (H^(k+1)_ℝ)⁴ → H^k_ℝ × (H^k_ℝ)³`

at the real coordinates `u₀` of `x₀` is onto with a kernel of dimension `2m`
(`TauCeti.Vortex.realSobolevGaugeFixedOperator_surjective`,
`TauCeti.Vortex.finrank_ker_realSobolevGaugeFixedOperator`). This file draws the consequences:

* `L_{x₀}` is Fredholm (`isFredholm_realSobolevGaugeFixedOperator`) of index `2m`
  (`index_realSobolevGaugeFixedOperator_eq_two_mul`). This is Taubes's index theorem on the Sobolev
  scale `H^(k+1) → H^k`, on which the vortex equation is smooth; the corresponding statement for
  `H¹ → L²` is `TauCeti.Vortex.index_sobolevGaugeFixedOperator_eq_two_mul`.
* **The Coulomb slice chart.** The zeros of the slice equation through `x₀`
  (`TauCeti.Vortex.realSobolevSliceEquation`), the real coordinates of the vortices in the
  Coulomb slice through `x₀`, are near `u₀` homeomorphic to an open subset of `ℝ^(2m)`, of the
  dimension of the divisor space `Sym^m ℂ`: `coulombSliceChart` is a chart of this zero set at
  `u₀` with values in `Fin (2 * m) → ℝ`, sending `u₀` to `0` (`coulombSliceChart_apply_self`). It
  is the implicit-function chart `TauCeti.levelSetChartModel`.

The chart describes the Coulomb slice, not yet the quotient by the gauge group `G_(k+2)`: that
the slice meets each nearby gauge orbit exactly once is a separate statement.

## Main definitions

* `TauCeti.Vortex.coulombSliceChart`: the chart of the zeros of the slice equation at a vortex,
  modelled on `Fin (2 * m) → ℝ`.

## Main results

* `TauCeti.Vortex.isFredholm_realSobolevGaugeFixedOperator`,
  `TauCeti.Vortex.index_realSobolevGaugeFixedOperator_eq_two_mul`: at a vortex the gauge-fixed
  operator on the Sobolev scale is Fredholm of index `2m`.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Appendix A.3 (regular zero sets of Fredholm maps).
-/

public section

noncomputable section

namespace TauCeti.Vortex

open BesselPotentialSpace Module

variable {f : ContDiffBump (0 : ℝ)} {m k : ℕ}

variable (hk : 2 ≤ k) (x₀ : SobolevFieldSpace f m ((k : ℝ) + 1))
  (hmem : ∀ j : ℕ, ⇑x₀ ∈ framedFieldSpace f m j) (hsol : ∀ z, equation x₀ z = 0)

include hsol in
/-- At a vortex, the section satisfies the holomorphicity rows `∂bar_a α = 0`. -/
private theorem equation_apply_one_and_apply_two_eq_zero (w : ℂ) :
    equation x₀ w 1 = 0 ∧ equation x₀ w 2 = 0 := by
  simp [hsol w]

/-! ### The Fredholm property at a vortex -/

include hmem hsol in
/-- **The gauge-fixed operator on the Sobolev scale is Fredholm at a vortex.** At a continuous
vortex `x₀` of `A_m^(k+1)`, `k ≥ 2`, lying in `A_m^j` for every `j`, the gauge-fixed operator
`L_{x₀} : (H^(k+1)_ℝ)⁴ → H^k_ℝ × (H^k_ℝ)³` is a Fredholm operator. -/
theorem isFredholm_realSobolevGaugeFixedOperator :
    (realSobolevGaugeFixedOperator f m hk (x₀.realSubRef _)).IsFredholm := by
  have := finiteDimensional_ker_realSobolevGaugeFixedOperator hk x₀ hmem
    (equation_apply_one_and_apply_two_eq_zero x₀ hsol)
  exact .of_surjective (realSobolevGaugeFixedOperator_surjective hk x₀ hmem hsol)

include hmem hsol in
/-- **Taubes's index theorem on the Sobolev scale.** At a continuous vortex `x₀` of `A_m^(k+1)`,
`k ≥ 2`, lying in `A_m^j` for every `j`, the gauge-fixed operator
`L_{x₀} : (H^(k+1)_ℝ)⁴ → H^k_ℝ × (H^k_ℝ)³`, which is onto, has real index `2m`, the dimension of
the divisor space `Sym^m ℂ`. -/
theorem index_realSobolevGaugeFixedOperator_eq_two_mul :
    (realSobolevGaugeFixedOperator f m hk (x₀.realSubRef _)).index = 2 * m := by
  exact_mod_cast (ContinuousLinearMap.finrank_ker_eq_iff_index_eq _
    (realSobolevGaugeFixedOperator_surjective hk x₀ hmem hsol)).1
      (finrank_ker_realSobolevGaugeFixedOperator hk x₀ hmem
        (equation_apply_one_and_apply_two_eq_zero x₀ hsol))

/-! ### The Coulomb slice chart -/

include hsol in
/-- At a vortex `x₀` the slice equation through `x₀` vanishes at its real coordinates. -/
theorem realSobolevSliceEquation_realSubRef_self_eq_zero :
    realSobolevSliceEquation f m hk x₀ (x₀.realSubRef _) = 0 :=
  (realSobolevSliceEquation_realSubRef_eq_zero_iff hk x₀ x₀).2
    ⟨funext fun z ↦ by simp [gaugeAdjoint_def], funext hsol⟩

/-- **The Coulomb slice chart at a plane vortex.** Let `x₀` be a continuous vortex of
`A_m^(k+1)`, `k ≥ 2`, lying in `A_m^j` for every `j`, with real coordinates `u₀`. The zero set of
the slice equation through `x₀`, the real coordinates of the vortices in the Coulomb slice through
`x₀` (`realSobolevSliceEquation_realSubRef_eq_zero_iff`), is homeomorphic near `u₀` to an open
subset of `ℝ^(2m)`: this is a chart of it at `u₀` with values in `Fin (2 * m) → ℝ`, sending `u₀`
to `0` (`coulombSliceChart_apply_self`). It reads a zero `u` near `u₀` through the projection of
`u - u₀` onto the kernel of `L_{x₀}`, by the implicit function theorem
(`TauCeti.levelSetChartModel`), which applies because `L_{x₀}` is onto with a kernel of dimension
`2m`. -/
def coulombSliceChart :
    OpenPartialHomeomorph {u | realSobolevSliceEquation f m hk x₀ u = 0} (Fin (2 * m) → ℝ) :=
  have := finiteDimensional_ker_realSobolevGaugeFixedOperator hk x₀ hmem
    (equation_apply_one_and_apply_two_eq_zero x₀ hsol)
  levelSetChartModel (hasStrictFDerivAt_realSobolevSliceEquation hk x₀)
    (LinearMap.range_eq_top.2 (realSobolevGaugeFixedOperator_surjective hk x₀ hmem hsol))
    (.of_finiteDimensional _) this
    (finrank_ker_realSobolevGaugeFixedOperator hk x₀ hmem
      (equation_apply_one_and_apply_two_eq_zero x₀ hsol))
    (realSobolevSliceEquation_realSubRef_self_eq_zero hk x₀ hsol)

/-- **The Coulomb slice chart is the model chart of the zero set of the slice equation** at `u₀`,
`TauCeti.levelSetChartModel`, for any proofs of its hypotheses: the `TauCeti.levelSetChartModel_*`
lemmas give its values, its inverse, its source and its target. -/
theorem coulombSliceChart_eq
    (hker : (realSobolevGaugeFixedOperator f m hk (x₀.realSubRef _)).ker.ClosedComplemented)
    (hfin : FiniteDimensional ℝ (realSobolevGaugeFixedOperator f m hk (x₀.realSubRef _)).ker)
    (hn : finrank ℝ (realSobolevGaugeFixedOperator f m hk (x₀.realSubRef _)).ker = 2 * m) :
    coulombSliceChart hk x₀ hmem hsol =
      levelSetChartModel (hasStrictFDerivAt_realSobolevSliceEquation hk x₀)
        (LinearMap.range_eq_top.2 (realSobolevGaugeFixedOperator_surjective hk x₀ hmem hsol))
        hker hfin hn (realSobolevSliceEquation_realSubRef_self_eq_zero hk x₀ hsol) :=
  (rfl)

/-- The base point lies in the source of the Coulomb slice chart. -/
theorem mem_coulombSliceChart_source :
    ⟨x₀.realSubRef _, realSobolevSliceEquation_realSubRef_self_eq_zero hk x₀ hsol⟩ ∈
      (coulombSliceChart hk x₀ hmem hsol).source :=
  mem_levelSetChartModel_source _ _ _ _ _ _

/-- The Coulomb slice chart sends the vortex `x₀` to the origin. -/
@[simp]
theorem coulombSliceChart_apply_self :
    coulombSliceChart hk x₀ hmem hsol
        ⟨x₀.realSubRef _, realSobolevSliceEquation_realSubRef_self_eq_zero hk x₀ hsol⟩ = 0 :=
  levelSetChartModel_apply_self _ _ _ _ _ _

/-- The origin, the value of the Coulomb slice chart at the vortex `x₀`, lies in its target. -/
theorem mem_coulombSliceChart_target : 0 ∈ (coulombSliceChart hk x₀ hmem hsol).target :=
  mem_levelSetChartModel_target _ _ _ _ _ _

end TauCeti.Vortex
