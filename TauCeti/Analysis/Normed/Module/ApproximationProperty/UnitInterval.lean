/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.ApproximationProperty.Basic
public import TauCeti.MeasureTheory.Constructions.UnitInterval.Dyadic
public import TauCeti.MeasureTheory.Function.ConditionalExpectation.CondexpLp

/-!
# Metric approximation of `Lᵖ([0, 1])`

For `1 ≤ p < ∞`, the space `Lᵖ([0, 1])` of real or complex functions on the unit interval has the
metric approximation property. The approximating operators are the dyadic averaging projections:
the conditional expectations with respect to the steps `dyadicFiltration N` of the Haar-ordered
dyadic filtration. Each is a contraction of `Lᵖ` with finite-dimensional range, since its values
are constant on the dyadic cells of level `N`, and they converge pointwise to the identity because
the dyadic cells generate the σ-algebra of `[0, 1]`.

## Main results

* `TauCeti.unitInterval.hasFiniteRange_condExpLpCLM_dyadicFiltration`: the dyadic conditional
  expectations have finite rank.
* `TauCeti.unitInterval.tendsto_condExpLpCLM_dyadicFiltration`: they converge to the identity
  pointwise on `Lᵖ`.
* `TauCeti.unitInterval.hasMetricApproximationProperty_Lp`: `Lᵖ([0, 1])` has the metric
  approximation property.

## References

* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, 2nd ed., Graduate Texts in
  Mathematics 233, Springer (2016), §6.1.
* R. E. Megginson, *An Introduction to Banach Space Theory*, Section 3.4.
-/

public section

open MeasureTheory Filter

open scoped ENNReal Topology unitInterval

namespace TauCeti.unitInterval

variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The conditional expectation on `Lᵖ([0, 1])` with respect to the dyadic filtration has finite
rank: its values are constant on the dyadic cells of a fixed level. -/
theorem hasFiniteRange_condExpLpCLM_dyadicFiltration (N : ℕ) :
    (condExpLpCLM 𝕜 p (dyadicFiltration N) volume :
      Lp 𝕜 p (volume : Measure I) →L[𝕜] Lp 𝕜 p volume).toLinearMap.HasFiniteRange := by
  -- Step `N` is coarser than step `2 ^ N`, which is pulled back along the cell index of level `N`.
  let g : I → Fin (2 ^ N) := fun x => ⟨cellIdx (2 ^ N) x, cellIdx_lt (by positivity) x⟩
  have hg : Measurable g := measurable_to_countable' fun i => by
    convert measurableSet_preimage_cellIdx (2 ^ N) i
    ext x
    simp [g, Fin.ext_iff]
  refine hasFiniteRange_condExpLpCLM hg ?_
  calc (dyadicFiltration N : MeasurableSpace I) ≤ dyadicFiltration (2 ^ N) :=
        dyadicFiltration.mono (Nat.lt_two_pow_self).le
    _ = MeasurableSpace.comap (Fin.val ∘ g) ⊤ := dyadicFiltration_two_pow_eq_comap N
    _ ≤ MeasurableSpace.comap g _ := by
        rw [← MeasurableSpace.comap_comp]
        exact MeasurableSpace.comap_mono le_top

/-- The dyadic conditional expectations converge to the identity pointwise on `Lᵖ([0, 1])` for
`1 ≤ p < ∞`. -/
theorem tendsto_condExpLpCLM_dyadicFiltration (hp : p ≠ ∞) (f : Lp 𝕜 p (volume : Measure I)) :
    Tendsto (fun N => condExpLpCLM 𝕜 p (dyadicFiltration N) volume f) atTop (𝓝 f) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
    (tendsto_eLpNorm_condExp_dyadicFiltration Fact.out hp (Lp.memLp f))).congr fun N => ?_
  rw [Function.comp_apply, Lp.norm_def]
  congr 1
  refine eLpNorm_congr_ae ?_
  filter_upwards [Lp.coeFn_sub (condExpLpCLM 𝕜 p (dyadicFiltration N) volume f) f,
    coeFn_condExpLpCLM (𝕜 := 𝕜) (m := dyadicFiltration N) f] with x hx hx'
  rw [hx, Pi.sub_apply, Pi.sub_apply, hx']

/-- **The metric approximation property of `Lᵖ([0, 1])`.** For `1 ≤ p < ∞`, the identity of
`Lᵖ([0, 1])` is approximated uniformly on compact sets by the dyadic conditional expectations,
which are finite-rank contractions. -/
theorem hasMetricApproximationProperty_Lp (hp : p ≠ ∞) :
    HasMetricApproximationProperty 𝕜 (Lp 𝕜 p (volume : Measure I)) :=
  hasMetricApproximationProperty_iff.2 <| HasBoundedApproximationPropertyWith.of_tendsto
    (l := atTop) (fun N => condExpLpCLM 𝕜 p (dyadicFiltration N) volume)
    hasFiniteRange_condExpLpCLM_dyadicFiltration
    (fun _ => NNReal.coe_one ▸ norm_condExpLpCLM_le) (tendsto_condExpLpCLM_dyadicFiltration hp)

end TauCeti.unitInterval
