/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Basic
public import TauCeti.Topology.Algebra.Nonarchimedean.ZeroAtFilter

import Mathlib.Data.Finsupp.Interval
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean

/-!
# Summing the coefficients of a multivariate power series along a ray

Fix an exponent `d` and read the coefficients of `u` along the rays `ν, ν + d, ν + 2d, …`. Two
convergence statements need only a nonarchimedean coefficient group: if the coefficients of `u`
tend to zero along the cofinite filter, then so do the ray sums, and so do the coefficients along
each single ray once the step `d` is nonzero.

The coefficient ring is a (not necessarily commutative) `Ring`: `MvPowerSeries.coeff` is an
`R`-linear map, so `Semiring R` is the floor for stating any of this, and the nonarchimedean and
uniform hypotheses below need the additive group.

Peeling the first term of a ray is a statement about an actual sum, so it asks for more: the
coefficient group must also be complete and separated for a compatible uniform structure
(`[UniformSpace R] [IsUniformAddGroup R] [CompleteSpace R] [T0Space R]`), which is what makes each
ray summable and its `tsum` the value one expects.

The rays are what turns a statement about a *diagonal* — the exponents congruent to one another
modulo `d` — into one about coefficients, which is how the decomposition of a two-variable
restricted series modulo `1 - XY` is proved.

## Main results

* `MvPowerSeries.tendsto_tsum_coeff_add_nsmul`: the ray sums tend to zero along `cofinite`.
* `MvPowerSeries.tendsto_coeff_add_nsmul`: along one ray the coefficients tend to zero, provided
  the step `d` is nonzero.
* `MvPowerSeries.tsum_coeff_add_nsmul_eq`: peeling the first term of a ray, over a complete
  separated nonarchimedean uniform additive group.
-/

public section

namespace MvPowerSeries

open Filter Finsupp Topology

variable {σ R : Type*} [Ring R]

/-- **The ray sums tend to zero**: if the coefficients of `u` tend to zero along `cofinite`, so
does `ν ↦ ∑' n, coeff (ν + n • d) u`. A nonarchimedean subgroup `W` is closed, so a ray sum
outside `W` must have a term outside `W`, and `ν` lies below that term's index. -/
theorem tendsto_tsum_coeff_add_nsmul [TopologicalSpace R] [NonarchimedeanAddGroup R]
    {u : MvPowerSeries σ R} (hu : Tendsto (coeff · u) cofinite (𝓝 0)) (d : σ →₀ ℕ) :
    Tendsto (fun ν ↦ ∑' n : ℕ, coeff (ν + n • d) u) cofinite (𝓝 0) := by
  classical
  refine NonarchimedeanAddGroup.zeroAtFilter_cofinite_iff_finite_notMem.mpr fun W ↦ ?_
  refine ((NonarchimedeanAddGroup.zeroAtFilter_cofinite_iff_finite_notMem.mp hu W).biUnion
    fun μ _ ↦ Set.finite_Iic μ).subset fun ν hν ↦ ?_
  obtain ⟨n, hn⟩ := not_forall.mp (mt (tsum_mem W.isClosed) hν)
  exact Set.mem_biUnion hn (Set.mem_Iic.mpr le_self_add)

/-- **Along one ray the coefficients tend to zero.** The step `d` must be nonzero, so that
`n ↦ ν + n • d` is injective and cofinite sets pull back to cofinite sets. -/
theorem tendsto_coeff_add_nsmul [TopologicalSpace R] {u : MvPowerSeries σ R}
    (hu : Tendsto (coeff · u) cofinite (𝓝 0)) {d : σ →₀ ℕ} (hd : d ≠ 0) (ν : σ →₀ ℕ) :
    Tendsto (fun n : ℕ ↦ coeff (ν + n • d) u) cofinite (𝓝 0) :=
  hu.comp ((nsmul_left_strictMono hd.bot_lt).const_add ν).injective.tendsto_cofinite

/-- **Peeling the first term of a ray**: the ray at `ν` is its own first coefficient plus the ray
at `ν + d`. Summability comes from `tendsto_coeff_add_nsmul` over a complete nonarchimedean
group. -/
theorem tsum_coeff_add_nsmul_eq [UniformSpace R] [IsUniformAddGroup R]
    [NonarchimedeanAddGroup R] [CompleteSpace R] [T0Space R] {u : MvPowerSeries σ R}
    (hu : Tendsto (coeff · u) cofinite (𝓝 0)) {d : σ →₀ ℕ} (hd : d ≠ 0) (ν : σ →₀ ℕ) :
    ∑' n : ℕ, coeff (ν + n • d) u = coeff ν u + ∑' n : ℕ, coeff (ν + d + n • d) u := by
  simpa [succ_nsmul', add_assoc] using (NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
    (tendsto_coeff_add_nsmul hu hd ν)).tsum_eq_zero_add

end MvPowerSeries
