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

Fix an exponent `d` and read the coefficients of `u` along the rays `ν, ν + d, ν + 2d, …`. If the
coefficients of `u` converge along the cofinite filter, then the coefficients along each single
ray have the same limit once the step `d` is nonzero. This needs only a topological coefficient
semiring, with no continuity assumption on its operations.

For a nonarchimedean coefficient ring, if the coefficients of `u` tend to zero along the
cofinite filter, then so do the ray sums. No completeness or separation hypothesis is needed
for this convergence statement about `tsum`.

Peeling the first term of a ray is a statement about an actual sum, so it asks for more: the
coefficient group must also be complete and separated for a compatible uniform structure
(`[UniformSpace R] [IsUniformAddGroup R] [CompleteSpace R] [T0Space R]`), which is what makes each
ray summable and its `tsum` the value one expects.

The rays are what turns a statement about a *diagonal* — the exponents congruent to one another
modulo `d` — into one about coefficients, which is how the decomposition of a two-variable
restricted series modulo `1 - XY` is proved.

## Main results

* `MvPowerSeries.tendsto_tsum_coeff_add_nsmul`: the ray sums tend to zero along `cofinite`.
* `MvPowerSeries.tendsto_coeff_add_nsmul`: along one ray the coefficients have the same limit
  as the full coefficient family, provided the step `d` is nonzero.
* `MvPowerSeries.tsum_coeff_add_nsmul_eq`: peeling the first term of a ray, over a complete
  separated nonarchimedean uniform additive group.
-/

public section

namespace MvPowerSeries

open Filter Finsupp Topology

variable {σ R : Type*}

section Semiring

variable [Semiring R]

/-- Along a ray with nonzero step, the coefficients have the same cofinite limit as the full
coefficient family. -/
theorem tendsto_coeff_add_nsmul [TopologicalSpace R] (u : MvPowerSeries σ R) {a : R}
    (hu : Tendsto (coeff · u) cofinite (𝓝 a)) {d : σ →₀ ℕ} (hd : d ≠ 0) (ν : σ →₀ ℕ) :
    Tendsto (fun n : ℕ ↦ coeff (ν + n • d) u) cofinite (𝓝 a) :=
  hu.comp ((nsmul_left_strictMono hd.bot_lt).const_add ν).injective.tendsto_cofinite

end Semiring

variable [Ring R]

/-- If the coefficients of `u` tend to zero along `cofinite`, so does the family of ray sums
`ν ↦ ∑' n, coeff (ν + n • d) u` in a nonarchimedean coefficient ring. -/
theorem tendsto_tsum_coeff_add_nsmul [TopologicalSpace R] [NonarchimedeanAddGroup R]
    (u : MvPowerSeries σ R) (hu : Tendsto (coeff · u) cofinite (𝓝 0)) (d : σ →₀ ℕ) :
    Tendsto (fun ν ↦ ∑' n : ℕ, coeff (ν + n • d) u) cofinite (𝓝 0) := by
  classical
  refine NonarchimedeanAddGroup.zeroAtFilter_cofinite_iff_finite_notMem.mpr fun W ↦ ?_
  refine ((NonarchimedeanAddGroup.zeroAtFilter_cofinite_iff_finite_notMem.mp hu W).biUnion
    fun μ _ ↦ Set.finite_Iic μ).subset fun ν hν ↦ ?_
  obtain ⟨n, hn⟩ := not_forall.mp (mt (tsum_mem W.isClosed) hν)
  exact Set.mem_biUnion hn (Set.mem_Iic.mpr le_self_add)

/-- The sum along a ray with nonzero step is its first coefficient plus the sum along the ray
starting one step further, in a complete separated nonarchimedean coefficient group. -/
theorem tsum_coeff_add_nsmul_eq [UniformSpace R] [IsUniformAddGroup R]
    [NonarchimedeanAddGroup R] [CompleteSpace R] [T0Space R] (u : MvPowerSeries σ R)
    (hu : Tendsto (coeff · u) cofinite (𝓝 0)) {d : σ →₀ ℕ} (hd : d ≠ 0) (ν : σ →₀ ℕ) :
    ∑' n : ℕ, coeff (ν + n • d) u = coeff ν u + ∑' n : ℕ, coeff (ν + d + n • d) u := by
  simpa [succ_nsmul', add_assoc] using (NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
    (u.tendsto_coeff_add_nsmul hu hd ν)).tsum_eq_zero_add

end MvPowerSeries
