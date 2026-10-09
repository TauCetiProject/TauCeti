/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.FiniteMeasure

/-!
# The borderline Sobolev embedding `p = n`

Let `E` be a real normed space of dimension `n ≥ 1` with an additive Haar measure `μ`, and let
`ω = μ(B(0, 1))`. In the borderline case `p = n` of the Sobolev embedding, `W^{1,n}_0(Ω)` does not
embed in `L^∞(Ω)` once `n ≥ 2`, but on a set `Ω` of finite measure it embeds in `L^q(Ω)` for every
finite `q`, with the explicit bound

`‖u‖_{L^q} ≤ n⁻¹ ω ^ (-1/n) (q (1 - 1/n) + 1) ^ (1 - 1/n + 1/q) μ(Ω) ^ (1/q) ‖Du‖_{Lⁿ}`

for every `q ≥ n`. For `n ≥ 2` the constant grows like `q ^ (1 - 1/n)` as `q → ∞`; this is the
growth rate which, summed in the exponential series, gives Trudinger's exponential integrability
of `|u| ^ (n / (n - 1))`. For `n = 1` the constant is bounded in `q`, in line with the embedding
of `W^{1,1}_0` in `L^∞`.

The proof is that of Gilbarg–Trudinger, Theorem 7.15: the bound is the case `p = n`,
`δ = 1/n - 1/q` of the Sobolev inequality on sets of finite measure,
`TauCeti.eLpNorm_le_mul_measure_rpow_mul_eLpNorm_fderiv_of_lt`, which rests on the Riesz potential
of `‖Du‖` of order one. The estimate then passes from test functions to their closure
`W^{1,n}_0(Ω)` (`TauCeti.W1p.eLpNorm_value_le_of_forall_testFunction`).

## Main declarations

* `TauCeti.eLpNorm_le_mul_measure_rpow_mul_eLpNorm_fderiv`: the bound for compactly supported
  `C¹` functions.
* `TauCeti.W1p.eLpNorm_value_le_mul_measure_rpow_mul_enorm_gradient`: the bound on
  `W^{1,n}_0(Ω)`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 7.15 and its proof.
* N. S. Trudinger, *On imbeddings into Orlicz spaces and some applications*, J. Math. Mech. 17
  (1967), 473–483.
-/

public section

noncomputable section

namespace TauCeti

open Function MeasureTheory Metric Set Module TopologicalSpace
open scoped Distributions ENNReal NNReal

section CompactSupport

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure E} [μ.IsAddHaarMeasure] {u : E → F} {Ω : Set E}

/-- **The borderline Sobolev inequality for compactly supported functions.** Let `n` be the
dimension and `ω = μ(B(0, 1))`. If `u` is `C¹` with compact support inside a measurable set `Ω`,
then for every `q ≥ n`,

`‖u‖_{L^q} ≤ n⁻¹ ω ^ (-1/n) (q (1 - 1/n) + 1) ^ (1 - 1/n + 1/q) μ(Ω) ^ (1/q) ‖Du‖_{Lⁿ}`. -/
theorem eLpNorm_le_mul_measure_rpow_mul_eLpNorm_fderiv (hu : ContDiff ℝ 1 u)
    (h2u : HasCompactSupport u) (hΩ : MeasurableSet Ω) (hsupp : tsupport u ⊆ Ω) {q : ℝ≥0}
    (hq : (finrank ℝ E : ℝ≥0) ≤ q) :
    eLpNorm u q μ ≤
      ENNReal.ofReal ((finrank ℝ E : ℝ)⁻¹ * μ.real (ball 0 1) ^ (-(finrank ℝ E : ℝ)⁻¹) *
        (q * (1 - (finrank ℝ E : ℝ)⁻¹) + 1) ^ (1 - (finrank ℝ E : ℝ)⁻¹ + (q : ℝ)⁻¹)) *
        μ Ω ^ (q : ℝ)⁻¹ * eLpNorm (fderiv ℝ u) (finrank ℝ E) μ := by
  set n := finrank ℝ E
  have hn0 : (n : ℝ) ≠ 0 := by have : 0 < n := finrank_pos; positivity
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le (by have : 0 < n := finrank_pos; positivity)
    (by exact_mod_cast hq : (n : ℝ) ≤ q)
  have h := eLpNorm_le_mul_measure_rpow_mul_eLpNorm_fderiv_of_lt (μ := μ) hu h2u hΩ hsupp
    (p := n) (by exact_mod_cast finrank_pos) hq (δ := (n : ℝ)⁻¹ - (q : ℝ)⁻¹) (by simp)
    (by linarith [inv_pos.2 hq0])
  -- At `p = n`, `δ = 1/n - 1/q`, so `1/n - δ = 1/q` and `(1 - δ) / (1/n - δ) = q (1 - 1/n) + 1`.
  have hbase : (1 - ((n : ℝ)⁻¹ - (q : ℝ)⁻¹)) / ((n : ℝ)⁻¹ - ((n : ℝ)⁻¹ - (q : ℝ)⁻¹)) =
      q * (1 - (n : ℝ)⁻¹) + 1 := by
    field_simp [hn0]
    ring
  rwa [hbase, sub_sub_cancel, show 1 - ((n : ℝ)⁻¹ - (q : ℝ)⁻¹) = 1 - (n : ℝ)⁻¹ + (q : ℝ)⁻¹ by
    ring, ENNReal.coe_natCast] at h

end CompactSupport

section W1p0

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **The borderline Sobolev inequality on `W^{1,n}_0(Ω)`.** Let `n` be the dimension and
`ω = μ(B(0, 1))`. If `Ω` has finite measure, then every `u ∈ W^{1,n}_0(Ω)` lies in `L^q(Ω)` for
every finite `q ≥ n`, with

`‖u‖_{L^q} ≤ n⁻¹ ω ^ (-1/n) (q (1 - 1/n) + 1) ^ (1 - 1/n + 1/q) μ(Ω) ^ (1/q) ‖∇u‖_{Lⁿ}`.

No regularity of `Ω` is assumed. -/
theorem W1p.eLpNorm_value_le_mul_measure_rpow_mul_enorm_gradient (hp : p = finrank ℝ E)
    (hOmega : mu Omega ≠ ∞) {q : ℝ≥0} (hq : (finrank ℝ E : ℝ≥0) ≤ q)
    {u : W1p mu Omega p} (hu : u ∈ w1p0Submodule mu Omega p) :
    eLpNorm (W1p.value u : E → ℝ) q (mu.restrict Omega) ≤
      ENNReal.ofReal ((finrank ℝ E : ℝ)⁻¹ * mu.real (ball 0 1) ^ (-(finrank ℝ E : ℝ)⁻¹) *
        (q * (1 - (finrank ℝ E : ℝ)⁻¹) + 1) ^ (1 - (finrank ℝ E : ℝ)⁻¹ + (q : ℝ)⁻¹)) *
        mu Omega ^ (q : ℝ)⁻¹ * ‖W1p.gradient u‖ₑ := by
  have hn : 0 < finrank ℝ E := by
    have h1 : (1 : ℝ≥0∞) ≤ p := Fact.out
    rw [hp] at h1
    exact_mod_cast h1
  have : Nontrivial E := Module.nontrivial_of_finrank_pos hn
  set C : ℝ≥0∞ := ENNReal.ofReal ((finrank ℝ E : ℝ)⁻¹ *
    mu.real (ball 0 1) ^ (-(finrank ℝ E : ℝ)⁻¹) *
    (q * (1 - (finrank ℝ E : ℝ)⁻¹) + 1) ^ (1 - (finrank ℝ E : ℝ)⁻¹ + (q : ℝ)⁻¹)) *
    mu Omega ^ (q : ℝ)⁻¹
  have hC : C ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.rpow_ne_top_of_nonneg (by positivity) hOmega)
  have h := W1p.eLpNorm_value_le_of_forall_testFunction (q := q) (C := C.toNNReal)
    (fun phi => ?_) hu
  · rwa [ENNReal.coe_toNNReal hC] at h
  · rw [ENNReal.coe_toNNReal hC, hp]
    exact eLpNorm_le_mul_measure_rpow_mul_eLpNorm_fderiv (phi.contDiff.of_le (by simp))
      phi.hasCompactSupport Omega.isOpen.measurableSet phi.tsupport_subset hq

end W1p0

end TauCeti
