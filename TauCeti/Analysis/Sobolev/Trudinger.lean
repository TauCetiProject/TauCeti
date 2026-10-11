/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Embedding
import TauCeti.Analysis.Sobolev.Poincare.Potential
import TauCeti.MeasureTheory.Integral.RieszPotential

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

The proof is that of Gilbarg–Trudinger, Theorem 7.15. A `C¹` function `u` with compact support in
`Ω` is bounded pointwise by the Riesz potential of `‖Du‖` of order one,
`‖u x‖ ≤ (n ω)⁻¹ ∫_Ω ‖Du y‖ ‖x - y‖ ^ (1 - n) dy`
(`TauCeti.enorm_le_lintegral_enorm_fderiv_mul_enorm_sub_rpow`), and that potential maps `Lⁿ(Ω)`
to `L^q(Ω)` with the stated constant (`TauCeti.eLpNorm_setLIntegral_enorm_sub_rpow_mul_le` with
`κ = 1/n`, `p = n`). The estimate then passes from test functions to their closure
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
  set ω := μ.real (ball (0 : E) 1)
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast finrank_pos
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hω : 0 < ω := ENNReal.toReal_pos (measure_ball_pos μ 0 one_pos).ne'
    measure_ball_lt_top.ne
  have hq' : (n : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  -- The Riesz potential of order one of `‖Du‖`, over `Ω`.
  set V : E → ℝ≥0∞ := fun x =>
    ∫⁻ y in Ω, ‖x - y‖ₑ ^ ((n : ℝ) * ((n : ℝ)⁻¹ - 1)) * ‖fderiv ℝ u y‖ₑ ∂μ
  have hcont := hu.continuous_fderiv one_ne_zero
  -- The pointwise potential bound `‖u x‖ ≤ (n ω)⁻¹ V x`.
  have hpt : ∀ x, ‖u x‖ₑ ≤ ENNReal.ofReal ((n * ω)⁻¹) * ‖V x‖ₑ := fun x => by
    refine (enorm_le_lintegral_enorm_fderiv_mul_enorm_sub_rpow (μ := μ) hu h2u x).trans_eq ?_
    rw [enorm_eq_self, ← setLIntegral_eq_of_support_subset (s := Ω)]
    · congr 1
      refine lintegral_congr fun y => ?_
      rw [mul_comm, show (n : ℝ) * ((n : ℝ)⁻¹ - 1) = 1 - n by field_simp]
    · intro y hy
      by_contra hyΩ
      rw [mem_support, fderiv_of_notMem_tsupport ℝ fun h => hyΩ (hsupp h)] at hy
      simp [enorm_eq_nnnorm] at hy
  -- The `Lⁿ`-`L^q` bound for the potential, with `κ = 1/n`, `p = n` and `δ = 1/n - 1/q`.
  have hpot := eLpNorm_setLIntegral_enorm_sub_rpow_mul_le (μ := μ) (p := (n : ℝ≥0)) (q := q)
    (κ := (n : ℝ)⁻¹) (δ := (n : ℝ)⁻¹ - (q : ℝ)⁻¹) (by exact_mod_cast finrank_pos) hq
    (by simp) (by linarith [inv_pos.2 hq0]) (inv_le_one_of_one_le₀ hn) hΩ
    hcont.enorm.aemeasurable
  rw [← eLpNorm_restrict_eq_of_support_subset hu.continuous.aestronglyMeasurable
    ((subset_tsupport _).trans hsupp)]
  calc
    eLpNorm u q (μ.restrict Ω) ≤ ENNReal.ofReal ((n * ω)⁻¹) * eLpNorm V q (μ.restrict Ω) :=
      eLpNorm_le_mul_eLpNorm_of_ae_le_mul'' _ hu.continuous.aestronglyMeasurable.restrict
        (ae_of_all _ hpt)
    _ ≤ _ := by
      rw [mul_assoc]
      refine (mul_le_mul_right hpot _).trans_eq ?_
      have hbase : (1 - ((n : ℝ)⁻¹ - (q : ℝ)⁻¹)) / ((n : ℝ)⁻¹ - ((n : ℝ)⁻¹ - (q : ℝ)⁻¹)) =
          q * (1 - (n : ℝ)⁻¹) + 1 := by
        field_simp [hn0]
        ring
      have hexp : 1 - ((n : ℝ)⁻¹ - (q : ℝ)⁻¹) = 1 - (n : ℝ)⁻¹ + (q : ℝ)⁻¹ := by ring
      have hω' : ω ^ (1 - (n : ℝ)⁻¹) = ω * ω ^ (-(n : ℝ)⁻¹) := by
        rw [sub_eq_add_neg, Real.rpow_add hω, Real.rpow_one]
      rw [hbase, hexp, hω', sub_sub_cancel, eLpNorm_enorm _ hcont.aestronglyMeasurable,
        eLpNorm_restrict_eq_of_support_subset hcont.aestronglyMeasurable
          ((support_fderiv_subset ℝ).trans hsupp),
        ENNReal.coe_natCast, ← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      rw [mul_assoc]
      congr 2
      field_simp

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
