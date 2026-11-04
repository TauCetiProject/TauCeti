/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
public import TauCeti.Analysis.BoundedVariation.ReducedBoundary
public import TauCeti.MeasureTheory.Covering.EssentialBoundary
import Mathlib.Analysis.Calculus.Monotone
import TauCeti.Analysis.BoundedVariation.CutByBall
import TauCeti.Analysis.BoundedVariation.DensityEstimates
import TauCeti.Analysis.BoundedVariation.RelativeIsoperimetric
import TauCeti.Analysis.BoundedVariation.Sobolev
import TauCeti.Analysis.Calculus.PowerGrowth
import TauCeti.Basic.Real.ConjExponents
import TauCeti.MeasureTheory.Measure.InterBall
import TauCeti.MeasureTheory.Measure.OpenPos

/-!
# The lower density estimates at the reduced boundary

Let `E` be a finite-dimensional real inner product space of dimension `n ≥ 2` with an additive Haar
measure `μ`, let `Ω` be an open subset of `E` and let `x` be a point of the reduced boundary `∂*s`
of a set `s` in `Ω` (`TauCeti.reducedBoundary`). This file proves the **lower density estimates**:
for every `t > 1` and every small `r > 0`,

`r ^ n ≤ K ^ n μ(s ∩ ball x r)`,    `r ^ n ≤ K ^ n μ(ball x r \ s)`,

(`TauCeti.eventually_ofReal_pow_le_mul_measure_inter_ball`,
`TauCeti.eventually_ofReal_pow_le_mul_measure_ball_sdiff`) and

`r ^ (n - 1) ≤ K ^ (n - 1) C' P(s; ball x r)`

(`TauCeti.eventually_ofReal_pow_le_mul_perimeter_ball`), where `K = (1 + t) n C`, `C` is the
constant `MeasureTheory.eLpNormLESNormFDerivOneConst μ p` of the Gagliardo–Nirenberg–Sobolev
inequality with `p = n / (n - 1)`, and `C' = 2 ^ (n + 1) μ(ball 0 1) ^ (-1/n)` is the constant of
the relative isoperimetric inequality `TauCeti.min_measure_inter_measure_sdiff_rpow_le_perimeter`.
The constants depend only on `n`, `μ` and `t`. Together with the upper density estimate
`TauCeti.eventually_perimeter_ball_le`, they say that near a point of the reduced boundary both
`s` and its complement fill a definite proportion of every small ball, and the perimeter measure of
the ball is comparable to `r ^ (n - 1)`. These are the estimates behind the compactness of the
blow-ups of `s` at points of `∂*s` in De Giorgi's structure theorem. As a first consequence, the
reduced boundary lies in the essential boundary
(`TauCeti.reducedBoundary_subset_essentialBoundary`).

Write `m(ρ) = μ(s ∩ ball x ρ)`. Cutting `s` by the ball of radius `ρ` adds at most `m'(ρ)` to its
perimeter (`TauCeti.ae_perimeter_inter_ball_le`), and at the reduced boundary
`P(s; ball x ρ) ≤ t m'(ρ)` for small `ρ`
(`TauCeti.eventually_variationMeasure_closedBall_le_mul_enorm_setIntegral`,
`TauCeti.enorm_setIntegral_polarDensity_closedBall_le_of_hasDerivWithinAt`). The nonsharp
isoperimetric inequality `TauCeti.measure_rpow_le_perimeter` applied to `s ∩ ball x ρ` then gives
the differential inequality `m(ρ) ^ (1 - 1/n) ≤ (1 + t) C m'(ρ)` for almost every small `ρ`, which
integrates to `r ≤ K m(r) ^ (1/n)` (`TauCeti.mul_le_mul_rpow_of_rpow_one_sub_le_mul_deriv`). The
complement has the same reduced boundary, and the relative isoperimetric inequality turns the two
volume bounds into the perimeter bound.

Neither finite perimeter, finite measure nor measurability of `s` in the whole space is assumed: a
point of the reduced boundary already forces `s` to have locally finite perimeter in `Ω`.

## References

* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, Theorem 16.2.
* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §5.7.2, Lemma 5.8.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory TopologicalSpace Set Filter Metric Module
open scoped ENNReal NNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E}
  {s : Set E} {x : E} {p : ℝ≥0}

/-- **The differential inequality at the reduced boundary.** For a null-measurable `s`, a point
`x` of its reduced boundary in `Ω` and `t > 1`, the function `m(ρ) = μ(s ∩ ball x ρ)` satisfies
`m(ρ) ^ (1 - 1/n) ≤ (1 + t) C m'(ρ)` at almost every small radius `ρ`. -/
private theorem exists_ae_measureReal_inter_ball_rpow_le
    (hp : NNReal.HolderConjugate (finrank ℝ E) p) (hs : NullMeasurableSet s μ)
    (hx : x ∈ reducedBoundary μ Ω s) {t : ℝ≥0} (ht : 1 < t) :
    ∃ ε > 0, ∀ᵐ ρ, ρ ∈ Ioo 0 ε → μ.real (s ∩ ball x ρ) ^ (1 - (finrank ℝ E : ℝ)⁻¹) ≤
      ((1 + t) * eLpNormLESNormFDerivOneConst μ p : ℝ≥0) *
        deriv (fun ρ => μ.real (s ∩ ball x ρ)) ρ := by
  obtain ⟨hu, hfin⟩ := locallyIntegrableOn_and_totalVariationOn_ne_top_of_mem_reducedBoundary hx
  obtain ⟨ε₁, hε₁, hε₁Ω⟩ :=
    nhds_basis_closedBall.mem_iff.1 (Ω.isOpen.mem_nhds (reducedBoundary_subset hx))
  obtain ⟨ε₂, hε₂, hε₂t⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1
    (eventually_variationMeasure_closedBall_le_mul_enorm_setIntegral hx ht)
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, ?_⟩
  set m := fun ρ => μ.real (s ∩ ball x ρ)
  set C := eLpNormLESNormFDerivOneConst μ p
  have hexp : 1 - (finrank ℝ E : ℝ)⁻¹ = (p : ℝ)⁻¹ := by simpa using hp.coe.one_sub_inv
  filter_upwards [ae_perimeter_inter_ball_le hs x,
    (monotone_measureReal_inter_ball μ s x).ae_differentiableAt] with ρ hcut hdiff hρ
  have hρΩ : closedBall x ρ ⊆ Ω :=
    (closedBall_subset_closedBall (hρ.2.le.trans (min_le_left _ _))).trans hε₁Ω
  have hD : 0 ≤ deriv m ρ := (monotone_measureReal_inter_ball μ s x).deriv_nonneg
  -- At the reduced boundary, `P(s; ball x ρ) ≤ |Dχ_s| (closedBall x ρ) ≤ t m'(ρ)`.
  have hP : perimeter μ ⟨ball x ρ, isOpen_ball⟩ s ≤ t * ENNReal.ofReal (deriv m ρ) := by
    rw [perimeter_def, ← variationMeasure_preimage_coe hu hfin (U := ⟨ball x ρ, isOpen_ball⟩)
      fun y hy => hρΩ (ball_subset_closedBall hy)]
    refine (measure_mono (preimage_mono ball_subset_closedBall)).trans
      ((hε₂t ⟨hρ.1, hρ.2.trans_le (min_le_right _ _)⟩).trans ?_)
    gcongr
    exact enorm_setIntegral_polarDensity_closedBall_le_of_hasDerivWithinAt hu hfin hs hρΩ
      hdiff.hasDerivAt.hasDerivWithinAt
  have hfin' : μ (s ∩ ball x ρ) ≠ ∞ :=
    measure_ne_top_of_subset inter_subset_right measure_ball_lt_top.ne
  -- The isoperimetric inequality for `s ∩ ball x ρ`, and cutting `s` by the ball.
  have key : μ (s ∩ ball x ρ) ^ (p : ℝ)⁻¹ ≤ ENNReal.ofReal (((1 + t) * C : ℝ≥0) * deriv m ρ) := by
    calc μ (s ∩ ball x ρ) ^ (p : ℝ)⁻¹ ≤ C * perimeter μ ⊤ (s ∩ ball x ρ) :=
          measure_rpow_le_perimeter (hs.inter measurableSet_ball.nullMeasurableSet) hfin' hp
      _ ≤ C * (t * ENNReal.ofReal (deriv m ρ) + ENNReal.ofReal (deriv m ρ)) := by
          gcongr
          exact hcut.trans (add_le_add_left hP _)
      _ = ENNReal.ofReal (((1 + t) * C : ℝ≥0) * deriv m ρ) := by
          rw [ENNReal.ofReal_mul NNReal.zero_le_coe, ENNReal.ofReal_coe_nnreal]
          push_cast
          ring
  rw [← ofReal_measureReal hfin', ENNReal.ofReal_rpow_of_nonneg measureReal_nonneg (by positivity),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at key
  rwa [hexp]

/-- The lower volume density estimate at the reduced boundary, for a null-measurable set, in the
form `r ≤ K m(r) ^ (1/n)`. -/
private theorem eventually_ofReal_le_mul_measure_inter_ball_rpow_of_nullMeasurableSet
    (hp : NNReal.HolderConjugate (finrank ℝ E) p) (hs : NullMeasurableSet s μ)
    (hx : x ∈ reducedBoundary μ Ω s) {t : ℝ≥0} (ht : 1 < t) :
    ∀ᶠ r in 𝓝[>] 0, ENNReal.ofReal r ≤
      ((1 + t) * finrank ℝ E * eLpNormLESNormFDerivOneConst μ p : ℝ≥0) *
        μ (s ∩ ball x r) ^ (finrank ℝ E : ℝ)⁻¹ := by
  obtain ⟨ε, hε, h⟩ := exists_ae_measureReal_inter_ball_rpow_le hp hs hx ht
  have hn : (0 : ℝ) < finrank ℝ E := by
    exact_mod_cast zero_lt_two.trans_le hp.two_le_of_natCast
  filter_upwards [Ioo_mem_nhdsGT hε] with r hr
  have hfin : μ (s ∩ ball x r) ≠ ∞ :=
    measure_ne_top_of_subset inter_subset_right measure_ball_lt_top.ne
  -- Integrate the differential inequality on `(0, r)`.
  have hode := mul_le_mul_rpow_of_rpow_one_sub_le_mul_deriv hr.1.le
    ((monotone_measureReal_inter_ball μ s x).monotoneOn _) measureReal_nonneg
    (fun ρ hρ => ENNReal.toReal_pos (measure_inter_ball_pos hx hρ.1).ne'
      (measure_ne_top_of_subset inter_subset_right measure_ball_lt_top.ne))
    (inv_pos.2 hn) NNReal.zero_le_coe
    (h.mono fun ρ hρ hρr => hρ ⟨hρr.1, hρr.2.trans hr.2⟩)
  rw [← ofReal_measureReal hfin, ENNReal.ofReal_rpow_of_nonneg measureReal_nonneg (by positivity),
    ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul NNReal.zero_le_coe]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [inv_mul_le_iff₀ hn] at hode
  refine hode.trans_eq ?_
  push_cast
  ring

/-- The lower volume density estimate at the reduced boundary in the form `r ≤ K m(r) ^ (1/n)`. -/
private theorem eventually_ofReal_le_mul_measure_inter_ball_rpow
    (hp : NNReal.HolderConjugate (finrank ℝ E) p) (hx : x ∈ reducedBoundary μ Ω s) {t : ℝ≥0}
    (ht : 1 < t) :
    ∀ᶠ r in 𝓝[>] 0, ENNReal.ofReal r ≤
      ((1 + t) * finrank ℝ E * eLpNormLESNormFDerivOneConst μ p : ℝ≥0) *
        μ (s ∩ ball x r) ^ (finrank ℝ E : ℝ)⁻¹ := by
  -- Replace `s` by the null-measurable set `s ∩ Ω`, which agrees with `s` in small balls.
  have hx' : x ∈ reducedBoundary μ Ω (s ∩ Ω) := by rwa [reducedBoundary_inter_opens]
  obtain ⟨ε, hε, hεΩ⟩ := Metric.mem_nhds_iff.1 (Ω.isOpen.mem_nhds (reducedBoundary_subset hx))
  filter_upwards [eventually_ofReal_le_mul_measure_inter_ball_rpow_of_nullMeasurableSet hp
    (nullMeasurableSet_inter_of_mem_reducedBoundary hx) hx' ht, Ioo_mem_nhdsGT hε] with r h hr
  rwa [inter_assoc, inter_eq_right.2 ((ball_subset_ball hr.2.le).trans hεΩ)] at h

/-- **The lower volume density estimate at the reduced boundary.** Let `E` have dimension `n ≥ 2`
and let `p = n / (n - 1)`. At a point `x` of the reduced boundary of `s` in `Ω`, for every `t > 1`
and every small `r > 0`,

`r ^ n ≤ ((1 + t) n C) ^ n μ(s ∩ ball x r)`,

where `C` is the constant `MeasureTheory.eLpNormLESNormFDerivOneConst μ p` of the
Gagliardo–Nirenberg–Sobolev inequality. -/
theorem eventually_ofReal_pow_le_mul_measure_inter_ball
    (hp : NNReal.HolderConjugate (finrank ℝ E) p) (hx : x ∈ reducedBoundary μ Ω s) {t : ℝ≥0}
    (ht : 1 < t) :
    ∀ᶠ r in 𝓝[>] 0, ENNReal.ofReal (r ^ finrank ℝ E) ≤
      ((1 + t) * finrank ℝ E * eLpNormLESNormFDerivOneConst μ p : ℝ≥0) ^ finrank ℝ E *
        μ (s ∩ ball x r) := by
  have hn : finrank ℝ E ≠ 0 := (zero_lt_two.trans_le hp.two_le_of_natCast).ne'
  filter_upwards [eventually_ofReal_le_mul_measure_inter_ball_rpow hp hx ht,
    self_mem_nhdsWithin] with r h (hr : 0 < r)
  rw [ENNReal.ofReal_pow hr.le]
  refine (pow_le_pow_left₀ zero_le h _).trans_eq ?_
  rw [mul_pow, ENNReal.rpow_inv_natCast_pow hn]

/-- **The lower volume density estimate for the complement.** Let `E` have dimension `n ≥ 2` and
let `p = n / (n - 1)`. At a point `x` of the reduced boundary of `s` in `Ω`, for every `t > 1` and
every small `r > 0`,

`r ^ n ≤ ((1 + t) n C) ^ n μ(ball x r \ s)`,

where `C` is the constant `MeasureTheory.eLpNormLESNormFDerivOneConst μ p` of the
Gagliardo–Nirenberg–Sobolev inequality. -/
theorem eventually_ofReal_pow_le_mul_measure_ball_sdiff
    (hp : NNReal.HolderConjugate (finrank ℝ E) p) (hx : x ∈ reducedBoundary μ Ω s) {t : ℝ≥0}
    (ht : 1 < t) :
    ∀ᶠ r in 𝓝[>] 0, ENNReal.ofReal (r ^ finrank ℝ E) ≤
      ((1 + t) * finrank ℝ E * eLpNormLESNormFDerivOneConst μ p : ℝ≥0) ^ finrank ℝ E *
        μ (ball x r \ s) := by
  simpa only [sdiff_eq_compl_inter] using
    eventually_ofReal_pow_le_mul_measure_inter_ball hp
      (by rwa [reducedBoundary_compl] : x ∈ reducedBoundary μ Ω sᶜ) ht

/-- **The lower perimeter density estimate at the reduced boundary.** Let `E` have dimension
`n ≥ 2`, let `p = n / (n - 1)` and let `ω = μ(ball 0 1)`. At a point `x` of the reduced boundary of
`s` in `Ω`, for every `t > 1` and every small `r > 0`,

`r ^ (n - 1) ≤ ((1 + t) n C) ^ (n - 1) 2 ^ (n + 1) ω ^ (-1/n) P(s; ball x r)`,

where `C` is the constant `MeasureTheory.eLpNormLESNormFDerivOneConst μ p` of the
Gagliardo–Nirenberg–Sobolev inequality. -/
theorem eventually_ofReal_pow_le_mul_perimeter_ball
    (hp : NNReal.HolderConjugate (finrank ℝ E) p) (hx : x ∈ reducedBoundary μ Ω s) {t : ℝ≥0}
    (ht : 1 < t) :
    ∀ᶠ r in 𝓝[>] 0, ENNReal.ofReal (r ^ (finrank ℝ E - 1)) ≤
      ((1 + t) * finrank ℝ E * eLpNormLESNormFDerivOneConst μ p : ℝ≥0) ^ (finrank ℝ E - 1) *
        ENNReal.ofReal (2 ^ (finrank ℝ E + 1) / μ.real (ball 0 1) ^ (finrank ℝ E : ℝ)⁻¹) *
          perimeter μ ⟨ball x r, isOpen_ball⟩ s := by
  have hn := hp.two_le_of_natCast
  have hs := nullMeasurableSet_restrict_of_mem_reducedBoundary hx
  obtain ⟨ε, hε, hεΩ⟩ := Metric.mem_nhds_iff.1 (Ω.isOpen.mem_nhds (reducedBoundary_subset hx))
  have hxc : x ∈ reducedBoundary μ Ω sᶜ := by rwa [reducedBoundary_compl]
  filter_upwards [eventually_ofReal_le_mul_measure_inter_ball_rpow hp hx ht,
    eventually_ofReal_le_mul_measure_inter_ball_rpow hp hxc ht, Ioo_mem_nhdsGT hε]
    with r h₁ h₂ hr
  set K := ((1 + t) * finrank ℝ E * eLpNormLESNormFDerivOneConst μ p : ℝ≥0)
  rw [← sdiff_eq_compl_inter] at h₂
  -- Both `s` and its complement fill a proportion of the ball, so the smaller one does.
  have hmin : ENNReal.ofReal r ≤ K * min (μ (s ∩ ball x r)) (μ (ball x r \ s)) ^
      (finrank ℝ E : ℝ)⁻¹ := by
    rcases min_choice (μ (s ∩ ball x r)) (μ (ball x r \ s)) with h | h <;> rw [h] <;> assumption
  have hiso := min_measure_inter_measure_sdiff_rpow_le_perimeter hn
    (hs.mono (Measure.restrict_mono ((ball_subset_ball hr.2.le).trans hεΩ) le_rfl))
    (Ω := ⟨ball x r, isOpen_ball⟩) subset_rfl
  have hexp : (finrank ℝ E : ℝ)⁻¹ * ((finrank ℝ E - 1 : ℕ) : ℝ) = 1 - (finrank ℝ E : ℝ)⁻¹ := by
    rw [Nat.cast_sub (one_le_two.trans hn)]
    field_simp
    ring
  rw [ENNReal.ofReal_pow hr.1.le, mul_assoc]
  refine (pow_le_pow_left₀ zero_le hmin _).trans ?_
  rw [mul_pow, ← ENNReal.rpow_natCast (_ ^ _), ← ENNReal.rpow_mul, hexp]
  gcongr

/-- **The lower density estimate for the perimeter measure.** Let `E` have dimension `n ≥ 2`, let
`p = n / (n - 1)` and let `ω = μ(ball 0 1)`. At a point `x` of the reduced boundary of `s` in `Ω`,
for every `t > 1` and every small `r > 0`,

`r ^ (n - 1) ≤ ((1 + t) n C) ^ (n - 1) 2 ^ (n + 1) ω ^ (-1/n) |Dχ_s| (closedBall x r)`,

where `C` is the constant `MeasureTheory.eLpNormLESNormFDerivOneConst μ p` of the
Gagliardo–Nirenberg–Sobolev inequality. -/
theorem eventually_ofReal_pow_le_mul_variationMeasure_closedBall
    (hp : NNReal.HolderConjugate (finrank ℝ E) p) (hx : x ∈ reducedBoundary μ Ω s) {t : ℝ≥0}
    (ht : 1 < t) :
    ∀ᶠ r in 𝓝[>] 0, ENNReal.ofReal (r ^ (finrank ℝ E - 1)) ≤
      ((1 + t) * finrank ℝ E * eLpNormLESNormFDerivOneConst μ p : ℝ≥0) ^ (finrank ℝ E - 1) *
        ENNReal.ofReal (2 ^ (finrank ℝ E + 1) / μ.real (ball 0 1) ^ (finrank ℝ E : ℝ)⁻¹) *
          variationMeasure μ Ω (s.indicator 1) (((↑) : Ω → E) ⁻¹' closedBall x r) := by
  obtain ⟨hu, hfin⟩ := locallyIntegrableOn_and_totalVariationOn_ne_top_of_mem_reducedBoundary hx
  obtain ⟨ε, hε, hεΩ⟩ :=
    nhds_basis_closedBall.mem_iff.1 (Ω.isOpen.mem_nhds (reducedBoundary_subset hx))
  filter_upwards [eventually_ofReal_pow_le_mul_perimeter_ball hp hx ht, Ioo_mem_nhdsGT hε]
    with r h hr
  refine h.trans (mul_le_mul_right ?_ _)
  rw [perimeter_def, ← variationMeasure_preimage_coe hu hfin (U := ⟨ball x r, isOpen_ball⟩)
    fun y hy => hεΩ (closedBall_subset_closedBall hr.2.le (ball_subset_closedBall hy))]
  exact measure_mono (preimage_mono ball_subset_closedBall)

/-- **The reduced boundary lies in the essential boundary.** Let `E` have dimension `n ≥ 2` and
let `μ` be an additive Haar measure. At a point of the reduced boundary of `s` in an open set `Ω`,
`s` has neither density zero nor density one. -/
theorem reducedBoundary_subset_essentialBoundary (hn : 2 ≤ finrank ℝ E) :
    reducedBoundary μ Ω s ⊆ essentialBoundary μ s := by
  intro x hx
  set q := NNReal.conjExponent (finrank ℝ E)
  have hp : NNReal.HolderConjugate (finrank ℝ E) q := .conjExponent (by exact_mod_cast hn)
  have hc : (((1 + 2) * finrank ℝ E * eLpNormLESNormFDerivOneConst μ q : ℝ≥0) : ℝ≥0∞) ^
      finrank ℝ E ≠ ∞ := ENNReal.pow_ne_top ENNReal.coe_ne_top
  rw [mem_essentialBoundary, mem_essentialInterior, mem_essentialExterior]
  refine ⟨fun h1 => ?_,
    not_hasDensityAt_zero_of_eventually_ofReal_pow_le_mul_measure_inter_ball hc
      (eventually_ofReal_pow_le_mul_measure_inter_ball hp hx one_lt_two)⟩
  -- Density one of `s` is density one of the null-measurable `s ∩ Ω`, and hence density zero of
  -- its complement, which contains `ball x r \ s` for small `r`.
  have hs := nullMeasurableSet_inter_of_mem_reducedBoundary hx
  obtain ⟨ε, hε, hεΩ⟩ :=
    nhds_basis_closedBall.mem_iff.1 (Ω.isOpen.mem_nhds (reducedBoundary_subset hx))
  have h1' : HasDensityAt μ (s ∩ Ω) x 1 := by
    refine hasDensityAt_iff.2 ((hasDensityAt_iff.1 h1).congr' ?_)
    filter_upwards [Ioo_mem_nhdsGT hε] with r hr
    rw [inter_assoc, inter_eq_right.2 ((closedBall_subset_closedBall hr.2.le).trans hεΩ)]
  refine not_hasDensityAt_zero_of_eventually_ofReal_pow_le_mul_measure_inter_ball hc ?_
    (by simpa using h1'.compl hs (Metric.eventually_measure_closedBall_ne_zero_ne_top μ x))
  filter_upwards [eventually_ofReal_pow_le_mul_measure_ball_sdiff hp hx one_lt_two] with r hr
  refine hr.trans ?_
  gcongr
  exact fun y hy => ⟨.inl hy.2, hy.1⟩

end TauCeti
