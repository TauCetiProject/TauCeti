/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import TauCeti.MeasureTheory.Function.PreciseRepresentative
import Mathlib.Analysis.Convex.Integral
import TauCeti.Topology.MetricSpace.Holder

/-!
# Campanato's characterization of Hölder continuity

Let `μ` be an additive Haar measure on a finite-dimensional real normed space `E` of dimension
`n`, and let `0 < α`. For a locally integrable `f : E → F`, write `f_{x,r}` for its average over
`closedBall x r`, and call `⨍_{closedBall x r} ‖f - f_{x,r}‖` its *mean oscillation* on that
ball. **Campanato's theorem** says that `f` agrees almost everywhere with an `α`-Hölder function
exactly when its mean oscillation on balls of radius `r` is `O(r^α)`. The Hölder representative
is the precise representative `TauCeti.MeasureTheory.preciseRepresentative μ f`, the limit of the
averages `f_{x,r}` as `r → 0`.

The hypothesis controls an integral average rather than an essential supremum, so it is much
weaker than the oscillation bound behind `TauCeti.MeasureTheory.holderOnWith_preciseRepresentative`.
This is the form in which energy estimates deliver regularity: Poincaré's inequality turns a
growth bound on `∫_{closedBall x r} ‖∇u‖ᵖ` (Morrey's Dirichlet growth condition) into such a mean
oscillation bound, and the Campanato approach to the Schauder estimates compares a solution with
solutions of a constant-coefficient problem in the same integral norms.

The proof is a telescoping argument. Comparing the averages over `closedBall x r` and
`closedBall x (r / 2)` costs at most `2ⁿ M r^α`, the factor `2ⁿ` being the ratio of the two
measures. Summing over dyadic radii shows that the averages `f_{x,r}` converge as `r → 0`, with
`‖f_{x,r} - f*(x)‖ ≤ 2ⁿ / (1 - 2^(-α)) · M r^α`, and comparing the averages over
`closedBall y d ⊆ closedBall x (2 d)`, `d = dist x y`, then gives the Hölder bound.

## Main declarations

All declarations are in the `TauCeti.MeasureTheory` namespace.

* `norm_setAverage_sub_le_of_subset`: the average over a subset `s ⊆ t` differs from a constant
  `c` by at most `μ t / μ s` times the average of `‖f - c‖` over `t`.
* `setAverage_norm_sub_setAverage_le_of_holderOnWith`: the mean oscillation of an `α`-Hölder
  function on a ball of radius `r` is at most a multiple of `r^α`.
* `tendsto_setAverage_closedBall_preciseRepresentative_of_setAverage_norm_sub_le`: mean
  oscillation decaying like `r^α` at `x` makes the averages converge at `x`.
* `norm_setAverage_closedBall_sub_preciseRepresentative_le`: the rate of that convergence.
* `dist_preciseRepresentative_le_of_setAverage_norm_sub_le`: the local Hölder estimate between
  two points, from mean oscillation bounds on balls of radius comparable to their distance.
* `holderWith_preciseRepresentative_of_setAverage_norm_sub_le`: **Campanato's theorem** on the
  whole space.
* `exists_holderWith_ae_eq_iff_forall_setAverage_norm_sub_le`: a locally integrable function
  agrees almost everywhere with an `α`-Hölder function if and only if its mean oscillation on
  balls of radius `r` is `O(r^α)`.

## References

* S. Campanato, *Proprietà di hölderianità di alcune classi di funzioni*, Ann. Scuola Norm. Sup.
  Pisa (3) 17 (1963), 175–188.
* M. Giaquinta, L. Martinazzi, *An Introduction to the Regularity Theory for Elliptic Systems,
  Harmonic Maps and Minimal Graphs*, Theorem 5.5.
* Q. Han, F. Lin, *Elliptic Partial Differential Equations*, Theorem 3.1.
-/

public section

noncomputable section

open Filter Metric Set Topology MeasureTheory Module
open scoped NNReal

namespace TauCeti

namespace MeasureTheory

section General

variable {X F : Type*} [MeasurableSpace X] {μ : Measure X} [NormedAddCommGroup F]
  [NormedSpace ℝ F] {f : X → F} {s t : Set X}

/-- The average of `f` over a subset `s` of `t` differs from a constant `c` by at most
`μ t / μ s` times the average of `‖f - c‖` over `t`. -/
theorem norm_setAverage_sub_le_of_subset [CompleteSpace F] (hst : s ⊆ t) (hs : μ s ≠ 0)
    (ht : μ t ≠ ⊤) (hf : IntegrableOn f t μ) (c : F) :
    ‖(⨍ x in s, f x ∂μ) - c‖ ≤ μ.real t / μ.real s * ⨍ x in t, ‖f x - c‖ ∂μ := by
  have hs' : μ s ≠ ⊤ := ne_top_of_le_ne_top ht (measure_mono hst)
  have hsr : 0 < μ.real s := ENNReal.toReal_pos hs hs'
  have htr : 0 < μ.real t := hsr.trans_le (measureReal_mono hst ht)
  have hfs : IntegrableOn f s μ := hf.mono_set hst
  have heq : (⨍ x in s, f x ∂μ) - c = ⨍ x in s, (f x - c) ∂μ := by
    rw [setAverage_fun_sub hfs (integrableOn_const hs'), setAverage_const hs hs']
  rw [heq, setAverage_eq, setAverage_eq, norm_smul, smul_eq_mul,
    Real.norm_of_nonneg (inv_nonneg.2 hsr.le), div_mul_eq_mul_div, mul_inv_cancel_left₀ htr.ne',
    div_eq_inv_mul]
  gcongr
  refine (norm_integral_le_integral_norm _).trans (setIntegral_mono_set ?_ ?_ hst.eventuallyLE)
  · exact (hf.sub (integrableOn_const ht)).norm
  · exact ae_of_all _ fun _ ↦ norm_nonneg _

section Holder

variable [CompleteSpace F] [MetricSpace X] [ProperSpace X] [OpensMeasurableSpace X]
  [IsFiniteMeasureOnCompacts μ] {x : X}

/-- **The mean oscillation of a Hölder function.** If `f` is `α`-Hölder continuous on
`closedBall x r` with constant `K`, `α > 0`, and this ball has positive measure, then the mean
oscillation of `f` on the ball is at most `K (2 r)^α`. -/
theorem setAverage_norm_sub_setAverage_le_of_holderOnWith {K α : ℝ≥0} {r : ℝ} (hα : 0 < α)
    (hμ : μ (closedBall x r) ≠ 0) (hf : HolderOnWith K α f (closedBall x r)) :
    ⨍ y in closedBall x r, ‖f y - ⨍ z in closedBall x r, f z ∂μ‖ ∂μ ≤
      K * (2 * r) ^ (α : ℝ) := by
  have hμ' : μ (closedBall x r) ≠ ⊤ := (isCompact_closedBall x r).measure_lt_top.ne
  have hcont := hf.continuousOn hα
  have hint : IntegrableOn f (closedBall x r) μ :=
    hcont.integrableOn_compact (isCompact_closedBall _ _)
  -- Every value of `f` on the ball lies within `K (2 r)^α` of every other one, hence of their
  -- average.
  have hpt : ∀ y ∈ closedBall x r,
      ‖f y - ⨍ z in closedBall x r, f z ∂μ‖ ≤ K * (2 * r) ^ (α : ℝ) := by
    intro y hy
    have hmem : ⨍ z in closedBall x r, f z ∂μ ∈ closedBall (f y) (K * (2 * r) ^ (α : ℝ)) := by
      refine (convex_closedBall _ _).set_average_mem isClosed_closedBall hμ hμ' ?_ hint
      filter_upwards [self_mem_ae_restrict measurableSet_closedBall] with z hz
      rw [mem_closedBall]
      refine (hf.dist_le hz hy).trans ?_
      gcongr
      calc dist z y ≤ dist z x + dist y x := dist_triangle_right _ _ _
        _ ≤ 2 * r := by linarith [mem_closedBall.1 hz, mem_closedBall.1 hy]
    rw [← dist_eq_norm, dist_comm]
    exact mem_closedBall.1 hmem
  refine (convex_Iic ((K : ℝ) * (2 * r) ^ (α : ℝ))).set_average_mem isClosed_Iic hμ hμ' ?_ ?_
  · filter_upwards [self_mem_ae_restrict measurableSet_closedBall] with y hy using hpt y hy
  · exact (hcont.sub continuousOn_const).norm.integrableOn_compact (isCompact_closedBall _ _)

end Holder

end General

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {f : E → F} {x : E} {M α ρ : ℝ}

/-- For Haar measure, a closed ball of radius `R ≤ 2 r` has at most `2ⁿ` times the measure of a
closed ball of radius `r`. -/
private lemma measureReal_closedBall_div_le {y : E} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hRr : R ≤ 2 * r) :
    μ.real (closedBall x R) / μ.real (closedBall y r) ≤ 2 ^ finrank ℝ E := by
  have hball : 0 < μ.real (ball (0 : E) 1) :=
    ENNReal.toReal_pos (measure_ball_pos μ 0 one_pos).ne' measure_ball_lt_top.ne
  rw [Measure.addHaar_real_closedBall μ x hR, Measure.addHaar_real_closedBall μ y hr.le,
    mul_div_mul_right _ _ hball.ne', div_le_iff₀ (by positivity), ← mul_pow]
  exact pow_le_pow_left₀ hR hRr _

/-- Comparing the averages over `closedBall x ε ⊆ closedBall x r` for `r ≤ 2 ε` costs at most
`2ⁿ` times the mean oscillation on `closedBall x r`. -/
private lemma norm_setAverage_closedBall_sub_le_of_le_two_mul {ε r : ℝ} (hε : 0 < ε)
    (hεr : ε ≤ r) (hrε : r ≤ 2 * ε) (hf : IntegrableOn f (closedBall x r) μ)
    (hosc : ⨍ y in closedBall x r, ‖f y - ⨍ z in closedBall x r, f z ∂μ‖ ∂μ ≤ M * r ^ α) :
    ‖(⨍ y in closedBall x ε, f y ∂μ) - ⨍ y in closedBall x r, f y ∂μ‖ ≤
      2 ^ finrank ℝ E * (M * r ^ α) :=
  (norm_setAverage_sub_le_of_subset (closedBall_subset_closedBall hεr)
    (measure_closedBall_pos μ x hε).ne' measure_closedBall_lt_top.ne hf _).trans <|
    mul_le_mul (measureReal_closedBall_div_le hε (hε.le.trans hεr) hrε) hosc
      (average_nonneg fun _ ↦ norm_nonneg _) (by positivity)

/-- **Telescoping over dyadic radii.** If the mean oscillation of `f` on `closedBall x r` is at
most `M r^α` for `0 < r ≤ ρ`, then the averages over `closedBall x ε` and `closedBall x r`,
`0 < ε ≤ r ≤ ρ`, differ by at most `2ⁿ / (1 - 2^(-α)) · M r^α`. -/
private lemma norm_setAverage_closedBall_sub_le (hα : 0 < α)
    (hf : IntegrableOn f (closedBall x ρ) μ)
    (hosc : ∀ r, 0 < r → r ≤ ρ →
      ⨍ y in closedBall x r, ‖f y - ⨍ z in closedBall x r, f z ∂μ‖ ∂μ ≤ M * r ^ α)
    {ε r : ℝ} (hε : 0 < ε) (hεr : ε ≤ r) (hrρ : r ≤ ρ) :
    ‖(⨍ y in closedBall x ε, f y ∂μ) - ⨍ y in closedBall x r, f y ∂μ‖ ≤
      2 ^ finrank ℝ E / (1 - 2 ^ (-α)) * (M * r ^ α) := by
  set C : ℝ := 2 ^ finrank ℝ E / (1 - 2 ^ (-α))
  have hq : (2 : ℝ) ^ (-α) < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (neg_lt_zero.2 hα)
  have hq0 : 0 < (2 : ℝ) ^ (-α) := Real.rpow_pos_of_pos two_pos _
  have hC : 2 ^ finrank ℝ E ≤ C := le_div_self (by positivity) (sub_pos.2 hq) (by linarith)
  have hCq : C * 2 ^ (-α) + 2 ^ finrank ℝ E = C := by
    simp only [C]
    field_simp [(sub_pos.2 hq).ne']
    ring
  have hM : ∀ r, 0 < r → r ≤ ρ → 0 ≤ M * r ^ α := fun r hr hrρ ↦
    (average_nonneg fun _ ↦ norm_nonneg _).trans (hosc r hr hrρ)
  have hint : ∀ r ≤ ρ, IntegrableOn f (closedBall x r) μ := fun r hrρ ↦
    hf.mono_set (closedBall_subset_closedBall hrρ)
  -- By induction on `k`, the bound holds for `r / 2 ^ k ≤ ε ≤ r`: either `ε ≥ r / 2`, and one
  -- step suffices, or `ε < r / 2`, and we pass through the average over `closedBall x (r / 2)`,
  -- the identity `C 2^(-α) + 2ⁿ = C` absorbing the extra step.
  have key : ∀ k : ℕ, ∀ r, 0 < r → r ≤ ρ → ∀ ε, r / 2 ^ k ≤ ε → ε ≤ r →
      ‖(⨍ y in closedBall x ε, f y ∂μ) - ⨍ y in closedBall x r, f y ∂μ‖ ≤ C * (M * r ^ α) := by
    intro k
    induction k with
    | zero =>
      intro r hr hrρ ε h₁ h₂
      obtain rfl : ε = r := le_antisymm h₂ (by simpa using h₁)
      simpa using mul_nonneg ((by positivity : (0 : ℝ) ≤ 2 ^ finrank ℝ E).trans hC)
        (hM ε hr hrρ)
    | succ k ih =>
      intro r hr hrρ ε h₁ h₂
      have hε : 0 < ε := (by positivity : 0 < r / 2 ^ (k + 1)).trans_le h₁
      rcases le_or_gt (r / 2) ε with h | h
      · exact (norm_setAverage_closedBall_sub_le_of_le_two_mul hε h₂ (by linarith) (hint r hrρ)
          (hosc r hr hrρ)).trans (mul_le_mul_of_nonneg_right hC (hM r hr hrρ))
      have h₃ := ih (r / 2) (by positivity) (by linarith) ε
        (by rwa [div_div, ← pow_succ']) h.le
      have h₄ := norm_setAverage_closedBall_sub_le_of_le_two_mul (x := x) (half_pos hr)
        (half_le_self hr.le) (by linarith) (hint r hrρ) (hosc r hr hrρ)
      calc ‖(⨍ y in closedBall x ε, f y ∂μ) - ⨍ y in closedBall x r, f y ∂μ‖
          ≤ ‖(⨍ y in closedBall x ε, f y ∂μ) - ⨍ y in closedBall x (r / 2), f y ∂μ‖ +
            ‖(⨍ y in closedBall x (r / 2), f y ∂μ) - ⨍ y in closedBall x r, f y ∂μ‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ C * (M * (r / 2) ^ α) + 2 ^ finrank ℝ E * (M * r ^ α) := add_le_add h₃ h₄
        _ = (C * 2 ^ (-α) + 2 ^ finrank ℝ E) * (M * r ^ α) := by
            rw [Real.div_rpow hr.le zero_le_two, Real.rpow_neg zero_le_two]
            ring
        _ = C * (M * r ^ α) := by rw [hCq]
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos hε (hε.trans_le hεr)) one_half_lt_one
  refine key k r (hε.trans_le hεr) hrρ ε ?_ hεr
  calc r / 2 ^ k = (1 / 2) ^ k * r := by rw [one_div, inv_pow, div_eq_mul_inv, mul_comm]
    _ ≤ ε := ((lt_div_iff₀ (hε.trans_le hεr)).1 hk).le

/-- **Mean oscillation decay gives convergence of the averages.** Let `α > 0` and `ρ > 0`. If `f`
is integrable on `closedBall x ρ` and its mean oscillation on `closedBall x r` is at most `M r^α`
for `0 < r ≤ ρ`, then the averages of `f` over the closed balls around `x` converge to the
precise representative of `f` at `x`. -/
theorem tendsto_setAverage_closedBall_preciseRepresentative_of_setAverage_norm_sub_le
    (hα : 0 < α) (hρ : 0 < ρ) (hf : IntegrableOn f (closedBall x ρ) μ)
    (hosc : ∀ r, 0 < r → r ≤ ρ →
      ⨍ y in closedBall x r, ‖f y - ⨍ z in closedBall x r, f z ∂μ‖ ∂μ ≤ M * r ^ α) :
    Tendsto (fun ε ↦ ⨍ y in closedBall x ε, f y ∂μ) (𝓝[>] 0)
      (𝓝 (preciseRepresentative μ f x)) := by
  set C : ℝ := 2 ^ finrank ℝ E / (1 - 2 ^ (-α))
  -- The averages form a Cauchy filter: those of radius at most `τ` lie within `C M τ^α` of the
  -- average of radius `τ`.
  have hcauchy : Cauchy (map (fun ε ↦ ⨍ y in closedBall x ε, f y ∂μ) (𝓝[>] (0 : ℝ))) := by
    refine Metric.cauchy_iff.2 ⟨inferInstance, fun δ hδ ↦ ?_⟩
    have h0 : Tendsto (fun r : ℝ ↦ C * (M * r ^ α)) (𝓝[>] 0) (𝓝 0) := by
      have h := ((Real.continuous_rpow_const hα.le).tendsto 0).mono_left
        (nhdsWithin_le_nhds (s := Ioi 0))
      simpa [Real.zero_rpow hα.ne'] using (h.const_mul M).const_mul C
    obtain ⟨τ, hτ, hτρ⟩ := ((h0.eventually (gt_mem_nhds (half_pos hδ))).and
      (Ioc_mem_nhdsGT hρ)).exists
    refine ⟨(fun ε ↦ ⨍ y in closedBall x ε, f y ∂μ) '' Ioc 0 τ,
      image_mem_map (Ioc_mem_nhdsGT hτρ.1), ?_⟩
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    calc dist (⨍ y in closedBall x a, f y ∂μ) (⨍ y in closedBall x b, f y ∂μ)
        ≤ dist (⨍ y in closedBall x a, f y ∂μ) (⨍ y in closedBall x τ, f y ∂μ) +
          dist (⨍ y in closedBall x b, f y ∂μ) (⨍ y in closedBall x τ, f y ∂μ) :=
          dist_triangle_right _ _ _
      _ ≤ C * (M * τ ^ α) + C * (M * τ ^ α) := by
          rw [dist_eq_norm, dist_eq_norm]
          exact add_le_add (norm_setAverage_closedBall_sub_le hα hf hosc ha.1 ha.2 hτρ.2)
            (norm_setAverage_closedBall_sub_le hα hf hosc hb.1 hb.2 hτρ.2)
      _ < δ := by linarith
  obtain ⟨v, hv⟩ := CompleteSpace.complete hcauchy
  rwa [preciseRepresentative_eq_of_tendsto hv]

/-- **The rate of convergence of the averages.** Let `α > 0`. If `f` is integrable on
`closedBall x ρ` and its mean oscillation on `closedBall x r` is at most `M r^α` for
`0 < r ≤ ρ`, then for `0 < r ≤ ρ` the average of `f` over `closedBall x r` lies within
`2ⁿ / (1 - 2^(-α)) · M r^α` of the precise representative of `f` at `x`, where `n` is the
dimension. -/
theorem norm_setAverage_closedBall_sub_preciseRepresentative_le (hα : 0 < α)
    (hf : IntegrableOn f (closedBall x ρ) μ)
    (hosc : ∀ r, 0 < r → r ≤ ρ →
      ⨍ y in closedBall x r, ‖f y - ⨍ z in closedBall x r, f z ∂μ‖ ∂μ ≤ M * r ^ α)
    {r : ℝ} (hr : 0 < r) (hrρ : r ≤ ρ) :
    ‖(⨍ y in closedBall x r, f y ∂μ) - preciseRepresentative μ f x‖ ≤
      2 ^ finrank ℝ E / (1 - 2 ^ (-α)) * (M * r ^ α) := by
  have ht := tendsto_setAverage_closedBall_preciseRepresentative_of_setAverage_norm_sub_le hα
    (hr.trans_le hrρ) hf hosc
  refine le_of_tendsto (tendsto_const_nhds.sub ht).norm ?_
  filter_upwards [Ioc_mem_nhdsGT hr] with ε hε
  rw [norm_sub_rev]
  exact norm_setAverage_closedBall_sub_le hα hf hosc hε.1 hε.2 hrρ

/-- **The local Campanato estimate.** Let `α > 0` and `d = dist x y`. If `f` has mean oscillation
at most `M r^α` on `closedBall x r` for `0 < r ≤ 2 d` and on `closedBall y r` for `0 < r ≤ d`,
and is integrable on `closedBall x (2 d)`, then the precise representatives of `f` at `x`
and `y` differ by at most `2 · 2^α · 2ⁿ / (1 - 2^(-α)) · M d^α`, where `n` is the dimension. -/
theorem dist_preciseRepresentative_le_of_setAverage_norm_sub_le {y : E}
    (hα : 0 < α) (hf : IntegrableOn f (closedBall x (2 * dist x y)) μ)
    (hoscx : ∀ r, 0 < r → r ≤ 2 * dist x y →
      ⨍ z in closedBall x r, ‖f z - ⨍ w in closedBall x r, f w ∂μ‖ ∂μ ≤ M * r ^ α)
    (hoscy : ∀ r, 0 < r → r ≤ dist x y →
      ⨍ z in closedBall y r, ‖f z - ⨍ w in closedBall y r, f w ∂μ‖ ∂μ ≤ M * r ^ α) :
    dist (preciseRepresentative μ f x) (preciseRepresentative μ f y) ≤
      2 * 2 ^ α * (2 ^ finrank ℝ E / (1 - 2 ^ (-α))) * (M * dist x y ^ α) := by
  rcases eq_or_ne x y with rfl | hxy
  · simp [Real.zero_rpow hα.ne']
  set d := dist x y
  set C : ℝ := 2 ^ finrank ℝ E / (1 - 2 ^ (-α))
  have hd : 0 < d := dist_pos.2 hxy
  have hq : (2 : ℝ) ^ (-α) < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (neg_lt_zero.2 hα)
  -- Pass from `x` to `y` through the averages over `closedBall x (2 d) ⊇ closedBall y d`.
  have hsub : closedBall y d ⊆ closedBall x (2 * d) :=
    closedBall_subset_closedBall' (by rw [dist_comm]; linarith)
  have h₁ := norm_setAverage_closedBall_sub_preciseRepresentative_le hα hf hoscx
    (by positivity) le_rfl
  have h₂ := norm_setAverage_closedBall_sub_preciseRepresentative_le hα (hf.mono_set hsub) hoscy
    hd le_rfl
  have h₃ : ‖(⨍ z in closedBall y d, f z ∂μ) - ⨍ z in closedBall x (2 * d), f z ∂μ‖ ≤
      2 ^ finrank ℝ E * (M * (2 * d) ^ α) :=
    (norm_setAverage_sub_le_of_subset hsub (measure_closedBall_pos μ y hd).ne'
      measure_closedBall_lt_top.ne hf _).trans <|
      mul_le_mul (measureReal_closedBall_div_le hd (by positivity) le_rfl) (hoscx _ (by positivity)
        le_rfl) (average_nonneg fun _ ↦ norm_nonneg _) (by positivity)
  have hCq : 2 ^ α * 2 ^ finrank ℝ E = C * (2 ^ α - 1) := by
    simp only [C]
    field_simp [(sub_pos.2 hq).ne']
    rw [Real.rpow_neg zero_le_two]
    field_simp
  rw [dist_eq_norm]
  calc ‖preciseRepresentative μ f x - preciseRepresentative μ f y‖
      ≤ ‖preciseRepresentative μ f x - ⨍ z in closedBall x (2 * d), f z ∂μ‖ +
        ‖(⨍ z in closedBall x (2 * d), f z ∂μ) - ⨍ z in closedBall y d, f z ∂μ‖ +
        ‖(⨍ z in closedBall y d, f z ∂μ) - preciseRepresentative μ f y‖ :=
        (norm_sub_le_norm_sub_add_norm_sub _ (⨍ z in closedBall y d, f z ∂μ) _).trans
          (add_le_add_left (norm_sub_le_norm_sub_add_norm_sub _ _ _) _)
    _ ≤ C * (M * (2 * d) ^ α) + 2 ^ finrank ℝ E * (M * (2 * d) ^ α) + C * (M * d ^ α) := by
        refine add_le_add (add_le_add ?_ ?_) h₂ <;> rw [norm_sub_rev]
        exacts [h₁, h₃]
    _ = (2 ^ α * C + 2 ^ α * 2 ^ finrank ℝ E + C) * (M * d ^ α) := by
        rw [Real.mul_rpow zero_le_two hd.le]
        ring
    _ = 2 * 2 ^ α * C * (M * d ^ α) := by
        rw [hCq]
        ring

/-- **Campanato's theorem.** Let `α > 0`, and let `f` be locally integrable, with mean oscillation
on every closed ball of radius `r > 0` at most `M r^α`. Then the precise representative of `f`
is `α`-Hölder continuous, with constant `2 · 2^α · 2ⁿ / (1 - 2^(-α)) · M`, where `n` is the
dimension. It agrees with `f` almost everywhere
(`TauCeti.MeasureTheory.ae_eq_preciseRepresentative`). -/
theorem holderWith_preciseRepresentative_of_setAverage_norm_sub_le
    {α M : ℝ≥0} (hα : 0 < α) (hf : LocallyIntegrable f μ)
    (hosc : ∀ x r, 0 < r →
      ⨍ y in closedBall x r, ‖f y - ⨍ z in closedBall x r, f z ∂μ‖ ∂μ ≤ M * r ^ (α : ℝ)) :
    HolderWith (Real.toNNReal (2 * 2 ^ (α : ℝ) *
      (2 ^ finrank ℝ E / (1 - 2 ^ (-(α : ℝ))))) * M) α (preciseRepresentative μ f) := by
  have hα' : (0 : ℝ) < α := hα
  have hq : (2 : ℝ) ^ (-(α : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (neg_lt_zero.2 hα')
  have hC : (0 : ℝ) ≤ 2 * 2 ^ (α : ℝ) * (2 ^ finrank ℝ E / (1 - 2 ^ (-(α : ℝ)))) :=
    mul_nonneg (by positivity) (div_nonneg (by positivity) (sub_pos.2 hq).le)
  refine holderOnWith_univ.1 <| HolderOnWith.of_dist_le fun x _ y _ ↦ ?_
  rw [NNReal.coe_mul, Real.coe_toNNReal _ hC, mul_assoc]
  exact dist_preciseRepresentative_le_of_setAverage_norm_sub_le hα'
    (hf.integrableOn_isCompact (isCompact_closedBall _ _)) (fun r hr _ ↦ hosc x r hr)
    (fun r hr _ ↦ hosc y r hr)

/-- **Campanato's characterization of Hölder continuity.** Let `α > 0`. A locally integrable
function agrees almost everywhere with an `α`-Hölder continuous function if and only if its mean
oscillation on closed balls of radius `r > 0` is at most `M r^α` for some constant `M`. -/
theorem exists_holderWith_ae_eq_iff_forall_setAverage_norm_sub_le {α : ℝ≥0}
    (hα : 0 < α) (hf : LocallyIntegrable f μ) :
    (∃ (K : ℝ≥0) (g : E → F), HolderWith K α g ∧ f =ᵐ[μ] g) ↔
      ∃ M : ℝ≥0, ∀ x r, 0 < r →
        ⨍ y in closedBall x r, ‖f y - ⨍ z in closedBall x r, f z ∂μ‖ ∂μ ≤ M * r ^ (α : ℝ) := by
  constructor
  · rintro ⟨K, g, hg, hfg⟩
    refine ⟨K * 2 ^ (α : ℝ), fun x r hr ↦ ?_⟩
    -- The averages of `f` and `g` over every ball agree.
    have havg : ⨍ z in closedBall x r, f z ∂μ = ⨍ z in closedBall x r, g z ∂μ :=
      average_congr (ae_restrict_of_ae hfg)
    rw [havg, average_congr (ae_restrict_of_ae (hfg.mono fun y hy ↦ by rw [hy])),
      NNReal.coe_mul, NNReal.coe_rpow, NNReal.coe_ofNat, mul_assoc,
      ← Real.mul_rpow zero_le_two hr.le]
    exact setAverage_norm_sub_setAverage_le_of_holderOnWith hα
      (measure_closedBall_pos μ x hr).ne' (hg.holderOnWith _)
  · rintro ⟨M, hM⟩
    exact ⟨_, _, holderWith_preciseRepresentative_of_setAverage_norm_sub_le hα hf hM,
      ae_eq_preciseRepresentative hf⟩

end MeasureTheory

end TauCeti
