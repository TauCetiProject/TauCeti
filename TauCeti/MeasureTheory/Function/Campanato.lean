/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import TauCeti.MeasureTheory.Function.PreciseRepresentative
import Mathlib.Analysis.Convex.Integral
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Integral.Average
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.MeasureTheory.Measure.OpenPos
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
measures (by `TauCeti.norm_setAverage_sub_le_of_subset` and
`MeasureTheory.Measure.addHaar_real_closedBall_div_le`). Summing over dyadic radii shows that
the averages `f_{x,r}` converge as `r → 0`, with `‖f_{x,r} - f*(x)‖ ≤ 2ⁿ / (1 - 2^(-α)) · M r^α`,
and comparing the averages over `closedBall y d ⊆ closedBall x (2 d)`, `d = dist x y`, then gives
the Hölder bound.

## Main declarations

All declarations are in the `TauCeti.MeasureTheory` namespace.

* `setAverage_norm_sub_setAverage_le_of_holderOnWith`: the mean oscillation of an `α`-Hölder
  function on a ball of radius `r` is at most a multiple of `r^α`.
* `tendsto_setAverage_closedBall_preciseRepresentative_of_setAverage_norm_sub_le`: mean
  oscillation decaying like `r^α` at `x` makes the averages converge at `x`.
* `norm_setAverage_closedBall_sub_preciseRepresentative_le`: the rate of that convergence.
* `dist_preciseRepresentative_le_of_setAverage_norm_sub_le`: the local Hölder estimate between
  two points, from mean oscillation bounds on balls of radius comparable to their distance.
* `dist_preciseRepresentative_le_of_forall_setAverage_norm_sub_le`: the Hölder estimate on a set
  `S` for `f ∈ L²(s)`, from mean oscillation bounds on balls of radius at most `R` centred in `S`,
  with an extra term `R^{-n/2-α} ‖f‖_{L²(s)}` for distant points.
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

section Holder

variable {X F : Type*} [MetricSpace X] [MeasurableSpace X] [ProperSpace X]
  [OpensMeasurableSpace X] {μ : Measure X} [IsFiniteMeasureOnCompacts μ] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [CompleteSpace F] {f : X → F} {x : X}

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

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {f : E → F} {x : E} {M α ρ : ℝ}

/-- For `α > 0`, `1 - 2^(-α)` is positive: the dyadic series of ratio `2^(-α)` converges. -/
private lemma one_sub_two_rpow_neg_pos (hα : 0 < α) : 0 < 1 - (2 : ℝ) ^ (-α) :=
  sub_pos.2 (Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (neg_lt_zero.2 hα))

/-- Comparing the averages over `closedBall y ε ⊆ closedBall x r` for `r ≤ 2 ε` costs at most
`2ⁿ` times the mean oscillation on `closedBall x r`. -/
private lemma norm_setAverage_closedBall_sub_le_of_le_two_mul {y : E} {ε r : ℝ} (hε : 0 < ε)
    (hsub : closedBall y ε ⊆ closedBall x r) (hrε : r ≤ 2 * ε)
    (hf : IntegrableOn f (closedBall x r) μ)
    (hosc : ⨍ z in closedBall x r, ‖f z - ⨍ w in closedBall x r, f w ∂μ‖ ∂μ ≤ M * r ^ α) :
    ‖(⨍ z in closedBall y ε, f z ∂μ) - ⨍ z in closedBall x r, f z ∂μ‖ ≤
      2 ^ finrank ℝ E * (M * r ^ α) := by
  have hr : 0 ≤ r := dist_nonneg.trans (mem_closedBall.1 (hsub (mem_closedBall_self hε.le)))
  exact (norm_setAverage_sub_le_of_subset hsub (measure_closedBall_pos μ y hε).ne'
    measure_closedBall_lt_top.ne hf _).trans <|
    mul_le_mul (μ.addHaar_real_closedBall_div_le x y hε hr hrε) hosc
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
  have hq := one_sub_two_rpow_neg_pos hα
  have hC : 2 ^ finrank ℝ E ≤ C :=
    le_div_self (by positivity) hq (sub_le_self _ (Real.rpow_pos_of_pos two_pos _).le)
  have hCq : C * 2 ^ (-α) + 2 ^ finrank ℝ E = C := by
    simp only [C]
    field_simp [hq.ne']
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
      · exact (norm_setAverage_closedBall_sub_le_of_le_two_mul hε
          (closedBall_subset_closedBall h₂) (by linarith) (hint r hrρ) (hosc r hr hrρ)).trans
          (mul_le_mul_of_nonneg_right hC (hM r hr hrρ))
      have h₃ := ih (r / 2) (by positivity) (by linarith) ε
        (by rwa [div_div, ← pow_succ']) h.le
      have h₄ := norm_setAverage_closedBall_sub_le_of_le_two_mul (half_pos hr)
        (closedBall_subset_closedBall (half_le_self hr.le)) (by linarith) (hint r hrρ)
        (hosc r hr hrρ)
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
  calc r / 2 ^ k = (1 / 2) ^ k * r := by rw [one_div_pow]; ring
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
  -- Pass from `x` to `y` through the averages over `closedBall x (2 d) ⊇ closedBall y d`.
  have hsub : closedBall y d ⊆ closedBall x (2 * d) :=
    closedBall_subset_closedBall' (by rw [dist_comm]; linarith)
  have h₁ := norm_setAverage_closedBall_sub_preciseRepresentative_le hα hf hoscx
    (by positivity) le_rfl
  have h₂ := norm_setAverage_closedBall_sub_preciseRepresentative_le hα (hf.mono_set hsub) hoscy
    hd le_rfl
  have h₃ : ‖(⨍ z in closedBall y d, f z ∂μ) - ⨍ z in closedBall x (2 * d), f z ∂μ‖ ≤
      2 ^ finrank ℝ E * (M * (2 * d) ^ α) :=
    norm_setAverage_closedBall_sub_le_of_le_two_mul hd hsub le_rfl hf
      (hoscx _ (by positivity) le_rfl)
  have hCq : 2 ^ α * 2 ^ finrank ℝ E = C * (2 ^ α - 1) := by
    simp only [C]
    field_simp [(one_sub_two_rpow_neg_pos hα).ne']
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
  have hC : (0 : ℝ) ≤ 2 * 2 ^ (α : ℝ) * (2 ^ finrank ℝ E / (1 - 2 ^ (-(α : ℝ)))) :=
    mul_nonneg (by positivity) (div_nonneg (by positivity) (one_sub_two_rpow_neg_pos hα').le)
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
    rw [havg, average_congr (ae_restrict_of_ae (hfg.mono fun y hy ↦ by rw [hy]))]
    refine (setAverage_norm_sub_setAverage_le_of_holderOnWith hα
      (measure_closedBall_pos μ x hr).ne' (hg.holderOnWith _)).trans_eq ?_
    push_cast
    rw [Real.mul_rpow zero_le_two hr.le]
    ring
  · rintro ⟨M, hM⟩
    exact ⟨_, _, holderWith_preciseRepresentative_of_setAverage_norm_sub_le hα hf hM,
      ae_eq_preciseRepresentative hf⟩

omit [CompleteSpace F] in
/-- **Mean oscillation from square mean oscillation.** Let `f ∈ L²(s)` with `ball x t ⊆ s` and
`t > 0`. If `∫_{ball x t} ‖f - f_{ball x t}‖² ≤ M² t^{n+2α}`, where `n` is the dimension and
`M ≥ 0`, then the mean oscillation of `f` on `closedBall x t` is at most `ω^{-1/2} M t^α`, where
`ω` is the measure of the unit ball. -/
theorem setAverage_norm_sub_le_of_setIntegral_norm_sub_sq_le {s : Set E} {t : ℝ}
    (hf : MemLp f 2 (μ.restrict s)) (hball : ball x t ⊆ s) (ht : 0 < t) (hM : 0 ≤ M)
    (hosc : ∫ y in ball x t, ‖f y - ⨍ z in ball x t, f z ∂μ‖ ^ 2 ∂μ ≤
      M ^ 2 * t ^ ((finrank ℝ E : ℝ) + 2 * α)) :
    ⨍ y in closedBall x t, ‖f y - ⨍ z in closedBall x t, f z ∂μ‖ ∂μ ≤
      (√(μ.real (ball (0 : E) 1)))⁻¹ * M * t ^ α := by
  have hω : 0 < μ.real (ball (0 : E) 1) := measureReal_ball_pos μ _ one_pos
  -- The averages over `closedBall x t` and `ball x t` agree.
  rw [Measure.restrict_congr_set (μ.addHaar_closedBall_ae_eq_ball_of_ne_zero x t ht.ne')]
  -- Jensen's inequality bounds the mean oscillation by the square mean oscillation.
  have hJ : (⨍ y in ball x t, ‖f y - ⨍ z in ball x t, f z ∂μ‖ ∂μ) ^ 2 ≤
      (∫ y in ball x t, ‖f y - ⨍ z in ball x t, f z ∂μ‖ ^ 2 ∂μ) / μ.real (ball x t) := by
    rw [div_eq_inv_mul, ← smul_eq_mul, ← setAverage_eq]
    exact sq_setAverage_norm_le_setAverage_norm_sq (measure_ball_pos μ x ht).ne'
      measure_ball_lt_top.ne ((hf.integrableOn_of_subset one_le_two hball
        measure_ball_lt_top.ne).sub (integrableOn_const measure_ball_lt_top.ne))
      (hf.integrableOn_norm_sub_sq_of_subset hball measure_ball_lt_top.ne _)
  rw [← pow_le_pow_iff_left₀ (average_nonneg fun _ ↦ norm_nonneg _) (by positivity) two_ne_zero]
  refine hJ.trans ?_
  rw [μ.addHaar_real_ball_of_pos x ht, div_le_iff₀ (by positivity)]
  refine hosc.trans_eq ?_
  rw [Real.rpow_add ht, Real.rpow_natCast, mul_comm 2 α, Real.rpow_mul ht.le, Real.rpow_two,
    mul_pow, mul_pow, inv_pow, Real.sq_sqrt hω.le]
  field_simp

/-- **A bound on the precise representative.** Let `α > 0`, `R > 0` and `f ∈ L²(s)` with
`ball x R ⊆ s`. If the mean oscillation of `f` on `closedBall x t` is at most `M t^α` for
`0 < t ≤ R`, then
`‖f*(x)‖ ≤ (2ⁿ / (1 - 2^(-α)) · M + ω^{-1/2} R^{-n/2-α} ‖f‖_{L²(s)}) R^α`, where `f*` is the
precise representative, `n` is the dimension and `ω` is the measure of the unit ball. -/
theorem norm_preciseRepresentative_le_of_setAverage_norm_sub_le {s : Set E}
    (f : Lp F 2 (μ.restrict s)) (hα : 0 < α) {R : ℝ} (hR : 0 < R) (hball : ball x R ⊆ s)
    (hosc : ∀ t, 0 < t → t ≤ R →
      ⨍ y in closedBall x t, ‖f y - ⨍ z in closedBall x t, f z ∂μ‖ ∂μ ≤ M * t ^ α) :
    ‖preciseRepresentative μ (f : E → F) x‖ ≤
      (2 ^ finrank ℝ E / (1 - 2 ^ (-α)) * M +
        (√(μ.real (ball (0 : E) 1)))⁻¹ * (R ^ (-((finrank ℝ E : ℝ) / 2 + α)) * ‖f‖)) *
        R ^ α := by
  have hint : IntegrableOn f (closedBall x R) μ :=
    ((Lp.memLp f).integrableOn_of_subset one_le_two hball measure_ball_lt_top.ne).congr_set_ae
      (μ.addHaar_closedBall_ae_eq_ball_of_ne_zero x R hR.ne')
  have hω : 0 < μ.real (ball (0 : E) 1) := measureReal_ball_pos μ _ one_pos
  -- Compare the precise representative with the average over `closedBall x R`.
  have h1 := norm_setAverage_closedBall_sub_preciseRepresentative_le hα hint hosc hR le_rfl
  -- Hölder's bound `‖⨍_B f‖ ≤ |B|^{-1/2} ‖f‖_{L²(B)}` on the average, with
  -- `‖f‖_{L²(B)} ≤ ‖f‖_{L²(s)}`.
  have h2 : ‖⨍ y in closedBall x R, f y ∂μ‖ ≤
      (√(μ.real (ball (0 : E) 1)))⁻¹ * (R ^ (-(finrank ℝ E : ℝ) / 2) * ‖f‖) := by
    rw [Measure.restrict_congr_set (μ.addHaar_closedBall_ae_eq_ball_of_ne_zero x R hR.ne')]
    have h := (enorm_setAverage_le (f := f) (mu := μ) (p := 2) one_le_two
      ENNReal.ofNat_ne_top).trans
      (mul_le_mul' le_rfl (eLpNorm_mono_measure _ (Measure.restrict_mono hball le_rfl)))
    replace h := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_ne_zero
      (measure_ball_pos μ x hR).ne' measure_ball_lt_top.ne) (Lp.eLpNorm_ne_top _)) h
    rw [toReal_enorm, ENNReal.toReal_mul, ← Lp.norm_def, ← ENNReal.toReal_rpow,
      ← measureReal_def, μ.addHaar_real_ball_of_pos x hR] at h
    refine h.trans_eq ?_
    rw [ENNReal.toReal_ofNat, Real.mul_rpow (by positivity) hω.le, ← Real.rpow_natCast,
      ← Real.rpow_mul hR.le, Real.sqrt_eq_rpow, ← Real.rpow_neg hω.le]
    ring_nf
  have haR : R ^ (-(finrank ℝ E : ℝ) / 2) * ‖f‖ =
      R ^ (-((finrank ℝ E : ℝ) / 2 + α)) * ‖f‖ * R ^ α := by
    rw [mul_right_comm, ← Real.rpow_add hR]
    congr 2
    ring
  rw [haR] at h2
  have h3 := norm_sub_le (⨍ y in closedBall x R, f y ∂μ)
    ((⨍ y in closedBall x R, f y ∂μ) - preciseRepresentative μ f x)
  rw [sub_sub_cancel] at h3
  calc _ ≤ _ := h3
    _ ≤ _ := add_le_add h2 h1
    _ = _ := by ring

/-- **Campanato's estimate on a set.** Let `α > 0`, `R > 0`, `M ≥ 0` and `f ∈ L²(s)`. If
`ball z R ⊆ s` and the mean oscillation of `f` on `closedBall z t` is at most `M t^α` for every
`z ∈ S` and `0 < t ≤ R`, then the precise representative of `f` satisfies
`‖f*(x) - f*(y)‖ ≤ c (M + R^{-n/2-α} ‖f‖_{L²(s)}) dist x y ^ α` for `x, y ∈ S`, where `n` is the
dimension and `c = 2 · 2^α (2ⁿ / (1 - 2^(-α)) + ω^{-1/2})`, with `ω` the measure of the unit
ball. -/
theorem dist_preciseRepresentative_le_of_forall_setAverage_norm_sub_le {s S : Set E}
    (f : Lp F 2 (μ.restrict s)) (hα : 0 < α) {R : ℝ} (hR : 0 < R) (hM : 0 ≤ M)
    (hball : ∀ z ∈ S, ball z R ⊆ s)
    (hosc : ∀ z ∈ S, ∀ t, 0 < t → t ≤ R →
      ⨍ y in closedBall z t, ‖f y - ⨍ w in closedBall z t, f w ∂μ‖ ∂μ ≤ M * t ^ α)
    {y : E} (hx : x ∈ S) (hy : y ∈ S) :
    dist (preciseRepresentative μ (f : E → F) x) (preciseRepresentative μ (f : E → F) y) ≤
      2 * 2 ^ α * (2 ^ finrank ℝ E / (1 - 2 ^ (-α)) + (√(μ.real (ball (0 : E) 1)))⁻¹) *
        (M + R ^ (-((finrank ℝ E : ℝ) / 2 + α)) * ‖f‖) * dist x y ^ α := by
  obtain ⟨cα, hcαdef⟩ : ∃ cα : ℝ, cα = 2 ^ finrank ℝ E / (1 - 2 ^ (-α)) := ⟨_, rfl⟩
  have hcα0 : 0 ≤ cα := hcαdef ▸ div_nonneg (by positivity) (one_sub_two_rpow_neg_pos hα).le
  obtain ⟨ω', hω'⟩ : ∃ ω', ω' = (√(μ.real (ball (0 : E) 1)))⁻¹ := ⟨_, rfl⟩
  have hω'0 : 0 ≤ ω' := hω' ▸ by positivity
  obtain ⟨a, ha⟩ : ∃ a, a = R ^ (-((finrank ℝ E : ℝ) / 2 + α)) * ‖f‖ := ⟨_, rfl⟩
  have ha0 : 0 ≤ a := ha ▸ by positivity
  rw [← hcαdef, ← hω', ← ha]
  have hd0 : 0 ≤ dist x y ^ α := by positivity
  rcases le_or_gt (2 * dist x y) R with hd | hd
  · -- Nearby points: the local Campanato estimate.
    have hint : IntegrableOn f (closedBall x (2 * dist x y)) μ := by
      rcases hd.lt_or_eq with hd | hd
      · exact (Lp.memLp f).integrableOn_of_subset one_le_two
          ((closedBall_subset_ball hd).trans (hball x hx)) measure_closedBall_lt_top.ne
      · rw [hd]
        exact ((Lp.memLp f).integrableOn_of_subset one_le_two (hball x hx)
          measure_ball_lt_top.ne).congr_set_ae
          (μ.addHaar_closedBall_ae_eq_ball_of_ne_zero x R hR.ne')
    have h := dist_preciseRepresentative_le_of_setAverage_norm_sub_le hα hint
      (fun r hr hr' ↦ hosc x hx r hr (hr'.trans hd))
      (fun r hr hr' ↦ hosc y hy r hr (by linarith [dist_nonneg (x := x) (y := y)]))
    rw [← hcαdef] at h
    refine h.trans ?_
    have : 0 ≤ 2 * 2 ^ α * (ω' * M + (cα + ω') * a) * dist x y ^ α := by positivity
    nlinarith
  · -- Distant points: both values are controlled by averages over balls of radius `R`.
    have hbound : ∀ z ∈ S, ‖preciseRepresentative μ (f : E → F) z‖ ≤
        (cα + ω') * (M + a) * R ^ α := fun z hz ↦ by
      refine (norm_preciseRepresentative_le_of_setAverage_norm_sub_le f hα hR (hball z hz)
        (hosc z hz)).trans ?_
      rw [← hcαdef, ← hω', ← ha]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      nlinarith [mul_nonneg hω'0 hM, mul_nonneg hcα0 ha0]
    have hRd : R ^ α ≤ 2 ^ α * dist x y ^ α := by
      rw [← Real.mul_rpow zero_le_two dist_nonneg]
      exact Real.rpow_le_rpow hR.le hd.le hα.le
    have hsum := dist_le_norm_add_norm (preciseRepresentative μ (f : E → F) x)
      (preciseRepresentative μ (f : E → F) y)
    have hc : 0 ≤ (cα + ω') * (M + a) := by positivity
    have := mul_le_mul_of_nonneg_left hRd hc
    nlinarith [hbound x hx, hbound y hy]

end MeasureTheory

end TauCeti
