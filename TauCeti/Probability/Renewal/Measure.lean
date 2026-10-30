/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Group.ConvolutionPower
public import TauCeti.MeasureTheory.Measure.HalfLine
public import TauCeti.Probability.Renewal.Basic

/-!
# The renewal measure and the renewal function

Let `F` be the law of the increments of an ordinary renewal process, a probability measure on the
half-line `ℝ≥0`. The `n`-th additive convolution power of `F` is `F.convolutionPower n`, with
`F.convolutionPower 0 = δ₀` and `F.convolutionPower (n + 1) = F.convolutionPower n ∗ F`. This file
studies the renewal measure

```text
renewalMeasure F = ∑' n, F.convolutionPower n
```

and the renewal function

```text
renewalFunction F t = ∑' n, (F.convolutionPower (n + 1)) (Icc 0 t) = renewalMeasure F [0, t] - 1.
```

The `n`-th convolution power is the law of the `n`-th arrival time, so `renewalMeasure F [0, t]` is
`1 + renewalFunction F t`: the `1` is the artificial arrival at time zero and `renewalFunction F t`
is the expected number of genuine arrivals in `[0, t]`. Both endpoints of `[0, t]` are counted, so
this identity holds even when `F` has an atom at zero.

The main results are that `renewalMeasure F` satisfies the renewal equation `U = δ₀ + F ∗ U`, that
it is finite on bounded intervals, and that the renewal function is monotone and right-continuous,
with finite values when `F {0} < 1`. Local finiteness is where the hypothesis `F {0} < 1` enters,
and it cannot be dropped: if `F = δ₀` then every convolution power is `δ₀` again, so
`renewalMeasure F` gives infinite mass to every neighbourhood of zero.

## Main definitions

* `TauCeti.Probability.renewalMeasure` — the renewal measure `U = ∑' n, F.convolutionPower n`.
* `TauCeti.Probability.renewalFunction` — the renewal function `m t = ∑' n, F.convolutionPower
  (n + 1) [0, t]`.

## Main results

* `TauCeti.Probability.renewalMeasure_eq_dirac_zero_add_conv` — the renewal equation
  `U = δ₀ + F ∗ U` for an s-finite measure `F`.
* `TauCeti.Probability.renewalMeasure_Iic_lt_top` — `U` is finite on bounded intervals when
  `F {0} < 1`.
* `TauCeti.Probability.renewalMeasure_Icc_eq_one_add_renewalFunction` — `U [0, t] = 1 + m t`.
* `TauCeti.Probability.monotone_renewalFunction`,
  `TauCeti.Probability.continuousWithinAt_renewalFunction_Ici` — monotonicity and right
  continuity of `m`.
* `TauCeti.Probability.lintegral_renewalCount_eq_renewalFunction` — `m t` is the expected number
  of arrivals in `[0, t]`.

## References

* William Feller, *An Introduction to Probability Theory and Its Applications*, vol. II, 2nd
  edition, Wiley, 1971, Chapter XI, §1.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal MeasureTheory

namespace TauCeti.Probability

/-! ### The renewal measure -/

/-- The renewal measure `U = ∑ n, F ^ (∗n)` of a law `F` on the half-line, where `F ^ (∗0) = δ₀`
and `F ^ (∗(n + 1)) = F ^ (∗n) ∗ F`. Its mass on `[0, t]` is `1 + renewalFunction F t`. -/
noncomputable def renewalMeasure (F : Measure ℝ≥0) : Measure ℝ≥0 :=
  Measure.sum fun n => F.convolutionPower n

lemma renewalMeasure_def (F : Measure ℝ≥0) :
    renewalMeasure F = Measure.sum fun n => F.convolutionPower n := (rfl)

@[simp]
lemma renewalMeasure_apply (F : Measure ℝ≥0) {s : Set ℝ≥0} (hs : MeasurableSet s) :
    renewalMeasure F s = ∑' n, F.convolutionPower n s :=
  Measure.sum_apply _ hs

instance sfinite_renewalMeasure (F : Measure ℝ≥0) [SFinite F] : SFinite (renewalMeasure F) :=
  inferInstanceAs (SFinite (Measure.sum fun n => F.convolutionPower n))

/-- Splitting the term `n = 0` off the renewal measure leaves the point mass at zero. -/
theorem renewalMeasure_eq_dirac_zero_add_sum_succ (F : Measure ℝ≥0) :
    renewalMeasure F
      = Measure.dirac (0 : ℝ≥0) + Measure.sum fun n => F.convolutionPower (n + 1) := by
  ext s hs
  rw [renewalMeasure_apply F hs, Measure.add_apply, Measure.sum_apply _ hs,
    Measure.dirac_apply' (0 : ℝ≥0) hs]
  conv_lhs => rw [tsum_eq_zero_add' ENNReal.summable, Measure.convolutionPower_zero,
    Measure.dirac_apply' (0 : ℝ≥0) hs]

/-- **The renewal equation** `U = δ₀ + F ∗ U` for an s-finite measure `F` on the half-line: the
renewal measure is the point mass at zero together with one more increment convolution. -/
theorem renewalMeasure_eq_dirac_zero_add_conv (F : Measure ℝ≥0) [SFinite F] :
    renewalMeasure F = Measure.dirac (0 : ℝ≥0) + F ∗ renewalMeasure F := by
  have h : F ∗ renewalMeasure F = Measure.sum fun n => F.convolutionPower (n + 1) := by
    rw [renewalMeasure_def, Measure.conv_sum_right]
    exact congrArg Measure.sum (funext fun n => (F.convolutionPower_succ' n).symm)
  rw [h, renewalMeasure_eq_dirac_zero_add_sum_succ]

/-! ### The renewal function -/

/-- The renewal function `m t = ∑ n, F ^ (∗(n + 1)) [0, t]`, the expected number of arrivals in
`[0, t]`. Both endpoints are counted and the artificial arrival at zero is not, so
`renewalMeasure F [0, t] = 1 + m t`. -/
noncomputable def renewalFunction (F : Measure ℝ≥0) (t : ℝ≥0) : ℝ≥0∞ :=
  ∑' n, F.convolutionPower (n + 1) (Icc 0 t)

lemma renewalFunction_def (F : Measure ℝ≥0) (t : ℝ≥0) :
    renewalFunction F t = ∑' n, F.convolutionPower (n + 1) (Icc 0 t) := (rfl)

lemma renewalFunction_eq_measure_sum (F : Measure ℝ≥0) (t : ℝ≥0) :
    renewalFunction F t = (Measure.sum fun n => F.convolutionPower (n + 1)) (Icc 0 t) :=
  (Measure.sum_apply _ measurableSet_Icc).symm

@[simp]
lemma renewalFunction_eq_measure_sum_Iic (F : Measure ℝ≥0) (t : ℝ≥0) :
    renewalFunction F t = (Measure.sum fun n => F.convolutionPower (n + 1)) (Iic t) := by
  have h : Icc 0 t = Iic t := by
    ext s
    simp
  rw [renewalFunction_eq_measure_sum, h]

/-- The mass of the renewal measure on `[0, t]` is `1` plus the renewal function. -/
theorem renewalMeasure_Icc_eq_one_add_renewalFunction (F : Measure ℝ≥0) (t : ℝ≥0) :
    renewalMeasure F (Icc 0 t) = 1 + renewalFunction F t := by
  rw [renewalMeasure_eq_dirac_zero_add_sum_succ, Measure.add_apply, renewalFunction_eq_measure_sum,
    Measure.sum_apply _ measurableSet_Icc, Measure.dirac_apply' (0 : ℝ≥0) measurableSet_Icc]
  simp

/-- The renewal function is nondecreasing in time. -/
theorem monotone_renewalFunction (F : Measure ℝ≥0) : Monotone (renewalFunction F) := by
  intro s t hst
  exact ENNReal.tsum_le_tsum fun n => measure_mono (Icc_subset_Icc le_rfl hst)

/-! ### Local finiteness of the renewal measure -/

/-- **Local finiteness of the renewal measure.** If the increment law is not the point mass at
zero, the renewal measure is finite on every bounded interval. Without the hypothesis `F {0} < 1`
this fails: for `F = δ₀` every convolution power equals `δ₀`. -/
theorem renewalMeasure_Iic_lt_top (F : Measure ℝ≥0) [IsProbabilityMeasure F] (h0 : F {0} < 1)
    (t : ℝ≥0) : renewalMeasure F (Iic t) < ⊤ := by
  -- Split the increments into blocks of `k + 1`, where `k` is chosen with `t < (k + 1) * a` and
  -- `F` charges `[a, ∞)`. A block all of whose increments reach `a` already pushes the arrival
  -- past `t`, so each block multiplies the mass of `[0, t]` by at most the geometric factor
  -- `(F.convolutionPower (k + 1)) (Iic t) < 1`.
  obtain ⟨a, ha, hpa⟩ := Measure.exists_pos_measure_Ici h0
  obtain ⟨k, hk⟩ := exists_nat_gt (t / a)
  have h1 : t < (k : ℝ≥0) * a := by rwa [div_lt_iff₀ ha] at hk
  have hkt : t < ((k + 1 : ℕ) : ℝ≥0) * a := by
    refine lt_of_lt_of_le h1 ?_
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.2 (Nat.le_succ k)) zero_le
  set c : ℝ≥0∞ := F.convolutionPower (k + 1) (Iic t) with hc
  have hc1 : c < 1 := hc.symm ▸ Measure.convolutionPower_Iic_lt_one hpa hkt
  have hstep : ∀ q : ℕ, F.convolutionPower ((k + 1) * q) (Iic t) ≤ c ^ q := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
        rw [Nat.mul_succ, Measure.convolutionPower_add, pow_succ']
        exact (Measure.conv_Iic_le _ _ t).trans (mul_le_mul' le_rfl ih)
  have hbound : ∀ n : ℕ, F.convolutionPower n (Iic t) ≤ c ^ (n / (k + 1)) := by
    intro n
    have hn : (k + 1) * (n / (k + 1)) + n % (k + 1) = n := by
      rw [mul_comm]
      exact Nat.div_add_mod' n (k + 1)
    have hmono : F.convolutionPower (n % (k + 1)) (Iic t) ≤ 1 := by
      rw [← measure_univ (μ := F.convolutionPower (n % (k + 1)))]
      exact measure_mono (subset_univ _)
    calc F.convolutionPower n (Iic t)
        = F.convolutionPower ((k + 1) * (n / (k + 1)) + n % (k + 1)) (Iic t) := by rw [hn]
      _ = ((F.convolutionPower ((k + 1) * (n / (k + 1)))) ∗
            F.convolutionPower (n % (k + 1))) (Iic t) := by rw [Measure.convolutionPower_add]
      _ ≤ F.convolutionPower (n % (k + 1)) (Iic t) *
            F.convolutionPower ((k + 1) * (n / (k + 1))) (Iic t) := Measure.conv_Iic_le _ _ t
      _ ≤ 1 * c ^ (n / (k + 1)) := mul_le_mul' hmono (hstep (n / (k + 1)))
      _ = c ^ (n / (k + 1)) := one_mul _
  calc renewalMeasure F (Iic t) = ∑' n, F.convolutionPower n (Iic t) :=
        renewalMeasure_apply F measurableSet_Iic
    _ ≤ ∑' n, c ^ (n / (k + 1)) := ENNReal.tsum_le_tsum hbound
    _ = ∑' p : ℕ × Fin (k + 1), c ^ p.1 :=
        Equiv.tsum_eq (Nat.divModEquiv (k + 1)) (fun p : ℕ × Fin (k + 1) => c ^ p.1)
    _ = ∑' q : ℕ, ((k + 1 : ℕ) : ℝ≥0∞) * c ^ q := by
        rw [ENNReal.tsum_prod (f := fun q (_ : Fin (k + 1)) => c ^ q)]
        exact tsum_congr fun q => by simp
    _ = ((k + 1 : ℕ) : ℝ≥0∞) * ∑' q : ℕ, c ^ q := ENNReal.tsum_mul_left
    _ < ⊤ := ENNReal.mul_lt_top (by simp) (tsum_geometric_lt_top.2 hc1)

/-- The renewal function is finite on every bounded interval when the increment law is not the
point mass at zero. -/
theorem renewalFunction_lt_top (F : Measure ℝ≥0) [IsProbabilityMeasure F] (h0 : F {0} < 1)
    (t : ℝ≥0) : renewalFunction F t < ⊤ := by
  rw [renewalFunction_eq_measure_sum_Iic]
  refine lt_of_le_of_lt ?_ (renewalMeasure_Iic_lt_top F h0 t)
  rw [renewalMeasure_eq_dirac_zero_add_sum_succ, Measure.add_apply]
  refine le_add_of_nonneg_left ?_
  exact zero_le

/-! ### Right continuity of the renewal function -/

/-- Every convolution power of the point mass at zero is the point mass at zero, so the renewal
function of the point mass at zero is identically infinite. -/
lemma renewalFunction_dirac_zero (t : ℝ≥0) :
    renewalFunction (Measure.dirac (0 : ℝ≥0)) t = ⊤ := by
  have h1 : ∀ n : ℕ, (Measure.dirac (0 : ℝ≥0)).convolutionPower (n + 1) (Icc 0 t) = 1 := by
    intro n
    rw [Measure.convolutionPower_dirac_zero, Measure.dirac_apply' (0 : ℝ≥0) measurableSet_Icc]
    simp
  rw [renewalFunction_def, tsum_congr h1]
  exact ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero

/-- The renewal function has no upward jump at `t`: its value is the infimum of the values just to
the right of `t`. This holds for every probability law, including the point mass at zero. -/
theorem iInf_renewalFunction_Ioi (F : Measure ℝ≥0) [IsProbabilityMeasure F] (t : ℝ≥0) :
    (⨅ s ∈ Ioi t, renewalFunction F s) = renewalFunction F t := by
  have hle_one : F {0} ≤ 1 := by
    rw [← measure_univ (μ := F)]
    exact measure_mono (subset_univ _)
  rcases eq_or_lt_of_le hle_one with h | h0
  · -- The point mass at zero has an infinite renewal function, so both sides are `⊤`.
    rw [Measure.eq_dirac_zero_of_measure_singleton_eq_one h]
    simp only [renewalFunction_dirac_zero]
    exact top_le_iff.1 (le_iInf fun s => le_iInf fun _ => le_top)
  -- From here on `F {0} < 1`, so the renewal function is finite at every time.
  set V : Measure ℝ≥0 := Measure.sum fun n => F.convolutionPower (n + 1) with hV
  have hVt : ∀ s : ℝ≥0, renewalFunction F s = V (Iic s) := fun s =>
    renewalFunction_eq_measure_sum_Iic F s
  -- Continuity from above for `V`: the half-lines `Iic (t + 1 / (n + 1))` decrease to `Iic t`,
  -- and `V` charges the first of them finitely, so their masses tend to the mass of `Iic t`.
  have hanti : Antitone fun n : ℕ => Iic (t + 1 / ((n : ℝ≥0) + 1)) := by
    intro n m hnm
    refine Iic_subset_Iic.2 ?_
    have hle : (n : ℝ≥0) + 1 ≤ (m : ℝ≥0) + 1 := by
      exact_mod_cast Nat.succ_le_succ hnm
    gcongr
  have hInter : (⋂ n : ℕ, Iic (t + 1 / ((n : ℝ≥0) + 1))) = Iic t := by
    ext s
    simp only [mem_iInter, mem_Iic]
    refine ⟨fun h => ?_, fun h n => h.trans (le_add_of_nonneg_right zero_le)⟩
    by_contra hcon
    push Not at hcon
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (tsub_pos_of_lt hcon)
    have hlt : t + 1 / ((n : ℝ≥0) + 1) < s := by
      rw [add_comm t, ← tsub_add_cancel_of_le hcon.le]
      exact add_lt_add_left hn t
    exact absurd (h n) (not_le.2 hlt)
  have hchain : renewalFunction F t = ⨅ n : ℕ, renewalFunction F (t + 1 / ((n : ℝ≥0) + 1)) := by
    have hcont : V (Iic t) = ⨅ n : ℕ, V (Iic (t + 1 / ((n : ℝ≥0) + 1))) := by
      rw [← hInter]
      exact Antitone.measure_iInter hanti (fun n => measurableSet_Iic.nullMeasurableSet)
        ⟨0, by
          simp only [Nat.cast_zero, zero_add]
          rw [div_one, ← hVt (t + 1)]
          exact (renewalFunction_lt_top F h0 (t + 1)).ne⟩
    simpa only [hVt] using hcont
  -- The infimum of the values to the right of `t` is the value at `t` itself, because the values
  -- decrease towards it along `t + 1 / (n + 1)` and every right neighbourhood contains such a
  -- point.
  rw [hchain]
  refine le_antisymm ?_ ?_
  · refine le_iInf fun n => ?_
    have hmem : t + 1 / ((n : ℝ≥0) + 1) ∈ Ioi t := mem_Ioi.2 (lt_add_of_pos_right t (by positivity))
    exact iInf₂_le _ hmem
  · refine le_iInf fun s => le_iInf fun hs => ?_
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (tsub_pos_of_lt (mem_Ioi.1 hs))
    have hle : t + 1 / ((n : ℝ≥0) + 1) ≤ s := by
      rw [add_comm t, ← tsub_add_cancel_of_le (mem_Ioi.1 hs).le]
      exact add_le_add_left hn.le t
    exact (iInf_le _ n).trans (monotone_renewalFunction F hle)

/-- The renewal function is right-continuous in time. -/
theorem continuousWithinAt_renewalFunction_Ici (F : Measure ℝ≥0) [IsProbabilityMeasure F]
    (t : ℝ≥0) : ContinuousWithinAt (renewalFunction F) (Ici t) t := by
  rw [ContinuousWithinAt, tendsto_order]
  refine ⟨fun b hb => ?_, fun b hb => ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact hb.trans_le (monotone_renewalFunction F (mem_Ici.1 hs))
  · have hex : ∃ u : ℝ≥0, t < u ∧ renewalFunction F u < b := by
      by_contra hcon
      push Not at hcon
      have hle : b ≤ renewalFunction F t := by
        rw [← iInf_renewalFunction_Ioi F t]
        exact le_iInf fun u => le_iInf fun hu => hcon u (mem_Ioi.1 hu)
      exact absurd hle (not_le.2 hb)
    obtain ⟨u, htu, hu⟩ := hex
    filter_upwards [Ico_mem_nhdsGE htu] with s hs
    exact lt_of_le_of_lt (monotone_renewalFunction F hs.2.le) hu

/-! ### The renewal function as an expected count -/

section Law

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {T : ℕ → Ω → ℝ≥0}

/-- **The renewal function is the expected number of arrivals.** For independent identically
distributed increments with law `F`, the expected count of arrivals in `[0, t]` is the renewal
function of `F`. -/
theorem lintegral_renewalCount_eq_renewalFunction (hT : ∀ n, Measurable (T n))
    (hindep : iIndepFun T P) (hid : ∀ n, IdentDistrib (T n) (T 0) P P) (t : ℝ≥0) :
    ∫⁻ ω, renewalCount T t ω ∂P = renewalFunction (P.map (T 0)) t := by
  have := hindep.isProbabilityMeasure
  have hset : ∀ n, MeasurableSet {ω | arrival T (n + 1) ω ≤ t} := fun n =>
    measurableSet_le (measurable_arrival hT _) measurable_const
  have hif : ∀ n, Measurable fun ω => if arrival T (n + 1) ω ≤ t then (1 : ℝ≥0∞) else 0 :=
    fun n => Measurable.ite (hset n) measurable_const measurable_const
  simp only [renewalCount_def, renewalFunction_def]
  rw [lintegral_tsum (f := fun n ω => if arrival T (n + 1) ω ≤ t then (1 : ℝ≥0∞) else 0)
    (fun n => (hif n).aemeasurable)]
  refine tsum_congr fun n => ?_
  have h1 : ∫⁻ ω, (if arrival T (n + 1) ω ≤ t then (1 : ℝ≥0∞) else 0) ∂P
      = P {ω | arrival T (n + 1) ω ≤ t} := by
    rw [← lintegral_indicator_one (hset n)]
    exact lintegral_congr fun ω => rfl
  rw [h1, ← map_arrival_eq_convolutionPower hT hindep hid (n + 1),
    Measure.map_apply (measurable_arrival hT _) measurableSet_Icc]
  congr 1
  ext ω
  simp

end Law

end TauCeti.Probability
