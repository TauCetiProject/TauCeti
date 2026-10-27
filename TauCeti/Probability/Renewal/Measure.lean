/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Group.ConvolutionPower
public import TauCeti.Probability.Independence.ConvolutionPower
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
it is finite on bounded intervals, and that the renewal function is monotone and right-continuous
with finite values. Local finiteness is where the hypothesis `F {0} < 1` enters, and it cannot be
dropped: if `F = δ₀` then every convolution power is `δ₀` again, so `renewalMeasure F` gives
infinite mass to every neighbourhood of zero.

## Main definitions

* `TauCeti.Probability.renewalMeasure` — the renewal measure `U = ∑' n, F.convolutionPower n`.
* `TauCeti.Probability.renewalFunction` — the renewal function `m t = ∑' n, F.convolutionPower
  (n + 1) [0, t]`.

## Main results

* `TauCeti.Probability.renewalMeasure_eq_dirac_zero_add_conv` — the renewal equation
  `U = δ₀ + F ∗ U`.
* `TauCeti.Probability.renewalMeasure_Iic_lt_top` — `U` is finite on bounded intervals when
  `F {0} < 1`.
* `TauCeti.Probability.renewalMeasure_Icc_eq_one_add_renewalFunction` — `U [0, t] = 1 + m t`.
* `TauCeti.Probability.monotone_renewalFunction`,
  `TauCeti.Probability.continuousWithinAt_renewalFunction_Ici` — monotonicity and right
  continuity of `m`.
* `TauCeti.Probability.map_arrival_eq_convolutionPower`,
  `TauCeti.Probability.lintegral_renewalCount_eq_renewalFunction` — `m t` is the expected number
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

lemma renewalMeasure_apply (F : Measure ℝ≥0) {s : Set ℝ≥0} (hs : MeasurableSet s) :
    renewalMeasure F s = ∑' n, F.convolutionPower n s :=
  Measure.sum_apply _ hs

/-- Splitting the term `n = 0` off the renewal measure leaves the point mass at zero. -/
theorem renewalMeasure_eq_dirac_zero_add_sum_succ (F : Measure ℝ≥0) :
    renewalMeasure F
      = Measure.dirac (0 : ℝ≥0) + Measure.sum fun n => F.convolutionPower (n + 1) := by
  ext s hs
  rw [renewalMeasure_apply F hs, Measure.add_apply, Measure.sum_apply _ hs,
    Measure.dirac_apply' (0 : ℝ≥0) hs]
  conv_lhs => rw [tsum_eq_zero_add' ENNReal.summable, Measure.convolutionPower_zero,
    Measure.dirac_apply' (0 : ℝ≥0) hs]

/-- **The renewal equation** `U = δ₀ + F ∗ U`: the renewal measure is the point mass at zero
together with one more increment convolution. -/
theorem renewalMeasure_eq_dirac_zero_add_conv (F : Measure ℝ≥0) [IsProbabilityMeasure F] :
    renewalMeasure F = Measure.dirac (0 : ℝ≥0) + F ∗ renewalMeasure F := by
  have h : F ∗ renewalMeasure F = Measure.sum fun n => F.convolutionPower (n + 1) := by
    rw [renewalMeasure_def, Measure.conv_sum]
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

/-- A probability measure on the half-line that is not the point mass at zero charges some
half-line `[a, ∞)` with `a > 0`. -/
theorem exists_pos_measure_Ici {F : Measure ℝ≥0} [IsProbabilityMeasure F] (h0 : F {0} < 1) :
    ∃ a : ℝ≥0, 0 < a ∧ 0 < F (Ici a) := by
  have hcompl : ({0} : Set ℝ≥0)ᶜ = Ioi 0 := by
    ext x
    simp only [mem_compl_iff, mem_singleton_iff, mem_Ioi, pos_iff_ne_zero]
  have hunion : (⋃ k : ℕ, Ici (1 / ((k : ℝ≥0) + 1))) = Ioi 0 := by
    ext x
    simp only [mem_iUnion, mem_Ici, mem_Ioi]
    exact ⟨fun ⟨k, hk⟩ => lt_of_lt_of_le (by positivity) hk, fun hx =>
      let ⟨k, hk⟩ := exists_nat_one_div_lt hx
      ⟨k, hk.le⟩⟩
  have hpos : F (Ioi (0 : ℝ≥0)) ≠ 0 := by
    intro h
    have huniv : F univ = F {0} + F (Ioi 0) := by
      rw [← hcompl]
      exact (measure_add_measure_compl (measurableSet_singleton (0 : ℝ≥0))).symm
    rw [measure_univ, h, add_zero] at huniv
    exact h0.ne huniv.symm
  obtain ⟨k, hk⟩ := exists_measure_pos_of_not_measure_iUnion_null
    (s := fun k : ℕ => Ici (1 / ((k : ℝ≥0) + 1))) (by rw [hunion]; exact hpos)
  exact ⟨_, by positivity, hk⟩

/-- The mass that a convolution gives to the translates `{y | x + y ≤ t}` is bounded by the mass
of `[0, t]` carried by the two factors. -/
theorem conv_Iic_le (μ ν : Measure ℝ≥0) [SFinite ν] (t : ℝ≥0) :
    (μ ∗ ν) (Iic t) ≤ ν (Iic t) * μ (Iic t) := by
  rw [Measure.conv_apply μ ν measurableSet_Iic]
  calc ∫⁻ x, ν {y | x + y ∈ Iic t} ∂μ
      ≤ ∫⁻ x, (Iic t).indicator (fun _ => ν (Iic t)) x ∂μ := by
        refine lintegral_mono fun x => ?_
        by_cases hx : x ∈ Iic t
        · rw [Set.indicator_of_mem hx]
          refine measure_mono fun y hy => mem_Iic.2 ?_
          exact (le_add_of_nonneg_left zero_le).trans (mem_Iic.1 hy)
        · rw [Set.indicator_of_notMem hx]
          refine le_of_eq (measure_mono_null ?_ (measure_empty (μ := ν)))
          intro y hy
          exact hx (mem_Iic.2 ((le_add_of_nonneg_right zero_le).trans (mem_Iic.1 hy)))
    _ = ν (Iic t) * μ (Iic t) := lintegral_indicator_const measurableSet_Iic _

/-- A convolution charges the half-line `[c + d, ∞)` at least as much as the two half-lines
`[c, ∞)` and `[d, ∞)` weigh together. -/
theorem le_conv_Ici (μ ν : Measure ℝ≥0) [SFinite ν] (c d : ℝ≥0) :
    ν (Ici d) * μ (Ici c) ≤ (μ ∗ ν) (Ici (c + d)) := by
  rw [Measure.conv_apply μ ν measurableSet_Ici]
  calc ν (Ici d) * μ (Ici c) = ∫⁻ x, (Ici c).indicator (fun _ => ν (Ici d)) x ∂μ :=
        (lintegral_indicator_const measurableSet_Ici _).symm
    _ ≤ ∫⁻ x, ν {y | x + y ∈ Ici (c + d)} ∂μ := by
        refine lintegral_mono fun x => ?_
        by_cases hx : x ∈ Ici c
        · rw [Set.indicator_of_mem hx]
          exact measure_mono fun y hy => mem_Ici.2 (add_le_add hx (mem_Ici.1 hy))
        · rw [Set.indicator_of_notMem hx]
          exact zero_le

/-- Each convolution power of a law that charges `[a, ∞)` charges `[m * a, ∞)` at least as much
as the `m`-th power of the charge of `[a, ∞)`. -/
theorem convolutionPower_Ici_pos {F : Measure ℝ≥0} [SFinite F] {a : ℝ≥0}
    (ha : 0 < F (Ici a)) (m : ℕ) : 0 < F.convolutionPower m (Ici ((m : ℝ≥0) * a)) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Measure.convolutionPower_succ, Nat.cast_succ, add_mul, one_mul]
      exact (ENNReal.mul_pos ha.ne' ih.ne').trans_le (le_conv_Ici _ _ _ _)

/-- A convolution power whose length exceeds `t / a` puts less than full mass on `[0, t]` when the
law charges `[a, ∞)`. -/
theorem convolutionPower_Iic_lt_one {F : Measure ℝ≥0} [IsProbabilityMeasure F] {a t : ℝ≥0}
    {m : ℕ} (ha : 0 < F (Ici a)) (ht : t < (m : ℝ≥0) * a) :
    F.convolutionPower m (Iic t) < 1 := by
  have hdisj : Disjoint (Iic t) (Ici ((m : ℝ≥0) * a)) :=
    Set.disjoint_left.2 fun x hx hx' => absurd (le_trans hx' (mem_Iic.1 hx)) (not_le.2 ht)
  have hsum : F.convolutionPower m (Iic t) + F.convolutionPower m (Ici ((m : ℝ≥0) * a)) ≤ 1 := by
    rw [← measure_union hdisj measurableSet_Ici, ← measure_univ (μ := F.convolutionPower m)]
    exact measure_mono (subset_univ _)
  have hpos := convolutionPower_Ici_pos ha m
  refine lt_of_lt_of_le (ENNReal.lt_add_right ?_ hpos.ne') hsum
  exact ne_top_of_le_ne_top (by simp) ((le_add_of_nonneg_right zero_le).trans hsum)

/-- **Local finiteness of the renewal measure.** If the increment law is not the point mass at
zero, the renewal measure is finite on every bounded interval. Without the hypothesis `F {0} < 1`
this fails: for `F = δ₀` every convolution power equals `δ₀`.

The proof splits the `n` increments into blocks of `k + 1`, where `k` is chosen with
`t < (k + 1) * a` and `F` charges `[a, ∞)`. A block all of whose increments reach `a` already
pushes the arrival past `t`, so each block multiplies the mass of `[0, t]` by at most the geometric
factor `(F.convolutionPower (k + 1)) (Iic t) < 1`. -/
theorem renewalMeasure_Iic_lt_top (F : Measure ℝ≥0) [IsProbabilityMeasure F] (h0 : F {0} < 1)
    (t : ℝ≥0) : renewalMeasure F (Iic t) < ⊤ := by
  obtain ⟨a, ha, hpa⟩ := exists_pos_measure_Ici h0
  obtain ⟨k, hk⟩ := exists_nat_gt (t / a)
  have h1 : t < (k : ℝ≥0) * a := by rwa [div_lt_iff₀ ha] at hk
  have hkt : t < ((k + 1 : ℕ) : ℝ≥0) * a := by
    refine lt_of_lt_of_le h1 ?_
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.2 (Nat.le_succ k)) zero_le
  set c : ℝ≥0∞ := F.convolutionPower (k + 1) (Iic t) with hc
  have hc1 : c < 1 := hc.symm ▸ convolutionPower_Iic_lt_one hpa hkt
  have hstep : ∀ q : ℕ, F.convolutionPower ((k + 1) * q) (Iic t) ≤ c ^ q := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
        rw [Nat.mul_succ, Measure.convolutionPower_add, pow_succ']
        exact (conv_Iic_le _ _ t).trans (mul_le_mul' le_rfl ih)
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
            F.convolutionPower ((k + 1) * (n / (k + 1))) (Iic t) := conv_Iic_le _ _ t
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
    _ < ⊤ := by
        rw [ENNReal.tsum_geometric]
        refine ENNReal.mul_lt_top (by simp) ?_
        rw [ENNReal.inv_lt_top]
        exact tsub_pos_of_lt hc1

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

/-- The renewal function has no upward jump at `t`: its value is the infimum of the values just to
the right of `t`. -/
theorem iInf_renewalFunction_Ioi (F : Measure ℝ≥0) [IsProbabilityMeasure F] (h0 : F {0} < 1)
    (t : ℝ≥0) : (⨅ s ∈ Ioi t, renewalFunction F s) = renewalFunction F t := by
  set V : Measure ℝ≥0 := Measure.sum fun n => F.convolutionPower (n + 1) with hV
  have hVt : ∀ s : ℝ≥0, renewalFunction F s = V (Iic s) := fun s =>
    renewalFunction_eq_measure_sum_Iic F s
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
    (h0 : F {0} < 1) (t : ℝ≥0) : ContinuousWithinAt (renewalFunction F) (Ici t) t := by
  rw [ContinuousWithinAt, tendsto_order]
  refine ⟨fun b hb => ?_, fun b hb => ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact hb.trans_le (monotone_renewalFunction F (mem_Ici.1 hs))
  · have hex : ∃ u : ℝ≥0, t < u ∧ renewalFunction F u < b := by
      by_contra hcon
      push Not at hcon
      have hle : b ≤ renewalFunction F t := by
        rw [← iInf_renewalFunction_Ioi F h0 t]
        exact le_iInf fun u => le_iInf fun hu => hcon u (mem_Ioi.1 hu)
      exact absurd hle (not_le.2 hb)
    obtain ⟨u, htu, hu⟩ := hex
    filter_upwards [Ico_mem_nhdsGE htu] with s hs
    exact lt_of_le_of_lt (monotone_renewalFunction F hs.2.le) hu

/-! ### The renewal function as an expected count -/

section Law

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {T : ℕ → Ω → ℝ≥0}

/-- The law of the `n`-th arrival time is the `n`-th convolution power of the increment law. -/
theorem map_arrival_eq_convolutionPower [IsProbabilityMeasure P] (hT : ∀ n, Measurable (T n))
    (hindep : iIndepFun T P) (hid : ∀ n, IdentDistrib (T n) (T 0) P P) (n : ℕ) :
    P.map (arrival T n) = (P.map (T 0)).convolutionPower n := by
  have hX : ∀ i, HasLaw (T i) (P.map (T 0)) P := fun i =>
    ⟨(hT i).aemeasurable, (hid i).map_eq⟩
  have h := hindep.hasLaw_finset_sum_convolutionPower (μ := P.map (T 0)) hX (Finset.range n)
  rw [Finset.card_range] at h
  have hfun : (∑ i ∈ Finset.range n, T i) = arrival T n := by
    funext ω
    simp [arrival_def]
  rw [hfun] at h
  exact h.map_eq

/-- **The renewal function is the expected number of arrivals.** For independent identically
distributed increments with law `F`, the expected count of arrivals in `[0, t]` is the renewal
function of `F`. -/
theorem lintegral_renewalCount_eq_renewalFunction [IsProbabilityMeasure P]
    (hT : ∀ n, Measurable (T n)) (hindep : iIndepFun T P)
    (hid : ∀ n, IdentDistrib (T n) (T 0) P P) (t : ℝ≥0) :
    ∫⁻ ω, renewalCount T t ω ∂P = renewalFunction (P.map (T 0)) t := by
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
