/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.CurveAction.Basic
import TauCeti.Topology.Instances.ENNReal

/-!
# The action of a limit of piecewise constant interpolants

Implicit time discretizations, such as the minimizing movement scheme for gradient flows,
produce for a time step `τ > 0` a sequence of points `U 0, U 1, U 2, …`, and the *piecewise
constant interpolant* `t ↦ U ⌈t / τ⌉₊`. Its *discrete `p`-action* up to time `T` is

`∑_{n < ⌈T / τ⌉₊} d(U n, U (n + 1)) ^ p / τ ^ (p - 1)`,

that is, the sum of `τ (d(U n, U (n + 1)) / τ) ^ p`: the `p`-action of the curve that would
cover each step at constant speed in time `τ`. The interpolants are not continuous, so the lower
semicontinuity of the action under pointwise convergence of absolutely continuous curves
(`TauCeti.curveAction_le_liminf`) does not apply to them. This file proves its discrete
counterpart: if the interpolants for time steps `τ i → 0` converge to a curve `u` on `[0, T]`, in
the weak sense that

`d(u s, u t) ≤ liminf_i d(U i ⌈s / τ i⌉₊, U i ⌈t / τ i⌉₊)`

for all `s, t ∈ [0, T]`, and their discrete `p`-actions have finite lower limit, for an exponent
`1 < p`, then `u` is absolutely continuous on `[0, T]` and its `p`-action is at most that lower
limit. The weak form of convergence covers convergence for a topology weaker than that of the
metric, for which the distance is lower semicontinuous, as for narrow convergence of
probability measures and the Wasserstein distance.

Both results rest on the discrete Hölder estimate: the distance between the interpolant at times
`s ≤ t` is at most the sum of the steps taken in between, of which there are at most
`(t - s) / τ + 1`, so that `d(U ⌈s / τ⌉₊, U ⌈t / τ⌉₊) ^ p ≤ ((t - s) / τ + 1) ^ (p - 1)` times the
sum of the `p`-th powers of these steps. Summed over a disjoint family of intervals this gives the
bound of `TauCeti.absolutelyContinuousOnInterval_of_sum_edist_rpow_le`, up to an error that
vanishes with `τ`; integrated over the windows `[t, t + h]` it bounds the difference quotients of
the action formula `AbsolutelyContinuousOnInterval.tendsto_lintegral_edist_div_rpow`.

## Main results

* `TauCeti.sum_edist_ceil_div_rpow_le`: the discrete Hölder estimate for a disjoint family of
  intervals in `[0, T]`.
* `TauCeti.absolutelyContinuousOnInterval_of_liminf_sum_edist_rpow_ne_top`: a limit of piecewise
  constant interpolants with bounded discrete `p`-actions is absolutely continuous.
* `TauCeti.curveAction_le_liminf_sum_edist_rpow`: its `p`-action is at most the lower limit of
  the discrete `p`-actions.

## References

* L. Ambrosio, N. Gigli, G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd ed., Birkhäuser 2008, Chapter 3, Section 3.3.
-/

public section

noncomputable section

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal Interval

namespace TauCeti

section PseudoEMetricSpace

variable {X : Type*} [PseudoEMetricSpace X] {p : ℝ} {τ : ℝ≥0} {U : ℕ → X}

/-- The steps of the piecewise constant interpolant taken during the times `(s, t]` are those with
indices in `[⌈s / τ⌉₊, ⌈t / τ⌉₊)`, and there are at most `(t - s) / τ + 1` of them. -/
private lemma natCast_ceil_div_sub_ceil_div_le (hτ : 0 < τ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ((⌈t / τ⌉₊ - ⌈s / τ⌉₊ : ℕ) : ℝ) ≤ (t - s) / τ + 1 := by
  have hτr : (0 : ℝ) < τ := NNReal.coe_pos.2 hτ
  have hle : ⌈s / τ⌉₊ ≤ ⌈t / τ⌉₊ := Nat.ceil_mono (div_le_div_of_nonneg_right hst hτr.le)
  rw [Nat.cast_sub hle, sub_div]
  linarith [Nat.ceil_lt_add_one (div_nonneg (hs.trans hst) hτr.le), Nat.le_ceil (s / τ)]

/-- A step index `n` lies in `[⌈s / τ⌉₊, ⌈t / τ⌉₊)` exactly when the time `n τ` lies in
`[s, t)`. -/
private lemma mem_Ico_ceil_div_iff (hτ : 0 < τ) {s t : ℝ} {n : ℕ} :
    n ∈ Finset.Ico ⌈s / τ⌉₊ ⌈t / τ⌉₊ ↔ n * (τ : ℝ) ∈ Ico s t := by
  have hτr : (0 : ℝ) < τ := NNReal.coe_pos.2 hτ
  rw [Finset.mem_Ico, Nat.ceil_le, Nat.lt_ceil, div_le_iff₀ hτr, lt_div_iff₀ hτr, mem_Ico]

/-- **Discrete Hölder estimate** on one interval: for `0 ≤ s ≤ t`, the `p`-th power of the distance
between the piecewise constant interpolant at times `s` and `t` is at most
`((t - s) / τ + 1) ^ (p - 1)` times the sum of the `p`-th powers of the steps taken in between. -/
private lemma edist_ceil_div_rpow_le (hp : 1 ≤ p) (hτ : 0 < τ) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) :
    edist (U ⌈s / τ⌉₊) (U ⌈t / τ⌉₊) ^ p ≤ ENNReal.ofReal ((t - s) / τ + 1) ^ (p - 1) *
      ∑ n ∈ Finset.Ico ⌈s / τ⌉₊ ⌈t / τ⌉₊, edist (U n) (U (n + 1)) ^ p := by
  have hle : ⌈s / τ⌉₊ ≤ ⌈t / τ⌉₊ :=
    Nat.ceil_mono (div_le_div_of_nonneg_right hst (NNReal.coe_nonneg τ))
  calc edist (U ⌈s / τ⌉₊) (U ⌈t / τ⌉₊) ^ p
      ≤ (∑ n ∈ Finset.Ico ⌈s / τ⌉₊ ⌈t / τ⌉₊, edist (U n) (U (n + 1))) ^ p :=
        ENNReal.rpow_le_rpow (edist_le_Ico_sum_edist U hle) (by linarith)
    _ ≤ ((Finset.Ico ⌈s / τ⌉₊ ⌈t / τ⌉₊).card : ℝ≥0∞) ^ (p - 1) *
          ∑ n ∈ Finset.Ico ⌈s / τ⌉₊ ⌈t / τ⌉₊, edist (U n) (U (n + 1)) ^ p :=
        ENNReal.rpow_sum_le_const_mul_sum_rpow _ _ hp
    _ ≤ _ := by
        gcongr
        rw [Nat.card_Ico, ← ENNReal.ofReal_natCast]
        exact ENNReal.ofReal_le_ofReal (natCast_ceil_div_sub_ceil_div_le hτ hs hst)

/-- **Discrete Hölder estimate** for a disjoint family of intervals `(sᵢ, tᵢ]` in `[0, T]`: the
`p`-th power of the sum of the distances between the piecewise constant interpolant at times `sᵢ`
and `tᵢ` is at most `(|⋃ (sᵢ, tᵢ]| + k τ) ^ (p - 1)` times the discrete `p`-action up to time `T`,
where `k` is the number of intervals. As `τ → 0` the factor tends to the one in the Hölder
estimate `AbsolutelyContinuousOnInterval.edist_rpow_le_mul_curveAction` for curves. -/
theorem sum_edist_ceil_div_rpow_le (hp : 1 ≤ p) (hτ : 0 < τ) {T : ℝ} (hT : 0 ≤ T)
    {E : ℕ × (ℕ → ℝ × ℝ)} (hE : E ∈ AbsolutelyContinuousOnInterval.disjWithin 0 T) :
    (∑ i ∈ Finset.range E.1, edist (U ⌈(E.2 i).1 / τ⌉₊) (U ⌈(E.2 i).2 / τ⌉₊)) ^ p ≤
      (volume (⋃ i ∈ Finset.range E.1, Ι (E.2 i).1 (E.2 i).2) + E.1 * τ) ^ (p - 1) *
        ∑ n ∈ Finset.range ⌈T / τ⌉₊, edist (U n) (U (n + 1)) ^ p / (τ : ℝ≥0∞) ^ (p - 1) := by
  obtain ⟨k, I⟩ := E
  have hτr : (0 : ℝ) < τ := NNReal.coe_pos.2 hτ
  -- The `i`-th interval is `(s i, t i]`, and `J i` indexes the steps taken during it.
  set s : ℕ → ℝ := fun i ↦ min (I i).1 (I i).2
  set t : ℕ → ℝ := fun i ↦ max (I i).1 (I i).2
  set J : ℕ → Finset ℕ := fun i ↦ Finset.Ico ⌈s i / τ⌉₊ ⌈t i / τ⌉₊
  have hst i (hi : i ∈ Finset.range k) : 0 ≤ s i ∧ s i ≤ t i ∧ t i ≤ T := by
    obtain ⟨h₁, h₂⟩ := hE.1 i hi
    rw [uIcc_of_le hT] at h₁ h₂
    exact ⟨le_min h₁.1 h₂.1, min_le_max, max_le h₁.2 h₂.2⟩
  have hedist i (hi : i ∈ Finset.range k) :
      edist (U ⌈(I i).1 / τ⌉₊) (U ⌈(I i).2 / τ⌉₊) ≤ ∑ n ∈ J i, edist (U n) (U (n + 1)) := by
    have h := edist_le_Ico_sum_edist U
      (Nat.ceil_mono (div_le_div_of_nonneg_right (hst i hi).2.1 hτr.le))
    rcases le_total (I i).1 (I i).2 with hle | hle
    · simpa [J, s, t, min_eq_left hle, max_eq_right hle] using h
    · rw [edist_comm]
      simpa [J, s, t, min_eq_right hle, max_eq_left hle] using h
  -- The index sets of disjoint intervals are disjoint.
  have hdisj : (Finset.range k : Set ℕ).PairwiseDisjoint J := by
    intro i hi j hj hij
    refine Finset.disjoint_left.2 fun n hni hnj ↦ ?_
    rw [mem_Ico_ceil_div_iff hτ] at hni hnj
    exact Set.disjoint_left.1 (hE.2 hi hj hij)
      ⟨lt_of_le_of_lt hni.1 (lt_min hni.2 hnj.2), min_le_left _ _⟩
      ⟨lt_of_le_of_lt hnj.1 (lt_min hni.2 hnj.2), min_le_right _ _⟩
  -- The total number of steps taken during the intervals.
  have hvol : volume (⋃ i ∈ Finset.range k, Ι (I i).1 (I i).2) =
      ENNReal.ofReal (∑ i ∈ Finset.range k, (t i - s i)) := by
    rw [measure_biUnion_finset hE.2 fun _ _ ↦ measurableSet_uIoc,
      ENNReal.ofReal_sum_of_nonneg fun i hi ↦ sub_nonneg.2 (hst i hi).2.1]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Real.volume_uIoc, ← max_sub_min_eq_abs']
    simp only [t, s, max_comm (I i).1, min_comm (I i).1]
  have hcard : (((Finset.range k).biUnion J).card : ℝ≥0∞) ≤
      ENNReal.ofReal ((∑ i ∈ Finset.range k, (t i - s i)) / τ + k) := by
    rw [← ENNReal.ofReal_natCast]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [Finset.card_biUnion hdisj, Nat.cast_sum, Finset.sum_div]
    have := Finset.sum_le_sum fun i hi ↦
      natCast_ceil_div_sub_ceil_div_le hτ (hst i hi).1 (hst i hi).2.1
    simpa [J, Finset.sum_add_distrib] using this
  have hsub : (Finset.range k).biUnion J ⊆ Finset.range ⌈T / τ⌉₊ := by
    intro n hn
    obtain ⟨i, hi, hn⟩ := Finset.mem_biUnion.1 hn
    exact Finset.mem_range.2 ((Finset.mem_Ico.1 hn).2.trans_le
      (Nat.ceil_mono (div_le_div_of_nonneg_right (hst i hi).2.2 hτr.le)))
  -- The factor `(|⋃ (sᵢ, tᵢ]| / τ + k) ^ (p - 1)`, rewritten.
  have hfac : ENNReal.ofReal ((∑ i ∈ Finset.range k, (t i - s i)) / τ + k) =
      (volume (⋃ i ∈ Finset.range k, Ι (I i).1 (I i).2) + k * τ) / τ := by
    rw [hvol, ENNReal.ofReal_add (div_nonneg (Finset.sum_nonneg fun i hi ↦
      sub_nonneg.2 (hst i hi).2.1) hτr.le) k.cast_nonneg, ENNReal.ofReal_div_of_pos hτr,
      ENNReal.ofReal_natCast, ENNReal.add_div, ENNReal.ofReal_coe_nnreal,
      ENNReal.mul_div_cancel_right (by simpa using hτ.ne') ENNReal.coe_ne_top]
  calc (∑ i ∈ Finset.range k, edist (U ⌈(I i).1 / τ⌉₊) (U ⌈(I i).2 / τ⌉₊)) ^ p
      ≤ (∑ n ∈ (Finset.range k).biUnion J, edist (U n) (U (n + 1))) ^ p := by
        rw [Finset.sum_biUnion hdisj]
        exact ENNReal.rpow_le_rpow (Finset.sum_le_sum hedist) (by linarith)
    _ ≤ (((Finset.range k).biUnion J).card : ℝ≥0∞) ^ (p - 1) *
          ∑ n ∈ (Finset.range k).biUnion J, edist (U n) (U (n + 1)) ^ p :=
        ENNReal.rpow_sum_le_const_mul_sum_rpow _ _ hp
    _ ≤ ((volume (⋃ i ∈ Finset.range k, Ι (I i).1 (I i).2) + k * τ) / τ) ^ (p - 1) *
          ∑ n ∈ Finset.range ⌈T / τ⌉₊, edist (U n) (U (n + 1)) ^ p := by
        rw [← hfac]
        gcongr
    _ = _ := by
        rw [ENNReal.div_rpow_of_nonneg _ _ (by linarith), ← ENNReal.sum_div]
        simp only [div_eq_mul_inv]
        ring

/-- **Discrete difference-quotient estimate.** For `t ∈ (0, T - h]`, the `p`-th power of the
difference quotient over `[t, t + h]` of the piecewise constant interpolant is at most
`((h + τ) / h) ^ (p - 1) / h` times the sum of `d(U n, U (n + 1)) ^ p / τ ^ (p - 1)` over the steps
`n < ⌈T / τ⌉₊` whose window `(n τ - h, n τ]` contains `t`. Integrated over `t`, each step counts
once with weight `h`. -/
private lemma edist_ceil_div_div_rpow_le (hp : 1 ≤ p) (hτ : 0 < τ) {T h t : ℝ} (hh : 0 < h)
    (ht : t ∈ Ioc 0 (T - h)) :
    (edist (U ⌈t / τ⌉₊) (U ⌈(t + h) / τ⌉₊) / ENNReal.ofReal h) ^ p ≤
      ((ENNReal.ofReal h + τ) / ENNReal.ofReal h) ^ (p - 1) * (ENNReal.ofReal h)⁻¹ *
        ∑ n ∈ Finset.range ⌈T / τ⌉₊, (Ioc (n * τ - h) (n * τ)).indicator
          (fun _ ↦ edist (U n) (U (n + 1)) ^ p / (τ : ℝ≥0∞) ^ (p - 1)) t := by
  set H := ENNReal.ofReal h
  have hH : H ≠ 0 := (ENNReal.ofReal_pos.2 hh).ne'
  have hHtop : H ≠ ∞ := ENNReal.ofReal_ne_top
  have hτr : (0 : ℝ) < τ := NNReal.coe_pos.2 hτ
  have hτ' : (τ : ℝ≥0∞) ≠ 0 := by simpa using hτ.ne'
  have hq : 0 ≤ p - 1 := by linarith
  have hHölder := edist_ceil_div_rpow_le (U := U) hp hτ ht.1.le (le_add_of_nonneg_right hh.le)
  rw [add_sub_cancel_left] at hHölder
  -- The steps taken during `(t, t + h]` are those whose window contains `t`.
  have hsum : ∑ n ∈ Finset.Ico ⌈t / τ⌉₊ ⌈(t + h) / τ⌉₊, edist (U n) (U (n + 1)) ^ p =
      ∑ n ∈ Finset.range ⌈T / τ⌉₊,
        (Ioc (n * τ - h) (n * τ)).indicator (fun _ ↦ edist (U n) (U (n + 1)) ^ p) t := by
    rw [Finset.sum_indicator_eq_sum_filter]
    refine Finset.sum_congr (Finset.ext fun n ↦ ?_) fun _ _ ↦ rfl
    rw [mem_Ico_ceil_div_iff hτ, Finset.mem_filter, Finset.mem_range, mem_Ico, mem_Ioc]
    constructor
    · rintro ⟨h₁, h₂⟩
      refine ⟨?_, by linarith, h₁⟩
      rw [← Nat.cast_lt (α := ℝ), ← mul_lt_mul_iff_of_pos_right hτr]
      exact h₂.trans_le (by linarith [ht.2, (div_le_iff₀ hτr).1 (Nat.le_ceil (T / τ))])
    · rintro ⟨-, h₁, h₂⟩
      exact ⟨h₂, by linarith⟩
  -- The factor `(h / τ + 1) ^ (p - 1) / h ^ p` is `((h + τ) / h) ^ (p - 1) / (h τ ^ (p - 1))`.
  have hfac : ENNReal.ofReal (h / τ + 1) ^ (p - 1) / H ^ p =
      ((H + τ) / H) ^ (p - 1) * H⁻¹ * ((τ : ℝ≥0∞) ^ (p - 1))⁻¹ := by
    have h₁ : ENNReal.ofReal (h / τ + 1) = (H + τ) / τ := by
      rw [ENNReal.ofReal_add (div_nonneg hh.le hτr.le) zero_le_one, ENNReal.ofReal_div_of_pos hτr,
        ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_one, ENNReal.add_div,
        ENNReal.div_self hτ' ENNReal.coe_ne_top]
    have h₂ : H ^ p = H ^ (p - 1) * H := by
      conv_lhs => rw [← sub_add_cancel p 1]
      rw [ENNReal.rpow_add _ _ hH hHtop, ENNReal.rpow_one]
    rw [h₁, h₂, ENNReal.div_rpow_of_nonneg _ _ hq, ENNReal.div_rpow_of_nonneg _ _ hq]
    simp only [div_eq_mul_inv]
    rw [ENNReal.mul_inv (by simp [hHtop]) (by simp [hH])]
    ring
  calc (edist (U ⌈t / τ⌉₊) (U ⌈(t + h) / τ⌉₊) / H) ^ p
      = edist (U ⌈t / τ⌉₊) (U ⌈(t + h) / τ⌉₊) ^ p / H ^ p :=
        ENNReal.div_rpow_of_nonneg _ _ (by linarith)
    _ ≤ (ENNReal.ofReal (h / τ + 1) ^ (p - 1) * ∑ n ∈ Finset.Ico ⌈t / τ⌉₊
          ⌈(t + h) / τ⌉₊, edist (U n) (U (n + 1)) ^ p) / H ^ p := by gcongr
    _ = _ := by
        rw [div_eq_mul_inv, mul_right_comm, ← div_eq_mul_inv, hfac, hsum]
        simp only [mul_assoc, Finset.mul_sum]
        refine Finset.sum_congr rfl fun n _ ↦ ?_
        simp only [indicator, div_eq_mul_inv]
        split_ifs <;> ring

end PseudoEMetricSpace

section PseudoMetricSpace

variable {X : Type*} [PseudoMetricSpace X] {p : ℝ} {ι : Type*} {l : Filter ι} {τ : ι → ℝ≥0}
  {U : ι → ℕ → X} {u : ℝ → X} {T : ℝ}

/-- **Absolute continuity of a limit of piecewise constant interpolants.** Let `U i` be sequences
of points with time steps `τ i > 0` tending to `0`, and let `u` be a curve with
`d(u s, u t) ≤ liminf_i d(U i ⌈s / τ i⌉₊, U i ⌈t / τ i⌉₊)` for all `s, t ∈ [0, T]`. If the discrete
`p`-actions `∑_{n < ⌈T / τ i⌉₊} d(U i n, U i (n + 1)) ^ p / τ i ^ (p - 1)` have finite lower limit,
for an exponent `1 < p`, then `u` is absolutely continuous on `[0, T]`. -/
theorem absolutelyContinuousOnInterval_of_liminf_sum_edist_rpow_ne_top (hp : 1 < p)
    (hτ : ∀ i, 0 < τ i) (hτ0 : Tendsto τ l (𝓝 0)) (hT : 0 ≤ T)
    (hu : ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T,
      edist (u s) (u t) ≤ liminf (fun i ↦ edist (U i ⌈s / τ i⌉₊) (U i ⌈t / τ i⌉₊)) l)
    (hS : liminf (fun i ↦ ∑ n ∈ Finset.range ⌈T / τ i⌉₊,
      edist (U i n) (U i (n + 1)) ^ p / (τ i : ℝ≥0∞) ^ (p - 1)) l ≠ ∞) :
    AbsolutelyContinuousOnInterval u 0 T := by
  set S : ι → ℝ≥0∞ := fun i ↦ ∑ n ∈ Finset.range ⌈T / τ i⌉₊,
    edist (U i n) (U i (n + 1)) ^ p / (τ i : ℝ≥0∞) ^ (p - 1)
  refine absolutelyContinuousOnInterval_of_sum_edist_rpow_le hp hS ?_
  rintro ⟨k, I⟩ hE
  set V := volume (⋃ j ∈ Finset.range k, Ι (I j).1 (I j).2)
  have hmem j (hj : j ∈ Finset.range k) : (I j).1 ∈ Icc 0 T ∧ (I j).2 ∈ Icc 0 T := by
    simpa [uIcc_of_le hT] using hE.1 j hj
  have hV : V ≠ ∞ := ne_top_of_le_ne_top (by simp [Real.volume_uIoc])
    (measure_mono (AbsolutelyContinuousOnInterval.biUnion_uIoc_subset_of_mem_disjWithin hE))
  -- The factor `(V + k τ i) ^ (p - 1)` of the discrete Hölder estimate tends to `V ^ (p - 1)`.
  have hfac : Tendsto (fun i ↦ (V + k * (τ i : ℝ≥0∞)) ^ (p - 1)) l (𝓝 (V ^ (p - 1))) := by
    have : Tendsto (fun i ↦ V + k * (τ i : ℝ≥0∞)) l (𝓝 (V + k * 0)) :=
      tendsto_const_nhds.add (ENNReal.Tendsto.const_mul (ENNReal.tendsto_coe.2 hτ0)
        (Or.inr (ENNReal.natCast_ne_top k)))
    rw [mul_zero, add_zero] at this
    exact (ENNReal.continuous_rpow_const.tendsto _).comp this
  rcases l.eq_or_neBot with rfl | hl
  · simp [S] at hS
  calc (∑ j ∈ Finset.range k, edist (u (I j).1) (u (I j).2)) ^ p
      ≤ (liminf (fun i ↦ ∑ j ∈ Finset.range k,
          edist (U i ⌈(I j).1 / τ i⌉₊) (U i ⌈(I j).2 / τ i⌉₊)) l) ^ p := by
        refine ENNReal.rpow_le_rpow ((Finset.sum_le_sum fun j hj ↦ hu _ (hmem j hj).1 _
          (hmem j hj).2).trans (ENNReal.sum_liminf_le_liminf_sum _ _)) (by linarith)
    _ = liminf (fun i ↦ (∑ j ∈ Finset.range k,
          edist (U i ⌈(I j).1 / τ i⌉₊) (U i ⌈(I j).2 / τ i⌉₊)) ^ p) l :=
        Monotone.map_liminf_of_continuousAt (fun _ _ h ↦ ENNReal.rpow_le_rpow h (by linarith)) _
          ENNReal.continuous_rpow_const.continuousAt
    _ ≤ liminf (fun i ↦ (V + k * (τ i : ℝ≥0∞)) ^ (p - 1) * S i) l :=
        liminf_le_liminf (Eventually.of_forall fun i ↦
          sum_edist_ceil_div_rpow_le hp.le (hτ i) hT hE)
    _ ≤ limsup (fun i ↦ (V + k * (τ i : ℝ≥0∞)) ^ (p - 1)) l * liminf S l :=
        ENNReal.liminf_mul_le (Or.inr hS) (Or.inl (hfac.limsup_eq ▸
          ENNReal.rpow_ne_top_of_nonneg (by linarith) hV))
    _ = V ^ (p - 1) * liminf S l := by rw [hfac.limsup_eq]

/-- For a fixed step `h > 0`, the integrated `p`-th powers of the difference quotients of a limit
`u` of piecewise constant interpolants are at most the lower limit of their discrete `p`-actions:
by the discrete Hölder estimate, each step of an interpolant contributes to the difference quotient
at the times `t` of a window `(n τ - h, n τ]` of length `h`, and Fatou's lemma passes to the limit.
-/
private lemma lintegral_edist_div_rpow_le_liminf [l.IsCountablyGenerated] (hp : 1 ≤ p)
    (hτ : ∀ i, 0 < τ i) (hτ0 : Tendsto τ l (𝓝 0))
    (hu : ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T,
      edist (u s) (u t) ≤ liminf (fun i ↦ edist (U i ⌈s / τ i⌉₊) (U i ⌈t / τ i⌉₊)) l)
    {h : ℝ} (hh : 0 < h) :
    ∫⁻ t in Ioc 0 (T - h), (edist (u t) (u (t + h)) / ENNReal.ofReal h) ^ p ≤
      liminf (fun i ↦ ∑ n ∈ Finset.range ⌈T / τ i⌉₊,
        edist (U i n) (U i (n + 1)) ^ p / (τ i : ℝ≥0∞) ^ (p - 1)) l := by
  rcases l.eq_or_neBot with rfl | _
  · simp
  set H := ENNReal.ofReal h
  have hH : H ≠ 0 := (ENNReal.ofReal_pos.2 hh).ne'
  have hHtop : H ≠ ∞ := ENNReal.ofReal_ne_top
  set S : ι → ℝ≥0∞ := fun i ↦ ∑ n ∈ Finset.range ⌈T / τ i⌉₊,
    edist (U i n) (U i (n + 1)) ^ p / (τ i : ℝ≥0∞) ^ (p - 1)
  -- The factors `c i = ((h + τ i) / h) ^ (p - 1)` tend to `1`.
  set c : ι → ℝ≥0∞ := fun i ↦ ((H + τ i) / H) ^ (p - 1)
  have hc : Tendsto c l (𝓝 1) := by
    have : Tendsto (fun i ↦ (H + τ i) / H) l (𝓝 ((H + 0) / H)) :=
      ENNReal.Tendsto.div_const (tendsto_const_nhds.add (ENNReal.tendsto_coe.2 hτ0))
        (Or.inr hH)
    rw [add_zero, ENNReal.div_self hH hHtop] at this
    have h₁ := ((ENNReal.continuous_rpow_const (y := p - 1)).tendsto 1).comp this
    rw [ENNReal.one_rpow] at h₁
    exact h₁
  -- The bounds `F i` for the difference quotients of the interpolants.
  set F : ι → ℝ → ℝ≥0∞ := fun i t ↦ c i * H⁻¹ * ∑ n ∈ Finset.range ⌈T / τ i⌉₊,
    (Ioc (n * τ i - h) (n * τ i)).indicator
      (fun _ ↦ edist (U i n) (U i (n + 1)) ^ p / (τ i : ℝ≥0∞) ^ (p - 1)) t
  have hF_meas i : Measurable (F i) :=
    measurable_const.mul (Finset.measurable_sum _ fun _ _ ↦
      measurable_const.indicator measurableSet_Ioc)
  have hF_int i : ∫⁻ t in Ioc 0 (T - h), F i t ≤ c i * S i := by
    refine setLIntegral_le_lintegral _ _ |>.trans_eq ?_
    rw [lintegral_const_mul _ (Finset.measurable_sum _ fun _ _ ↦
      measurable_const.indicator measurableSet_Ioc), lintegral_finsetSum _ fun _ _ ↦
      measurable_const.indicator measurableSet_Ioc]
    simp only [lintegral_indicator_const measurableSet_Ioc, Real.volume_Ioc, sub_sub_cancel]
    rw [← Finset.sum_mul, mul_comm _ H, ← mul_assoc, mul_assoc (c i),
      ENNReal.inv_mul_cancel hH hHtop, mul_one]
  -- Fatou's lemma.
  calc ∫⁻ t in Ioc 0 (T - h), (edist (u t) (u (t + h)) / H) ^ p
      ≤ ∫⁻ t in Ioc 0 (T - h), liminf (fun i ↦ F i t) l := by
        refine setLIntegral_mono' measurableSet_Ioc fun t ht ↦ ?_
        have hts : t ∈ Icc 0 T := ⟨ht.1.le, by linarith [ht.2]⟩
        have hth : t + h ∈ Icc 0 T := ⟨by linarith [ht.1], by linarith [ht.2]⟩
        have hg : Monotone fun x : ℝ≥0∞ ↦ (x / H) ^ p := fun _ _ hxy ↦
          ENNReal.rpow_le_rpow (by gcongr) (by linarith)
        calc (edist (u t) (u (t + h)) / H) ^ p
            ≤ (liminf (fun i ↦ edist (U i ⌈t / τ i⌉₊) (U i ⌈(t + h) / τ i⌉₊)) l / H) ^ p :=
              hg (hu t hts (t + h) hth)
          _ = liminf (fun i ↦ (edist (U i ⌈t / τ i⌉₊) (U i ⌈(t + h) / τ i⌉₊) / H) ^ p) l :=
              hg.map_liminf_of_continuousAt _ ((ENNReal.continuous_rpow_const.comp
                (ENNReal.continuous_div_const H hH)).continuousAt)
          _ ≤ liminf (fun i ↦ F i t) l :=
              liminf_le_liminf (Eventually.of_forall fun i ↦
                edist_ceil_div_div_rpow_le hp (hτ i) hh ht)
    _ ≤ liminf (fun i ↦ ∫⁻ t in Ioc 0 (T - h), F i t) l :=
        lintegral_liminf_le fun i ↦ hF_meas i
    _ ≤ liminf (fun i ↦ c i * S i) l := liminf_le_liminf (Eventually.of_forall hF_int)
    _ ≤ limsup c l * liminf S l :=
        ENNReal.liminf_mul_le (Or.inl (by simp [hc.limsup_eq])) (Or.inl (by simp [hc.limsup_eq]))
    _ = liminf S l := by rw [hc.limsup_eq, one_mul]

/-- **Lower semicontinuity of the action along piecewise constant interpolants.** Let `U i` be
sequences of points with time steps `τ i > 0` tending to `0` along a countably generated filter,
and let `u` be a curve with `d(u s, u t) ≤ liminf_i d(U i ⌈s / τ i⌉₊, U i ⌈t / τ i⌉₊)` for all
`s, t ∈ [0, T]`. Then for `1 < p` the `p`-action of `u` over `[0, T]` is at most the lower limit of
the discrete `p`-actions `∑_{n < ⌈T / τ i⌉₊} d(U i n, U i (n + 1)) ^ p / τ i ^ (p - 1)`. When this
lower limit is finite, `u` is absolutely continuous on `[0, T]` by
`TauCeti.absolutelyContinuousOnInterval_of_liminf_sum_edist_rpow_ne_top`. -/
theorem curveAction_le_liminf_sum_edist_rpow [l.IsCountablyGenerated] (hp : 1 < p)
    (hτ : ∀ i, 0 < τ i) (hτ0 : Tendsto τ l (𝓝 0)) (hT : 0 ≤ T)
    (hu : ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T,
      edist (u s) (u t) ≤ liminf (fun i ↦ edist (U i ⌈s / τ i⌉₊) (U i ⌈t / τ i⌉₊)) l) :
    curveAction p u 0 T ≤ liminf (fun i ↦ ∑ n ∈ Finset.range ⌈T / τ i⌉₊,
      edist (U i n) (U i (n + 1)) ^ p / (τ i : ℝ≥0∞) ^ (p - 1)) l := by
  by_cases hS : liminf (fun i ↦ ∑ n ∈ Finset.range ⌈T / τ i⌉₊,
      edist (U i n) (U i (n + 1)) ^ p / (τ i : ℝ≥0∞) ^ (p - 1)) l = ∞
  · rw [hS]
    exact le_top
  have hac := absolutelyContinuousOnInterval_of_liminf_sum_edist_rpow_ne_top hp hτ hτ0 hT hu hS
  refine le_of_tendsto (hac.tendsto_lintegral_edist_div_rpow hp.le hT) ?_
  filter_upwards [self_mem_nhdsWithin] with h (hh : 0 < h)
  exact lintegral_edist_div_rpow_le_liminf hp.le hτ hτ0 hu hh

end PseudoMetricSpace

end TauCeti
