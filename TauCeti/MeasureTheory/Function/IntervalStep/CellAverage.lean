/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.Floor
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# Cell averages on a uniform partition

For the uniform partition of `(a, b)` into `N` cells of length `h = (b - a) / N`, this file
defines the index of the cell containing a point (`MeasureTheory.intervalCellIndex`), the average
of a function over a cell (`MeasureTheory.intervalCellAverage`) and the cellwise average, which is
constant on each cell (`MeasureTheory.intervalStepAverage`).

The cellwise average is a contraction in `L²(a, b)`
(`MeasureTheory.integral_norm_intervalStepAverage_sq_le`), by Jensen's inequality on each cell,
and it converges to the function in `L²(a, b)` as `N → ∞`
(`MeasureTheory.tendsto_integral_norm_intervalStepAverage_sub_sq`), by density of continuous
functions. This is the `L²` counterpart, by averaging rather than by sampling, of the
approximation by interval step functions `MeasureTheory.intervalStep`.
-/

public section

noncomputable section

open Filter Set Topology
open scoped Interval

namespace MeasureTheory

variable {E : Type*} [NormedAddCommGroup E]

/-! ### The cells of a uniform partition -/

/-- The index `k` of the cell `(a + (k - 1) h, a + k h]` of the uniform partition of step `h`
starting at `a` that contains `t`. -/
def intervalCellIndex (a h t : ℝ) : ℕ := ⌈(t - a) / h⌉₊

theorem intervalCellIndex_eq {a h t : ℝ} (hh : 0 < h) {k : ℕ}
    (ht : t ∈ Ioc (a + k * h) (a + (k + 1) * h)) : intervalCellIndex a h t = k + 1 := by
  rw [intervalCellIndex, Nat.ceil_eq_iff (Nat.succ_ne_zero k), Nat.succ_sub_one, lt_div_iff₀ hh,
    div_le_iff₀ hh]
  push_cast
  constructor <;> linarith [ht.1, ht.2]

theorem measurable_intervalCellIndex (a h : ℝ) : Measurable (intervalCellIndex a h) :=
  ((measurable_id.sub_const a).div_const h).nat_ceil

/-- The last node of the partition of `[a, b]` into `N` cells is `b`. -/
private theorem add_natCast_mul_sub_div_natCast_self (a b : ℝ) {N : ℕ} (hN : 0 < N) :
    a + N * ((b - a) / N) = b := by
  rw [mul_div_cancel₀ _ (Nat.cast_ne_zero.2 hN.ne')]
  ring

/-- The cells of the partition of `[a, b]`, `a < b`, into `N` cells have positive length
`(b - a) / N`. -/
theorem sub_div_natCast_pos {a b : ℝ} (hab : a < b) {N : ℕ} (hN : 0 < N) : 0 < (b - a) / N :=
  div_pos (sub_pos.2 hab) (Nat.cast_pos.2 hN)

/-- The nodes `a + k (b - a) / N`, `k ≤ N`, of the partition of `[a, b]` into `N` cells lie in
`[a, b]`. -/
theorem add_natCast_mul_sub_div_natCast_mem_Icc {a b : ℝ} (hab : a ≤ b) {N k : ℕ} (hN : 0 < N)
    (hk : k ≤ N) : a + k * ((b - a) / N) ∈ Icc a b := by
  have hh : 0 ≤ (b - a) / N := div_nonneg (sub_nonneg.2 hab) N.cast_nonneg
  refine ⟨le_add_of_nonneg_right (mul_nonneg k.cast_nonneg hh), ?_⟩
  calc a + k * ((b - a) / N) ≤ a + N * ((b - a) / N) := by gcongr
    _ = b := add_natCast_mul_sub_div_natCast_self a b hN

/-- The cells `[a + k h, a + (k + 1) h]`, `k < N`, of the partition of `[a, b]` into `N` cells of
length `h = (b - a) / N` lie in `[a, b]`. -/
theorem Icc_add_natCast_mul_sub_div_natCast_subset_Icc {a b : ℝ} (hab : a ≤ b) {N k : ℕ}
    (hN : 0 < N) (hk : k < N) :
    Icc (a + k * ((b - a) / N)) (a + (k + 1) * ((b - a) / N)) ⊆ Icc a b := by
  have h₂ := add_natCast_mul_sub_div_natCast_mem_Icc hab hN hk
  push_cast at h₂
  exact Icc_subset_Icc (add_natCast_mul_sub_div_natCast_mem_Icc hab hN hk.le).1 h₂.2

/-- On `(a, b)`, the index of the cell of the partition into `N` cells lies between `1` and `N`. -/
theorem intervalCellIndex_mem_Icc {a b t : ℝ} (ht : t ∈ Ioo a b) {N : ℕ} (hN : 0 < N) :
    intervalCellIndex a ((b - a) / N) t ∈ Icc 1 N := by
  have hh : 0 < (b - a) / N := sub_div_natCast_pos (ht.1.trans ht.2) hN
  have hpos : 0 < (t - a) / ((b - a) / N) := div_pos (sub_pos.2 ht.1) hh
  refine ⟨Nat.one_le_iff_ne_zero.2 fun h ↦ ?_, Nat.ceil_le.2 ?_⟩
  · rw [intervalCellIndex, Nat.ceil_eq_zero] at h
    linarith
  · rw [div_le_iff₀ hh, mul_div_cancel₀ _ (Nat.cast_ne_zero.2 hN.ne')]
    linarith [ht.2]

/-- **The cell of a point.** A point `t ∈ (a, b)` lies in a cell `(a + k h, a + (k + 1) h]`,
`k < N`, of the partition into `N` cells of length `h = (b - a) / N`, and its cell index is
`k + 1`. -/
theorem exists_intervalCellIndex_eq {a b t : ℝ} (ht : t ∈ Ioo a b) {N : ℕ} (hN : 0 < N) :
    ∃ k < N, intervalCellIndex a ((b - a) / N) t = k + 1 ∧
      t ∈ Ioc (a + k * ((b - a) / N)) (a + (k + 1) * ((b - a) / N)) := by
  have hh : 0 < (b - a) / N := sub_div_natCast_pos (ht.1.trans ht.2) hN
  obtain ⟨h₁, hN'⟩ := intervalCellIndex_mem_Icc ht hN
  obtain ⟨k, hk⟩ : ∃ k, intervalCellIndex a ((b - a) / N) t = k + 1 :=
    ⟨_, (Nat.sub_add_cancel h₁).symm⟩
  have hc := (Nat.ceil_eq_iff (Nat.succ_ne_zero k)).1 hk
  rw [lt_div_iff₀ hh, div_le_iff₀ hh] at hc
  push_cast at hc
  exact ⟨k, by omega, hk, by constructor <;> linarith [hc.1, hc.2]⟩

/-- The integral over `(a, b)` is the sum of the integrals over the cells of the partition into
`N` cells. -/
theorem integral_Ioo_eq_sum [NormedSpace ℝ E] {a b : ℝ} (hab : a < b) {N : ℕ}
    (hN : 0 < N) {f : ℝ → E}
    (hf : ∀ k < N, IntervalIntegrable f volume (a + k * ((b - a) / N))
      (a + (k + 1) * ((b - a) / N))) :
    ∫ t in Ioo a b, f t = ∑ k ∈ Finset.range N,
      ∫ t in (a + k * ((b - a) / N))..(a + (k + 1) * ((b - a) / N)), f t := by
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun k : ℕ ↦ a + (k : ℝ) * ((b - a) / N)) (n := N) fun k hk ↦ by
      push_cast
      exact hf k hk
  push_cast at hsum
  rw [zero_mul, add_zero, add_natCast_mul_sub_div_natCast_self a b hN] at hsum
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab.le, ← hsum]

/-- **Integrals of cellwise constant functions.** For the partition of `(a, b)` into `N` cells of
length `h = (b - a) / N`, the integral of `t ↦ F (intervalCellIndex a h t)` is
`∑ₖ h F (k + 1)`. -/
theorem integral_Ioo_comp_intervalCellIndex [NormedSpace ℝ E] [CompleteSpace E] {a b : ℝ}
    (hab : a < b) {N : ℕ} (hN : 0 < N) (F : ℕ → E) :
    ∫ t in Ioo a b, F (intervalCellIndex a ((b - a) / N) t) =
      ∑ k ∈ Finset.range N, ((b - a) / N) • F (k + 1) := by
  have hh : 0 < (b - a) / N := sub_div_natCast_pos hab hN
  have hae (k : ℕ) : ∀ᵐ t ∂volume,
      t ∈ Ι (a + k * ((b - a) / N)) (a + (k + 1) * ((b - a) / N)) →
        F (intervalCellIndex a ((b - a) / N) t) = F (k + 1) := Eventually.of_forall fun t ht ↦ by
    rw [uIoc_of_le (by nlinarith)] at ht
    rw [intervalCellIndex_eq hh ht]
  rw [integral_Ioo_eq_sum hab hN fun k _ ↦ (intervalIntegrable_const (c := F (k + 1))).congr_ae
    ((ae_restrict_iff' measurableSet_uIoc).2 ((hae k).mono fun t ht ht' ↦ (ht ht').symm))]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [intervalIntegral.integral_congr_ae (hae k), intervalIntegral.integral_const]
  congr 1
  ring

/-- A cellwise constant function on `(a, b)` is in every `Lᵖ`. -/
theorem memLp_comp_intervalCellIndex {a b : ℝ} {N : ℕ} (hN : 0 < N) (F : ℕ → E)
    (p : ENNReal) :
    MemLp (fun t ↦ F (intervalCellIndex a ((b - a) / N) t)) p (volume.restrict (Ioo a b)) := by
  refine MemLp.of_bound ((StronglyMeasurable.of_discrete (f := F)).comp_measurable
    (measurable_intervalCellIndex _ _)).aestronglyMeasurable
    (∑ k ∈ Finset.range (N + 1), ‖F k‖) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  exact Finset.single_le_sum (f := fun k ↦ ‖F k‖) (fun _ _ ↦ norm_nonneg _)
    (Finset.mem_range.2 (Nat.lt_succ_of_le (intervalCellIndex_mem_Icc ht hN).2))

/-- An integrable function on `(a, b)` is integrable on each cell of a uniform partition. -/
theorem IntegrableOn.intervalIntegrable_cell {a b : ℝ} {g : ℝ → E}
    (hg : IntegrableOn g (Ioo a b)) (hab : a ≤ b) {N k : ℕ} (hN : 0 < N) (hk : k < N) :
    IntervalIntegrable g volume (a + k * ((b - a) / N)) (a + (k + 1) * ((b - a) / N)) := by
  have hh : 0 ≤ (b - a) / N := div_nonneg (sub_nonneg.2 hab) N.cast_nonneg
  have hI : IntegrableOn g (Icc a b) := (integrableOn_Icc_iff_integrableOn_Ioo (μ := volume)).2 hg
  refine (hI.mono_set ?_).intervalIntegrable
  rw [uIcc_of_le (by nlinarith)]
  exact Icc_add_natCast_mul_sub_div_natCast_subset_Icc hab hN hk

/-! ### Cell averages -/

section Average

variable [NormedSpace ℝ E]

/-- The average of `g` over the cell `(a + k h, a + (k + 1) h]`. -/
def intervalCellAverage (g : ℝ → E) (a h : ℝ) (k : ℕ) : E :=
  h⁻¹ • ∫ s in (a + k * h)..(a + (k + 1) * h), g s

/-- The average of `g` over the cell `(a + k h, a + (k + 1) h]` is `h⁻¹ ∫ g` over the cell. -/
theorem intervalCellAverage_def (g : ℝ → E) (a h : ℝ) (k : ℕ) :
    intervalCellAverage g a h k = h⁻¹ • ∫ s in (a + k * h)..(a + (k + 1) * h), g s := (rfl)

/-- The cellwise average of `g`, constant on each cell `(a + (k - 1) h, a + k h]`. -/
def intervalStepAverage (g : ℝ → E) (a h t : ℝ) : E :=
  intervalCellAverage g a h (intervalCellIndex a h t - 1)

/-- On the cell `(a + k h, a + (k + 1) h]`, the cellwise average is the average over that cell. -/
theorem intervalStepAverage_eq (g : ℝ → E) {a h t : ℝ} (hh : 0 < h) {k : ℕ}
    (ht : t ∈ Ioc (a + k * h) (a + (k + 1) * h)) :
    intervalStepAverage g a h t = intervalCellAverage g a h k := by
  rw [intervalStepAverage, intervalCellIndex_eq hh ht, Nat.add_sub_cancel]

/-- The cellwise average is in every `Lᵖ` on `(a, b)`. -/
theorem memLp_intervalStepAverage {a b : ℝ} {N : ℕ} (hN : 0 < N) (g : ℝ → E) (p : ENNReal) :
    MemLp (intervalStepAverage g a ((b - a) / N)) p (volume.restrict (Ioo a b)) :=
  memLp_comp_intervalCellIndex hN (fun n ↦ intervalCellAverage g a ((b - a) / N) (n - 1)) p

/-- **Jensen's inequality on a cell.** `h ‖avg_I g‖² ≤ ∫_I ‖g‖²` for a cell `I` of length `h`. -/
theorem mul_norm_intervalCellAverage_sq_le [CompleteSpace E] {g : ℝ → E} {a h : ℝ} (hh : 0 < h)
    {k : ℕ}
    (hg : IntervalIntegrable g volume (a + k * h) (a + (k + 1) * h))
    (hg2 : IntervalIntegrable (fun s ↦ ‖g s‖ ^ 2) volume (a + k * h) (a + (k + 1) * h)) :
    h * ‖intervalCellAverage g a h k‖ ^ 2 ≤ ∫ s in (a + k * h)..(a + (k + 1) * h), ‖g s‖ ^ 2 := by
  have hlt : a + k * h < a + (k + 1) * h := by nlinarith
  have hpq := hlt.le
  have hvol : volume.real (Ioc (a + k * h) (a + (k + 1) * h)) = h := by
    rw [Real.volume_real_Ioc_of_le hpq]
    ring
  have hJ := (convexOn_univ_norm.pow (fun _ _ ↦ norm_nonneg _) 2).map_set_average_le
    (continuous_norm.pow 2).continuousOn isClosed_univ
    (by rw [Real.volume_Ioc]; exact (ENNReal.ofReal_pos.2 (sub_pos.2 hlt)).ne')
    (by simp [Real.volume_Ioc]) (by simp) hg.1 (by simpa [Function.comp_def] using hg2.1)
  simp only [Pi.pow_apply, setAverage_eq, hvol, smul_eq_mul] at hJ
  rw [intervalCellAverage_def, intervalIntegral.integral_of_le hpq,
    intervalIntegral.integral_of_le hpq]
  calc h * ‖h⁻¹ • ∫ s in Ioc (a + k * h) (a + (k + 1) * h), g s‖ ^ 2
      ≤ h * (h⁻¹ * ∫ s in Ioc (a + k * h) (a + (k + 1) * h), ‖g s‖ ^ 2) := by gcongr
    _ = _ := by field_simp

/-- The cellwise average is a contraction in `L²(a, b)`. -/
theorem integral_norm_intervalStepAverage_sq_le [CompleteSpace E] {a b : ℝ} (hab : a < b) {N : ℕ}
    (hN : 0 < N)
    {g : ℝ → E} (hg : MemLp g 2 (volume.restrict (Ioo a b))) :
    ∫ t in Ioo a b, ‖intervalStepAverage g a ((b - a) / N) t‖ ^ 2 ≤ ∫ t in Ioo a b, ‖g t‖ ^ 2 := by
  have hh : 0 < (b - a) / N := sub_div_natCast_pos hab hN
  have hg2 : IntegrableOn (fun s ↦ ‖g s‖ ^ 2) (Ioo a b) :=
    (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).1 hg
  rw [integral_Ioo_eq_sum hab hN fun k hk ↦ hg2.intervalIntegrable_cell hab.le hN hk]
  simp only [intervalStepAverage]
  rw [integral_Ioo_comp_intervalCellIndex hab hN
    (fun n ↦ ‖intervalCellAverage g a ((b - a) / N) (n - 1)‖ ^ 2)]
  refine Finset.sum_le_sum fun k hk ↦ ?_
  simpa using mul_norm_intervalCellAverage_sq_le hh
    (IntegrableOn.intervalIntegrable_cell (hg.integrable one_le_two) hab.le hN
      (Finset.mem_range.1 hk))
    (hg2.intervalIntegrable_cell hab.le hN (Finset.mem_range.1 hk))

/-- `∑_{j < k} h ‖avg_j g‖² ≤ ∫ ‖g‖²` for the cells `j < k ≤ N` of the partition into `N` cells
of length `h`. -/
theorem sum_mul_norm_intervalCellAverage_sq_le [CompleteSpace E] {a b : ℝ} (hab : a < b) {N : ℕ}
    (hN : 0 < N)
    {g : ℝ → E} (hg : MemLp g 2 (volume.restrict (Ioo a b))) {k : ℕ} (hk : k ≤ N) :
    ∑ j ∈ Finset.range k, (b - a) / N * ‖intervalCellAverage g a ((b - a) / N) j‖ ^ 2 ≤
      ∫ t in Ioo a b, ‖g t‖ ^ 2 := by
  have hsum := integral_Ioo_comp_intervalCellIndex hab hN
    (fun n ↦ ‖intervalCellAverage g a ((b - a) / N) (n - 1)‖ ^ 2)
  simp only [Nat.add_sub_cancel, smul_eq_mul] at hsum
  refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hk)
    fun _ _ _ ↦ by positivity).trans ?_
  rw [← hsum]
  exact integral_norm_intervalStepAverage_sq_le hab hN hg

/-- On `(a, b)`, the cellwise average of `g - φ` is the difference of the cellwise averages. -/
theorem intervalStepAverage_sub {a b t : ℝ} (ht : t ∈ Ioo a b) {N : ℕ} (hN : 0 < N)
    {g φ : ℝ → E} (hg : IntegrableOn g (Ioo a b)) (hφ : IntegrableOn φ (Ioo a b)) :
    intervalStepAverage (fun s ↦ g s - φ s) a ((b - a) / N) t =
      intervalStepAverage g a ((b - a) / N) t - intervalStepAverage φ a ((b - a) / N) t := by
  have hab := (ht.1.trans ht.2).le
  obtain ⟨k, hk, hidx, -⟩ := exists_intervalCellIndex_eq ht hN
  simp only [intervalStepAverage, intervalCellAverage_def, hidx, Nat.add_sub_cancel]
  rw [intervalIntegral.integral_sub (hg.intervalIntegrable_cell hab hN hk)
    (hφ.intervalIntegrable_cell hab hN hk), smul_sub]

/-- If `φ` varies by at most `η` over distances at most `h` on `[a, b]`, its cellwise average on
cells of length `h` is within `η` of `φ` on `(a, b)`. -/
private theorem norm_intervalStepAverage_sub_le [CompleteSpace E] {φ : ℝ → E} (hφ : Continuous φ)
    {a b t η : ℝ} (ht : t ∈ Ioo a b) {N : ℕ} (hN : 0 < N)
    (hη : ∀ s ∈ Icc a b, |s - t| ≤ (b - a) / N → ‖φ s - φ t‖ ≤ η) :
    ‖intervalStepAverage φ a ((b - a) / N) t - φ t‖ ≤ η := by
  have hh : 0 < (b - a) / N := sub_div_natCast_pos (ht.1.trans ht.2) hN
  obtain ⟨k, hk, -, hmem⟩ := exists_intervalCellIndex_eq ht hN
  have hsub := Icc_add_natCast_mul_sub_div_natCast_subset_Icc (ht.1.trans ht.2).le hN hk
  rw [intervalStepAverage_eq φ hh hmem]
  set h := (b - a) / N
  set p := a + k * h
  set q := a + (k + 1) * h
  have hpq : p ≤ q := hmem.1.le.trans hmem.2
  have hlen : q - p = h := by simp only [p, q]; ring
  have hbound : ‖∫ s in p..q, (φ s - φ t)‖ ≤ η * h := by
    rw [← hlen, ← abs_of_nonneg (sub_nonneg.2 hpq)]
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun s hs ↦ ?_
    rw [uIoc_of_le hpq] at hs
    refine hη s (hsub (Ioc_subset_Icc_self hs)) (abs_le.2 ⟨?_, ?_⟩) <;>
      linarith [hs.1, hs.2, hmem.1, hmem.2]
  have heq : intervalCellAverage φ a h k - φ t = h⁻¹ • ∫ s in p..q, (φ s - φ t) := by
    rw [intervalIntegral.integral_sub (hφ.intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_const, hlen, smul_sub, inv_smul_smul₀ hh.ne',
      intervalCellAverage_def]
  rw [heq, norm_smul, norm_inv, Real.norm_of_nonneg hh.le]
  calc h⁻¹ * ‖∫ s in p..q, (φ s - φ t)‖ ≤ h⁻¹ * (η * h) := by gcongr
    _ = η := by field_simp

/-- The `L²` estimate behind `tendsto_integral_norm_intervalStepAverage_sub_sq`, for a continuous
approximation `φ` of `g` that varies by less than `η` over distances less than `δ`. -/
private theorem integral_norm_intervalStepAverage_sub_sq_le [CompleteSpace E] {a b : ℝ}
    (hab : a < b) {N : ℕ} (hN : 0 < N)
    {g φ : ℝ → E} (hg : MemLp g 2 (volume.restrict (Ioo a b))) (hφc : Continuous φ)
    (hφL : MemLp φ 2 (volume.restrict (Ioo a b))) {η δ : ℝ}
    (hδφ : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, dist x y < δ → dist (φ x) (φ y) < η)
    (hhδ : (b - a) / N < δ) :
    ∫ t in Ioo a b, ‖intervalStepAverage g a ((b - a) / N) t - g t‖ ^ 2 ≤
      3 * ((∫ t in Ioo a b, ‖g t - φ t‖ ^ 2) + η ^ 2 * (b - a) +
        ∫ t in Ioo a b, ‖g t - φ t‖ ^ 2) := by
  set h := (b - a) / N with hh_def
  set μ := volume.restrict (Ioo a b)
  have hstep (f : ℝ → E) : MemLp (intervalStepAverage f a h) 2 μ :=
    memLp_intervalStepAverage hN f 2
  have hgφ : MemLp (fun t ↦ g t - φ t) 2 μ := hg.sub hφL
  have hle := integral_norm_sq_le_three_mul (μ := μ)
    (f := fun t ↦ intervalStepAverage g a h t - g t)
    (hstep fun s ↦ g s - φ s) ((hstep φ).sub hφL) (hφL.sub hg) <| by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      rw [intervalStepAverage_sub ht hN (hg.integrable one_le_two) (hφL.integrable one_le_two),
        ← hh_def]
      simp only [Pi.sub_apply]
      abel
  refine hle.trans (mul_le_mul_of_nonneg_left (add_le_add_three
    (integral_norm_intervalStepAverage_sq_le hab hN hgφ) ?_ (le_of_eq ?_)) (by norm_num))
  · have hpt : ∀ t ∈ Ioo a b, ‖intervalStepAverage φ a h t - φ t‖ ^ 2 ≤ η ^ 2 := fun t ht ↦ by
      refine pow_le_pow_left₀ (norm_nonneg _) (norm_intervalStepAverage_sub_le hφc ht hN
        fun s hs hst ↦ ?_) 2
      rw [← dist_eq_norm]
      exact (hδφ s hs t (Ioo_subset_Icc_self ht)
        (by rw [Real.dist_eq]; exact hst.trans_lt hhδ)).le
    calc ∫ t in Ioo a b, ‖intervalStepAverage φ a h t - φ t‖ ^ 2 ≤ ∫ _ in Ioo a b, η ^ 2 :=
          setIntegral_mono_on ((memLp_two_iff_integrable_sq_norm
            ((hstep φ).sub hφL).aestronglyMeasurable).1 ((hstep φ).sub hφL))
            (integrableOn_const (by simp)) measurableSet_Ioo hpt
      _ = η ^ 2 * (b - a) := by
          rw [setIntegral_const, smul_eq_mul, measureReal_def, Real.volume_Ioo,
            ENNReal.toReal_ofReal (sub_nonneg.2 hab.le), mul_comm]
  · exact integral_congr_ae (Eventually.of_forall fun t ↦ by simp only [Pi.sub_apply, norm_sub_rev])

/-- **Cellwise averages converge in `L²`.** For `g ∈ L²(a, b)`, the averages of `g` over the
cells of the uniform partition into `N` cells converge to `g` in `L²(a, b)` as `N → ∞`. -/
theorem tendsto_integral_norm_intervalStepAverage_sub_sq [CompleteSpace E] {a b : ℝ} (hab : a < b)
    {g : ℝ → E} (hg : MemLp g 2 (volume.restrict (Ioo a b))) :
    Tendsto (fun N : ℕ ↦ ∫ t in Ioo a b, ‖intervalStepAverage g a ((b - a) / N) t - g t‖ ^ 2)
      atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- Approximate `g` by a continuous `φ` in `L²(a, b)`.
  have hg' : MemLp ((Ioo a b).indicator g) (ENNReal.ofReal 2) volume := by
    rw [ENNReal.ofReal_ofNat]
    exact (memLp_indicator_iff_restrict measurableSet_Ioo.nullMeasurableSet).2 hg
  obtain ⟨φ, -, hφε, hφc, hφL⟩ :=
    hg'.exists_hasCompactSupport_integral_rpow_sub_le two_pos (show 0 < ε / 12 by positivity)
  rw [ENNReal.ofReal_ofNat] at hφL hg'
  have hφL' : MemLp φ 2 (volume.restrict (Ioo a b)) := hφL.restrict _
  have hφε' : ∫ x, ‖(Ioo a b).indicator g x - φ x‖ ^ 2 ≤ ε / 12 := by
    simpa only [Real.rpow_two] using hφε
  have hgφ2 : ∫ t in Ioo a b, ‖g t - φ t‖ ^ 2 ≤ ε / 12 :=
    calc ∫ t in Ioo a b, ‖g t - φ t‖ ^ 2
        = ∫ t in Ioo a b, ‖(Ioo a b).indicator g t - φ t‖ ^ 2 :=
          setIntegral_congr_fun measurableSet_Ioo fun t ht ↦ by simp [indicator_of_mem ht]
      _ ≤ ∫ t, ‖(Ioo a b).indicator g t - φ t‖ ^ 2 :=
          setIntegral_le_integral ((memLp_two_iff_integrable_sq_norm
            (hg'.sub hφL).aestronglyMeasurable).1 (hg'.sub hφL))
            (Eventually.of_forall fun _ ↦ by positivity)
      _ ≤ ε / 12 := hφε'
  -- Uniform continuity of `φ` on `[a, b]`.
  set η := Real.sqrt (ε / (12 * (b - a)))
  have hη : 0 < η := Real.sqrt_pos.2 (div_pos hε (by linarith))
  obtain ⟨δ, hδ, hδφ⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hφc.continuousOn) η hη
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt ((b - a) / δ)
  refine ⟨N₀ + 1, fun N hN ↦ ?_⟩
  have hN0 : 0 < N := by omega
  have hhδ : (b - a) / N < δ := by
    rw [div_lt_iff₀ (Nat.cast_pos.2 hN0)]
    rw [div_lt_iff₀ hδ] at hN₀
    have : (N₀ : ℝ) + 1 ≤ N := by exact_mod_cast hN
    nlinarith
  have hηε : η ^ 2 * (b - a) = ε / 12 := by
    rw [Real.sq_sqrt (div_nonneg hε.le (by linarith))]
    field_simp
  have hnn : 0 ≤ ∫ t in Ioo a b, ‖intervalStepAverage g a ((b - a) / N) t - g t‖ ^ 2 :=
    setIntegral_nonneg measurableSet_Ioo fun _ _ ↦ by positivity
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
  have := integral_norm_intervalStepAverage_sub_sq_le hab hN0 hg hφc hφL' hδφ hhδ
  linarith

end Average

end MeasureTheory
