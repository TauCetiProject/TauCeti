/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.Data.List.TFAE
public import TauCeti.MeasureTheory.Measure.Haar.UnitAddTorus
public import TauCeti.NumberTheory.Equidistribution.Basic
public import TauCeti.NumberTheory.Equidistribution.Weyl
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Positivity
import TauCeti.Analysis.Fourier.Monomial

/-!
# Linear equidistribution, van der Corput's difference theorem, and Weyl's polynomial theorem

This file proves the classical equidistribution theorems for linear and polynomial orbits in the
finite-dimensional unit torus `UnitAddTorus d`:

* `TauCeti.linear_equidistribution_tfae` and `TauCeti.linear_equidistributionInt_tfae`: for
  `α, β : UnitAddTorus d`, the linear sequence `n ↦ n • α + β` (indexed by `ℕ` or `ℤ`) is
  equidistributed for Haar measure iff it is totally equidistributed iff `TorusIrrational α`.
* `TauCeti.vanDerCorput_inequality`: van der Corput's finite lag inequality bounding
  `H² ‖∑_{n < N} b n‖²` in terms of the squared norm sum and shifted correlations of `b : ℕ → ℂ`.
* `TauCeti.tendsto_cesaro_zero_of_forall_correlation` and `TauCeti.vanDerCorput_difference`:
  van der Corput's difference theorem for bounded complex sequences and for torus sequences.
* `TauCeti.weyl_polynomial`: Weyl's polynomial equidistribution theorem — if `s ≥ 1` and `α s` is
  irrational, then `n ↦ ∑ j ∈ range (s + 1), n ^ j • α j` is equidistributed for Haar measure.
* `TauCeti.polynomial_equidistribution_tfae`, `TauCeti.polynomial_equidistribution_iff`,
  `TauCeti.polynomial_total_equidistribution_iff`, and
  `TauCeti.polynomial_total_equidistributionInt_iff`: full characterization of equidistribution and
  total equidistribution (on `ℕ` and `ℤ`) for polynomial sequences in `UnitAddTorus d`.

## References

* T. Tao, *Higher Order Fourier Analysis*, Graduate Studies in Mathematics 142, AMS, 2012,
  §1.1.1 (Lemma 1.1.6, Corollary 1.1.7, Corollary 1.1.9, Exercises 1.1.5 and 1.1.6).
-/

public section

open Filter Finset MeasureTheory Topology
open scoped ENNReal

namespace TauCeti

section Linear

variable {d : Type*} [Fintype d]

/-- If `α` is irrational in `UnitAddTorus d`, then the linear orbit `n ↦ n • α + β` is
equidistributed for Haar probability. -/
private theorem asympEquidistributed_linear_of_torusIrrational {α : UnitAddTorus d}
    (hα : TorusIrrational α) (β : UnitAddTorus d) :
    AsympEquidistributed (fun n : ℕ ↦ n • α + β)
      (volume : Measure (UnitAddTorus d)).toProbabilityMeasure := by
  rw [weyl_criterion]
  intro k hk
  set ζ : ℂ := UnitAddTorus.mFourier k α
  have hζne : ζ ≠ 1 := torusIrrational_iff_mFourier.mp hα k hk
  have hζ1 : ‖ζ‖ = 1 := UnitAddTorus.norm_mFourier_apply k α
  have hbound : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)⁻¹ * (2 / ‖ζ - 1‖)) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp
      ((tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1))).mul_const
      (2 / ‖ζ - 1‖)
  refine squeeze_zero_norm (fun n ↦ ?_) hbound
  have hsum : ∑ i ∈ range (n + 1), UnitAddTorus.mFourier k (i • α + β) =
      UnitAddTorus.mFourier k β * ((ζ ^ (n + 1) - 1) / (ζ - 1)) := by
    have hterm (i : ℕ) :
        UnitAddTorus.mFourier k (i • α + β) = UnitAddTorus.mFourier k β * ζ ^ i := by
      rw [UnitAddTorus.mFourier_apply_add, UnitAddTorus.mFourier_apply_nsmul, mul_comm]
    simp_rw [hterm, ← mul_sum, geom_sum_eq hζne]
  rw [hsum, norm_mul, norm_inv, Complex.norm_natCast, norm_mul, UnitAddTorus.norm_mFourier_apply,
    one_mul, norm_div]
  gcongr
  calc ‖ζ ^ (n + 1) - 1‖
      ≤ ‖ζ ^ (n + 1)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_pow, hζ1, one_pow, norm_one]; norm_num

/-- **Equidistribution of linear orbits on `UnitAddTorus d`**: for `α, β : UnitAddTorus d`,
equidistribution of `n ↦ n • α + β`, total equidistribution of `n ↦ n • α + β`, and irrationality
of `α` are equivalent. -/
theorem linear_equidistribution_tfae (α β : UnitAddTorus d) :
    List.TFAE [
      AsympEquidistributed (fun n : ℕ ↦ n • α + β)
        (volume : Measure (UnitAddTorus d)).toProbabilityMeasure,
      TotallyAsympEquidistributed (fun n : ℕ ↦ n • α + β)
        (volume : Measure (UnitAddTorus d)).toProbabilityMeasure,
      TorusIrrational α
    ] := by
  tfae_have 3 → 2 := by
    intro hα
    rw [totallyAsympEquidistributed_def]
    intro q r hq
    have heq : (fun n : ℕ ↦ (q * n + r) • α + β) = fun n : ℕ ↦ n • (q • α) + (r • α + β) := by
      funext n
      rw [add_nsmul, mul_nsmul, add_assoc]
    rw [heq]
    exact asympEquidistributed_linear_of_torusIrrational (hα.nsmul hq.ne') (r • α + β)
  tfae_have 2 → 1 := TotallyAsympEquidistributed.asympEquidistributed
  tfae_have 1 → 3 := by
    intro h
    rw [torusIrrational_iff_mFourier]
    intro k hk h1
    have hlim := (weyl_criterion.mp h) k hk
    have hconst (n : ℕ) :
        ((n + 1 : ℕ) : ℂ)⁻¹ * ∑ i ∈ range (n + 1), UnitAddTorus.mFourier k (i • α + β) =
          UnitAddTorus.mFourier k β := by
      have hterm (i : ℕ) : UnitAddTorus.mFourier k (i • α + β) = UnitAddTorus.mFourier k β := by
        rw [UnitAddTorus.mFourier_apply_add, UnitAddTorus.mFourier_apply_nsmul, h1, one_pow,
          one_mul]
      simp_rw [hterm, sum_const, card_range, nsmul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)), one_mul]
    simp_rw [hconst] at hlim
    have hzero : UnitAddTorus.mFourier k β = 0 := tendsto_nhds_unique tendsto_const_nhds hlim
    have hnorm := UnitAddTorus.norm_mFourier_apply k β
    rw [hzero, norm_zero] at hnorm
    norm_num at hnorm
  tfae_finish

/-- **Equidistribution of doubly infinite linear orbits on `UnitAddTorus d`**: for
`α, β : UnitAddTorus d`, two-sided equidistribution of `n ↦ n • α + β` (`n : ℤ`), total two-sided
equidistribution, and irrationality of `α` are equivalent. -/
theorem linear_equidistributionInt_tfae (α β : UnitAddTorus d) :
    List.TFAE [
      AsympEquidistributedInt (fun n : ℤ ↦ n • α + β)
        (volume : Measure (UnitAddTorus d)).toProbabilityMeasure,
      TotallyAsympEquidistributedInt (fun n : ℤ ↦ n • α + β)
        (volume : Measure (UnitAddTorus d)).toProbabilityMeasure,
      TorusIrrational α
    ] := by
  tfae_have 3 → 2 := by
    intro hα
    rw [totallyAsympEquidistributedInt_def]
    intro q hq r
    rw [asympEquidistributedInt_def]
    constructor
    · have heq : (fun n : ℕ ↦ ((q : ℤ) * ((n : ℤ) + 1) + r) • α + β) =
          fun n : ℕ ↦ n • (q • α) + (((q : ℤ) + r) • α + β) := by
        funext n
        rw [← add_assoc, ← natCast_zsmul, ← natCast_zsmul, ← mul_zsmul, ← add_zsmul]
        congr 2; ring
      rw [heq]
      exact asympEquidistributed_linear_of_torusIrrational (hα.nsmul hq.ne') _
    · have heq : (fun n : ℕ ↦ ((q : ℤ) * -((n : ℤ) + 1) + r) • α + β) =
          fun n : ℕ ↦ n • ((-(q : ℤ)) • α) + ((r - (q : ℤ)) • α + β) := by
        funext n
        rw [← add_assoc, ← natCast_zsmul, ← mul_zsmul, ← add_zsmul]
        congr 2; ring
      rw [heq]
      exact asympEquidistributed_linear_of_torusIrrational
        (hα.zsmul (neg_ne_zero.mpr (Int.natCast_ne_zero.mpr hq.ne'))) _
  tfae_have 2 → 1 := TotallyAsympEquidistributedInt.asympEquidistributedInt
  tfae_have 1 → 3 := by
    intro h
    have hnat : AsympEquidistributed (fun n : ℕ ↦ n • α + β)
        (volume : Measure (UnitAddTorus d)).toProbabilityMeasure := by
      simpa only [natCast_zsmul] using h.natCast
    exact ((linear_equidistribution_tfae α β).out 1 3).mp hnat
  tfae_finish

end Linear

section VanDerCorput

/-- Counting pairs `0 ≤ h₁ < h₂ < H` by their lag `h = h₂ - h₁` gives multiplicity `H - h`. -/
private theorem sum_range_sum_Ico_sub {M : Type*} [AddCommMonoid M] (H : ℕ) (φ : ℕ → M) :
    ∑ h₁ ∈ range H, ∑ h₂ ∈ Ico (h₁ + 1) H, φ (h₂ - h₁) =
      ∑ h ∈ Ico 1 H, (H - h) • φ h := by
  induction H with
  | zero => simp
  | succ H ih =>
    rw [sum_range_succ, Finset.Ico_self, sum_empty, add_zero]
    have hsplit : ∑ h₁ ∈ range H, ∑ h₂ ∈ Ico (h₁ + 1) (H + 1), φ (h₂ - h₁) =
        (∑ h₁ ∈ range H, ∑ h₂ ∈ Ico (h₁ + 1) H, φ (h₂ - h₁)) +
          ∑ h₁ ∈ range H, φ (H - h₁) := by
      rw [← sum_add_distrib]
      exact sum_congr rfl fun h₁ hh₁ ↦
        sum_Ico_succ_top (Nat.succ_le_of_lt (Finset.mem_range.mp hh₁)) _
    have hrev : ∑ h₁ ∈ range H, φ (H - h₁) = ∑ h ∈ Ico 1 (H + 1), φ h := by
      refine sum_bij (fun h₁ _ ↦ H - h₁) ?_ ?_ ?_ (fun _ _ ↦ rfl)
      · intro h₁ hh₁
        rw [Finset.mem_range] at hh₁; rw [Finset.mem_Ico]; omega
      · intro a ha b hb hab
        rw [Finset.mem_range] at ha hb; omega
      · intro h hh
        rw [Finset.mem_Ico] at hh
        exact ⟨H - h, Finset.mem_range.mpr (by omega), by omega⟩
    rw [hsplit, ih, hrev]
    cases H with
    | zero => simp
    | succ H' =>
      rw [sum_Ico_succ_top (by omega : 1 ≤ H' + 1), sum_Ico_succ_top (by omega : 1 ≤ H' + 1),
        ← add_assoc, ← sum_add_distrib]
      congr 1
      · refine sum_congr rfl fun h hh ↦ ?_
        rw [Finset.mem_Ico] at hh
        rw [show H' + 1 + 1 - h = (H' + 1 - h) + 1 by omega, add_nsmul, one_nsmul]
      · simp

/-- Swapping indices in a strict triangular sum over `range H`. -/
private theorem sum_range_sum_range_lt {M : Type*} [AddCommMonoid M] (H : ℕ) (ψ : ℕ → ℕ → M) :
    ∑ h₁ ∈ range H, ∑ h₂ ∈ range h₁, ψ h₂ h₁ =
      ∑ h₂ ∈ range H, ∑ h₁ ∈ Ico (h₂ + 1) H, ψ h₂ h₁ := by
  induction H with
  | zero => simp
  | succ H ih =>
    rw [sum_range_succ, ih, sum_range_succ, Finset.Ico_self, sum_empty, add_zero, ← sum_add_distrib]
    exact sum_congr rfl fun h₂ hh₂ ↦
      (sum_Ico_succ_top (Nat.succ_le_of_lt (Finset.mem_range.mp hh₂)) _).symm

/-- Shifted-sum identity for van der Corput's inequality: summing the `H` translates of a
`range N`-supported sequence over `range (N + H - 1)` multiplies the total sum by `H`. -/
private theorem vanDerCorput_sum_shift {N H : ℕ} (hN : 1 ≤ N) (hH : 1 ≤ H) (b : ℕ → ℂ) :
    ∑ m ∈ range (N + H - 1),
        ∑ h ∈ range H, (if h ≤ m then (if m - h < N then b (m - h) else 0) else 0) =
      (H : ℂ) * ∑ n ∈ range N, b n := by
  rw [sum_comm]
  have hinner (h : ℕ) (hh : h ∈ range H) :
      ∑ m ∈ range (N + H - 1),
          (if h ≤ m then (if m - h < N then b (m - h) else 0) else 0) =
        ∑ n ∈ range N, b n := by
    have hhH : h < H := Finset.mem_range.mp hh
    rw [← sum_range_add_sum_Ico _ (by omega : h ≤ N + H - 1)]
    have hlow : ∑ m ∈ range h,
        (if h ≤ m then (if m - h < N then b (m - h) else 0) else 0) = 0 :=
      sum_eq_zero fun m hm ↦ by simp [not_le_of_gt (Finset.mem_range.mp hm)]
    rw [hlow, zero_add, sum_Ico_eq_sum_range,
      ← sum_range_add_sum_Ico _ (by omega : N ≤ N + H - 1 - h)]
    have hhi : ∑ n ∈ Ico N (N + H - 1 - h),
        (if h ≤ h + n then (if h + n - h < N then b (h + n - h) else 0) else 0) = 0 :=
      sum_eq_zero fun n hn ↦ by simp [not_lt.mpr (Finset.mem_Ico.mp hn).1]
    rw [hhi, add_zero]
    exact sum_congr rfl fun n hn ↦ by simp [Finset.mem_range.mp hn]
  rw [sum_congr rfl hinner, sum_const, card_range, nsmul_eq_mul]

/-- Inner correlation identity for two shifts `h₁ ≤ h₂ < H` in van der Corput's inequality. -/
private theorem vanDerCorput_inner_corr {N H : ℕ} (hN : 1 ≤ N) (b : ℕ → ℂ)
    {h₁ h₂ : ℕ} (h12 : h₁ ≤ h₂) (h2H : h₂ < H) :
    ∑ m ∈ range (N + H - 1),
        (if h₁ ≤ m then (if m - h₁ < N then b (m - h₁) else 0) else 0) *
          starRingEnd ℂ (if h₂ ≤ m then (if m - h₂ < N then b (m - h₂) else 0) else 0) =
      ∑ n ∈ range (N - (h₂ - h₁)), b (n + (h₂ - h₁)) * starRingEnd ℂ (b n) := by
  rw [← sum_range_add_sum_Ico _ (by omega : h₂ ≤ N + H - 1)]
  have hlow : ∑ m ∈ range h₂,
      (if h₁ ≤ m then (if m - h₁ < N then b (m - h₁) else 0) else 0) *
        starRingEnd ℂ (if h₂ ≤ m then (if m - h₂ < N then b (m - h₂) else 0) else 0) = 0 :=
    sum_eq_zero fun m hm ↦ by simp [not_le_of_gt (Finset.mem_range.mp hm)]
  rw [hlow, zero_add, sum_Ico_eq_sum_range,
    ← sum_range_add_sum_Ico _ (by omega : N - (h₂ - h₁) ≤ N + H - 1 - h₂)]
  have hhi : ∑ n ∈ Ico (N - (h₂ - h₁)) (N + H - 1 - h₂),
      (if h₁ ≤ h₂ + n then (if h₂ + n - h₁ < N then b (h₂ + n - h₁) else 0) else 0) *
        starRingEnd ℂ
          (if h₂ ≤ h₂ + n then (if h₂ + n - h₂ < N then b (h₂ + n - h₂) else 0) else 0) = 0 :=
    sum_eq_zero fun n hn ↦ by
      have hge : N - (h₂ - h₁) ≤ n := (Finset.mem_Ico.mp hn).1
      have hnot : ¬ h₂ + n - h₁ < N := by omega
      simp [hnot]
  rw [hhi, add_zero]
  refine sum_congr rfl fun n hn ↦ ?_
  have hlt : n < N - (h₂ - h₁) := Finset.mem_range.mp hn
  have hsub : h₂ + n - h₁ = n + (h₂ - h₁) := by omega
  have hlt1 : n + (h₂ - h₁) < N := by omega
  have hlt2 : n < N := by omega
  have hle1 : h₁ ≤ h₂ + n := by omega
  simp [hle1, hsub, hlt1, hlt2]

/-- Diagonal plus conjugate upper-triangle decomposition for a Hermitian matrix on `range H`. -/
private theorem sum_range_hermitian_split (H : ℕ) (S : ℕ → ℕ → ℂ)
    (hconj : ∀ h₁ h₂, S h₂ h₁ = starRingEnd ℂ (S h₁ h₂)) :
    ∑ h₁ ∈ range H, ∑ h₂ ∈ range H, S h₁ h₂ =
      (∑ h₁ ∈ range H, S h₁ h₁) +
        ∑ h₁ ∈ range H, ∑ h₂ ∈ Ico (h₁ + 1) H, (S h₁ h₂ + starRingEnd ℂ (S h₁ h₂)) := by
  have hrow (h₁ : ℕ) (hh₁ : h₁ ∈ range H) :
      ∑ h₂ ∈ range H, S h₁ h₂ =
        S h₁ h₁ + (∑ h₂ ∈ range h₁, S h₁ h₂) + ∑ h₂ ∈ Ico (h₁ + 1) H, S h₁ h₂ := by
    rw [← sum_range_add_sum_Ico _ (Nat.succ_le_of_lt (Finset.mem_range.mp hh₁)), sum_range_succ]
    abel
  rw [sum_congr rfl hrow, sum_add_distrib, sum_add_distrib, add_assoc]
  congr 1
  rw [sum_range_sum_range_lt]
  simp_rw [← sum_add_distrib]
  exact sum_congr rfl fun h₁ _ ↦ sum_congr rfl fun h₂ _ ↦ by rw [hconj, add_comm]

/-- Expanding the squared norm sum of the shifted window sums in van der Corput's inequality. -/
private theorem vanDerCorput_expand_sq {N H : ℕ} (hN : 1 ≤ N) (b : ℕ → ℂ) :
    ∑ m ∈ range (N + H - 1),
        ‖∑ h ∈ range H, (if h ≤ m then (if m - h < N then b (m - h) else 0) else 0)‖ ^ 2 ≤
      (H : ℝ) * ∑ n ∈ range N, ‖b n‖ ^ 2 +
        2 * ∑ h ∈ Ico 1 H, ((H - h : ℕ) : ℝ) *
          ‖∑ n ∈ range (N - h), b (n + h) * starRingEnd ℂ (b n)‖ := by
  let a : ℕ → ℕ → ℂ := fun m h ↦ if h ≤ m then (if m - h < N then b (m - h) else 0) else 0
  let S : ℕ → ℕ → ℂ := fun h₁ h₂ ↦ ∑ m ∈ range (N + H - 1), a m h₁ * starRingEnd ℂ (a m h₂)
  let C : ℕ → ℂ := fun h ↦ ∑ n ∈ range (N - h), b (n + h) * starRingEnd ℂ (b n)
  have hexpand : ((∑ m ∈ range (N + H - 1), ‖∑ h ∈ range H, a m h‖ ^ 2 : ℝ) : ℂ) =
      ∑ h₁ ∈ range H, ∑ h₂ ∈ range H, S h₁ h₂ := by
    have hcm (m : ℕ) : ((‖∑ h ∈ range H, a m h‖ ^ 2 : ℝ) : ℂ) =
        ∑ h₁ ∈ range H, ∑ h₂ ∈ range H, a m h₁ * starRingEnd ℂ (a m h₂) := by
      push_cast; rw [← Complex.mul_conj', map_sum, sum_mul]
      exact sum_congr rfl fun h₁ _ ↦ mul_sum _ _ _
    rw [Complex.ofReal_sum]; simp_rw [hcm]; rw [sum_comm]
    exact sum_congr rfl fun h₁ _ ↦ sum_comm
  have hsplit := sum_range_hermitian_split H S fun h₁ h₂ ↦ by
    simp only [S, map_sum, map_mul, starRingEnd_self_apply, mul_comm]
  have hdiag : (∑ h₁ ∈ range H, S h₁ h₁).re = (H : ℝ) * ∑ n ∈ range N, ‖b n‖ ^ 2 := by
    have hterm (h₁ : ℕ) (hh₁ : h₁ ∈ range H) :
        S h₁ h₁ = ((∑ n ∈ range N, ‖b n‖ ^ 2 : ℝ) : ℂ) := by
      simpa only [S, a, Nat.sub_self, Nat.sub_zero, add_zero, Complex.mul_conj',
        Complex.ofReal_sum, Complex.ofReal_pow] using
        vanDerCorput_inner_corr hN b le_rfl (Finset.mem_range.mp hh₁)
    rw [sum_congr rfl hterm, sum_const, card_range, nsmul_eq_mul, ← Complex.ofReal_natCast,
      ← Complex.ofReal_mul, Complex.ofReal_re]
  have hoff : (∑ h₁ ∈ range H, ∑ h₂ ∈ Ico (h₁ + 1) H, (S h₁ h₂ + starRingEnd ℂ (S h₁ h₂))).re ≤
      2 * ∑ h ∈ Ico 1 H, ((H - h : ℕ) : ℝ) * ‖C h‖ := by
    have heq : ∑ h₁ ∈ range H, ∑ h₂ ∈ Ico (h₁ + 1) H, (S h₁ h₂ + starRingEnd ℂ (S h₁ h₂)) =
        ∑ h ∈ Ico 1 H, (H - h) • (C h + starRingEnd ℂ (C h)) := by
      rw [← sum_range_sum_Ico_sub H (fun h ↦ C h + starRingEnd ℂ (C h))]
      refine sum_congr rfl fun h₁ _ ↦ sum_congr rfl fun h₂ hh₂ ↦ ?_
      have hS : S h₁ h₂ = C (h₂ - h₁) :=
        vanDerCorput_inner_corr hN b (by have := (Finset.mem_Ico.mp hh₂).1; omega)
          (Finset.mem_Ico.mp hh₂).2
      rw [hS]
    rw [heq, Complex.re_sum, mul_sum]
    refine sum_le_sum fun h _ ↦ ?_
    simp only [nsmul_eq_mul, Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul,
      sub_zero, Complex.add_re, Complex.conj_re]
    nlinarith [Complex.re_le_norm (C h), Nat.cast_nonneg (α := ℝ) (H - h)]
  have hre := congrArg Complex.re (hexpand.trans hsplit)
  rw [Complex.ofReal_re, Complex.add_re, hdiag] at hre
  linarith

/-- **Van der Corput's finite lag inequality**: for any `N H : ℕ` and any complex sequence
`b : ℕ → ℂ`,
`H² ‖∑_{n < N} b n‖² ≤ (N + H - 1) (H ∑_{n < N} ‖b n‖² + 2 ∑_{1 ≤ h < H} (H - h) ‖C(h)‖)`,
where `C(h) = ∑_{n < N - h} b (n + h) conj (b n)`. -/
theorem vanDerCorput_inequality (N H : ℕ) (b : ℕ → ℂ) :
    (H : ℝ) ^ 2 * ‖∑ n ∈ range N, b n‖ ^ 2 ≤
      ((N + H - 1 : ℕ) : ℝ) *
        ((H : ℝ) * ∑ n ∈ range N, ‖b n‖ ^ 2 +
          2 * ∑ h ∈ Ico 1 H, ((H - h : ℕ) : ℝ) *
            ‖∑ n ∈ range (N - h), b (n + h) * starRingEnd ℂ (b n)‖) := by
  by_cases hH0 : H = 0
  · subst hH0; simp
  by_cases hN0 : N = 0
  · subst hN0; simp
  have hN : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN0
  have hH : 1 ≤ H := Nat.one_le_iff_ne_zero.mpr hH0
  let c : ℕ → ℂ := fun m ↦
    ∑ h ∈ range H, (if h ≤ m then (if m - h < N then b (m - h) else 0) else 0)
  have hnorm : (H : ℝ) * ‖∑ n ∈ range N, b n‖ ≤ ∑ m ∈ range (N + H - 1), ‖c m‖ := by
    calc (H : ℝ) * ‖∑ n ∈ range N, b n‖
        = ‖(H : ℂ) * ∑ n ∈ range N, b n‖ := by rw [norm_mul, Complex.norm_natCast]
      _ = ‖∑ m ∈ range (N + H - 1), c m‖ := by rw [vanDerCorput_sum_shift hN hH b]
      _ ≤ ∑ m ∈ range (N + H - 1), ‖c m‖ := norm_sum_le _ _
  have hCS : (H : ℝ) ^ 2 * ‖∑ n ∈ range N, b n‖ ^ 2 ≤
      ((N + H - 1 : ℕ) : ℝ) * ∑ m ∈ range (N + H - 1), ‖c m‖ ^ 2 := by
    calc (H : ℝ) ^ 2 * ‖∑ n ∈ range N, b n‖ ^ 2
        = ((H : ℝ) * ‖∑ n ∈ range N, b n‖) ^ 2 := by ring
      _ ≤ (∑ m ∈ range (N + H - 1), (1 : ℝ) * ‖c m‖) ^ 2 := by
          simpa only [one_mul] using pow_le_pow_left₀ (by positivity) hnorm 2
      _ ≤ (∑ _m ∈ range (N + H - 1), (1 : ℝ) ^ 2) * ∑ m ∈ range (N + H - 1), ‖c m‖ ^ 2 :=
          Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ = ((N + H - 1 : ℕ) : ℝ) * ∑ m ∈ range (N + H - 1), ‖c m‖ ^ 2 := by simp
  exact hCS.trans (mul_le_mul_of_nonneg_left (vanDerCorput_expand_sq hN b) (Nat.cast_nonneg _))

/-- Truncating a bounded lag-`h` correlation sum from `range (n + 1)` to `range (n + 1 - h)` does
not affect convergence of its normalized norm to `0`. -/
private theorem tendsto_vanDerCorput_lag {b : ℕ → ℂ} {C : ℝ} (hC : ∀ n, ‖b n‖ ≤ C) {h : ℕ}
    (hcorr : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℂ)⁻¹ *
        ∑ i ∈ range (n + 1), b (i + h) * starRingEnd ℂ (b i)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ ↦
        ‖∑ i ∈ range (n + 1 - h), b (i + h) * starRingEnd ℂ (b i)‖ / ((n + 1 : ℕ) : ℝ))
      atTop (𝓝 0) := by
  have hC0 : 0 ≤ C := (norm_nonneg (b 0)).trans (hC 0)
  have hfull : Tendsto (fun n : ℕ ↦
      ‖∑ i ∈ range (n + 1), b (i + h) * starRingEnd ℂ (b i)‖ / ((n + 1 : ℕ) : ℝ))
      atTop (𝓝 0) := by
    have h0 := hcorr.norm
    rw [norm_zero] at h0
    exact h0.congr fun n ↦ by rw [norm_mul, norm_inv, Complex.norm_natCast, div_eq_inv_mul]
  have htail : Tendsto (fun n : ℕ ↦ ((h : ℝ) * C ^ 2) * ((n + 1 : ℕ) : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp
      ((tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1))).const_mul
      ((h : ℝ) * C ^ 2)
  have hbound := hfull.add htail
  rw [add_zero] at hbound
  refine squeeze_zero' (Eventually.of_forall fun n ↦ by positivity) ?_ hbound
  filter_upwards [eventually_ge_atTop h] with n hn
  have hsplit : ∑ i ∈ range (n + 1 - h), b (i + h) * starRingEnd ℂ (b i) =
      (∑ i ∈ range (n + 1), b (i + h) * starRingEnd ℂ (b i)) -
        ∑ i ∈ Ico (n + 1 - h) (n + 1), b (i + h) * starRingEnd ℂ (b i) := by
    rw [← sum_range_add_sum_Ico _ (by omega : n + 1 - h ≤ n + 1), add_sub_cancel_right]
  have hdiff_le : ‖∑ i ∈ Ico (n + 1 - h) (n + 1), b (i + h) * starRingEnd ℂ (b i)‖ ≤
      (h : ℝ) * C ^ 2 := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i ∈ Ico (n + 1 - h) (n + 1), ‖b (i + h) * starRingEnd ℂ (b i)‖
        ≤ ∑ _i ∈ Ico (n + 1 - h) (n + 1), C ^ 2 := by
          refine sum_le_sum fun i _ ↦ ?_
          rw [norm_mul, Complex.norm_conj, sq]
          exact mul_le_mul (hC _) (hC _) (norm_nonneg _) hC0
      _ = ((n + 1 - (n + 1 - h) : ℕ) : ℝ) * C ^ 2 := by simp
      _ = (h : ℝ) * C ^ 2 := by rw [show n + 1 - (n + 1 - h) = h by omega]
  rw [hsplit, ← div_eq_mul_inv, ← add_div]
  gcongr
  calc ‖(∑ i ∈ range (n + 1), b (i + h) * starRingEnd ℂ (b i)) -
          ∑ i ∈ Ico (n + 1 - h) (n + 1), b (i + h) * starRingEnd ℂ (b i)‖
      ≤ ‖∑ i ∈ range (n + 1), b (i + h) * starRingEnd ℂ (b i)‖ +
          ‖∑ i ∈ Ico (n + 1 - h) (n + 1), b (i + h) * starRingEnd ℂ (b i)‖ := norm_sub_le _ _
    _ ≤ ‖∑ i ∈ range (n + 1), b (i + h) * starRingEnd ℂ (b i)‖ + (h : ℝ) * C ^ 2 := by gcongr

/-- Normalized form of van der Corput's inequality for a `C`-bounded sequence `b : ℕ → ℂ`. -/
private theorem vanDerCorput_avg_sq_le {b : ℕ → ℂ} {C : ℝ} (hC : ∀ n, ‖b n‖ ≤ C)
    {H : ℕ} (hH : 0 < H) (n : ℕ) :
    ‖((n + 1 : ℕ) : ℂ)⁻¹ * ∑ i ∈ range (n + 1), b i‖ ^ 2 ≤
      (((n + 1 + H - 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) *
        (C ^ 2 / (H : ℝ) +
          (2 / (H : ℝ) ^ 2) * ∑ h ∈ Ico 1 H, ((H - h : ℕ) : ℝ) *
            (‖∑ i ∈ range (n + 1 - h), b (i + h) * starRingEnd ℂ (b i)‖ / ((n + 1 : ℕ) : ℝ))) := by
  have hHreal : (0 : ℝ) < (H : ℝ) := Nat.cast_pos.mpr hH
  have hn1 : ((n + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  have hden_pos : (0 : ℝ) < (H : ℝ) ^ 2 * ((n + 1 : ℕ) : ℝ) ^ 2 := by positivity
  have hsumC : ∑ i ∈ range (n + 1), ‖b i‖ ^ 2 ≤ ((n + 1 : ℕ) : ℝ) * C ^ 2 := by
    calc ∑ i ∈ range (n + 1), ‖b i‖ ^ 2
        ≤ ∑ _i ∈ range (n + 1), C ^ 2 := sum_le_sum fun i _ ↦
          pow_le_pow_left₀ (norm_nonneg _) (hC i) 2
      _ = ((n + 1 : ℕ) : ℝ) * C ^ 2 := by simp
  have hlhs : ‖((n + 1 : ℕ) : ℂ)⁻¹ * ∑ i ∈ range (n + 1), b i‖ ^ 2 =
      ((H : ℝ) ^ 2 * ‖∑ i ∈ range (n + 1), b i‖ ^ 2) /
        ((H : ℝ) ^ 2 * ((n + 1 : ℕ) : ℝ) ^ 2) := by
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    field_simp [hHreal.ne']
  rw [hlhs, div_le_iff₀ hden_pos]
  calc (H : ℝ) ^ 2 * ‖∑ i ∈ range (n + 1), b i‖ ^ 2
      ≤ ((n + 1 + H - 1 : ℕ) : ℝ) *
          ((H : ℝ) * (((n + 1 : ℕ) : ℝ) * C ^ 2) +
            2 * ∑ h ∈ Ico 1 H, ((H - h : ℕ) : ℝ) *
              ‖∑ i ∈ range (n + 1 - h), b (i + h) * starRingEnd ℂ (b i)‖) :=
        (vanDerCorput_inequality (n + 1) H b).trans (by gcongr)
    _ = (((n + 1 + H - 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) *
          (C ^ 2 / (H : ℝ) +
            (2 / (H : ℝ) ^ 2) * ∑ h ∈ Ico 1 H, ((H - h : ℕ) : ℝ) *
              (‖∑ i ∈ range (n + 1 - h), b (i + h) * starRingEnd ℂ (b i)‖ /
                ((n + 1 : ℕ) : ℝ))) *
          ((H : ℝ) ^ 2 * ((n + 1 : ℕ) : ℝ) ^ 2) := by
        have hsum_div : ∑ h ∈ Ico 1 H, ((H - h : ℕ) : ℝ) *
              (‖∑ i ∈ range (n + 1 - h), b (i + h) * starRingEnd ℂ (b i)‖ / ((n + 1 : ℕ) : ℝ)) =
            (∑ h ∈ Ico 1 H, ((H - h : ℕ) : ℝ) *
              ‖∑ i ∈ range (n + 1 - h), b (i + h) * starRingEnd ℂ (b i)‖) /
              ((n + 1 : ℕ) : ℝ) := by
          rw [sum_div]
          exact sum_congr rfl fun h _ ↦ by ring
        rw [hsum_div]
        field_simp [hHreal.ne', hn1]

/-- **Van der Corput's lemma for bounded complex sequences**: if `b : ℕ → ℂ` is bounded and all
its positive-lag correlation averages `n ↦ (n + 1)⁻¹ ∑_{i ≤ n} b (i + h) conj (b i)` tend to `0`,
then the Cesàro averages of `b` tend to `0`. -/
theorem tendsto_cesaro_zero_of_forall_correlation {b : ℕ → ℂ} (hb : ∃ C : ℝ, ∀ n, ‖b n‖ ≤ C)
    (hcorr : ∀ h : ℕ, 0 < h →
      Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℂ)⁻¹ *
          ∑ i ∈ range (n + 1), b (i + h) * starRingEnd ℂ (b i))
        atTop (𝓝 0)) :
    Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℂ)⁻¹ * ∑ i ∈ range (n + 1), b i) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := hb
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨H₀, hH₀⟩ := exists_nat_gt (2 * C ^ 2 / ε ^ 2)
  set H : ℕ := H₀ + 1
  have hHpos : 0 < H := Nat.succ_pos H₀
  have hHreal : (0 : ℝ) < (H : ℝ) := Nat.cast_pos.mpr hHpos
  have hCH : C ^ 2 / (H : ℝ) < ε ^ 2 := by
    have h1 : 2 * C ^ 2 / ε ^ 2 < (H : ℝ) := hH₀.trans (by exact_mod_cast Nat.lt_succ_self H₀)
    rw [div_lt_iff₀ hHreal]
    nlinarith [(div_lt_iff₀ (sq_pos_of_pos hε)).mp h1, sq_nonneg C]
  have hratio : Tendsto (fun n : ℕ ↦ (((n + 1 + H - 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)))
      atTop (𝓝 1) := by
    have hinv : Tendsto (fun n : ℕ ↦ (1 : ℝ) + ((H - 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ)⁻¹)
        atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.add ((tendsto_inv_atTop_zero.comp
        ((tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1))).const_mul
        ((H - 1 : ℕ) : ℝ))
    refine hinv.congr fun n ↦ ?_
    rw [show n + 1 + H - 1 = (n + 1) + (H - 1) by omega, Nat.cast_add (n + 1), add_div,
      div_self (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)), div_eq_mul_inv]
  have hsum0 : Tendsto (fun n : ℕ ↦
      ∑ h ∈ Ico 1 H, ((H - h : ℕ) : ℝ) *
        (‖∑ i ∈ range (n + 1 - h), b (i + h) * starRingEnd ℂ (b i)‖ / ((n + 1 : ℕ) : ℝ)))
      atTop (𝓝 0) := by
    rw [← Finset.sum_const_zero (s := Ico 1 H)]
    exact tendsto_finsetSum (Ico 1 H) fun h hh ↦ by
      simpa only [mul_zero] using
        (tendsto_vanDerCorput_lag hC (hcorr h (Finset.mem_Ico.mp hh).1)).const_mul
          ((H - h : ℕ) : ℝ)
  have hrhs : Tendsto (fun n : ℕ ↦
      (((n + 1 + H - 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) *
        (C ^ 2 / (H : ℝ) +
          (2 / (H : ℝ) ^ 2) * ∑ h ∈ Ico 1 H, ((H - h : ℕ) : ℝ) *
            (‖∑ i ∈ range (n + 1 - h), b (i + h) * starRingEnd ℂ (b i)‖ / ((n + 1 : ℕ) : ℝ))))
      atTop (𝓝 (C ^ 2 / (H : ℝ))) := by
    simpa using hratio.mul (tendsto_const_nhds.add (hsum0.const_mul (2 / (H : ℝ) ^ 2)))
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hrhs.eventually (gt_mem_nhds hCH))
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [dist_zero_right]
  have hsq_lt := (vanDerCorput_avg_sq_le hC hHpos n).trans_lt (hN n hn)
  nlinarith [norm_nonneg (((n + 1 : ℕ) : ℂ)⁻¹ * ∑ i ∈ range (n + 1), b i)]

/-- **Van der Corput's difference theorem on `UnitAddTorus d`**: if every positive-lag difference
sequence `n ↦ x (n + h) - x n` (`h > 0`) is equidistributed for Haar probability, then `x` is
equidistributed for Haar probability. -/
theorem vanDerCorput_difference {d : Type*} [Fintype d] {x : ℕ → UnitAddTorus d}
    (hx : ∀ h : ℕ, 0 < h →
      AsympEquidistributed (fun n ↦ x (n + h) - x n)
        (volume : Measure (UnitAddTorus d)).toProbabilityMeasure) :
    AsympEquidistributed x (volume : Measure (UnitAddTorus d)).toProbabilityMeasure := by
  rw [weyl_criterion]
  intro k hk
  refine tendsto_cesaro_zero_of_forall_correlation ⟨1, fun n ↦ by simp⟩ fun h hh ↦ ?_
  simpa only [← UnitAddTorus.mFourier_apply_sub] using (weyl_criterion.mp (hx h hh)) k hk

end VanDerCorput

section Polynomial

/-- Binomial difference identity for a degree-`(m + 2)` polynomial in an additive abelian group. -/
private theorem poly_sub_shift {G : Type*} [AddCommGroup G] (m h : ℕ) (α : ℕ → G) (n : ℕ) :
    (∑ j ∈ range (m + 3), (n + h) ^ j • α j) - ∑ j ∈ range (m + 3), n ^ j • α j =
      ∑ r ∈ range (m + 2), n ^ r •
        ∑ j ∈ Ico (r + 1) (m + 3), (h ^ (j - r) * j.choose r) • α j := by
  rw [← sum_sub_distrib]
  have hterm (j : ℕ) :
      (n + h) ^ j • α j - n ^ j • α j =
        ∑ r ∈ range j, n ^ r • ((h ^ (j - r) * j.choose r) • α j) := by
    rw [add_pow, sum_range_succ, Nat.sub_self, pow_zero, mul_one, Nat.choose_self, Nat.cast_one,
      mul_one, add_nsmul, add_sub_cancel_right, sum_smul]
    exact sum_congr rfl fun r _ ↦ by rw [Nat.cast_id, mul_assoc, mul_nsmul']
  simp_rw [hterm]
  rw [sum_range_sum_range_lt (m + 3) (fun r j ↦ n ^ r • ((h ^ (j - r) * j.choose r) • α j)),
    sum_range_succ, Finset.Ico_self, sum_empty, add_zero]
  exact sum_congr rfl fun r _ ↦ smul_sum.symm

/-- **Weyl's polynomial equidistribution theorem**: if `s ≥ 1` and the leading coefficient `α s`
is irrational in `UnitAddTorus d`, then the polynomial sequence
`n ↦ ∑ j ∈ range (s + 1), n ^ j • α j` is equidistributed for Haar probability. -/
theorem weyl_polynomial {d : Type*} [Fintype d] (s : ℕ) (hs : 1 ≤ s) (α : ℕ → UnitAddTorus d)
    (hα : TorusIrrational (α s)) :
    AsympEquidistributed (fun n : ℕ ↦ ∑ j ∈ range (s + 1), n ^ j • α j)
      (volume : Measure (UnitAddTorus d)).toProbabilityMeasure := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hs
  clear hs
  induction m generalizing α with
  | zero =>
    have heq : (fun n : ℕ ↦ ∑ j ∈ range 2, n ^ j • α j) = fun n : ℕ ↦ n • α 1 + α 0 := by
      funext n
      simp [sum_range_succ, add_comm]
    rw [heq]
    exact ((linear_equidistribution_tfae (α 1) (α 0)).out 3 1).mp hα
  | succ m ih =>
    apply vanDerCorput_difference
    intro h hh
    let β : ℕ → UnitAddTorus d := fun r ↦
      ∑ j ∈ Ico (r + 1) (m + 3), (h ^ (j - r) * j.choose r) • α j
    have heq : (fun n : ℕ ↦ (∑ j ∈ range (m + 3), (n + h) ^ j • α j) -
        ∑ j ∈ range (m + 3), n ^ j • α j) =
        fun n : ℕ ↦ ∑ r ∈ range (m + 2), n ^ r • β r :=
      funext (poly_sub_shift m h α)
    have hlead : β (m + 1) = (h * (m + 2)) • α (m + 2) := by
      simp [β, Nat.choose_succ_self_right]
    have hβ : TorusIrrational (β (m + 1)) := by
      rw [hlead]
      exact hα.nsmul (Nat.mul_ne_zero hh.ne' (Nat.succ_ne_zero _))
    rw [heq]
    exact ih β hβ

/-- Affine reparametrization of an integer-indexed polynomial in an additive abelian group. -/
private theorem poly_comp_affine_int {G : Type*} [AddCommGroup G] (s : ℕ) (c : ℕ → G)
    (Q R n : ℤ) :
    ∑ j ∈ range (s + 1), (Q * n + R) ^ j • c j =
      ∑ t ∈ range (s + 1), n ^ t •
        ∑ j ∈ Ico t (s + 1), (Q ^ t * R ^ (j - t) * (j.choose t : ℤ)) • c j := by
  have hterm (j : ℕ) :
      (Q * n + R) ^ j • c j =
        ∑ t ∈ range (j + 1), n ^ t • ((Q ^ t * R ^ (j - t) * (j.choose t : ℤ)) • c j) := by
    rw [add_pow, sum_smul]
    refine sum_congr rfl fun t _ ↦ ?_
    rw [mul_pow, ← mul_zsmul]
    congr 1; ring
  simp_rw [hterm]
  have hswap : ∀ k : ℕ, ∀ ψ : ℕ → ℕ → G,
      ∑ j ∈ range k, ∑ t ∈ range (j + 1), ψ t j =
        ∑ t ∈ range k, ∑ j ∈ Ico t k, ψ t j := by
    intro k ψ
    induction k with
    | zero => simp
    | succ k ih =>
      calc ∑ j ∈ range (k + 1), ∑ t ∈ range (j + 1), ψ t j
          = (∑ t ∈ range k, ∑ j ∈ Ico t k, ψ t j) + (∑ t ∈ range k, ψ t k) + ψ k k := by
            rw [sum_range_succ, ih, sum_range_succ, add_assoc]
        _ = (∑ t ∈ range k, ∑ j ∈ Ico t (k + 1), ψ t j) + ∑ j ∈ Ico k (k + 1), ψ k j := by
            rw [Nat.Ico_succ_singleton, sum_singleton, ← sum_add_distrib]
            congr 1
            exact sum_congr rfl fun t ht ↦
              (sum_Ico_succ_top (le_of_lt (Finset.mem_range.mp ht)) _).symm
        _ = ∑ t ∈ range (k + 1), ∑ j ∈ Ico t (k + 1), ψ t j := (sum_range_succ _ k).symm
  rw [hswap (s + 1)]
  exact sum_congr rfl fun t _ ↦ smul_sum.symm

/-- One-dimensional Weyl polynomial equidistribution on `UnitAddCircle`. -/
private theorem weyl_polynomial_addCircle (s : ℕ) (hs : 1 ≤ s) (c : ℕ → UnitAddCircle)
    (hc : addOrderOf (c s) = 0) :
    AsympEquidistributed (fun n : ℕ ↦ ∑ j ∈ range (s + 1), n ^ j • c j)
      AddCircle.haarAddCircle.toProbabilityMeasure := by
  have hirr : TorusIrrational (fun _ : Unit ↦ c s) := torusIrrational_unique_iff.mpr hc
  have htorus := weyl_polynomial (d := Unit) s hs (fun j _ ↦ c j) hirr
  have hproj := (asympEquidistributed_unitAddTorus_iff_forall_linear_comb.mp htorus)
    (fun _ ↦ 1) (fun h0 ↦ one_ne_zero (congrFun h0 ()))
  simpa [Fintype.sum_unique] using hproj

/-- Passing to an arithmetic progression of step `D` annihilating all high-degree torsion
coefficients `c j` (`j₀ < j ≤ s`) collapses an affine reparametrization of a degree-`s` polynomial
to a degree-`j₀` polynomial with leading coefficient `(Q * D) ^ j₀ • c j₀`. -/
private theorem poly_comp_affine_kill_high {G : Type*} [AddCommGroup G] {s j₀ D : ℕ}
    (hj₀_ge : 1 ≤ j₀) (hj₀_le : j₀ ≤ s) (c : ℕ → G)
    (hDkill : ∀ j ∈ Ioc j₀ s, (D : ℤ) • c j = 0) (Q R : ℤ) (r : ℕ) :
    ∃ γ : ℕ → G, γ j₀ = (Q * (D : ℤ)) ^ j₀ • c j₀ ∧
      ∀ u : ℕ, ∑ j ∈ range (s + 1), (Q * ((D * u + r : ℕ) : ℤ) + R) ^ j • c j =
        ∑ t ∈ range (j₀ + 1), u ^ t • γ t := by
  let Q' : ℤ := Q * (D : ℤ)
  let R' : ℤ := Q * (r : ℤ) + R
  let γ : ℕ → G := fun t ↦
    ∑ j ∈ Ico t (s + 1), (Q' ^ t * R' ^ (j - t) * (j.choose t : ℤ)) • c j
  have hkill (t j : ℕ) (ht : 1 ≤ t) (hj : j ∈ Ioc j₀ s) :
      (Q' ^ t * R' ^ (j - t) * (j.choose t : ℤ)) • c j = 0 := by
    have hQt : Q' ^ t = (Q ^ t * (D : ℤ) ^ (t - 1)) * (D : ℤ) := by
      rw [mul_pow, mul_assoc, ← pow_succ, Nat.sub_add_cancel ht]
    rw [hQt, mul_assoc, mul_assoc, mul_comm (D : ℤ), ← mul_assoc, mul_zsmul, hDkill j hj, smul_zero]
  refine ⟨γ, ?_, fun u ↦ ?_⟩
  · have hsplit : Ico j₀ (s + 1) = insert j₀ (Ioc j₀ s) := by
      ext j; simp only [Finset.mem_Ico, Finset.mem_insert, Finset.mem_Ioc]; omega
    simp only [γ, Q', hsplit, sum_insert (by simp : j₀ ∉ Ioc j₀ s),
      sum_eq_zero fun j hj ↦ hkill j₀ j hj₀_ge hj, add_zero, Nat.sub_self, pow_zero, mul_one,
      Nat.choose_self, Nat.cast_one]
  · have haff : Q * ((D * u + r : ℕ) : ℤ) + R = Q' * (u : ℤ) + R' := by
      simp only [Q', R']; push_cast; ring
    rw [haff, poly_comp_affine_int, ← sum_range_add_sum_Ico _ (by omega : j₀ + 1 ≤ s + 1)]
    have htail : ∑ t ∈ Ico (j₀ + 1) (s + 1), (u : ℤ) ^ t • γ t = 0 :=
      sum_eq_zero fun t ht ↦ by
        have ht_gt : j₀ < t := by have := (Finset.mem_Ico.mp ht).1; omega
        have hγ0 : γ t = 0 := sum_eq_zero fun j hj ↦ hkill t j (by omega)
          (Finset.mem_Ioc.mpr ⟨by have := (Finset.mem_Ico.mp hj).1; omega,
            by have := (Finset.mem_Ico.mp hj).2; omega⟩)
        rw [hγ0, smul_zero]
    rw [htail, add_zero]
    exact sum_congr rfl fun t _ ↦ by rw [← Int.natCast_pow, natCast_zsmul]

/-- If a 1D polynomial on `UnitAddCircle` has at least one non-constant coefficient of infinite
additive order, then its restriction to any non-constant integer affine progression `Q * n + R`
(`Q ≠ 0`) is equidistributed for Haar probability. -/
private theorem asympEquidistributed_poly_comp_affine_addCircle {s : ℕ} (c : ℕ → UnitAddCircle)
    (hex : ∃ j ∈ Finset.Icc 1 s, addOrderOf (c j) = 0) {Q : ℤ} (hQ : Q ≠ 0) (R : ℤ) :
    AsympEquidistributed (fun n : ℕ ↦ ∑ j ∈ range (s + 1), (Q * (n : ℤ) + R) ^ j • c j)
      AddCircle.haarAddCircle.toProbabilityMeasure := by
  let S : Finset ℕ := (Finset.Icc 1 s).filter (fun j ↦ addOrderOf (c j) = 0)
  have hSne : S.Nonempty := by obtain ⟨j, hj, h0⟩ := hex; exact ⟨j, mem_filter.mpr ⟨hj, h0⟩⟩
  set j₀ : ℕ := S.max' hSne
  have hj₀_mem : j₀ ∈ S := max'_mem S hSne
  have hj₀_ge : 1 ≤ j₀ := (Finset.mem_Icc.mp (mem_filter.mp hj₀_mem).1).1
  have hj₀_le : j₀ ≤ s := (Finset.mem_Icc.mp (mem_filter.mp hj₀_mem).1).2
  have hj₀_ord : addOrderOf (c j₀) = 0 := (mem_filter.mp hj₀_mem).2
  have hhi_ord (j : ℕ) (hj : j ∈ Ioc j₀ s) : 0 < addOrderOf (c j) := by
    have hnot : j ∉ S := fun hmem ↦ not_le_of_gt (Finset.mem_Ioc.mp hj).1 (le_max' S j hmem)
    exact Nat.pos_of_ne_zero fun h0 ↦ hnot (mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨by have := (Finset.mem_Ioc.mp hj).1; omega, (Finset.mem_Ioc.mp hj).2⟩, h0⟩)
  let D : ℕ := ∏ j ∈ Ioc j₀ s, addOrderOf (c j)
  have hDpos : 0 < D := Finset.prod_pos hhi_ord
  have hDkill (j : ℕ) (hj : j ∈ Ioc j₀ s) : (D : ℤ) • c j = 0 := by
    rw [natCast_zsmul, ← addOrderOf_dvd_iff_nsmul_eq_zero]
    exact Finset.dvd_prod_of_mem _ hj
  refine asympEquidistributed_of_forall_mod hDpos fun r _ ↦ ?_
  obtain ⟨γ, hγ_lead, hγ_eq⟩ := poly_comp_affine_kill_high hj₀_ge hj₀_le c hDkill Q R r
  have hγ_ord : addOrderOf (γ j₀) = 0 := by
    rw [hγ_lead, ← torusIrrational_unique_iff (d := Unit) (α := fun _ ↦ (Q * (D : ℤ)) ^ j₀ • c j₀)]
    have hne : (Q * (D : ℤ)) ^ j₀ ≠ 0 :=
      pow_ne_zero j₀ (mul_ne_zero hQ (Int.natCast_ne_zero.mpr hDpos.ne'))
    exact ((torusIrrational_unique_iff (d := Unit) (α := fun _ ↦ c j₀)).mpr hj₀_ord).zsmul hne
  simpa only [funext hγ_eq] using weyl_polynomial_addCircle j₀ hj₀_ge γ hγ_ord

/-- Linear pairing commutes with finite integer-weighted polynomial sums on `UnitAddTorus d`. -/
private theorem pairing_sum_zsmul {d : Type*} [Fintype d] (k : d → ℤ) (s : ℕ) (w : ℕ → ℤ)
    (α : ℕ → UnitAddTorus d) :
    ∑ i, k i • (∑ j ∈ range (s + 1), w j • α j) i =
      ∑ j ∈ range (s + 1), w j • (∑ i, k i • α j i) := by
  simp_rw [Finset.sum_apply, Pi.smul_apply, smul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun j _ ↦ sum_congr rfl fun i _ ↦ zsmul_comm _ _ _

/-- If every nonzero frequency admits a non-constant coefficient pairing of infinite additive order,
then the doubly infinite polynomial sequence on `UnitAddTorus d` is totally equidistributed for Haar
probability. -/
private theorem totallyAsympEquidistributedInt_poly_of_forall_addOrderOf {d : Type*} [Fintype d]
    (s : ℕ) (α : ℕ → UnitAddTorus d)
    (h6 : ∀ k : d → ℤ, k ≠ 0 → ∃ j ∈ Icc 1 s, addOrderOf (∑ i, k i • α j i) = 0) :
    TotallyAsympEquidistributedInt (fun n : ℤ ↦ ∑ j ∈ range (s + 1), n ^ j • α j)
      (volume : Measure (UnitAddTorus d)).toProbabilityMeasure := by
  have haff (Q R : ℤ) (hQ : Q ≠ 0) :
      AsympEquidistributed (fun n : ℕ ↦ ∑ j ∈ range (s + 1), (Q * (n : ℤ) + R) ^ j • α j)
        (volume : Measure (UnitAddTorus d)).toProbabilityMeasure := by
    rw [asympEquidistributed_unitAddTorus_iff_forall_linear_comb]
    intro k hk
    simp_rw [pairing_sum_zsmul]
    exact asympEquidistributed_poly_comp_affine_addCircle (fun j ↦ ∑ i, k i • α j i)
      (h6 k hk) hQ R
  rw [totallyAsympEquidistributedInt_def]
  intro q hq r
  rw [asympEquidistributedInt_def]
  constructor
  · have heq : (fun n : ℕ ↦ ∑ j ∈ range (s + 1), ((q : ℤ) * ((n : ℤ) + 1) + r) ^ j • α j) =
        fun n : ℕ ↦ ∑ j ∈ range (s + 1), ((q : ℤ) * (n : ℤ) + ((q : ℤ) + r)) ^ j • α j := by
      funext n; exact sum_congr rfl fun j _ ↦ by ring_nf
    rw [heq]
    exact haff (q : ℤ) ((q : ℤ) + r) (Int.natCast_ne_zero.mpr hq.ne')
  · have heq : (fun n : ℕ ↦ ∑ j ∈ range (s + 1), ((q : ℤ) * -((n : ℤ) + 1) + r) ^ j • α j) =
        fun n : ℕ ↦ ∑ j ∈ range (s + 1), ((-(q : ℤ)) * (n : ℤ) + (r - (q : ℤ))) ^ j • α j := by
      funext n; exact sum_congr rfl fun j _ ↦ by ring_nf
    rw [heq]
    exact haff (-(q : ℤ)) (r - (q : ℤ)) (neg_ne_zero.mpr (Int.natCast_ne_zero.mpr hq.ne'))

/-- If a polynomial sequence on `UnitAddTorus d` is equidistributed for Haar probability, then no
nonzero integer frequency can annihilate all non-constant coefficients `α 1, …, α s`. -/
private theorem forall_pairing_ne_zero_of_asympEquidistributed_poly {d : Type*} [Fintype d]
    (s : ℕ) (α : ℕ → UnitAddTorus d)
    (h1 : AsympEquidistributed (fun n : ℕ ↦ ∑ j ∈ range (s + 1), n ^ j • α j)
      (volume : Measure (UnitAddTorus d)).toProbabilityMeasure) :
    ∀ k : d → ℤ, k ≠ 0 → ∃ j ∈ Icc 1 s, ∑ i, k i • α j i ≠ 0 := by
  intro k hk
  by_contra hnone
  push Not at hnone
  have hconst_term (n : ℕ) :
      UnitAddTorus.mFourier k (∑ j ∈ range (s + 1), n ^ j • α j) =
        UnitAddTorus.mFourier k (α 0) := by
    rw [UnitAddTorus.mFourier_eq_fourier_sum, UnitAddTorus.mFourier_eq_fourier_sum]
    congr 1
    have hcast : ∑ j ∈ range (s + 1), ((n : ℤ) ^ j) • α j = ∑ j ∈ range (s + 1), n ^ j • α j :=
      sum_congr rfl fun j _ ↦ by rw [← Int.natCast_pow, natCast_zsmul]
    rw [← hcast, pairing_sum_zsmul, sum_range_succ', pow_zero, one_zsmul]
    have hzero : ∑ j ∈ range s, ((n : ℤ) ^ (j + 1)) • ∑ i, k i • α (j + 1) i = 0 :=
      sum_eq_zero fun j hj ↦ by
        rw [hnone (j + 1) (mem_Icc.mpr ⟨by omega, by have := mem_range.mp hj; omega⟩), smul_zero]
    rw [hzero, zero_add]
  have hlim := (weyl_criterion.mp h1) k hk
  have havg (n : ℕ) :
      ((n + 1 : ℕ) : ℂ)⁻¹ *
          ∑ i ∈ range (n + 1), UnitAddTorus.mFourier k (∑ j ∈ range (s + 1), i ^ j • α j) =
        UnitAddTorus.mFourier k (α 0) := by
    simp_rw [hconst_term, sum_const, card_range, nsmul_eq_mul]
    rw [← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)), one_mul]
  simp_rw [havg] at hlim
  have h0 : UnitAddTorus.mFourier k (α 0) = 0 := tendsto_nhds_unique tendsto_const_nhds hlim
  have hnorm := UnitAddTorus.norm_mFourier_apply k (α 0)
  rw [h0, norm_zero] at hnorm
  norm_num at hnorm

/-- If no nonzero frequency kills all of `α 1, …, α s`, then for every nonzero frequency `k`, at
least one pairing `∑ i, k i • α j i` (`1 ≤ j ≤ s`) has infinite additive order. -/
private theorem exists_addOrderOf_eq_zero_of_forall_pairing {d : Type*} [Fintype d]
    (s : ℕ) (α : ℕ → UnitAddTorus d)
    (h5 : ∀ k : d → ℤ, k ≠ 0 → ∃ j ∈ Icc 1 s, ∑ i, k i • α j i ≠ 0) :
    ∀ k : d → ℤ, k ≠ 0 → ∃ j ∈ Icc 1 s, addOrderOf (∑ i, k i • α j i) = 0 := by
  intro k hk
  by_contra hfin
  push Not at hfin
  let M : ℕ := ∏ j ∈ Icc 1 s, addOrderOf (∑ i, k i • α j i)
  have hMpos : 0 < M := Finset.prod_pos fun j hj ↦ Nat.pos_of_ne_zero (hfin j hj)
  have hMk_ne : (M : ℤ) • k ≠ 0 := by
    intro h0
    apply hk
    funext i
    have hi := congrFun h0 i
    rw [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi
    exact (mul_eq_zero.mp hi).resolve_left (Int.natCast_ne_zero.mpr hMpos.ne')
  obtain ⟨j, hj, hne⟩ := h5 ((M : ℤ) • k) hMk_ne
  apply hne
  calc ∑ i, ((M : ℤ) • k) i • α j i
      = (M : ℤ) • ∑ i, k i • α j i := by
        rw [smul_sum]
        exact sum_congr rfl fun i _ ↦ by rw [Pi.smul_apply, smul_eq_mul, mul_zsmul]
    _ = 0 := by
        rw [natCast_zsmul, ← addOrderOf_dvd_iff_nsmul_eq_zero]
        exact Finset.dvd_prod_of_mem _ hj

/-- **Full equidistribution criterion for polynomial sequences on `UnitAddTorus d`**: for any
`s : ℕ` and `α : ℕ → UnitAddTorus d`, the following six properties are equivalent:
1. `n ↦ ∑_{j=0}^s n^j • α j` (`n : ℕ`) is equidistributed for Haar probability;
2. it is totally equidistributed on `ℕ`;
3. `n ↦ ∑_{j=0}^s n^j • α j` (`n : ℤ`) is two-sided equidistributed for Haar probability;
4. it is totally two-sided equidistributed on `ℤ`;
5. no nonzero frequency `k : d → ℤ` annihilates all non-constant coefficients `α 1, …, α s`;
6. for every nonzero frequency `k : d → ℤ`, some pairing `∑ i, k i • α j i` (`1 ≤ j ≤ s`) has
   infinite additive order in `UnitAddCircle`. -/
theorem polynomial_equidistribution_tfae {d : Type*} [Fintype d] (s : ℕ)
    (α : ℕ → UnitAddTorus d) :
    List.TFAE [
      AsympEquidistributed (fun n : ℕ ↦ ∑ j ∈ range (s + 1), n ^ j • α j)
        (volume : Measure (UnitAddTorus d)).toProbabilityMeasure,
      TotallyAsympEquidistributed (fun n : ℕ ↦ ∑ j ∈ range (s + 1), n ^ j • α j)
        (volume : Measure (UnitAddTorus d)).toProbabilityMeasure,
      AsympEquidistributedInt (fun n : ℤ ↦ ∑ j ∈ range (s + 1), n ^ j • α j)
        (volume : Measure (UnitAddTorus d)).toProbabilityMeasure,
      TotallyAsympEquidistributedInt (fun n : ℤ ↦ ∑ j ∈ range (s + 1), n ^ j • α j)
        (volume : Measure (UnitAddTorus d)).toProbabilityMeasure,
      ∀ k : d → ℤ, k ≠ 0 → ∃ j ∈ Icc 1 s, ∑ i, k i • α j i ≠ 0,
      ∀ k : d → ℤ, k ≠ 0 → ∃ j ∈ Icc 1 s, addOrderOf (∑ i, k i • α j i) = 0
    ] := by
  have hcast (n : ℕ) :
      ∑ j ∈ range (s + 1), ((n : ℤ) ^ j) • α j = ∑ j ∈ range (s + 1), n ^ j • α j :=
    sum_congr rfl fun j _ ↦ by rw [← Int.natCast_pow, natCast_zsmul]
  tfae_have 6 → 4 := totallyAsympEquidistributedInt_poly_of_forall_addOrderOf s α
  tfae_have 4 → 3 := TotallyAsympEquidistributedInt.asympEquidistributedInt
  tfae_have 4 → 2 := fun h ↦ by simpa only [hcast] using h.totallyAsympEquidistributed_natCast
  tfae_have 3 → 1 := fun h ↦ by simpa only [hcast] using h.natCast
  tfae_have 2 → 1 := TotallyAsympEquidistributed.asympEquidistributed
  tfae_have 1 → 5 := forall_pairing_ne_zero_of_asympEquidistributed_poly s α
  tfae_have 5 → 6 := exists_addOrderOf_eq_zero_of_forall_pairing s α
  tfae_finish

/-- A polynomial sequence `n ↦ ∑_{j=0}^s n^j • α j` in `UnitAddTorus d` is equidistributed for
Haar probability iff no nonzero integer frequency annihilates all of `α 1, …, α s`. -/
theorem polynomial_equidistribution_iff {d : Type*} [Fintype d] (s : ℕ) (α : ℕ → UnitAddTorus d) :
    AsympEquidistributed (fun n : ℕ ↦ ∑ j ∈ range (s + 1), n ^ j • α j)
        (volume : Measure (UnitAddTorus d)).toProbabilityMeasure ↔
      ∀ k : d → ℤ, k ≠ 0 → ∃ j ∈ Icc 1 s, ∑ i, k i • α j i ≠ 0 :=
  (polynomial_equidistribution_tfae s α).out 1 5

/-- A polynomial sequence `n ↦ ∑_{j=0}^s n^j • α j` in `UnitAddTorus d` is totally equidistributed
for Haar probability iff no nonzero integer frequency annihilates all of `α 1, …, α s`. -/
theorem polynomial_total_equidistribution_iff {d : Type*} [Fintype d] (s : ℕ)
    (α : ℕ → UnitAddTorus d) :
    TotallyAsympEquidistributed (fun n : ℕ ↦ ∑ j ∈ range (s + 1), n ^ j • α j)
        (volume : Measure (UnitAddTorus d)).toProbabilityMeasure ↔
      ∀ k : d → ℤ, k ≠ 0 → ∃ j ∈ Icc 1 s, ∑ i, k i • α j i ≠ 0 :=
  (polynomial_equidistribution_tfae s α).out 2 5

/-- A doubly infinite polynomial sequence `n ↦ ∑_{j=0}^s n^j • α j` (`n : ℤ`) in `UnitAddTorus d`
is totally two-sided equidistributed for Haar probability iff no nonzero integer frequency
annihilates all of `α 1, …, α s`. -/
theorem polynomial_total_equidistributionInt_iff {d : Type*} [Fintype d] (s : ℕ)
    (α : ℕ → UnitAddTorus d) :
    TotallyAsympEquidistributedInt (fun n : ℤ ↦ ∑ j ∈ range (s + 1), n ^ j • α j)
        (volume : Measure (UnitAddTorus d)).toProbabilityMeasure ↔
      ∀ k : d → ℤ, k ≠ 0 → ∃ j ∈ Icc 1 s, ∑ i, k i • α j i ≠ 0 :=
  (polynomial_equidistribution_tfae s α).out 4 5

end Polynomial

end TauCeti
