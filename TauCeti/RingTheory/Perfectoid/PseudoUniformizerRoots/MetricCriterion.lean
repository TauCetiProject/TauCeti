/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Perfectoid.Basic
public import TauCeti.RingTheory.Perfectoid.PseudoUniformizerRoots.Gauge

/-!
# The metric criterion for perfectoid Tate rings

For a uniform complete Hausdorff Tate ring with a pseudouniformiser with compatible roots,
perfectoidness is equivalent to uniformly approximating every element by a `p`-th power with
relative spectral-gauge error strictly less than one. In a perfectoid ring, any constant
strictly larger than `(1 / 2) ^ p` works for the normalized gauge. If the element has gauge at
most one, so does the approximating root when the constant is at most one.

## References

* K. S. Kedlaya, *Sheaves, stacks, and shtukas*, Arizona Winter School 2017,
  §2.8, Lemma 2.8.3.
-/

public section

open TauCeti.Huber

namespace TauCeti.Perfectoid.PseudoUniformizerRoots

variable {p : ℕ} {R : Type*} [CommRing R] [UniformSpace R]
  [IsTopologicalRing R] [IsTateRing R] [IsUniform R] [Fact p.Prime]
  (ϖ : PseudoUniformizerRoots p R)

variable [IsUniformAddGroup R] [CompleteSpace R] [T2Space R]

private theorem exists_scaled_gauge_sub_pow_le [IsPerfectoidTateRing p R]
    (x : R) (m : ℤ) (n : ℕ)
    (hx : (ϖ.zpow (-m) n : R) * x ∈ powerBoundedSubring R) :
    ∃ y : R, ϖ.gauge (x - y ^ p) ≤
      (2 : ℝ) ^ (-((m : ℝ) / p ^ n)) * (1 / 2 : ℝ) ^ p := by
  obtain ⟨y, hy⟩ := IsPerfectoidTateRing.exists_natCast_dvd_sub_pow
    (p := p) (⟨_, hx⟩ : powerBoundedSubring R)
  have he : ϖ.gauge ((ϖ.zpow (-m) n : R) * x - (y : R) ^ p) ≤ (1 / 2 : ℝ) ^ p := by
    simpa [Real.rpow_neg, Real.rpow_natCast, one_div, inv_pow] using
      (ϖ.gauge_le_root_radius_iff _ 0).mpr ((ϖ.rootPB_pow_dvd 0).trans hy)
  refine ⟨(ϖ.zpow m (n + 1) : R) * (y : R), ?_⟩
  -- Undo the scaling using the next root, so its `p`-th power supplies the original scale.
  have hpow : (ϖ.zpow m (n + 1) : R) ^ p = (ϖ.zpow m n : R) := by
    rw [← Units.val_pow_eq_pow_val, zpow_def, ← zpow_natCast, ← _root_.zpow_mul, ← zpow_def,
      zpow_mul_p]
  have heq : x - ((ϖ.zpow m (n + 1) : R) * (y : R)) ^ p =
      (ϖ.zpow m n : R) * ((ϖ.zpow (-m) n : R) * x - (y : R) ^ p) := by
    rw [mul_pow, hpow, mul_sub, zpow_neg, ← mul_assoc]
    simp
  rw [heq, gauge_zpow_mul]
  exact mul_le_mul_of_nonneg_left he (by positivity)

/-- In a perfectoid Tate ring every element is approximated by a `p`-th power with relative
spectral-gauge error at most `c`, for any `c > (1 / 2) ^ p`. -/
theorem exists_gauge_sub_pow_le_mul [IsPerfectoidTateRing p R] {c : ℝ}
    (hc : (1 / 2 : ℝ) ^ p < c) (x : R) :
    ∃ y : R, ϖ.gauge (x - y ^ p) ≤ c * ϖ.gauge x := by
  by_cases hx : x = 0
  · exact ⟨0, by simp [hx, (Fact.out : p.Prime).ne_zero]⟩
  have hx0 : 0 < ϖ.gauge x := (apply_nonneg _ _).lt_of_ne'
    (fun h ↦ hx (ϖ.gauge_eq_zero_iff.mp h))
  have ha : 0 < (1 / 2 : ℝ) ^ p := by positivity
  obtain ⟨m, n, hm, hn⟩ := ϖ.exists_gauge_radius_lt (Fact.out : p.Prime).one_lt
    (x := x) (d := c / (1 / 2 : ℝ) ^ p * ϖ.gauge x) (by
      have hca : 1 < c / (1 / 2 : ℝ) ^ p := (lt_div_iff₀ ha).mpr (by simpa using hc)
      simpa using mul_lt_mul_of_pos_right hca hx0)
  obtain ⟨y, hy⟩ := ϖ.exists_scaled_gauge_sub_pow_le x m n hm
  refine ⟨y, hy.trans ?_⟩
  have := mul_lt_mul_of_pos_right hn ha
  field_simp at this
  exact this.le

/-- The approximating root may be chosen in the closed unit ball whenever the original
element lies in that ball and the relative error constant is at most one. -/
theorem exists_gauge_sub_pow_le_mul_of_gauge_le_one [IsPerfectoidTateRing p R] {c : ℝ}
    (hc : (1 / 2 : ℝ) ^ p < c) (hc1 : c ≤ 1) {x : R} (hx : ϖ.gauge x ≤ 1) :
    ∃ y : R, ϖ.gauge y ≤ 1 ∧ ϖ.gauge (x - y ^ p) ≤ c * ϖ.gauge x := by
  obtain ⟨y, hy⟩ := ϖ.exists_gauge_sub_pow_le_mul hc x
  exact ⟨y, ϖ.gauge_le_one_of_relative_error hc1 hx hy, hy⟩

/-- A uniform complete Hausdorff Tate ring is perfectoid if its spectral gauge admits
`p`-th-power approximations with a fixed relative error less than one. -/
theorem isPerfectoidTateRing_of_exists_gauge_sub_pow_le_mul {c : ℝ}
    (hc0 : 0 < c) (hc1 : c < 1)
    (h : ∀ x : R, ∃ y : R, ϖ.gauge (x - y ^ p) ≤ c * ϖ.gauge x) :
    IsPerfectoidTateRing p R := by
  -- Deep enough roots make the relative error divisible by the selected root to the power `p`.
  obtain ⟨n, hn⟩ : ∃ n : ℕ, c ≤ (2 : ℝ) ^ (-((p : ℝ) / p ^ n)) := by
    have hl : 0 < -Real.logb 2 c := neg_pos.mpr (Real.logb_neg one_lt_two hc0 hc1)
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((p : ℝ) / -Real.logb 2 c)
      (by exact_mod_cast (Fact.out : p.Prime).one_lt : (1 : ℝ) < p)
    refine ⟨n, le_of_lt ((Real.logb_lt_iff_lt_rpow one_lt_two hc0).mp ?_)⟩
    have hn0 : 0 < (p : ℝ) ^ n := pow_pos (Nat.cast_pos.mpr (Fact.out : p.Prime).pos) n
    have hn' := (div_lt_iff₀ hl).mp hn
    have hp' : (p : ℝ) / (p : ℝ) ^ n < -Real.logb 2 c :=
      (div_lt_iff₀ hn0).mpr (by simpa only [mul_comm] using hn')
    linarith
  refine IsPerfectoidTateRing.of_surjective (ϖ.rootPB n) (by
    simpa only [coe_rootPB] using ϖ.isPseudoUniformizer_root n)
    (ϖ.rootPB_pow_dvd n) fun x ↦ ?_
  obtain ⟨y, hy⟩ := h (x : R)
  have hx : ϖ.gauge (x : R) ≤ 1 := ϖ.gauge_le_one_iff.mpr x.property
  have hyle : ϖ.gauge y ≤ 1 := ϖ.gauge_le_one_of_relative_error hc1.le hx hy
  refine ⟨⟨y, ϖ.gauge_le_one_iff.mp hyle⟩, (ϖ.gauge_le_root_radius_iff _ n).mp ?_⟩
  exact hy.trans ((mul_le_of_le_one_right hc0.le hx).trans hn)

/-- **The metric criterion for perfectoidness**: a uniform complete Hausdorff Tate ring
with a pseudouniformiser with compatible roots is perfectoid exactly when every element
admits a `p`-th-power approximation with a fixed relative spectral-gauge error less than one. -/
theorem isPerfectoidTateRing_iff_exists_gauge_sub_pow_le_mul :
    IsPerfectoidTateRing p R ↔ ∃ c ∈ Set.Ioo (0 : ℝ) 1,
      ∀ x : R, ∃ y : R, ϖ.gauge (x - y ^ p) ≤ c * ϖ.gauge x := by
  refine ⟨fun hR ↦ ?_, fun ⟨c, hc, h⟩ ↦
    ϖ.isPerfectoidTateRing_of_exists_gauge_sub_pow_le_mul hc.1 hc.2 h⟩
  have ha : (1 / 2 : ℝ) ^ p < 1 :=
    pow_lt_one₀ (by norm_num) (by norm_num) (Fact.out : p.Prime).ne_zero
  obtain ⟨c, hc0, hc1⟩ := exists_between ha
  exact ⟨c, ⟨(by positivity : (0 : ℝ) < (1 / 2) ^ p).trans hc0, hc1⟩,
    ϖ.exists_gauge_sub_pow_le_mul hc0⟩

end TauCeti.Perfectoid.PseudoUniformizerRoots
