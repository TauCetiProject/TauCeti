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

For a prime `p`, let `R` be a uniform complete Hausdorff Tate ring with a pseudouniformiser `ϖ`
admitting compatible `p`-power roots and satisfying `ϖ ^ p ∣ p` in the power-bounded subring.
Then `R` is perfectoid exactly when one constant `0 < c < 1` gives, for every `x : R`, a
`p`-th-power approximation whose spectral-gauge error is at most `c` times the gauge of `x`.
In a perfectoid ring, any constant strictly larger than the gauge of `p` works. This gauge
is at most `(1 / 2) ^ p` for the normalized gauge, and vanishes in characteristic `p`. The same
approximating root is power bounded whenever the input is power bounded and
the constant is at most one.

For the converse, `1 < p` and a uniform absolute error bound strictly less than one on the
power-bounded subring suffice.

## References

* K. S. Kedlaya, *Sheaves, stacks, and shtukas*, Arizona Winter School 2017,
  §2.8, Lemma 2.8.3.
-/

public section

open TauCeti.Huber

namespace TauCeti.Perfectoid.PseudoUniformizerRoots

variable {p : ℕ} {R : Type*} [CommRing R] [UniformSpace R]
  [IsTopologicalRing R] [IsTateRing R] [IsUniform R]
  (ϖ : PseudoUniformizerRoots p R)

variable [IsUniformAddGroup R] [CompleteSpace R] [T2Space R]

private theorem exists_scaled_gauge_sub_pow_le [Fact p.Prime] [IsPerfectoidTateRing p R]
    (x : R) (m : ℤ) (n : ℕ)
    (hx : (ϖ.zpow (-m) n : R) * x ∈ powerBoundedSubring R) :
    ∃ y : R, ϖ.gauge (x - y ^ p) ≤
      (2 : ℝ) ^ (-((m : ℝ) / p ^ n)) * ϖ.gauge (p : R) := by
  obtain ⟨y, hy⟩ := IsPerfectoidTateRing.exists_natCast_dvd_sub_pow
    (p := p) (⟨_, hx⟩ : powerBoundedSubring R)
  have he : ϖ.gauge ((ϖ.zpow (-m) n : R) * x - (y : R) ^ p) ≤
      ϖ.gauge (p : R) := by
    obtain ⟨z, hz⟩ := hy
    have heq : (ϖ.zpow (-m) n : R) * x - (y : R) ^ p = (p : R) * z :=
      congrArg Subtype.val hz
    rw [heq]
    exact (map_mul_le_mul ϖ.gauge _ _).trans
      (mul_le_of_le_one_right (apply_nonneg _ _) (ϖ.gauge_le_one_iff.mpr z.property))
  refine ⟨(ϖ.zpow m (n + 1) : R) * (y : R), ?_⟩
  -- Undo the scaling using the next root, so its `p`-th power supplies the original scale.
  have hpow : (ϖ.zpow m (n + 1) : R) ^ p = (ϖ.zpow m n : R) := by
    have hscale : ϖ.zpow m (n + 1) ^ p = ϖ.zpow m n := by
      calc
        ϖ.zpow m (n + 1) ^ p = ϖ.zpow (m * p) (n + 1) := by
          rw [zpow_def, zpow_def, _root_.zpow_mul, zpow_natCast]
        _ = ϖ.zpow m n := ϖ.zpow_mul_p m n
    exact (Units.val_pow_eq_pow_val _ _).symm.trans (congrArg Units.val hscale)
  have heq : x - ((ϖ.zpow m (n + 1) : R) * (y : R)) ^ p =
      (ϖ.zpow m n : R) * ((ϖ.zpow (-m) n : R) * x - (y : R) ^ p) := by
    rw [mul_pow, hpow, mul_sub, zpow_neg, Units.mul_inv_cancel_left]
  rw [heq, gauge_zpow_mul]
  exact mul_le_mul_of_nonneg_left he (by positivity)

/-- For prime `p`, given a pseudouniformiser `ϖ` with compatible `p`-power roots and `ϖ ^ p ∣ p`
in the power-bounded subring, every element of a perfectoid Tate ring admits a `p`-th-power
approximation with relative spectral-gauge error at most `c` whenever `c > ϖ.gauge (p : R)`,
including every positive tolerance in characteristic `p`.
The same witness is power bounded if `x` is power bounded and `c ≤ 1`. -/
theorem exists_gauge_sub_pow_le_mul [Fact p.Prime] [IsPerfectoidTateRing p R] {c : ℝ}
    (hc : ϖ.gauge (p : R) < c) (x : R) :
    ∃ y : R, ϖ.gauge (x - y ^ p) ≤ c * ϖ.gauge x ∧
      (c ≤ 1 → x ∈ powerBoundedSubring R → y ∈ powerBoundedSubring R) := by
  suffices h : ∃ y : R, ϖ.gauge (x - y ^ p) ≤ c * ϖ.gauge x by
    obtain ⟨y, hy⟩ := h
    refine ⟨y, hy, fun hc1 hx ↦ ?_⟩
    have he : ϖ.gauge (x - y ^ p) ≤ 1 :=
      hy.trans ((mul_le_of_le_one_left (apply_nonneg _ _) hc1).trans
        (ϖ.gauge_le_one_iff.mpr hx))
    exact mem_powerBoundedSubring.mpr <| (mem_powerBoundedSubring.mp hx).of_sub_pow
      (Fact.out : p.Prime).ne_zero (mem_powerBoundedSubring.mp (ϖ.gauge_le_one_iff.mp he))
  by_cases hx : x = 0
  · exact ⟨0, by simp [hx, (Fact.out : p.Prime).ne_zero]⟩
  have hx0 : 0 < ϖ.gauge x := (apply_nonneg _ _).lt_of_ne'
    (fun h ↦ hx (ϖ.gauge_eq_zero_iff.mp h))
  -- A positive intermediate bound also covers the case where the gauge of `p` is zero.
  let a : ℝ := max (ϖ.gauge (p : R)) (c / 2)
  have hc0 : 0 < c := (apply_nonneg _ _).trans_lt hc
  have ha : 0 < a := lt_of_lt_of_le (by positivity) (le_max_right _ _)
  have hac : a < c := max_lt hc (by linarith)
  obtain ⟨m, n, hm, hn⟩ := ϖ.exists_gauge_radius_lt (Fact.out : p.Prime).one_lt
    (x := x) (d := c / a * ϖ.gauge x) (by
      have hca : 1 < c / a := (lt_div_iff₀ ha).mpr (by simpa using hac)
      simpa using mul_lt_mul_of_pos_right hca hx0)
  obtain ⟨y, hy⟩ := ϖ.exists_scaled_gauge_sub_pow_le x m n hm
  refine ⟨y, hy.trans ((mul_le_mul_of_nonneg_left (le_max_left (ϖ.gauge (p : R)) (c / 2))
    (by positivity)).trans ?_)⟩
  have := mul_lt_mul_of_pos_right hn ha
  field_simp at this
  exact this.le

/-- A uniform complete Hausdorff Tate ring is perfectoid if `1 < p` and every power-bounded
input admits a `p`-th-power approximation with one global absolute spectral-gauge error bound
less than one. The pseudouniformiser `ϖ` admits compatible `p`-power roots and satisfies
`ϖ ^ p ∣ p` in the power-bounded subring. -/
theorem isPerfectoidTateRing_of_exists_gauge_sub_pow_le (hp : 1 < p) {c : ℝ}
    (hc : c < 1)
    (h : ∀ x : powerBoundedSubring R, ∃ y : R, ϖ.gauge ((x : R) - y ^ p) ≤ c) :
    IsPerfectoidTateRing p R := by
  let : NeZero p := ⟨by omega⟩
  let d : ℝ := max c (1 / 2)
  have hd0 : 0 < d := lt_of_lt_of_le (by norm_num) (le_max_right c (1 / 2))
  have hd1 : d < 1 := max_lt hc (by norm_num)
  -- Deep enough roots make the absolute error divisible by the selected root to the power `p`.
  obtain ⟨n, hn⟩ : ∃ n : ℕ, d ≤ (2 : ℝ) ^ (-((p : ℝ) / p ^ n)) := by
    have hl : 0 < -Real.logb 2 d := neg_pos.mpr (Real.logb_neg one_lt_two hd0 hd1)
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((p : ℝ) / -Real.logb 2 d)
      (by exact_mod_cast hp : (1 : ℝ) < p)
    refine ⟨n, le_of_lt ((Real.logb_lt_iff_lt_rpow one_lt_two hd0).mp ?_)⟩
    have hn0 : 0 < (p : ℝ) ^ n := pow_pos (Nat.cast_pos.mpr (by omega)) n
    have hn' := (div_lt_iff₀ hl).mp hn
    have hp' : (p : ℝ) / (p : ℝ) ^ n < -Real.logb 2 d :=
      (div_lt_iff₀ hn0).mpr (by simpa only [mul_comm] using hn')
    linarith
  refine IsPerfectoidTateRing.of_surjective (ϖ.rootPB n) (by
    simpa only [coe_rootPB] using ϖ.isPseudoUniformizer_root n)
    (ϖ.rootPB_pow_dvd n) fun x ↦ ?_
  obtain ⟨y, hy⟩ := h x
  have hy' : ϖ.gauge ((x : R) - y ^ p) ≤ d := hy.trans (le_max_left c (1 / 2))
  have he : IsPowerBounded ((x : R) - y ^ p) :=
    mem_powerBoundedSubring.mp (ϖ.gauge_le_one_iff.mp (hy'.trans hd1.le))
  have hyPB : y ∈ powerBoundedSubring R :=
    mem_powerBoundedSubring.mpr <| (mem_powerBoundedSubring.mp x.property).of_sub_pow
      (NeZero.ne p) he
  refine ⟨⟨y, hyPB⟩, ?_⟩
  apply (ϖ.gauge_le_rpow_iff_rootPB_pow_dvd _ n p).mp
  simpa only [AddSubgroupClass.coe_sub, Subring.coe_pow] using hy'.trans hn

/-- **The metric criterion for perfectoidness**: for prime `p`, a uniform complete Hausdorff
Tate ring with a pseudouniformiser `ϖ` admitting compatible `p`-power roots and satisfying
`ϖ ^ p ∣ p` in the power-bounded subring is perfectoid exactly when one constant `0 < c < 1`
bounds the relative spectral-gauge error of a `p`-th-power approximation for every element. -/
theorem isPerfectoidTateRing_iff_exists_gauge_sub_pow_le_mul [Fact p.Prime] :
    IsPerfectoidTateRing p R ↔ ∃ c ∈ Set.Ioo (0 : ℝ) 1,
      ∀ x : R, ∃ y : R, ϖ.gauge (x - y ^ p) ≤ c * ϖ.gauge x := by
  refine ⟨fun hR ↦ ?_, fun ⟨c, hc, h⟩ ↦ ?_⟩
  swap
  · apply ϖ.isPerfectoidTateRing_of_exists_gauge_sub_pow_le (Fact.out : p.Prime).one_lt hc.2
    intro x
    obtain ⟨y, hy⟩ := h (x : R)
    exact ⟨y, hy.trans (mul_le_of_le_one_right hc.1.le
      (ϖ.gauge_le_one_iff.mpr x.property))⟩
  have ha : (1 / 2 : ℝ) ^ p < 1 :=
    pow_lt_one₀ (by norm_num) (by norm_num) (Fact.out : p.Prime).ne_zero
  obtain ⟨c, hc0, hc1⟩ := exists_between ha
  have hpGauge : ϖ.gauge (p : R) ≤ (1 / 2 : ℝ) ^ p := by
    have hradius : (2 : ℝ) ^ (-((p : ℝ) / p ^ 0)) = (1 / 2 : ℝ) ^ p := by
      calc
        (2 : ℝ) ^ (-((p : ℝ) / p ^ 0)) = ((2 : ℝ) ^ p)⁻¹ := by
          rw [pow_zero, div_one, Real.rpow_neg zero_le_two, Real.rpow_natCast]
        _ = (1 / 2 : ℝ) ^ p := by rw [← inv_pow, one_div]
    rw [← hradius]
    simpa only [Subring.coe_natCast] using
      (ϖ.gauge_le_rpow_iff_rootPB_pow_dvd (p : powerBoundedSubring R) 0 p).mpr
        (ϖ.rootPB_pow_dvd 0)
  exact ⟨c, ⟨(by positivity : (0 : ℝ) < (1 / 2) ^ p).trans hc0, hc1⟩,
    fun x ↦ (ϖ.exists_gauge_sub_pow_le_mul (hpGauge.trans_lt hc0) x).imp fun _ hy ↦ hy.1⟩

end TauCeti.Perfectoid.PseudoUniformizerRoots
