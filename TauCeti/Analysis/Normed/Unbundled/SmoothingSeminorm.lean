/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Unbundled.SmoothingSeminorm

import Mathlib.Analysis.Normed.Unbundled.SeminormFromBounded

/-!
# Smoothings of ring seminorms on commutative rings

The smoothing `smoothingFun μ x = inf_{n ≥ 1} μ (x ^ n) ^ (1 / n)` of a ring seminorm `μ` on a
commutative ring `R` only depends on the growth rate of `μ` along powers. In Mathlib,
`smoothingSeminorm` bundles `smoothingFun μ` as a `RingSeminorm R` under `μ 1 ≤ 1` and
`IsNonarchimedean μ`. Neither hypothesis is needed for the ring-seminorm axioms:

* When `μ 1 ≤ 1`, expanding `(x + y) ^ n` by the binomial theorem and bounding `μ (x ^ k)` and
  `μ (y ^ k)` geometrically gives `smoothingFun μ (x + y) ≤ smoothingFun μ x + smoothingFun μ y`
  for any ring seminorm on a commutative ring, archimedean or nonarchimedean.
* For an arbitrary `μ : RingSeminorm R`, the operator seminorm `ν` attached to `μ` by
  `seminormFromBounded` satisfies `ν 1 ≤ 1`, `ν ≤ μ`, and `μ ≤ μ 1 • ν`, hence has the same
  smoothing as `μ`. Consequently `smoothingSeminormSeq μ x` converges to `smoothingFun μ x`, and
  `RingSeminorm.smoothing μ` is a power-multiplicative `RingSeminorm R` with `μ.smoothing 1 ≤ 1`
  (`μ.smoothing 1 = 1` iff `μ ≠ 0`), without assuming `μ 1 ≤ 1` or `IsNonarchimedean μ`.

This file also records three comparison principles for `smoothingFun`:

* A bound `ν ∘ φ ≤ C μ` through a ring homomorphism `φ`, for any constant `C`, gives
  `smoothingFun ν ∘ φ ≤ smoothingFun μ`: the constant disappears in the limit.
* If multiplication by `c` scales `μ` exactly by `s ≥ 0`, it scales `smoothingFun μ` by `s`.
* If `ν = μ ^ t` for some `t > 0`, then `smoothingFun ν = (smoothingFun μ) ^ t`.

## Main definitions

* `RingSeminorm.smoothing`: the power-multiplicative ring seminorm `x ↦ smoothingFun μ x` attached
  to any ring seminorm `μ` on a commutative ring.

## Main results

* `RingHom.smoothingFun_map_le_of_le_mul`: a multiplicative bound through a ring homomorphism gives
  a contractive bound on smoothings.
* `RingSeminorm.smoothingFun_add_le_of_map_one_le_one`: subadditivity of `smoothingFun μ` under
  `μ 1 ≤ 1`, without nonarchimedeanity.
* `RingSeminorm.tendsto_smoothingFun`: `μ (x ^ n) ^ (1 / n)` tends to `smoothingFun μ x` for every
  ring seminorm `μ` on a commutative ring.
* `RingSeminorm.isPowMul_smoothing`, `RingSeminorm.smoothing_one_eq_one`,
  `RingSeminorm.smoothing_eq_zero_iff`, `RingSeminorm.smoothing_eq_zero_of_isNilpotent`:
  characteristic properties of `RingSeminorm.smoothing`.

## References

* V. G. Berkovich, *Spectral Theory and Analytic Geometry over Non-Archimedean Fields*,
  Mathematical Surveys and Monographs 33, AMS, 1990, §1.3.
* S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*, §1.3.2.
* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: foundations*, Astérisque 371 (2015),
  Definition 2.1.9 and §2.3.
-/

public section

open Filter Topology

variable {R S : Type*} [CommRing R] [CommRing S]

namespace RingHom

/-- **Smoothing absorbs multiplicative constants.** If `ν (φ x) ≤ C * μ x` for a ring
homomorphism `φ : R →+* S` and every `x`, then the smoothing of `ν` at `φ x` is at most the
smoothing of `μ` at `x`, whatever the constant `C`. Only `μ` needs `μ 1 ≤ 1`, so that its
smoothing is a limit. -/
theorem smoothingFun_map_le_of_le_mul {μ : RingSeminorm R} {ν : RingSeminorm S} (φ : R →+* S)
    (hμ1 : μ 1 ≤ 1) {C : ℝ} (h : ∀ x, ν (φ x) ≤ C * μ x) (x : R) :
    smoothingFun ν (φ x) ≤ smoothingFun μ x := by
  -- Replace `C` by a positive constant `D`, so that `D ^ (1 / n) → 1`.
  set D := max C 1
  have hD : 0 < D := zero_lt_one.trans_le (le_max_right _ _)
  have hlim : Tendsto (fun n : ℕ ↦ D ^ (1 / n : ℝ) * smoothingSeminormSeq μ x n) atTop
      (𝓝 (smoothingFun μ x)) := by
    have hD1 : Tendsto (fun n : ℕ ↦ D ^ (1 / n : ℝ)) atTop (𝓝 1) := by
      simpa [Function.comp_def] using ((Real.continuousAt_const_rpow hD.ne').tendsto).comp
        (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa using hD1.mul (tendsto_smoothingFun_of_map_one_le_one μ hμ1 x)
  refine ge_of_tendsto hlim (eventually_atTop.2 ⟨1, fun n hn ↦ ?_⟩)
  calc smoothingFun ν (φ x) ≤ ν (φ x ^ n) ^ (1 / n : ℝ) :=
        smoothingFun_le ν (φ x) ⟨n, hn⟩
    _ ≤ (D * μ (x ^ n)) ^ (1 / n : ℝ) := by
        rw [← map_pow]
        gcongr
        exact (h _).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (apply_nonneg μ _))
    _ = D ^ (1 / n : ℝ) * smoothingSeminormSeq μ x n :=
        Real.mul_rpow hD.le (apply_nonneg μ _)

end RingHom

namespace RingSeminorm

private theorem map_mul_natCast_le {T : Type*} [Ring T] (μ : RingSeminorm T) (x : T) :
    ∀ n : ℕ, μ (x * n) ≤ n * μ x
  | 0 => by simp
  | n + 1 => by
    rw [Nat.cast_add_one, mul_add, mul_one, Nat.cast_add_one, add_mul, one_mul]
    exact (map_add_le_add μ _ _).trans (add_le_add_left (map_mul_natCast_le μ x n) _)

private theorem map_sum_range_le {T : Type*} [NonUnitalRing T] (μ : RingSeminorm T) (f : ℕ → T) :
    ∀ m : ℕ, μ (∑ k ∈ Finset.range m, f k) ≤ ∑ k ∈ Finset.range m, μ (f k)
  | 0 => by simp
  | m + 1 => by
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    exact (map_add_le_add μ _ _).trans (add_le_add (map_sum_range_le μ f m) le_rfl)

private theorem exists_pow_le_const_mul_pow (μ : RingSeminorm R) (hμ1 : μ 1 ≤ 1) (x : R)
    {a : ℝ} (ha : smoothingFun μ x < a) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ k : ℕ, μ (x ^ k) ≤ C * a ^ k := by
  have ha0 : 0 < a := (smoothingFun_nonneg μ hμ1 x).trans_lt ha
  obtain ⟨K, hK⟩ := eventually_atTop.1
    ((tendsto_smoothingFun_of_map_one_le_one μ hμ1 x).eventually (gt_mem_nhds ha))
  refine ⟨1 + ∑ j ∈ Finset.range (K + 1), μ (x ^ j) / a ^ j,
    le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ ↦ by positivity), fun k ↦ ?_⟩
  rcases lt_or_ge k (K + 1) with hk | hk
  · have hmem : k ∈ Finset.range (K + 1) := Finset.mem_range.2 hk
    have hdiv : μ (x ^ k) / a ^ k ≤ 1 + ∑ j ∈ Finset.range (K + 1), μ (x ^ j) / a ^ j :=
      (Finset.single_le_sum (f := fun j : ℕ ↦ μ (x ^ j) / a ^ j)
        (fun _ _ ↦ by positivity) hmem).trans (le_add_of_nonneg_left zero_le_one)
    exact (div_le_iff₀ (pow_pos ha0 k)).1 hdiv
  · have hk1 : 1 ≤ k := (Nat.le_add_left 1 K).trans hk
    have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.one_le_iff_ne_zero.1 hk1)
    have hlt : μ (x ^ k) ^ (1 / k : ℝ) ≤ a := (hK k (Nat.le_of_succ_le hk)).le
    have hpow : μ (x ^ k) ≤ a ^ k := by
      calc μ (x ^ k) = (μ (x ^ k) ^ (1 / k : ℝ)) ^ k := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (apply_nonneg μ _), one_div_mul_cancel hk0,
              Real.rpow_one]
        _ ≤ a ^ k := pow_le_pow_left₀ (by positivity) hlt k
    exact hpow.trans (le_mul_of_one_le_left (pow_nonneg ha0.le k)
      (le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ ↦ by positivity)))

/-- **Subadditivity of `smoothingFun` on commutative rings.** For any ring seminorm `μ` with
`μ 1 ≤ 1` on a commutative ring, `smoothingFun μ` satisfies the triangle inequality, without
assuming `IsNonarchimedean μ`. -/
theorem smoothingFun_add_le_of_map_one_le_one (μ : RingSeminorm R) (hμ1 : μ 1 ≤ 1) (x y : R) :
    smoothingFun μ (x + y) ≤ smoothingFun μ x + smoothingFun μ y := by
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  set a := smoothingFun μ x + ε / 2
  set b := smoothingFun μ y + ε / 2
  have ha0 : 0 < a := add_pos_of_nonneg_of_pos (smoothingFun_nonneg μ hμ1 x) (half_pos hε)
  have hb0 : 0 < b := add_pos_of_nonneg_of_pos (smoothingFun_nonneg μ hμ1 y) (half_pos hε)
  obtain ⟨Cx, hCx1, hCx⟩ :=
    exists_pow_le_const_mul_pow μ hμ1 x (lt_add_of_pos_right _ (half_pos hε))
  obtain ⟨Cy, hCy1, hCy⟩ :=
    exists_pow_le_const_mul_pow μ hμ1 y (lt_add_of_pos_right _ (half_pos hε))
  have hC : 0 < Cx * Cy := mul_pos (zero_lt_one.trans_le hCx1) (zero_lt_one.trans_le hCy1)
  have hClim : Tendsto (fun n : ℕ ↦ (Cx * Cy) ^ (1 / n : ℝ) * (a + b)) atTop (𝓝 (a + b)) := by
    have h1 : Tendsto (fun n : ℕ ↦ (Cx * Cy) ^ (1 / n : ℝ)) atTop (𝓝 1) := by
      simpa [Function.comp_def] using ((Real.continuousAt_const_rpow hC.ne').tendsto).comp
        (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa using h1.mul_const (a + b)
  have hab : a + b = smoothingFun μ x + smoothingFun μ y + ε := by
    dsimp [a, b]; ring
  rw [← hab]
  refine le_of_tendsto_of_tendsto (tendsto_smoothingFun_of_map_one_le_one μ hμ1 (x + y)) hClim
    (eventually_atTop.2 ⟨1, fun n hn ↦ ?_⟩)
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.one_le_iff_ne_zero.1 hn)
  have hbound : μ ((x + y) ^ n) ≤ Cx * Cy * (a + b) ^ n := by
    calc μ ((x + y) ^ n)
        = μ (∑ k ∈ Finset.range (n + 1), x ^ k * y ^ (n - k) * n.choose k) := by
          rw [add_pow]
      _ ≤ ∑ k ∈ Finset.range (n + 1), μ (x ^ k * y ^ (n - k) * n.choose k) :=
          map_sum_range_le μ _ (n + 1)
      _ ≤ ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * (μ (x ^ k) * μ (y ^ (n - k))) := by
          gcongr with k
          exact (map_mul_natCast_le μ _ _).trans
            (mul_le_mul_of_nonneg_left (map_mul_le_mul μ _ _) (Nat.cast_nonneg _))
      _ ≤ ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * ((Cx * a ^ k) * (Cy * b ^ (n - k))) := by
          gcongr with k
          exacts [hCx k, hCy (n - k)]
      _ = Cx * Cy * ∑ k ∈ Finset.range (n + 1), a ^ k * b ^ (n - k) * n.choose k := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ ↦ ?_
          ring
      _ = Cx * Cy * (a + b) ^ n := by rw [← add_pow]
  calc smoothingSeminormSeq μ (x + y) n
      ≤ (Cx * Cy * (a + b) ^ n) ^ (1 / n : ℝ) := by
        dsimp [smoothingSeminormSeq]
        gcongr
    _ = (Cx * Cy) ^ (1 / n : ℝ) * ((a + b) ^ n) ^ (1 / n : ℝ) :=
        Real.mul_rpow hC.le (pow_nonneg (add_pos ha0 hb0).le n)
    _ = (Cx * Cy) ^ (1 / n : ℝ) * (a + b) := by
        rw [← Real.rpow_natCast (a + b), ← Real.rpow_mul (add_pos ha0 hb0).le,
          mul_one_div_cancel hn0, Real.rpow_one]

/-- Auxiliary operator seminorm attached to `μ`, satisfying `boundedSeminorm μ 1 ≤ 1` and sharing
the same `smoothingFun`. -/
private noncomputable def boundedSeminorm (μ : RingSeminorm R) : RingSeminorm R :=
  seminormFromBounded (map_zero μ) (apply_nonneg μ)
    (c := 1) (fun x y ↦ by simpa only [one_mul] using map_mul_le_mul μ x y)
    (map_add_le_add μ) (map_neg_eq_map μ)

private theorem boundedSeminorm_one_le (μ : RingSeminorm R) : μ.boundedSeminorm 1 ≤ 1 :=
  seminormFromBounded_one_le (apply_nonneg μ)
    (c := 1) (fun x y ↦ by simpa only [one_mul] using map_mul_le_mul μ x y)

private theorem boundedSeminorm_le (μ : RingSeminorm R) (x : R) : μ.boundedSeminorm x ≤ μ x := by
  change seminormFromBounded' μ x ≤ μ x
  simpa only [one_mul] using seminormFromBounded_le (apply_nonneg μ)
    (c := 1) (fun x y ↦ by simpa only [one_mul] using map_mul_le_mul μ x y) x

private theorem le_mul_boundedSeminorm (μ : RingSeminorm R) (x : R) :
    μ x ≤ μ 1 * μ.boundedSeminorm x :=
  seminormFromBounded_ge (apply_nonneg μ)
    (c := 1) (fun x y ↦ by simpa only [one_mul] using map_mul_le_mul μ x y) x

private theorem smoothingFun_eq_boundedSeminorm (μ : RingSeminorm R) (x : R) :
    smoothingFun μ x = smoothingFun μ.boundedSeminorm x := by
  refine le_antisymm ?_ ?_
  · exact (RingHom.id R).smoothingFun_map_le_of_le_mul μ.boundedSeminorm_one_le
      μ.le_mul_boundedSeminorm x
  · refine le_ciInf fun n ↦ (smoothingFun_le μ.boundedSeminorm x n).trans ?_
    gcongr
    exact μ.boundedSeminorm_le _

/-- For every ring seminorm `μ` on a commutative ring, `μ (x ^ n) ^ (1 / n)` tends to
`smoothingFun μ x` as `n → ∞`, without assuming `μ 1 ≤ 1`. -/
theorem tendsto_smoothingFun (μ : RingSeminorm R) (x : R) :
    Tendsto (smoothingSeminormSeq μ x) atTop (𝓝 (smoothingFun μ x)) := by
  rw [μ.smoothingFun_eq_boundedSeminorm x]
  set D := max (μ 1) 1
  have hD : 0 < D := zero_lt_one.trans_le (le_max_right _ _)
  have hlow := tendsto_smoothingFun_of_map_one_le_one μ.boundedSeminorm μ.boundedSeminorm_one_le x
  have hhigh : Tendsto (fun n : ℕ ↦ D ^ (1 / n : ℝ) * smoothingSeminormSeq μ.boundedSeminorm x n)
      atTop (𝓝 (smoothingFun μ.boundedSeminorm x)) := by
    have hD1 : Tendsto (fun n : ℕ ↦ D ^ (1 / n : ℝ)) atTop (𝓝 1) := by
      simpa [Function.comp_def] using ((Real.continuousAt_const_rpow hD.ne').tendsto).comp
        (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa using hD1.mul hlow
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hhigh
    (Eventually.of_forall fun n ↦ ?_) (Eventually.of_forall fun n ↦ ?_)
  · dsimp [smoothingSeminormSeq]
    gcongr
    exact μ.boundedSeminorm_le _
  · dsimp [smoothingSeminormSeq]
    rw [← Real.mul_rpow hD.le (apply_nonneg μ.boundedSeminorm _)]
    gcongr
    exact (μ.le_mul_boundedSeminorm _).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (apply_nonneg μ.boundedSeminorm _))

/-- **The smoothing of a ring seminorm on a commutative ring**, bundled as a `RingSeminorm R`.
Neither `μ 1 ≤ 1` nor `IsNonarchimedean μ` is required. -/
noncomputable def smoothing (μ : RingSeminorm R) : RingSeminorm R where
  toFun := smoothingFun μ
  map_zero' := by
    rw [μ.smoothingFun_eq_boundedSeminorm]
    refine tendsto_nhds_unique_of_eventuallyEq
      (tendsto_smoothingFun_of_map_one_le_one _ μ.boundedSeminorm_one_le 0) tendsto_const_nhds
      (eventually_atTop.2 ⟨1, fun n hn ↦ ?_⟩)
    dsimp [smoothingSeminormSeq]
    rw [zero_pow (Nat.one_le_iff_ne_zero.1 hn), map_zero,
      Real.zero_rpow (one_div_ne_zero (Nat.cast_ne_zero.2 (Nat.one_le_iff_ne_zero.1 hn)))]
  add_le' x y := by
    simp only [μ.smoothingFun_eq_boundedSeminorm]
    exact smoothingFun_add_le_of_map_one_le_one μ.boundedSeminorm μ.boundedSeminorm_one_le x y
  neg' x := by
    simp only [smoothingFun]
    congr 1
    ext n
    rw [neg_pow]
    rcases neg_one_pow_eq_or R n with h | h
    · rw [h, one_mul]
    · rw [h, neg_one_mul, map_neg_eq_map μ]
  mul_le' x y := by
    refine le_of_tendsto_of_tendsto' (μ.tendsto_smoothingFun (x * y))
      ((μ.tendsto_smoothingFun x).mul (μ.tendsto_smoothingFun y)) fun n ↦ ?_
    dsimp [smoothingSeminormSeq]
    rw [← Real.mul_rpow (apply_nonneg μ _) (apply_nonneg μ _), mul_pow]
    gcongr
    exact map_mul_le_mul μ _ _

/-- Applying `μ.smoothing` evaluates `smoothingFun μ`. -/
@[simp]
theorem smoothing_apply (μ : RingSeminorm R) (x : R) :
    μ.smoothing x = smoothingFun μ x :=
  (rfl)

/-- The underlying function of `μ.smoothing` is `smoothingFun μ`. -/
@[simp]
theorem coe_smoothing (μ : RingSeminorm R) :
    ⇑μ.smoothing = smoothingFun μ :=
  (rfl)

/-- `μ.smoothing` is bounded above by `μ`. -/
theorem smoothing_le_self (μ : RingSeminorm R) (x : R) :
    μ.smoothing x ≤ μ x :=
  smoothingFun_le_self μ x

/-- `μ.smoothing` is power-multiplicative for every ring seminorm `μ` on a commutative ring. -/
theorem isPowMul_smoothing (μ : RingSeminorm R) : IsPowMul μ.smoothing := by
  have h : ⇑μ.smoothing = smoothingFun μ.boundedSeminorm :=
    funext μ.smoothingFun_eq_boundedSeminorm
  rw [h]
  exact isPowMul_smoothingFun μ.boundedSeminorm μ.boundedSeminorm_one_le

/-- `μ.smoothing 1` is at most `1`. -/
theorem smoothing_one_le (μ : RingSeminorm R) : μ.smoothing 1 ≤ 1 :=
  μ.isPowMul_smoothing.map_one_le_one

/-- The smoothing of the zero seminorm is the zero seminorm. -/
@[simp]
theorem smoothing_zero : (0 : RingSeminorm R).smoothing = 0 :=
  eq_zero_iff.2 fun x ↦ le_antisymm
    ((smoothing_le_self 0 x).trans_eq (eq_zero_iff.1 rfl x)) (apply_nonneg _ x)

/-- If `μ ≠ 0`, then `μ.smoothing 1 = 1`. -/
theorem smoothing_one_eq_one {μ : RingSeminorm R} (hμ : μ ≠ 0) : μ.smoothing 1 = 1 := by
  have hfn : (μ : R → ℝ) ≠ 0 := fun h ↦ hμ (DFunLike.coe_injective h)
  have hν1 : μ.boundedSeminorm 1 = 1 :=
    seminormFromBounded_one hfn (apply_nonneg μ)
      (c := 1) (fun x y ↦ by simpa only [one_mul] using map_mul_le_mul μ x y)
  rw [smoothing_apply, μ.smoothingFun_eq_boundedSeminorm,
    smoothingFun_of_powMul μ.boundedSeminorm (le_of_eq hν1) (fun n _ ↦ by simp [hν1]), hν1]

/-- The smoothing of `μ` vanishes identically if and only if `μ = 0`. -/
@[simp]
theorem smoothing_eq_zero_iff {μ : RingSeminorm R} : μ.smoothing = 0 ↔ μ = 0 := by
  refine ⟨fun h ↦ ?_, by rintro rfl; exact smoothing_zero⟩
  by_contra hμ
  have h1 : μ.smoothing 1 = 1 := smoothing_one_eq_one hμ
  have h0 : μ.smoothing 1 = 0 := eq_zero_iff.1 h 1
  linarith

/-- `μ.smoothing` kills every nilpotent element. -/
theorem smoothing_eq_zero_of_isNilpotent (μ : RingSeminorm R) {x : R} (hx : IsNilpotent x) :
    μ.smoothing x = 0 := by
  obtain ⟨m, hm⟩ := hx
  have hm1 : x ^ (m + 1) = 0 := by rw [pow_succ', hm, mul_zero]
  have hpow : μ.smoothing x ^ (m + 1) = 0 := by
    rw [← μ.isPowMul_smoothing x (Nat.le_add_left 1 m), hm1, map_zero]
  exact eq_zero_of_pow_eq_zero hpow

end RingSeminorm

namespace TauCeti

/-- **Exact scaling passes to the smoothing.** If multiplication by `c` scales `μ` by the factor
`s ≥ 0`, then it scales the smoothing of `μ` by the same factor. -/
theorem smoothingFun_mul_eq_mul_of_forall {μ : RingSeminorm R} (hμ1 : μ 1 ≤ 1) {c : R} {s : ℝ}
    (hs : 0 ≤ s) (h : ∀ y, μ (c * y) = s * μ y) (x : R) :
    smoothingFun μ (c * x) = s * smoothingFun μ x := by
  have hpow (n : ℕ) (y : R) : μ (c ^ n * y) = s ^ n * μ y := by
    induction n generalizing y with
    | zero => simp
    | succ n ih => rw [pow_succ', mul_assoc, h, ih, ← mul_assoc, pow_succ']
  refine tendsto_nhds_unique_of_eventuallyEq
    (tendsto_smoothingFun_of_map_one_le_one μ hμ1 (c * x))
    ((tendsto_smoothingFun_of_map_one_le_one μ hμ1 x).const_mul s)
    (eventually_atTop.2 ⟨1, fun n hn ↦ ?_⟩)
  have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn
  simp only [smoothingSeminormSeq, mul_pow, hpow, one_div]
  rw [Real.mul_rpow (pow_nonneg hs n) (apply_nonneg μ _), Real.pow_rpow_inv_natCast hs hn0]

/-- **The smoothing of a power of a seminorm is the power of the smoothing.** If `ν x = μ x ^ t`
for every `x`, with `t > 0`, then `smoothingFun ν x = smoothingFun μ x ^ t`. -/
theorem smoothingFun_eq_rpow_of_forall {μ ν : RingSeminorm R} (hμ1 : μ 1 ≤ 1) {t : ℝ}
    (ht : 0 < t) (h : ∀ x, ν x = μ x ^ t) (x : R) :
    smoothingFun ν x = smoothingFun μ x ^ t := by
  have hν1 : ν 1 ≤ 1 := by
    rw [h]
    exact Real.rpow_le_one (apply_nonneg μ _) hμ1 ht.le
  refine tendsto_nhds_unique_of_eventuallyEq
    (tendsto_smoothingFun_of_map_one_le_one ν hν1 x)
    ((tendsto_smoothingFun_of_map_one_le_one μ hμ1 x).rpow_const (Or.inr ht.le))
    (Eventually.of_forall fun n ↦ ?_)
  simp only [smoothingSeminormSeq, h, ← Real.rpow_mul (apply_nonneg μ _), mul_comm t]

end TauCeti
