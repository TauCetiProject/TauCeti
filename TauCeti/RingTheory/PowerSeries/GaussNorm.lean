/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.GaussNorm
public import Mathlib.RingTheory.PowerSeries.Restricted
import Mathlib.Topology.Order.LiminfLimsup

/-!
# The Gauss norm of restricted power series

A restricted power series has finite Gauss norm. At a positive radius, a nonzero restricted
series has a last coefficient attaining that norm; the degree of that coefficient is the
*distinguished degree* of the series, and `IsDistinguished` names the property. Over a
nonarchimedean normed ring with multiplicative norm, a pair of distinguished degrees produces a
dominant coefficient in a product, and the Gauss norm is therefore multiplicative on restricted
series.

The distinguished degree is the datum Weierstrass division and preparation for Tate algebras are
organised around. No completeness hypothesis is needed for the norm identities here. The radius is
any positive real number, including the unit radius of the usual Tate algebra.

## Main definitions

* `TauCeti.PowerSeries.IsDistinguished`: the Gauss norm is attained in degree `s` and every later
  coefficient is strictly smaller.

## Main results

* `TauCeti.PowerSeries.exists_isDistinguished`: at a positive radius, every nonzero restricted
  series is distinguished of some degree.
* `TauCeti.PowerSeries.IsDistinguished.unique`: of no more than one degree.
* `TauCeti.PowerSeries.IsDistinguished.norm_coeff_mul_mul_pow_eq_gaussNorm_mul`: the dominant
  coefficient of a product of distinguished series.
* `TauCeti.PowerSeries.gaussNorm_mul_of_isRestricted`: multiplicativity of the Gauss norm.

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §5.2.

The dominant-coefficient argument follows Mathlib's proof of `Polynomial.gaussNorm_mul`;
restrictedness replaces the finite-support argument for attaining the maximum. We use Mathlib's
`PowerSeries.IsRestricted` and `PowerSeries.gaussNorm` throughout.
-/

public section

namespace TauCeti.PowerSeries

open Filter
open scoped Topology

variable {R : Type*} [NormedRing R] {c : ℝ} {i j s t : ℕ} {f g : PowerSeries R}

/-- A restricted power series has bounded weighted coefficient norms. -/
theorem hasGaussNorm_of_isRestricted (hf : f.IsRestricted c) :
    f.HasGaussNorm norm c :=
  ((PowerSeries.isRestricted_iff c f).mp hf).bddAbove_range_of_cofinite

/-- A power series whose coefficients vanish in every degree `≥ n` is restricted at every radius:
its weighted coefficient norms are eventually zero. Such a series is a polynomial of degree less
than `n`. -/
theorem isRestricted_of_forall_coeff_eq_zero {n : ℕ}
    (hf : ∀ m, n ≤ m → f.coeff m = 0) : f.IsRestricted c := by
  rw [PowerSeries.isRestricted_iff']
  have h : ∀ᶠ m in Filter.atTop, (0 : ℝ) = ‖f.coeff m‖ * c ^ m := by
    filter_upwards [Filter.eventually_ge_atTop n] with m hm
    simp [hf m hm]
  exact Filter.Tendsto.congr' h tendsto_const_nhds

section

variable (c) (s) (f)

/-- `f` is **distinguished of degree `s`** at the radius `c` when its Gauss norm at `c` is attained
in degree `s` and every later coefficient is strictly smaller.

At the unit radius this is the classical condition that the leading coefficient of `f` dominates,
in the sense of Bosch–Güntzer–Remmert §5.2. At a positive radius, a nonzero restricted series is
distinguished of exactly one degree (`TauCeti.PowerSeries.exists_isDistinguished` and
`TauCeti.PowerSeries.IsDistinguished.unique`), so this is a genuine invariant of `f` and `c` rather
than extra data.

The first field is the univariate reading of Mathlib's `MvPowerSeries.AchievesGaussNorm`; the
second is what makes the degree unique and pins down the dominant coefficient of a product.

This is unrelated to `Polynomial.IsDistinguishedAt`, which asks a polynomial to be monic with its
remaining coefficients in an ideal. -/
structure IsDistinguished : Prop where
  /-- The Gauss norm is attained in degree `s`. -/
  norm_coeff_mul_pow_eq : ‖f.coeff s‖ * c ^ s = f.gaussNorm norm c
  /-- Every coefficient in a degree past `s` is strictly smaller. -/
  norm_coeff_mul_pow_lt : ∀ m, s < m → ‖f.coeff m‖ * c ^ m < f.gaussNorm norm c

end

/-- A distinguished series has positive Gauss norm: the degree just past the distinguished one
witnesses a value strictly below it. Taking an even degree makes the weighted norm nonnegative
without any sign assumption on the radius. -/
theorem IsDistinguished.gaussNorm_pos (hf : IsDistinguished c s f) :
    0 < f.gaussNorm norm c := by
  have hpow : 0 ≤ c ^ (2 * (s + 1)) := by
    rw [pow_mul]
    exact pow_nonneg (sq_nonneg c) _
  exact lt_of_le_of_lt (mul_nonneg (norm_nonneg _) hpow)
    (hf.norm_coeff_mul_pow_lt (2 * (s + 1)) (by omega))

/-- A distinguished series is nonzero. -/
theorem IsDistinguished.ne_zero (hf : IsDistinguished c s f) : f ≠ 0 := by
  rintro rfl
  have h := hf.gaussNorm_pos
  rw [PowerSeries.gaussNorm_zero norm c (norm_zero : ‖(0 : R)‖ = 0)] at h
  exact absurd h (lt_irrefl 0)

/-- The coefficient of a distinguished series in its distinguished degree is nonzero. -/
theorem IsDistinguished.coeff_ne_zero (hf : IsDistinguished c s f) : f.coeff s ≠ 0 := by
  intro h
  have hpos := hf.gaussNorm_pos
  rw [← hf.norm_coeff_mul_pow_eq, h] at hpos
  simp at hpos

/-- The distinguished degree is unique: a series cannot be distinguished of two degrees at the
same radius. -/
theorem IsDistinguished.unique (hf : IsDistinguished c s f) (hf' : IsDistinguished c t f) :
    s = t := by
  rcases lt_trichotomy s t with h | h | h
  · exact absurd hf'.norm_coeff_mul_pow_eq (hf.norm_coeff_mul_pow_lt t h).ne
  · exact h
  · exact absurd hf.norm_coeff_mul_pow_eq (hf'.norm_coeff_mul_pow_lt s h).ne

/-- Every nonzero restricted series is distinguished of some degree: its last coefficient
attaining the Gauss norm supplies that degree. -/
theorem exists_isDistinguished (hc : 0 < c) (hf : f.IsRestricted c) (hf0 : f ≠ 0) :
    ∃ s : ℕ, IsDistinguished c s f := by
  classical
  have hex : ∃ i, f.coeff i ≠ 0 := by
    simpa only [not_forall] using (PowerSeries.forall_coeff_eq_zero f).not.mpr hf0
  obtain ⟨i, hi⟩ := hex
  let a : ℕ → ℝ := fun n ↦ ‖f.coeff n‖ * c ^ n
  have hi_pos : 0 < a i := mul_pos (norm_pos_iff.mpr hi) (pow_pos hc _)
  have hfinite : {n | a i ≤ a n}.Finite := by
    have h : ∀ᶠ n in cofinite, a n < a i :=
      ((PowerSeries.isRestricted_iff c f).mp hf).eventually (gt_mem_nhds hi_pos)
    simpa only [eventually_cofinite, not_lt] using h
  let S := hfinite.toFinset
  have hi_mem : i ∈ S := by simp [S]
  obtain ⟨k, hk, hmax⟩ := S.exists_max_image a ⟨i, hi_mem⟩
  have hbound (m : ℕ) : a m ≤ a k := by
    by_cases hm : m ∈ S
    · exact hmax m hm
    · have hm' : a m < a i := by simpa [S] using hm
      exact hm'.le.trans (hmax i hi_mem)
  have heq : a k = f.gaussNorm norm c := by
    rw [PowerSeries.gaussNorm_eq]
    exact (ciSup_eq_of_forall_le_of_forall_lt_exists_gt hbound fun _ h ↦ ⟨k, h⟩).symm
  let T := S.filter fun n ↦ a n = a k
  have hk_mem : k ∈ T := by simp [T, hk]
  obtain ⟨n, hn, hnmax⟩ := T.exists_max_image id ⟨k, hk_mem⟩
  have hn_eq : a n = a k := (Finset.mem_filter.mp hn).2
  refine ⟨n, hn_eq.trans heq, fun m hm ↦ ?_⟩
  rw [← heq]
  refine lt_of_le_of_ne (hbound m) fun h ↦ ?_
  have hm_mem : m ∈ T := by
    simp only [T, Finset.mem_filter]
    exact ⟨by simpa [S] using (hmax i hi_mem).trans_eq h.symm, h⟩
  exact (not_le_of_gt hm) (hnmax m hm_mem)

variable [IsUltrametricDist R] [NormMulClass R]

/-- **The dominant coefficient of a product of distinguished series.** If `f` is distinguished of
degree `i` and `g` of degree `j`, then the coefficient of `f * g` in degree `i + j` realises the
product of the two Gauss norms.

Every other convolution term in that degree has one of its two indices past a distinguished
degree, hence is strictly smaller, so the nonarchimedean sum cannot lose the dominant term. -/
theorem IsDistinguished.norm_coeff_mul_mul_pow_eq_gaussNorm_mul (hf : IsDistinguished c i f)
    (hg : IsDistinguished c j g) (hc : 0 < c) (hbf : f.HasGaussNorm norm c)
    (hbg : g.HasGaussNorm norm c) :
    ‖(f * g).coeff (i + j)‖ * c ^ (i + j) = f.gaussNorm norm c * g.gaussNorm norm c := by
  have hfp := hf.gaussNorm_pos
  have hgp := hg.gaussNorm_pos
  have hdom (p : ℕ × ℕ) (hp : p ∈ Finset.antidiagonal (i + j)) (hne : p ≠ (i, j)) :
      ‖f.coeff p.1 * g.coeff p.2‖ < ‖f.coeff i * g.coeff j‖ := by
    have hsum : p.1 + p.2 = i + j := Finset.mem_antidiagonal.mp hp
    have hweight (x y : ℕ) (hxy : x + y = i + j) :
        ‖f.coeff x * g.coeff y‖ * c ^ (i + j) =
          (‖f.coeff x‖ * c ^ x) * (‖g.coeff y‖ * c ^ y) := by
      rw [norm_mul, ← hxy, pow_add]
      ring
    apply (mul_lt_mul_iff_left₀ (pow_pos hc (i + j))).mp
    rw [hweight _ _ hsum, hweight _ _ rfl, hf.norm_coeff_mul_pow_eq, hg.norm_coeff_mul_pow_eq]
    by_cases hpi : i < p.1
    · exact (mul_le_mul_of_nonneg_left (PowerSeries.le_gaussNorm norm c g hbg p.2)
        (mul_nonneg (norm_nonneg _) (pow_nonneg hc.le _))).trans_lt
          (mul_lt_mul_of_pos_right (hf.norm_coeff_mul_pow_lt _ hpi) hgp)
    · have hpj : j < p.2 := by
        have : p.1 ≠ i ∨ p.2 ≠ j := by simpa only [Ne, Prod.ext_iff, not_and_or] using hne
        omega
      exact (mul_le_mul_of_nonneg_right (PowerSeries.le_gaussNorm norm c f hbf p.1)
        (mul_nonneg (norm_nonneg _) (pow_nonneg hc.le _))).trans_lt
          (mul_lt_mul_of_pos_left (hg.norm_coeff_mul_pow_lt _ hpj) hfp)
  have hcoeff : ‖(f * g).coeff (i + j)‖ = ‖f.coeff i * g.coeff j‖ := by
    rw [PowerSeries.coeff_mul]
    exact IsUltrametricDist.isNonarchimedean_norm.apply_sum_eq_of_lt
      (fun p : ℕ × ℕ ↦ f.coeff p.1 * g.coeff p.2) norm_neg
      (Finset.mem_antidiagonal.mpr (rfl : i + j = i + j)) hdom
  rw [hcoeff, norm_mul, pow_add, ← hf.norm_coeff_mul_pow_eq, ← hg.norm_coeff_mul_pow_eq]
  ring

/-- The Gauss norm is multiplicative on restricted power series at every positive radius. -/
theorem gaussNorm_mul_of_isRestricted (hc : 0 < c) (hf : f.IsRestricted c)
    (hg : g.IsRestricted c) :
    (f * g).gaussNorm norm c = f.gaussNorm norm c * g.gaussNorm norm c := by
  by_cases hf0 : f = 0
  · simp [hf0, PowerSeries.gaussNorm_zero norm c (norm_zero : ‖(0 : R)‖ = 0)]
  by_cases hg0 : g = 0
  · simp [hg0, PowerSeries.gaussNorm_zero norm c (norm_zero : ‖(0 : R)‖ = 0)]
  obtain ⟨i, hi⟩ := exists_isDistinguished hc hf hf0
  obtain ⟨j, hj⟩ := exists_isDistinguished hc hg hg0
  refine le_antisymm (MvPowerSeries.gaussNorm_mul_le norm (fun _ : Unit ↦ c) f g
    (fun _ ↦ hc.le) norm_nonneg norm_mul_le IsUltrametricDist.isNonarchimedean_norm
    norm_zero (hasGaussNorm_of_isRestricted hf).hasMvGaussNorm
    (hasGaussNorm_of_isRestricted hg).hasMvGaussNorm) ?_
  calc
    f.gaussNorm norm c * g.gaussNorm norm c = ‖(f * g).coeff (i + j)‖ * c ^ (i + j) :=
      (hi.norm_coeff_mul_mul_pow_eq_gaussNorm_mul hj hc (hasGaussNorm_of_isRestricted hf)
        (hasGaussNorm_of_isRestricted hg)).symm
    _ ≤ (f * g).gaussNorm norm c := PowerSeries.le_gaussNorm norm c (f * g)
      (hasGaussNorm_of_isRestricted (PowerSeries.isRestricted.mul c hf hg)) _

/-- The product of series distinguished in degrees `i` and `j` is distinguished in degree
`i + j`, provided both series are restricted at the positive radius. -/
theorem IsDistinguished.mul (hf : IsDistinguished c i f) (hg : IsDistinguished c j g)
    (hc : 0 < c) (hfr : f.IsRestricted c) (hgr : g.IsRestricted c) :
    IsDistinguished c (i + j) (f * g) := by
  have hfp := hf.gaussNorm_pos
  have hgp := hg.gaussNorm_pos
  have hbf := hasGaussNorm_of_isRestricted hfr
  have hbg := hasGaussNorm_of_isRestricted hgr
  have hmul := gaussNorm_mul_of_isRestricted hc hfr hgr
  refine ⟨(hf.norm_coeff_mul_mul_pow_eq_gaussNorm_mul hg hc hbf hbg).trans hmul.symm,
    fun m hm ↦ ?_⟩
  rw [PowerSeries.coeff_mul]
  have hne := Finset.HasAntidiagonal.nonempty_antidiagonal m
  calc
    ‖∑ p ∈ Finset.antidiagonal m, f.coeff p.1 * g.coeff p.2‖ * c ^ m
        ≤ (Finset.antidiagonal m).sup' hne
            (fun p : ℕ × ℕ ↦ ‖f.coeff p.1 * g.coeff p.2‖) * c ^ m :=
      mul_le_mul_of_nonneg_right (hne.norm_sum_le_sup'_norm
        (fun p : ℕ × ℕ ↦ f.coeff p.1 * g.coeff p.2)) (pow_nonneg hc.le m)
    _ = (Finset.antidiagonal m).sup' hne
        (fun p : ℕ × ℕ ↦ ‖f.coeff p.1 * g.coeff p.2‖ * c ^ m) :=
      Finset.sup'_mul₀ (pow_nonneg hc.le m) _ _ _
    _ < f.gaussNorm norm c * g.gaussNorm norm c :=
      (Finset.sup'_lt_iff hne).2 fun p hp ↦ by
      have hsum : p.1 + p.2 = m := Finset.mem_antidiagonal.mp hp
      rw [← hsum, norm_mul, pow_add]
      have hweight :
          ‖f.coeff p.1‖ * ‖g.coeff p.2‖ * (c ^ p.1 * c ^ p.2) =
            (‖f.coeff p.1‖ * c ^ p.1) * (‖g.coeff p.2‖ * c ^ p.2) := by ring
      rw [hweight]
      by_cases hpi : i < p.1
      · exact (mul_le_mul_of_nonneg_left (PowerSeries.le_gaussNorm norm c g hbg p.2)
            (mul_nonneg (norm_nonneg _) (pow_nonneg hc.le _))).trans_lt
          (mul_lt_mul_of_pos_right (hf.norm_coeff_mul_pow_lt _ hpi) hgp)
      · have hpj : j < p.2 := by omega
        exact (mul_le_mul_of_nonneg_right (PowerSeries.le_gaussNorm norm c f hbf p.1)
              (mul_nonneg (norm_nonneg _) (pow_nonneg hc.le _))).trans_lt
          (mul_lt_mul_of_pos_left (hg.norm_coeff_mul_pow_lt _ hpj) hfp)
    _ = (f * g).gaussNorm norm c := hmul.symm

end TauCeti.PowerSeries
