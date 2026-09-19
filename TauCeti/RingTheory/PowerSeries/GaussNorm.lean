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
series has a last coefficient attaining that norm. Over a nonarchimedean normed ring with
multiplicative norm, the Gauss norm is multiplicative on restricted series.

The last maximal coefficient supplies the distinguished degree used in Weierstrass division
and preparation for Tate algebras. No completeness hypothesis is needed for these norm identities.
The radius is any positive real number, including the unit radius of the usual Tate algebra.

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

variable {R : Type*} [NormedRing R] {c : ℝ} {f g : PowerSeries R}

/-- A restricted power series has bounded weighted coefficient norms. -/
theorem hasGaussNorm_of_isRestricted (hf : f.IsRestricted c) :
    f.HasGaussNorm norm c :=
  ((PowerSeries.isRestricted_iff c f).mp hf).bddAbove_range_of_cofinite

/-- A nonzero restricted series has a last coefficient attaining its Gauss norm. -/
theorem exists_max_eq_gaussNorm_of_isRestricted (hc : 0 < c) (hf : f.IsRestricted c)
    (hf0 : f ≠ 0) :
    ∃ n : ℕ, ‖f.coeff n‖ * c ^ n = f.gaussNorm norm c ∧
      ∀ m, n < m → ‖f.coeff m‖ * c ^ m < f.gaussNorm norm c := by
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
  let s := hfinite.toFinset
  have hi_mem : i ∈ s := by simp [s]
  obtain ⟨j, hj, hmax⟩ := s.exists_max_image a ⟨i, hi_mem⟩
  have hbound (m : ℕ) : a m ≤ a j := by
    by_cases hm : m ∈ s
    · exact hmax m hm
    · have hm' : a m < a i := by simpa [s] using hm
      exact hm'.le.trans (hmax i hi_mem)
  have heq : a j = f.gaussNorm norm c := by
    rw [PowerSeries.gaussNorm_eq]
    exact (ciSup_eq_of_forall_le_of_forall_lt_exists_gt hbound fun _ h ↦ ⟨j, h⟩).symm
  let t := s.filter fun n ↦ a n = a j
  have hj_mem : j ∈ t := by simp [t, hj]
  obtain ⟨n, hn, hnmax⟩ := t.exists_max_image id ⟨j, hj_mem⟩
  have hn_eq : a n = a j := (Finset.mem_filter.mp hn).2
  refine ⟨n, hn_eq.trans heq, fun m hm ↦ ?_⟩
  rw [← heq]
  refine lt_of_le_of_ne (hbound m) fun h ↦ ?_
  have hm_mem : m ∈ t := by
    simp only [t, Finset.mem_filter]
    exact ⟨by simpa [s] using (hmax i hi_mem).trans_eq h.symm, h⟩
  exact (not_le_of_gt hm) (hnmax m hm_mem)

variable [IsUltrametricDist R] [NormMulClass R]

/-- The Gauss norm is multiplicative on restricted power series at every positive radius. -/
theorem gaussNorm_mul_of_isRestricted (hc : 0 < c) (hf : f.IsRestricted c)
    (hg : g.IsRestricted c) :
    (f * g).gaussNorm norm c = f.gaussNorm norm c * g.gaussNorm norm c := by
  by_cases hf0 : f = 0
  · simp [hf0, PowerSeries.gaussNorm_zero norm c (norm_zero : ‖(0 : R)‖ = 0)]
  by_cases hg0 : g = 0
  · simp [hg0, PowerSeries.gaussNorm_zero norm c (norm_zero : ‖(0 : R)‖ = 0)]
  have hbf := hasGaussNorm_of_isRestricted hf
  have hbg := hasGaussNorm_of_isRestricted hg
  have hbfg := hasGaussNorm_of_isRestricted (PowerSeries.isRestricted.mul c hf hg)
  have hfp : 0 < f.gaussNorm norm c := lt_of_le_of_ne
    (PowerSeries.gaussNorm_nonneg norm c f norm_nonneg)
    (Ne.symm ((PowerSeries.gaussNorm_eq_zero_iff norm c f norm_zero norm_nonneg
      (fun _ ↦ norm_eq_zero.mp) hc hbf).not.mpr hf0))
  have hgp : 0 < g.gaussNorm norm c := lt_of_le_of_ne
    (PowerSeries.gaussNorm_nonneg norm c g norm_nonneg)
    (Ne.symm ((PowerSeries.gaussNorm_eq_zero_iff norm c g norm_zero norm_nonneg
      (fun _ ↦ norm_eq_zero.mp) hc hbg).not.mpr hg0))
  obtain ⟨i, hi, hitail⟩ := exists_max_eq_gaussNorm_of_isRestricted hc hf hf0
  obtain ⟨j, hj, hjtail⟩ := exists_max_eq_gaussNorm_of_isRestricted hc hg hg0
  -- At degree `i + j`, every convolution term except `(i,j)` has one index beyond
  -- the last maximal coefficient. Multiplying by the common positive weight compares them.
  have hdom (p : ℕ × ℕ) (hp : p ∈ Finset.antidiagonal (i + j)) (hne : p ≠ (i, j)) :
      ‖f.coeff p.1 * g.coeff p.2‖ < ‖f.coeff i * g.coeff j‖ := by
    have hsum : p.1 + p.2 = i + j := Finset.mem_antidiagonal.mp hp
    have hweight (x y : ℕ) (hxy : x + y = i + j) :
        ‖f.coeff x * g.coeff y‖ * c ^ (i + j) =
          (‖f.coeff x‖ * c ^ x) * (‖g.coeff y‖ * c ^ y) := by
      rw [norm_mul, ← hxy, pow_add]
      ring
    apply (mul_lt_mul_iff_left₀ (pow_pos hc (i + j))).mp
    rw [hweight _ _ hsum, hweight _ _ rfl, hi, hj]
    by_cases hpi : i < p.1
    · exact (mul_le_mul_of_nonneg_left (PowerSeries.le_gaussNorm norm c g hbg p.2)
        (mul_nonneg (norm_nonneg _) (pow_nonneg hc.le _))).trans_lt
          (mul_lt_mul_of_pos_right (hitail _ hpi) hgp)
    · have hpj : j < p.2 := by
        have : p.1 ≠ i ∨ p.2 ≠ j := by simpa only [Ne, Prod.ext_iff, not_and_or] using hne
        omega
      exact (mul_le_mul_of_nonneg_right (PowerSeries.le_gaussNorm norm c f hbf p.1)
        (mul_nonneg (norm_nonneg _) (pow_nonneg hc.le _))).trans_lt
          (mul_lt_mul_of_pos_left (hjtail _ hpj) hfp)
  have hcoeff : ‖(f * g).coeff (i + j)‖ = ‖f.coeff i * g.coeff j‖ := by
    rw [PowerSeries.coeff_mul]
    exact IsUltrametricDist.isNonarchimedean_norm.apply_sum_eq_of_lt
      (fun p : ℕ × ℕ ↦ f.coeff p.1 * g.coeff p.2) norm_neg
      (Finset.mem_antidiagonal.mpr (rfl : i + j = i + j)) hdom
  apply le_antisymm
  · exact MvPowerSeries.gaussNorm_mul_le norm (fun _ : Unit ↦ c) f g
      (fun _ ↦ hc.le) norm_nonneg norm_mul_le IsUltrametricDist.isNonarchimedean_norm
      norm_zero hbf.hasMvGaussNorm hbg.hasMvGaussNorm
  · calc
      f.gaussNorm norm c * g.gaussNorm norm c =
          ‖(f * g).coeff (i + j)‖ * c ^ (i + j) := by
        rw [hcoeff, norm_mul, pow_add, ← hi, ← hj]
        ring
      _ ≤ (f * g).gaussNorm norm c := PowerSeries.le_gaussNorm norm c (f * g) hbfg _

end TauCeti.PowerSeries
