/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.ThetaSeries.Basic
public import TauCeti.Algebra.Module.ZLattice.Covolume
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import TauCeti.Analysis.Distribution.SchwartzSpace.Gaussian
import TauCeti.Analysis.Fourier.PoissonSummation

/-!
# Gaussian sums on lattice translates

The coset theta series at `i/s²` is a real Gaussian sum. Poisson summation expresses
it through the dual lattice at reciprocal scale. This shows that centering maximizes
the sum and controls its growth as the scale increases, the inputs to Gaussian tail
estimates in lattice transference.

The estimates follow Oded Regev, *Transference Theorems*, Lecture 11, equations (1)–(2)
and Lemmas 5–7. We use `SchwartzMap.tsum_eq_tsum_dual_fourier` for Poisson summation.
-/

public noncomputable section

open Complex Module
open scoped FourierTransform Real RealInnerProductSpace

namespace ZLattice

variable {E : Type*} [NormedAddCommGroup E] (L : Submodule ℤ E)

/-- The sum of the Gaussian `exp(-π ‖x‖²/s²)` over the translate `u + L`, at scale `s`. -/
def latticeGaussianSum (s : ℝ) (u : E) : ℝ :=
  ∑' x : L, Real.exp (-(Real.pi / s ^ 2) * ‖u + (x : E)‖ ^ 2)

/-- The Gaussian mass is a sum over the lattice subtype. -/
theorem latticeGaussianSum_def (s : ℝ) (u : E) :
    latticeGaussianSum L s u = ∑' x : L, Real.exp (-(Real.pi / s ^ 2) * ‖u + (x : E)‖ ^ 2) :=
  (rfl)

/-- A coset theta value on the imaginary axis is the Gaussian mass at the corresponding scale. -/
theorem thetaCoset_eq_latticeGaussianSum {s : ℝ} (hs : s ≠ 0) (u : E) :
    thetaCoset L u ⟨I / (s : ℂ) ^ 2, by
      rw [← ofReal_pow, div_ofReal_im, I_im]
      exact div_pos zero_lt_one (sq_pos_of_ne_zero hs)⟩ = (latticeGaussianSum L s u : ℂ) := by
  rw [thetaCoset_apply, latticeGaussianSum_def, ofReal_tsum]
  refine tsum_congr fun x ↦ ?_
  rw [ofReal_exp]
  congr 1
  push_cast
  calc
    _ = (π * (↑‖u + (x : E)‖ : ℂ) ^ 2 * (I * I)) / (s : ℂ) ^ 2 := by ring
    _ = _ := by rw [I_mul_I]; ring

/-- The Gaussian sum does not depend on the representative of a lattice coset. -/
theorem latticeGaussianSum_eq_of_sub_mem (s : ℝ) {u v : E} (h : u - v ∈ L) :
    latticeGaussianSum L s u = latticeGaussianSum L s v := by
  rw [latticeGaussianSum_def, latticeGaussianSum_def]
  conv_rhs => rw [← (Equiv.addLeft (⟨u - v, h⟩ : L)).tsum_eq]
  have huv : v + (u - v) = u := by abel
  exact tsum_congr fun x ↦ by
    simp only [Equiv.coe_addLeft, Submodule.coe_add, ← add_assoc, huv]

/-- In a zero-dimensional space the Gaussian mass is the contribution of the zero vector. -/
@[simp] theorem latticeGaussianSum_of_subsingleton [Subsingleton E] (s : ℝ) (u : E) :
    latticeGaussianSum L s u = 1 := by
  rw [latticeGaussianSum_def, tsum_eq_single (0 : L) fun x hx ↦ (hx (Subsingleton.elim x 0)).elim]
  simp [Subsingleton.elim u 0]

/-- The Gaussian mass of a translate is nonnegative. -/
theorem latticeGaussianSum_nonneg (s : ℝ) (u : E) : 0 ≤ latticeGaussianSum L s u :=
  tsum_nonneg fun _ ↦ Real.exp_nonneg _

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [DiscreteTopology L] [IsZLattice ℝ L]

omit [IsZLattice ℝ L] in
/-- The Gaussian weights on a translate of a discrete lattice are summable at nonzero scale. -/
theorem summable_latticeGaussianSum {s : ℝ} (hs : s ≠ 0) (u : E) :
    Summable (fun x : L ↦ Real.exp (-(Real.pi / s ^ 2) * ‖u + (x : E)‖ ^ 2)) := by
  have hb : 0 < ((Real.pi / s ^ 2 : ℝ) : ℂ).re := div_pos Real.pi_pos (sq_pos_of_ne_zero hs)
  simpa only [SchwartzMap.norm_gaussian_apply, ofReal_re] using
    (summable_poisson_left L (SchwartzMap.gaussian hb) u).norm

/-- Poisson summation for a shifted Gaussian. The dual sum has reciprocal scale and the
positive Fourier phase. -/
theorem latticeGaussianSum_poisson [MeasurableSpace E] [BorelSpace E] {s : ℝ}
    (hs : 0 < s) (u : E) :
    (latticeGaussianSum L s u : ℂ) = (covolume L : ℂ)⁻¹ * (s : ℂ) ^ finrank ℝ E *
      ∑' y : dual L, (Real.exp (-(Real.pi / (s⁻¹) ^ 2) * ‖(y : E)‖ ^ 2) : ℂ) *
        Complex.exp (2 * π * I * ⟪u, (y : E)⟫) := by
  have hb : 0 < ((Real.pi / s ^ 2 : ℝ) : ℂ).re := div_pos Real.pi_pos (sq_pos_of_ne_zero hs.ne')
  have hsum : (latticeGaussianSum L s u : ℂ) = ∑' x : L, SchwartzMap.gaussian hb (u + x) := by
    rw [latticeGaussianSum_def, ofReal_tsum]
    exact tsum_congr fun x ↦ by
      rw [SchwartzMap.gaussian_apply, ofReal_exp]
      push_cast
      rfl
  -- The Fourier multiplier at positive scale is the integer power `s^dim`.
  have hF (w : E) : 𝓕 (SchwartzMap.gaussian hb : E → ℂ) w =
      (s : ℂ) ^ finrank ℝ E * (Real.exp (-(π * s ^ 2) * ‖w‖ ^ 2) : ℂ) := by
    have hsC : (s : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs.ne'
    have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    have hbase : (π : ℂ) / (↑(π / s ^ 2 : ℝ) : ℂ) = (s : ℂ) ^ 2 := by
      push_cast
      field_simp
    have hpow : ((s : ℂ) ^ 2) ^ (finrank ℝ E / 2 : ℂ) = (s : ℂ) ^ finrank ℝ E := by
      have hr : (s ^ 2) ^ ((finrank ℝ E : ℝ) / 2) = s ^ finrank ℝ E := by
        rw [← Real.rpow_two s, ← Real.rpow_mul hs.le, mul_div_cancel₀ _ (by norm_num),
          Real.rpow_natCast]
      simpa only [ofReal_pow, ofReal_div, ofReal_natCast, ofReal_ofNat,
        ofReal_cpow (sq_nonneg s)] using congrArg Complex.ofReal hr
    rw [SchwartzMap.coe_gaussian, fourier_gaussian_innerProductSpace hb, hbase, hpow, ofReal_exp]
    congr 2
    push_cast
    field_simp
  rw [hsum, SchwartzMap.tsum_eq_tsum_dual_fourier]
  simp_rw [hF, inv_pow, div_inv_eq_mul, mul_assoc]
  rw [tsum_mul_left]

/-- The unshifted Gaussian sum is the dual sum at reciprocal scale, multiplied by
`s^dim / covolume L`. -/
theorem latticeGaussianSum_zero_eq [MeasurableSpace E] [BorelSpace E] {s : ℝ} (hs : 0 < s) :
    latticeGaussianSum L s 0 = (covolume L)⁻¹ * s ^ finrank ℝ E *
      latticeGaussianSum (dual L) s⁻¹ 0 := by
  apply ofReal_injective
  simpa only [zero_add, inner_zero_left, ofReal_zero, mul_zero, Complex.exp_zero,
    mul_one, ofReal_mul, ofReal_inv, ofReal_pow, latticeGaussianSum_def (dual L), ofReal_tsum]
    using latticeGaussianSum_poisson L hs (0 : E)

/-- Among all translates of a full lattice, the unshifted lattice maximizes Gaussian mass. -/
theorem latticeGaussianSum_le_unshifted {s : ℝ} (hs : 0 < s) (u : E) :
    latticeGaussianSum L s u ≤ latticeGaussianSum L s 0 := by
  borelize E
  have hn (v : E) : ‖(latticeGaussianSum L s v : ℂ)‖ = latticeGaussianSum L s v := by
    rw [norm_real, Real.norm_eq_abs, abs_of_nonneg (latticeGaussianSum_nonneg L s v)]
  have hterm (y : dual L) :
      ‖(Real.exp (-(Real.pi / (s⁻¹) ^ 2) * ‖(y : E)‖ ^ 2) : ℂ) *
        Complex.exp (2 * π * I * ⟪u, (y : E)⟫)‖ =
      Real.exp (-(Real.pi / (s⁻¹) ^ 2) * ‖(y : E)‖ ^ 2) := by
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Complex.norm_exp]
    simp [mul_assoc]
  have hvol : 0 ≤ covolume L := covolume_nonneg L
  rw [← hn u, latticeGaussianSum_poisson L hs, norm_mul, norm_mul, norm_inv, norm_real,
    norm_pow, norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hs.le,
    abs_of_nonneg hvol, latticeGaussianSum_zero_eq L hs]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (inv_nonneg.mpr hvol) (pow_nonneg hs.le _))
  rw [latticeGaussianSum_def]
  have hsum := norm_tsum_le_tsum_norm
    ((summable_latticeGaussianSum (dual L) (inv_ne_zero hs.ne') (0 : E)).congr
      fun y ↦ by rw [hterm, zero_add])
  simp_rw [hterm] at hsum
  simpa only [zero_add] using hsum

omit [IsZLattice ℝ L] in
/-- Gaussian mass is monotone in the positive scale. -/
theorem latticeGaussianSum_mono {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) (u : E) :
    latticeGaussianSum L s u ≤ latticeGaussianSum L t u := by
  rw [latticeGaussianSum_def, latticeGaussianSum_def]
  refine (summable_latticeGaussianSum L hs.ne' u).tsum_le_tsum (fun x ↦ ?_)
    (summable_latticeGaussianSum L (hs.trans_le hst).ne' u)
  apply Real.exp_le_exp.mpr
  have h := div_le_div_of_nonneg_left Real.pi_pos.le (sq_pos_of_ne_zero hs.ne')
    (pow_le_pow_left₀ hs.le hst 2)
  exact mul_le_mul_of_nonneg_right (neg_le_neg h) (sq_nonneg _)

/-- Increasing the scale from `t` to `s` increases the Gaussian mass of any translate by
at most the volume scaling factor `(s/t)^dim`, relative to the unshifted lattice at `t`. -/
theorem latticeGaussianSum_le_scale_mul {s t : ℝ} (ht : 0 < t) (hts : t ≤ s) (u : E) :
    latticeGaussianSum L s u ≤ (s / t) ^ finrank ℝ E * latticeGaussianSum L t 0 := by
  borelize E
  have hs := ht.trans_le hts
  have hscale := latticeGaussianSum_mono (dual L) (inv_pos.mpr hs) (inv_anti₀ ht hts) (0 : E)
  calc
    _ ≤ latticeGaussianSum L s 0 := latticeGaussianSum_le_unshifted L hs u
    _ = (covolume L)⁻¹ * s ^ finrank ℝ E * latticeGaussianSum (dual L) s⁻¹ 0 :=
      latticeGaussianSum_zero_eq L hs
    _ ≤ (covolume L)⁻¹ * s ^ finrank ℝ E * latticeGaussianSum (dual L) t⁻¹ 0 :=
      mul_le_mul_of_nonneg_left hscale
        (mul_nonneg (inv_nonneg.mpr (covolume_nonneg L)) (pow_nonneg hs.le _))
    _ = _ := by rw [latticeGaussianSum_zero_eq L ht, div_pow]; field_simp

/-- The unit-scale Gaussian mass of the points outside the open ball of radius `√dim`, on any
translate, is at most `(2 exp(-3π/4))^dim` times the total unshifted mass. -/
theorem tsum_gaussian_outside_sqrt_finrank_le (u : E) :
    (∑' x : {x : L // √(finrank ℝ E : ℝ) ≤ ‖u + (x : E)‖},
      Real.exp (-π * ‖u + (x.val : E)‖ ^ 2)) ≤
        (2 * Real.exp (-3 * π / 4)) ^ finrank ℝ E * latticeGaussianSum L 1 0 := by
  set n := finrank ℝ E
  let A : Set L := {x | √(n : ℝ) ≤ ‖u + (x : E)‖}
  let g : L → ℝ := fun x ↦ Real.exp (-(π / 2 ^ 2) * ‖u + (x : E)‖ ^ 2)
  have hg : Summable g := summable_latticeGaussianSum L two_ne_zero u
  have hfac : 0 ≤ Real.exp (-3 * π / 4 * n) := Real.exp_nonneg _
  calc
    _ ≤ ∑' x : A, Real.exp (-3 * π / 4 * n) * g x := by
      have hf : Summable (fun x : A ↦ Real.exp (-π * ‖u + (x.val : E)‖ ^ 2)) := by
        simpa only [Function.comp_def, one_pow, div_one] using
          (summable_latticeGaussianSum L one_ne_zero u).subtype (· ∈ A)
      refine hf.tsum_le_tsum (fun x ↦ ?_) ((hg.subtype (· ∈ A)).mul_left _)
      dsimp only [g]
      rw [← Real.exp_add, Real.exp_le_exp]
      norm_num only [Nat.reducePow]
      have hn : (n : ℝ) ≤ ‖u + (x.val : E)‖ ^ 2 := by
        exact (Real.sq_sqrt (Nat.cast_nonneg n)).symm.trans_le
          (pow_le_pow_left₀ (Real.sqrt_nonneg _) x.property 2)
      nlinarith [mul_le_mul_of_nonneg_left hn Real.pi_pos.le]
    _ ≤ Real.exp (-3 * π / 4 * n) * latticeGaussianSum L 2 u := by
      rw [tsum_mul_left, latticeGaussianSum_def]
      gcongr
      exact hg.tsum_subtype_le g A (fun _ ↦ Real.exp_nonneg _)
    _ ≤ Real.exp (-3 * π / 4 * n) * (2 ^ n * latticeGaussianSum L 1 0) :=
      mul_le_mul_of_nonneg_left (by
        simpa only [div_one] using latticeGaussianSum_le_scale_mul L zero_lt_one one_le_two u) hfac
    _ = _ := by
      rw [mul_pow, ← Real.exp_natCast_mul]
      ac_rfl

end ZLattice

namespace TauCeti

/-- The exponential base in the radius-`√dim` Gaussian tail bound is less than `1/4`. -/
theorem two_mul_exp_neg_three_pi_div_four_lt_one_div_four : 2 * Real.exp (-3 * π / 4) < 1 / 4 := by
  have hlog : 3 * Real.log 2 < 3 * π / 4 := by
    linarith [Real.log_two_lt_d9, Real.pi_gt_three]
  rw [neg_mul, neg_div, Real.exp_neg, mul_inv_lt_iff₀ (Real.exp_pos _)]
  have he : Real.exp (3 * Real.log 2) = 8 := by
    simpa only [Nat.cast_ofNat, Real.exp_log (by norm_num : (0 : ℝ) < 2),
      show (2 : ℝ) ^ (3 : ℕ) = 8 by norm_num] using Real.exp_natCast_mul 3 (Real.log 2)
  linarith [Real.exp_lt_exp.mpr hlog]

end TauCeti
