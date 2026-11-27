/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.ConvergenceRadius
public import Mathlib.Analysis.Normed.Algebra.GelfandFormula
public import Mathlib.Analysis.Normed.Algebra.UnitizationL1
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.Unbundled.SmoothingSeminorm
public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm

import TauCeti.Analysis.Normed.Unbundled.RootBound
import TauCeti.Analysis.Normed.Unbundled.SpectralNorm.Basic

/-!
# The Gelfand radius: idempotents, nonunital elements, power series, and ultrametric rings

The Gelfand radius `gelfandRadius a` of an element of a normed ring is the limit of
`‖a ^ k‖ ^ (1 / k)`. A nonzero idempotent has Gelfand radius one, whatever its norm, since all
of its positive powers coincide with it.

In a unital complex Banach algebra, Gelfand's spectral radius formula implies that if
`spectrum ℂ a` lies inside an open extended ball `Metric.eball z₀ r` of radius at most the
convergence radius of a scalar formal power series `p`, then `∑ ‖p.coeff n • (a - z₀)^n‖`
converges.

A nonunital algebra has no powers `a ^ 0`, so its Gelfand radius is computed in the ℓ¹
unitization `WithLp 1 (Unitization ℂ A)`, into which `A` embeds isometrically. Gelfand's formula
holds there: the spectral radius of `a`, the supremum of the moduli of its quasispectrum, is the
Gelfand radius of its image in the unitization. Together these give a lower bound on spectral
radii of elements of nonunital Banach algebras near a nonzero idempotent, which is how
idempotents obstruct the separating spaces of algebra homomorphisms.

Finally, whenever `ENNReal.ofReal (gelfandRadius a) < p.radius`, the power series
`∑ p.coeff k • a ^ k` is absolutely summable in norm, with no completeness assumption on the
ring. Combined with Gelfand's formula in a complex Banach algebra, this gives absolute convergence
of `∑ p.coeff k • (a - z₀ 1) ^ k` whenever `spectrum ℂ a ⊆ Metric.eball z₀ p.radius`.

In any seminormed commutative ring `A`, `gelfandRadius` agrees with Mathlib's smoothing seminorm
`smoothingFun (normRingSeminorm A)` and forms a power-multiplicative `RingSeminorm A`
(`TauCeti.gelfandRadiusRingSeminorm`) without requiring `‖(1 : A)‖ ≤ 1`. When `A` is ultrametric,
`gelfandRadius` is moreover nonarchimedean (`Commute.gelfandRadius_add_le_max`,
`TauCeti.isNonarchimedean_gelfandRadius`), yielding the polynomial root bound
`TauCeti.gelfandRadius_le_spectralValue_of_aeval_eq_zero`.

## Main results

* `IsIdempotentElem.gelfandRadius_eq_one`: a nonzero idempotent has Gelfand radius one.
* `IsIdempotentElem.one_le_gelfandRadius_mul_norm_inverse`: a lower bound on the Gelfand radius
  of elements of the corner `p R p`.
* `TauCeti.summable_norm_smul_sub_pow_of_le_radius`: absolute convergence of a formal power series
  evaluated at `a - z₀` whenever `spectrum ℂ a` lies in `Metric.eball z₀ r` with `r ≤ p.radius`.
* `TauCeti.spectralRadius_eq_gelfandRadius_toLp_inr`: Gelfand's formula for a nonunital complex
  Banach algebra, through its ℓ¹ unitization.
* `FormalMultilinearSeries.summable_norm_coeff_smul_pow_of_gelfandRadius_lt`: absolute convergence
  of `∑ p.coeff k • a ^ k` when `ENNReal.ofReal (gelfandRadius a) < p.radius`.
* `FormalMultilinearSeries.summable_norm_coeff_smul_pow_of_spectrum_subset_eball`: absolute
  convergence of `∑ p.coeff k • (a - z₀ 1) ^ k` in a complex Banach algebra when
  `spectrum ℂ a ⊆ Metric.eball z₀ p.radius`.
* `TauCeti.le_gelfandRadius_of_bound`: lower bound `r ≤ gelfandRadius a` from
  `∀ n ≠ 0, r ^ n ≤ C * ‖a ^ n‖`.
* `Commute.gelfandRadius_add_le_max` and `TauCeti.isNonarchimedean_gelfandRadius`: ultrametric
  subadditivity of `gelfandRadius` without `‖1‖ ≤ 1`.
* `TauCeti.smoothingFun_normRingSeminorm_eq_gelfandRadius` and
  `TauCeti.gelfandRadiusRingSeminorm`: identification with `smoothingFun (normRingSeminorm A)` and
  `RingSeminorm` bundling.
* `TauCeti.gelfandRadius_le_spectralValue_of_aeval_eq_zero`: root bound
  `gelfandRadius a ≤ spectralValue p` for any monic polynomial `p` vanishing at `a` in an
  ultrametric seminormed commutative algebra.
-/

public section

open Filter Topology
open scoped ENNReal NNReal

/-- A nonzero idempotent has Gelfand radius one: all its positive powers are equal to it, so
`‖p ^ k‖ ^ (1 / k) = ‖p‖ ^ (1 / k)` tends to one. No normalization of the norm is needed. -/
theorem IsIdempotentElem.gelfandRadius_eq_one {A : Type*} [NormedRing A] {p : A}
    (hp : IsIdempotentElem p) (h0 : p ≠ 0) : gelfandRadius p = 1 := by
  refine tendsto_nhds_unique (tendsto_gelfandRadius p) ?_
  have h : Tendsto (fun k : ℕ ↦ ‖p‖ ^ (k : ℝ)⁻¹) atTop (𝓝 1) :=
    ((Real.continuous_const_rpow (norm_ne_zero_iff.2 h0)).tendsto' 0 1
      (Real.rpow_zero _)).comp tendsto_inv_atTop_nhds_zero_nat
  refine h.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with k hk
  rw [hp.pow_eq hk]

/-- Elements of the corner `p R p` of a nonzero idempotent `p` are bounded away from
quasinilpotence near `p`. If `p * y = y = y * p` and `1 - p + y` is a unit, then `y` is
`p * (1 - p + y)`, and the Gelfand radius of `y` is at least `‖(1 - p + y)⁻¹‖⁻¹`. As `y`
tends to `p`, this lower bound tends to `‖1‖⁻¹`. -/
theorem IsIdempotentElem.one_le_gelfandRadius_mul_norm_inverse {R : Type*} [NormedRing R]
    {p y : R} (hp : IsIdempotentElem p) (h0 : p ≠ 0) (hpy : p * y = y) (hyp : y * p = y)
    (hu : IsUnit (1 - p + y)) : 1 ≤ gelfandRadius y * ‖Ring.inverse (1 - p + y)‖ := by
  obtain ⟨w, hw⟩ := hu
  have hyw : y = p * w := by rw [hw, mul_add, mul_sub, mul_one, hp.eq, sub_self, zero_add, hpy]
  have hcomm : Commute y (w⁻¹ : Rˣ) := by
    refine Commute.units_inv_right ?_
    rw [hw]
    exact ((Commute.one_right y).sub_right (hpy.trans hyp.symm).symm).add_right (Commute.refl y)
  rw [← hw, Ring.inverse_unit, ← hp.gelfandRadius_eq_one h0]
  calc gelfandRadius p = gelfandRadius (y * (w⁻¹ : Rˣ)) := by
        rw [hyw, mul_assoc, w.mul_inv, mul_one]
    _ ≤ gelfandRadius y * gelfandRadius ((w⁻¹ : Rˣ) : R) := hcomm.gelfandRadius_mul_le
    _ ≤ gelfandRadius y * ‖((w⁻¹ : Rˣ) : R)‖ := by grw [gelfandRadius_le_norm ((w⁻¹ : Rˣ) : R)]

/-- In an ultrametric seminormed ring, the Gelfand radius of a sum of commuting elements is at most
the maximum of their Gelfand radii. No normalization on `‖1‖` is needed. -/
theorem Commute.gelfandRadius_add_le_max {A : Type*} [SeminormedRing A] [IsUltrametricDist A]
    {a b : A} (h : Commute a b) :
    gelfandRadius (a + b) ≤ max (gelfandRadius a) (gelfandRadius b) := by
  refine le_of_forall_gt_imp_ge_of_dense fun r hr ↦ ?_
  have ha_lt : gelfandRadius a < r := (le_max_left _ _).trans_lt hr
  have hb_lt : gelfandRadius b < r := (le_max_right _ _).trans_lt hr
  have hr0 : 0 < r := (gelfandRadius_nonneg a).trans_lt ha_lt
  obtain ⟨Ca, hCa, ha⟩ := norm_pow_le_mul_pow_of_gelfandRadius_lt a ha_lt
  obtain ⟨Cb, hCb, hb⟩ := norm_pow_le_mul_pow_of_gelfandRadius_lt b hb_lt
  refine gelfandRadius_le_of_bound hr0.le (C := Ca * Cb * ‖(1 : A)‖) fun n ↦ ?_
  rw [h.add_pow]
  obtain ⟨k, hk, hle⟩ := IsUltrametricDist.isNonarchimedean_norm.finset_image_add_of_nonempty
    (fun k ↦ a ^ k * b ^ (n - k) * (n.choose k : A)) (Finset.nonempty_range_add_one)
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hnat : ‖(n.choose k : A)‖ ≤ ‖(1 : A)‖ := by
    simpa using IsUltrametricDist.norm_nsmul_le (1 : A) (n.choose k)
  calc
    ‖∑ m ∈ Finset.range (n + 1), a ^ m * b ^ (n - m) * (n.choose m : A)‖
        ≤ ‖a ^ k * b ^ (n - k) * (n.choose k : A)‖ := hle
    _ ≤ ‖a ^ k‖ * ‖b ^ (n - k)‖ * ‖(n.choose k : A)‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (Ca * r ^ k) * (Cb * r ^ (n - k)) * ‖(1 : A)‖ := by
      gcongr
      · exact ha k
      · exact hb (n - k)
    _ = Ca * Cb * ‖(1 : A)‖ * r ^ n := by
      have hrpow : r ^ k * r ^ (n - k) = r ^ n := by
        rw [← pow_add, Nat.add_sub_of_le hkn]
      calc
        (Ca * r ^ k) * (Cb * r ^ (n - k)) * ‖(1 : A)‖
            = Ca * Cb * ‖(1 : A)‖ * (r ^ k * r ^ (n - k)) := by ring
        _ = Ca * Cb * ‖(1 : A)‖ * r ^ n := by rw [hrpow]

namespace FormalMultilinearSeries

/-- If `ENNReal.ofReal (gelfandRadius a) < p.radius`, then `∑ p.coeff k • a ^ k` is absolutely
summable in norm, with no completeness assumption on `A`. -/
theorem summable_norm_coeff_smul_pow_of_gelfandRadius_lt {𝕜 A : Type*} [NontriviallyNormedField 𝕜]
    [SeminormedRing A] [SMulZeroClass 𝕜 A] [IsBoundedSMul 𝕜 A]
    (p : FormalMultilinearSeries 𝕜 𝕜 𝕜) {a : A}
    (ha : ENNReal.ofReal (gelfandRadius a) < p.radius) :
    Summable fun k : ℕ ↦ ‖p.coeff k • a ^ k‖ := by
  obtain ⟨ρ, hg_lt, hρ_lt⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp ha
  have hρ_gt : gelfandRadius a < (ρ : ℝ) :=
    (ENNReal.ofReal_lt_iff_lt_toReal (gelfandRadius_nonneg a) ENNReal.coe_ne_top).mp hg_lt
  obtain ⟨C, _, hC⟩ := norm_pow_le_mul_pow_of_gelfandRadius_lt a hρ_gt
  refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun k ↦ ?_)
    ((p.summable_norm_mul_pow hρ_lt).mul_left C)
  calc ‖p.coeff k • a ^ k‖ ≤ ‖p.coeff k‖ * ‖a ^ k‖ := norm_smul_le _ _
    _ = ‖p k‖ * ‖a ^ k‖ := by rw [p.norm_apply_eq_norm_coef]
    _ ≤ ‖p k‖ * (C * (ρ : ℝ) ^ k) := mul_le_mul_of_nonneg_left (hC k) (norm_nonneg _)
    _ = C * (‖p k‖ * (ρ : ℝ) ^ k) := by ring

/-- **Absolute convergence of Banach-algebra power series under spectral containment.** If
`spectrum ℂ a ⊆ Metric.eball z₀ p.radius` in a complex Banach algebra `A`, then
`∑ p.coeff k • (a - z₀ 1) ^ k` is absolutely summable in norm (including in the zero algebra). -/
theorem summable_norm_coeff_smul_pow_of_spectrum_subset_eball {A : Type*} [NormedRing A]
    [NormedAlgebra ℂ A] [CompleteSpace A] (p : FormalMultilinearSeries ℂ ℂ ℂ) {a : A} {z₀ : ℂ}
    (ha : spectrum ℂ a ⊆ Metric.eball z₀ p.radius) :
    Summable fun k : ℕ ↦ ‖p.coeff k • (a - algebraMap ℂ A z₀) ^ k‖ := by
  rcases subsingleton_or_nontrivial A with _ | _
  · convert summable_zero with k
    rw [Subsingleton.elim (p.coeff k • (a - algebraMap ℂ A z₀) ^ k) 0, norm_zero]
  set b := a - algebraMap ℂ A z₀
  obtain ⟨w, hw, hsr⟩ := spectrum.exists_eNorm_eq_spectralRadius b
  have hw_mem : w + z₀ ∈ spectrum ℂ a := by
    rwa [spectrum.add_mem_iff, neg_add_eq_sub]
  have hlt : ENNReal.ofReal (gelfandRadius b) < p.radius := by
    rw [← spectrum.spectralRadius_eq_gelfandRadius]
    have hed : edist (w + z₀) z₀ < p.radius := Metric.mem_eball.mp (ha hw_mem)
    simpa only [← hsr, eDist_eq_eNorm_sub, add_sub_cancel_right, eNorm_eq_nnNorm] using hed
  exact p.summable_norm_coeff_smul_pow_of_gelfandRadius_lt hlt

end FormalMultilinearSeries

namespace TauCeti

section NonUnital

/-- If `spectrum ℂ a` lies in the open extended ball `Metric.eball z₀ r` and `r` does not exceed
the convergence radius of a formal power series `p : FormalMultilinearSeries ℂ ℂ ℂ`, then
`∑ ‖p.coeff n • (a - z₀)^n‖` converges. -/
theorem summable_norm_smul_sub_pow_of_le_radius {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] (a : A) {p : FormalMultilinearSeries ℂ ℂ ℂ}
    {z₀ : ℂ} {r : ℝ≥0∞} (ha : spectrum ℂ a ⊆ Metric.eball z₀ r) (hr : r ≤ p.radius) :
    Summable fun n => ‖p.coeff n • (a - algebraMap ℂ A z₀) ^ n‖ := by
  let b := a - algebraMap ℂ A z₀
  rcases subsingleton_or_nontrivial A with hsub | hnt
  · exact summable_zero.congr fun n => by
      rw [Subsingleton.elim (p.coeff n • b ^ n) 0, norm_zero]
  · obtain ⟨w, hw, hw_eq⟩ := spectrum.exists_eNorm_eq_spectralRadius b
    have hzw : z₀ + w ∈ spectrum ℂ a :=
      (add_comm z₀ w).symm ▸ spectrum.add_mem_iff.mpr (by simpa [b, neg_add_eq_sub] using hw)
    have hw_lt : (‖w‖₊ : ℝ≥0∞) < r := by
      have hmem := ha hzw
      rwa [Metric.mem_eball, edist_nndist, nnDist_eq_nnNorm, add_sub_cancel_left] at hmem
    have hspec : spectralRadius ℂ b < r := hw_eq ▸ hw_lt
    obtain ⟨ρ, hρ_gt, hρ_lt⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hspec
    rw [spectrum.spectralRadius_eq_gelfandRadius,
      ENNReal.ofReal_lt_coe_iff (gelfandRadius_nonneg b)] at hρ_gt
    obtain ⟨C, _, hC⟩ := norm_pow_le_mul_pow_of_gelfandRadius_lt b hρ_gt
    have hpsum : Summable fun n => ‖p.coeff n‖ * (ρ : ℝ) ^ n := by
      simpa only [FormalMultilinearSeries.norm_apply_eq_norm_coef] using
        p.summable_norm_mul_pow (hρ_lt.trans_le hr)
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) (hpsum.mul_left C)
    rw [norm_smul]
    calc ‖p.coeff n‖ * ‖b ^ n‖
        ≤ ‖p.coeff n‖ * (C * (ρ : ℝ) ^ n) := mul_le_mul_of_nonneg_left (hC n) (norm_nonneg _)
      _ = C * (‖p.coeff n‖ * (ρ : ℝ) ^ n) := by ring

variable {A : Type*} [NonUnitalNormedRing A] [NormedSpace ℂ A] [IsScalarTower ℂ A A]
  [SMulCommClass ℂ A A] [CompleteSpace A]

/-- **Gelfand's formula** in a nonunital complex Banach algebra: the spectral radius of `a`,
computed from its quasispectrum, is the Gelfand radius of its image in the ℓ¹ unitization. -/
theorem spectralRadius_eq_gelfandRadius_toLp_inr (a : A) :
    spectralRadius ℂ a = ENNReal.ofReal (gelfandRadius (WithLp.toLp 1 (a : Unitization ℂ A))) := by
  rw [← spectrum.spectralRadius_eq_gelfandRadius, spectralRadius_eq_of_unital,
    ← AlgEquiv.spectrum_eq (WithLp.unitizationAlgEquiv (𝕜 := ℂ) (A := A) ℂ),
    WithLp.unitizationAlgEquiv_apply,
    WithLp.ofLp_toLp, ← Unitization.quasispectrum_eq_spectrum_inr, spectralRadius]

end NonUnital

/-- If `r ^ n ≤ C * ‖a ^ n‖` for all `n ≠ 0`, then `r ≤ gelfandRadius a`.
Dual to Mathlib's `gelfandRadius_le_of_bound`. -/
theorem le_gelfandRadius_of_bound {A : Type*} [SeminormedRing A] {a : A} {C r : ℝ}
    (h : ∀ n ≠ 0, r ^ n ≤ C * ‖a ^ n‖) : r ≤ gelfandRadius a := by
  by_cases hr : 0 ≤ r
  · have hC : 0 < max C 1 := by positivity
    have hlim : Tendsto (fun n : ℕ ↦ max C 1 ^ (n : ℝ)⁻¹ * ‖a ^ n‖ ^ (n : ℝ)⁻¹)
        atTop (𝓝 (gelfandRadius a)) := by
      simpa using (((Real.continuous_const_rpow hC.ne').tendsto' 0 1 (Real.rpow_zero _)).comp
        tendsto_inv_atTop_nhds_zero_nat).mul (tendsto_gelfandRadius a)
    refine ge_of_tendsto hlim ?_
    filter_upwards [eventually_ne_atTop 0] with n hn
    have hstep : r ^ n ≤ max C 1 * ‖a ^ n‖ :=
      (h n hn).trans (mul_le_mul_of_nonneg_right (le_max_left C 1) (norm_nonneg _))
    calc
      r = (r ^ n) ^ (n : ℝ)⁻¹ := (Real.pow_rpow_inv_natCast hr hn).symm
      _ ≤ (max C 1 * ‖a ^ n‖) ^ (n : ℝ)⁻¹ :=
        Real.rpow_le_rpow (pow_nonneg hr n) hstep (by positivity)
      _ = max C 1 ^ (n : ℝ)⁻¹ * ‖a ^ n‖ ^ (n : ℝ)⁻¹ :=
        Real.mul_rpow hC.le (norm_nonneg _)
  · exact (le_of_not_ge hr).trans (gelfandRadius_nonneg a)

/-- In any seminormed commutative ring, `smoothingFun (normRingSeminorm A)` agrees with Mathlib's
`gelfandRadius`, without requiring `‖(1 : A)‖ ≤ 1`. -/
theorem smoothingFun_normRingSeminorm_eq_gelfandRadius {A : Type*} [SeminormedCommRing A] (a : A) :
    smoothingFun (normRingSeminorm A) a = gelfandRadius a := by
  have hnorm (x : A) : normRingSeminorm A x = ‖x‖ := rfl
  refine le_antisymm ?_ ?_
  · refine ge_of_tendsto' (tendsto_gelfandRadius' a) fun k ↦ ?_
    have hk := smoothingFun_le (normRingSeminorm A) a k
    rwa [hnorm, one_div] at hk
  · refine le_ciInf fun k ↦ ?_
    rw [hnorm, one_div]
    exact gelfandRadius_le_norm_pow a k.ne_zero

/-- In an ultrametric seminormed commutative ring, `gelfandRadius` is nonarchimedean. -/
theorem isNonarchimedean_gelfandRadius {A : Type*} [SeminormedCommRing A] [IsUltrametricDist A] :
    IsNonarchimedean (gelfandRadius : A → ℝ) := fun a b ↦
  (Commute.all a b).gelfandRadius_add_le_max

/-- In any seminormed commutative ring, `gelfandRadius` bundled as a `RingSeminorm`, without
requiring `‖(1 : A)‖ ≤ 1`. -/
noncomputable def gelfandRadiusRingSeminorm (A : Type*) [SeminormedCommRing A] :
    RingSeminorm A where
  toFun := gelfandRadius
  map_zero' := gelfandRadius_zero
  add_le' := gelfandRadius_add_le
  neg' := gelfandRadius_neg
  mul_le' := gelfandRadius_mul_le

/-- `gelfandRadiusRingSeminorm A` evaluates to `gelfandRadius`. -/
@[simp]
theorem gelfandRadiusRingSeminorm_apply {A : Type*} [SeminormedCommRing A] (a : A) :
    gelfandRadiusRingSeminorm A a = gelfandRadius a := (rfl)

/-- `gelfandRadiusRingSeminorm A` is power-multiplicative. -/
theorem isPowMul_gelfandRadiusRingSeminorm {A : Type*} [SeminormedCommRing A] :
    IsPowMul (gelfandRadiusRingSeminorm A) := fun a _n hn ↦
  gelfandRadius_pow_of_ne_zero a (Nat.one_le_iff_ne_zero.mp hn)

/-- In an ultrametric seminormed commutative ring, `gelfandRadiusRingSeminorm A` is
nonarchimedean. -/
theorem isNonarchimedean_gelfandRadiusRingSeminorm {A : Type*} [SeminormedCommRing A]
    [IsUltrametricDist A] : IsNonarchimedean (gelfandRadiusRingSeminorm A) :=
  isNonarchimedean_gelfandRadius

open Polynomial in
/-- If `a` is a root of a monic polynomial `p : B[X]` in an ultrametric seminormed commutative
`B`-algebra `A` whose structure map satisfies `gelfandRadius (algebraMap B A b) ≤ ‖b‖`, then
`gelfandRadius a ≤ spectralValue p`. -/
theorem gelfandRadius_le_spectralValue_of_aeval_eq_zero {B A : Type*} [SeminormedCommRing B]
    [SeminormedCommRing A] [IsUltrametricDist A] [Algebra B A]
    (hBA : ∀ b : B, gelfandRadius (algebraMap B A b) ≤ ‖b‖)
    {p : B[X]} (hp : p.Monic) {a : A} (ha : aeval a p = 0) :
    gelfandRadius a ≤ spectralValue p := by
  rcases subsingleton_or_nontrivial A with _ | _
  · rw [Subsingleton.elim a 0, gelfandRadius_zero]
    exact spectralValue_nonneg p
  have hroot := (hp.map (algebraMap B A)).apply_le_iSup_apply_coeff_rpow_of_eval_eq_zero
    (map_zero _) (apply_nonneg _) (map_mul_le_mul _)
    isPowMul_gelfandRadiusRingSeminorm isNonarchimedean_gelfandRadiusRingSeminorm
    (x := a) (by rw [eval_map_algebraMap, ha])
  have hdeg : (p.map (algebraMap B A)).natDegree = p.natDegree :=
    hp.natDegree_map (algebraMap B A)
  rw [← gelfandRadiusRingSeminorm_apply, spectralValue_eq_iSup_fin]
  refine hroot.trans (Real.iSup_le (fun ⟨j, hj⟩ ↦ ?_)
    (Real.iSup_nonneg fun _ ↦ Real.rpow_nonneg (norm_nonneg _) _))
  have hjd : j < p.natDegree := hdeg ▸ hj
  rw [Fin.val_mk, gelfandRadiusRingSeminorm_apply, coeff_map, hdeg]
  refine le_trans ?_ (le_ciSup (Finite.bddAbove_range _) ⟨j, hjd⟩)
  exact Real.rpow_le_rpow (gelfandRadius_nonneg _) (hBA _)
    (one_div_nonneg.mpr (sub_nonneg.mpr (Nat.cast_le.mpr hjd.le)))

end TauCeti
