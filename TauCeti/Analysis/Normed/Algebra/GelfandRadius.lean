/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.ConvergenceRadius
public import Mathlib.Analysis.Normed.Algebra.GelfandFormula
public import Mathlib.Analysis.Normed.Algebra.UnitizationL1

/-!
# The Gelfand radius of idempotents, power series, and nonunital elements

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

## Main results

* `IsIdempotentElem.gelfandRadius_eq_one`: a nonzero idempotent has Gelfand radius one.
* `IsIdempotentElem.one_le_gelfandRadius_mul_norm_inverse`: a lower bound on the Gelfand radius
  of elements of the corner `p R p`.
* `TauCeti.summable_norm_smul_sub_pow_of_le_radius`: absolute convergence of a formal power series
  evaluated at `a - z₀` whenever `spectrum ℂ a` lies in `Metric.eball z₀ r` with `r ≤ p.radius`.
* `TauCeti.spectralRadius_eq_gelfandRadius_toLp_inr`: Gelfand's formula for a nonunital complex
  Banach algebra, through its ℓ¹ unitization.
-/

public section

open Filter Topology
open scoped ENNReal

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

namespace TauCeti

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
  · obtain ⟨w, hw, hw_eq⟩ := spectrum.exists_nnNorm_eq_spectralRadius b
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

end TauCeti
