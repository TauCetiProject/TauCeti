/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.CanonicalHeight.Basic
public import TauCeti.NumberTheory.Height.TateLimit

/-!
# The canonical height as a limit along all multiples

The canonical height is constructed by averaging the naïve `x`-height along powers of two.
Here we prove the classical formula

`canonicalHeight P = lim_{n → ∞} naiveHeight (n • P) / n²`.

Convergence is uniform in the point: the error is bounded by `C / n²`, with `C` depending
only on the curve. No Northcott or number-field assumption is needed. We also characterize
the canonical height as the unique quadratic map at bounded distance from the naïve height.
This fixes its normalization without referring to the doubling sequence used to construct it.
Finally, the canonical height is Tate's limit `TauCeti.tateLimit` of the naïve height along
multiplication by any `m ≥ 2`, with scaling factor `m ^ 2`.

## Main results

* `WeierstrassCurve.Affine.Point.exists_abs_naiveHeight_nsmul_div_sq_sub_le`: a uniform error bound.
* `WeierstrassCurve.Affine.tendstoUniformly_naiveHeight_nsmul_div_sq`: uniform convergence.
* `WeierstrassCurve.Affine.Point.tendsto_naiveHeight_nsmul_div_sq`: the classical pointwise limit.
* `WeierstrassCurve.Affine.canonicalHeightQuadratic_eq_iff`: the bounded-distance characterization.
* `WeierstrassCurve.Affine.Point.canonicalHeight_eq_tateLimit`: the canonical height is Tate's
  limit of the naïve height along `P ↦ m • P`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VIII.9.
-/

public section

open Filter Height Topology

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] [AdmissibleAbsValues F] [DecidableEq F]
  {W : Affine F} [W.toAffine.IsElliptic]

/-- The normalized naïve heights approximate the canonical height with an error bounded
uniformly in the point by `C / n²`, for every nonzero natural number `n`. -/
theorem Point.exists_abs_naiveHeight_nsmul_div_sq_sub_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ), n ≠ 0 → ∀ P : W.Point,
      |(n • P).naiveHeight / (n : ℝ) ^ 2 - P.canonicalHeight| ≤ C / (n : ℝ) ^ 2 := by
  obtain ⟨C, hC⟩ := Point.abs_canonicalHeight_sub_naiveHeight_le (W := W)
  refine ⟨C, (abs_nonneg _).trans (hC 0), fun n hn P ↦ ?_⟩
  have hn' : (n : ℝ) ^ 2 ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hn)
  rw [div_sub' hn', ← Point.canonicalHeight_nsmul, abs_div,
    abs_of_nonneg (sq_nonneg (n : ℝ))]
  exact div_le_div_of_nonneg_right (by simpa only [abs_sub_comm] using hC (n • P))
    (sq_nonneg _)

/-- The normalized naïve heights converge to the canonical height uniformly over all points. -/
theorem tendstoUniformly_naiveHeight_nsmul_div_sq :
    TendstoUniformly (fun (n : ℕ) (P : W.Point) ↦ (n • P).naiveHeight / (n : ℝ) ^ 2)
      (fun P ↦ P.canonicalHeight) atTop := by
  obtain ⟨C, _, hC⟩ := Point.exists_abs_naiveHeight_nsmul_div_sq_sub_le (W := W)
  have hlim : Tendsto (fun n : ℕ ↦ C / (n : ℝ) ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      ((tendsto_pow_atTop (by decide : 2 ≠ 0)).comp tendsto_natCast_atTop_atTop)
  refine Metric.tendstoUniformly_iff.mpr fun ε hε ↦ ?_
  filter_upwards [hlim.eventually (gt_mem_nhds hε), eventually_ne_atTop 0] with n hn hn0 P
  rw [Real.dist_eq, abs_sub_comm]
  exact (hC n hn0 P).trans_lt hn

/-- The classical limit formula for the canonical height, along all natural multiples. -/
theorem Point.tendsto_naiveHeight_nsmul_div_sq (P : W.Point) :
    Tendsto (fun n : ℕ ↦ (n • P).naiveHeight / (n : ℝ) ^ 2) atTop
      (𝓝 P.canonicalHeight) :=
  tendstoUniformly_naiveHeight_nsmul_div_sq.tendsto_at P

/-- The canonical height is the limit of the normalized naïve heights along all multiples. -/
theorem Point.canonicalHeight_eq_limUnder_naiveHeight_nsmul_div_sq (P : W.Point) :
    P.canonicalHeight = limUnder atTop (fun n : ℕ ↦ (n • P).naiveHeight / (n : ℝ) ^ 2) :=
  P.tendsto_naiveHeight_nsmul_div_sq.limUnder_eq.symm

/-- The canonical height is exactly the quadratic map at bounded distance from the naïve height. -/
theorem canonicalHeightQuadratic_eq_iff (W : Affine F) [W.toAffine.IsElliptic]
    (q : QuadraticMap ℤ W.Point ℝ) :
    canonicalHeightQuadratic W = q ↔ ∃ C : ℝ, ∀ P, |q P - P.naiveHeight| ≤ C := by
  refine ⟨fun h ↦ ?_, fun hq ↦ ?_⟩
  · subst q
    simpa only [canonicalHeightQuadratic_apply] using
      (Point.abs_canonicalHeight_sub_naiveHeight_le (W := W))
  obtain ⟨C, hC⟩ := hq
  ext P
  have hlim : Tendsto (fun n : ℕ ↦ C / (n : ℝ) ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      ((tendsto_pow_atTop (by decide : 2 ≠ 0)).comp tendsto_natCast_atTop_atTop)
  have hzero : Tendsto (fun n : ℕ ↦ q P - (n • P).naiveHeight / (n : ℝ) ^ 2)
      atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ne_atTop 0] with n hn
    have hn' : (n : ℝ) ^ 2 ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hn)
    have hscale : q (n • P) = (n : ℝ) ^ 2 * q P := by
      simpa only [natCast_zsmul, zsmul_eq_mul, Int.cast_mul, Int.cast_natCast, pow_two] using
        q.map_smul (n : ℤ) P
    rw [Real.norm_eq_abs, sub_div' hn', mul_comm, ← hscale, abs_div,
      abs_of_nonneg (sq_nonneg (n : ℝ))]
    exact div_le_div_of_nonneg_right (hC _) (sq_nonneg _)
  have hvalue := tendsto_nhds_unique
    (tendsto_const_nhds.sub P.tendsto_naiveHeight_nsmul_div_sq) hzero
  rw [canonicalHeightQuadratic_apply]
  exact (sub_eq_zero.mp hvalue).symm

/-- **The canonical height is Tate's limit of the naïve height** along multiplication by any
`m ≥ 2`, with scaling factor `m ^ 2`. For `m = 2` this is the doubling construction defining
`canonicalHeight`; for general `m` it says that the construction does not depend on the
multiplication map used. -/
theorem Point.canonicalHeight_eq_tateLimit {m : ℕ} (hm : 1 < m) (P : W.Point) :
    P.canonicalHeight =
      TauCeti.tateLimit (fun Q : W.Point ↦ m • Q) ((m : ℝ) ^ 2) Point.naiveHeight P := by
  obtain ⟨D, hD⟩ := Point.abs_canonicalHeight_sub_naiveHeight_le (W := W)
  have hm' : (1 : ℝ) < (m : ℝ) ^ 2 := one_lt_pow₀ (by exact_mod_cast hm) two_ne_zero
  exact (congrFun (TauCeti.tateLimit_unique hm' (Point.canonicalHeight_nsmul m) hD) P).symm

end WeierstrassCurve.Affine
