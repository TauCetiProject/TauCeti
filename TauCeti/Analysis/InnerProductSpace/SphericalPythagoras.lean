/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# The spherical right-triangle law, and the Pythagorean angle inequality

Let `K` be a closed subspace of an inner product space, `e ∈ K` a unit vector and
`f` an arbitrary unit vector whose projection onto `K` is nonzero.  Write

* `ω` for the line angle between `e` and `f`;
* `η` for the line angle between `f` and `K`, so that `cos η = ‖P f‖`;
* `ψ` for the line angle between `e` and the normalized projection
  `g = ‖P f‖⁻¹ • P f`, which is the direction `f` points to inside `K`.

Because `e` lies in `K` and `f - P f` is orthogonal to `K`, the inner product
`⟪e, f⟫` equals `⟪e, P f⟫`, and taking norms gives the **exact** identity

```text
cos ω = cos η * cos ψ
```

— the spherical law of cosines for a right triangle.  From it,

```text
ω ^ 2 ≤ η ^ 2 + ψ ^ 2
```

which is likewise **exact on `[0, π/2]²`, not a small-angle approximation.**

## Main results

* `TauCeti.cos_sqrt_sq_add_sq_le_cos_mul_cos` — the scalar inequality
  `cos √(a² + b²) ≤ cos a * cos b` for `a, b ∈ [0, π/2]`.
* `TauCeti.arccos_cos_mul_cos_le_sqrt` — its `arccos` form.
* `TauCeti.sq_le_sq_add_sq_of_cos_eq_cos_mul_cos` — the Pythagorean inequality
  for any angle satisfying the spherical identity.
* `TauCeti.Submodule.cos_lineAngle_eq_mul` — the exact identity, in an inner
  product space over an `RCLike` field.
* `TauCeti.Submodule.sq_lineAngle_le_sq_add_sq` — the two combined: the angle
  between `e` and `f` is dominated in square by the out-of-plane angle plus the
  in-plane angle.

## The scalar proof

Set `h t = -log (cos t) / t ^ 2` on `(0, π/2)`.  Then `h` is monotone, because

```text
h' t = (t * tan t + 2 * log (cos t)) / t ^ 3
```

and the numerator `q t` vanishes at `0` with
`q' t = t / cos t ^ 2 - tan t = (t - sin t * cos t) / cos t ^ 2 ≥ 0`,
the last step being `sin t * cos t ≤ sin t ≤ t`.  With `r = √(a² + b²)` and
`a, b ≤ r < π/2`,

```text
-log (cos a * cos b) = a ^ 2 * h a + b ^ 2 * h b ≤ (a ^ 2 + b ^ 2) * h r
                     = -log (cos r),
```

so `cos a * cos b ≥ cos r`.  When `r ≥ π/2` the inequality is immediate, since
then `cos r ≤ 0 ≤ cos a * cos b`; note `r ≤ √2 * (π/2) < π`, so `cos r` never
turns positive again.

## Sources

The identity is the spherical Pythagorean theorem.  The consumer is the
Davis--Kahan 1970 Section 9 free-beam example, whose final individual
eigenvector bound combines a Schur-complement in-plane estimate with an
out-of-plane tangent estimate exactly this way.

## Provenance

*New.*  Statement and proof are ours.
-/

public section

open scoped InnerProductSpace

namespace TauCeti

open Real

/-! ### The scalar inequality `cos √(a² + b²) ≤ cos a * cos b` -/

private lemma cos_pos_of_nonneg_of_lt_pi_div_two {t : ℝ} (h0 : 0 ≤ t)
    (h : t < π / 2) : 0 < Real.cos t :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h⟩

/-- The numerator appearing in the derivative of `t ↦ -log (cos t) / t ^ 2`. -/
private noncomputable def logCosNumer (t : ℝ) : ℝ :=
  t * Real.tan t + 2 * Real.log (Real.cos t)

private lemma hasDerivAt_logCosNumer {t : ℝ} (ht : Real.cos t ≠ 0) :
    HasDerivAt logCosNumer (t / Real.cos t ^ 2 - Real.tan t) t := by
  have h1 : HasDerivAt (fun s : ℝ => s * Real.tan s)
      (1 * Real.tan t + t * (1 / Real.cos t ^ 2)) t :=
    (hasDerivAt_id t).mul (Real.hasDerivAt_tan ht)
  have h2 : HasDerivAt (fun s : ℝ => Real.log (Real.cos s))
      ((Real.cos t)⁻¹ * -Real.sin t) t :=
    (Real.hasDerivAt_log ht).comp t (Real.hasDerivAt_cos t)
  have h3 := h1.add (HasDerivAt.const_mul (2 : ℝ) h2)
  refine h3.congr_deriv ?_
  simp only [Real.tan_eq_sin_div_cos]
  field_simp
  ring

private lemma logCosNumer_deriv_nonneg {t : ℝ} (h0 : 0 < t) (h : t < π / 2) :
    0 ≤ t / Real.cos t ^ 2 - Real.tan t := by
  have hc : 0 < Real.cos t := cos_pos_of_nonneg_of_lt_pi_div_two h0.le h
  have hs : 0 ≤ Real.sin t :=
    Real.sin_nonneg_of_nonneg_of_le_pi h0.le (by linarith [Real.pi_pos])
  have hsl : Real.sin t ≤ t := Real.sin_le h0.le
  have hc1 : Real.cos t ≤ 1 := Real.cos_le_one t
  have hkey : Real.sin t * Real.cos t ≤ t := by nlinarith
  have hsplit : t / Real.cos t ^ 2 - Real.sin t / Real.cos t =
      (t - Real.sin t * Real.cos t) / Real.cos t ^ 2 := by
    field_simp
  rw [Real.tan_eq_sin_div_cos, hsplit]
  exact div_nonneg (by linarith) (by positivity)

private lemma logCosNumer_nonneg {t : ℝ} (h0 : 0 ≤ t) (h : t < π / 2) :
    0 ≤ logCosNumer t := by
  have hD : Convex ℝ (Set.Ico (0 : ℝ) (π / 2)) := convex_Ico _ _
  have hint : interior (Set.Ico (0 : ℝ) (π / 2)) = Set.Ioo 0 (π / 2) := interior_Ico
  have hmono : MonotoneOn logCosNumer (Set.Ico (0 : ℝ) (π / 2)) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun s =>
      s / Real.cos s ^ 2 - Real.tan s) hD ?_ ?_ ?_
    · intro s hs
      exact ((hasDerivAt_logCosNumer
        (cos_pos_of_nonneg_of_lt_pi_div_two hs.1 hs.2).ne').continuousAt).continuousWithinAt
    · intro s hs
      rw [hint] at hs
      exact (hasDerivAt_logCosNumer
        (cos_pos_of_nonneg_of_lt_pi_div_two hs.1.le hs.2).ne').hasDerivWithinAt
    · intro s hs
      rw [hint] at hs
      exact logCosNumer_deriv_nonneg hs.1 hs.2
  have hzero : logCosNumer 0 = 0 := by simp [logCosNumer]
  have := hmono (Set.mem_Ico.2 ⟨le_refl 0, by linarith [Real.pi_pos]⟩)
    (Set.mem_Ico.2 ⟨h0, h⟩) h0
  simpa [hzero] using this

/-- The quotient whose monotonicity carries the whole scalar argument. -/
private noncomputable def logCosQuot (t : ℝ) : ℝ :=
  -Real.log (Real.cos t) / t ^ 2

private lemma hasDerivAt_logCosQuot {t : ℝ} (h0 : 0 < t) (h : t < π / 2) :
    HasDerivAt logCosQuot (logCosNumer t / t ^ 3) t := by
  have hc : 0 < Real.cos t := cos_pos_of_nonneg_of_lt_pi_div_two h0.le h
  have h2 : HasDerivAt (fun s : ℝ => Real.log (Real.cos s))
      ((Real.cos t)⁻¹ * -Real.sin t) t :=
    (Real.hasDerivAt_log hc.ne').comp t (Real.hasDerivAt_cos t)
  have hn : HasDerivAt (fun s : ℝ => -Real.log (Real.cos s))
      (-((Real.cos t)⁻¹ * -Real.sin t)) t := h2.neg
  have hd : HasDerivAt (fun s : ℝ => s ^ 2) ((2 : ℕ) * t ^ (2 - 1)) t :=
    hasDerivAt_pow 2 t
  have hdiv := hn.div hd (by positivity)
  refine hdiv.congr_deriv ?_
  have ht3 : t ^ 3 ≠ 0 := by positivity
  simp only [logCosNumer, Real.tan_eq_sin_div_cos]
  field_simp
  ring

private lemma logCosQuot_monotoneOn :
    MonotoneOn logCosQuot (Set.Ioo (0 : ℝ) (π / 2)) := by
  have hD : Convex ℝ (Set.Ioo (0 : ℝ) (π / 2)) := convex_Ioo _ _
  have hint : interior (Set.Ioo (0 : ℝ) (π / 2)) = Set.Ioo 0 (π / 2) :=
    isOpen_Ioo.interior_eq
  refine monotoneOn_of_hasDerivWithinAt_nonneg
    (f' := fun s => logCosNumer s / s ^ 3) hD ?_ ?_ ?_
  · intro s hs
    exact ((hasDerivAt_logCosQuot hs.1 hs.2).continuousAt).continuousWithinAt
  · intro s hs
    rw [hint] at hs
    exact (hasDerivAt_logCosQuot hs.1 hs.2).hasDerivWithinAt
  · intro s hs
    rw [hint] at hs
    exact div_nonneg (logCosNumer_nonneg hs.1.le hs.2) (pow_nonneg hs.1.le 3)

/-- **The spherical Pythagorean inequality, scalar form.**  For two angles in
the first quadrant, `cos a * cos b` never drops below the cosine of the
Euclidean combination `√(a² + b²)`. -/
theorem cos_sqrt_sq_add_sq_le_cos_mul_cos {a b : ℝ} (ha0 : 0 ≤ a)
    (ha : a ≤ π / 2) (hb0 : 0 ≤ b) (hb : b ≤ π / 2) :
    Real.cos (Real.sqrt (a ^ 2 + b ^ 2)) ≤ Real.cos a * Real.cos b := by
  set r := Real.sqrt (a ^ 2 + b ^ 2) with hr
  have hrnn : 0 ≤ r := Real.sqrt_nonneg _
  have hrsq : r ^ 2 = a ^ 2 + b ^ 2 := Real.sq_sqrt (by positivity)
  have har : a ≤ r := by nlinarith
  have hbr : b ≤ r := by nlinarith
  have hcosa : 0 ≤ Real.cos a :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], ha⟩
  have hcosb : 0 ≤ Real.cos b :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hb⟩
  rcases le_or_gt (π / 2) r with hcase | hcase
  · -- large radius: the left side is already nonpositive
    have hrle : r ≤ π := by
      nlinarith [Real.pi_pos, Real.sq_sqrt (show (0:ℝ) ≤ a ^ 2 + b ^ 2 by positivity)]
    have : Real.cos r ≤ 0 :=
      Real.cos_nonpos_of_pi_div_two_le_of_le hcase (by linarith [Real.pi_pos])
    exact this.trans (by positivity)
  · -- small radius: the monotone quotient argument
    have hcosr : 0 < Real.cos r := cos_pos_of_nonneg_of_lt_pi_div_two hrnn hcase
    rcases eq_or_lt_of_le ha0 with ha0' | ha0'
    · have : r = b := by
        rw [hr, ← ha0']
        simpa using Real.sqrt_sq hb0
      rw [this, ← ha0']
      simp
    rcases eq_or_lt_of_le hb0 with hb0' | hb0'
    · have : r = a := by
        rw [hr, ← hb0']
        simpa using Real.sqrt_sq ha0
      rw [this, ← hb0']
      simp
    have hrpos : 0 < r := lt_of_lt_of_le ha0' har
    have hamem : a ∈ Set.Ioo (0 : ℝ) (π / 2) := ⟨ha0', lt_of_le_of_lt har hcase⟩
    have hbmem : b ∈ Set.Ioo (0 : ℝ) (π / 2) := ⟨hb0', lt_of_le_of_lt hbr hcase⟩
    have hrmem : r ∈ Set.Ioo (0 : ℝ) (π / 2) := ⟨hrpos, hcase⟩
    have hqa : logCosQuot a ≤ logCosQuot r :=
      logCosQuot_monotoneOn hamem hrmem har
    have hqb : logCosQuot b ≤ logCosQuot r :=
      logCosQuot_monotoneOn hbmem hrmem hbr
    have hexa : -Real.log (Real.cos a) = a ^ 2 * logCosQuot a := by
      simp only [logCosQuot]
      field_simp
    have hexb : -Real.log (Real.cos b) = b ^ 2 * logCosQuot b := by
      simp only [logCosQuot]
      field_simp
    have hexr : -Real.log (Real.cos r) = r ^ 2 * logCosQuot r := by
      simp only [logCosQuot]
      field_simp
    have hkey : a ^ 2 * logCosQuot r + b ^ 2 * logCosQuot r = r ^ 2 * logCosQuot r := by
      rw [← add_mul, ← hrsq]
    have hlog : Real.log (Real.cos r) ≤ Real.log (Real.cos a) + Real.log (Real.cos b) := by
      have h1 := mul_le_mul_of_nonneg_left hqa (show (0 : ℝ) ≤ a ^ 2 by positivity)
      have h2 := mul_le_mul_of_nonneg_left hqb (show (0 : ℝ) ≤ b ^ 2 by positivity)
      linarith
    have hcosapos : 0 < Real.cos a := cos_pos_of_nonneg_of_lt_pi_div_two ha0 hamem.2
    have hcosbpos : 0 < Real.cos b := cos_pos_of_nonneg_of_lt_pi_div_two hb0 hbmem.2
    have := Real.log_mul hcosapos.ne' hcosbpos.ne'
    rw [← this] at hlog
    exact (Real.log_le_log_iff hcosr (by positivity)).1 hlog

/-- **The spherical Pythagorean inequality, `arccos` form.** -/
theorem arccos_cos_mul_cos_le_sqrt {a b : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ π / 2)
    (hb0 : 0 ≤ b) (hb : b ≤ π / 2) :
    Real.arccos (Real.cos a * Real.cos b) ≤ Real.sqrt (a ^ 2 + b ^ 2) := by
  have hrnn : 0 ≤ Real.sqrt (a ^ 2 + b ^ 2) := Real.sqrt_nonneg _
  have hrle : Real.sqrt (a ^ 2 + b ^ 2) ≤ π := by
    nlinarith [Real.pi_pos, Real.sq_sqrt (show (0:ℝ) ≤ a ^ 2 + b ^ 2 by positivity)]
  calc Real.arccos (Real.cos a * Real.cos b)
      ≤ Real.arccos (Real.cos (Real.sqrt (a ^ 2 + b ^ 2))) :=
        Real.arccos_le_arccos (cos_sqrt_sq_add_sq_le_cos_mul_cos ha0 ha hb0 hb)
    _ = Real.sqrt (a ^ 2 + b ^ 2) := Real.arccos_cos hrnn hrle

/-- **The Pythagorean angle inequality.**  Any angle `ω ∈ [0, π]` obeying the
spherical right-triangle identity `cos ω = cos a * cos b`, with `a` and `b` in
the first quadrant, satisfies `ω ^ 2 ≤ a ^ 2 + b ^ 2`.  This is an exact
inequality, not a small-angle approximation. -/
theorem sq_le_sq_add_sq_of_cos_eq_cos_mul_cos {ω a b : ℝ} (hω0 : 0 ≤ ω)
    (hωπ : ω ≤ π) (ha0 : 0 ≤ a) (ha : a ≤ π / 2) (hb0 : 0 ≤ b) (hb : b ≤ π / 2)
    (hcos : Real.cos ω = Real.cos a * Real.cos b) : ω ^ 2 ≤ a ^ 2 + b ^ 2 := by
  have hle : ω ≤ Real.sqrt (a ^ 2 + b ^ 2) := by
    rw [← Real.arccos_cos hω0 hωπ, hcos]
    exact arccos_cos_mul_cos_le_sqrt ha0 ha hb0 hb
  have hsq : Real.sqrt (a ^ 2 + b ^ 2) ^ 2 = a ^ 2 + b ^ 2 :=
    Real.sq_sqrt (by positivity)
  nlinarith [Real.sqrt_nonneg (a ^ 2 + b ^ 2)]

/-! ### The exact identity in an inner product space -/

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- For `e` in `K`, the inner product with `f` only sees the projection of `f`.
Taking norms, this is `cos ω = cos η * cos ψ` before any `arccos` appears. -/
theorem norm_inner_eq_norm_starProjection_mul (K : Submodule 𝕜 E)
    [K.HasOrthogonalProjection] {e f : E} (he : e ∈ K)
    (hPf : K.starProjection f ≠ 0) :
    ‖(inner 𝕜 e f)‖ =
      ‖K.starProjection f‖ *
        ‖(inner 𝕜 e (((‖K.starProjection f‖ : ℝ) : 𝕜)⁻¹ • K.starProjection f))‖ := by
  have hnpos : 0 < ‖K.starProjection f‖ := norm_pos_iff.2 hPf
  have hproj : (inner 𝕜 e f) = inner 𝕜 e (K.starProjection f) := by
    have := Submodule.inner_starProjection_left_eq_right K e f
    rwa [Submodule.starProjection_eq_self_iff.mpr he] at this
  rw [inner_smul_right, norm_mul, hproj]
  simp only [RCLike.norm_ofReal, norm_inv, abs_of_pos hnpos]
  field_simp

/-- **The spherical right-triangle identity.**  With `ω` the line angle between
the unit vectors `e ∈ K` and `f`, `η` the angle between `f` and `K`, and `ψ` the
angle inside `K` between `e` and the normalized projection of `f`,
`cos ω = cos η * cos ψ`.  Exact; no approximation. -/
theorem cos_lineAngle_eq_mul (K : Submodule 𝕜 E) [K.HasOrthogonalProjection]
    {e f : E} (he : e ∈ K) (hef : ‖e‖ = 1) (hf : ‖f‖ = 1)
    (hPf : K.starProjection f ≠ 0) :
    Real.cos (Real.arccos ‖(inner 𝕜 e f)‖) =
      Real.cos (Real.arccos ‖K.starProjection f‖) *
        Real.cos (Real.arccos
          ‖(inner 𝕜 e (((‖K.starProjection f‖ : ℝ) : 𝕜)⁻¹ • K.starProjection f))‖) := by
  have hnpos : 0 < ‖K.starProjection f‖ := norm_pos_iff.2 hPf
  have hgnorm : ‖((‖K.starProjection f‖ : ℝ) : 𝕜)⁻¹ • K.starProjection f‖ = 1 := by
    rw [norm_smul]
    simp [hnpos.ne']
  have hef1 : ‖(inner 𝕜 e f)‖ ≤ 1 := by
    have := norm_inner_le_norm (𝕜 := 𝕜) e f
    rwa [hef, hf, one_mul] at this
  have hP1 : ‖K.starProjection f‖ ≤ 1 := by
    have := K.norm_starProjection_apply_le f
    rwa [hf] at this
  have hg1 : ‖(inner 𝕜 e (((‖K.starProjection f‖ : ℝ) : 𝕜)⁻¹ • K.starProjection f))‖ ≤ 1 := by
    have := norm_inner_le_norm (𝕜 := 𝕜) e
      (((‖K.starProjection f‖ : ℝ) : 𝕜)⁻¹ • K.starProjection f)
    rwa [hef, hgnorm, one_mul] at this
  rw [Real.cos_arccos (by linarith [norm_nonneg (inner 𝕜 e f)]) hef1,
    Real.cos_arccos (by linarith [norm_nonneg (K.starProjection f)]) hP1,
    Real.cos_arccos (by
      linarith [norm_nonneg
        (inner 𝕜 e (((‖K.starProjection f‖ : ℝ) : 𝕜)⁻¹ • K.starProjection f))]) hg1]
  exact norm_inner_eq_norm_starProjection_mul K he hPf

/-- **The Pythagorean angle bound in an inner product space.**  The squared line
angle between `e` and `f` is at most the squared out-of-plane angle plus the
squared in-plane angle.  Exact on the whole first quadrant. -/
theorem sq_lineAngle_le_sq_add_sq (K : Submodule 𝕜 E) [K.HasOrthogonalProjection]
    {e f : E} (he : e ∈ K) (hef : ‖e‖ = 1) (hf : ‖f‖ = 1)
    (hPf : K.starProjection f ≠ 0) :
    Real.arccos ‖(inner 𝕜 e f)‖ ^ 2 ≤
      Real.arccos ‖K.starProjection f‖ ^ 2 +
        Real.arccos
          ‖(inner 𝕜 e (((‖K.starProjection f‖ : ℝ) : 𝕜)⁻¹ • K.starProjection f))‖ ^ 2 := by
  refine sq_le_sq_add_sq_of_cos_eq_cos_mul_cos (Real.arccos_nonneg _)
    (Real.arccos_le_pi _) (Real.arccos_nonneg _)
    (Real.arccos_le_pi_div_two.2 (norm_nonneg _)) (Real.arccos_nonneg _)
    (Real.arccos_le_pi_div_two.2 (norm_nonneg _)) ?_
  exact cos_lineAngle_eq_mul K he hef hf hPf

end Submodule

end TauCeti
