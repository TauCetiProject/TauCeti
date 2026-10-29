/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Module

/-!
# Chord-to-tangent bounds in the plane

The elementary plane geometry behind the Hungerbühler–Wasem connecting-arc analysis: decompose a
vector `w ∈ ℂ` into its projection on a direction `L` and the orthogonal remainder, and bound the
chord from `w` to the "natural" tangent target `(‖w‖/‖L‖) • L` — the point of the ray `ℝ₊ • L` at
the same distance — by the orthogonal deviation:

  `‖w - (‖w‖/‖L‖) • L‖ ≤ ‖tangentDeviation w L‖ + ‖tangentDeviation w L‖² / ‖w‖`.

For a curve flat of order `n` at an on-cycle singularity the deviation is `o(‖w‖ⁿ)`
(`Contour.FlatOfOrder`), so the chord to the tangent target is too — the radius-based bound the
sector analysis of the generalized residue theorem consumes.

## Main definitions

* `Contour.tangentDeviation w L` — the component of `w` perpendicular to the real line `ℝ • L`
  (the remainder after subtracting the private projection on `L`). Its norm is the distance from
  `w` to the line, the quantity `Contour.FlatOfOrder` bounds (`norm_tangentDeviation`).

This is a scalar formula on `ℂ`, deliberately not routed through Mathlib's submodule-valued
`orthogonalProjection`: the contour development needs only the one-line projection onto a known
direction, not the inner-product-space machinery.

## Main results

* `Contour.norm_tangentDeviation` — `‖tangentDeviation w L‖ = |(w * conj L).im| / ‖L‖`, the
  bridge to the inline form used by `Contour.FlatOfOrder`.
* `Contour.tangentDeviation_self`, `Contour.tangentDeviation_real_smul_self` — points of the
  line `ℝ • L` have zero deviation.
* `Contour.tangentDeviation_neg_right`, `Contour.tangentDeviation_real_smul_right` — the
  deviation depends only on the line `ℝ • L`, not on the chosen nonzero direction vector.
* `Contour.im_mul_conj_eq_zero_iff_exists_real_smul` — `Im(L · conj v) = 0` characterizes the
  points of the line `ℝ • v`.
* `Contour.norm_tangentDeviation_le_norm_sub_smul` — the deviation norm is at most the distance
  to any point `r • L` of the line, generalising `Contour.norm_tangentDeviation_le`.
* `Contour.norm_chord_to_tangent_target_le` — the chord-to-tangent-target bound (the Pythagoras
  decomposition and norm-shortfall estimate behind it are private implementation steps).

## Provenance

Migrated from `FlatChordBound.lean` (with the `orthogonalProjectionComplex` and
`tangentDeviation` definitions of `FlatnessConditions.lean`) of the AINTLIB `LeanModularForms`
development. See N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a
generalized Residue Theorem*, arXiv:1808.00997, §3.
-/

public section

noncomputable section

namespace TauCeti.Contour

open Complex

/-- **Projection of `w` on the direction `L`** in the plane: the component of `w` along the real
line `ℝ • L`, namely `(Re(w · conj L) / ‖L‖²) • L` (zero for `L = 0`). Implementation device for
`tangentDeviation`; consumers work with the deviation and `norm_tangentDeviation`. -/
private def orthogonalProjectionComplex (w L : ℂ) : ℂ :=
  ((w * starRingEnd ℂ L).re / Complex.normSq L : ℝ) • L

/-- **Orthogonal deviation of `w` from the direction `L`**: the remainder
`w - orthogonalProjectionComplex w L`, the component of `w` perpendicular to the line `ℝ • L`. -/
def tangentDeviation (w L : ℂ) : ℂ :=
  w - orthogonalProjectionComplex w L

/-- `tangentDeviation` is additive in its vector argument. -/
@[simp]
theorem tangentDeviation_add (a b L : ℂ) :
    tangentDeviation (a + b) L = tangentDeviation a L + tangentDeviation b L := by
  simp only [tangentDeviation, orthogonalProjectionComplex, add_mul, Complex.add_re, add_div,
    add_smul]
  abel

/-- `tangentDeviation` sends the zero vector to `0`. -/
@[simp]
theorem tangentDeviation_zero (L : ℂ) : tangentDeviation 0 L = 0 := by
  simp [tangentDeviation, orthogonalProjectionComplex]

/-- `tangentDeviation` respects subtraction in its vector argument. -/
@[simp]
theorem tangentDeviation_sub (a b L : ℂ) :
    tangentDeviation (a - b) L = tangentDeviation a L - tangentDeviation b L := by
  simp only [tangentDeviation, orthogonalProjectionComplex, sub_mul, Complex.sub_re, sub_div,
    sub_smul]
  abel

/-- `tangentDeviation` negates in its vector argument. -/
@[simp]
theorem tangentDeviation_neg (w L : ℂ) :
    tangentDeviation (-w) L = -tangentDeviation w L := by
  simp only [tangentDeviation, orthogonalProjectionComplex, neg_mul, Complex.neg_re, neg_div,
    neg_smul]
  abel

/-- `tangentDeviation` is homogeneous over real scalars in its vector argument. (Not `@[simp]`:
`simp` normalizes the real smul `c • w` to `↑c * w`, so this left-hand side never fires.) -/
theorem tangentDeviation_real_smul (c : ℝ) (w L : ℂ) :
    tangentDeviation (c • w) L = c • tangentDeviation w L := by
  have hopc : orthogonalProjectionComplex (c • w) L = c • orthogonalProjectionComplex w L := by
    simp only [orthogonalProjectionComplex, smul_smul, smul_mul_assoc, Complex.smul_re,
      smul_eq_mul, mul_div_assoc]
  simp only [tangentDeviation, hopc, smul_sub]

/-- The `simp`-normal companion of `tangentDeviation_real_smul`: `simp` normalizes the real smul
`c • w` to `↑c * w`, so this is the form that fires for `simp`-driven automation. -/
@[simp]
theorem tangentDeviation_ofReal_mul (c : ℝ) (w L : ℂ) :
    tangentDeviation ((c : ℂ) * w) L = (c : ℂ) * tangentDeviation w L := by
  simpa only [Complex.real_smul] using tangentDeviation_real_smul c w L

/-- The norm of the orthogonal deviation is the distance from `w` to the line `ℝ • L`:
`‖tangentDeviation w L‖ = |Im(w · conj L)| / ‖L‖` — the quantity `Contour.FlatOfOrder` bounds. -/
theorem norm_tangentDeviation {L : ℂ} (hL : L ≠ 0) (w : ℂ) :
    ‖tangentDeviation w L‖ = |(w * starRingEnd ℂ L).im| / ‖L‖ := by
  have hN : (Complex.normSq L : ℂ) ≠ 0 := by exact_mod_cast (Complex.normSq_pos.mpr hL).ne'
  have hkey : tangentDeviation w L * starRingEnd ℂ L
      = ((w * starRingEnd ℂ L).im : ℂ) * Complex.I := by
    rw [tangentDeviation, orthogonalProjectionComplex, Complex.real_smul, sub_mul, mul_assoc,
      Complex.mul_conj, Complex.ofReal_div, div_mul_cancel₀ _ hN]
    apply Complex.ext <;> simp
  rw [eq_div_iff (norm_ne_zero_iff.mpr hL), ← RCLike.norm_conj L, ← norm_mul, hkey, norm_mul,
    Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

/-- A direction has no deviation from its own line. -/
@[simp]
theorem tangentDeviation_self (L : ℂ) : tangentDeviation L L = 0 := by
  rcases eq_or_ne L 0 with rfl | hL
  · simp [tangentDeviation, orthogonalProjectionComplex]
  simp [tangentDeviation, orthogonalProjectionComplex, Complex.mul_conj, hL]

/-- Every real multiple of the direction lies on its line, so has no deviation. Not a `simp`
lemma: `simp` already reaches it through `tangentDeviation_ofReal_mul` and
`tangentDeviation_self`. -/
theorem tangentDeviation_real_smul_self (r : ℝ) (L : ℂ) : tangentDeviation (r • L) L = 0 := by
  rw [tangentDeviation_real_smul, tangentDeviation_self, smul_zero]

/-- The deviation depends only on the line `ℝ • L`, not on the orientation of `L`: measuring
against `-L` gives the same perpendicular component. -/
@[simp]
theorem tangentDeviation_neg_right (w L : ℂ) : tangentDeviation w (-L) = tangentDeviation w L := by
  simp only [tangentDeviation, orthogonalProjectionComplex, map_neg, mul_neg, Complex.neg_re,
    Complex.normSq_neg, neg_div, neg_smul, smul_neg, neg_neg]

/-- The deviation depends only on the line `ℝ • L`: rescaling the direction by a nonzero real
does not change the perpendicular component. -/
theorem tangentDeviation_real_smul_right {c : ℝ} (hc : c ≠ 0) (w L : ℂ) :
    tangentDeviation w (c • L) = tangentDeviation w L := by
  rw [tangentDeviation, tangentDeviation, orthogonalProjectionComplex,
    orthogonalProjectionComplex, smul_smul]
  rcases eq_or_ne L 0 with rfl | hL
  · simp
  have hN := (Complex.normSq_pos.mpr hL).ne'
  congr 2
  simp only [Complex.real_smul, map_mul, Complex.conj_ofReal, Complex.normSq_ofReal,
    mul_left_comm w, Complex.re_ofReal_mul]
  field_simp

/-- A complex number has real pairing against a nonzero direction exactly when it lies on the
direction's real line: `Im(L · conj v) = 0 ↔ L = c • v` for some real `c`. -/
theorem im_mul_conj_eq_zero_iff_exists_real_smul {L v : ℂ} (hv : v ≠ 0) :
    (L * starRingEnd ℂ v).im = 0 ↔ ∃ c : ℝ, L = c • v := by
  refine ⟨fun h => ⟨(L * starRingEnd ℂ v).re / Complex.normSq v, ?_⟩, ?_⟩
  · have hLv : L * starRingEnd ℂ v = ((L * starRingEnd ℂ v).re : ℂ) :=
      Complex.ext (by simp) (by simpa using h)
    have hv' : starRingEnd ℂ v ≠ 0 := by simpa using hv
    rw [Complex.real_smul, Complex.ofReal_div, ← hLv, ← Complex.mul_conj]
    field_simp
  · rintro ⟨c, rfl⟩
    simp [Complex.real_smul, mul_assoc, Complex.mul_conj]

/-- **Pythagoras for the plane projection.** The squared norm of `w` decomposes into the squared
norms of its projection on `L` and its orthogonal deviation. -/
private theorem proj_sq_add_dev_sq (w L : ℂ) :
    ‖orthogonalProjectionComplex w L‖ ^ 2 + ‖tangentDeviation w L‖ ^ 2 = ‖w‖ ^ 2 := by
  rcases eq_or_ne L 0 with rfl | hL
  · simp [orthogonalProjectionComplex, tangentDeviation]
  have hN := (Complex.normSq_pos.mpr hL).ne'
  simp only [tangentDeviation, orthogonalProjectionComplex, Complex.sq_norm, Complex.real_smul,
    Complex.normSq_sub, map_mul, Complex.normSq_ofReal, Complex.conj_ofReal, mul_left_comm w,
    Complex.re_ofReal_mul]
  field_simp
  ring

/-- The projection on `L` is no longer than the vector. -/
private theorem norm_orthogonalProjectionComplex_le (w L : ℂ) :
    ‖orthogonalProjectionComplex w L‖ ≤ ‖w‖ :=
  (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1
    (by nlinarith [proj_sq_add_dev_sq w L, sq_nonneg ‖tangentDeviation w L‖])

/-- The deviation norm is bounded by the vector norm: the perpendicular component is no longer
than the vector. At `L = 0` the deviation is `w` itself and the bound is an equality. -/
theorem norm_tangentDeviation_le (w L : ℂ) :
    ‖tangentDeviation w L‖ ≤ ‖w‖ :=
  (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1
    (by nlinarith [proj_sq_add_dev_sq w L, sq_nonneg ‖orthogonalProjectionComplex w L‖])

/-- **The deviation norm is at most the distance to any point of the line.** The perpendicular
component of `w` is bounded by `‖w - r • L‖` for every real `r`. At `L = 0` both sides are `‖w‖`,
and at `r = 0` this is `norm_tangentDeviation_le`. -/
theorem norm_tangentDeviation_le_norm_sub_smul (w L : ℂ) (r : ℝ) :
    ‖tangentDeviation w L‖ ≤ ‖w - r • L‖ := by
  calc ‖tangentDeviation w L‖ = ‖tangentDeviation (w - r • L) L‖ := by
        rw [tangentDeviation_sub, tangentDeviation_real_smul_self, sub_zero]
    _ ≤ ‖w - r • L‖ := norm_tangentDeviation_le _ _

/-- **Norm shortfall of the projection.** The projection is shorter than `w` by at most
`‖tangentDeviation w L‖² / ‖w‖`. -/
private theorem norm_sub_norm_orthogonalProjectionComplex_le (w L : ℂ) :
    ‖w‖ - ‖orthogonalProjectionComplex w L‖ ≤ ‖tangentDeviation w L‖ ^ 2 / ‖w‖ := by
  rcases (norm_nonneg w).eq_or_lt with hw | hw
  · simp [← hw]
  rw [le_div_iff₀ hw]
  nlinarith [proj_sq_add_dev_sq w L, mul_nonneg (norm_nonneg (orthogonalProjectionComplex w L))
    (sub_nonneg.2 (norm_orthogonalProjectionComplex_le w L))]

/-- **Chord-to-tangent-target bound.** For `w` in the closed `+L` half-plane, the chord from `w` to
the natural tangent target `(‖w‖/‖L‖) • L` is controlled by the orthogonal deviation:
`‖w - (‖w‖/‖L‖) • L‖ ≤ ‖tangentDeviation w L‖ + ‖tangentDeviation w L‖² / ‖w‖`. -/
theorem norm_chord_to_tangent_target_le {w L : ℂ} (h_pos : 0 ≤ (w * starRingEnd ℂ L).re) :
    ‖w - (‖w‖ / ‖L‖ : ℝ) • L‖ ≤
      ‖tangentDeviation w L‖ + ‖tangentDeviation w L‖ ^ 2 / ‖w‖ := by
  set c := (w * starRingEnd ℂ L).re / Complex.normSq L
  have hP : orthogonalProjectionComplex w L = c • L := rfl
  -- The projection `c • L` lies on the `+L` ray, so its distance to the target is the norm
  -- shortfall.
  have h_target : ‖(c - ‖w‖ / ‖L‖) • L‖ ≤ ‖w‖ - ‖orthogonalProjectionComplex w L‖ := by
    rcases eq_or_ne L 0 with rfl | hL
    · simp [norm_orthogonalProjectionComplex_le]
    have hc : 0 ≤ c := div_nonneg h_pos (Complex.normSq_nonneg L)
    have hPn : ‖orthogonalProjectionComplex w L‖ = c * ‖L‖ := by
      rw [hP, norm_smul, Real.norm_of_nonneg hc]
    have hcw : c ≤ ‖w‖ / ‖L‖ := by
      rw [le_div_iff₀ (norm_pos_iff.2 hL), ← hPn]
      exact norm_orthogonalProjectionComplex_le w L
    rw [norm_smul, Real.norm_of_nonpos (sub_nonpos.2 hcw), hPn, neg_sub, sub_mul,
      div_mul_cancel₀ _ (norm_ne_zero_iff.2 hL)]
  calc ‖w - (‖w‖ / ‖L‖ : ℝ) • L‖ = ‖(c - ‖w‖ / ‖L‖) • L + tangentDeviation w L‖ := by
        rw [tangentDeviation, hP]; congr 1; module
    _ ≤ ‖(c - ‖w‖ / ‖L‖) • L‖ + ‖tangentDeviation w L‖ := norm_add_le _ _
    _ ≤ _ := by linarith [norm_sub_norm_orthogonalProjectionComplex_le w L]

end TauCeti.Contour

end
