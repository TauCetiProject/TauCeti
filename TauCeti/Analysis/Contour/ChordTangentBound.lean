/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
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
* `Contour.norm_chord_to_tangent_target_le` — the chord-to-tangent-target bound (the Pythagoras
  decomposition and square-root estimates behind it are private implementation steps).

## Provenance

Migrated from `FlatChordBound.lean` (with the `orthogonalProjectionComplex` and
`tangentDeviation` definitions of `FlatnessConditions.lean`) of the AINTLIB `LeanModularForms`
development. See K. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a
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

/-- The norm of the orthogonal deviation is the distance from `w` to the line `ℝ • L`:
`‖tangentDeviation w L‖ = |Im(w · conj L)| / ‖L‖` — the quantity `Contour.FlatOfOrder` bounds. -/
theorem norm_tangentDeviation {L : ℂ} (hL : L ≠ 0) (w : ℂ) :
    ‖tangentDeviation w L‖ = |(w * starRingEnd ℂ L).im| / ‖L‖ := by
  have hkey : tangentDeviation w L * starRingEnd ℂ L
      = ((w * starRingEnd ℂ L).im : ℂ) * Complex.I := by
    unfold tangentDeviation orthogonalProjectionComplex
    rw [sub_mul, Complex.real_smul,
      show ((((w * starRingEnd ℂ L).re / Complex.normSq L : ℝ)) : ℂ) * L * starRingEnd ℂ L
        = (((w * starRingEnd ℂ L).re / Complex.normSq L : ℝ) : ℂ) * (L * starRingEnd ℂ L) by
        ring,
      Complex.mul_conj, ← Complex.ofReal_mul,
      div_mul_cancel₀ _ (Complex.normSq_pos.mpr hL).ne']
    apply Complex.ext <;> simp
  have hnorm : ‖tangentDeviation w L‖ * ‖L‖ = |(w * starRingEnd ℂ L).im| := by
    have h := congrArg norm hkey
    rwa [norm_mul, RCLike.norm_conj, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
      Real.norm_eq_abs] at h
  rw [eq_div_iff (norm_ne_zero_iff.mpr hL)]
  exact hnorm

/-- **Pythagoras for the plane projection.** The squared norm of `w` decomposes into the squared
norms of its projection on `L` and its orthogonal deviation. -/
private theorem proj_sq_add_dev_sq (w L : ℂ) :
    ‖orthogonalProjectionComplex w L‖ ^ 2 + ‖tangentDeviation w L‖ ^ 2 = ‖w‖ ^ 2 := by
  rcases eq_or_ne L 0 with rfl | hL
  · simp [orthogonalProjectionComplex, tangentDeviation]
  rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm]
  unfold tangentDeviation orthogonalProjectionComplex
  simp only [Complex.real_smul]
  set u := (w * starRingEnd ℂ L).re with hu
  set N := Complex.normSq L
  have hN_ne : N ≠ 0 := (Complex.normSq_pos.mpr hL).ne'
  have h1 : Complex.normSq ((↑(u / N) : ℂ) * L) = (u / N) ^ 2 * N := by
    rw [Complex.normSq_mul, Complex.normSq_ofReal]
    ring
  have h2 : (w * starRingEnd ℂ ((↑(u / N) : ℂ) * L)).re = (u / N) * u := by
    rw [map_mul, Complex.conj_ofReal,
      show w * ((↑(u / N) : ℂ) * starRingEnd ℂ L) =
        (↑(u / N) : ℂ) * (w * starRingEnd ℂ L) by ring,
      Complex.mul_re]
    simp [hu]
  rw [Complex.normSq_sub, h1, h2]
  field_simp
  ring

/-- **Square-root shortfall bound.** For `0 ≤ δ ≤ ε` with `0 < ε`:
`ε - √(ε² - δ²) ≤ δ²/ε`. -/
private theorem sub_sqrt_le {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 ≤ δ) (hle : δ ≤ ε) :
    ε - Real.sqrt (ε ^ 2 - δ ^ 2) ≤ δ ^ 2 / ε := by
  have h_sqrt_sq : Real.sqrt (ε ^ 2 - δ ^ 2) ^ 2 = ε ^ 2 - δ ^ 2 :=
    Real.sq_sqrt (by nlinarith)
  have h_sqrt_nn : 0 ≤ Real.sqrt (ε ^ 2 - δ ^ 2) := Real.sqrt_nonneg _
  rw [show ε - Real.sqrt (ε ^ 2 - δ ^ 2) =
      δ ^ 2 / (ε + Real.sqrt (ε ^ 2 - δ ^ 2)) by
    field_simp; nlinarith [h_sqrt_sq]]
  exact div_le_div_of_nonneg_left (by positivity) hε (by linarith)

/-- **Norm shortfall of the projection.** For `‖w‖ > 0`, the projection is shorter than `w` by at
most `‖tangentDeviation w L‖² / ‖w‖`. -/
private theorem norm_sub_norm_orthogonalProjectionComplex_le {w : ℂ} (L : ℂ) (hw : 0 < ‖w‖) :
    ‖w‖ - ‖orthogonalProjectionComplex w L‖ ≤ ‖tangentDeviation w L‖ ^ 2 / ‖w‖ := by
  have h_proj_sq : ‖orthogonalProjectionComplex w L‖ ^ 2 =
      ‖w‖ ^ 2 - ‖tangentDeviation w L‖ ^ 2 := by linarith [proj_sq_add_dev_sq w L]
  have h_dev_le : ‖tangentDeviation w L‖ ≤ ‖w‖ := by
    nlinarith [h_proj_sq ▸ sq_nonneg (‖orthogonalProjectionComplex w L‖), sq_nonneg ‖w‖]
  have h_sqrt_eq : Real.sqrt (‖w‖ ^ 2 - ‖tangentDeviation w L‖ ^ 2) =
      ‖orthogonalProjectionComplex w L‖ := by
    rw [← h_proj_sq]; exact Real.sqrt_sq (norm_nonneg _)
  rw [← h_sqrt_eq]
  exact sub_sqrt_le hw (norm_nonneg _) h_dev_le

/-- **Projection-to-target distance in the `+L` hemisphere.** If `Re(w · conj L) ≥ 0`, the
distance from the projection to the same-magnitude target `(‖w‖/‖L‖) • L` on the `+L` ray equals
the norm shortfall `‖w‖ - ‖orthogonalProjectionComplex w L‖`. -/
private theorem norm_orthogonalProjectionComplex_sub_target_eq {w L : ℂ} (hL : L ≠ 0)
    (h_pos : 0 ≤ (w * starRingEnd ℂ L).re) :
    ‖orthogonalProjectionComplex w L - (‖w‖ / ‖L‖ : ℝ) • L‖ =
      ‖w‖ - ‖orthogonalProjectionComplex w L‖ := by
  set c := (w * starRingEnd ℂ L).re / Complex.normSq L
  have hc_nonneg : 0 ≤ c := div_nonneg h_pos (Complex.normSq_pos.mpr hL).le
  have hL_norm_pos : 0 < ‖L‖ := norm_pos_iff.mpr hL
  have h_proj_norm : ‖orthogonalProjectionComplex w L‖ = c * ‖L‖ := by
    -- `change` unfolds the definition with the `set c` abbreviation folded in; a rewrite cannot
    -- target the folded occurrence.
    change ‖(c : ℝ) • L‖ = c * ‖L‖
    rw [norm_smul]
    simp [abs_of_nonneg hc_nonneg]
  have h_proj_le_w : ‖orthogonalProjectionComplex w L‖ ≤ ‖w‖ := by
    have h_sq : ‖orthogonalProjectionComplex w L‖ ^ 2 ≤ ‖w‖ ^ 2 := by
      linarith [proj_sq_add_dev_sq w L, sq_nonneg ‖tangentDeviation w L‖]
    exact (abs_le_of_sq_le_sq' h_sq (norm_nonneg w)).2
  have h_c_le_div : c ≤ ‖w‖ / ‖L‖ := by
    rw [le_div_iff₀ hL_norm_pos, ← h_proj_norm]; exact h_proj_le_w
  -- `change` unfolds `orthogonalProjectionComplex w L` to `(c : ℝ) • L` (the `set c`
  -- abbreviation folded in); a rewrite cannot target the folded occurrence.
  change ‖(c : ℝ) • L - (‖w‖ / ‖L‖ : ℝ) • L‖ = ‖w‖ - ‖orthogonalProjectionComplex w L‖
  rw [show (c : ℝ) • L - (‖w‖ / ‖L‖ : ℝ) • L = (c - ‖w‖ / ‖L‖ : ℝ) • L by module,
    norm_smul, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr h_c_le_div), h_proj_norm]
  field_simp
  ring

/-- **Chord-to-tangent-target bound.** For `w` in the `+L` hemisphere with `‖w‖ > 0`, the chord
from `w` to the natural tangent target `(‖w‖/‖L‖) • L` is controlled by the orthogonal
deviation: `‖w - (‖w‖/‖L‖) • L‖ ≤ ‖tangentDeviation w L‖ + ‖tangentDeviation w L‖² / ‖w‖`. -/
theorem norm_chord_to_tangent_target_le {w L : ℂ} (hL : L ≠ 0) (hw : 0 < ‖w‖)
    (h_pos : 0 ≤ (w * starRingEnd ℂ L).re) :
    ‖w - (‖w‖ / ‖L‖ : ℝ) • L‖ ≤
      ‖tangentDeviation w L‖ + ‖tangentDeviation w L‖ ^ 2 / ‖w‖ := by
  rw [show w - (‖w‖ / ‖L‖ : ℝ) • L =
      (orthogonalProjectionComplex w L - (‖w‖ / ‖L‖ : ℝ) • L) +
        tangentDeviation w L by unfold tangentDeviation; ring]
  refine (norm_add_le _ _).trans ?_
  rw [norm_orthogonalProjectionComplex_sub_target_eq hL h_pos]
  linarith [norm_sub_norm_orthogonalProjectionComplex_le L hw]

end TauCeti.Contour

end
