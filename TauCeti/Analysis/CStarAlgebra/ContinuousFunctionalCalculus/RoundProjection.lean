/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
public import TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Projection
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import TauCeti.Analysis.Normed.Ring.Basic
import TauCeti.Topology.Algebra.Indicator

/-!
# Rounding an almost-projection

The rounding `Q = χ_{[1/2, ∞)}(h)` of an element `h` of a C⋆-algebra (`TauCeti.roundProjection`)
is a star projection commuting with `h`. If `‖h - h²‖ ≤ δ`, every point `t` of the real spectrum
of `h` has `|t - t²| ≤ δ`, so `t` lies within `2δ` of `0` (when `t < 1/2`) or of `1` (when
`t ≥ 1/2`). For `δ < 1/4` the spectrum therefore avoids `1/2`, the indicator of `[1/2, ∞)` is
continuous on it, and for self-adjoint `h` we get `‖h - Q‖ ≤ 2δ` and `‖(1 - Q)h‖ ≤ 2δ`.
The bound `δ < 1/4` is sharp: for `h = id` in `C([0, 1], ℂ)`, `‖h - h²‖ = 1/4` and the rounding is
the junk value `0`.

## Main declarations

* `TauCeti.roundProjection`, `TauCeti.isStarProjection_roundProjection`,
  `TauCeti.commute_roundProjection`: the rounding.
* `TauCeti.lt_and_abs_le_or_le_and_abs_one_sub_le_of_mem_spectrum`: the spectral dichotomy.
* `TauCeti.continuousOn_roundProjection_indicator`: the indicator of `[1/2, ∞)` is continuous on
  the spectrum of an almost-projection.
* `TauCeti.norm_sub_roundProjection_le`, `TauCeti.norm_one_sub_roundProjection_mul_le`:
  `‖h - Q‖ ≤ 2δ` and `‖(1 - Q)h‖ ≤ 2δ`.

## References

* N. P. Brown, *Invariant means and finite representation theory of C⋆-algebras*, Mem. Amer.
  Math. Soc. 184 (2006), no. 865; arXiv:math/0304009v2, Lemma 2.7. The rounding is the
  spectral-projection step of the operator-norm version of its unitalization.
-/

public section

open scoped CStarAlgebra

namespace TauCeti

private theorem lt_and_abs_le_or_le_and_abs_one_sub_le {t δ : ℝ} (ht : |t - t ^ 2| ≤ δ) :
    (t < 1 / 2 ∧ |t| ≤ 2 * δ) ∨ (1 / 2 ≤ t ∧ |1 - t| ≤ 2 * δ) := by
  rw [abs_le] at ht
  rcases lt_or_ge t (1 / 2) with h | h
  · refine .inl ⟨h, abs_le.mpr ⟨?_, ?_⟩⟩ <;> nlinarith
  · refine .inr ⟨h, abs_le.mpr ⟨?_, ?_⟩⟩ <;> nlinarith

section Banach

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [HasSummableGeomSeries A] {h : A} {δ : ℝ}

/-- **Spectrum of an almost-projection.** If `‖h - h²‖ ≤ δ`, every point `t` of the real spectrum
of `h` lies within `2δ` of `0`, if `t < 1/2`, or of `1`, if `t ≥ 1/2`. -/
theorem lt_and_abs_le_or_le_and_abs_one_sub_le_of_mem_spectrum (hδ : ‖h - h ^ 2‖ ≤ δ) {t : ℝ}
    (ht : t ∈ spectrum ℝ h) :
    (t < 1 / 2 ∧ |t| ≤ 2 * δ) ∨ (1 / 2 ≤ t ∧ |1 - t| ≤ 2 * δ) := by
  refine lt_and_abs_le_or_le_and_abs_one_sub_le (le_trans ?_ hδ)
  have hp := spectrum.subset_polynomial_aeval h (Polynomial.X - Polynomial.X ^ 2) ⟨t, ht, rfl⟩
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_pow, map_sub,
    Polynomial.aeval_X, map_pow] at hp
  exact quasispectrum.norm_le_norm_of_mem (spectrum_subset_quasispectrum ℝ _ hp)

/-- If `‖h - h²‖ ≤ δ < 1/4`, the spectrum of `h` avoids `1/2`, so the indicator of `[1/2, ∞)`
defining `TauCeti.roundProjection h` is continuous on it. -/
theorem continuousOn_roundProjection_indicator (hδ : ‖h - h ^ 2‖ ≤ δ) (hδ4 : δ < 1 / 4) :
    ContinuousOn ((Set.Ici (1 / 2 : ℝ)).indicator (1 : ℝ → ℝ)) (spectrum ℝ h) := by
  refine continuousOn_const.continuousOn_indicator_of_disjoint_frontier ?_
  rw [frontier_Ici, Set.disjoint_singleton_left]
  intro ht
  rcases lt_and_abs_le_or_le_and_abs_one_sub_le_of_mem_spectrum hδ ht with ⟨h1, -⟩ | ⟨-, h2⟩
  · exact h1.false
  · rw [abs_le] at h2
    linarith

end Banach

section CStarAlgebra

variable {A : Type*} [CStarAlgebra A]

/-- The **rounding** of `h` to a projection: the spectral projection `χ_{[1/2, ∞)}(h)`. For a
self-adjoint `h` with `‖h - h²‖ ≤ δ < 1/4` it is a star projection within `2δ` of `h`
(`TauCeti.norm_sub_roundProjection_le`). -/
noncomputable def roundProjection (h : A) : A :=
  cfc ((Set.Ici (1 / 2 : ℝ)).indicator (1 : ℝ → ℝ)) h

/-- Unfolding lemma for `roundProjection`. -/
theorem roundProjection_def (h : A) :
    roundProjection h = cfc ((Set.Ici (1 / 2 : ℝ)).indicator (1 : ℝ → ℝ)) h :=
  (rfl)

/-- The rounding of `h` is a star projection. -/
theorem isStarProjection_roundProjection (h : A) : IsStarProjection (roundProjection h) :=
  isStarProjection_cfc_indicator h _

/-- The rounding of `h` commutes with `h`. -/
theorem commute_roundProjection (h : A) : Commute (roundProjection h) h :=
  Commute.cfc_real (Commute.refl h) _

variable {h : A} {δ : ℝ}

/-- **Rounding an almost-projection.** If `h` is self-adjoint with `‖h - h²‖ ≤ δ < 1/4`, then its
rounding `χ_{[1/2, ∞)}(h)` is within `2δ` of `h`. -/
theorem norm_sub_roundProjection_le (hh : IsSelfAdjoint h) (hδ : ‖h - h ^ 2‖ ≤ δ)
    (hδ4 : δ < 1 / 4) : ‖h - roundProjection h‖ ≤ 2 * δ := by
  have hc := continuousOn_roundProjection_indicator hδ hδ4
  have h0 : 0 ≤ δ := (norm_nonneg _).trans hδ
  have he : cfc (fun t : ℝ ↦ t - (Set.Ici (1 / 2 : ℝ)).indicator (1 : ℝ → ℝ) t) h =
      h - roundProjection h := by
    rw [cfc_sub (fun t : ℝ ↦ t) _ h (hg := hc), cfc_id' ℝ h, roundProjection_def]
  rw [← he]
  refine norm_cfc_le (by positivity) fun t ht ↦ ?_
  rcases lt_and_abs_le_or_le_and_abs_one_sub_le_of_mem_spectrum hδ ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rwa [Set.indicator_of_notMem (by simpa using h1), sub_zero, Real.norm_eq_abs]
  · rwa [Set.indicator_of_mem (by simpa using h1), Pi.one_apply, Real.norm_eq_abs, abs_sub_comm]

/-- If `h` is self-adjoint with `‖h - h²‖ ≤ δ < 1/4`, then `h` is within `2δ` of `0` off its
rounding: `‖(1 - χ_{[1/2, ∞)}(h)) h‖ ≤ 2δ`. -/
theorem norm_one_sub_roundProjection_mul_le (hh : IsSelfAdjoint h) (hδ : ‖h - h ^ 2‖ ≤ δ)
    (hδ4 : δ < 1 / 4) : ‖(1 - roundProjection h) * h‖ ≤ 2 * δ := by
  have hQ := isStarProjection_roundProjection h
  have he : (1 - roundProjection h) * h = (1 - roundProjection h) * (h - roundProjection h) := by
    simp [mul_sub, sub_mul, hQ.isIdempotentElem.eq]
  rw [he]
  exact (norm_mul_le_of_norm_le_one_left hQ.one_sub.norm_le _).trans
    (norm_sub_roundProjection_le hh hδ hδ4)

end CStarAlgebra

end TauCeti
