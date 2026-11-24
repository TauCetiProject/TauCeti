/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
public import TauCeti.Analysis.CStarAlgebra.CompletelyPositiveMap.Defect
public import TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Projection

/-!
# Rounding an almost-projection, and compressing a completely positive contraction

This file is the first step of the norm unitalization of a completely positive contraction
`φ : A → M_k` on a unital C⋆-algebra whose unit is almost sent to a projection,
`δ = ‖φ(1) - φ(1)²‖ ≤ 1/8`.

The rounding `Q = χ_{[1/2, ∞)}(h)` of a self-adjoint `h` (`TauCeti.roundProjection`) is a star
projection. If `‖h - h²‖ ≤ δ ≤ 1/8`, every point `t` of the spectrum of `h` has `|t - t²| ≤ δ`, so
`t` lies within `2δ` of `0` or of `1`; hence `‖h - Q‖ ≤ 2δ` and `‖(1 - Q)h‖ ≤ 2δ`. The indicator of
`[1/2, ∞)` is continuous on such a spectrum, which avoids `(1/4, 3/4)`.

Applied to `h = φ(1)`, the Kadison–Schwarz inequality `φ(b)φ(b)⋆ ≤ φ(bb⋆) ≤ ‖b‖²φ(1)` gives
`‖(1 - Q)φ(b)‖² ≤ ‖b‖²‖(1 - Q)φ(1)(1 - Q)‖ ≤ 2δ‖b‖²`. So the compression `QφQ` keeps the norm
multiplicativity defects of `φ` up to `2δ‖a‖‖b‖`: closeness of `QφQ` to `φ` alone does not give
this, because compressing creates the cross term `Qφ(a)(1 - Q)·(1 - Q)φ(b)Q`.

## Main declarations

* `TauCeti.roundProjection`, `TauCeti.isStarProjection_roundProjection`: the rounding.
* `TauCeti.norm_sub_roundProjection_le`, `TauCeti.norm_one_sub_roundProjection_mul_le`:
  `‖h - Q‖ ≤ 2δ` and `‖(1 - Q)h‖ ≤ 2δ`.
* `TauCeti.norm_mul_map_sq_le`: `‖Pφ(b)‖² ≤ ‖b‖²‖Pφ(1)P‖` for self-adjoint `P`.
* `TauCeti.norm_compress_map_mul_sub_le`,
  `TauCeti.norm_roundProjection_compress_map_mul_sub_le`: the defect estimate for `QφQ`.
-/

public section

open scoped CStarAlgebra ComplexOrder

namespace TauCeti

section RoundProjection

variable {A : Type*} [CStarAlgebra A]

/-- The **rounding** of `h` to a projection: the spectral projection `χ_{[1/2, ∞)}(h)`. For a
self-adjoint `h` with `‖h - h²‖ ≤ δ ≤ 1/8` it is a star projection within `2δ` of `h`
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

private theorem abs_le_of_abs_sub_sq_le {t δ : ℝ} (hδ : δ ≤ 1 / 8) (ht : |t - t ^ 2| ≤ δ) :
    (t < 1 / 2 ∧ |t| ≤ 2 * δ) ∨ (1 / 2 ≤ t ∧ |1 - t| ≤ 2 * δ) := by
  rw [abs_le] at ht
  rcases lt_or_ge t (1 / 2) with h | h
  · refine .inl ⟨h, abs_le.mpr ⟨?_, ?_⟩⟩ <;> nlinarith
  · refine .inr ⟨h, abs_le.mpr ⟨?_, ?_⟩⟩ <;> nlinarith

variable {h : A} {δ : ℝ}

private theorem spectrum_dichotomy (hh : IsSelfAdjoint h) (hδ : ‖h - h ^ 2‖ ≤ δ)
    (hδ8 : δ ≤ 1 / 8) {t : ℝ} (ht : t ∈ spectrum ℝ h) :
    (t < 1 / 2 ∧ |t| ≤ 2 * δ) ∨ (1 / 2 ≤ t ∧ |1 - t| ≤ 2 * δ) := by
  refine abs_le_of_abs_sub_sq_le hδ8 ?_
  have h1 := norm_apply_le_norm_cfc (fun t : ℝ ↦ t - t ^ 2) h ht
  rw [cfc_sub (fun t : ℝ ↦ t) (fun t : ℝ ↦ t ^ 2) h, cfc_id' ℝ h, cfc_pow_id h 2] at h1
  exact h1.trans hδ

private theorem continuousOn_indicator (hh : IsSelfAdjoint h) (hδ : ‖h - h ^ 2‖ ≤ δ)
    (hδ8 : δ ≤ 1 / 8) :
    ContinuousOn ((Set.Ici (1 / 2 : ℝ)).indicator (1 : ℝ → ℝ)) (spectrum ℝ h) := by
  refine (Continuous.continuousOn (f := fun t : ℝ ↦ max 0 (min 1 (2 * t - 1 / 2)))
    (by fun_prop)).congr fun t ht ↦ ?_
  rcases spectrum_dichotomy hh hδ hδ8 ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [Set.indicator_of_notMem (by simpa using h1)]
    rw [abs_le] at h2
    simp only
    rw [max_eq_left (by rw [min_le_iff]; right; linarith)]
  · rw [Set.indicator_of_mem (by simpa using h1)]
    rw [abs_le] at h2
    simp only [Pi.one_apply]
    rw [min_eq_left (by linarith), max_eq_right zero_le_one]

/-- **Rounding an almost-projection.** If `h` is self-adjoint with `‖h - h²‖ ≤ δ ≤ 1/8`, then its
rounding `χ_{[1/2, ∞)}(h)` is within `2δ` of `h`. -/
theorem norm_sub_roundProjection_le (hh : IsSelfAdjoint h) (hδ : ‖h - h ^ 2‖ ≤ δ)
    (hδ8 : δ ≤ 1 / 8) : ‖h - roundProjection h‖ ≤ 2 * δ := by
  have hc := continuousOn_indicator hh hδ hδ8
  have h0 : 0 ≤ δ := (norm_nonneg _).trans hδ
  have he : cfc (fun t : ℝ ↦ t - (Set.Ici (1 / 2 : ℝ)).indicator (1 : ℝ → ℝ) t) h =
      h - roundProjection h := by
    rw [cfc_sub (fun t : ℝ ↦ t) _ h, cfc_id' ℝ h, roundProjection_def]
  rw [← he]
  refine norm_cfc_le (by positivity) fun t ht ↦ ?_
  rcases spectrum_dichotomy hh hδ hδ8 ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rwa [Set.indicator_of_notMem (by simpa using h1), sub_zero, Real.norm_eq_abs]
  · rwa [Set.indicator_of_mem (by simpa using h1), Pi.one_apply, Real.norm_eq_abs, abs_sub_comm]

/-- If `h` is self-adjoint with `‖h - h²‖ ≤ δ ≤ 1/8`, then `h` is within `2δ` of `0` off its
rounding: `‖(1 - χ_{[1/2, ∞)}(h)) h‖ ≤ 2δ`. -/
theorem norm_one_sub_roundProjection_mul_le (hh : IsSelfAdjoint h) (hδ : ‖h - h ^ 2‖ ≤ δ)
    (hδ8 : δ ≤ 1 / 8) : ‖(1 - roundProjection h) * h‖ ≤ 2 * δ := by
  have hc := continuousOn_indicator hh hδ hδ8
  have h0 : 0 ≤ δ := (norm_nonneg _).trans hδ
  have he : cfc (fun t : ℝ ↦ (1 - (Set.Ici (1 / 2 : ℝ)).indicator (1 : ℝ → ℝ) t) * t) h =
      (1 - roundProjection h) * h := by
    rw [cfc_mul (fun t : ℝ ↦ 1 - (Set.Ici (1 / 2 : ℝ)).indicator (1 : ℝ → ℝ) t) (fun t ↦ t) h,
      cfc_sub (fun _ : ℝ ↦ (1 : ℝ)) _ h, cfc_const_one ℝ h, cfc_id' ℝ h, roundProjection_def]
  rw [← he]
  refine norm_cfc_le (by positivity) fun t ht ↦ ?_
  rcases spectrum_dichotomy hh hδ hδ8 ht with ⟨h1, h2⟩ | ⟨h1, -⟩
  · rwa [Set.indicator_of_notMem (by simpa using h1), sub_zero, one_mul, Real.norm_eq_abs]
  · rw [Set.indicator_of_mem (by simpa using h1), Pi.one_apply, sub_self, zero_mul, norm_zero]
    positivity

end RoundProjection

private theorem compress_mul_sub_eq {R : Type*} [Ring R] {Q : R} (hQ : Q * Q = Q) (x y z : R) :
    Q * x * Q - Q * y * Q * (Q * z * Q) =
      Q * (x - y * z) * Q + Q * y * (1 - Q) * ((1 - Q) * z * Q) := by
  have hQ' (w : R) : Q * (Q * w) = Q * w := by rw [← mul_assoc, hQ]
  simp only [mul_sub, sub_mul, mul_one, one_mul, mul_assoc, hQ']
  abel

section Compression

open CStarMatrix CompletelyPositiveMap

variable {n : Type*} [Fintype n]
  {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {φ : A →CP CStarMatrix n n ℂ} (hφ : ∀ a, ‖φ a‖ ≤ ‖a‖)
include hφ

/-- **Cutting a completely positive contraction by a self-adjoint `P`.** For a completely
positive contraction `φ : A → M_k` on a unital C⋆-algebra and a self-adjoint `P ∈ M_k`,
`‖Pφ(b)‖² ≤ ‖b‖²‖Pφ(1)P‖`, from `φ(b)φ(b)⋆ ≤ φ(bb⋆) ≤ ‖b‖²φ(1)`. -/
theorem norm_mul_map_sq_le {P : CStarMatrix n n ℂ} (hP : IsSelfAdjoint P) (b : A) :
    ‖P * φ b‖ ^ 2 ≤ ‖b‖ ^ 2 * ‖P * φ 1 * P‖ := by
  have hks : φ b * star (φ b) ≤ φ (b * star b) := by
    simpa [φ.map_star] using star_map_mul_map_le_of_norm_map_le hφ (star b)
  have hb : φ (b * star b) ≤ ((‖b‖ ^ 2 : ℝ) : ℂ) • φ 1 := by
    have h := OrderHomClass.mono φ (CStarAlgebra.mul_star_le_algebraMap_norm_sq b)
    rwa [Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul, map_smul] at h
  have hle : P * (φ b * star (φ b)) * P ≤ ((‖b‖ ^ 2 : ℝ) : ℂ) • (P * φ 1 * P) := by
    rw [← smul_mul_assoc, ← mul_smul_comm]
    exact hP.conjugate_le_conjugate (hks.trans hb)
  have h0 : 0 ≤ P * (φ b * star (φ b)) * P := hP.conjugate_nonneg (mul_star_self_nonneg _)
  calc ‖P * φ b‖ ^ 2 = ‖P * (φ b * star (φ b)) * P‖ := by
        rw [sq, ← CStarRing.norm_self_mul_star, star_mul, hP.star_eq, mul_assoc, mul_assoc,
          mul_assoc]
    _ ≤ ‖((‖b‖ ^ 2 : ℝ) : ℂ) • (P * φ 1 * P)‖ := CStarAlgebra.norm_le_norm_of_le_of_nonneg hle h0
    _ = ‖b‖ ^ 2 * ‖P * φ 1 * P‖ := by
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

/-- **Compressing a completely positive contraction by a projection.** Let `φ : A → M_k` be a
completely positive contraction on a unital C⋆-algebra and `Q` a projection with
`‖(1 - Q)φ(1)(1 - Q)‖ ≤ ε`. Then the compression `QφQ` keeps the norm defects of `φ` up to
`ε‖a‖‖b‖`: the cross term `Qφ(a)(1 - Q)·(1 - Q)φ(b)Q` of
`Qφ(ab)Q - Qφ(a)Q·Qφ(b)Q = Q(φ(ab) - φ(a)φ(b))Q + Qφ(a)(1 - Q)·(1 - Q)φ(b)Q` has norm at most
`ε‖a‖‖b‖` by `TauCeti.norm_mul_map_sq_le`. -/
theorem norm_compress_map_mul_sub_le [DecidableEq n] {Q : CStarMatrix n n ℂ}
    (hQ : IsStarProjection Q) {ε : ℝ}
    (hε : ‖(1 - Q) * φ 1 * (1 - Q)‖ ≤ ε) (a b : A) :
    ‖Q * φ (a * b) * Q - Q * φ a * Q * (Q * φ b * Q)‖ ≤
      ‖φ (a * b) - φ a * φ b‖ + ε * ‖a‖ * ‖b‖ := by
  have hP : IsSelfAdjoint (1 - Q) := hQ.one_sub.isSelfAdjoint
  have hQn : ‖Q‖ ≤ 1 := hQ.norm_le
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans hε
  have hb := (norm_mul_map_sq_le hφ hP b).trans (mul_le_mul_of_nonneg_left hε (by positivity))
  have ha := (norm_mul_map_sq_le hφ hP (star a)).trans
    (mul_le_mul_of_nonneg_left hε (by positivity))
  rw [φ.map_star, ← norm_star, star_mul, star_star, hP.star_eq, norm_star] at ha
  have hab : ‖φ a * (1 - Q)‖ * ‖(1 - Q) * φ b‖ ≤ ε * ‖a‖ * ‖b‖ := by
    rw [← pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero]
    calc (‖φ a * (1 - Q)‖ * ‖(1 - Q) * φ b‖) ^ 2 =
          ‖φ a * (1 - Q)‖ ^ 2 * ‖(1 - Q) * φ b‖ ^ 2 := mul_pow _ _ _
      _ ≤ (‖a‖ ^ 2 * ε) * (‖b‖ ^ 2 * ε) := mul_le_mul ha hb (by positivity) (by positivity)
      _ = (ε * ‖a‖ * ‖b‖) ^ 2 := by ring
  rw [compress_mul_sub_eq hQ.isIdempotentElem.eq]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (norm_mul_le _ _).trans ((mul_le_of_le_one_right (norm_nonneg _) hQn).trans ?_)
    exact (norm_mul_le _ _).trans (mul_le_of_le_one_left (norm_nonneg _) hQn)
  · calc ‖Q * φ a * (1 - Q) * ((1 - Q) * φ b * Q)‖
        ≤ ‖Q * φ a * (1 - Q)‖ * ‖(1 - Q) * φ b * Q‖ := norm_mul_le _ _
      _ ≤ ‖φ a * (1 - Q)‖ * ‖(1 - Q) * φ b‖ := by
          gcongr
          · rw [mul_assoc]
            exact (norm_mul_le _ _).trans (mul_le_of_le_one_left (norm_nonneg _) hQn)
          · exact (norm_mul_le _ _).trans (mul_le_of_le_one_right (norm_nonneg _) hQn)
      _ ≤ ε * ‖a‖ * ‖b‖ := hab

/-- **Rounding `φ(1)` to a projection.** For a completely positive contraction `φ : A → M_k` on a
unital C⋆-algebra with `δ = ‖φ(1) - φ(1)²‖ ≤ 1/8`, the rounding `Q = χ_{[1/2, ∞)}(φ(1))` is a
projection with `‖φ(1) - Q‖ ≤ 2δ` (`TauCeti.norm_sub_roundProjection_le`), and the compression
`QφQ` satisfies
`‖Qφ(ab)Q - Qφ(a)Q·Qφ(b)Q‖ ≤ ‖φ(ab) - φ(a)φ(b)‖ + 2δ‖a‖‖b‖`. -/
theorem norm_roundProjection_compress_map_mul_sub_le [DecidableEq n]
    (hδ : ‖φ 1 - φ 1 ^ 2‖ ≤ 1 / 8) (a b : A) :
    ‖roundProjection (φ 1) * φ (a * b) * roundProjection (φ 1) -
        roundProjection (φ 1) * φ a * roundProjection (φ 1) *
          (roundProjection (φ 1) * φ b * roundProjection (φ 1))‖ ≤
      ‖φ (a * b) - φ a * φ b‖ + 2 * ‖φ 1 - φ 1 ^ 2‖ * ‖a‖ * ‖b‖ := by
  have h1 : IsSelfAdjoint (φ 1) := IsSelfAdjoint.of_nonneg (map_nonneg φ zero_le_one)
  have hQ := isStarProjection_roundProjection (φ 1)
  refine norm_compress_map_mul_sub_le hφ hQ ?_ a b
  calc ‖(1 - roundProjection (φ 1)) * φ 1 * (1 - roundProjection (φ 1))‖
      ≤ ‖(1 - roundProjection (φ 1)) * φ 1‖ * ‖1 - roundProjection (φ 1)‖ := norm_mul_le _ _
    _ ≤ 2 * ‖φ 1 - φ 1 ^ 2‖ * 1 := by
        gcongr
        · exact norm_one_sub_roundProjection_mul_le h1 le_rfl hδ
        · exact hQ.one_sub.norm_le
    _ = 2 * ‖φ 1 - φ 1 ^ 2‖ := mul_one _

end Compression

end TauCeti
