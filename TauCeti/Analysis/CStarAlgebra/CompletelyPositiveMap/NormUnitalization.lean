/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.CompletelyPositiveMap.Defect
public import TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.RoundProjection
import TauCeti.Algebra.Ring.Idempotent.Basic
import TauCeti.Analysis.Normed.Ring.Basic

/-!
# Compressing a completely positive contraction

This file is the first step of the norm unitalization of a completely positive contraction
`φ : A → M_k` on a unital C⋆-algebra whose unit is almost sent to a projection,
`δ = ‖φ(1) - φ(1)²‖ < 1/4`. The rounding `Q = χ_{[1/2, ∞)}(φ(1))` (`TauCeti.roundProjection`)
is a projection with `‖(1 - Q)φ(1)‖ ≤ 2δ` (`TauCeti.norm_one_sub_roundProjection_mul_le`).

The Kadison–Schwarz inequality `φ(b)φ(b)⋆ ≤ φ(bb⋆) ≤ ‖b‖²φ(1)` gives
`‖(1 - Q)φ(b)‖² ≤ ‖b‖²‖(1 - Q)φ(1)(1 - Q)‖ ≤ 2δ‖b‖²`. So the compression `QφQ` keeps the norm
multiplicativity defects of `φ` up to `2δ‖a‖‖b‖`: closeness of `QφQ` to `φ` alone does not give
this, because compressing creates the cross term `Qφ(a)(1 - Q)·(1 - Q)φ(b)Q`.

## Main declarations

* `CompletelyPositiveMap.norm_mul_map_sq_le`, `CompletelyPositiveMap.norm_map_mul_sq_le`:
  `‖Tφ(b)‖² ≤ ‖b‖²‖Tφ(1)T⋆‖` and `‖φ(b)T‖² ≤ ‖b‖²‖T⋆φ(1)T‖` for every `T`.
* `CompletelyPositiveMap.norm_compress_map_mul_sub_le`,
  `CompletelyPositiveMap.norm_roundProjection_compress_map_mul_sub_le`: the defect estimate for
  `QφQ`.

## References

* N. P. Brown, *Invariant means and finite representation theory of C⋆-algebras*, Mem. Amer.
  Math. Soc. 184 (2006), no. 865; arXiv:math/0304009v2, Lemma 2.7. This file begins the
  operator-norm version of its unitalization.
-/

public section

open scoped CStarAlgebra ComplexOrder

namespace CompletelyPositiveMap

open CStarMatrix TauCeti

variable {n : Type*} [Fintype n]
  {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {φ : A →CP CStarMatrix n n ℂ} (hφ : ∀ a, ‖φ a‖ ≤ ‖a‖)
include hφ

/-- **Cutting a completely positive contraction.** For a completely positive contraction
`φ : A → M_k` on a unital C⋆-algebra and any `T ∈ M_k`, `‖Tφ(b)‖² ≤ ‖b‖²‖Tφ(1)T⋆‖`, from
`φ(b)φ(b)⋆ ≤ φ(bb⋆) ≤ ‖b‖²φ(1)`. -/
theorem norm_mul_map_sq_le (T : CStarMatrix n n ℂ) (b : A) :
    ‖T * φ b‖ ^ 2 ≤ ‖b‖ ^ 2 * ‖T * φ 1 * star T‖ := by
  have hks : φ b * star (φ b) ≤ φ (b * star b) := by
    simpa [φ.map_star] using star_map_mul_map_le_of_norm_map_le hφ (star b)
  have hb : φ (b * star b) ≤ ((‖b‖ ^ 2 : ℝ) : ℂ) • φ 1 := by
    have h := OrderHomClass.mono φ (CStarAlgebra.mul_star_le_algebraMap_norm_sq b)
    rwa [Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul, map_smul] at h
  have hle : T * (φ b * star (φ b)) * star T ≤ ((‖b‖ ^ 2 : ℝ) : ℂ) • (T * φ 1 * star T) := by
    rw [← smul_mul_assoc, ← mul_smul_comm]
    exact star_right_conjugate_le_conjugate (hks.trans hb) T
  have h0 : 0 ≤ T * (φ b * star (φ b)) * star T :=
    star_right_conjugate_nonneg (mul_star_self_nonneg _) T
  calc ‖T * φ b‖ ^ 2 = ‖T * (φ b * star (φ b)) * star T‖ := by
        rw [sq, ← CStarRing.norm_self_mul_star, star_mul, mul_assoc, mul_assoc, mul_assoc]
    _ ≤ ‖((‖b‖ ^ 2 : ℝ) : ℂ) • (T * φ 1 * star T)‖ :=
        CStarAlgebra.norm_le_norm_of_le_of_nonneg hle h0
    _ = ‖b‖ ^ 2 * ‖T * φ 1 * star T‖ := by
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

/-- The mirror of `CompletelyPositiveMap.norm_mul_map_sq_le`: for a completely positive
contraction `φ : A → M_k` on a unital C⋆-algebra and any `T ∈ M_k`,
`‖φ(b)T‖² ≤ ‖b‖²‖T⋆φ(1)T‖`. -/
theorem norm_map_mul_sq_le (T : CStarMatrix n n ℂ) (b : A) :
    ‖φ b * T‖ ^ 2 ≤ ‖b‖ ^ 2 * ‖star T * φ 1 * T‖ := by
  have h := norm_mul_map_sq_le hφ (star T) (star b)
  rwa [φ.map_star, ← norm_star, star_mul, star_star, star_star, norm_star] at h

/-- **Compressing a completely positive contraction by a projection.** Let `φ : A → M_k` be a
completely positive contraction on a unital C⋆-algebra and `Q` a projection with
`‖(1 - Q)φ(1)(1 - Q)‖ ≤ ε`. Then the compression `QφQ` keeps the norm defects of `φ` up to
`ε‖a‖‖b‖`: the cross term `Qφ(a)(1 - Q)·(1 - Q)φ(b)Q` of
`Qφ(ab)Q - Qφ(a)Q·Qφ(b)Q = Q(φ(ab) - φ(a)φ(b))Q + Qφ(a)(1 - Q)·(1 - Q)φ(b)Q` has norm at most
`ε‖a‖‖b‖` by `CompletelyPositiveMap.norm_mul_map_sq_le` and its mirror. -/
theorem norm_compress_map_mul_sub_le [DecidableEq n] {Q : CStarMatrix n n ℂ}
    (hQ : IsStarProjection Q) {ε : ℝ}
    (hε : ‖(1 - Q) * φ 1 * (1 - Q)‖ ≤ ε) (a b : A) :
    ‖Q * φ (a * b) * Q - Q * φ a * Q * (Q * φ b * Q)‖ ≤
      ‖φ (a * b) - φ a * φ b‖ + ε * ‖a‖ * ‖b‖ := by
  have hP : IsSelfAdjoint (1 - Q) := hQ.one_sub.isSelfAdjoint
  have hQn : ‖Q‖ ≤ 1 := hQ.norm_le
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans hε
  have hb := norm_mul_map_sq_le hφ (1 - Q) b
  have ha := norm_map_mul_sq_le hφ (1 - Q) a
  rw [hP.star_eq] at hb ha
  replace hb := hb.trans (mul_le_mul_of_nonneg_left hε (by positivity))
  replace ha := ha.trans (mul_le_mul_of_nonneg_left hε (by positivity))
  have hab : ‖φ a * (1 - Q)‖ * ‖(1 - Q) * φ b‖ ≤ ε * ‖a‖ * ‖b‖ := by
    rw [← pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero]
    calc (‖φ a * (1 - Q)‖ * ‖(1 - Q) * φ b‖) ^ 2 =
          ‖φ a * (1 - Q)‖ ^ 2 * ‖(1 - Q) * φ b‖ ^ 2 := mul_pow _ _ _
      _ ≤ (‖a‖ ^ 2 * ε) * (‖b‖ ^ 2 * ε) := mul_le_mul ha hb (by positivity) (by positivity)
      _ = (ε * ‖a‖ * ‖b‖) ^ 2 := by ring
  rw [hQ.isIdempotentElem.compress_sub_compress_mul_compress]
  refine (norm_add_le _ _).trans (add_le_add (norm_mul_mul_le_of_norm_le_one hQn hQn _) ?_)
  calc ‖Q * φ a * (1 - Q) * ((1 - Q) * φ b * Q)‖
      ≤ ‖Q * φ a * (1 - Q)‖ * ‖(1 - Q) * φ b * Q‖ := norm_mul_le _ _
    _ ≤ ‖φ a * (1 - Q)‖ * ‖(1 - Q) * φ b‖ := by
        rw [mul_assoc Q]
        gcongr
        · exact norm_mul_le_of_norm_le_one_left hQn _
        · exact norm_mul_le_of_norm_le_one_right hQn _
    _ ≤ ε * ‖a‖ * ‖b‖ := hab

/-- **Rounding `φ(1)` to a projection.** For a completely positive contraction `φ : A → M_k` on a
unital C⋆-algebra with `δ = ‖φ(1) - φ(1)²‖ < 1/4`, the rounding `Q = χ_{[1/2, ∞)}(φ(1))` is a
projection with `‖φ(1) - Q‖ ≤ 2δ` (`TauCeti.norm_sub_roundProjection_le`), and the compression
`QφQ` satisfies
`‖Qφ(ab)Q - Qφ(a)Q·Qφ(b)Q‖ ≤ ‖φ(ab) - φ(a)φ(b)‖ + 2δ‖a‖‖b‖`. -/
theorem norm_roundProjection_compress_map_mul_sub_le [DecidableEq n]
    (hδ : ‖φ 1 - φ 1 ^ 2‖ < 1 / 4) (a b : A) :
    ‖roundProjection (φ 1) * φ (a * b) * roundProjection (φ 1) -
        roundProjection (φ 1) * φ a * roundProjection (φ 1) *
          (roundProjection (φ 1) * φ b * roundProjection (φ 1))‖ ≤
      ‖φ (a * b) - φ a * φ b‖ + 2 * ‖φ 1 - φ 1 ^ 2‖ * ‖a‖ * ‖b‖ := by
  have h1 : IsSelfAdjoint (φ 1) := IsSelfAdjoint.of_nonneg (map_nonneg φ zero_le_one)
  have hQ := isStarProjection_roundProjection (φ 1)
  refine norm_compress_map_mul_sub_le hφ hQ ?_ a b
  exact (norm_mul_le_of_norm_le_one_right hQ.one_sub.norm_le _).trans
    (norm_one_sub_roundProjection_mul_le h1 le_rfl hδ)

end CompletelyPositiveMap
