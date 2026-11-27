/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.CompletelyPositiveMap.Defect
public import TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.RoundProjection
public import TauCeti.Analysis.CStarAlgebra.CompletelyPositiveMap.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import TauCeti.Algebra.Ring.Idempotent.Basic
import TauCeti.Analysis.Normed.Ring.Basic

/-!
# The norm unitalization of a completely positive contraction

This file is the norm unitalization of a completely positive contraction
`φ : A → M_k` on a unital C⋆-algebra whose unit is almost sent to a projection,
`δ = ‖φ(1) - φ(1)²‖ < 1/4`. The rounding `Q = χ_{[1/2, ∞)}(φ(1))` (`TauCeti.roundProjection`)
is a projection with `‖(1 - Q)φ(1)‖ ≤ 2δ` (`TauCeti.norm_one_sub_roundProjection_mul_le`).

The Kadison–Schwarz inequality `φ(b)φ(b)⋆ ≤ φ(bb⋆) ≤ ‖b‖²φ(1)` gives
`‖(1 - Q)φ(b)‖² ≤ ‖b‖²‖(1 - Q)φ(1)(1 - Q)‖ ≤ 2δ‖b‖²`. So the compression `QφQ` keeps the norm
multiplicativity defects of `φ` up to `2δ‖a‖‖b‖`: closeness of `QφQ` to `φ` alone does not give
this, because compressing creates the cross term `Qφ(a)(1 - Q)·(1 - Q)φ(b)Q`.

Renormalizing the compression gives a completely positive map that is unital onto the corner
`Q M_k Q`. With `k = Qφ(1)Q + (1 - Q)`, which is within `2δ` of `1`, and `g = k^{-1/2}`
(`TauCeti.exists_isSelfAdjoint_mul_mul_eq_one`, by the continuous functional calculus for
`t ↦ t^{-1/2}`, which moves points of `[3/4, 5/4]` by at most their distance to `1`), the map
`ψ(a) = gQφ(a)Qg` satisfies `ψ(1) = Q`, is within `5δ‖a‖` of `QφQ`, and keeps the norm defects of
`φ` up to `17δ‖a‖‖b‖` when `δ ≤ 1/8` (`CompletelyPositiveMap.exists_unital_compress`). Since
`‖φ(1) - Q‖ ≤ 2δ`, `Q` is nonzero as soon as `‖φ(1)‖ > 2δ`
(`TauCeti.roundProjection_ne_zero`).

## Main declarations

* `CompletelyPositiveMap.norm_mul_map_sq_le`, `CompletelyPositiveMap.norm_map_mul_sq_le`:
  `‖Tφ(b)‖² ≤ ‖b‖²‖Tφ(1)T⋆‖` and `‖φ(b)T‖² ≤ ‖b‖²‖T⋆φ(1)T‖` for every `T`.
* `CompletelyPositiveMap.norm_compress_map_mul_sub_le`,
  `CompletelyPositiveMap.norm_roundProjection_compress_map_mul_sub_le`: the defect estimate for
  `QφQ`.
* `TauCeti.exists_isSelfAdjoint_mul_mul_eq_one`,
  `IsStarProjection.exists_isSelfAdjoint_mul_compress_mul_eq`: the renormalizing element `g`.
* `CompletelyPositiveMap.norm_map_mul_sub_le_of_norm_sub_compress_le`: a contraction close to
  `QφQ` keeps the norm defects of `φ`.
* `CompletelyPositiveMap.exists_unital_compress`: the norm unitalization, with `ψ(1) = Q`, the
  `5δ` closeness and the `17δ` product estimate.

## References

* N. P. Brown, *Invariant means and finite representation theory of C⋆-algebras*, Mem. Amer.
  Math. Soc. 184 (2006), no. 865; arXiv:math/0304009v2, Lemma 2.7. This file is the
  operator-norm version of its unitalization.
-/

public section

open scoped CStarAlgebra ComplexOrder

namespace TauCeti

/-- On `[3/4, 5/4]`, `t ↦ t^{-1/2}` moves a point by at most its distance to `1`. -/
private theorem abs_inv_sqrt_sub_one_le {t : ℝ} (ht : |t - 1| ≤ 1 / 4) :
    |(√t)⁻¹ - 1| ≤ |t - 1| := by
  have ht' : 3 / 4 ≤ t := by linarith [abs_le.mp ht]
  have hs : 7 / 10 ≤ √t := Real.le_sqrt_of_sq_le (by linarith)
  have hsq : √t ^ 2 = t := Real.sq_sqrt (by linarith)
  have key : (√t)⁻¹ - 1 = -(t - 1) / (√t * (1 + √t)) := by
    field_simp
    nlinarith
  rw [key, abs_div, abs_neg, abs_of_pos (by positivity : 0 < √t * (1 + √t))]
  exact div_le_self (abs_nonneg _) (by nlinarith)

variable {B : Type*} [CStarAlgebra B]

/-- The spectrum of a self-adjoint `k` lies within `‖k - 1‖` of `1`. -/
private theorem abs_sub_one_le_of_mem_spectrum {k : B} (hk : IsSelfAdjoint k) {t : ℝ}
    (ht : t ∈ spectrum ℝ k) : |t - 1| ≤ ‖k - 1‖ := by
  have he : cfc (fun s : ℝ ↦ s - 1) k = k - 1 := by
    rw [cfc_sub (fun s : ℝ ↦ s) _ k, cfc_id' ℝ k, cfc_const_one ℝ k]
  rw [← he, ← Real.norm_eq_abs]
  exact (norm_cfc_le_iff (fun s : ℝ ↦ s - 1) k (norm_nonneg _)).mp le_rfl t ht

/-- **Renormalizing an element close to `1`.** A self-adjoint `k` with `‖k - 1‖ ≤ ε ≤ 1/4` has
a self-adjoint `g = k^{-1/2}` with `gkg = 1` and `‖g - 1‖ ≤ ε`, commuting with everything that
commutes with `k`. -/
theorem exists_isSelfAdjoint_mul_mul_eq_one {k : B} (hk : IsSelfAdjoint k) {ε : ℝ}
    (hε : ‖k - 1‖ ≤ ε) (hε4 : ε ≤ 1 / 4) :
    ∃ g : B, IsSelfAdjoint g ∧ g * k * g = 1 ∧ ‖g - 1‖ ≤ ε ∧
      ∀ b : B, Commute k b → Commute g b := by
  have hspec : ∀ t ∈ spectrum ℝ k, |t - 1| ≤ ε := fun t ht ↦
    (abs_sub_one_le_of_mem_spectrum hk ht).trans hε
  have hpos : ∀ t ∈ spectrum ℝ k, 0 < t := fun t ht ↦ by
    linarith [abs_le.mp ((hspec t ht).trans hε4)]
  have hcont : ContinuousOn (fun t : ℝ ↦ (√t)⁻¹) (spectrum ℝ k) :=
    Real.continuous_sqrt.continuousOn.inv₀ fun t ht ↦ (Real.sqrt_pos.mpr (hpos t ht)).ne'
  refine ⟨cfc (fun t : ℝ ↦ (√t)⁻¹) k, cfc_predicate _ k, ?_, ?_, fun b hb ↦ hb.cfc_real _⟩
  · nth_rewrite 2 [← cfc_id' ℝ k]
    rw [← cfc_mul _ _ k, ← cfc_mul _ _ k, ← cfc_const_one ℝ k]
    refine cfc_congr fun t ht ↦ ?_
    have h0 := (Real.sqrt_pos.mpr (hpos t ht)).ne'
    field_simp
    exact (Real.sq_sqrt (hpos t ht).le).symm
  · have he : cfc (fun t : ℝ ↦ (√t)⁻¹ - 1) k = cfc (fun t : ℝ ↦ (√t)⁻¹) k - 1 := by
      rw [cfc_sub _ _ k, cfc_const_one ℝ k]
    rw [← he]
    refine norm_cfc_le ((norm_nonneg _).trans hε) fun t ht ↦ ?_
    rw [Real.norm_eq_abs]
    exact (abs_inv_sqrt_sub_one_le ((hspec t ht).trans hε4)).trans (hspec t ht)

/-- **Renormalizing a compression.** If `Q` is a projection commuting with a self-adjoint `h`
with `‖h - Q‖ ≤ ε ≤ 1/4`, then some self-adjoint `g` commuting with `Q`, with `‖g - 1‖ ≤ ε`,
renormalizes the compression: `g(QhQ)g = Q`. Here `g = k^{-1/2}` for `k = QhQ + (1 - Q)`. -/
theorem _root_.IsStarProjection.exists_isSelfAdjoint_mul_compress_mul_eq {Q h : B}
    (hQ : IsStarProjection Q) (hh : IsSelfAdjoint h) (hQh : Commute Q h) {ε : ℝ}
    (hε : ‖h - Q‖ ≤ ε) (hε4 : ε ≤ 1 / 4) :
    ∃ g : B, IsSelfAdjoint g ∧ Commute g Q ∧ g * (Q * h * Q) * g = Q ∧ ‖g - 1‖ ≤ ε := by
  have hQQ : Q * Q = Q := hQ.isIdempotentElem.eq
  have hksa : IsSelfAdjoint (Q * h + (1 - Q)) := by
    refine IsSelfAdjoint.add ?_ hQ.one_sub.isSelfAdjoint
    rw [IsSelfAdjoint, star_mul, hh.star_eq, hQ.isSelfAdjoint.star_eq]
    exact hQh.eq.symm
  have hk1 : ‖Q * h + (1 - Q) - 1‖ ≤ ε := by
    have : Q * h + (1 - Q) - 1 = Q * (h - Q) := by
      rw [mul_sub, hQQ]
      abel
    rw [this]
    exact (norm_mul_le_of_norm_le_one_left hQ.norm_le _).trans hε
  obtain ⟨g, hgsa, hgkg, hg1, hgc⟩ := exists_isSelfAdjoint_mul_mul_eq_one hksa hk1 hε4
  have hgQ : Commute g Q := hgc Q (((Commute.refl Q).mul_left hQh.symm).add_left
    ((Commute.one_left Q).sub_left (Commute.refl Q)))
  have hQk : Q * h * Q = Q * (Q * h + (1 - Q)) := by
    rw [mul_add, mul_sub, mul_one, hQQ, sub_self, add_zero, ← mul_assoc, hQQ, mul_assoc,
      ← hQh.eq, ← mul_assoc, hQQ]
  refine ⟨g, hgsa, hgQ, ?_, hg1⟩
  calc g * (Q * h * Q) * g = Q * (g * (Q * h + (1 - Q)) * g) := by
        rw [hQk, ← mul_assoc, hgQ.eq]; simp only [mul_assoc]
    _ = Q := by rw [hgkg, mul_one]

/-- A rounding is nonzero as soon as `‖h‖ > 2δ`: if `h` is self-adjoint with
`‖h - h²‖ ≤ δ < 1/4` and `2δ < ‖h‖`, then `χ_{[1/2, ∞)}(h) ≠ 0`. -/
theorem roundProjection_ne_zero {h : B} (hh : IsSelfAdjoint h) {δ : ℝ} (hδ : ‖h - h ^ 2‖ ≤ δ)
    (hδ4 : δ < 1 / 4) (hlt : 2 * δ < ‖h‖) : roundProjection h ≠ 0 := by
  intro h0
  have := norm_sub_roundProjection_le hh hδ hδ4
  rw [h0, sub_zero] at this
  linarith

end TauCeti

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

/-- **A contraction close to the compression keeps the norm defects.** If `Q` is a projection
with `‖(1 - Q)φ(1)(1 - Q)‖ ≤ ε` and `ψ : A → M_k` is a contraction with `‖ψ(a) - Qφ(a)Q‖ ≤ c‖a‖`
for all `a`, then `‖ψ(ab) - ψ(a)ψ(b)‖ ≤ ‖φ(ab) - φ(a)φ(b)‖ + (ε + 3c)‖a‖‖b‖`. -/
theorem norm_map_mul_sub_le_of_norm_sub_compress_le [DecidableEq n] {Q : CStarMatrix n n ℂ}
    (hQ : IsStarProjection Q) {ε c : ℝ} (hε : ‖(1 - Q) * φ 1 * (1 - Q)‖ ≤ ε) (hc : 0 ≤ c)
    (ψ : A → CStarMatrix n n ℂ) (hψn : ∀ a, ‖ψ a‖ ≤ ‖a‖)
    (hclose : ∀ a, ‖ψ a - Q * φ a * Q‖ ≤ c * ‖a‖) (a b : A) :
    ‖ψ (a * b) - ψ a * ψ b‖ ≤ ‖φ (a * b) - φ a * φ b‖ + (ε + 3 * c) * ‖a‖ * ‖b‖ := by
  have hcomp := norm_compress_map_mul_sub_le hφ hQ hε a b
  have hXb : ‖Q * φ b * Q‖ ≤ ‖b‖ :=
    (norm_mul_mul_le_of_norm_le_one hQ.norm_le hQ.norm_le _).trans (hφ b)
  have he : ψ (a * b) - ψ a * ψ b = (ψ (a * b) - Q * φ (a * b) * Q) +
      (Q * φ (a * b) * Q - Q * φ a * Q * (Q * φ b * Q)) +
      ((Q * φ a * Q - ψ a) * (Q * φ b * Q) + ψ a * (Q * φ b * Q - ψ b)) := by
    noncomm_ring
  have h2 := hclose a
  have h3 := hclose b
  rw [← norm_neg, neg_sub] at h2 h3
  rw [he]
  calc _ ≤ ‖ψ (a * b) - Q * φ (a * b) * Q‖ +
        ‖Q * φ (a * b) * Q - Q * φ a * Q * (Q * φ b * Q)‖ +
        (‖Q * φ a * Q - ψ a‖ * ‖Q * φ b * Q‖ + ‖ψ a‖ * ‖Q * φ b * Q - ψ b‖) :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _)
          ((norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))))
    _ ≤ c * (‖a‖ * ‖b‖) + (‖φ (a * b) - φ a * φ b‖ + ε * ‖a‖ * ‖b‖) +
        (c * ‖a‖ * ‖b‖ + ‖a‖ * (c * ‖b‖)) := by
        refine add_le_add (add_le_add ((hclose _).trans ?_) hcomp) (add_le_add ?_ ?_)
        · exact mul_le_mul_of_nonneg_left (norm_mul_le a b) hc
        · exact mul_le_mul h2 hXb (norm_nonneg _) (by positivity)
        · exact mul_le_mul (hψn a) h3 (norm_nonneg _) (norm_nonneg _)
    _ = ‖φ (a * b) - φ a * φ b‖ + (ε + 3 * c) * ‖a‖ * ‖b‖ := by ring

/-- **The norm unitalization** (Brown, Lemma 2.7, operator-norm version). Let `φ : A → M_k` be a
completely positive contraction on a unital C⋆-algebra with `‖φ(1) - φ(1)²‖ ≤ δ ≤ 1/8`, and
`Q = χ_{[1/2, ∞)}(φ(1))`. Then there is a completely positive `ψ : A → M_k` with values in the
corner `Q M_k Q` and `ψ(1) = Q`, so unital onto the corner, with `‖ψ(a) - Qφ(a)Q‖ ≤ 5δ‖a‖` and
`‖ψ(ab) - ψ(a)ψ(b)‖ ≤ ‖φ(ab) - φ(a)φ(b)‖ + 17δ‖a‖‖b‖`. It is `ψ(a) = gQφ(a)Qg` for
`g = (Qφ(1)Q + (1 - Q))^{-1/2}`. -/
theorem exists_unital_compress [DecidableEq n] {δ : ℝ} (hδ : ‖φ 1 - φ 1 ^ 2‖ ≤ δ)
    (hδ8 : δ ≤ 1 / 8) :
    ∃ ψ : A →CP CStarMatrix n n ℂ, ψ 1 = roundProjection (φ 1) ∧
      (∀ a, roundProjection (φ 1) * ψ a = ψ a ∧ ψ a * roundProjection (φ 1) = ψ a) ∧
      (∀ a, ‖ψ a - roundProjection (φ 1) * φ a * roundProjection (φ 1)‖ ≤ 5 * δ * ‖a‖) ∧
      ∀ a b, ‖ψ (a * b) - ψ a * ψ b‖ ≤ ‖φ (a * b) - φ a * φ b‖ + 17 * δ * ‖a‖ * ‖b‖ := by
  set Q := roundProjection (φ 1)
  have hsa : IsSelfAdjoint (φ 1) := IsSelfAdjoint.of_nonneg (map_nonneg φ zero_le_one)
  have hQ : IsStarProjection Q := isStarProjection_roundProjection (φ 1)
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans hδ
  have hδ4 : δ < 1 / 4 := by linarith
  have hhQ := norm_sub_roundProjection_le hsa hδ hδ4
  obtain ⟨g, hgsa, hgQ, hgkg, hg1⟩ := hQ.exists_isSelfAdjoint_mul_compress_mul_eq hsa
    (commute_roundProjection (φ 1)) hhQ (by linarith)
  have hg : ‖g‖ ≤ 1 + 2 * δ := by
    calc ‖g‖ = ‖(g - 1) + 1‖ := by rw [sub_add_cancel]
      _ ≤ ‖g - 1‖ + ‖(1 : CStarMatrix n n ℂ)‖ := norm_add_le _ _
      _ ≤ 2 * δ + 1 := add_le_add hg1 (IsStarProjection.one (R := CStarMatrix n n ℂ)).norm_le
      _ = 1 + 2 * δ := add_comm _ _
  let ψ : A →CP CStarMatrix n n ℂ := (conj (Q * g)).comp φ
  have hψ : ∀ a, ψ a = g * (Q * φ a * Q) * g := fun a ↦ by
    simp only [ψ, CompletelyPositiveMap.comp_apply, conj_apply, star_mul, hgsa.star_eq,
      hQ.isSelfAdjoint.star_eq, mul_assoc]
  have hclose : ∀ a, ‖ψ a - Q * φ a * Q‖ ≤ 5 * δ * ‖a‖ := fun a ↦ by
    have he : ψ a - Q * φ a * Q =
        (g - 1) * (Q * φ a * Q) * g + (Q * φ a * Q) * (g - 1) := by
      rw [hψ]; noncomm_ring
    have hX : ‖Q * φ a * Q‖ ≤ ‖a‖ :=
      (norm_mul_mul_le_of_norm_le_one hQ.norm_le hQ.norm_le _).trans (hφ a)
    rw [he]
    calc _ ≤ ‖g - 1‖ * ‖Q * φ a * Q‖ * ‖g‖ + ‖Q * φ a * Q‖ * ‖g - 1‖ :=
          (norm_add_le _ _).trans (add_le_add ((norm_mul_le _ _).trans
            (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))) (norm_mul_le _ _))
      _ ≤ 2 * δ * ‖a‖ * (1 + 2 * δ) + ‖a‖ * (2 * δ) := by gcongr
      _ ≤ 5 * δ * ‖a‖ := by
        nlinarith [mul_nonneg (mul_nonneg hδ0 (norm_nonneg a)) (by linarith : (0 : ℝ) ≤ 1 - 4 * δ)]
  have hψ1 : ψ 1 = Q := by rw [hψ, hgkg]
  have hQQx : ∀ x, Q * (Q * x) = Q * x := fun x ↦ by rw [← mul_assoc, hQ.isIdempotentElem.eq]
  have hQgx : ∀ x, Q * (g * x) = g * (Q * x) := fun x ↦ by rw [← mul_assoc, ← hgQ.eq, mul_assoc]
  have hψn : ∀ a, ‖ψ a‖ ≤ ‖a‖ := fun a ↦
    (CompletelyPositiveMapClass.norm_apply_le ψ a).trans
      (by rw [hψ1]; exact mul_le_of_le_one_left (norm_nonneg _) hQ.norm_le)
  have hε : ‖(1 - Q) * φ 1 * (1 - Q)‖ ≤ 2 * δ :=
    (norm_mul_le_of_norm_le_one_right hQ.one_sub.norm_le _).trans
      (norm_one_sub_roundProjection_mul_le hsa hδ hδ4)
  refine ⟨ψ, hψ1, fun a ↦ ⟨?_, ?_⟩, hclose, fun a b ↦ ?_⟩
  · simp only [hψ, mul_assoc, hQgx, hQQx]
  · simp only [hψ, mul_assoc, hgQ.eq, hQQx]
  have := norm_map_mul_sub_le_of_norm_sub_compress_le hφ hQ hε (by positivity) ψ hψn hclose a b
  linarith [mul_nonneg (norm_nonneg a) (norm_nonneg b)]

end CompletelyPositiveMap
