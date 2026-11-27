/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.RoundProjection
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.Unitization
import TauCeti.Algebra.Algebra.Unitization
import TauCeti.Algebra.Star.PartialIsometry
import TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.InvSqrtOneSub

/-!
# Projections from approximate data

The perturbation steps that replace approximate projections and approximate partial isometries in
a C⋆-algebra, possibly without unit, by exact ones.

* **Rounding.** A self-adjoint element `x` with `‖x - x * x‖ ≤ δ < 1/4` is within `2δ` of a star
  projection (`TauCeti.exists_isStarProjection_norm_sub_le`): the spectral projection
  `χ_{[1/2, ∞)}(x)`, computed in the unitization and lying in the algebra since the indicator
  vanishes at `0`.
* **Approximate partial isometries.** Let `p` and `q` be star projections and `w = q w p` with
  `‖w⋆w - p‖ < 1` and `‖ww⋆ - q‖ < 1`. Then `p` and `q` are Murray–von Neumann equivalent
  (`IsStarProjection.exists_star_mul_self_eq_of_norm_star_mul_self_sub_lt_one`). In the
  unitization, `h = p - w⋆w` has norm `< 1`, so `c = (1 - h) ^ (-1 / 2)` exists and commutes with
  `p`; the polar part `v = w c` has `v⋆v = p` and `vv⋆ ≤ q`, and `e = q - vv⋆` satisfies
  `e = e (q - ww⋆)`, so `‖e‖ ≤ ‖e‖ ‖ww⋆ - q‖` forces `e = 0`.
* **Estimates.** An element within `η ≤ 1` of a projection has defect `‖x - x * x‖ ≤ 4η`
  (`IsStarProjection.norm_sub_mul_self_le`), and compressing an element within `η ≤ 1` of a
  partial isometry `v` between its final and initial projections gives an approximate partial
  isometry with defects at most `3η` (`IsStarProjection.norm_compress_sub_le`).

These are the perturbation steps of the continuity of `K₀` along C⋆-inductive limits.

## Main statements

* `TauCeti.exists_isStarProjection_norm_sub_le`: rounding an almost-projection.
* `IsStarProjection.exists_star_mul_self_eq_of_norm_star_mul_self_sub_lt_one`: projections joined
  by an approximate partial isometry are Murray–von Neumann equivalent.
* `IsStarProjection.norm_sub_mul_self_le`, `IsStarProjection.norm_compress_sub_le`: the defect
  estimates.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., Cambridge University Press (1998),
  5.2.4.
-/

public section

open scoped CStarAlgebra

namespace TauCeti

section Rounding

variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- **Rounding an almost-projection, without unit.** A self-adjoint element `x` of a C⋆-algebra,
possibly without unit, with `‖x - x * x‖ ≤ δ < 1/4` is within `2δ` of a star projection. -/
theorem exists_isStarProjection_norm_sub_le {x : A} (hx : IsSelfAdjoint x) {δ : ℝ}
    (hδ : ‖x - x * x‖ ≤ δ) (hδ4 : δ < 1 / 4) :
    ∃ p : A, IsStarProjection p ∧ ‖x - p‖ ≤ 2 * δ := by
  set g : ℝ → ℝ := (Set.Ici (1 / 2 : ℝ)).indicator 1 with hg
  have hg0 : g 0 = 0 := Set.indicator_of_notMem (by norm_num) _
  have hinr : ((cfcₙ g x : A) : Unitization ℂ A) = roundProjection (x : Unitization ℂ A) := by
    rw [roundProjection_eq_cfc, ← hg, Unitization.real_cfcₙ_eq_cfc_inr x g hg0]
  refine ⟨cfcₙ g x, ?_, ?_⟩
  · rw [← Unitization.isStarProjection_inr_iff (R := ℂ), hinr]
    exact isStarProjection_roundProjection _
  · have hδ' : ‖(x : Unitization ℂ A) - (x : Unitization ℂ A) ^ 2‖ ≤ δ := by
      rwa [sq, ← Unitization.inr_mul, ← Unitization.inr_sub, Unitization.norm_inr]
    have := norm_sub_roundProjection_le (hx.inr ℂ) hδ' hδ4
    rwa [← hinr, ← Unitization.inr_sub, Unitization.norm_inr] at this

end Rounding

end TauCeti

namespace IsStarProjection

section Unital

variable {A : Type*} [CStarAlgebra A] {p q w : A}

/-- **Approximate partial isometries, unital case.** If `w = q w p` with `‖w⋆w - p‖ < 1` and
`‖ww⋆ - q‖ < 1`, then `v = w (1 - p + w⋆w) ^ (-1 / 2)` has `v⋆v = p` and `vv⋆ = q`. -/
private theorem exists_star_mul_self_eq_of_norm_star_mul_self_sub_lt_one_of_unital
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hw : q * w * p = w)
    (h₁ : ‖star w * w - p‖ < 1) (h₂ : ‖w * star w - q‖ < 1) :
    ∃ v : A, star v * v = p ∧ v * star v = q := by
  have hpp : p * p = p := hp.isIdempotentElem.eq
  have hqq : q * q = q := hq.isIdempotentElem.eq
  have hwp : w * p = w := by rw [← hw, mul_assoc, hpp]
  have hqw : q * w = w := by rw [← hw, ← mul_assoc, ← mul_assoc, hqq]
  have hpw : p * star w = star w := by
    simpa [hp.isSelfAdjoint.star_eq] using congrArg star hwp
  -- `h = p - w⋆w` commutes with `p`, and `w⋆w = (1 - h) * p`
  set h := p - star w * w with hh_def
  have hph : p * h = h := by rw [hh_def, mul_sub, hpp, ← mul_assoc, hpw]
  have hhp : h * p = h := by rw [hh_def, sub_mul, hpp, mul_assoc, hwp]
  have hww : star w * w = (1 - h) * p := by rw [sub_mul, one_mul, hhp, hh_def, sub_sub_cancel]
  -- `c = (1 - h) ^ (-1 / 2)` is self-adjoint and commutes with `p` and `w⋆w`
  set c := cfc (fun t : ℝ ↦ (√(1 - t))⁻¹) h
  have hc : IsSelfAdjoint c := IsSelfAdjoint.cfc
  have hcc : c * c * (1 - h) = 1 := TauCeti.cfc_inv_sqrt_one_sub_mul_self_mul_one_sub
    (hp.isSelfAdjoint.sub (IsSelfAdjoint.star_mul_self w)) (by rwa [norm_sub_rev])
  have hcp : Commute c p := Commute.cfc_real (hhp.trans hph.symm) _
  have hcw : Commute c (star w * w) := by
    rw [show star w * w = p - h by rw [hh_def, sub_sub_cancel]]
    exact hcp.sub_right (Commute.cfc_real (.refl h) _)
  set v := w * c with hv
  have hv₁ : star v * v = p :=
    calc star v * v = c * (star w * w) * c := by simp only [hv, star_mul, hc.star_eq, mul_assoc]
      _ = c * c * (1 - h) * p := by rw [mul_assoc, ← hcw.eq, ← mul_assoc, hww, ← mul_assoc]
      _ = p := by rw [hcc, one_mul]
  have hvp : v * p = v := by rw [hv, mul_assoc, hcp.eq, ← mul_assoc, hwp]
  have hqv : q * v = v := by rw [hv, ← mul_assoc, hqw]
  -- `w = v * c'` for `c' = c * (1 - h)`, so `e = q - vv⋆` kills `ww⋆`
  have hwv : w = v * (c * (1 - h)) := by rw [hv, mul_assoc, ← mul_assoc c, hcc, mul_one]
  set e := q - v * star v with he
  have hev : e * v = 0 := by rw [he, sub_mul, hqv, mul_assoc, hv₁, hvp, sub_self]
  have heq : e * q = e := by
    have : v * star v * q = v * star v := by
      rw [mul_assoc, ← hq.isSelfAdjoint.star_eq, ← star_mul, hqv]
    rw [he, sub_mul, hqq, this]
  have hee : e = e * (q - w * star w) := by
    rw [mul_sub, heq, hwv, ← mul_assoc, ← mul_assoc, hev, zero_mul, zero_mul, sub_zero]
  have hnorm : ‖e‖ ≤ ‖e‖ * ‖w * star w - q‖ := by
    conv_lhs => rw [hee]
    rw [← norm_neg (w * star w - q), neg_sub]
    exact norm_mul_le _ _
  have he0 : e = 0 := norm_le_zero_iff.1 (by nlinarith [norm_nonneg e])
  exact ⟨v, hv₁, (sub_eq_zero.1 he0).symm⟩

end Unital

variable {A : Type*} [NonUnitalCStarAlgebra A] {p q w : A}

/-- **Approximate partial isometries give equivalences.** Let `p` and `q` be star projections of
a C⋆-algebra, possibly without unit, and `w = q w p` with `‖w⋆w - p‖ < 1` and `‖ww⋆ - q‖ < 1`.
Then `star v * v = p` and `v * star v = q` for some `v`. -/
theorem exists_star_mul_self_eq_of_norm_star_mul_self_sub_lt_one (hp : IsStarProjection p)
    (hq : IsStarProjection q) (hw : q * w * p = w) (h₁ : ‖star w * w - p‖ < 1)
    (h₂ : ‖w * star w - q‖ < 1) : ∃ v : A, star v * v = p ∧ v * star v = q := by
  have hp' : IsStarProjection (p : Unitization ℂ A) := hp.inr
  have hq' : IsStarProjection (q : Unitization ℂ A) := hq.inr
  have hinr {x y : A} : ‖x - y‖ = ‖(x : Unitization ℂ A) - y‖ := by
    rw [← Unitization.inr_sub, Unitization.norm_inr]
  obtain ⟨u, hu₁, hu₂⟩ := exists_star_mul_self_eq_of_norm_star_mul_self_sub_lt_one_of_unital hp'
    hq' (w := (w : Unitization ℂ A)) (by rw [← Unitization.inr_mul, ← Unitization.inr_mul, hw])
    (by rwa [← Unitization.inr_star, ← Unitization.inr_mul, ← hinr])
    (by rwa [← Unitization.inr_star, ← Unitization.inr_mul, ← hinr])
  exact hp.exists_star_mul_self_eq_of_star_mul_self_eq_unitization hq.isIdempotentElem hu₁ hu₂

/-- **Defect near a projection.** If `‖x - p‖ ≤ η ≤ 1` for a star projection `p`, then
`‖x - x * x‖ ≤ 4 η`. -/
theorem norm_sub_mul_self_le {x : A} (hp : IsStarProjection p) {η : ℝ} (hx : ‖x - p‖ ≤ η)
    (hη : η ≤ 1) : ‖x - x * x‖ ≤ 4 * η := by
  set d := x - p with hd
  have he : x - x * x = d - (p * d + d * p + d * d) := by
    rw [show x = p + d by rw [hd]; abel]
    have hpp : p * p = p := hp.isIdempotentElem.eq
    noncomm_ring
    rw [hpp]
    abel
  have hp1 : ‖p‖ ≤ 1 := hp.norm_le
  have hη0 : 0 ≤ η := (norm_nonneg _).trans hx
  rw [he]
  calc ‖d - (p * d + d * p + d * d)‖ ≤ ‖d‖ + (‖p‖ * ‖d‖ + ‖d‖ * ‖p‖ + ‖d‖ * ‖d‖) := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        refine (norm_add₃_le).trans ?_
        gcongr <;> exact norm_mul_le _ _
    _ ≤ η + (1 * η + η * 1 + η * η) := by gcongr
    _ ≤ 4 * η := by nlinarith [norm_nonneg d]

/-- **Compressing an approximate partial isometry.** Let `p` be a star projection, `v⋆v = p` (so
`v` is a partial isometry), `vv⋆ = q` and `‖y - v‖ ≤ η ≤ 1`. Then the compression `q y p`
has `‖(q y p)⋆ (q y p) - p‖ ≤ 3 η` and `‖(q y p) (q y p)⋆ - q‖ ≤ 3 η`. -/
theorem norm_compress_sub_le {v y : A} (hp : IsStarProjection p) (hv₁ : star v * v = p)
    (hv₂ : v * star v = q) {η : ℝ} (hy : ‖y - v‖ ≤ η) (hη : η ≤ 1) :
    ‖star (q * y * p) * (q * y * p) - p‖ ≤ 3 * η ∧
      ‖q * y * p * star (q * y * p) - q‖ ≤ 3 * η := by
  have hv := TauCeti.IsPartialIsometry.of_star_mul_self_eq hp hv₁
  have hv₃ : v * star v * v = v := hv.mul_star_mul_self
  have hq : IsStarProjection q := hv₂ ▸ hv.isStarProjection_mul_star_self
  have hv1 : ‖v‖ ≤ 1 := by
    have h1 : ‖v‖ * ‖v‖ ≤ 1 := by
      rw [← CStarRing.norm_star_mul_self, hv₁]
      exact hp.norm_le
    nlinarith [norm_nonneg v]
  have hη0 : 0 ≤ η := (norm_nonneg _).trans hy
  have hqv : q * v = v := by rw [← hv₂, hv₃]
  have hvp : v * p = v := by rw [← hv₁, ← mul_assoc, hv₃]
  set w := q * y * p
  have hwv : ‖w - v‖ ≤ η := by
    have he : q * (y - v) * p = w - v := by rw [mul_sub, sub_mul, hqv, hvp]
    rw [← he]
    calc ‖q * (y - v) * p‖ ≤ ‖q‖ * ‖y - v‖ * ‖p‖ := norm_mul₃_le
      _ ≤ 1 * η * 1 :=
        mul_le_mul (mul_le_mul hq.norm_le hy (norm_nonneg _) zero_le_one) hp.norm_le
          (norm_nonneg _) (by positivity)
      _ = η := by ring
  have hw1 : ‖w‖ ≤ 1 + η :=
    calc ‖w‖ = ‖v + (w - v)‖ := by rw [add_sub_cancel]
      _ ≤ 1 + η := norm_add_le_of_le hv1 hwv
  have key (a b c d : A) (ha : ‖a‖ ≤ 1 + η) (hb : ‖b‖ ≤ η) (hc : ‖c‖ ≤ η) (hd : ‖d‖ ≤ 1) :
      ‖a * b + c * d‖ ≤ 3 * η :=
    calc ‖a * b + c * d‖ ≤ ‖a‖ * ‖b‖ + ‖c‖ * ‖d‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ ≤ (1 + η) * η + η * 1 := by gcongr
      _ ≤ 3 * η := by nlinarith
  constructor
  · have he : star w * w - p = star w * (w - v) + star (w - v) * v := by
      rw [← hv₁, star_sub]
      noncomm_ring
    rw [he]
    exact key _ _ _ _ (by rwa [norm_star]) hwv (by rwa [norm_star]) hv1
  · have he : w * star w - q = w * star (w - v) + (w - v) * star v := by
      rw [← hv₂, star_sub]
      noncomm_ring
    rw [he]
    exact key _ _ _ _ hw1 (by rwa [norm_star]) hwv (by rwa [norm_star])

end IsStarProjection
