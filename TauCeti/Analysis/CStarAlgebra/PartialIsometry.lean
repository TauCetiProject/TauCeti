/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import TauCeti.Algebra.Star.PartialIsometry
public import TauCeti.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.Unitization
import TauCeti.Algebra.Algebra.Unitization
import TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.InvSqrtOneSub
import TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.RoundProjection
import TauCeti.Analysis.Normed.Algebra.Star

/-!
# Norm stability of partial isometries in C⋆-algebras

Every partial isometry in a C⋆-ring has norm at most `1` (`TauCeti.IsPartialIsometry.norm_le_one`).
For star projections `p, q` and a corner-compressed element `w` (`q * w * p = w`) with
`‖star w * w - p‖ < 1` and `‖w * star w - q‖ < 1`, polar normalization gives a partial isometry
with `star v * v = p` and `v * star v = q`
(`IsStarProjection.exists_star_mul_self_eq_of_norm_star_mul_self_sub_lt_one`). When
`‖star z * z - p‖ < η` and `‖z * star z - q‖ < η` with `η ≤ 1 / 32`, `v` satisfies
`‖v - z‖ < 10 * η` and belongs to every closed non-unital `𝕜'`-`⋆`-subalgebra (for any scalar
monoid `𝕜'` over `ℝ`) containing `z` (`TauCeti.exists_isPartialIsometry_mem_of_approx`), and
compressing an element within `η ≤ 1` of a partial isometry between `p` and `q` gives defects
at most `3 * η` (`IsStarProjection.norm_compress_sub_le`).

## Main results

* `TauCeti.IsPartialIsometry.norm_le_one`,
  `IsStarProjection.exists_star_mul_self_eq_of_norm_star_mul_self_sub_lt_one`,
  `IsStarProjection.norm_compress_sub_le`,
  `TauCeti.exists_isPartialIsometry_mem_of_approx`, `TauCeti.exists_isPartialIsometry_of_approx`.

## References

* B. Blackadar, *Operator Algebras*, Springer (2006), Proposition II.8.3.23; *K-Theory for Operator
  Algebras*, 2nd ed., Cambridge Univ. Press (1998), 5.2.4.
-/

public section
open scoped CStarAlgebra
open NonUnitalStarSubalgebra (mem_corner mem_ofClass)
namespace TauCeti

/-- Every partial isometry in a C⋆-ring has norm at most `1`. -/
theorem IsPartialIsometry.norm_le_one {E : Type*} [NonUnitalNormedRing E] [StarRing E]
    [CStarRing E] {v : E} (hv : IsPartialIsometry v) : ‖v‖ ≤ 1 := by
  have hle : ‖star v * v‖ ≤ 1 := hv.isStarProjection_star_mul_self.norm_le _
  rw [CStarRing.norm_star_mul_self] at hle; nlinarith [norm_nonneg v]

variable {A : Type*} [NonUnitalCStarAlgebra A]
/-- **Quantitative polar perturbation of an approximate partial isometry** in a closed non-unital
`𝕜'`-`⋆`-subalgebra `s` (scalar monoid `𝕜'` over `ℝ`): for star projections `p, q` and `z ∈ s`
with `q * z = z`, `z * p = z`, `‖star z * z - p‖ < η`, `‖z * star z - q‖ < η` (`η ≤ 1 / 32`), some
partial isometry `v ∈ s` has `star v * v = p`, `v * star v = q`, `‖v - z‖ < 10 * η`. -/
theorem exists_isPartialIsometry_mem_of_approx {𝕜' S : Type*} [Monoid 𝕜'] [MulAction 𝕜' A]
    [SetLike S A] [NonUnitalSubringClass S A] [SMul ℝ 𝕜'] [IsScalarTower ℝ 𝕜' A]
    [SMulMemClass S 𝕜' A] [StarMemClass S A] {s : S} [IsClosed (s : Set A)] {η : ℝ}
    (hη : η ≤ 1 / 32) {p q z : A} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hzs : z ∈ s) (hqz : q * z = z) (hzp : z * p = z) (hinit : ‖star z * z - p‖ < η)
    (hfin : ‖z * star z - q‖ < η) :
    ∃ v ∈ s, IsPartialIsometry v ∧ star v * v = p ∧ v * star v = q ∧ ‖v - z‖ < 10 * η := by
  have : SMulMemClass S ℝ A := SMulMemClass.ofIsScalarTower S ℝ 𝕜' A
  have hph : p * (star z * z) = star z * z := by
    rw [← hp.isSelfAdjoint.star_eq, ← mul_assoc, ← star_mul, hzp]
  have hhp : star z * z * p = star z * z := by rw [mul_assoc, hzp]
  obtain ⟨w, hw_corner, hw_sa, hwhw, hw_sub_p⟩ :=
    (IsSelfAdjoint.star_mul_self z).exists_mem_corner_of_norm_sub_le
      (s := NonUnitalStarSubalgebra.ofClass s) hp
      (mem_corner.mpr ⟨mul_mem (star_mem (mem_ofClass.mpr hzs)) (mem_ofClass.mpr hzs), hph, hhp⟩)
      (by linarith)
  obtain ⟨hw_mem_s', -, hwp⟩ := mem_corner.mp hw_corner
  set v : A := z * w
  have hv_init : star v * v = p := by
    simpa only [v, star_mul, hw_sa.star_eq, mul_assoc] using hwhw
  have hv_pi : IsPartialIsometry v := by
    rw [isPartialIsometry_iff, mul_assoc, hv_init]; dsimp [v]; rw [mul_assoc, hwp]
  have hz_norm : ‖z‖ ≤ 2 := by
    have hnorm_sq : ‖star z * z‖ = ‖z‖ * ‖z‖ := CStarRing.norm_star_mul_self
    nlinarith [norm_nonneg z, hp.norm_le p, norm_le_norm_add_norm_sub' (star z * z) p]
  have hv_sub_z : ‖v - z‖ < 10 * η := by
    have hvz : v - z = z * (w - p) := by dsimp [v]; rw [mul_sub, hzp]
    rw [hvz]
    exact (norm_mul_le_of_le hz_norm le_rfl).trans_lt
      (by nlinarith [norm_nonneg (star z * z - p)])
  have hv_fin_q : (v * star v) * q = v * star v := by
    have hqv : q * v = v := by dsimp [v]; rw [← mul_assoc, hqz]
    rw [← hq.isSelfAdjoint.star_eq, mul_assoc, ← star_mul, hqv]
  have hv_fin_dist : ‖v * star v - q‖ < 1 := by
    have hprod_diff : ‖v * star v - z * star z‖ ≤ ‖v - z‖ * ‖v‖ + ‖z‖ * ‖v - z‖ :=
      norm_mul_star_sub_mul_star_le v v z z
    have h1 : ‖v - z‖ * ‖v‖ ≤ (10 * η) * 1 :=
      mul_le_mul hv_sub_z.le hv_pi.norm_le_one (norm_nonneg _) (by linarith [norm_nonneg (v - z)])
    have h2 : ‖z‖ * ‖v - z‖ ≤ 2 * (10 * η) :=
      mul_le_mul hz_norm hv_sub_z.le (norm_nonneg _) (by positivity)
    linarith [norm_sub_le_norm_sub_add_norm_sub (v * star v) (z * star z) q]
  exact ⟨v, mul_mem hzs (mem_ofClass.mp hw_mem_s'), hv_pi, hv_init,
    hv_pi.isStarProjection_mul_star_self.eq_of_mul_eq_left_of_norm_sub_lt_one hq hv_fin_q
      hv_fin_dist, hv_sub_z⟩
/-- **Quantitative polar perturbation of an approximate partial isometry**: for projections `p, q`
and `z` (`q * z = z`, `z * p = z`, `‖star z * z - p‖ < η`, `‖z * star z - q‖ < η`, `η ≤ 1 / 32`),
a partial isometry `v` has `star v * v = p`, `v * star v = q`, `‖v - z‖ < 10 * η`. -/
theorem exists_isPartialIsometry_of_approx {η : ℝ} (hη : η ≤ 1 / 32) {p q z : A}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hqz : q * z = z) (hzp : z * p = z)
    (hinit : ‖star z * z - p‖ < η) (hfin : ‖z * star z - q‖ < η) :
    ∃ v : A, IsPartialIsometry v ∧ star v * v = p ∧ v * star v = q ∧ ‖v - z‖ < 10 * η :=
  let ⟨v, _, h⟩ := exists_isPartialIsometry_mem_of_approx (𝕜' := ℝ)
    (s := (⊤ : NonUnitalStarSubalgebra ℝ A)) hη hp hq NonUnitalStarAlgebra.mem_top hqz hzp
    hinit hfin
  ⟨v, h⟩
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
