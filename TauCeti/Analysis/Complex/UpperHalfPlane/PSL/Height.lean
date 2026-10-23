/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
public import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
public import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Action
public import TauCeti.Topology.Compactification.OnePoint.ProjectiveLine
import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Affine
import TauCeti.Analysis.Complex.UpperHalfPlane.ProperAction

/-!
# Heights after moving a real boundary point to `∞`

If `g ∈ PSL(2, ℝ)` carries the real boundary point `ξ` to `∞`, then a lift of `g` has lower row
proportional to `(1, -ξ)`, so `g` acts as `z ↦ (az + b) / (c (z - ξ))`. Its effect on heights is
therefore `Im (g • z) = Im z / (c² |z - ξ|²)`. For `A > 0` the set `{z | A < Im (g • z)}` is a
horodisc at `ξ`, a Euclidean disc tangent to `ℝ` at `ξ` (for `A ≤ 0` it is all of `ℍ`), and this
formula is how a horodisc at a real point is compared with Euclidean distances to that point.

The formula shows that the points of `ℍ` escaping a horodisc are plentiful: all sufficiently high
points lie outside a horodisc at a real point, and points of a small fixed height lie outside any
given horodisc once they are far enough to the left. Consequently, a set with points arbitrarily
high up that stays bounded after removing finitely many horodiscs has one of them centred at `∞`.

## Main results

* `TauCeti.UpperHalfPlane.exists_im_smul_eq_div_of_smul_coe_eq_infty`: the height formula above.
* `TauCeti.UpperHalfPlane.eventually_im_smul_le`: high points lie outside a horodisc at a real
  point.
* `TauCeti.UpperHalfPlane.exists_pos_eventually_im_smul_le`: points of a small fixed height lie
  outside a horodisc once they are far enough to the left.
* `TauCeti.UpperHalfPlane.exists_smul_infty_eq_infty`: a set with points arbitrarily high up that
  is bounded after removing finitely many horodiscs has one of them centred at `∞`.
-/

public section

open Matrix Matrix.ProjectiveSpecialLinearGroup OnePoint UpperHalfPlane Set Filter
open scoped MatrixGroups Pointwise

namespace TauCeti.UpperHalfPlane

/-- If `g ∈ PSL(2, ℝ)` carries the real boundary point `ξ` to `∞`, then there is `c > 0` such that
`Im (g • z) = Im z / (c |z - ξ|²)` for every `z ∈ ℍ`; here `c` is the square of the lower-left
entry of a lift of `g`. -/
theorem exists_im_smul_eq_div_of_smul_coe_eq_infty {g : PSL(2, ℝ)} {ξ : ℝ}
    (hg : g • (ξ : OnePoint ℝ) = ∞) :
    ∃ c : ℝ, 0 < c ∧ ∀ z : ℍ, (g • z).im = z.im / (c * Complex.normSq ((z : ℂ) - ξ)) := by
  induction g using QuotientGroup.induction_on with | H a => ?_
  rw [OnePoint.pslMk_smul, OnePoint.smul_some_eq_ite] at hg
  split_ifs at hg with h
  · simp only [SpecialLinearGroup.coe_GL_coe_matrix] at h
    have hdet : a 0 0 * a 1 1 - a 0 1 * a 1 0 = 1 := by
      rw [← Matrix.det_fin_two]
      exact a.det_coe
    -- the lower-left entry is nonzero, since otherwise the lower row would vanish
    have hc : a 1 0 ≠ 0 := by
      intro hc
      rw [hc, zero_mul, zero_add] at h
      rw [h, hc] at hdet
      simp at hdet
    refine ⟨a 1 0 ^ 2, by positivity, fun z ↦ ?_⟩
    have hd : a 1 1 = -(a 1 0 * ξ) := by linear_combination h
    have hdenom : denom (SpecialLinearGroup.mapGL ℝ a) z = a 1 0 * ((z : ℂ) - ξ) := by
      simp [denom, hd]
      ring
    rw [UpperHalfPlane.pslMk_smul, MulAction.compHom_smul_def, im_smul_eq_div_normSq, hdenom,
      Complex.normSq_mul, Complex.normSq_ofReal]
    simp [sq]
  · exact absurd hg (OnePoint.coe_ne_infty _)

/-! ### Points outside horodiscs -/

/-- An element of `PSL(2, ℝ)` not fixing `∞` carries some real point to `∞`. -/
theorem exists_smul_coe_eq_infty {g : PSL(2, ℝ)} (hg : g • (∞ : OnePoint ℝ) ≠ ∞) :
    ∃ ξ : ℝ, g • (ξ : OnePoint ℝ) = ∞ := by
  obtain ⟨ξ, hξ⟩ := OnePoint.ne_infty_iff_exists.1 fun h : g⁻¹ • (∞ : OnePoint ℝ) = ∞ ↦
    hg (by calc g • (∞ : OnePoint ℝ) = g • (g⁻¹ • ∞) := by rw [h]
      _ = ∞ := smul_inv_smul g ∞)
  exact ⟨ξ, by rw [hξ, smul_inv_smul]⟩

/-- For `A > 0`, the points of every sufficiently small height `h` lie outside the horodisc
`{z | A < Im (g • z)}` once they are far enough to the left. -/
theorem exists_pos_eventually_im_smul_le (g : PSL(2, ℝ)) {A : ℝ} (hA : 0 < A) :
    ∃ b > 0, ∀ h, h ≤ b → ∀ᶠ x in atBot, ∀ z : ℍ, z.re = x → z.im = h →
      (g • z).im ≤ A := by
  by_cases hg : g • (∞ : OnePoint ℝ) = ∞
  · -- a horodisc at `∞` is the region above a fixed height
    obtain ⟨μ, hμ, c, hc⟩ := exists_coe_smul_eq_mul_add_of_smul_infty hg
    refine ⟨A / μ, div_pos hA hμ, fun h hb ↦ Eventually.of_forall fun x z _ hz ↦ ?_⟩
    have him : (g • z).im = μ * z.im := by
      rw [← coe_im, hc]
      simp
    rw [him, hz]
    calc μ * h ≤ μ * (A / μ) := by gcongr
      _ = A := mul_div_cancel₀ A hμ.ne'
  -- a horodisc at a real point `ξ` lies in a vertical strip around `ξ`
  obtain ⟨ξ, hξ⟩ := exists_smul_coe_eq_infty hg
  obtain ⟨c, hc, hgc⟩ := exists_im_smul_eq_div_of_smul_coe_eq_infty hξ
  refine ⟨1, one_pos, fun h hb ↦ ?_⟩
  filter_upwards [eventually_le_atBot (ξ - (1 + 1 / (c * A)))] with x hx z hzx hzh
  have hcA : 0 < c * A := mul_pos hc hA
  have hN : Complex.normSq ((z : ℂ) - ξ) = (ξ - x) ^ 2 + h ^ 2 := by
    rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, coe_re, coe_im, Complex.ofReal_re,
      Complex.ofReal_im, hzx, hzh]
    ring
  have hxξ : 0 < ξ - x := by linarith [one_div_pos.2 hcA]
  have hd : 1 / (c * A) ≤ (ξ - x) ^ 2 := by nlinarith [one_div_pos.2 hcA]
  rw [div_le_iff₀ hcA] at hd
  have hpos : 0 < c * Complex.normSq ((z : ℂ) - ξ) := by
    rw [hN]
    exact mul_pos hc (add_pos_of_pos_of_nonneg (pow_pos hxξ 2) (sq_nonneg h))
  rw [hgc, div_le_iff₀ hpos, hN, hzh]
  nlinarith [mul_nonneg hcA.le (sq_nonneg h)]

/-- For `A > 0`, all sufficiently high points lie outside a horodisc `{z | A < Im (g • z)}` at a
real point. -/
theorem eventually_im_smul_le {g : PSL(2, ℝ)} (hg : g • (∞ : OnePoint ℝ) ≠ ∞) {A : ℝ}
    (hA : 0 < A) : ∀ᶠ z : ℍ in atImInfty, (g • z).im ≤ A := by
  obtain ⟨ξ, hξ⟩ := exists_smul_coe_eq_infty hg
  obtain ⟨c, hc, hgc⟩ := exists_im_smul_eq_div_of_smul_coe_eq_infty hξ
  refine (atImInfty_mem _).2 ⟨1 / (c * A), fun z hz ↦ ?_⟩
  have hcA : 0 < c * A := mul_pos hc hA
  have hN : z.im ^ 2 ≤ Complex.normSq ((z : ℂ) - ξ) := by
    rw [Complex.normSq_apply, Complex.sub_im, coe_im, Complex.ofReal_im, sub_zero]
    nlinarith [mul_self_nonneg ((z : ℂ) - ξ).re]
  rw [div_le_iff₀ hcA] at hz
  rw [mem_ofPred_eq, hgc, div_le_iff₀ (mul_pos hc (lt_of_lt_of_le (by positivity) hN))]
  nlinarith [z.im_pos]

variable {ι : Type*} {K : Set ℍ}

/-- If `K` has points arbitrarily high up and stays bounded after removing finitely many
horodiscs, one of these horodiscs is centred at `∞`. -/
theorem exists_smul_infty_eq_infty [Finite ι] (hfreq : ∃ᶠ z in atImInfty, z ∈ K)
    (g : ι → PSL(2, ℝ)) {A : ι → ℝ} (hA : ∀ i, 0 < A i)
    (hb : Bornology.IsBounded (K \ ⋃ i, {z : ℍ | A i < (g i • z).im})) :
    ∃ i, g i • (∞ : OnePoint ℝ) = ∞ := by
  by_contra! hg
  -- a bounded set has bounded heights
  obtain ⟨R, hR⟩ := hb.subset_closedBall UpperHalfPlane.I
  have hhigh : ∀ᶠ z : ℍ in atImInfty, z ∉ K \ ⋃ i, {z : ℍ | A i < (g i • z).im} := by
    refine (atImInfty_mem _).2 ⟨Real.exp R + 1, fun z hz hzT ↦ ?_⟩
    have hzR := Metric.mem_closedBall.1 (hR hzT)
    have him : z.im ≤ Real.exp R := by
      calc z.im ≤ UpperHalfPlane.I.im * Real.exp (dist z UpperHalfPlane.I) :=
            im_le_im_mul_exp_dist z UpperHalfPlane.I
        _ ≤ Real.exp R := by
          rw [UpperHalfPlane.I_im, one_mul]
          exact Real.exp_le_exp.2 hzR
    linarith
  have hout : ∀ᶠ z : ℍ in atImInfty, z ∉ ⋃ i, {z : ℍ | A i < (g i • z).im} := by
    filter_upwards [eventually_all.2 fun i ↦ eventually_im_smul_le (hg i) (hA i)] with z hz
    simp only [mem_iUnion, mem_ofPred_eq, not_exists, not_lt]
    exact hz
  obtain ⟨z, ⟨hzK, hzo⟩, hzT⟩ := ((hfreq.and_eventually hout).and_eventually hhigh).exists
  exact hzT ⟨hzK, hzo⟩

/-- Moving `K` by `h` and the horodiscs along with it preserves boundedness of the truncation. -/
theorem isBounded_smul_sdiff (h : PSL(2, ℝ)) (g : ι → PSL(2, ℝ)) (A : ι → ℝ)
    (hb : Bornology.IsBounded (K \ ⋃ i, {z : ℍ | A i < (g i • z).im})) :
    Bornology.IsBounded (h • K \ ⋃ i, {z : ℍ | A i < ((g i * h⁻¹) • z).im}) := by
  have heq : h • K \ ⋃ i, {z : ℍ | A i < ((g i * h⁻¹) • z).im} =
      h • (K \ ⋃ i, {z : ℍ | A i < (g i • z).im}) := by
    ext z
    simp only [Set.mem_sdiff, mem_smul_set_iff_inv_smul_mem, mem_iUnion, mem_ofPred_eq, mul_smul]
  rw [heq, ← image_smul]
  exact (isometry_smul ℍ h).lipschitzWith.isBounded_image hb

/-- A set containing all the points of a fixed height `h > 0` and real part at most `X` is
unbounded. -/
theorem not_isBounded_of_forall_re_le {S : Set ℍ} {h X : ℝ} (hh : 0 < h)
    (hS : ∀ z : ℍ, z.re ≤ X → z.im = h → z ∈ S) : ¬Bornology.IsBounded S := by
  intro hb
  let pt (x : ℝ) : ℍ := UpperHalfPlane.mk (x + h * Complex.I) (by simpa using hh)
  have hre (x : ℝ) : (pt x).re = x := by simp [pt, UpperHalfPlane.mk_re]
  have him (x : ℝ) : (pt x).im = h := by simp [pt, UpperHalfPlane.mk_im]
  have hpt (x : ℝ) (hx : x ≤ X) : pt x ∈ S := hS _ ((hre x).le.trans hx) (him x)
  obtain ⟨R, hR⟩ := hb.subset_closedBall (pt X)
  -- a point far to the left is far from `pt X` in `ℂ`, hence also in `ℍ`
  set x := X - h * Real.exp R - 1
  have hxX : x ≤ X := by
    have := mul_pos hh (Real.exp_pos R)
    simp only [x]
    linarith
  have hd := (dist_coe_le (pt x) (pt X)).trans (mul_le_mul_of_nonneg_left
    (sub_le_sub_right (Real.exp_le_exp.2 (Metric.mem_closedBall.1 (hR (hpt x hxX)))) 1)
    (pt X).im_pos.le)
  have hre' : |(pt x).re - (pt X).re| ≤ dist ((pt x : ℍ) : ℂ) (pt X) := by
    rw [dist_eq_norm, ← coe_re, ← coe_re, ← Complex.sub_re]
    exact Complex.abs_re_le_norm _
  rw [him] at hd
  rw [hre, hre, abs_of_nonpos (by linarith)] at hre'
  simp only [x] at hre'
  nlinarith

end TauCeti.UpperHalfPlane
