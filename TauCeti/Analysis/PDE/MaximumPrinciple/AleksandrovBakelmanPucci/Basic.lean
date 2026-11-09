/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import TauCeti.Analysis.PDE.MaximumPrinciple.ContactSet
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.Analysis.InnerProductSpace.Spectrum
import TauCeti.Analysis.Matrix.PosSemidef.Determinant
import TauCeti.Analysis.PDE.MaximumPrinciple.NonDivergence

/-!
# The Aleksandrov–Bakelman–Pucci maximum principle

Let `Ω` be a bounded open subset of `ℝⁿ = EuclideanSpace ℝ ι`, `n ≥ 1`, and let `u` be continuous
on `closure Ω` and `C²` in `Ω`. Let `a` be a field of matrices and `f` a function such that, on
the upper contact set `Γ⁺ = TauCeti.PDE.upperContactSet u Ω`, the matrices `a` are positive
definite and

`f ≤ ∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu`,

and let `m` bound `u` on `frontier Ω`. Write `D* = (det a)^{1/n}`, `f⁻ = max (-f) 0` and `ωₙ`
for the volume of the unit ball, and suppose that `f⁻ / D*` lies in `Lⁿ(Γ⁺)`. The
Aleksandrov–Bakelman–Pucci estimate bounds `u` on `Ω` by

`u ≤ m + diam Ω / (n ωₙ^{1/n}) ‖f⁻ / D*‖_{Lⁿ(Γ⁺)}`

(Gilbarg–Trudinger, Lemma 9.3 and Theorem 9.1, for operators without drift). Nothing is assumed
of `a` and `f` off the contact set, and the coefficients need no regularity. The measure form
`TauCeti.PDE.volume_ball_le_setLIntegral_upperContactSet` needs no measurability of `a` or `f`
at all; the `Lⁿ` form needs only the integrability of `f⁻ / D*` on `Γ⁺` stated above.

The proof combines the Aleksandrov measure estimate
`TauCeti.PDE.addHaar_ball_le_lintegral_abs_det_hessianOperator` with a pointwise bound on the
contact set. There the negated Hessian matrix `M` is positive semidefinite, so the
determinant–trace inequality `det a det M ≤ (tr (a M) / n)ⁿ` and `tr (a M) ≤ f⁻` give
`|det D²u| ≤ (f⁻ / n)ⁿ / det a`. The pointwise bound
(`TauCeti.PDE.abs_det_le_negPart_div_card_pow_div_det`) is stated for any operator `T` with
`-T` positive in place of `D²u`, so that it applies equally to the weak Hessian of a `W^{2,n}`
function (`TauCeti.Analysis.PDE.MaximumPrinciple.AleksandrovBakelmanPucci.Sobolev`).

## Main declarations

* `TauCeti.PDE.sum_mul_fderiv_fderiv_nonpos_of_mem_upperContactSet`: on the contact set, the
  principal part `∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu` is nonpositive for every `A` with nonnegative quadratic form.
* `TauCeti.PDE.abs_det_le_negPart_div_card_pow_div_det`: for `-T` positive, `A` positive
  definite and `c ≤ ∑ᵢⱼ Aᵢⱼ (T eⱼ)ᵢ`, the bound `|det T| ≤ (c⁻ / n)ⁿ / det A`.
* `TauCeti.PDE.abs_det_hessianOperator_mul_det_le_of_mem_upperContactSet`: the pointwise bound
  `|det D²u| det A ≤ (-∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu / n)ⁿ` on the contact set, for positive semidefinite `A`.
* `TauCeti.PDE.volume_ball_le_setLIntegral_upperContactSet`: the
  Aleksandrov–Bakelman–Pucci estimate in measure form,
  `|B(0, (u x - m) / diam Ω)| ≤ ∫_{Γ⁺} (f⁻ / n)ⁿ / det a`.
* `TauCeti.PDE.setLIntegral_negPart_div_det_eq_mul_eLpNorm_pow` and
  `TauCeti.PDE.le_add_div_mul_toReal_of_volume_ball_le`: the right-hand side of the measure form
  is `n⁻ⁿ ‖f⁻ / (det a)^{1/n}‖ⁿ`, and the measure form inverts to a bound on `u`.
* `TauCeti.PDE.le_add_mul_eLpNorm_negPart_div_det_rpow`: **the Aleksandrov–Bakelman–Pucci
  estimate** `u ≤ m + diam Ω / (n ωₙ^{1/n}) ‖f⁻ / (det a)^{1/n}‖_{Lⁿ(Γ⁺)}`, for
  `f⁻ / (det a)^{1/n} ∈ Lⁿ(Γ⁺)`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 9.1 (Lemmas 9.2 and 9.3, Theorem 9.1).
* A. D. Aleksandrov, *Uniqueness conditions and estimates for the solution of the Dirichlet
  problem*, Vestnik Leningrad. Univ. 18 (1963), 5–29.
-/

public section

noncomputable section

open Filter InnerProductSpace Matrix Metric MeasureTheory Set Topology
open scoped ENNReal Gradient RealInnerProductSpace

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : Set (EuclideanSpace ℝ ι)}
  {u f : EuclideanSpace ℝ ι → ℝ} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {m : ℝ}
  {x y : EuclideanSpace ℝ ι}

/-- **The principal part on the upper contact set.** If the matrix `A` has nonnegative quadratic
form and `u` is `C²` on an open set `Ω`, then `∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu(y) ≤ 0` at every point `y` of the
upper contact set. -/
theorem sum_mul_fderiv_fderiv_nonpos_of_mem_upperContactSet (hΩ : IsOpen Ω)
    (hu : ContDiffOn ℝ 2 u Ω) (hy : y ∈ upperContactSet u Ω) {A : Matrix ι ι ℝ}
    (hA : ∀ ξ : EuclideanSpace ℝ ι, 0 ≤ A.toQuadraticForm' ξ) :
    ∑ i, ∑ j, A i j * fderiv ℝ (fderiv ℝ u) y (EuclideanSpace.single i 1)
      (EuclideanSpace.single j 1) ≤ 0 :=
  sum_mul_fderiv_fderiv_nonpos hA (hu.contDiffAt (hΩ.mem_nhds (upperContactSet_subset hy)))
    (fderiv_fderiv_self_nonpos_of_mem_upperContactSet hΩ hu hy)

/-- In the standard basis of `ℝⁿ`, the entries `(D²u(y) eⱼ)ᵢ` of the Hessian operator of a function
`C²` at `y` are the second partial derivatives `∂ᵢ∂ⱼu(y)`. -/
private theorem hessianOperator_single_apply (hu : ContDiffAt ℝ 2 u y) (i j : ι) :
    hessianOperator u y (EuclideanSpace.single j 1) i =
      fderiv ℝ (fderiv ℝ u) y (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
  rw [← hu.isSymmSndFDerivAt (by simp), ← inner_hessianOperator_left]
  simp [EuclideanSpace.inner_single_right]

/-- **The pointwise bound by the elliptic operator.** If `-T` is a positive operator on `ℝⁿ`, `A`
is positive definite and `c ≤ ∑ᵢⱼ Aᵢⱼ (T eⱼ)ᵢ`, then `|det T| ≤ (c⁻ / n)ⁿ / det A`. Applied to the
Hessian `T = D²u` on the upper contact set, with `c = f`, it bounds the integrand of the
Aleksandrov measure estimate by that of the Aleksandrov–Bakelman–Pucci estimate. -/
theorem abs_det_le_negPart_div_card_pow_div_det
    {T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι} (hT : (-T).IsPositive) {A : Matrix ι ι ℝ}
    (hA : A.PosDef) {c : ℝ} (hc : c ≤ ∑ i, ∑ j, A i j * T (EuclideanSpace.single j 1) i) :
    |LinearMap.det T| ≤ (c⁻ / Fintype.card ι) ^ Fintype.card ι / A.det := by
  have hentry : ∑ i, ∑ j, A i j * (-T) (EuclideanSpace.single j 1) i =
      -∑ i, ∑ j, A i j * T (EuclideanSpace.single j 1) i := by
    simp [Finset.sum_neg_distrib]
  have hS := hT.sum_mul_apply_nonneg hA.posSemidef
  have hD := hT.det_mul_det_le_sum_mul_apply_div_card_pow hA.posSemidef
  rw [hentry] at hS hD
  rw [← hT.abs_det_neg, neg_neg] at hD
  refine (le_div_iff₀ hA.det_pos).2 (hD.trans (pow_le_pow_left₀
    (div_nonneg hS (Nat.cast_nonneg _)) (div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)) _))
  exact (neg_le_neg hc).trans (neg_le_negPart _)

/-- **The determinant bound on the upper contact set.** If `u` is `C²` on an open set `Ω` and
`A` is positive semidefinite, then at every point `y` of the upper contact set,
`|det D²u(y)| det A ≤ (-∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu(y) / n)ⁿ`, where `n` is the dimension. -/
theorem abs_det_hessianOperator_mul_det_le_of_mem_upperContactSet (hΩ : IsOpen Ω)
    (hu : ContDiffOn ℝ 2 u Ω) (hy : y ∈ upperContactSet u Ω) {A : Matrix ι ι ℝ}
    (hA : A.PosSemidef) :
    |(hessianOperator u y).det| * A.det ≤
      ((-∑ i, ∑ j, A i j * fderiv ℝ (fderiv ℝ u) y (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1)) / Fintype.card ι) ^ Fintype.card ι := by
  have hT := (isPositive_neg_hessianOperator_of_mem_upperContactSet hΩ hu hy).toLinearMap
  have h := hT.det_mul_det_le_sum_mul_apply_div_card_pow hA
  rw [hT.abs_det_neg.symm, ContinuousLinearMap.toLinearMap_neg, neg_neg] at h
  simpa only [ContinuousLinearMap.coe_coe, LinearMap.neg_apply, PiLp.neg_apply,
    hessianOperator_single_apply (hu.contDiffAt (hΩ.mem_nhds (upperContactSet_subset hy))),
    mul_neg, Finset.sum_neg_distrib] using h

/-- **The Aleksandrov–Bakelman–Pucci estimate, measure form** (Gilbarg–Trudinger, Lemma 9.3
without drift). Let `Ω` be bounded and open, let `u` be continuous on `closure Ω` and `C²` in
`Ω`, and let `m` bound `u` on `frontier Ω`. If on the upper contact set `Γ⁺` the matrices `a y`
are positive definite and `f y ≤ ∑ᵢⱼ aⁱʲ(y) ∂ᵢ∂ⱼu(y)`, then for `x ∈ Ω`,
`|B(0, (u x - m) / diam Ω)| ≤ ∫_{Γ⁺} (f⁻ / n)ⁿ / det a`. -/
theorem volume_ball_le_setLIntegral_upperContactSet
    (hΩb : Bornology.IsBounded Ω) (hΩ : IsOpen Ω) (hcont : ContinuousOn u (closure Ω))
    (hu : ContDiffOn ℝ 2 u Ω) (ha : ∀ y ∈ upperContactSet u Ω, (a y).PosDef)
    (hf : ∀ y ∈ upperContactSet u Ω, f y ≤ ∑ i, ∑ j, a y i j *
      fderiv ℝ (fderiv ℝ u) y (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))
    (hm : ∀ z ∈ frontier Ω, u z ≤ m) (hx : x ∈ Ω) :
    volume (ball (0 : EuclideanSpace ℝ ι) ((u x - m) / diam Ω)) ≤
      ∫⁻ y in upperContactSet u Ω,
        ENNReal.ofReal (((f y)⁻ / Fintype.card ι) ^ Fintype.card ι / (a y).det) := by
  refine (addHaar_ball_le_lintegral_abs_det_hessianOperator volume hΩb hΩ hcont hu hm hx).trans
    (setLIntegral_mono' (measurableSet_upperContactSet hΩ (hu.of_le (by norm_num)))
      fun y hy => ENNReal.ofReal_le_ofReal ?_)
  refine abs_det_le_negPart_div_card_pow_div_det
    (isPositive_neg_hessianOperator_of_mem_upperContactSet hΩ hu hy).toLinearMap (ha y hy) ?_
  simpa only [ContinuousLinearMap.coe_coe, hessianOperator_single_apply
    (hu.contDiffAt (hΩ.mem_nhds (upperContactSet_subset hy)))] using hf y hy

/-- **The right-hand side of the Aleksandrov–Bakelman–Pucci estimate.** If the matrices `a y` are
positive definite for almost every `y ∈ S`, then
`∫_S (f⁻ / n)ⁿ / det a = n⁻ⁿ ‖f⁻ / D*‖_{Lⁿ(S)}ⁿ` with `D* = (det a)^{1/n}`. -/
theorem setLIntegral_negPart_div_det_eq_mul_eLpNorm_pow [Nonempty ι]
    {S : Set (EuclideanSpace ℝ ι)} (ha : ∀ᵐ y ∂volume.restrict S, (a y).PosDef)
    (hg : AEStronglyMeasurable (fun y => (f y)⁻ / (a y).det ^ (Fintype.card ι : ℝ)⁻¹)
      (volume.restrict S)) :
    ∫⁻ y in S, ENNReal.ofReal (((f y)⁻ / Fintype.card ι) ^ Fintype.card ι / (a y).det) =
      ENNReal.ofReal (((Fintype.card ι : ℝ) ^ Fintype.card ι)⁻¹) *
        eLpNorm (fun y => (f y)⁻ / (a y).det ^ (Fintype.card ι : ℝ)⁻¹) (Fintype.card ι)
          (volume.restrict S) ^ Fintype.card ι := by
  set n := Fintype.card ι
  set g := fun y => (f y)⁻ / (a y).det ^ (n : ℝ)⁻¹
  have hn : n ≠ 0 := Fintype.card_ne_zero
  have h := eLpNorm_nnreal_pow_eq_lintegral (p := (n : NNReal)) (Nat.cast_ne_zero.2 hn) hg
  simp only [ENNReal.coe_natCast, NNReal.coe_natCast, ENNReal.rpow_natCast] at h
  rw [h, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr_ae (ha.mono fun y hy => ?_)
  have hdet := hy.det_pos
  have hgy : 0 ≤ g y := div_nonneg (negPart_nonneg _) (Real.rpow_nonneg hdet.le _)
  dsimp only
  rw [Real.enorm_eq_ofReal hgy, ← ENNReal.ofReal_pow hgy,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  simp only [g, div_pow, Real.rpow_inv_natCast_pow hdet.le hn]
  field_simp

omit [DecidableEq ι] in
/-- **Inverting the measure form.** In `ℝⁿ`, `n ≥ 1`, if `d > 0` and the ball of radius
`(t - m) / d` has volume at most `n⁻ⁿ Nⁿ` for a finite `N`, then
`t ≤ m + d / (n ωₙ^{1/n}) N`, where `ωₙ` is the volume of the unit ball. -/
theorem le_add_div_mul_toReal_of_volume_ball_le [Nonempty ι] {t d : ℝ} {N : ℝ≥0∞}
    (hd : 0 < d) (hN : N ≠ ∞)
    (h : volume (ball (0 : EuclideanSpace ℝ ι) ((t - m) / d)) ≤
      ENNReal.ofReal (((Fintype.card ι : ℝ) ^ Fintype.card ι)⁻¹) * N ^ Fintype.card ι) :
    t ≤ m + d / (Fintype.card ι *
        (volume (ball (0 : EuclideanSpace ℝ ι) 1)).toReal ^ (Fintype.card ι : ℝ)⁻¹) * N.toReal := by
  set n := Fintype.card ι
  set ω := (volume (ball (0 : EuclideanSpace ℝ ι) 1)).toReal
  have hn : n ≠ 0 := Fintype.card_ne_zero
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  have hω : 0 < ω := ENNReal.toReal_pos (measure_ball_pos volume _ one_pos).ne'
    measure_ball_lt_top.ne
  rcases le_or_gt t m with htm | htm
  · exact le_add_of_le_of_nonneg htm (mul_nonneg (div_nonneg hd.le (by positivity))
      ENNReal.toReal_nonneg)
  set r := (t - m) / d with hr_def
  have hr : 0 < r := div_pos (sub_pos.2 htm) hd
  have htm' : t - m = r * d := by
    rw [hr_def]
    field_simp
  clear_value r
  rw [Measure.addHaar_ball_of_pos _ _ hr, finrank_euclideanSpace] at h
  -- Pass to real numbers: `rⁿ ω ≤ N.toRealⁿ / nⁿ`, so `r ω^{1/n} ≤ N.toReal / n`.
  have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.pow_ne_top hN)) h
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_pow] at hreal
  have hroot : r * ω ^ (n : ℝ)⁻¹ ≤ N.toReal / n := by
    refine (pow_le_pow_iff_left₀ (by positivity) (by positivity) hn).1 ?_
    rw [mul_pow, Real.rpow_inv_natCast_pow hω.le hn]
    calc r ^ n * ω ≤ ((n : ℝ) ^ n)⁻¹ * N.toReal ^ n := hreal
      _ = (N.toReal / n) ^ n := by rw [div_pow]; ring
  have hωn : 0 < ω ^ (n : ℝ)⁻¹ := Real.rpow_pos_of_pos hω _
  rw [← sub_le_iff_le_add', htm', div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  calc r * d * (n * ω ^ (n : ℝ)⁻¹) = d * n * (r * ω ^ (n : ℝ)⁻¹) := by ring
    _ ≤ d * n * (N.toReal / n) := by gcongr
    _ = d * N.toReal := by field_simp

/-- **The Aleksandrov–Bakelman–Pucci estimate** (Gilbarg–Trudinger, Lemma 9.3 and Theorem 9.1
without drift). Let `Ω ⊆ ℝⁿ`, `n ≥ 1`, be bounded and open, let `u` be continuous on `closure Ω`
and `C²` in `Ω`, and let `m` bound `u` on `frontier Ω`. Suppose that on the upper contact set
`Γ⁺` the matrices `a y` are positive definite and `f y ≤ ∑ᵢⱼ aⁱʲ(y) ∂ᵢ∂ⱼu(y)`, and that
`f⁻ / D*`, with `D* = (det a)^{1/n}`, lies in `Lⁿ(Γ⁺)`. Then on `Ω`,
`u ≤ m + diam Ω / (n ωₙ^{1/n}) ‖f⁻ / D*‖_{Lⁿ(Γ⁺)}`, where `ωₙ` is the volume of the unit ball. -/
theorem le_add_mul_eLpNorm_negPart_div_det_rpow [Nonempty ι] (hΩb : Bornology.IsBounded Ω)
    (hΩ : IsOpen Ω) (hcont : ContinuousOn u (closure Ω)) (hu : ContDiffOn ℝ 2 u Ω)
    (ha : ∀ y ∈ upperContactSet u Ω, (a y).PosDef)
    (hf : ∀ y ∈ upperContactSet u Ω, f y ≤ ∑ i, ∑ j, a y i j *
      fderiv ℝ (fderiv ℝ u) y (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))
    (hg : MemLp (fun y => (f y)⁻ / (a y).det ^ (Fintype.card ι : ℝ)⁻¹) (Fintype.card ι)
      (volume.restrict (upperContactSet u Ω)))
    (hm : ∀ z ∈ frontier Ω, u z ≤ m) (hx : x ∈ Ω) :
    u x ≤ m + diam Ω / (Fintype.card ι *
        (volume (ball (0 : EuclideanSpace ℝ ι) 1)).toReal ^ (Fintype.card ι : ℝ)⁻¹) *
      (eLpNorm (fun y => (f y)⁻ / (a y).det ^ (Fintype.card ι : ℝ)⁻¹) (Fintype.card ι)
        (volume.restrict (upperContactSet u Ω))).toReal := by
  refine le_add_div_mul_toReal_of_volume_ball_le
    (diam_pos (infinite_of_mem_nhds x (hΩ.mem_nhds hx)).nontrivial hΩb) hg.eLpNorm_lt_top.ne ?_
  rw [← setLIntegral_negPart_div_det_eq_mul_eLpNorm_pow
    (ae_restrict_of_forall_mem (measurableSet_upperContactSet hΩ (hu.of_le (by norm_num))) ha)
    hg.aestronglyMeasurable]
  exact volume_ball_le_setLIntegral_upperContactSet hΩb hΩ hcont hu ha hf hm hx

end PDE

end TauCeti
