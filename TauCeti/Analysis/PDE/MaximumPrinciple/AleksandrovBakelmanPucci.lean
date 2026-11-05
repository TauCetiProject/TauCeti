/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import TauCeti.Analysis.PDE.MaximumPrinciple.ContactSet
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
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
`|det D²u| ≤ (f⁻ / n)ⁿ / det a`.

## Main declarations

* `TauCeti.PDE.sum_mul_fderiv_fderiv_nonpos_of_mem_upperContactSet`: on the contact set, the
  principal part `∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu` is nonpositive for every `A` with nonnegative quadratic form.
* `TauCeti.PDE.abs_det_hessianOperator_mul_det_le_of_mem_upperContactSet`: the pointwise bound
  `|det D²u| det A ≤ (-∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu / n)ⁿ` on the contact set, for positive semidefinite `A`.
* `TauCeti.PDE.volume_ball_le_setLIntegral_upperContactSet`: the
  Aleksandrov–Bakelman–Pucci estimate in measure form,
  `|B(0, (u x - m) / diam Ω)| ≤ ∫_{Γ⁺} (f⁻ / n)ⁿ / det a`.
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

/-- **The determinant bound on the upper contact set.** If `u` is `C²` on an open set `Ω` and
`A` is positive semidefinite, then at every point `y` of the upper contact set,
`|det D²u(y)| det A ≤ (-∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu(y) / n)ⁿ`, where `n` is the dimension. -/
theorem abs_det_hessianOperator_mul_det_le_of_mem_upperContactSet (hΩ : IsOpen Ω)
    (hu : ContDiffOn ℝ 2 u Ω) (hy : y ∈ upperContactSet u Ω) {A : Matrix ι ι ℝ}
    (hA : A.PosSemidef) :
    |(hessianOperator u y).det| * A.det ≤
      ((-∑ i, ∑ j, A i j * fderiv ℝ (fderiv ℝ u) y (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1)) / Fintype.card ι) ^ Fintype.card ι := by
  set H := fderiv ℝ (fderiv ℝ u) y
  set M : Matrix ι ι ℝ :=
    Matrix.of fun i j => -H (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
  have hM : M.PosSemidef :=
    posSemidef_neg_fderiv_fderiv (hu.contDiffAt (hΩ.mem_nhds (upperContactSet_subset hy)))
      (fderiv_fderiv_self_nonpos_of_mem_upperContactSet hΩ hu hy)
  have hsymm (i j : ι) : M j i = M i j := by simpa using hM.isHermitian.apply i j
  -- In the standard basis the Hessian operator has matrix `-M`.
  have hmat : (Matrix.of fun i j => fderiv ℝ (fderiv ℝ u) y (EuclideanSpace.single j 1)
      (EuclideanSpace.single i 1)) = -M := by
    ext i j
    rw [Matrix.neg_apply, ← hsymm]
    simp [M, H]
  have hdet : |(hessianOperator u y).det| = M.det := by
    simp [(EuclideanSpace.basisFun ι ℝ).det_hessianOperator, hmat, det_neg, abs_mul,
      abs_of_nonneg hM.det_nonneg]
  have htr : (A * M).trace = -∑ i, ∑ j, A i j * H (EuclideanSpace.single i 1)
      (EuclideanSpace.single j 1) := by
    simp only [trace, diag_apply, ← Finset.sum_neg_distrib, ← mul_neg]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    dsimp only
    rw [hsymm]
    simp [M]
  rw [hdet, mul_comm, ← htr]
  exact hA.det_mul_det_le_trace_mul_div_card_pow hM

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
  rw [le_div_iff₀ (ha y hy).det_pos]
  refine (abs_det_hessianOperator_mul_det_le_of_mem_upperContactSet hΩ hu hy
    (ha y hy).posSemidef).trans ?_
  have hS := sum_mul_fderiv_fderiv_nonpos_of_mem_upperContactSet hΩ hu hy (A := a y) fun ξ => by
    simpa [toQuadraticForm'_apply] using (ha y hy).posSemidef.dotProduct_mulVec_nonneg ξ.ofLp
  refine pow_le_pow_left₀ (div_nonneg (neg_nonneg.2 hS) (Nat.cast_nonneg _))
    (div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)) _
  exact (neg_le_neg (hf y hy)).trans (neg_le_negPart _)

/-- The right-hand side of the measure form is `n⁻ⁿ ‖f⁻ / (det a)^{1/n}‖_{Lⁿ(Γ⁺)}ⁿ`. -/
private theorem setLIntegral_upperContactSet_eq_mul_eLpNorm_pow [Nonempty ι] (hΩ : IsOpen Ω)
    (hu : ContDiffOn ℝ 2 u Ω) (ha : ∀ y ∈ upperContactSet u Ω, (a y).PosDef)
    (hg : MemLp (fun y => (f y)⁻ / (a y).det ^ (Fintype.card ι : ℝ)⁻¹) (Fintype.card ι)
      (volume.restrict (upperContactSet u Ω))) :
    ∫⁻ y in upperContactSet u Ω,
        ENNReal.ofReal (((f y)⁻ / Fintype.card ι) ^ Fintype.card ι / (a y).det) =
      ENNReal.ofReal (((Fintype.card ι : ℝ) ^ Fintype.card ι)⁻¹) *
        eLpNorm (fun y => (f y)⁻ / (a y).det ^ (Fintype.card ι : ℝ)⁻¹) (Fintype.card ι)
          (volume.restrict (upperContactSet u Ω)) ^ Fintype.card ι := by
  set n := Fintype.card ι
  set g := fun y => (f y)⁻ / (a y).det ^ (n : ℝ)⁻¹
  have hn : n ≠ 0 := Fintype.card_ne_zero
  have h := eLpNorm_nnreal_pow_eq_lintegral (p := (n : NNReal)) (Nat.cast_ne_zero.2 hn)
    (by simpa using hg.aestronglyMeasurable)
  simp only [ENNReal.coe_natCast, NNReal.coe_natCast, ENNReal.rpow_natCast] at h
  rw [h, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_congr_fun (measurableSet_upperContactSet hΩ (hu.of_le (by norm_num)))
    fun y hy => ?_
  have hdet := (ha y hy).det_pos
  have hgy : 0 ≤ g y := div_nonneg (negPart_nonneg _) (Real.rpow_nonneg hdet.le _)
  rw [Real.enorm_eq_ofReal hgy, ← ENNReal.ofReal_pow hgy,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  simp only [g, div_pow, Real.rpow_inv_natCast_pow hdet.le hn]
  field_simp

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
  set n := Fintype.card ι
  set Γ := upperContactSet u Ω
  set g := fun y => (f y)⁻ / (a y).det ^ (n : ℝ)⁻¹
  set N := (eLpNorm g n (volume.restrict Γ)).toReal
  set ω := (volume (ball (0 : EuclideanSpace ℝ ι) 1)).toReal
  have hn : n ≠ 0 := Fintype.card_ne_zero
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  have hω : 0 < ω := ENNReal.toReal_pos (measure_ball_pos volume _ one_pos).ne'
    measure_ball_lt_top.ne
  have hN : 0 ≤ N := ENNReal.toReal_nonneg
  rcases le_or_gt (u x) m with hux | hux
  · exact le_add_of_le_of_nonneg hux (mul_nonneg (div_nonneg diam_nonneg (by positivity)) hN)
  -- `Ω` is a nonempty open set, so it has positive diameter.
  have hd : 0 < diam Ω := by
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hΩ x hx
    calc 0 < 2 * ε := by positivity
      _ = diam (ball x ε) := (diam_ball_eq x hε.le).symm
      _ ≤ diam Ω := diam_mono hball hΩb
  set r := (u x - m) / diam Ω with hr_def
  have hr : 0 < r := div_pos (sub_pos.2 hux) hd
  have hux' : u x - m = r * diam Ω := by
    rw [hr_def]
    field_simp
  clear_value r
  -- The measure estimate, with the right-hand side rewritten through `‖g‖_{Lⁿ(Γ⁺)}`.
  have hkey := volume_ball_le_setLIntegral_upperContactSet hΩb hΩ hcont hu ha hf
    hm hx
  rw [← hr_def, Measure.addHaar_ball_of_pos _ _ hr, finrank_euclideanSpace,
    setLIntegral_upperContactSet_eq_mul_eLpNorm_pow hΩ hu ha hg] at hkey
  -- Pass to real numbers.
  have hfin : ENNReal.ofReal ((n : ℝ) ^ n)⁻¹ * eLpNorm g n (volume.restrict Γ) ^ n ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top hg.eLpNorm_lt_top.ne)
  have hreal := ENNReal.toReal_mono hfin hkey
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_pow] at hreal
  -- `hreal : rⁿ ω ≤ Nⁿ / nⁿ`, so `r ω^{1/n} ≤ N / n`.
  have hroot : r * ω ^ (n : ℝ)⁻¹ ≤ N / n := by
    refine (pow_le_pow_iff_left₀ (by positivity) (by positivity) hn).1 ?_
    rw [mul_pow, Real.rpow_inv_natCast_pow hω.le hn]
    calc r ^ n * ω ≤ ((n : ℝ) ^ n)⁻¹ * N ^ n := hreal
      _ = (N / n) ^ n := by rw [div_pow]; ring
  have hωn : 0 < ω ^ (n : ℝ)⁻¹ := Real.rpow_pos_of_pos hω _
  rw [← sub_le_iff_le_add', hux', div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  calc r * diam Ω * (n * ω ^ (n : ℝ)⁻¹) = diam Ω * n * (r * ω ^ (n : ℝ)⁻¹) := by ring
    _ ≤ diam Ω * n * (N / n) := by gcongr
    _ = diam Ω * N := by field_simp

end PDE

end TauCeti
