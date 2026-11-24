/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import TauCeti.Analysis.Contour.Curve.Rectangle
public import TauCeti.Analysis.Contour.Residue.Basic
import TauCeti.Analysis.Contour.Cauchy.Rectangle
import TauCeti.Analysis.Contour.Residue.Theorem
import TauCeti.Topology.MetricSpace.SeparatedBalls

/-!
# The residue theorem on a rectangle and U-shaped contour shifts

For a closed axis-parallel rectangle `R = Complex.Rectangle z w` with `z` its lower left corner,
a finite set `P` in its open interior `(z.re, w.re) ×ℂ (z.im, w.im)`, and a function `f : ℂ → ℂ`
continuous on `R \ P`, complex differentiable on `(z.re, w.re) ×ℂ (z.im, w.im) \ P`, and
meromorphic at each point of `P`, the contour integral of `f` along the counterclockwise boundary
`Complex.rectBoundary z w` is `2πi` times the sum of the residues of `f` at `P`:

`∫ t in 0..4, γ' t • f (γ t) = 2πi · ∑_{p ∈ P} Res_p f`.

No open neighbourhood of the closed rectangle is required: the four-edge rectangle residue theorem
`TauCeti.Contour.rectangle_boundary_integral_eq_residues` reduces the four-edge boundary integral
to small circle integrals around `P` via
`TauCeti.Contour.rectangle_boundary_integral_eq_sum_circleIntegral`, and
`TauCeti.Contour.classicalResidueTheorem_rectBoundary` derives the `Complex.rectBoundary` form
through `Complex.integral_rectBoundary`. We also provide finite-height and infinite-line U-shaped
contour shifts.

## Main results

* `TauCeti.Contour.classicalResidueTheorem_rectBoundary`: the residue theorem along
  `Complex.rectBoundary z w`, assuming only continuity on the closed rectangle off `P` and complex
  differentiability on its interior off `P`.
* `TauCeti.Contour.rectangle_boundary_integral_eq_residues`: the four-edge boundary integral of `f`
  around `[σ₁, σ₂] ×ℂ [t₁, t₂]` equals `2πi · ∑ p ∈ P, residue f p`, under the same hypotheses.
* `TauCeti.Contour.intervalIntegral_vertical_eq_uShaped_add_two_pi_mul_sum_residue`: the
  finite-height U-shaped identity expressing the right vertical edge in terms of the left vertical
  edge, the horizontal edges, and the enclosed residues.
* `TauCeti.Contour.integral_vertical_eq_uShaped_add_two_pi_mul_sum_residue`: the infinite-line
  U-shaped contour shift for an arbitrary vertical window `[t₁, t₂]`.
* `TauCeti.Contour.integral_vertical_eq_uShaped_symm_add_two_pi_mul_sum_residue`: the symmetric
  `[-T, T]` form with tail integral over `{y : ℝ | T < |y|}`.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 4, §5 (the residue theorem and improper integrals).
* E. C. Titchmarsh, *The Theory of Functions*, §3.1 and §9.5.
* S. Lang, *Complex Analysis* (GTM 103), Ch. VI.
* A. Kontorovich and T. Tao, *PrimeNumberTheoremAnd* blueprint
  (<https://github.com/AlexKontorovich/PrimeNumberTheoremAnd>), §4.1 (Definitions 4.1.3–4.1.5,
  Lemmas 4.1.1–4.1.4, and Theorem 4.1.2, for simple poles).
-/

public section

open Set Complex Filter MeasureTheory Metric
open scoped Real Interval Topology

namespace TauCeti.Contour

/-- **The rectangle residue theorem in four-edge form.** Let `σ₁ ≤ σ₂`, `t₁ ≤ t₂`, `P` a finite
subset of the open rectangle `(σ₁, σ₂) ×ℂ (t₁, t₂)`, and `f : ℂ → ℂ` continuous on the closed
rectangle minus `P`, complex differentiable on the open rectangle minus `P`, and meromorphic at
each point of `P`. Then Mathlib's counterclockwise four-edge boundary integral equals
`2πi · ∑ p ∈ P, residue f p`.

No open neighbourhood of the closed rectangle is required, and poles in `P` may have arbitrary
order (or be removable). -/
theorem rectangle_boundary_integral_eq_residues {σ₁ σ₂ t₁ t₂ : ℝ} (hσ : σ₁ ≤ σ₂) (ht : t₁ ≤ t₂)
    {P : Finset ℂ} (hP : ∀ p ∈ P, p ∈ Ioo σ₁ σ₂ ×ℂ Ioo t₁ t₂) {f : ℂ → ℂ}
    (hc : ContinuousOn f (Icc σ₁ σ₂ ×ℂ Icc t₁ t₂ \ P))
    (hd : DifferentiableOn ℂ f (Ioo σ₁ σ₂ ×ℂ Ioo t₁ t₂ \ P))
    (hmer : ∀ p ∈ P, MeromorphicAt f p) :
    (∫ x : ℝ in σ₁..σ₂, f (x + t₁ * I)) - (∫ x : ℝ in σ₁..σ₂, f (x + t₂ * I)) +
        I * (∫ y : ℝ in t₁..t₂, f (σ₂ + y * I)) - I * (∫ y : ℝ in t₁..t₂, f (σ₁ + y * I)) =
      2 * π * I * ∑ p ∈ P, residue f p := by
  let U : Set ℂ := Ioo σ₁ σ₂ ×ℂ Ioo t₁ t₂
  have hU : IsOpen U := isOpen_Ioo.reProdIm isOpen_Ioo
  obtain ⟨r, hr, hP_ball, hsep⟩ := TauCeti.exists_pos_closedBall_subset_and_lt_dist
    (T := P) (U := fun _ ↦ U) (fun p hp ↦ hU.mem_nhds (hP p hp))
  have hdisj : (P : Set ℂ).Pairwise fun p q ↦ Disjoint (closedBall p r) (closedBall q r) :=
    fun p hp q hq hne ↦ closedBall_disjoint_closedBall (by linarith [hsep p hp q hq hne])
  have hcirc := rectangle_boundary_integral_eq_sum_circleIntegral hσ ht hr hP_ball hdisj hc hd
  simp only [smul_eq_mul] at hcirc
  rw [hcirc, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  refine circleIntegral_eq_residue (mem_ball_self hr) (hmer p hp) fun z hz hzp ↦ ?_
  have hzUP : z ∈ U \ P := ⟨hP_ball p hp hz, fun hzP ↦
    disjoint_left.1 (hdisj hp hzP hzp.symm) hz (mem_closedBall_self hr.le)⟩
  exact hd.analyticAt ((hU.sdiff P.finite_toSet.isClosed).mem_nhds hzUP)

/-- **The classical residue theorem on a rectangle.** Let `z` be the lower left corner of the
closed rectangle `Rectangle z w`, and let `P` be a finite subset of the open rectangle
`(z.re, w.re) ×ℂ (z.im, w.im)`. If `f : ℂ → ℂ` is continuous on `Rectangle z w \ P`, complex
differentiable on `(z.re, w.re) ×ℂ (z.im, w.im) \ P`, and meromorphic at each point of `P`, then
the contour integral of `f` along `rectBoundary z w` equals `2πi · ∑ p ∈ P, residue f p`.

No open neighbourhood of the closed rectangle is required, and poles in `P` may have arbitrary
order (or be removable). -/
theorem classicalResidueTheorem_rectBoundary {f : ℂ → ℂ} {P : Finset ℂ} {z w : ℂ}
    (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hP : ∀ p ∈ P, p ∈ Ioo z.re w.re ×ℂ Ioo z.im w.im)
    (hc : ContinuousOn f (Rectangle z w \ P))
    (hd : DifferentiableOn ℂ f (Ioo z.re w.re ×ℂ Ioo z.im w.im \ P))
    (hmer : ∀ p ∈ P, MeromorphicAt f p) :
    ∫ t in (0 : ℝ)..4, deriv (rectBoundary z w) t • f (rectBoundary z w t) =
      2 * π * I * ∑ p ∈ P, residue f p := by
  have hrect : Rectangle z w = Icc z.re w.re ×ℂ Icc z.im w.im := by
    rw [Rectangle, uIcc_of_le hre, uIcc_of_le him]
  have hfr : ContinuousOn f (frontier (Rectangle z w)) :=
    hc.mono (frontier_rectangle_subset_sdiff fun p hp ↦ hP p (Finset.mem_coe.1 hp))
  rw [integral_rectBoundary hfr]
  simp only [smul_eq_mul]
  exact rectangle_boundary_integral_eq_residues hre him hP (hrect ▸ hc) hd hmer

/-- **Finite-height U-shaped contour identity.** Under the hypotheses of
`rectangle_boundary_integral_eq_residues` (with no integrability hypothesis), the right vertical
edge integral equals the left vertical edge integral plus the horizontal difference
`(top - bottom) / I` plus `2π · ∑ p ∈ P, residue f p`. -/
theorem intervalIntegral_vertical_eq_uShaped_add_two_pi_mul_sum_residue {σ₁ σ₂ t₁ t₂ : ℝ}
    (hσ : σ₁ ≤ σ₂) (ht : t₁ ≤ t₂)
    {P : Finset ℂ} (hP : ∀ p ∈ P, p ∈ Ioo σ₁ σ₂ ×ℂ Ioo t₁ t₂) {f : ℂ → ℂ}
    (hc : ContinuousOn f (Icc σ₁ σ₂ ×ℂ Icc t₁ t₂ \ P))
    (hd : DifferentiableOn ℂ f (Ioo σ₁ σ₂ ×ℂ Ioo t₁ t₂ \ P))
    (hmer : ∀ p ∈ P, MeromorphicAt f p) :
    (∫ y : ℝ in t₁..t₂, f (σ₂ + y * I)) =
      (∫ y : ℝ in t₁..t₂, f (σ₁ + y * I)) +
      ((∫ x : ℝ in σ₁..σ₂, f (x + t₂ * I)) - (∫ x : ℝ in σ₁..σ₂, f (x + t₁ * I))) / I +
      2 * π * ∑ p ∈ P, residue f p := by
  have hrect := rectangle_boundary_integral_eq_residues hσ ht hP hc hd hmer
  have hI : (I : ℂ) ≠ 0 := I_ne_zero
  apply mul_left_cancel₀ hI
  rw [mul_add, mul_add, mul_div_cancel₀ _ hI]
  linear_combination hrect

/-- **The U-shaped contour shift on an infinite vertical line.** If `y ↦ f (σ₂ + y * I)` is
integrable on `ℝ` and `f` satisfies the hypotheses of `rectangle_boundary_integral_eq_residues` on
`[σ₁, σ₂] ×ℂ [t₁, t₂]`, then `∫ y : ℝ, f (σ₂ + y * I)` splits into the complementary tails
`∫ y in (Icc t₁ t₂)ᶜ, f (σ₂ + y * I)`, the left vertical edge, the horizontal term
`(top - bottom) / I`, and `2π · ∑ p ∈ P, residue f p`. -/
theorem integral_vertical_eq_uShaped_add_two_pi_mul_sum_residue {σ₁ σ₂ t₁ t₂ : ℝ}
    (hσ : σ₁ ≤ σ₂) (ht : t₁ ≤ t₂)
    {P : Finset ℂ} (hP : ∀ p ∈ P, p ∈ Ioo σ₁ σ₂ ×ℂ Ioo t₁ t₂) {f : ℂ → ℂ}
    (hc : ContinuousOn f (Icc σ₁ σ₂ ×ℂ Icc t₁ t₂ \ P))
    (hd : DifferentiableOn ℂ f (Ioo σ₁ σ₂ ×ℂ Ioo t₁ t₂ \ P))
    (hmer : ∀ p ∈ P, MeromorphicAt f p)
    (hint : Integrable (fun y : ℝ ↦ f (σ₂ + y * I))) :
    ∫ y : ℝ, f (σ₂ + y * I) =
      (∫ y in (Icc t₁ t₂)ᶜ, f (σ₂ + y * I)) +
      (∫ y : ℝ in t₁..t₂, f (σ₁ + y * I)) +
      ((∫ x : ℝ in σ₁..σ₂, f (x + t₂ * I)) - (∫ x : ℝ in σ₁..σ₂, f (x + t₁ * I))) / I +
      2 * π * ∑ p ∈ P, residue f p := by
  rw [← integral_add_compl measurableSet_Icc hint, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le ht,
    intervalIntegral_vertical_eq_uShaped_add_two_pi_mul_sum_residue hσ ht hP hc hd hmer]
  ring

/-- **Symmetric U-shaped contour shift on an infinite vertical line.** Specialization of
`integral_vertical_eq_uShaped_add_two_pi_mul_sum_residue` to the symmetric vertical window
`[-T, T]` (`0 ≤ T`), writing the tail set `(Icc (-T) T)ᶜ` as `{y : ℝ | T < |y|}` and the bottom
edge as `x ↦ f (x - T * I)`. -/
theorem integral_vertical_eq_uShaped_symm_add_two_pi_mul_sum_residue {σ₁ σ₂ T : ℝ}
    (hσ : σ₁ ≤ σ₂) (hT : 0 ≤ T)
    {P : Finset ℂ} (hP : ∀ p ∈ P, p ∈ Ioo σ₁ σ₂ ×ℂ Ioo (-T) T) {f : ℂ → ℂ}
    (hc : ContinuousOn f (Icc σ₁ σ₂ ×ℂ Icc (-T) T \ P))
    (hd : DifferentiableOn ℂ f (Ioo σ₁ σ₂ ×ℂ Ioo (-T) T \ P))
    (hmer : ∀ p ∈ P, MeromorphicAt f p)
    (hint : Integrable (fun y : ℝ ↦ f (σ₂ + y * I))) :
    ∫ y : ℝ, f (σ₂ + y * I) =
      (∫ y in {y : ℝ | T < |y|}, f (σ₂ + y * I)) +
      (∫ y : ℝ in (-T)..T, f (σ₁ + y * I)) +
      ((∫ x : ℝ in σ₁..σ₂, f (x + T * I)) - (∫ x : ℝ in σ₁..σ₂, f (x - T * I))) / I +
      2 * π * ∑ p ∈ P, residue f p := by
  have hset : (Icc (-T) T)ᶜ = {y : ℝ | T < |y|} := by
    ext y
    simp only [mem_compl_iff, mem_Icc, mem_ofPred_eq, ← abs_le, not_le]
  have hbot : (∫ x : ℝ in σ₁..σ₂, f (x + (-T : ℝ) * I)) =
      ∫ x : ℝ in σ₁..σ₂, f (x - T * I) := by
    refine intervalIntegral.integral_congr fun x _ ↦ ?_
    simp [sub_eq_add_neg]
  simpa only [hset, hbot] using
    integral_vertical_eq_uShaped_add_two_pi_mul_sum_residue hσ (by linarith) hP hc hd hmer hint

end TauCeti.Contour
