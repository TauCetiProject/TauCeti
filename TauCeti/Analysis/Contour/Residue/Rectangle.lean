/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.MellinTransform
public import TauCeti.Analysis.Contour.Curve.Rectangle
public import TauCeti.Analysis.Contour.Residue.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.Analysis.Contour.Cauchy.Rectangle
import TauCeti.Analysis.Contour.Residue.Cycle
import TauCeti.Analysis.Contour.Residue.Theorem
import TauCeti.Analysis.Contour.Winding.Number.Rectangle
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Basic
import TauCeti.Topology.MetricSpace.SeparatedBalls

/-!
# The residue theorem on a rectangle, vertical-line shifts, and U-shaped contour shifts

For a closed axis-parallel rectangle `R = Complex.Rectangle z w` with `z` its lower left corner,
and a function `f` analytic on `R` outside a finite set `S` that avoids `frontier R` and
meromorphic at the points of `S` inside `R`, the contour integral of `f` along the counterclockwise
boundary `Complex.rectBoundary z w` is `2πi` times the sum of the residues of `f` at the points of
`S` in `R`:

`∫ t in 0..4, γ' t • f (γ t) = 2πi · ∑_{s ∈ S ∩ R} Res_s f`.

Expanding the boundary into its four edges relates the difference of the right and left vertical
segments to the residue sum and the two horizontal segments. Letting the horizontal heights tend to
`±∞` when `f` is vertically integrable on `Re s = σ₀` and `Re s = σ₁` and the horizontal segment
integrals vanish in the limit gives the improper vertical-line contour shift

`∫ y, f (σ₁ + y * I) - ∫ y, f (σ₀ + y * I) = 2π · ∑_{s ∈ S} Res_s f`

for poles `S` in the open strip `σ₀ < Re s < σ₁`. Notice that the factor `I` from `ds = I dy` along
the vertical lines cancels the `I` in `2πi`.

We also prove the four-edge rectangle residue theorem and finite-height / infinite-line U-shaped
contour shifts without requiring an open neighbourhood of the closed rectangle: given a finite set
`P` in `(σ₁, σ₂) ×ℂ (t₁, t₂)` and `f : ℂ → ℂ` continuous on `[σ₁, σ₂] ×ℂ [t₁, t₂] \ P`, complex
differentiable on `(σ₁, σ₂) ×ℂ (t₁, t₂) \ P`, and meromorphic at each point of `P`,
`TauCeti.Contour.rectangle_boundary_integral_eq_sum_circleIntegral` reduces the four-edge boundary
integral to small circle integrals around `P`, which evaluate to `2πi · ∑ p ∈ P, residue f p`.

## Main results

* `TauCeti.Contour.classicalResidueTheorem_rectBoundary`: the residue theorem along
  `Complex.rectBoundary z w`.
* `TauCeti.Contour.rectangle_boundary_integral_eq_residues`: the four-edge boundary integral of `f`
  around `[σ₁, σ₂] ×ℂ [t₁, t₂]` equals `2πi · ∑ p ∈ P, residue f p`, assuming only continuity on
  the closed rectangle off `P` and complex differentiability on its interior off `P`.
* `TauCeti.Contour.integral_add_mul_I_sub_integral_add_mul_I_eq_two_pi_mul_sum_residue`: shifting an
  improper vertical-line integral across a strip with finitely many poles.
* `TauCeti.Contour.integral_add_mul_I_sub_integral_add_mul_I_eq_two_pi_mul_sum_residue_of_norm_le`:
  the same vertical-line shift under a uniform decay bound on horizontal segments.
* `TauCeti.Contour.vertical_integral_eq_uShaped_add_residues`: the finite-height U-shaped identity
  expressing the right vertical edge in terms of the left vertical edge, the horizontal edges, and
  the enclosed residues.
* `TauCeti.Contour.integral_vertical_eq_uShaped_add_residues`: the infinite-line U-shaped contour
  shift for an arbitrary vertical window `[t₁, t₂]`.
* `TauCeti.Contour.integral_vertical_eq_uShaped_symm_add_residues`: the symmetric `[-T, T]` form
  with tail integral over `{y : ℝ | T < |y|}`.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 4, §5 (the residue theorem and improper integrals).
* E. C. Titchmarsh, *The Theory of Functions*, §3.1 and §9.5.
* S. Lang, *Complex Analysis* (GTM 103), Ch. VI.
* A. Kontorovich and T. Tao, *PrimeNumberTheoremAnd* blueprint, §4.1 (Definitions 4.1.3–4.1.5,
  Lemmas 4.1.1–4.1.4, and Theorem 4.1.2, for simple poles).
-/

public section

open Set Complex Filter MeasureTheory Metric
open scoped Real Interval Topology

namespace TauCeti.Contour

open scoped Classical in
/-- **The classical residue theorem on a rectangle.** Let `z` be the lower left corner of the
closed rectangle `Rectangle z w`, and let `S` be a finite set avoiding `frontier (Rectangle z w)`.
If `f` is analytic at every point of `Rectangle z w \ S` and meromorphic at every point of
`S ∩ Rectangle z w`, then the contour integral of `f` along `rectBoundary z w` equals `2πi` times
the sum of the residues of `f` at the points of `S` lying in the rectangle. -/
theorem classicalResidueTheorem_rectBoundary {f : ℂ → ℂ} {S : Finset ℂ} {z w : ℂ}
    (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hf : ∀ x ∈ Rectangle z w, x ∉ S → AnalyticAt ℂ f x)
    (hmero : ∀ s ∈ S, s ∈ Rectangle z w → MeromorphicAt f s)
    (hS : ∀ s ∈ S, s ∉ frontier (Rectangle z w)) :
    ∫ t in (0 : ℝ)..4, deriv (rectBoundary z w) t • f (rectBoundary z w t) =
      2 * π * I * ∑ s ∈ S with s ∈ Rectangle z w, residue f s := by
  set T : Finset ℂ := S.filter (· ∈ Rectangle z w)
  -- Off `T`, `Rectangle z w` lies in `{x | AnalyticAt ℂ f x}`, while `T` lies in `interior R`.
  set U : Set ℂ := {x : ℂ | AnalyticAt ℂ f x} ∪ interior (Rectangle z w)
  have hU : IsOpen U := (isOpen_analyticAt ℂ f).union isOpen_interior
  have hRU : Rectangle z w ⊆ U := fun x hx ↦ by
    by_cases hxS : x ∈ S
    · exact Or.inr (by rw [← self_sdiff_frontier]; exact ⟨hx, hS x hxS⟩)
    · exact Or.inl (hf x hx hxS)
  have hdiff : DifferentiableOn ℂ f (U \ (↑T : Set ℂ)) := fun x ⟨hxU, hxT⟩ ↦ by
    rcases hxU with ha | hint
    · exact ha.differentiableAt.differentiableWithinAt
    · have hxR : x ∈ Rectangle z w := interior_subset hint
      have hxS : x ∉ S := fun h ↦ hxT (Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨h, hxR⟩))
      exact (hf x hxR hxS).differentiableAt.differentiableWithinAt
  have hmT : ∀ s ∈ T, s ∈ U → MeromorphicAt f s := fun s hs _ ↦
    hmero s (Finset.mem_filter.mp hs).1 (Finset.mem_filter.mp hs).2
  have hoff : ∀ t ∈ uIcc (0 : ℝ) 4, rectBoundary z w t ∉ (↑T : Set ℂ) := fun t _ ht ↦
    hS _ (Finset.mem_filter.mp (Finset.mem_coe.mp ht)).1 (rectBoundary_mem_frontier t)
  rw [classicalResidueTheorem_nullHomologous hU hdiff hmT (isPiecewiseC1On_rectBoundary z w)
    (fun t _ ↦ hRU (rectBoundary_mem_rectangle t)) (by simp) hoff
    (isNullHomologous_rectBoundary hRU)]
  refine congrArg _ (Finset.sum_congr rfl fun s hs ↦ ?_)
  have hsR := (Finset.mem_filter.mp hs).2
  have hsfr := hS s (Finset.mem_filter.mp hs).1
  rw [windingNumber_rectBoundary_eq_one (mem_Ioo_reProdIm_of_mem_rectangle hre him hsR hsfr),
    one_mul]

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
    fun p hp q hq hne ↦ disjoint_left.2 fun z hzp hzq ↦ by
      linarith [hsep p hp q hq hne, dist_triangle_left p q z, mem_closedBall.1 hzp,
        mem_closedBall.1 hzq]
  have hcirc := rectangle_boundary_integral_eq_sum_circleIntegral hσ ht hr hP_ball hdisj hc hd
  simp only [smul_eq_mul] at hcirc
  rw [hcirc, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  refine circleIntegral_eq_residue (mem_ball_self hr) (hmer p hp) fun z hz hzp ↦ ?_
  have hzUP : z ∈ U \ P := ⟨hP_ball p hp hz, fun hzP ↦
    disjoint_left.1 (hdisj hp hzP hzp.symm) hz (mem_closedBall_self hr.le)⟩
  exact hd.analyticAt ((hU.sdiff P.finite_toSet.isClosed).mem_nhds hzUP)

/-- **Shifting a vertical-line integral across poles.** Let `σ₀ ≤ σ₁` and let `S` be a finite set
of points in the open strip `σ₀ < Re s < σ₁`. Suppose `f` is analytic on the closed strip
`σ₀ ≤ Re z ≤ σ₁` away from `S`, meromorphic at each point of `S`, and integrable on the vertical
lines `Re z = σ₀` and `Re z = σ₁`. If the horizontal segment integrals at heights `-T` and `T` tend
to `0` as `T → +∞`, then

`(∫ y, f (σ₁ + y * I)) - (∫ y, f (σ₀ + y * I)) = 2π · ∑ s ∈ S, residue f s`. -/
theorem integral_add_mul_I_sub_integral_add_mul_I_eq_two_pi_mul_sum_residue
    {f : ℂ → ℂ} {S : Finset ℂ} {σ₀ σ₁ : ℝ} (hσ : σ₀ ≤ σ₁)
    (hf : ∀ z : ℂ, z.re ∈ Icc σ₀ σ₁ → z ∉ S → AnalyticAt ℂ f z)
    (hmero : ∀ s ∈ S, MeromorphicAt f s)
    (hS : ∀ s ∈ S, s.re ∈ Ioo σ₀ σ₁)
    (hint₀ : VerticalIntegrable f σ₀) (hint₁ : VerticalIntegrable f σ₁)
    (hbot : Tendsto (fun T : ℝ ↦ ∫ x : ℝ in σ₀..σ₁, f (x - T * I)) atTop (𝓝 0))
    (htop : Tendsto (fun T : ℝ ↦ ∫ x : ℝ in σ₀..σ₁, f (x + T * I)) atTop (𝓝 0)) :
    (∫ y : ℝ, f (σ₁ + y * I)) - (∫ y : ℝ, f (σ₀ + y * I)) =
      2 * π * ∑ s ∈ S, residue f s := by
  classical
  -- Choose a height `M > 0` strictly bounding `|Im s|` for every `s ∈ S`.
  set M : ℝ := 1 + ∑ s ∈ S, |s.im|
  have hSim : ∀ s ∈ S, |s.im| < M := fun s hs ↦ by
    have hle : |s.im| ≤ ∑ x ∈ S, |x.im| :=
      Finset.single_le_sum (fun x _ ↦ abs_nonneg x.im) hs
    linarith
  have hev : (fun T : ℝ ↦ (∫ x : ℝ in σ₀..σ₁, f (x - T * I)) -
      (∫ x : ℝ in σ₀..σ₁, f (x + T * I)) +
      I * (∫ y : ℝ in (-T)..T, f (σ₁ + y * I)) -
      I * (∫ y : ℝ in (-T)..T, f (σ₀ + y * I))) =ᶠ[atTop]
      fun _ ↦ 2 * π * I * ∑ s ∈ S, residue f s := by
    filter_upwards [eventually_ge_atTop M] with T hT
    have hT0 : 0 < T := lt_of_lt_of_le (by positivity) hT
    have hST (s : ℂ) (hs : s ∈ S) : s ∈ Ioo σ₀ σ₁ ×ℂ Ioo (-T) T :=
      ⟨hS s hs, abs_lt.mp ((hSim s hs).trans_le hT)⟩
    have hc : ContinuousOn f (Icc σ₀ σ₁ ×ℂ Icc (-T) T \ S) := fun z hz ↦
      (hf z hz.1.1 (by simpa using hz.2)).continuousAt.continuousWithinAt
    have hd : DifferentiableOn ℂ f (Ioo σ₀ σ₁ ×ℂ Ioo (-T) T \ S) := fun z hz ↦
      (hf z (Ioo_subset_Icc_self hz.1.1) (by simpa using hz.2)).differentiableAt
        |>.differentiableWithinAt
    have hedge := rectangle_boundary_integral_eq_residues hσ (by linarith : -T ≤ T) hST hc hd hmero
    have hsub : ∀ x : ℝ, (x : ℂ) + (-T : ℝ) * I = (x : ℂ) - T * I := fun x ↦ by
      push_cast; ring
    simp_rw [hsub] at hedge
    exact hedge
  have hlim : Tendsto (fun T : ℝ ↦ (∫ x : ℝ in σ₀..σ₁, f (x - T * I)) -
      (∫ x : ℝ in σ₀..σ₁, f (x + T * I)) +
      I * (∫ y : ℝ in (-T)..T, f (σ₁ + y * I)) -
      I * (∫ y : ℝ in (-T)..T, f (σ₀ + y * I))) atTop
      (𝓝 ((0 : ℂ) - 0 + I * (∫ y : ℝ, f (σ₁ + y * I)) -
        I * (∫ y : ℝ, f (σ₀ + y * I)))) :=
    ((hbot.sub htop).add ((intervalIntegral_tendsto_integral hint₁ tendsto_neg_atTop_atBot
      tendsto_id).const_mul I)).sub
      ((intervalIntegral_tendsto_integral hint₀ tendsto_neg_atTop_atBot tendsto_id).const_mul I)
  have heq := tendsto_nhds_unique hlim (tendsto_const_nhds.congr' hev.symm)
  apply mul_left_cancel₀ I_ne_zero
  linear_combination heq

/-- **Shifting a vertical-line integral under uniform horizontal decay.** If on horizontal
segments `[σ₀, σ₁] ± i T` the integrand is eventually bounded by `B T` with `B T → 0` as
`T → +∞`, the horizontal segment integrals vanish in the limit and
`integral_add_mul_I_sub_integral_add_mul_I_eq_two_pi_mul_sum_residue` applies. -/
theorem integral_add_mul_I_sub_integral_add_mul_I_eq_two_pi_mul_sum_residue_of_norm_le
    {f : ℂ → ℂ} {S : Finset ℂ} {σ₀ σ₁ : ℝ} {B : ℝ → ℝ} (hσ : σ₀ ≤ σ₁)
    (hf : ∀ z : ℂ, z.re ∈ Icc σ₀ σ₁ → z ∉ S → AnalyticAt ℂ f z)
    (hmero : ∀ s ∈ S, MeromorphicAt f s)
    (hS : ∀ s ∈ S, s.re ∈ Ioo σ₀ σ₁)
    (hint₀ : VerticalIntegrable f σ₀) (hint₁ : VerticalIntegrable f σ₁)
    (hB : Tendsto B atTop (𝓝 0))
    (hbound : ∀ᶠ (T : ℝ) in atTop, ∀ x ∈ Icc σ₀ σ₁,
      ‖f ((x : ℂ) + T * I)‖ ≤ B T ∧ ‖f ((x : ℂ) - T * I)‖ ≤ B T) :
    (∫ y : ℝ, f (σ₁ + y * I)) - (∫ y : ℝ, f (σ₀ + y * I)) =
      2 * π * ∑ s ∈ S, residue f s := by
  have hseg (g : ℝ → ℝ → ℂ)
      (hg : ∀ᶠ (T : ℝ) in atTop, ∀ x ∈ Icc σ₀ σ₁, ‖g T x‖ ≤ B T) :
      Tendsto (fun T : ℝ ↦ ∫ x : ℝ in σ₀..σ₁, g T x) atTop (𝓝 0) :=
    TauCeti.intervalIntegral.tendsto_integral_nhds_zero_of_ae_norm_le hB <|
      hg.mono fun T hTB ↦ Eventually.of_forall fun x hx ↦
        hTB x (Ioc_subset_Icc_self (by rwa [uIoc_of_le hσ] at hx))
  exact integral_add_mul_I_sub_integral_add_mul_I_eq_two_pi_mul_sum_residue hσ hf hmero hS
    hint₀ hint₁
    (hseg (fun T x ↦ f ((x : ℂ) - T * I)) (hbound.mono fun T hT x hx ↦ (hT x hx).2))
    (hseg (fun T x ↦ f ((x : ℂ) + T * I)) (hbound.mono fun T hT x hx ↦ (hT x hx).1))

/-- **Finite-height U-shaped contour identity.** Under the hypotheses of
`rectangle_boundary_integral_eq_residues` (with no integrability hypothesis), the right vertical
edge integral equals the left vertical edge integral plus the horizontal difference
`(top - bottom) / I` plus `2π · ∑ p ∈ P, residue f p`. -/
theorem vertical_integral_eq_uShaped_add_residues {σ₁ σ₂ t₁ t₂ : ℝ} (hσ : σ₁ ≤ σ₂) (ht : t₁ ≤ t₂)
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
theorem integral_vertical_eq_uShaped_add_residues {σ₁ σ₂ t₁ t₂ : ℝ} (hσ : σ₁ ≤ σ₂) (ht : t₁ ≤ t₂)
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
    vertical_integral_eq_uShaped_add_residues hσ ht hP hc hd hmer]
  ring

/-- **Symmetric U-shaped contour shift on an infinite vertical line.** Specialization of
`integral_vertical_eq_uShaped_add_residues` to the symmetric vertical window `[-T, T]` (`0 ≤ T`),
writing the tail set `(Icc (-T) T)ᶜ` as `{y : ℝ | T < |y|}` and the bottom edge as
`x ↦ f (x - T * I)`. -/
theorem integral_vertical_eq_uShaped_symm_add_residues {σ₁ σ₂ T : ℝ} (hσ : σ₁ ≤ σ₂) (hT : 0 ≤ T)
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
    integral_vertical_eq_uShaped_add_residues hσ (by linarith) hP hc hd hmer hint

end TauCeti.Contour
