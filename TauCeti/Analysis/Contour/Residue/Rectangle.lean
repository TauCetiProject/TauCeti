/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Curve.Rectangle
public import TauCeti.Analysis.Contour.Residue.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import TauCeti.Analysis.Contour.Cauchy.Rectangle
import TauCeti.Analysis.Contour.Residue.Theorem

/-!
# The residue theorem on rectangles and U-shaped contour shifts

For a closed rectangle `[σ₁, σ₂] ×ℂ [t₁, t₂]` (`σ₁ ≤ σ₂`, `t₁ ≤ t₂`) and a function `f : ℂ → ℂ`
that is continuous on the closed rectangle minus a finite set `P` in the open rectangle, complex
differentiable on the open rectangle minus `P`, and meromorphic at each point of `P`, the
counterclockwise boundary integral of `f` along the rectangle equals `2πi · ∑_{p ∈ P} Res_p f`.
No open neighbourhood of the closed rectangle is required.

Four forms are provided:
* the four-edge boundary identity matching Mathlib's `Complex.integral_boundary_rect_eq_zero_*`;
* the parametrized curve form along `Complex.rectBoundary z w`, allowing `S` to include points
  outside the rectangle provided it avoids the frontier (mirroring
  `TauCeti.Contour.argumentPrinciple_rectBoundary`);
* the finite-height U-shaped contour identity expressing the right vertical edge
  `∫ y in t₁..t₂, f (σ₂ + y * I)` in terms of the left edge, the top and bottom horizontal edges,
  and the residues inside the rectangle;
* the full vertical-line U-shaped contour shift splitting `∫ y : ℝ, f (σ₂ + y * I)` into the
  outer tails over `(Icc t₁ t₂)ᶜ` plus the left edge, horizontal edges, and residues, as used in
  Perron-type contour shifts for Dirichlet series and L-functions.

## Main results

* `TauCeti.Contour.integral_boundary_rect_eq_sum_residue`: the rectangle residue theorem in
  four-edge form.
* `TauCeti.Contour.classicalResidueTheorem_rectBoundary`: the rectangle residue theorem along
  `Complex.rectBoundary z w`, summing over poles inside the rectangle.
* `TauCeti.Contour.integral_vertical_eq_add_horizontal_add_sum_residue`: the finite-height
  U-shaped contour identity.
* `TauCeti.Contour.integral_vertical_eq_compl_add_horizontal_add_sum_residue`: the full
  vertical-line U-shaped contour shift.

## References

* S. Lang, *Complex Analysis* (GTM 103), Ch. VI.
* A. Kontorovich, T. Tao and contributors, *Prime Number Theorem And …*, blueprint, §4.1
  (rectangle residue theorem and U-shaped contours).
-/

public section

noncomputable section

open Complex MeasureTheory Metric Set
open scoped Interval Real

namespace TauCeti.Contour

/-- **The residue theorem on a rectangle in four-edge form.** Let `σ₁ ≤ σ₂`, `t₁ ≤ t₂`, and let
`P` be a finite subset of the open rectangle `(σ₁, σ₂) ×ℂ (t₁, t₂)`. If `f : ℂ → ℂ` is continuous
on `[σ₁, σ₂] ×ℂ [t₁, t₂] \ P`, complex differentiable on `(σ₁, σ₂) ×ℂ (t₁, t₂) \ P`, and
meromorphic at each point of `P`, then the counterclockwise boundary integral of `f` around the
rectangle equals `2πi · ∑ p ∈ P, residue f p`. -/
theorem integral_boundary_rect_eq_sum_residue
    {σ₁ σ₂ t₁ t₂ : ℝ} (hσ : σ₁ ≤ σ₂) (ht : t₁ ≤ t₂)
    {P : Finset ℂ} (hP : ∀ p ∈ P, p ∈ Ioo σ₁ σ₂ ×ℂ Ioo t₁ t₂)
    {f : ℂ → ℂ}
    (hc : ContinuousOn f (Icc σ₁ σ₂ ×ℂ Icc t₁ t₂ \ P))
    (hd : DifferentiableOn ℂ f (Ioo σ₁ σ₂ ×ℂ Ioo t₁ t₂ \ P))
    (hmero : ∀ p ∈ P, MeromorphicAt f p) :
    (∫ x : ℝ in σ₁..σ₂, f (x + t₁ * I)) - (∫ x : ℝ in σ₁..σ₂, f (x + t₂ * I)) +
        I * (∫ y : ℝ in t₁..t₂, f (σ₂ + y * I)) - I * (∫ y : ℝ in t₁..t₂, f (σ₁ + y * I)) =
      2 * π * I * ∑ p ∈ P, residue f p := by
  classical
  -- Around each `p ∈ P`, choose a closed disc inside the open rectangle avoiding all other points
  -- of `P`.
  have hex : ∀ p : ℂ, p ∈ P →
      ∃ r : ℝ, 0 < r ∧ closedBall p r ⊆ (Ioo σ₁ σ₂ ×ℂ Ioo t₁ t₂) \ (P.erase p : Set ℂ) := by
    intro p hp
    have hopen : IsOpen ((Ioo σ₁ σ₂ ×ℂ Ioo t₁ t₂) \ (P.erase p : Set ℂ)) :=
      (isOpen_Ioo.reProdIm isOpen_Ioo).sdiff (P.erase p).finite_toSet.isClosed
    have hmem : p ∈ (Ioo σ₁ σ₂ ×ℂ Ioo t₁ t₂) \ (P.erase p : Set ℂ) :=
      ⟨hP p hp, by simp⟩
    exact nhds_basis_closedBall.mem_iff.mp (hopen.mem_nhds hmem)
  let r : ℂ → ℝ := fun p ↦ if hp : p ∈ P then (hex p hp).choose else 0
  have hr : ∀ p ∈ P, 0 < r p := fun p hp ↦ by
    simp only [r, dite_eq_left, hp]
    exact (hex p hp).choose_spec.1
  have hr_sub : ∀ p ∈ P, closedBall p (r p) ⊆ (Ioo σ₁ σ₂ ×ℂ Ioo t₁ t₂) \ (P.erase p : Set ℂ) :=
    fun p hp ↦ by
      simp only [r, dite_eq_left, hp]
      exact (hex p hp).choose_spec.2
  have hcircle := integral_boundary_rect_eq_sum_circleIntegral hσ ht hr
    (fun p hp ↦ (hr_sub p hp).trans sdiff_subset)
    (fun p hp p' hp' hne hmem ↦ (hr_sub p hp hmem).2 (by simp [hp', hne.symm]))
    hc hd
  simp only [smul_eq_mul] at hcircle
  rw [hcircle, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  have hU_open : IsOpen (Ioo σ₁ σ₂ ×ℂ Ioo t₁ t₂ \ (P : Set ℂ)) :=
    (isOpen_Ioo.reProdIm isOpen_Ioo).sdiff P.finite_toSet.isClosed
  refine circleIntegral_eq_residue (mem_ball_self (hr p hp)) (hmero p hp) fun z hz hzp ↦ ?_
  have hzU : z ∈ Ioo σ₁ σ₂ ×ℂ Ioo t₁ t₂ \ (P : Set ℂ) := by
    have hz' := hr_sub p hp hz
    refine ⟨hz'.1, fun hzP ↦ hz'.2 ?_⟩
    exact Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hzp, hzP⟩)
  exact hd.analyticAt (hU_open.mem_nhds hzU)

open scoped Classical in
/-- **The residue theorem along the boundary parametrization of a rectangle.** Let `z` be the lower
left corner of `Rectangle z w`, and let `S` be a finite set avoiding the frontier of the rectangle.
If `f : ℂ → ℂ` is continuous on `Rectangle z w \ S`, complex differentiable on the open rectangle
`Ioo z.re w.re ×ℂ Ioo z.im w.im \ S`, and meromorphic at each point of `S` inside the rectangle,
then the contour integral of `f` along `Complex.rectBoundary z w` equals `2πi` times the sum of the
residues of `f` at the points of `S` in the rectangle.

Nothing is assumed about `f` at points of `S` outside `Rectangle z w`. -/
theorem classicalResidueTheorem_rectBoundary {f : ℂ → ℂ} {S : Finset ℂ} {z w : ℂ}
    (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hS : ∀ s ∈ S, s ∉ frontier (Rectangle z w))
    (hc : ContinuousOn f (Rectangle z w \ (↑S : Set ℂ)))
    (hd : DifferentiableOn ℂ f (Ioo z.re w.re ×ℂ Ioo z.im w.im \ (↑S : Set ℂ)))
    (hmero : ∀ s ∈ S, s ∈ Rectangle z w → MeromorphicAt f s) :
    ∫ t in (0 : ℝ)..4, deriv (rectBoundary z w) t • f (rectBoundary z w t) =
      2 * π * I * ∑ s ∈ S with s ∈ Rectangle z w, residue f s := by
  have hfr : ContinuousOn f (frontier (Rectangle z w)) :=
    hc.mono fun s hs ↦
      ⟨(isClosed_rectangle z w).frontier_subset hs, fun hsS ↦ hS s hsS hs⟩
  rw [integral_rectBoundary hfr]
  simp only [smul_eq_mul]
  have hrect : Icc z.re w.re ×ℂ Icc z.im w.im = Rectangle z w := by
    rw [Rectangle, uIcc_of_le hre, uIcc_of_le him]
  refine integral_boundary_rect_eq_sum_residue hre him
    (P := S.filter (· ∈ Rectangle z w))
    (fun p hp ↦ by
      obtain ⟨hpS, hpR⟩ := Finset.mem_filter.mp hp
      exact mem_Ioo_reProdIm_of_mem_rectangle hre him hpR (hS p hpS))
    (hc.mono fun s hs ↦ ?_)
    (hd.mono fun s hs ↦ ?_)
    (fun p hp ↦ by
      obtain ⟨hpS, hpR⟩ := Finset.mem_filter.mp hp
      exact hmero p hpS hpR)
  · rw [hrect] at hs
    refine ⟨hs.1, fun hsS ↦ hs.2 ?_⟩
    exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hsS, hs.1⟩)
  · refine ⟨hs.1, fun hsS ↦ hs.2 ?_⟩
    have hsR : s ∈ Rectangle z w := by
      rw [← hrect]
      exact ⟨Ioo_subset_Icc_self hs.1.1, Ioo_subset_Icc_self hs.1.2⟩
    exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hsS, hsR⟩)

/-- **Finite-height U-shaped contour shift.** For `σ₁ ≤ σ₂`, `t₁ ≤ t₂`, and a finite set `P` inside
the open rectangle `(σ₁, σ₂) ×ℂ (t₁, t₂)`, if `f : ℂ → ℂ` is continuous on
`[σ₁, σ₂] ×ℂ [t₁, t₂] \ P`, complex differentiable on `(σ₁, σ₂) ×ℂ (t₁, t₂) \ P`, and meromorphic
at each point of `P`, then the right vertical edge integral `∫ y in t₁..t₂, f (σ₂ + y * I)` equals
the left vertical edge plus the top-minus-bottom horizontal difference divided by `I`, plus `2π`
times the sum of the residues inside the rectangle. No integrability on `ℝ` is needed. -/
theorem integral_vertical_eq_add_horizontal_add_sum_residue
    {σ₁ σ₂ t₁ t₂ : ℝ} (hσ : σ₁ ≤ σ₂) (ht : t₁ ≤ t₂)
    {P : Finset ℂ} (hP : ∀ p ∈ P, p ∈ Ioo σ₁ σ₂ ×ℂ Ioo t₁ t₂)
    {f : ℂ → ℂ}
    (hc : ContinuousOn f (Icc σ₁ σ₂ ×ℂ Icc t₁ t₂ \ P))
    (hd : DifferentiableOn ℂ f (Ioo σ₁ σ₂ ×ℂ Ioo t₁ t₂ \ P))
    (hmero : ∀ p ∈ P, MeromorphicAt f p) :
    ∫ y : ℝ in t₁..t₂, f (σ₂ + y * I) =
      (∫ y : ℝ in t₁..t₂, f (σ₁ + y * I)) +
        ((∫ x : ℝ in σ₁..σ₂, f (x + t₂ * I)) - (∫ x : ℝ in σ₁..σ₂, f (x + t₁ * I))) / I +
        2 * π * ∑ p ∈ P, residue f p := by
  have h := integral_boundary_rect_eq_sum_residue hσ ht hP hc hd hmero
  refine mul_left_cancel₀ Complex.I_ne_zero ?_
  rw [mul_add, mul_add, mul_div_cancel₀ _ Complex.I_ne_zero]
  linear_combination h

/-- **Vertical-line U-shaped contour shift.** If `y ↦ f (σ₂ + y * I)` is integrable on `ℝ` and `f`
satisfies the rectangle residue theorem hypotheses on `[σ₁, σ₂] ×ℂ [t₁, t₂]`, then the full
vertical-line integral `∫ y : ℝ, f (σ₂ + y * I)` equals the outer tails over `(Icc t₁ t₂)ᶜ` plus
the left vertical edge `∫ y in t₁..t₂, f (σ₁ + y * I)`, the horizontal contribution
`(∫ x in σ₁..σ₂, f (x + t₂ * I) - ∫ x in σ₁..σ₂, f (x + t₁ * I)) / I`, and
`2π · ∑ p ∈ P, residue f p`.

For a symmetric cutoff `t₁ = -T`, `t₂ = T` (`0 ≤ T`), the tail domain `(Icc (-T) T)ᶜ` is
`{y : ℝ | T < |y|}`. -/
theorem integral_vertical_eq_compl_add_horizontal_add_sum_residue
    {σ₁ σ₂ t₁ t₂ : ℝ} (hσ : σ₁ ≤ σ₂) (ht : t₁ ≤ t₂)
    {P : Finset ℂ} (hP : ∀ p ∈ P, p ∈ Ioo σ₁ σ₂ ×ℂ Ioo t₁ t₂)
    {f : ℂ → ℂ}
    (hc : ContinuousOn f (Icc σ₁ σ₂ ×ℂ Icc t₁ t₂ \ P))
    (hd : DifferentiableOn ℂ f (Ioo σ₁ σ₂ ×ℂ Ioo t₁ t₂ \ P))
    (hmero : ∀ p ∈ P, MeromorphicAt f p)
    (hint : Integrable (fun y : ℝ ↦ f (σ₂ + y * I))) :
    ∫ y : ℝ, f (σ₂ + y * I) =
      (∫ y in (Icc t₁ t₂)ᶜ, f (σ₂ + y * I)) +
        (∫ y : ℝ in t₁..t₂, f (σ₁ + y * I)) +
        ((∫ x : ℝ in σ₁..σ₂, f (x + t₂ * I)) - (∫ x : ℝ in σ₁..σ₂, f (x + t₁ * I))) / I +
        2 * π * ∑ p ∈ P, residue f p := by
  have hsplit := integral_add_compl (s := Icc t₁ t₂) measurableSet_Icc hint
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht] at hsplit
  rw [← hsplit, add_comm, integral_vertical_eq_add_horizontal_add_sum_residue hσ ht hP hc hd hmero]
  ring

end TauCeti.Contour

end
