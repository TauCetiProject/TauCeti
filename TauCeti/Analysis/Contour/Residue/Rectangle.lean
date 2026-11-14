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
import TauCeti.Analysis.Contour.Residue.Cycle
import TauCeti.Analysis.Contour.Winding.Number.Rectangle

/-!
# The residue theorem on a rectangle and vertical-line contour shifts

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

## Main results

* `TauCeti.Contour.classicalResidueTheorem_rectBoundary`: the residue theorem along
  `Complex.rectBoundary z w`.
* `TauCeti.Contour.edgeIntegral_rectBoundary_eq_sum_residue`: the unpacked four-edge residue
  formula on `Rectangle (σ₀ + T₁ * I) (σ₁ + T₂ * I)`.
* `TauCeti.Contour.verticalIntegral_sub_verticalIntegral_eq_two_pi_mul_sum_residue`: shifting an
  improper vertical-line integral across a strip with finitely many poles.
* `TauCeti.Contour.verticalIntegral_sub_verticalIntegral_eq_of_norm_le`: the same vertical-line
  shift under a uniform decay bound on horizontal segments.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 4, §5 (the residue theorem and improper integrals).
* E. C. Titchmarsh, *The Theory of Functions*, §3.1 and §9.5.
-/

public section

open Set Complex Filter MeasureTheory
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

open scoped Classical in
/-- **The four-edge residue formula on an axis-parallel rectangle.** For `σ₀ ≤ σ₁` and `T₁ ≤ T₂`,
if `f` is analytic on `Icc σ₀ σ₁ ×ℂ Icc T₁ T₂ \ S` and meromorphic at the points of `S` in that
rectangle, and `S` avoids the boundary of the rectangle, then the signed sum of the four edge
integrals equals `2πi` times the sum of the residues of `f` in the open rectangle
`Ioo σ₀ σ₁ ×ℂ Ioo T₁ T₂`. -/
theorem edgeIntegral_rectBoundary_eq_sum_residue {f : ℂ → ℂ} {S : Finset ℂ}
    {σ₀ σ₁ T₁ T₂ : ℝ} (hσ : σ₀ ≤ σ₁) (hT : T₁ ≤ T₂)
    (hf : ∀ x ∈ Icc σ₀ σ₁ ×ℂ Icc T₁ T₂, x ∉ S → AnalyticAt ℂ f x)
    (hmero : ∀ s ∈ S, s ∈ Icc σ₀ σ₁ ×ℂ Icc T₁ T₂ → MeromorphicAt f s)
    (hS : ∀ s ∈ S, s ∉ frontier (Rectangle ((σ₀ : ℂ) + T₁ * I) ((σ₁ : ℂ) + T₂ * I))) :
    (∫ x : ℝ in σ₀..σ₁, f (x + T₁ * I)) - (∫ x : ℝ in σ₀..σ₁, f (x + T₂ * I)) +
        I * (∫ y : ℝ in T₁..T₂, f (σ₁ + y * I)) -
        I * (∫ y : ℝ in T₁..T₂, f (σ₀ + y * I)) =
      2 * π * I * ∑ s ∈ S with s ∈ Ioo σ₀ σ₁ ×ℂ Ioo T₁ T₂, residue f s := by
  set z : ℂ := (σ₀ : ℂ) + T₁ * I
  set w : ℂ := (σ₁ : ℂ) + T₂ * I
  have hzre : z.re = σ₀ := by simp [z]
  have hzim : z.im = T₁ := by simp [z]
  have hwre : w.re = σ₁ := by simp [w]
  have hwim : w.im = T₂ := by simp [w]
  have hrect : Rectangle z w = Icc σ₀ σ₁ ×ℂ Icc T₁ T₂ := by
    rw [Rectangle, hzre, hzim, hwre, hwim, uIcc_of_le hσ, uIcc_of_le hT]
  have hcont : ContinuousOn f (frontier (Rectangle z w)) := fun x hx ↦
    (hf x (hrect ▸ (isClosed_rectangle z w).frontier_subset hx)
      fun hxS ↦ hS x hxS hx).continuousAt.continuousWithinAt
  have hres := classicalResidueTheorem_rectBoundary (hzre.trans_le (hσ.trans_eq hwre.symm))
    (hzim.trans_le (hT.trans_eq hwim.symm)) (hrect ▸ hf) (hrect ▸ hmero) hS
  rw [integral_rectBoundary hcont, hzre, hzim, hwre, hwim] at hres
  simp only [smul_eq_mul] at hres
  rw [hres]
  refine congrArg _ (Finset.sum_congr (Finset.ext fun s ↦ ?_) fun _ _ ↦ rfl)
  simp only [Finset.mem_filter, and_congr_right_iff]
  intro hs
  constructor
  · exact fun hsR ↦ hzre ▸ hwre ▸ hzim ▸ hwim ▸ mem_Ioo_reProdIm_of_mem_rectangle
      (hzre.trans_le (hσ.trans_eq hwre.symm)) (hzim.trans_le (hT.trans_eq hwim.symm)) hsR (hS s hs)
  · intro hsI
    rw [hrect]
    exact ⟨Ioo_subset_Icc_self hsI.1, Ioo_subset_Icc_self hsI.2⟩

/-- **Shifting a vertical-line integral across poles.** Let `σ₀ ≤ σ₁` and let `S` be a finite set
of points in the open strip `σ₀ < Re s < σ₁`. Suppose `f` is analytic on the closed strip
`σ₀ ≤ Re z ≤ σ₁` away from `S`, meromorphic at each point of `S`, and integrable on the vertical
lines `Re z = σ₀` and `Re z = σ₁`. If the horizontal segment integrals at heights `-T` and `T` tend
to `0` as `T → +∞`, then

`(∫ y, f (σ₁ + y * I)) - (∫ y, f (σ₀ + y * I)) = 2π · ∑ s ∈ S, residue f s`. -/
theorem verticalIntegral_sub_verticalIntegral_eq_two_pi_mul_sum_residue
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
    have hfr (s : ℂ) (hs : s ∈ S) :
        s ∉ frontier (Rectangle ((σ₀ : ℂ) + (-T : ℝ) * I) ((σ₁ : ℂ) + T * I)) := by
      have hint : s ∈ interior (Rectangle ((σ₀ : ℂ) + (-T : ℝ) * I) ((σ₁ : ℂ) + T * I)) := by
        rw [interior_rectangle (by simpa using hσ) (by simp; linarith)]
        simpa using hST s hs
      exact disjoint_left.1 disjoint_interior_frontier hint
    have hedge := edgeIntegral_rectBoundary_eq_sum_residue hσ (by linarith : -T ≤ T)
      (fun x hx hxS ↦ hf x hx.1 hxS) (fun s hs _ ↦ hmero s hs) hfr
    have hsub : ∀ x : ℝ, (x : ℂ) + (-T : ℝ) * I = (x : ℂ) - T * I := fun x ↦ by
      push_cast; ring
    simp_rw [hsub] at hedge
    rw [hedge, Finset.filter_true_of_mem hST]
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
`verticalIntegral_sub_verticalIntegral_eq_two_pi_mul_sum_residue` applies. -/
theorem verticalIntegral_sub_verticalIntegral_eq_of_norm_le
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
      Tendsto (fun T : ℝ ↦ ∫ x : ℝ in σ₀..σ₁, g T x) atTop (𝓝 0) := by
    refine tendsto_zero_iff_norm_tendsto_zero.mpr
      (squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_
        (by simpa using hB.const_mul (σ₁ - σ₀)))
    filter_upwards [hg] with T hTB
    have hb : ∀ x ∈ uIoc σ₀ σ₁, ‖g T x‖ ≤ B T := fun x hx ↦
      hTB x (Ioc_subset_Icc_self (by rwa [uIoc_of_le hσ] at hx))
    simpa [abs_of_nonneg (sub_nonneg.mpr hσ), mul_comm] using
      intervalIntegral.norm_integral_le_of_norm_le_const hb
  exact verticalIntegral_sub_verticalIntegral_eq_two_pi_mul_sum_residue hσ hf hmero hS hint₀ hint₁
    (hseg (fun T x ↦ f ((x : ℂ) - T * I)) (hbound.mono fun T hT x hx ↦ (hT x hx).2))
    (hseg (fun T x ↦ f ((x : ℂ) + T * I)) (hbound.mono fun T hT x hx ↦ (hT x hx).1))

end TauCeti.Contour
