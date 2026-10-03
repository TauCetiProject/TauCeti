/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Harmonic.MeanValue
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.MeasureTheory.Integral.NormRpow

/-!
# The mean-value inequality for `Δ w ≥ -A w²`

Let `E` be a real inner product space of dimension two with an additive Haar measure `μ`, and let
`w ≥ 0` be a `C²` function on a ball `ball x₀ r` with

`Δ w ≥ -A w²`.

The **mean-value inequality** says that if the integral of `w` over the ball is small,
`8 A ∫ w < μ (ball 0 1)`, then `w` is controlled at the centre by its average:

`μ (ball x₀ r) * w x₀ ≤ 8 * ∫ x in ball x₀ r, w x ∂μ`.

For Lebesgue measure on `ℂ`, with `r > 0` and `A > 0`, this is `w x₀ ≤ 8 / (π r²) ∫ w` under
`∫ w < π / (8 A)`. Applied to the energy density `w = |du|²` of a `J`-holomorphic curve, which
satisfies such a differential inequality, it bounds the derivative of a curve with small energy
pointwise; this is the analytic input to bubbling and Gromov compactness. The nonlinearity `w²` is
critical in dimension two: both sides of the hypothesis and the conclusion scale in the same way
under dilations, which is why the smallness condition does not depend on `r`.

The proof has two steps.

* **A quadratic correction.** If `Δ w ≥ -K` on `ball x₀ R`, then `w + K ‖x - x₀‖² / (2n)` has
  nonnegative Laplacian, and the sub-mean-value inequality
  `TauCeti.mul_le_setIntegral_ball_of_laplacian_nonneg` together with
  `∫ x in ball x₀ R, ‖x - x₀‖² = n R² μ (ball x₀ R) / (n + 2)` gives
  `μ (ball x₀ R) * w x₀ ≤ ∫ w + K R² μ (ball x₀ R) / (2 (n + 2))`, in any dimension `n`.
* **Choosing the centre.** The continuous function `(r - ρ)² w z` on the compact set
  `{(ρ, z) | 0 ≤ ρ ≤ r, dist z x₀ ≤ ρ}` attains its maximum at some `(ρ, z)`. With
  `c = w z` and `ε = (r - ρ) / 2`, maximality gives `r² w x₀ ≤ 4 ε² c` and `w ≤ 4 c` on
  `closedBall z ε`, so `Δ w ≥ -16 A c²` there. The first step on a ball `ball z δ` with `δ ≤ ε`
  and `4 A c δ² ≤ 1` gives `δ² c μ (ball 0 1) ≤ 2 ∫ w`. If `δ = ε` is allowed, this together with
  `r² w x₀ ≤ 4 ε² c` is the claim; otherwise `δ² = 1 / (4 A c)` contradicts the smallness of
  `∫ w`.

## Main declarations

* `TauCeti.mul_le_setIntegral_ball_add_of_neg_le_laplacian`: the mean-value inequality for
  `Δ w ≥ -K`, in any dimension.
* `TauCeti.mul_le_eight_mul_setIntegral_ball_of_neg_mul_sq_le_laplacian`: **the mean-value
  inequality** for `Δ w ≥ -A w²` in dimension two.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Section 4.3 (the mean-value inequality).
-/

public section

namespace TauCeti

open InnerProductSpace Laplacian MeasureTheory Metric Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- **The mean-value inequality for `Δ w ≥ -K`.** If `w` is `C²` on the ball `ball x₀ R`,
continuous on its closure, and `Δ w ≥ -K` on the ball, then, in dimension `n`,
`μ (ball x₀ R) * w x₀ ≤ ∫ x in ball x₀ R, w x ∂μ + K R² / (2 (n + 2)) * μ (ball x₀ R)`. -/
theorem mul_le_setIntegral_ball_add_of_neg_le_laplacian {w : E → ℝ} {x₀ : E}
    {R K : ℝ} (hw : ContDiffOn ℝ 2 w (ball x₀ R)) (hwc : ContinuousOn w (closedBall x₀ R))
    (hΔ : ∀ x ∈ ball x₀ R, -K ≤ Δ w x) :
    μ.real (ball x₀ R) * w x₀ ≤ ∫ x in ball x₀ R, w x ∂μ +
      K * R ^ 2 / (2 * (Module.finrank ℝ E + 2)) * μ.real (ball x₀ R) := by
  rcases le_or_gt R 0 with hR | hR
  · simp [ball_eq_empty.mpr hR]
  rcases subsingleton_or_nontrivial E with hE | hE
  · -- In the trivial space `w` is constant, so `Δ w = 0` and `0 ≤ K`.
    have hconst : ∀ x, w x = w x₀ := fun x ↦ congrArg w (Subsingleton.elim x x₀)
    have hK : 0 ≤ K := by
      have h := hΔ x₀ (mem_ball_self hR)
      have hw : w = fun _ ↦ w x₀ := funext hconst
      rw [hw, laplacian_const, Pi.zero_apply] at h
      linarith
    rw [setIntegral_congr_fun measurableSet_ball (g := fun _ ↦ w x₀) fun x _ ↦ hconst x,
      setIntegral_const, smul_eq_mul, le_add_iff_nonneg_right]
    exact mul_nonneg (div_nonneg (mul_nonneg hK (sq_nonneg R)) (by positivity)) measureReal_nonneg
  have hn : 0 < (Module.finrank ℝ E : ℝ) := Nat.cast_pos.mpr Module.finrank_pos
  set c : ℝ := K / (2 * Module.finrank ℝ E) with hc_def
  -- The quadratic correction `‖x - x₀‖ ^ 2`, with Laplacian `2 n`.
  have hq : ContDiff ℝ 2 fun x : E ↦ ‖x - x₀‖ ^ 2 :=
    (contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)
  have hΔq : ∀ x, Δ (fun x : E ↦ ‖x - x₀‖ ^ 2) x = 2 * Module.finrank ℝ E := fun x ↦ by
    have h := congrFun (laplacian_comp_add_right (fun y : E ↦ ‖y‖ ^ 2) (-x₀)) x
    simp only [← sub_eq_add_neg] at h
    rw [h, laplacian_norm_sq]
  have hv : ContDiffOn ℝ 2 (fun x ↦ w x + c * ‖x - x₀‖ ^ 2) (ball x₀ R) :=
    hw.add (contDiffOn_const.mul hq.contDiffOn)
  have hvc : ContinuousOn (fun x ↦ w x + c * ‖x - x₀‖ ^ 2) (closedBall x₀ R) :=
    hwc.add (continuous_const.mul hq.continuous).continuousOn
  have hΔv : ∀ x ∈ ball x₀ R, 0 ≤ Δ (fun x ↦ w x + c * ‖x - x₀‖ ^ 2) x := fun x hx ↦ by
    have hsmul : Δ (fun x : E ↦ c * ‖x - x₀‖ ^ 2) x = c * Δ (fun x : E ↦ ‖x - x₀‖ ^ 2) x :=
      laplacian_smul c hq.contDiffAt
    have hadd : Δ (fun x ↦ w x + c * ‖x - x₀‖ ^ 2) x =
        Δ w x + Δ (fun x : E ↦ c * ‖x - x₀‖ ^ 2) x :=
      (hw.contDiffAt (isOpen_ball.mem_nhds hx)).laplacian_add (contDiffAt_const.mul hq.contDiffAt)
    rw [hadd, hsmul, hΔq, hc_def,
      div_mul_cancel₀ _ (by positivity)]
    linarith [hΔ x hx]
  have hsub := mul_le_setIntegral_ball_of_laplacian_nonneg (μ := μ) hv hvc hΔv
  -- The integral of the correction over the ball.
  have hqint : ∫ x in ball x₀ R, ‖x - x₀‖ ^ 2 ∂μ =
      Module.finrank ℝ E / (Module.finrank ℝ E + 2) * R ^ 2 * μ.real (ball x₀ R) := by
    have h := integral_norm_sub_rpow_ball (mu := μ) (s := 2) (by linarith) hR.le x₀
    simp_rw [norm_sub_rev x₀, Real.rpow_two] at h
    have hball : μ.real (ball x₀ R) = R ^ Module.finrank ℝ E * μ.real (ball (0 : E) 1) := by
      rw [measureReal_def, Measure.addHaar_ball μ _ hR.le, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (by positivity), measureReal_def]
    rw [h, hball, Real.rpow_add hR, Real.rpow_two,
      Real.rpow_natCast]
    field_simp
  have hwint : IntegrableOn w (ball x₀ R) μ :=
    (hwc.integrableOn_compact (isCompact_closedBall _ _)).mono_set ball_subset_closedBall
  have hqint' : IntegrableOn (fun x : E ↦ ‖x - x₀‖ ^ 2) (ball x₀ R) μ :=
    (hq.continuous.continuousOn.integrableOn_compact (isCompact_closedBall _ _)).mono_set
      ball_subset_closedBall
  rw [integral_add hwint (hqint'.const_mul c), integral_const_mul, hqint, sub_self, norm_zero,
    zero_pow two_ne_zero, mul_zero, add_zero] at hsub
  calc μ.real (ball x₀ R) * w x₀ ≤ _ := hsub
    _ = _ := by rw [hc_def]; field_simp

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Choice of the centre.** For `w` continuous on `closedBall x₀ r`, a maximum `(ρ, z)` of
`(r - ρ) ^ 2 * w z` over `{(ρ, z) | 0 ≤ ρ ≤ r, dist z x₀ ≤ ρ}` satisfies
`r ^ 2 * w x₀ ≤ (r - ρ) ^ 2 * w z`, and `((r - ρ) / 2) ^ 2 * w y ≤ (r - ρ) ^ 2 * w z` for every
`y` within `(r - ρ) / 2` of `z`. -/
private lemma exists_center {w : E → ℝ} {x₀ : E} {r : ℝ} (hr : 0 < r)
    (hwc : ContinuousOn w (closedBall x₀ r)) :
    ∃ ρ z, 0 ≤ ρ ∧ ρ ≤ r ∧ dist z x₀ ≤ ρ ∧ r ^ 2 * w x₀ ≤ (r - ρ) ^ 2 * w z ∧
      ∀ y ∈ closedBall z ((r - ρ) / 2), ((r - ρ) / 2) ^ 2 * w y ≤ (r - ρ) ^ 2 * w z := by
  set S : Set (ℝ × E) := {p | 0 ≤ p.1} ∩ {p | p.1 ≤ r} ∩ {p | dist p.2 x₀ ≤ p.1} with hS_def
  have hS : IsCompact S := by
    refine ((isCompact_Icc (a := (0 : ℝ)) (b := r)).prod
      (isCompact_closedBall x₀ r)).of_isClosed_subset
      (((isClosed_le continuous_const continuous_fst).inter
        (isClosed_le continuous_fst continuous_const)).inter
          (isClosed_le (continuous_snd.dist continuous_const) continuous_fst)) ?_
    rintro p ⟨⟨h0, h1⟩, h2⟩
    exact ⟨⟨h0, h1⟩, mem_closedBall.mpr (h2.trans h1)⟩
  have hg : ContinuousOn (fun p : ℝ × E ↦ (r - p.1) ^ 2 * w p.2) S :=
    ((continuous_const.sub continuous_fst).pow 2).continuousOn.mul
      (hwc.comp continuous_snd.continuousOn fun p hp ↦ mem_closedBall.mpr (hp.2.trans hp.1.2))
  obtain ⟨⟨ρ, z⟩, hpS, hmax⟩ := hS.exists_isMaxOn ⟨(0, x₀), by simp [hS_def, hr.le]⟩ hg
  have hρ0 : 0 ≤ ρ := hpS.1.1
  have hρr : ρ ≤ r := hpS.1.2
  have hz : dist z x₀ ≤ ρ := hpS.2
  have hmax' : ∀ ρ' z', 0 ≤ ρ' → ρ' ≤ r → dist z' x₀ ≤ ρ' →
      (r - ρ') ^ 2 * w z' ≤ (r - ρ) ^ 2 * w z := fun ρ' z' h0 h1 h2 ↦
    hmax (a := (ρ', z')) ⟨⟨h0, h1⟩, h2⟩
  refine ⟨ρ, z, hρ0, hρr, hz, by simpa using hmax' 0 x₀ le_rfl hr.le (by simp), fun y hy ↦ ?_⟩
  -- A point within `(r - ρ) / 2` of `z` is within `ρ + (r - ρ) / 2` of `x₀`.
  have h := hmax' (ρ + (r - ρ) / 2) y (by linarith) (by linarith)
    ((dist_triangle y z x₀).trans (by linarith [mem_closedBall.mp hy]))
  have hrad : r - (ρ + (r - ρ) / 2) = (r - ρ) / 2 := by ring
  rwa [hrad] at h

/-- **The local estimate.** In dimension two, if `0 ≤ w ≤ 4 c` and `Δ w ≥ -A w²` on `ball z δ`,
with `A ≥ 0`, then `δ² μ (ball 0 1) w z ≤ ∫ w + 2 A c² δ² (δ² μ (ball 0 1))`, the integral
being over `ball z δ`. -/
private lemma local_estimate (hE : Module.finrank ℝ E = 2) {w : E → ℝ} {z : E} {δ A c : ℝ}
    (hδ : 0 ≤ δ) (hA : 0 ≤ A) (hw : ContDiffOn ℝ 2 w (ball z δ))
    (hwc : ContinuousOn w (closedBall z δ)) (hw0 : ∀ y ∈ ball z δ, 0 ≤ w y)
    (hw4 : ∀ y ∈ ball z δ, w y ≤ 4 * c) (hΔ : ∀ y ∈ ball z δ, -(A * w y ^ 2) ≤ Δ w y) :
    δ ^ 2 * μ.real (ball (0 : E) 1) * w z ≤ ∫ x in ball z δ, w x ∂μ +
      2 * A * c ^ 2 * δ ^ 2 * (δ ^ 2 * μ.real (ball (0 : E) 1)) := by
  have : Nontrivial E := Module.nontrivial_of_finrank_eq_succ hE
  have hK := mul_le_setIntegral_ball_add_of_neg_le_laplacian (μ := μ) (K := 16 * A * c ^ 2) hw hwc
    fun y hy ↦ by
      have hsq : w y ^ 2 ≤ 16 * c ^ 2 := by nlinarith [hw0 y hy, hw4 y hy]
      linarith [hΔ y hy, mul_le_mul_of_nonneg_left hsq hA]
  rw [measureReal_def, Measure.addHaar_ball μ _ hδ, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity), hE, ← measureReal_def] at hK
  calc δ ^ 2 * μ.real (ball (0 : E) 1) * w z ≤ _ := hK
    _ = _ := by push_cast; ring

/-- **The mean-value inequality.** Let `E` be two-dimensional, and let `w` be `C²` on the ball
`ball x₀ r`, continuous on its closure, nonnegative on the ball, with `Δ w ≥ -A w²` there. If
`8 A ∫ w < μ (ball 0 1)` over the ball, then `μ (ball x₀ r) * w x₀ ≤ 8 ∫ w`. For Lebesgue measure
on `ℂ`, where `μ (ball 0 1) = π`, and for `r > 0` and `A > 0`, this is `w x₀ ≤ 8 / (π r²) ∫ w`
under `∫ w < π / (8 A)`. -/
theorem mul_le_eight_mul_setIntegral_ball_of_neg_mul_sq_le_laplacian
    (hE : Module.finrank ℝ E = 2) {w : E → ℝ} {x₀ : E} {r A : ℝ}
    (hw : ContDiffOn ℝ 2 w (ball x₀ r)) (hwc : ContinuousOn w (closedBall x₀ r))
    (hw0 : ∀ x ∈ ball x₀ r, 0 ≤ w x) (hΔ : ∀ x ∈ ball x₀ r, -(A * w x ^ 2) ≤ Δ w x)
    (hsmall : 8 * A * ∫ x in ball x₀ r, w x ∂μ < μ.real (ball (0 : E) 1)) :
    μ.real (ball x₀ r) * w x₀ ≤ 8 * ∫ x in ball x₀ r, w x ∂μ := by
  have : Nontrivial E := Module.nontrivial_of_finrank_eq_succ hE
  rcases le_or_gt r 0 with hr | hr
  · simp [ball_eq_empty.mpr hr]
  set I := ∫ x in ball x₀ r, w x ∂μ with hI_def
  set V := μ.real (ball (0 : E) 1) with hV_def
  have hV : 0 < V := by
    rw [hV_def, measureReal_def]
    exact ENNReal.toReal_pos (measure_ball_pos μ 0 one_pos).ne' measure_ball_lt_top.ne
  -- Replacing `A` by `A' = max A 0` only weakens the hypotheses.
  set A' := max A 0 with hA'_def
  have hA' : 0 ≤ A' := le_max_right _ _
  have hΔ' : ∀ x ∈ ball x₀ r, -(A' * w x ^ 2) ≤ Δ w x := fun x hx ↦
    le_trans (neg_le_neg (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))) (hΔ x hx)
  have hsmall' : 8 * A' * I < V := by
    rcases le_total A 0 with hA | hA
    · rw [hA'_def, max_eq_right hA]
      simpa using hV
    · rwa [hA'_def, max_eq_left hA]
  -- Choose the centre `z` and the radius `ε = (r - ρ) / 2`, and put `c = w z`.
  obtain ⟨ρ, z, -, hρr, hz, hcenter, hw4⟩ := exists_center hr hwc
  rcases le_or_gt ((r - ρ) ^ 2 * w z) 0 with hpos | hpos
  · -- Then `w x₀ ≤ 0`, and the claim is trivial.
    have hwx₀ : w x₀ ≤ 0 := by nlinarith [sq_pos_of_pos hr]
    have hI0 : 0 ≤ I := setIntegral_nonneg measurableSet_ball hw0
    exact (mul_nonpos_of_nonneg_of_nonpos measureReal_nonneg hwx₀).trans (by linarith)
  have hρr' : ρ < r := lt_of_le_of_ne hρr fun h ↦ by simp [h] at hpos
  have hc : 0 < w z := pos_of_mul_pos_right hpos (sq_nonneg _)
  set ε := (r - ρ) / 2 with hε_def
  have hε : 0 < ε := by rw [hε_def]; linarith
  have hrρ : (r - ρ) ^ 2 = 4 * ε ^ 2 := by rw [hε_def]; ring
  rw [hrρ] at hcenter hw4
  -- Every ball `ball z δ` with `δ ≤ ε` lies in `ball x₀ r`, and `w ≤ 4 c` on it.
  have hsub : ∀ δ ≤ ε, closedBall z δ ⊆ ball x₀ r := fun δ hδ y hy ↦
    mem_ball.mpr ((dist_triangle y z x₀).trans_lt (by linarith [mem_closedBall.mp hy]))
  have hloc : ∀ δ, 0 < δ → δ ≤ ε →
      δ ^ 2 * V * w z ≤ I + 2 * A' * w z ^ 2 * δ ^ 2 * (δ ^ 2 * V) := by
    intro δ hδ hδε
    have h := local_estimate (μ := μ) (c := w z) hE hδ.le hA'
      (hw.mono (ball_subset_closedBall.trans (hsub δ hδε)))
      (hwc.mono ((hsub δ hδε).trans ball_subset_closedBall))
      (fun y hy ↦ hw0 y (hsub δ hδε (ball_subset_closedBall hy)))
      (fun y hy ↦ by
        have := hw4 y (closedBall_subset_closedBall hδε (ball_subset_closedBall hy))
        nlinarith [sq_pos_of_pos hε])
      fun y hy ↦ hΔ' y (hsub δ hδε (ball_subset_closedBall hy))
    have hint : ∫ x in ball z δ, w x ∂μ ≤ I :=
      setIntegral_mono_set ((hwc.integrableOn_compact (isCompact_closedBall _ _)).mono_set
        ball_subset_closedBall) (ae_restrict_of_forall_mem measurableSet_ball hw0)
        (ball_subset_closedBall.trans (hsub δ hδε)).eventuallyLE
    linarith
  rcases le_or_gt (4 * A' * w z * ε ^ 2) 1 with hcase | hcase
  · -- Take `δ = ε`: then `ε ^ 2 * V * c ≤ 2 I`, and the claim follows from the centre bound.
    have h := hloc ε hε le_rfl
    have hhalf : 2 * A' * w z ^ 2 * ε ^ 2 * (ε ^ 2 * V) ≤ ε ^ 2 * V * w z / 2 := by
      have : 0 ≤ ε ^ 2 * V * w z := by positivity
      nlinarith
    rw [measureReal_def, Measure.addHaar_ball μ _ hr.le, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity), hE, ← measureReal_def]
    nlinarith
  · -- Otherwise `δ ^ 2 = 1 / (4 A' c) < ε ^ 2` gives `V ≤ 8 A' I`, contradicting smallness.
    exfalso
    have hA'pos : 0 < A' := by
      by_contra h
      rw [le_antisymm (not_lt.mp h) hA'] at hcase
      linarith
    set δ := Real.sqrt (1 / (4 * A' * w z)) with hδ_def
    have hδ2 : δ ^ 2 = 1 / (4 * A' * w z) := Real.sq_sqrt (by positivity)
    have hδ : 0 < δ := Real.sqrt_pos.mpr (by positivity)
    have hδε : δ ≤ ε := by
      refine (pow_le_pow_iff_left₀ hδ.le hε.le two_ne_zero).mp ?_
      rw [hδ2, div_le_iff₀ (by positivity), mul_comm (ε ^ 2)]
      exact hcase.le
    have hAcδ : 4 * A' * w z * δ ^ 2 = 1 := by
      rw [hδ2]; field_simp
    have h := hloc δ hδ hδε
    have hhalf : 2 * A' * w z ^ 2 * δ ^ 2 * (δ ^ 2 * V) = δ ^ 2 * V * w z / 2 := by
      linear_combination (δ ^ 2 * V * w z / 2) * hAcδ
    have h2 : δ ^ 2 * V * w z ≤ 2 * I := by linarith
    have h3 : V ≤ 8 * A' * I := by
      have : δ ^ 2 * V * w z * (4 * A') = V := by linear_combination V * hAcδ
      nlinarith
    linarith

end TauCeti
