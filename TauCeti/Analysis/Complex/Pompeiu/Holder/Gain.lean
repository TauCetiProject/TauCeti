/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Pompeiu.Schauder
public import TauCeti.Analysis.Calculus.BumpFunction.HolderApproximation
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.Sequences
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import TauCeti.Topology.MetricSpace.Holder

/-!
# The Cauchy transform gains one Hölder derivative

The gain is first proved for real Hölder sources on one fixed support disc and then extended
to finite-dimensional complex normed targets through continuous complex coordinates.
The actual normalized Cauchy integral is
`C¹` on an output neighborhood, and its derivative has a uniform Hölder and supremum bound on
the output disc. Smooth normalized bump approximations preserve the source bounds. Their
Cauchy derivatives have a uniformly convergent subsequence by Arzelà–Ascoli; the derivative
limit theorem identifies the limit with the derivative of the actual Cauchy integral.
-/

public noncomputable section

open Complex Metric MeasureTheory Set Filter Topology
open scoped NNReal ContDiff BoundedContinuousFunction

namespace TauCeti

private theorem conjWirtingerDeriv_normalizedCauchy_smooth {f : ℂ → ℂ}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) (w : ℂ) :
    conjWirtingerDeriv (fun w ↦ (Real.pi : ℂ)⁻¹ • ∫ z, (w - z)⁻¹ • f z) w 1 = f w := by
  have hD := hc.hasFDerivAt_integral_sub_inv_smul hf w
  rw [conjWirtingerDeriv_smul_apply (differentiableAt_const ((Real.pi : ℂ)⁻¹)) hD.differentiableAt,
    hc.conjWirtingerDeriv_integral_sub_inv_smul_apply_one hf w]
  simp [Real.pi_ne_zero]

private theorem exists_tendstoUniformlyOn_fderiv_holderOnWith
    {Tn : ℕ → ℂ → ℂ} {c : ℂ} {R : ℝ} {B α : ℝ≥0} (hα : 0 < α)
    (hSmooth : ∀ n, ContDiff ℝ ∞ (Tn n))
    (hHolder : ∀ n, HolderOnWith B α (fderiv ℝ (Tn n)) (closedBall c R))
    (hNorm : ∀ n x, x ∈ closedBall c R → ‖fderiv ℝ (Tn n) x‖ ≤ B) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ G : ℂ → ℂ →L[ℝ] ℂ,
      TendstoUniformlyOn (fun n ↦ fderiv ℝ (Tn (φ n))) G atTop (closedBall c R) ∧
      HolderOnWith B α G (closedBall c R) ∧
      ∀ x ∈ closedBall c R, ‖G x‖ ≤ B := by
  classical
  let K := closedBall c R
  have : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_closedBall c R)
  let V (n : ℕ) : K →ᵇ (ℂ →L[ℝ] ℂ) := BoundedContinuousFunction.mkOfCompact
    ⟨fun x ↦ fderiv ℝ (Tn n) x, ((hSmooth n).continuous_fderiv (by simp)).comp
      continuous_subtype_val⟩
  have hEqui : Equicontinuous ((↑) : range V → K → (ℂ →L[ℝ] ℂ)) := by
    apply Metric.equicontinuous_of_continuity_modulus
      (fun t : ℝ ↦ B * t ^ (α : ℝ))
    · have hc : Continuous (fun t : ℝ ↦ B * t ^ (α : ℝ)) :=
        continuous_const.mul (Real.continuous_rpow_const α.coe_nonneg)
      simpa only [Real.zero_rpow (NNReal.coe_pos.mpr hα).ne', mul_zero] using hc.tendsto 0
    · intro x y q
      rcases q with ⟨_, n, rfl⟩
      exact (hHolder n).dist_le x.property y.property
  have hCompact := BoundedContinuousFunction.arzela_ascoli
    (closedBall (0 : ℂ →L[ℝ] ℂ) B) (isCompact_closedBall _ _) (range V)
    (fun q x hq ↦ by
      rcases hq with ⟨n, rfl⟩
      exact mem_closedBall_zero_iff.mpr (hNorm n x x.property)) hEqui
  obtain ⟨q, -, φ, hφ, hVlim⟩ := hCompact.tendsto_subseq
    (fun n ↦ subset_closure (mem_range_self n))
  have hUnif : TendstoUniformly (fun n ↦ (V (φ n) : K → (ℂ →L[ℝ] ℂ))) q atTop :=
    BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hVlim
  let G (x : ℂ) : ℂ →L[ℝ] ℂ := if hx : x ∈ K then q ⟨x, hx⟩ else 0
  have hG (x : ℂ) (hx : x ∈ K) : G x = q ⟨x, hx⟩ := by
    dsimp only [G]
    rw [dite_eq_left hx]
  have hUnifOn : TendstoUniformlyOn (fun n ↦ fderiv ℝ (Tn (φ n))) G atTop K := by
    rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
    convert hUnif using 1
    · funext n x
      rfl
    · funext x
      exact hG x x.property
  have hGHolder : HolderOnWith B α G K := by
    apply HolderOnWith.of_dist_le
    intro x hx y hy
    exact le_of_tendsto ((hUnifOn.tendsto_at hx).dist (hUnifOn.tendsto_at hy))
      (Eventually.of_forall fun n ↦ (hHolder (φ n)).dist_le hx hy)
  have hGNorm (x : ℂ) (hx : x ∈ K) : ‖G x‖ ≤ B :=
    le_of_tendsto (hUnifOn.tendsto_at hx).norm
      (Eventually.of_forall fun n ↦ hNorm (φ n) x hx)
  exact ⟨φ, hφ, G, hUnifOn, hGHolder, hGNorm⟩

/-- The actual Cauchy transform gains one Hölder derivative for real sources, with separately
fixed support and output discs. Its `C¹` neighborhood contains the closed output disc. -/
theorem exists_contDiffOn_holderOnWith_fderiv_pi_inv_smul_integral_sub_inv_smul_real
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) (c : ℂ) {r R : ℝ}
    (hr : 0 ≤ r) (hR : 0 ≤ R) :
    ∃ C : ℝ≥0, ∀ {f : ℂ → ℝ} {H M : ℝ≥0},
      Function.support f ⊆ closedBall c r → HolderWith H α f → (∀ x, ‖f x‖ ≤ M) →
      let T : ℂ → ℂ := fun w ↦ (Real.pi : ℂ)⁻¹ • ∫ z, (w - z)⁻¹ • (f z : ℂ)
      ContDiffOn ℝ 1 T (ball c (R + 1)) ∧
      HolderOnWith (C * (H + M)) α (fderiv ℝ T) (closedBall c R) ∧
        (∀ x ∈ closedBall c R, ‖fderiv ℝ T x‖ ≤ C * (H + M)) ∧
        ∀ x ∈ ball c (R + 1), conjWirtingerDeriv T x 1 = (f x : ℂ) := by
  classical
  obtain ⟨C, hC⟩ := exists_holderOnWith_fderiv_pi_inv_smul_integral_sub_inv_smul_real
    hα hα1 c (by linarith : 0 ≤ r + 1) (by linarith : 0 ≤ R + 1)
  refine ⟨C, fun {f H M} hs hf hM ↦ ?_⟩
  intro T
  -- Smooth probability-kernel approximants preserve both source bounds and one support disc.
  obtain ⟨g, hgsmooth, hgs, hgH, hgM, hglim⟩ :=
    exists_contDiff_support_subset_holderWith_tendstoUniformly hα hf hM hs
  let Tn (n : ℕ) : ℂ → ℂ := fun w ↦
    (Real.pi : ℂ)⁻¹ • ∫ z, (w - z)⁻¹ • (g n z : ℂ)
  have hSmooth (n : ℕ) : ContDiff ℝ ∞ (Tn n) ∧
      HolderOnWith (C * (H + M)) α (fderiv ℝ (Tn n)) (closedBall c (R + 1)) ∧
      ∀ x ∈ closedBall c (R + 1), ‖fderiv ℝ (Tn n) x‖ ≤ C * (H + M) :=
    hC (hgsmooth n) (hgs n) (hgH n) (hgM n)
  -- Compactness of the uniformly Hölder derivative fields produces a uniform derivative limit.
  obtain ⟨φ, hφ, G, hUnifOn, hGHolder, hGNorm⟩ :=
    exists_tendstoUniformlyOn_fderiv_holderOnWith hα
      (fun n ↦ (hSmooth n).1) (fun n ↦ (hSmooth n).2.1) (fun n ↦ (hSmooth n).2.2)
  have hgsC (n : ℕ) : Function.support (fun z ↦ (g n z : ℂ)) ⊆ closedBall c (r + 1) :=
    (Function.support_comp_subset Complex.ofReal_zero (g n)).trans (hgs n)
  have hfsC : Function.support (fun z ↦ (f z : ℂ)) ⊆ closedBall c (r + 1) :=
    (Function.support_comp_subset Complex.ofReal_zero f).trans
      (hs.trans (closedBall_subset_closedBall (by linarith : r ≤ r + 1)))
  have hTlim (x : ℂ) : Tendsto (fun n ↦ Tn n x) atTop (𝓝 (T x)) := by
    apply tendsto_pi_inv_smul_integral_sub_inv_smul
      (fun n ↦ continuous_ofReal.comp (hgsmooth n).continuous) hgsC hfsC
      (M := (M : ℝ)) (fun n z ↦ by simpa only [Function.comp_apply, norm_real] using hgM n z)
    intro z
    exact continuous_ofReal.continuousAt.tendsto.comp (hglim.tendsto_at z)
  -- The function and derivative limits identify the actual derivative of the Cauchy integral.
  have hDeriv (x : ℂ) (hx : x ∈ ball c (R + 1)) : HasFDerivAt T (G x) x :=
    hasFDerivAt_of_tendstoUniformlyOn isOpen_ball (hUnifOn.mono ball_subset_closedBall)
      (fun n y _ ↦ ((hSmooth (φ n)).1.differentiable (by simp) y).hasFDerivAt)
      (fun y _ ↦ (hTlim y).comp hφ.tendsto_atTop) hx
  have hDf (x : ℂ) (hx : x ∈ ball c (R + 1)) : fderiv ℝ T x = G x := (hDeriv x hx).fderiv
  have hsub : closedBall c R ⊆ ball c (R + 1) :=
    closedBall_subset_ball (by linarith)
  refine ⟨?_, ?_, (fun x hx ↦ ?_), fun x hx ↦ ?_⟩
  · rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl,
      contDiffOn_succ_iff_fderiv_of_isOpen isOpen_ball]
    refine ⟨fun x hx ↦ (hDeriv x hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    rw [contDiffOn_zero]
    exact ((hGHolder.continuousOn hα).mono ball_subset_closedBall).congr
      (fun x hx ↦ hDf x hx)
  · intro x hx y hy
    rw [hDf x (hsub hx), hDf y (hsub hy)]
    exact hGHolder x (ball_subset_closedBall (hsub hx)) y (ball_subset_closedBall (hsub hy))
  · rw [hDf x (hsub hx)]
    exact hGNorm x (ball_subset_closedBall (hsub hx))
  · -- Pass the normalized Wirtinger equation through the derivative and source limits.
    let L : (ℂ →L[ℝ] ℂ) → ℂ := fun A ↦ (2 : ℂ)⁻¹ • (A 1 + I • A I)
    have hL : Continuous L := by fun_prop
    have hleft := hL.continuousAt.tendsto.comp
      (hUnifOn.tendsto_at (ball_subset_closedBall hx))
    have hn (n : ℕ) : L (fderiv ℝ (Tn n) x) = (g n x : ℂ) := by
      have hc := HasCompactSupport.of_support_subset_isCompact
        (isCompact_closedBall c (r + 1)) (hgsC n)
      have hgc : ContDiff ℝ 1 (fun z ↦ (g n z : ℂ)) := by
        exact Complex.ofRealCLM.contDiff.comp ((hgsmooth n).of_le (by simp))
      simpa only [L, Tn, conjWirtingerDeriv_apply, smul_eq_mul, mul_one] using
        conjWirtingerDeriv_normalizedCauchy_smooth hgc hc x
    have hseq : (fun n ↦ L (fderiv ℝ (Tn (φ n)) x)) = fun n ↦ (g (φ n) x : ℂ) := by
      funext n
      exact hn (φ n)
    simp only [Function.comp_def] at hleft
    rw [hseq] at hleft
    have hright := continuous_ofReal.continuousAt.tendsto.comp
      ((hglim.tendsto_at x).comp hφ.tendsto_atTop)
    have heq := tendsto_nhds_unique hleft hright
    simpa only [conjWirtingerDeriv_apply, hDf x hx, smul_eq_mul, mul_one, L] using heq

/-- The actual Cauchy transform of complex Hölder data is `C¹` near the output disc, and its
derivative has supremum and `α`-Hölder constant at most `C (H + M)` on that disc. -/
private theorem exists_contDiffOn_holderOnWith_fderiv_pi_inv_smul_integral_sub_inv_smul_complex
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) (c : ℂ) {r R : ℝ}
    (hr : 0 ≤ r) (hR : 0 ≤ R) :
    ∃ C : ℝ≥0, ∀ {f : ℂ → ℂ} {H M : ℝ≥0},
      Function.support f ⊆ closedBall c r → HolderWith H α f → (∀ x, ‖f x‖ ≤ M) →
      let T : ℂ → ℂ := fun w ↦ (Real.pi : ℂ)⁻¹ • ∫ z, (w - z)⁻¹ • f z
      ContDiffOn ℝ 1 T (ball c (R + 1)) ∧
      HolderOnWith (C * (H + M)) α (fderiv ℝ T) (closedBall c R) ∧
        (∀ x ∈ closedBall c R, ‖fderiv ℝ T x‖ ≤ C * (H + M)) ∧
        ∀ x ∈ ball c (R + 1), conjWirtingerDeriv T x 1 = f x := by
  obtain ⟨C, hC⟩ :=
    exists_contDiffOn_holderOnWith_fderiv_pi_inv_smul_integral_sub_inv_smul_real hα hα1 c hr hR
  refine ⟨2 * C, fun {f H M} hs hf hM ↦ ?_⟩
  intro T
  let Tr : ℂ → ℂ := fun w ↦ (Real.pi : ℂ)⁻¹ • ∫ z, (w - z)⁻¹ • ((f z).re : ℂ)
  let Ti : ℂ → ℂ := fun w ↦ (Real.pi : ℂ)⁻¹ • ∫ z, (w - z)⁻¹ • ((f z).im : ℂ)
  have hsRe : Function.support (fun z ↦ (f z).re) ⊆ closedBall c r :=
    (Function.support_comp_subset Complex.zero_re f).trans hs
  have hsIm : Function.support (fun z ↦ (f z).im) ⊆ closedBall c r :=
    (Function.support_comp_subset Complex.zero_im f).trans hs
  have hRe : HolderWith H α (fun z ↦ (f z).re) := by
    simpa only [RCLike.re_eq_complex_re, Function.comp_def, one_mul, NNReal.coe_one,
      NNReal.rpow_one] using (RCLike.lipschitzWith_re (K := ℂ)).holderWith.comp hf
  have hIm : HolderWith H α (fun z ↦ (f z).im) := by
    simpa only [RCLike.im_eq_complex_im, Function.comp_def, one_mul, NNReal.coe_one,
      NNReal.rpow_one] using (RCLike.lipschitzWith_im (K := ℂ)).holderWith.comp hf
  have hMRe (z : ℂ) : ‖(f z).re‖ ≤ M := by
    rw [Real.norm_eq_abs]
    exact (abs_re_le_norm (f z)).trans (hM z)
  have hMIm (z : ℂ) : ‖(f z).im‖ ≤ M := by
    rw [Real.norm_eq_abs]
    exact (abs_im_le_norm (f z)).trans (hM z)
  obtain ⟨hTr, hDr, hNr, hIr⟩ := hC hsRe hRe hMRe
  obtain ⟨hTi, hDi, hNi, hIi⟩ := hC hsIm hIm hMIm
  have hc := HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall c r) hs
  have hT : T = fun x ↦ Tr x + I • Ti x := by
    funext x
    dsimp only [T, Tr, Ti]
    simp only [smul_eq_mul]
    rw [integral_sub_inv_mul_eq_re_add_I_mul_im (hf.continuous hα) hc x]
    ring
  have hdr (x : ℂ) (hx : x ∈ ball c (R + 1)) : DifferentiableAt ℝ Tr x :=
    (hTr.contDiffAt (isOpen_ball.mem_nhds hx)).differentiableAt one_ne_zero
  have hdi (x : ℂ) (hx : x ∈ ball c (R + 1)) : DifferentiableAt ℝ Ti x :=
    (hTi.contDiffAt (isOpen_ball.mem_nhds hx)).differentiableAt one_ne_zero
  have hDT (x : ℂ) (hx : x ∈ ball c (R + 1)) :
      fderiv ℝ T x = fderiv ℝ Tr x + I • fderiv ℝ Ti x := by
    rw [hT]
    exact ((hdr x hx).hasFDerivAt.add ((hdi x hx).hasFDerivAt.const_smul I)).fderiv
  have hsub : closedBall c R ⊆ ball c (R + 1) := closedBall_subset_ball (by linarith)
  refine ⟨by rw [hT]; exact hTr.add (hTi.const_smul I), ?_, (fun x hx ↦ ?_), fun x hx ↦ ?_⟩
  · apply HolderOnWith.of_dist_le
    intro x hx y hy
    rw [dist_eq_norm, hDT x (hsub hx), hDT y (hsub hy)]
    have heq : fderiv ℝ Tr x + I • fderiv ℝ Ti x - (fderiv ℝ Tr y + I • fderiv ℝ Ti y) =
        (fderiv ℝ Tr x - fderiv ℝ Tr y) + I • (fderiv ℝ Ti x - fderiv ℝ Ti y) := by module
    rw [heq]
    calc
      _ ≤ ‖fderiv ℝ Tr x - fderiv ℝ Tr y‖ + ‖I • (fderiv ℝ Ti x - fderiv ℝ Ti y)‖ :=
        norm_add_le _ _
      _ ≤ ((C * (H + M) : ℝ≥0) * dist x y ^ (α : ℝ)) +
          ((C * (H + M) : ℝ≥0) * dist x y ^ (α : ℝ)) := by
        simp only [norm_smul, norm_I, one_mul]
        exact add_le_add (by simpa only [dist_eq_norm] using hDr.dist_le hx hy)
          (by simpa only [dist_eq_norm] using hDi.dist_le hx hy)
      _ = _ := by push_cast; ring
  · rw [hDT x (hsub hx)]
    calc
      _ ≤ ‖fderiv ℝ Tr x‖ + ‖I • fderiv ℝ Ti x‖ := norm_add_le _ _
      _ ≤ (C * (H + M) : ℝ≥0) + (C * (H + M) : ℝ≥0) := by
        simp only [norm_smul, norm_I, one_mul]
        exact add_le_add (hNr x hx) (hNi x hx)
      _ = _ := by push_cast; ring
  · have hrx : conjWirtingerDeriv Tr x 1 = ((f x).re : ℂ) := hIr x hx
    have hix : conjWirtingerDeriv Ti x 1 = ((f x).im : ℂ) := hIi x hx
    simp only [conjWirtingerDeriv_apply, smul_eq_mul, mul_one] at hrx hix ⊢
    rw [hDT x hx]
    simp only [add_apply, smul_apply, smul_eq_mul]
    calc
      _ = (2 : ℂ)⁻¹ * (fderiv ℝ Tr x 1 + I * fderiv ℝ Tr x I) +
          I * ((2 : ℂ)⁻¹ * (fderiv ℝ Ti x 1 + I * fderiv ℝ Ti x I)) := by ring
      _ = (f x).re + I * (f x).im := by rw [hrx, hix]
      _ = f x := by rw [mul_comm I, (f x).re_add_im]

private theorem exists_cauchyCoordinate_gain
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] {ι : Type*} [Fintype ι]
    (e : F ≃L[ℂ] (ι → ℂ)) {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1)
    (c : ℂ) {r R : ℝ} (hr : 0 ≤ r) (hR : 0 ≤ R) :
    ∃ C : ℝ≥0, ∀ {f : ℂ → F} {H M : ℝ≥0},
      Function.support f ⊆ closedBall c r → HolderWith H α f → (∀ x, ‖f x‖ ≤ M) →
      ∀ i, let S : ℂ → ℂ := fun w ↦
        (Real.pi : ℂ)⁻¹ • ∫ z, (w - z)⁻¹ • e (f z) i
      ContDiffOn ℝ 1 S (ball c (R + 1)) ∧
      HolderOnWith (C * (‖e.toContinuousLinearMap‖₊ * H +
        ‖e.toContinuousLinearMap‖₊ * M)) α (fderiv ℝ S) (closedBall c R) ∧
      (∀ x ∈ closedBall c R, ‖fderiv ℝ S x‖ ≤
        C * (‖e.toContinuousLinearMap‖₊ * H + ‖e.toContinuousLinearMap‖₊ * M)) ∧
      ∀ x ∈ ball c (R + 1), conjWirtingerDeriv S x 1 = e (f x) i := by
  obtain ⟨C, hC⟩ :=
    exists_contDiffOn_holderOnWith_fderiv_pi_inv_smul_integral_sub_inv_smul_complex
      hα hα1 c hr hR
  refine ⟨C, fun {f H M} hs hf hM i ↦ ?_⟩
  let K := ‖e.toContinuousLinearMap‖₊
  let g (i : ι) (z : ℂ) := e (f z) i
  have hg (i) : HolderWith (K * H) α (g i) := by
    apply holderOnWith_univ.mp
    apply HolderOnWith.of_dist_le
    intro x _ y _
    calc
      dist (g i x) (g i y) ≤ dist (e (f x)) (e (f y)) := dist_le_pi_dist (e (f x)) (e (f y)) i
      _ ≤ K * dist (f x) (f y) := e.toContinuousLinearMap.lipschitzWith.dist_le_mul _ _
      _ ≤ K * (H * dist x y ^ (α : ℝ)) := mul_le_mul_of_nonneg_left
        (hf.dist_le x y) K.coe_nonneg
      _ = _ := by push_cast; ring
  have hgM (i) (z : ℂ) : ‖g i z‖ ≤ (K * M : ℝ≥0) :=
    (norm_le_pi_norm _ i).trans ((e.toContinuousLinearMap.le_opNorm (f z)).trans
      (mul_le_mul_of_nonneg_left (hM z) (norm_nonneg _)))
  have hgs (i) : Function.support (g i) ⊆ closedBall c r :=
    (Function.support_comp_subset (g := fun v : F ↦ e v i) (by simp) f).trans hs
  exact hC (f := g i) (H := K * H) (M := K * M) (hgs i) (hg i) (hgM i)

private theorem normalizedCauchy_coordinates
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {ι : Type*} (e : F ≃L[ℂ] (ι → ℂ)) {f : ℂ → F}
    (hf : Continuous f) {c : ℂ} {r : ℝ} (hs : Function.support f ⊆ closedBall c r)
    (w : ℂ) : e ((Real.pi : ℂ)⁻¹ • ∫ z, (w - z)⁻¹ • f z) =
      fun i ↦ (Real.pi : ℂ)⁻¹ • ∫ z, (w - z)⁻¹ • e (f z) i := by
  have hi := (Complex.locallyIntegrable_sub_inv w).integrable_smul_right_of_hasCompactSupport
    hf (HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall c r) hs)
  funext i
  let q := (ContinuousLinearMap.proj i).comp e.toContinuousLinearMap
  have hq := q.integral_comp_comm hi
  simpa only [q, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    map_smul, Pi.smul_apply, ContinuousLinearEquiv.coe_coe] using
    congrArg (fun v ↦ (Real.pi : ℂ)⁻¹ • v) hq.symm

private theorem cauchyCoordinate_reconstruct
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {ι : Type*} [Finite ι] (e : F ≃L[ℂ] (ι → ℂ)) {f : ℂ → F}
    (hf : Continuous f) {c : ℂ} {r R : ℝ} (hs : Function.support f ⊆ closedBall c r) :
    let S (i : ι) (w : ℂ) := (Real.pi : ℂ)⁻¹ • ∫ z, (w - z)⁻¹ • e (f z) i
    (∀ i, ContDiffOn ℝ 1 (S i) (ball c (R + 1))) →
    (∀ i x, x ∈ ball c (R + 1) → conjWirtingerDeriv (S i) x 1 = e (f x) i) →
    let T : ℂ → F := fun w ↦ (Real.pi : ℂ)⁻¹ • ∫ z, (w - z)⁻¹ • f z
    let L := e.symm.toContinuousLinearMap.restrictScalars ℝ
    ContDiffOn ℝ 1 T (ball c (R + 1)) ∧
    (∀ x ∈ ball c (R + 1), fderiv ℝ T x =
      L.comp (ContinuousLinearMap.pi fun i ↦ fderiv ℝ (S i) x)) ∧
    ∀ x ∈ ball c (R + 1), conjWirtingerDeriv T x 1 = f x := by
  classical
  let := Fintype.ofFinite ι
  intro S hS hI T L
  have hT : T = fun w ↦ L (fun i ↦ S i w) := by
    funext w
    exact (e.symm_apply_apply (T w)).symm.trans
      (congrArg e.symm (normalizedCauchy_coordinates e hf hs w))
  have hSi (i) (x : ℂ) (hx : x ∈ ball c (R + 1)) : DifferentiableAt ℝ (S i) x :=
    ((hS i).contDiffAt (isOpen_ball.mem_nhds hx)).differentiableAt one_ne_zero
  have hDT (x : ℂ) (hx : x ∈ ball c (R + 1)) : fderiv ℝ T x =
      L.comp (ContinuousLinearMap.pi fun i ↦ fderiv ℝ (S i) x) := by
    rw [hT]
    exact (L.hasFDerivAt.comp x (hasFDerivAt_pi.mpr fun i ↦ (hSi i x hx).hasFDerivAt)).fderiv
  refine ⟨?_, hDT, fun x hx ↦ ?_⟩
  · rw [hT]
    exact L.contDiff.comp_contDiffOn (contDiffOn_pi.mpr hS)
  · apply e.injective
    rw [conjWirtingerDeriv_apply, hDT x hx]
    simp only [ContinuousLinearMap.comp_apply, L,
      ContinuousLinearMap.coe_restrictScalars', ContinuousLinearEquiv.coe_coe,
      ← map_smul, ← map_add, e.apply_symm_apply]
    funext i
    simpa only [conjWirtingerDeriv_apply, ContinuousLinearMap.pi_apply,
      Pi.smul_apply, Pi.add_apply] using hI i x hx

/-- For finite-dimensional complex normed targets, the actual Cauchy integral is `C¹` near
an output disc, its real derivative has a uniform supremum and Hölder bound, and it solves
`conjWirtingerDeriv T x 1 = f x`. The constant depends only on the target norm, exponent and
the two fixed discs.
The compatible real scalar action remains a parameter because it determines the derivative's
continuous-linear-map carrier. -/
theorem exists_contDiffOn_holderOnWith_fderiv_pi_inv_smul_integral_sub_inv_smul
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F]
    [IsScalarTower ℝ ℂ F] [FiniteDimensional ℂ F]
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) (c : ℂ) {r R : ℝ}
    (hr : 0 ≤ r) (hR : 0 ≤ R) :
    ∃ C : ℝ≥0, ∀ {f : ℂ → F} {H M : ℝ≥0},
      Function.support f ⊆ closedBall c r → HolderWith H α f → (∀ x, ‖f x‖ ≤ M) →
      let T : ℂ → F := fun w ↦ (Real.pi : ℂ)⁻¹ • ∫ z, (w - z)⁻¹ • f z
      ContDiffOn ℝ 1 T (ball c (R + 1)) ∧
      HolderOnWith (C * (H + M)) α (fderiv ℝ T) (closedBall c R) ∧
        (∀ x ∈ closedBall c R, ‖fderiv ℝ T x‖ ≤ C * (H + M)) ∧
        ∀ x ∈ ball c (R + 1), conjWirtingerDeriv T x 1 = f x := by
  -- The real action is uniquely determined by the caller's compatible complex action.
  cases NormedSpace.restrictScalars_eq (𝕜 := ℝ) (𝕜' := ℂ) (E := F)
  classical
  let := FiniteDimensional.complete ℂ F
  let e := (Module.finBasis ℂ F).equivFunL
  let L := e.symm.toContinuousLinearMap.restrictScalars ℝ
  obtain ⟨C, hC⟩ := exists_cauchyCoordinate_gain e hα hα1 c hr hR
  refine ⟨‖L‖₊ * C * ‖e.toContinuousLinearMap‖₊, fun {f H M} hs hf hM ↦ ?_⟩
  intro T
  let K := ‖e.toContinuousLinearMap‖₊
  let g (i : Fin (Module.finrank ℂ F)) (z : ℂ) := e (f z) i
  let S (i : Fin (Module.finrank ℂ F)) (w : ℂ) :=
    (Real.pi : ℂ)⁻¹ • ∫ z, (w - z)⁻¹ • g i z
  have hS := hC hs hf hM
  -- Reconstruct the actual integral and both derivative identities from its coordinates.
  obtain ⟨hcd, hDT, hI⟩ := cauchyCoordinate_reconstruct e (hf.continuous hα) hs
    (fun i ↦ (hS i).1) (fun i ↦ (hS i).2.2.2)
  let A (x : ℂ) := ContinuousLinearMap.pi (fun i ↦ fderiv ℝ (S i) x)
  have hsub : closedBall c R ⊆ ball c (R + 1) := closedBall_subset_ball (by linarith)
  have hconst : (‖L‖₊ * C * ‖e.toContinuousLinearMap‖₊) * (H + M) =
      ‖L‖₊ * (C * (K * H + K * M)) := by dsimp only [K]; ring
  refine ⟨hcd, ?_, (fun x hx ↦ ?_), hI⟩
  · apply HolderOnWith.of_dist_le
    intro x hx y hy
    rw [dist_eq_norm, hDT x (hsub hx), hDT y (hsub hy), ← L.comp_sub, hconst]
    have hA : A x - A y = ContinuousLinearMap.pi
        (fun i ↦ fderiv ℝ (S i) x - fderiv ℝ (S i) y) := by
      ext v i
      rfl
    calc
      _ ≤ ‖L‖ * ‖A x - A y‖ := L.opNorm_comp_le _
      _ ≤ ‖L‖ * ((C * (K * H + K * M) : ℝ≥0) * dist x y ^ (α : ℝ)) := by
        gcongr
        rw [hA]
        exact ContinuousLinearMap.norm_pi_le_of_le (fun i ↦ by
          simpa only [dist_eq_norm] using (hS i).2.1.dist_le hx hy) (by positivity)
      _ = _ := by push_cast; ring
  · rw [hDT x (hsub hx)]
    rw [← NNReal.coe_add, ← NNReal.coe_mul, hconst]
    simp only [NNReal.coe_mul, coe_nnnorm]
    exact (L.opNorm_comp_le _).trans (mul_le_mul_of_nonneg_left
      (ContinuousLinearMap.norm_pi_le_of_le (fun i ↦ (hS i).2.2.1 x hx) (by positivity))
      (norm_nonneg _))

end TauCeti
