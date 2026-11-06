/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Pompeiu.Schauder
public import TauCeti.Analysis.Complex.Pompeiu.Approximation
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.Sequences
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import TauCeti.Topology.MetricSpace.Holder

/-!
# The Cauchy transform gains one Hölder derivative

For real Hölder sources on one fixed support disc, the actual normalized Cauchy integral is
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
  let T : ℂ → ℂ := fun w ↦ (Real.pi : ℂ)⁻¹ • ∫ z, (w - z)⁻¹ • (f z : ℂ)
  change ContDiffOn ℝ 1 T (ball c (R + 1)) ∧
    HolderOnWith (C * (H + M)) α (fderiv ℝ T) (closedBall c R) ∧
      (∀ x ∈ closedBall c R, ‖fderiv ℝ T x‖ ≤ C * (H + M)) ∧
      ∀ x ∈ ball c (R + 1), conjWirtingerDeriv T x 1 = (f x : ℂ)
  obtain ⟨g, hgsmooth, hgs, hgH, hgM, hglim⟩ :=
    exists_contDiff_support_subset_holderWith_tendstoUniformly hα hf hM hs
  let Tn (n : ℕ) : ℂ → ℂ := fun w ↦
    (Real.pi : ℂ)⁻¹ • ∫ z, (w - z)⁻¹ • (g n z : ℂ)
  have hSmooth (n : ℕ) : ContDiff ℝ ∞ (Tn n) ∧
      HolderOnWith (C * (H + M)) α (fderiv ℝ (Tn n)) (closedBall c (R + 1)) ∧
      ∀ x ∈ closedBall c (R + 1), ‖fderiv ℝ (Tn n) x‖ ≤ C * (H + M) :=
    hC (hgsmooth n) (hgs n) (hgH n) (hgM n)
  let K := closedBall c (R + 1)
  have : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_closedBall c (R + 1))
  let V (n : ℕ) : K →ᵇ (ℂ →L[ℝ] ℂ) := BoundedContinuousFunction.mkOfCompact
    ⟨fun x ↦ fderiv ℝ (Tn n) x, ((hSmooth n).1.continuous_fderiv (by simp)).comp
      continuous_subtype_val⟩
  have hEqui : Equicontinuous ((↑) : range V → K → (ℂ →L[ℝ] ℂ)) := by
    apply Metric.equicontinuous_of_continuity_modulus
      (fun t : ℝ ↦ (C * (H + M) : ℝ≥0) * t ^ (α : ℝ))
    · have hc : Continuous (fun t : ℝ ↦ (C * (H + M) : ℝ≥0) * t ^ (α : ℝ)) :=
        continuous_const.mul (Real.continuous_rpow_const α.coe_nonneg)
      simpa only [Real.zero_rpow (NNReal.coe_pos.mpr hα).ne', mul_zero] using hc.tendsto 0
    · intro x y q
      rcases q with ⟨_, n, rfl⟩
      exact (hSmooth n).2.1.dist_le x.property y.property
  have hCompact := BoundedContinuousFunction.arzela_ascoli
    (closedBall (0 : ℂ →L[ℝ] ℂ) (C * (H + M))) (isCompact_closedBall _ _) (range V)
    (fun q x hq ↦ by
      rcases hq with ⟨n, rfl⟩
      exact mem_closedBall_zero_iff.mpr ((hSmooth n).2.2 x x.property)) hEqui
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
  have hGHolder : HolderOnWith (C * (H + M)) α G K := by
    apply HolderOnWith.of_dist_le
    intro x hx y hy
    exact le_of_tendsto ((hUnifOn.tendsto_at hx).dist (hUnifOn.tendsto_at hy))
      (Eventually.of_forall fun n ↦ (hSmooth (φ n)).2.1.dist_le hx hy)
  have hGNorm (x : ℂ) (hx : x ∈ K) : ‖G x‖ ≤ (C * (H + M) : ℝ≥0) :=
    le_of_tendsto (hUnifOn.tendsto_at hx).norm
      (Eventually.of_forall fun n ↦ (hSmooth (φ n)).2.2 x hx)
  have hgsC (n : ℕ) : Function.support (fun z ↦ (g n z : ℂ)) ⊆ closedBall c (r + 1) := by
    intro z hz
    apply hgs n
    intro h
    exact hz (by change (g n z : ℂ) = 0; rw [h]; simp)
  have hfsC : Function.support (fun z ↦ (f z : ℂ)) ⊆ closedBall c (r + 1) := by
    intro z hz
    apply (closedBall_subset_closedBall (by linarith : r ≤ r + 1))
    apply hs
    intro h
    exact hz (by change (f z : ℂ) = 0; rw [h]; simp)
  have hTlim (x : ℂ) : Tendsto (fun n ↦ Tn n x) atTop (𝓝 (T x)) := by
    apply tendsto_pi_inv_smul_integral_sub_inv_smul
      (fun n ↦ continuous_ofReal.comp (hgsmooth n).continuous) hgsC hfsC
      (M := (M : ℝ)) (fun n z ↦ by simpa only [Function.comp_apply, norm_real] using hgM n z)
    intro z
    exact continuous_ofReal.continuousAt.tendsto.comp (hglim.tendsto_at z)
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
  · let L : (ℂ →L[ℝ] ℂ) → ℂ := fun A ↦ (2 : ℂ)⁻¹ • (A 1 + I • A I)
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

private theorem integral_sub_inv_mul_eq_re_add_I_mul_im {f : ℂ → ℂ}
    (hf : Continuous f) (hc : HasCompactSupport f) (w : ℂ) :
    (∫ z, (w - z)⁻¹ * f z) = (∫ z, (w - z)⁻¹ * ((f z).re : ℂ)) +
      I * (∫ z, (w - z)⁻¹ * ((f z).im : ℂ)) := by
  have hRe : Integrable (fun z ↦ (w - z)⁻¹ * ((f z).re : ℂ)) := by
    simpa only [smul_eq_mul, Function.comp_apply] using
      (Complex.locallyIntegrable_sub_inv w).integrable_smul_right_of_hasCompactSupport
        (continuous_ofReal.comp (continuous_re.comp hf))
        (hc.comp_left (g := fun z : ℂ ↦ (z.re : ℂ)) (by simp))
  have hIm : Integrable (fun z ↦ (w - z)⁻¹ * ((f z).im : ℂ)) := by
    simpa only [smul_eq_mul, Function.comp_apply] using
      (Complex.locallyIntegrable_sub_inv w).integrable_smul_right_of_hasCompactSupport
        (continuous_ofReal.comp (continuous_im.comp hf))
        (hc.comp_left (g := fun z : ℂ ↦ (z.im : ℂ)) (by simp))
  have heq (z : ℂ) : (w - z)⁻¹ * f z =
      (w - z)⁻¹ * ((f z).re : ℂ) + I * ((w - z)⁻¹ * ((f z).im : ℂ)) := by
    calc
      _ = (w - z)⁻¹ * (((f z).re : ℂ) + I * ((f z).im : ℂ)) := by
        rw [mul_comm I, (f z).re_add_im]
      _ = _ := by ring
  simp_rw [heq]
  rw [integral_add hRe (hIm.const_mul I), integral_const_mul]

/-- The actual normalized Cauchy transform maps compactly supported complex Hölder sources to
`C^{1,α}` on every fixed output disc, with a bound depending only on the two discs and `α`. -/
theorem exists_contDiffOn_holderOnWith_fderiv_pi_inv_smul_integral_sub_inv_smul
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
  let T : ℂ → ℂ := fun w ↦ (Real.pi : ℂ)⁻¹ • ∫ z, (w - z)⁻¹ • f z
  let Tr : ℂ → ℂ := fun w ↦ (Real.pi : ℂ)⁻¹ • ∫ z, (w - z)⁻¹ • ((f z).re : ℂ)
  let Ti : ℂ → ℂ := fun w ↦ (Real.pi : ℂ)⁻¹ • ∫ z, (w - z)⁻¹ • ((f z).im : ℂ)
  change ContDiffOn ℝ 1 T (ball c (R + 1)) ∧
    HolderOnWith ((2 * C) * (H + M)) α (fderiv ℝ T) (closedBall c R) ∧
      (∀ x ∈ closedBall c R, ‖fderiv ℝ T x‖ ≤ (2 * C : ℝ≥0) * (H + M)) ∧
      ∀ x ∈ ball c (R + 1), conjWirtingerDeriv T x 1 = f x
  have hsRe : Function.support (fun z ↦ (f z).re) ⊆ closedBall c r := by
    intro z hz
    apply hs
    intro h
    exact hz (by change (f z).re = 0; rw [h]; simp)
  have hsIm : Function.support (fun z ↦ (f z).im) ⊆ closedBall c r := by
    intro z hz
    apply hs
    intro h
    exact hz (by change (f z).im = 0; rw [h]; simp)
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
  · have hrx := hIr x hx
    have hix := hIi x hx
    change conjWirtingerDeriv Tr x 1 = ((f x).re : ℂ) at hrx
    change conjWirtingerDeriv Ti x 1 = ((f x).im : ℂ) at hix
    simp only [conjWirtingerDeriv_apply, smul_eq_mul, mul_one] at hrx hix ⊢
    rw [hDT x hx]
    simp only [add_apply, smul_apply, smul_eq_mul]
    calc
      _ = (2 : ℂ)⁻¹ * (fderiv ℝ Tr x 1 + I * fderiv ℝ Tr x I) +
          I * ((2 : ℂ)⁻¹ * (fderiv ℝ Ti x 1 + I * fderiv ℝ Ti x I)) := by ring
      _ = (f x).re + I * (f x).im := by rw [hrx, hix]
      _ = f x := by rw [mul_comm I, (f x).re_add_im]

end TauCeti
