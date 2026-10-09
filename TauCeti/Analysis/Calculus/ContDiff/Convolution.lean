/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Group.Integral

/-!
# Smoothness of convolutions with dominated kernels

Mathlib differentiates a convolution `f ⋆ g` under the integral sign when one factor is `C^n`
with compact support (`HasCompactSupport.contDiff_convolution_right`). Kernels such as the heat
kernel are not compactly supported, but their derivatives decay fast enough to be dominated,
uniformly over unit translates, by integrable functions: for each order `n` there is an
integrable `φ` with `‖D^n g (z + h)‖ ≤ φ z` whenever `‖h‖ ≤ 1`. This file proves that if the
other factor is essentially bounded, then `f ⋆ g` is as smooth as `g`, and its derivatives are
computed by differentiating `g` under the integral. The first-order argument is that of Mathlib's
`HasCompactSupport.hasFDerivAt_convolution_right`, with the compact-support bound replaced by the
domination hypothesis.

The iterated derivative of `f ⋆[L, μ] g` is a convolution against the iterated derivative of `g`,
for the bilinear map `L_n` sending `(a, B)` to the multilinear map `m ↦ L a (B m)`
(`ContinuousLinearMap.compContinuousMultilinearMapL` composed with `L`).

## Main declarations

* `TauCeti.convolutionExists_of_ae_norm_le_of_integrable`,
  `TauCeti.convolutionExists_of_integrable_of_ae_norm_le`: an essentially bounded function
  convolves with an integrable one.
* `TauCeti.continuous_convolution_right_of_dominated`: continuity of `f ⋆ g`.
* `TauCeti.hasFDerivAt_convolution_right_of_dominated`: `D (f ⋆ g) = f ⋆ D g`.
* `TauCeti.iteratedFDeriv_convolution_right_of_dominated`: `D^n (f ⋆ g) = f ⋆ D^n g`.
* `TauCeti.contDiff_convolution_right_of_dominated`,
  `TauCeti.contDiff_convolution_left_of_dominated`: `f ⋆ g` is `C^N` when the smooth factor is.
* `TauCeti.iteratedFDeriv_convolution_left_of_dominated`: `D^n (f ⋆ g) = D^n f ⋆ g`.
-/

public section

noncomputable section

namespace TauCeti

open ContinuousLinearMap Filter Metric MeasureTheory Set
open scoped Convolution Topology

variable {G E E' F : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [SFinite μ] [μ.IsAddLeftInvariant]
  [μ.IsNegInvariant]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {f : G → E} {g : G → E'} {φ : G → ℝ} {M : ℝ}

variable (L : E →L[ℝ] E' →L[ℝ] F)

/-- An essentially bounded function convolves with an integrable function at every point. -/
theorem convolutionExists_of_ae_norm_le_of_integrable (hf : AEStronglyMeasurable f μ)
    (hfM : ∀ᵐ t ∂μ, ‖f t‖ ≤ M) (hg : Integrable g μ) : ConvolutionExists f g L μ := fun x => by
  refine ((hg.comp_sub_left x).norm.const_mul (‖L‖ * M)).mono'
    (hf.convolution_integrand_snd L hg.aestronglyMeasurable x) ?_
  filter_upwards [hfM] with t ht
  refine (L.le_opNorm₂ _ _).trans ?_
  gcongr

/-- An integrable function convolves with an essentially bounded function at every point. -/
theorem convolutionExists_of_integrable_of_ae_norm_le (hf : Integrable f μ)
    (hg : AEStronglyMeasurable g μ) (hgM : ∀ᵐ t ∂μ, ‖g t‖ ≤ M) : ConvolutionExists f g L μ :=
  fun x =>
    convolutionExistsAt_flip.1 (convolutionExists_of_ae_norm_le_of_integrable L.flip hg hgM hf x)

omit [NormedSpace ℝ G] [FiniteDimensional ℝ G] [MeasurableSpace G] [BorelSpace G] in
/-- If `g` is dominated by `φ` on unit translates and `‖L a b‖ ≤ C ‖a‖ ‖b‖`, then for `x` within
distance one of `x₀`, the convolution integrand at `x` is dominated by `C M φ (x₀ - t)`. -/
private theorem norm_convolution_integrand_le {C : ℝ} (hC : 0 ≤ C)
    (hL : ∀ a b, ‖L a b‖ ≤ C * ‖a‖ * ‖b‖) (hgφ : ∀ z h, ‖h‖ ≤ 1 → ‖g (z + h)‖ ≤ φ z)
    {x₀ x t : G} (hx : x ∈ ball x₀ 1) (ht : ‖f t‖ ≤ M) :
    ‖L (f t) (g (x - t))‖ ≤ C * M * φ (x₀ - t) := by
  have hxt : x - t = (x₀ - t) + (x - x₀) := by abel
  have hφ := hgφ (x₀ - t) (x - x₀) (by rw [← dist_eq_norm]; exact (mem_ball.1 hx).le)
  rw [hxt]
  refine (hL _ _).trans ?_
  have hM : 0 ≤ M := (norm_nonneg _).trans ht
  gcongr

/-- The convolution of an essentially bounded function with a continuous function that is
dominated, uniformly on unit translates, by an integrable function is continuous. -/
theorem continuous_convolution_right_of_dominated (hf : AEStronglyMeasurable f μ)
    (hfM : ∀ᵐ t ∂μ, ‖f t‖ ≤ M) (hg : Continuous g) (hφ : Integrable φ μ)
    (hgφ : ∀ z h, ‖h‖ ≤ 1 → ‖g (z + h)‖ ≤ φ z) : Continuous (f ⋆[L, μ] g) := by
  refine continuous_iff_continuousAt.2 fun x₀ => continuousAt_of_dominated
    (Eventually.of_forall fun x => hf.convolution_integrand_snd L hg.aestronglyMeasurable x) ?_
    ((hφ.comp_sub_left x₀).const_mul (‖L‖ * M)) (Eventually.of_forall fun t => ?_)
  · filter_upwards [ball_mem_nhds x₀ one_pos] with x hx
    filter_upwards [hfM] with t ht
    exact norm_convolution_integrand_le L (norm_nonneg L) L.le_opNorm₂ hgφ hx ht
  · exact ((L (f t)).continuous.comp (hg.comp (continuous_id.sub continuous_const))).continuousAt

/-- **Differentiating a convolution under the integral.** Let `f` be essentially bounded and `g`
be `C¹` and integrable, with `D g` dominated, uniformly on unit translates, by an integrable
function. Then `D (f ⋆ g) = f ⋆ D g`. -/
theorem hasFDerivAt_convolution_right_of_dominated (hf : AEStronglyMeasurable f μ)
    (hfM : ∀ᵐ t ∂μ, ‖f t‖ ≤ M) (hg : ContDiff ℝ 1 g) (hgi : Integrable g μ)
    (hφ : Integrable φ μ) (hgφ : ∀ z h, ‖h‖ ≤ 1 → ‖fderiv ℝ g (z + h)‖ ≤ φ z) (x₀ : G) :
    HasFDerivAt (f ⋆[L, μ] g) ((f ⋆[L.precompR G, μ] fderiv ℝ g) x₀) x₀ := by
  have hdiff : ∀ x t, HasFDerivAt (fun x => g (x - t)) (fderiv ℝ g (x - t)) x := fun x t => by
    simpa [Function.comp_def] using ((hg.differentiable one_ne_zero) (x - t)).hasFDerivAt.comp x
      ((hasFDerivAt_id x).sub_const t)
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (ball_mem_nhds x₀ one_pos)
    (Eventually.of_forall fun x => hf.convolution_integrand_snd L hg.continuous.aestronglyMeasurable
      x) (convolutionExists_of_ae_norm_le_of_integrable L hf hfM hgi x₀)
    (hf.convolution_integrand_snd (L.precompR G)
      (hg.continuous_fderiv one_ne_zero).aestronglyMeasurable x₀)
    ?_ ((hφ.comp_sub_left x₀).const_mul (‖L‖ * M))
    (Eventually.of_forall fun t x _ => (L (f t)).hasFDerivAt.comp x (hdiff x t))
  filter_upwards [hfM] with t ht x hx
  -- `‖(L.precompR G) a B‖ = ‖(L a).comp B‖ ≤ ‖L‖ ‖a‖ ‖B‖`.
  refine norm_convolution_integrand_le (L.precompR G) (norm_nonneg L) (fun a B => ?_) hgφ hx ht
  exact (opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_right (L.le_opNorm a) (norm_nonneg _))

variable {N : ℕ∞}

omit [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [BorelSpace G] [SFinite μ]
  [μ.IsAddLeftInvariant] [μ.IsNegInvariant] in
/-- A linear isometric equivalence commutes with the Bochner integral. Stated with explicit source
and target spaces, so that it applies to the currying equivalences of multilinear maps, whose
normed-group instance paths differ from the ones `ContinuousLinearEquiv.integral_comp_comm`
infers. -/
private theorem integral_linearIsometryEquiv {X Y : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] (e : X ≃ₗᵢ[ℝ] Y) (u : G → X) :
    ∫ t, e (u t) ∂μ = e (∫ t, u t ∂μ) :=
  e.toContinuousLinearEquiv.integral_comp_comm u

omit [SFinite μ] [μ.IsAddLeftInvariant] [μ.IsNegInvariant] in
/-- If `g` is `C^N` with dominated derivatives and `n + 1 ≤ N`, then `D^n g` satisfies the
hypotheses of `hasFDerivAt_convolution_right_of_dominated`. -/
private theorem iteratedFDeriv_dominated (hg : ContDiff ℝ N g)
    (hgφ : ∀ n : ℕ, n ≤ N → ∃ φ : G → ℝ, Integrable φ μ ∧
      ∀ z h, ‖h‖ ≤ 1 → ‖iteratedFDeriv ℝ n g (z + h)‖ ≤ φ z) {n : ℕ} (hn : (n + 1 : ℕ) ≤ N) :
    ContDiff ℝ 1 (iteratedFDeriv ℝ n g) ∧ Integrable (iteratedFDeriv ℝ n g) μ ∧
      ∃ φ : G → ℝ, Integrable φ μ ∧
        ∀ z h, ‖h‖ ≤ 1 → ‖fderiv ℝ (iteratedFDeriv ℝ n g) (z + h)‖ ≤ φ z := by
  have hn' : (n : ℕ∞) ≤ N := le_trans (by exact_mod_cast n.le_succ) hn
  obtain ⟨φ₀, hφ₀, hgφ₀⟩ := hgφ n hn'
  obtain ⟨φ₁, hφ₁, hgφ₁⟩ := hgφ (n + 1) hn
  have hgn : ContDiff ℝ 1 (iteratedFDeriv ℝ n g) :=
    hg.iteratedFDeriv_right (by rw [add_comm]; exact_mod_cast hn)
  refine ⟨hgn, hφ₀.mono' hgn.continuous.aestronglyMeasurable (ae_of_all _ fun z => ?_),
    φ₁, hφ₁, fun z h hh => ?_⟩
  · simpa using hgφ₀ z 0 (by simp)
  · rw [norm_fderiv_iteratedFDeriv]
    exact hgφ₁ z h hh

/-- **Iterated derivatives of a convolution.** Let `f` be essentially bounded and `g` be `C^N`,
with each derivative of order at most `N` dominated, uniformly on unit translates, by an
integrable function. Then for `n ≤ N`, `D^n (f ⋆[L] g) = f ⋆[L_n] D^n g`, where
`L_n a B = (m ↦ L a (B m))`. -/
theorem iteratedFDeriv_convolution_right_of_dominated (hf : AEStronglyMeasurable f μ)
    (hfM : ∀ᵐ t ∂μ, ‖f t‖ ≤ M) (hg : ContDiff ℝ N g)
    (hgφ : ∀ n : ℕ, n ≤ N → ∃ φ : G → ℝ, Integrable φ μ ∧
      ∀ z h, ‖h‖ ≤ 1 → ‖iteratedFDeriv ℝ n g (z + h)‖ ≤ φ z) {n : ℕ} (hn : n ≤ N) :
    iteratedFDeriv ℝ n (f ⋆[L, μ] g) =
      f ⋆[(compContinuousMultilinearMapL ℝ (fun _ : Fin n => G) E' F).comp L, μ]
        iteratedFDeriv ℝ n g := by
  induction n with
  | zero =>
    funext x
    simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply, convolution_def]
    rw [← integral_linearIsometryEquiv]
    congr 1 with t m
  | succ n ih =>
    have hn' : (n : ℕ∞) ≤ N := le_trans (by exact_mod_cast n.le_succ) hn
    funext x
    obtain ⟨hgn, hgi, φ, hφ, hgφn⟩ := iteratedFDeriv_dominated (μ := μ) hg hgφ hn
    rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, ih hn',
      (hasFDerivAt_convolution_right_of_dominated _ hf hfM hgn hgi hφ hgφn x).fderiv,
      convolution_def, convolution_def]
    refine (integral_linearIsometryEquiv (μ := μ)
      (X := G →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin n => G) F)
      (Y := ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) => G) F)
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => G) F).symm _).symm.trans
      (integral_congr_ae (ae_of_all _ fun t => ?_))
    ext m
    simp [iteratedFDeriv_succ_eq_comp_left]

/-- **Smoothness of a convolution.** Let `f` be essentially bounded and `g` be `C^N`, with each
derivative of order at most `N` dominated, uniformly on unit translates, by an integrable
function. Then `f ⋆ g` is `C^N`. -/
theorem contDiff_convolution_right_of_dominated (hf : AEStronglyMeasurable f μ)
    (hfM : ∀ᵐ t ∂μ, ‖f t‖ ≤ M) (hg : ContDiff ℝ N g)
    (hgφ : ∀ n : ℕ, n ≤ N → ∃ φ : G → ℝ, Integrable φ μ ∧
      ∀ z h, ‖h‖ ≤ 1 → ‖iteratedFDeriv ℝ n g (z + h)‖ ≤ φ z) :
    ContDiff ℝ N (f ⋆[L, μ] g) := by
  refine contDiff_iff_continuous_differentiable.2 ⟨fun m hm => ?_, fun m hm x => ?_⟩
  · rw [iteratedFDeriv_convolution_right_of_dominated L hf hfM hg hgφ hm]
    obtain ⟨φ, hφ, hgφm⟩ := hgφ m hm
    exact continuous_convolution_right_of_dominated _ hf hfM
      (hg.continuous_iteratedFDeriv (by exact_mod_cast hm)) hφ hgφm
  · rw [iteratedFDeriv_convolution_right_of_dominated L hf hfM hg hgφ hm.le]
    obtain ⟨hgn, hgi, φ, hφ, hgφn⟩ :=
      iteratedFDeriv_dominated (μ := μ) hg hgφ (Order.add_one_le_of_lt hm)
    exact (hasFDerivAt_convolution_right_of_dominated _ hf hfM hgn hgi hφ hgφn x).differentiableAt

/-- **Smoothness of a convolution**, with the smooth factor on the left. -/
theorem contDiff_convolution_left_of_dominated (hf : ContDiff ℝ N f)
    (hfφ : ∀ n : ℕ, n ≤ N → ∃ φ : G → ℝ, Integrable φ μ ∧
      ∀ z h, ‖h‖ ≤ 1 → ‖iteratedFDeriv ℝ n f (z + h)‖ ≤ φ z)
    (hg : AEStronglyMeasurable g μ) (hgM : ∀ᵐ t ∂μ, ‖g t‖ ≤ M) :
    ContDiff ℝ N (f ⋆[L, μ] g) := by
  rw [← convolution_flip]
  exact contDiff_convolution_right_of_dominated L.flip hg hgM hf hfφ

/-- **Iterated derivatives of a convolution**, with the smooth factor on the left:
`D^n (f ⋆[L] g) = D^n f ⋆[L'_n] g`, where `L'_n A b = (m ↦ L (A m) b)`. -/
theorem iteratedFDeriv_convolution_left_of_dominated (hf : ContDiff ℝ N f)
    (hfφ : ∀ n : ℕ, n ≤ N → ∃ φ : G → ℝ, Integrable φ μ ∧
      ∀ z h, ‖h‖ ≤ 1 → ‖iteratedFDeriv ℝ n f (z + h)‖ ≤ φ z)
    (hg : AEStronglyMeasurable g μ) (hgM : ∀ᵐ t ∂μ, ‖g t‖ ≤ M) {n : ℕ} (hn : n ≤ N) :
    iteratedFDeriv ℝ n (f ⋆[L, μ] g) =
      iteratedFDeriv ℝ n f ⋆[((compContinuousMultilinearMapL ℝ (fun _ : Fin n => G) E F).comp
        L.flip).flip, μ] g := by
  rw [← convolution_flip, iteratedFDeriv_convolution_right_of_dominated L.flip hg hgM hf hfφ hn,
    ← convolution_flip]

end TauCeti
