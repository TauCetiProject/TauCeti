/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Group.Integral
public import TauCeti.Analysis.Calculus.ContDiff.Integrable
public import TauCeti.Analysis.Convolution

import Mathlib.Analysis.Calculus.LineDeriv.Basic

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

The dominated results use a measure invariant under translations and negation. Translations,
negation and open sets are measurable. The continuity theorem needs a seminormed abelian
domain, any nontrivially normed scalar field, and second-countability of either the domain or
the kernel's codomain. The convolution codomain also carries the real normed-space structure
needed for the Bochner integral. The dominated derivative statements use a second-countable
real normed domain.

The iterated derivative of `f ⋆[L, μ] g` is a convolution against the iterated derivative of `g`,
for the bilinear map `L_n` sending `(a, B)` to the multilinear map `m ↦ L a (B m)`
(`ContinuousLinearMap.compContinuousMultilinearMapL` composed with `L`).

For a compactly supported `C¹` factor `g`, the file also records the directional form
`∂ᵥ (f ⋆ g) = f ⋆ ∂ᵥ g` of Mathlib's rule `HasCompactSupport.hasFDerivAt_convolution_right`, in
which the derivative is a convolution with values in `F` rather than in a space of linear maps.

For mollification by a nonnegative compactly supported kernel `ρ` of integral `1`, the file
records two bounds that need no regularity of the mollified function `u`. One-sided bounds on the
forward differences of `u` in a direction pass to the directional derivative of `ρ ⋆ u`: this is
how a nonsmooth subsolution of a Hamilton–Jacobi inequality, such as a Hopf–Lax function, becomes
a smooth one. And a bounded `u` has a mollification with bounded derivative.

## Main declarations

* `MeasureTheory.continuous_convolution_right_of_dominated`: continuity of `f ⋆ g`.
* `MeasureTheory.hasFDerivAt_convolution_right_of_dominated`: `D (f ⋆ g) = f ⋆ D g`.
* `MeasureTheory.iteratedFDeriv_convolution_right_of_dominated`: `D^n (f ⋆ g) = f ⋆ D^n g`.
* `MeasureTheory.contDiff_convolution_right_of_dominated`,
  `MeasureTheory.contDiff_convolution_left_of_dominated`: `f ⋆ g` is `C^N` when the smooth factor
  is.
* `MeasureTheory.iteratedFDeriv_convolution_left_of_dominated`: `D^n (f ⋆ g) = D^n f ⋆ g`.
* `HasCompactSupport.fderiv_convolution_right_apply`: for `g` compactly supported, the
  directional derivative `∂ᵥ (f ⋆ g) = f ⋆ ∂ᵥ g`.
* `HasCompactSupport.fderiv_convolution_left_apply_le`: mollifying by a nonnegative kernel of
  integral `1` turns a one-sided bound `u (y + s • d) ≤ u y + s * c` on forward differences into
  the bound `∂_d (ρ ⋆ u) ≤ c` on the directional derivative.
* `HasCompactSupport.norm_fderiv_convolution_left_le`: the mollification of a function bounded by
  `M` has derivative bounded by `M * ∫ ‖Dρ‖`.
-/

public section

noncomputable section

namespace MeasureTheory

open ContinuousLinearMap Filter Metric Set
open scoped Convolution Topology

variable {G E E' F : Type*} {f : G → E} {g : G → E'} {φ : G → ℝ} {M : ℝ}

section

variable [SeminormedAddCommGroup G] [SeminormedAddGroup E]
  [SeminormedAddGroup E'] [Norm F] (L : E → E' → F)

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

end

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace ℝ F] [MeasurableSpace G] {μ : Measure G}
  [SeminormedAddCommGroup G] [OpensMeasurableSpace G] [MeasurableAdd G] [MeasurableNeg G]
  [SecondCountableTopologyEither G E'] [μ.IsAddLeftInvariant] [μ.IsNegInvariant]
  (L : E →L[𝕜] E' →L[𝕜] F)

/-- The convolution of an essentially bounded function with a continuous function that is
dominated, uniformly on unit translates, by an integrable function is continuous. -/
theorem continuous_convolution_right_of_dominated (hf : AEStronglyMeasurable f μ)
    (hfM : ∀ᵐ t ∂μ, ‖f t‖ ≤ M) (hg : Continuous g) (hφ : Integrable φ μ)
    (hgφ : ∀ z h, ‖h‖ ≤ 1 → ‖g (z + h)‖ ≤ φ z) : Continuous (f ⋆[L, μ] g) := by
  refine continuous_iff_continuousAt.2 fun x₀ => continuousAt_of_dominated
    (Eventually.of_forall fun x => L.aestronglyMeasurable_comp₂ hf
      (hg.comp ((continuous_const (y := x)).sub continuous_id)).aestronglyMeasurable) ?_
    ((hφ.comp_sub_left x₀).const_mul (‖L‖ * M)) (Eventually.of_forall fun t => ?_)
  · filter_upwards [ball_mem_nhds x₀ one_pos] with x hx
    filter_upwards [hfM] with t ht
    exact norm_convolution_integrand_le (fun a b => L a b) (norm_nonneg L) L.le_opNorm₂ hgφ hx ht
  · exact ((L (f t)).continuous.comp (hg.comp (continuous_id.sub continuous_const))).continuousAt

end

variable [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [MeasurableSpace G] {μ : Measure G} {N : ℕ∞} (L : E →L[ℝ] E' →L[ℝ] F)

section

variable [NormedAddCommGroup G] [NormedSpace ℝ G] [OpensMeasurableSpace G] [MeasurableAdd G]
  [MeasurableNeg G] [SecondCountableTopology G] [μ.IsAddLeftInvariant] [μ.IsNegInvariant]

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
    (Eventually.of_forall fun x => L.aestronglyMeasurable_comp₂ hf
      (hg.continuous.comp ((continuous_const (y := x)).sub continuous_id)).aestronglyMeasurable)
    (convolutionExists_of_ae_norm_le_of_integrable L hf hfM hgi x₀)
    ((L.precompR G).aestronglyMeasurable_comp₂ hf
      ((hg.continuous_fderiv one_ne_zero).comp
        ((continuous_const (y := x₀)).sub continuous_id)).aestronglyMeasurable)
    ?_ ((hφ.comp_sub_left x₀).const_mul (‖L‖ * M))
    (Eventually.of_forall fun t x _ => (L (f t)).hasFDerivAt.comp x (hdiff x t))
  filter_upwards [hfM] with t ht x hx
  -- `‖(L.precompR G) a B‖ = ‖(L a).comp B‖ ≤ ‖L‖ ‖a‖ ‖B‖`.
  refine norm_convolution_integrand_le (fun a B => (L.precompR G) a B) (norm_nonneg L)
    (fun a B => ?_) hgφ hx ht
  exact (opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_right (L.le_opNorm a) (norm_nonneg _))

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
    refine ((continuousMultilinearCurryFin0 ℝ G F).symm.toContinuousLinearEquiv.integral_comp_comm
      _).symm.trans (integral_congr_ae (ae_of_all _ fun t => ?_))
    ext m
    rfl
  | succ n ih =>
    have hn' : (n : ℕ∞) ≤ N := le_trans (by exact_mod_cast n.le_succ) hn
    funext x
    obtain ⟨hgn, hgi, φ, hφ, hgφn⟩ := hg.iteratedFDeriv_dominated (μ := μ) hgφ hn
    rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, ih hn',
      (hasFDerivAt_convolution_right_of_dominated _ hf hfM hgn hgi hφ hgφn x).fderiv,
      convolution_def, convolution_def]
    refine (ContinuousLinearEquiv.integral_comp_comm (𝕜 := ℝ) (μ := μ)
      (E := G →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin n => G) F)
      (F := ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) => G) F)
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => G)
        F).symm.toContinuousLinearEquiv _).symm.trans
      (integral_congr_ae (ae_of_all _ fun t => ?_))
    ext m
    simp [iteratedFDeriv_succ_eq_comp_left]
    rfl

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
      hg.iteratedFDeriv_dominated (μ := μ) hgφ (Order.add_one_le_of_lt hm)
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

end

variable [NormedAddCommGroup G] [NormedSpace ℝ G] [BorelSpace G] [SFinite μ]
  [μ.IsAddLeftInvariant]

/-- **Directional derivatives of a convolution.** If `f` is locally integrable and `g` is `C¹`
with compact support, then the derivative of `f ⋆ g` in a direction `v` is the convolution of `f`
with the derivative of `g` in the direction `v`. -/
theorem _root_.HasCompactSupport.fderiv_convolution_right_apply (hcg : HasCompactSupport g)
    (hf : LocallyIntegrable f μ) (hg : ContDiff ℝ 1 g) (x v : G) :
    fderiv ℝ (f ⋆[L, μ] g) x v = (f ⋆[L, μ] fun y => fderiv ℝ g y v) x := by
  rw [(hcg.hasFDerivAt_convolution_right L hf hg x).fderiv,
    convolution_precompR_apply L hf (hcg.fderiv (𝕜 := ℝ)) (hg.continuous_fderiv one_ne_zero) x v]

section Mollifier

variable [μ.IsNegInvariant] {ρ : G → ℝ}

/-- **Mollifying a one-sided difference bound.** Let `ρ` be a nonnegative `C¹` compactly supported
kernel of integral `1` and `u` a locally integrable function. If, for all small `s > 0`, the
forward difference `u (y + s • d) - u y` is at most `s * c` at every point `y = x - z` with
`z` in the support of `ρ`, then the derivative of the mollification `ρ ⋆ u` at `x` in the
direction `d` is at most `c`. No regularity of `u` is needed. -/
theorem _root_.HasCompactSupport.fderiv_convolution_left_apply_le (hρc : HasCompactSupport ρ)
    (hρ : ContDiff ℝ 1 ρ) (hρ0 : ∀ y, 0 ≤ ρ y) (hρ1 : ∫ y, ρ y ∂μ = 1) {u : G → ℝ}
    (hu : LocallyIntegrable u μ) {x d : G} {c : ℝ}
    (h : ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ z ∈ Function.support ρ, u (x - z + s • d) ≤ u (x - z) + s * c) :
    fderiv ℝ (ρ ⋆[lsmul ℝ ℝ, μ] u) x d ≤ c := by
  have hD := hρc.hasFDerivAt_convolution_left (lsmul ℝ ℝ) hρ hu x
  have hconv := hρc.convolutionExists_left (lsmul ℝ ℝ) hρ.continuous hu (μ := μ)
  have hρi : Integrable ρ μ := integrable_of_integral_eq_one hρ1
  have hi : Integrable (fun z ↦ ρ z * u (x - z)) μ := by simpa using (hconv x).integrable
  rw [hD.fderiv]
  refine le_of_tendsto (hD.hasLineDerivAt d).tendsto_slope_zero_right ?_
  filter_upwards [h, self_mem_nhdsWithin] with s hs (hs0 : 0 < s)
  -- Averaging the difference bound against `ρ`, of integral `1`.
  have hle : (ρ ⋆[lsmul ℝ ℝ, μ] u) (x + s • d) ≤ (ρ ⋆[lsmul ℝ ℝ, μ] u) x + s * c := by
    have h1 : (ρ ⋆[lsmul ℝ ℝ, μ] u) x + s * c = ∫ z, ρ z * u (x - z) + ρ z * (s * c) ∂μ := by
      rw [integral_add hi (hρi.mul_const _), integral_mul_const, hρ1, one_mul, convolution_def]
      simp
    rw [h1, convolution_def]
    refine integral_mono (hconv _).integrable (hi.add (hρi.mul_const _)) fun z ↦ ?_
    simp only [lsmul_apply, smul_eq_mul]
    by_cases hz : ρ z = 0
    · simp [hz]
    rw [show x + s • d - z = x - z + s • d by abel, ← mul_add]
    exact mul_le_mul_of_nonneg_left (hs z hz) (hρ0 z)
  rw [smul_eq_mul, inv_mul_le_iff₀ hs0]
  linarith

/-- The mollification `ρ ⋆ u` of a function bounded by `M`, by a `C¹` compactly supported kernel
`ρ`, has derivative bounded by `M * ∫ ‖Dρ‖`, uniformly in the point. -/
theorem _root_.HasCompactSupport.norm_fderiv_convolution_left_le [IsFiniteMeasureOnCompacts μ]
    (hρc : HasCompactSupport ρ) (hρ : ContDiff ℝ 1 ρ) {u : G → E'} (hu : LocallyIntegrable u μ)
    (huM : ∀ y, ‖u y‖ ≤ M) (x : G) :
    ‖fderiv ℝ (ρ ⋆[lsmul ℝ ℝ, μ] u) x‖ ≤ M * ∫ y, ‖fderiv ℝ ρ y‖ ∂μ := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (huM 0)
  refine opNorm_le_bound _ (mul_nonneg hM (integral_nonneg fun y ↦ norm_nonneg _)) fun d ↦ ?_
  have hgi : Integrable (fun y ↦ ‖fderiv ℝ ρ y‖) μ :=
    (hρ.continuous_fderiv one_ne_zero).norm.integrable_of_hasCompactSupport (hρc.fderiv ℝ).norm
  rw [← convolution_flip, hρc.fderiv_convolution_right_apply _ hu hρ, convolution_def]
  refine (norm_integral_le_of_norm_le ((hgi.comp_sub_left x).mul_const (M * ‖d‖))
    (Eventually.of_forall fun y ↦ ?_)).trans_eq ?_
  · simp only [flip_apply, lsmul_apply, norm_smul]
    calc ‖fderiv ℝ ρ (x - y) d‖ * ‖u y‖ ≤ (‖fderiv ℝ ρ (x - y)‖ * ‖d‖) * M :=
          mul_le_mul ((fderiv ℝ ρ (x - y)).le_opNorm d) (huM y) (norm_nonneg _) (by positivity)
      _ = ‖fderiv ℝ ρ (x - y)‖ * (M * ‖d‖) := by ring
  · rw [integral_mul_const, integral_sub_left_eq_self (fun y ↦ ‖fderiv ℝ ρ y‖) μ x]
    ring

end Mollifier

end MeasureTheory
