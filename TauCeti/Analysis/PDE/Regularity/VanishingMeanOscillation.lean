/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.SmallMeanOscillation
public import TauCeti.Analysis.Sobolev.Poincare.Wirtinger.Divergence
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.PDE.EnergyForm.Measurability
import TauCeti.Analysis.Sobolev.W1p.CompactSupport
import TauCeti.Analysis.SpecificLimits.Absorption
import TauCeti.MeasureTheory.Function.Lp.IntermediateExponent

/-!
# The interior `W^{1,p}` estimate for coefficients of vanishing mean oscillation

Let `a` be a measurable coefficient matrix on `ℝ^{n+1}`, neither symmetric nor continuous in
general, bounded by `Λ`, and of small mean oscillation below a radius `r₀`: on every ball `B` of
radius at most `r₀` some constant matrix `A`, uniformly elliptic with constants `0 < λ ≤ Λ`, has
mean deviation `⨍_B ‖a - A‖ ≤ δ` from `a`. Coefficients of vanishing mean oscillation, uniformly
elliptic, satisfy this for every `δ > 0` once `r₀` is small, with `A` the average of `a` over `B`;
`r₀` is then governed by the VMO modulus of `a`. Let `u ∈ H¹(Ω)` be a local weak solution of

`-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` in `Ω`,

that is `∫_Ω ⟨a ∇u, ∇φ⟩ = ∫_Ω ⟨G, ∇φ⟩` for every test function `φ` on `Ω`, with no boundary
condition. This file proves the interior `W^{1,p}` estimate, `2 < p < ∞`: if `B_R = B(x₀, R) ⊆ Ω`,
`4 R ≤ r₀`, and `u`, `∇u`, `G ∈ Lᵖ(B_R)`, then

`‖∇u‖_{Lᵖ(B_{R/2})} ≤ C (‖G‖_{Lᵖ(B_R)} + |B_R|^(1/p - 1/2) ‖∇u‖_{L²(B_R)})`

(`TauCeti.PDE.exists_eLpNorm_gradient_ball_le_of_setAverage_le`), with `C` and the threshold `δ`
depending only on `n`, `p`, `λ` and `Λ`, and not on `R`, `r₀`, `u` or `G`. The estimate is
invariant under dilations, and the factor `|B_R|^(1/p - 1/2)` turns the `L²` norm of `∇u` into its
`Lᵖ` scale. It is quantitative in `u`, as it must be: `u ↦ M u` scales both sides. The membership
`∇u ∈ Lᵖ(B_R)` is an a priori assumption: the estimate bounds the norm, it does not prove that it
is finite.

## The argument

The whole-space estimate for coefficients of small mean oscillation below a radius
(`TauCeti.PDE.exists_eLpNorm_gradient_le_of_setAverage_le_of_gradient_eq_zero`) applies to
functions whose gradient vanishes outside a small ball, so the work is the localization.

* **Cutoff.** For `R/2 ≤ s < t ≤ R`, a cutoff `ζ`, equal to one on `B_s` and supported in `B_t`
  with `‖∇ζ‖ ≲ (t - s)⁻¹`, gives `w = ζ (u - u_{B_t})`, extended by zero. It solves on the whole
  space `-div(a ∇w) = -div (ζ G + (u - u_{B_t}) a ∇ζ) + h`, with the scalar forcing
  `h = ⟪G, ∇ζ⟫ - ⟪∇ζ, a ∇u⟫` supported in `B_t`. Testing the equation of `u` with `ζ` shows that
  `h` has mean zero.
* **The scalar term.** A mean-zero function on `B_t` is a divergence
  (`TauCeti.exists_memLp_forall_integral_mul_eq_integral_inner_gradient_of_integral_eq_zero`):
  `h = -div H` with `‖H‖_{Lᵖ} ≲ t |B_t|^(-ε) ‖h‖_{L^q}` for an exponent `q < p`, where
  `ε = 1/q - 1/p`. So `w` solves a pure divergence-form equation, and the whole-space estimate
  bounds `‖∇u‖_{Lᵖ(B_s)}` by `‖G‖_{Lᵖ(B_R)}`, `‖H‖_{Lᵖ}` and the Sobolev–Poincaré bound
  `‖u - u_{B_t}‖_{Lᵖ(B_t)} ≲ t |B_t|^(-ε) ‖∇u‖_{L^q(B_t)}`. Both carry the gain from `q` to `p`.
* **Absorption.** The `L^q` norm of `∇u` lies between its `L²` and `Lᵖ` norms,
  `‖∇u‖_q ≤ ‖∇u‖₂^θ ‖∇u‖_p^(1-θ)`. Young's inequality then gives
  `f(s) ≤ f(t) / 2 + A (t - s)^(-1/θ) + B` for `f(σ) = ‖∇u‖_{Lᵖ(B_σ)}`, and the absorption lemma
  `TauCeti.exists_le_mul_mul_rpow_add_of_le_mul_add` bounds `f(R/2)`. The exponent `q` is chosen
  with `ε < 1/(n + 1)`, as the Sobolev–Poincaré inequality requires.

## Main declarations

* `TauCeti.PDE.exists_eLpNorm_gradient_ball_le_of_setAverage_le`: the interior `W^{1,p}` estimate,
  `2 < p < ∞`, for coefficients of small mean oscillation below a radius.

## References

* N. V. Krylov, *Parabolic and elliptic equations with VMO coefficients*, Comm. Partial
  Differential Equations **32** (2007), 453–475.
* S.-S. Byun, L. Wang, *Elliptic equations with BMO coefficients in Reifenberg domains*, Comm.
  Pure Appl. Math. **57** (2004), 1283–1310.
* M. Giaquinta, *Multiple Integrals in the Calculus of Variations and Nonlinear Elliptic Systems*,
  Princeton University Press, 1983, Chapter V, Lemma 3.1 (the absorption lemma).
-/

public section

noncomputable section

open Filter InnerProductSpace MeasureTheory Metric Module Set TopologicalSpace Matrix
open scoped ENNReal NNReal ContDiff Distributions Gradient InnerProductSpace Topology

namespace TauCeti

namespace PDE

variable {n : ℕ}

section Localization

variable {Ω U : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
  {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}

/-- A cutoff of a local weak solution, minus a constant, extended by zero to the whole space,
with its weak gradient. -/
private theorem exists_extendByZero_cutoff (hUΩ : U ≤ Ω)
    [IsFiniteMeasure (volume.restrict (U : Set (EuclideanSpace ℝ (Fin (n + 1)))))]
    (u : W1p volume Ω 2) {ζ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hζ : ContDiff ℝ ∞ ζ)
    (hζc : HasCompactSupport ζ) (hts : tsupport ζ ⊆ U) (c : ℝ) :
    ∃ w : W1p volume (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) 2,
      ∀ᵐ x, W1p.gradient w x = (U : Set (EuclideanSpace ℝ (Fin (n + 1)))).indicator
        (fun y => ζ y • W1p.gradient u y + (W1p.value u y - c) • ∇ ζ y) x := by
  obtain ⟨N, hN, hζN, hgradN⟩ := (hζ.of_le (by simp)).exists_abs_le_and_norm_gradient_le hζc
  set uU : W1p volume U 2 := W1p.restrictL hUΩ u + W1p.const (-c)
  have hval : ∀ᵐ x ∂volume.restrict U, W1p.value uU x = W1p.value u x - c := by
    filter_upwards [W1p.value_add_const_ae (W1p.restrictL hUΩ u) (-c),
      W1p.value_restrictL_ae hUΩ u] with x h1 h2
    rw [h1, h2, sub_eq_add_neg]
  have hgr : ∀ᵐ x ∂volume.restrict U, W1p.gradient uU x = W1p.gradient u x := by
    filter_upwards [W1p.gradient_restrictL_ae hUΩ u] with x h
    rw [W1p.gradient_add_const, h]
  have hv := W1p.contDiffSMul_mem_w1p0Submodule_of_hasCompactSupport (p := 2) (by norm_num) hζ hN
    (fun x _ => hζN x) (fun x _ => hgradN x) hζc hts uU
  refine ⟨W1p0.extendByZeroL le_top ⟨_, hv⟩, ?_⟩
  have h := W1p.gradient_extendByZeroL_contDiffSMul_ae le_top hζ hN (fun x _ => hζN x)
    (fun x _ => hgradN x) uU hv
  simp only [Opens.coe_top, Measure.restrict_univ] at h
  filter_upwards [h, ae_imp_of_ae_restrict hval, ae_imp_of_ae_restrict hgr] with x hx h1 h2
  rw [hx]
  by_cases hxU : x ∈ (U : Set (EuclideanSpace ℝ (Fin (n + 1))))
  · rw [indicator_of_mem hxU, indicator_of_mem hxU, h1 hxU, h2 hxU]
  · rw [indicator_of_notMem hxU, indicator_of_notMem hxU]

/-- The test function `ζ φ` on `Ω`, for a cutoff `ζ` supported in `U ⊆ Ω` and a test function `φ`
on the whole space, with its gradient. -/
private theorem exists_testFunction_mul (hUΩ : U ≤ Ω) {ζ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    (hζ : ContDiff ℝ ∞ ζ) (hζc : HasCompactSupport ζ) (hts : tsupport ζ ⊆ U)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))), ℝ)) :
    ∃ ψ : 𝓓(Ω, ℝ), (ψ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) = (fun x => ζ x * φ x) ∧
      ∀ x, ∇ (ψ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x = ζ x • ∇ φ x + φ x • ∇ ζ x := by
  refine ⟨⟨fun x => ζ x * φ x, hζ.mul φ.contDiff, hζc.mul_right,
    (tsupport_mul_subset_left).trans (hts.trans hUΩ)⟩, rfl, fun x => ?_⟩
  apply (toDual ℝ (EuclideanSpace ℝ (Fin (n + 1)))).injective
  simp only [toDual_gradient, map_add, map_smul]
  exact fderiv_fun_mul (hζ.differentiable (by simp) x) (φ.contDiff.differentiable (by simp) x)

/-- The gradient `ζ ∇φ + φ ∇ζ` of a product is bounded by `2 N P` when `|ζ|, ‖∇ζ‖ ≤ N` and
`|φ|, ‖∇φ‖ ≤ P`. -/
private theorem norm_smul_gradient_add_smul_gradient_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {ζ φ : E → ℝ} {N P : ℝ} (hζN : ∀ x, |ζ x| ≤ N)
    (hgradN : ∀ x, ‖∇ ζ x‖ ≤ N) (hφP : ∀ x, |φ x| ≤ P) (hgradP : ∀ x, ‖∇ φ x‖ ≤ P) (x : E) :
    ‖ζ x • ∇ φ x + φ x • ∇ ζ x‖ ≤ 2 * N * P := by
  have hN : 0 ≤ N := (abs_nonneg _).trans (hζN x)
  calc ‖ζ x • ∇ φ x + φ x • ∇ ζ x‖ ≤ |ζ x| * ‖∇ φ x‖ + |φ x| * ‖∇ ζ x‖ := by
        refine (norm_add_le _ _).trans_eq ?_
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ N * P + P * N := by
        gcongr
        exacts [hζN x, hgradP x, (abs_nonneg _).trans (hφP x), hφP x, hgradN x]
    _ = 2 * N * P := by ring

/-- The four terms of the weak equation of a cutoff are integrable on `U`. -/
private theorem integrable_cutoff_terms (ha : AEStronglyMeasurable a volume)
    {Lam : ℝ} (hbd : ∀ x, ‖matrixBilinearForm (a x)‖ ≤ Lam) (hUΩ : U ≤ Ω)
    [IsFiniteMeasure (volume.restrict (U : Set (EuclideanSpace ℝ (Fin (n + 1)))))]
    {u : W1p volume Ω 2}
    {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    (hG : MemLp G 2 (volume.restrict (U : Set (EuclideanSpace ℝ (Fin (n + 1))))))
    {ζ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hζ : ContDiff ℝ ∞ ζ) (hζc : HasCompactSupport ζ)
    (c : ℝ) (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))), ℝ)) :
    Integrable (fun x => matrixBilinearForm (a x) (ζ x • ∇ φ x + φ x • ∇ ζ x)
      (W1p.gradient u x)) (volume.restrict U) ∧
    Integrable (fun x => φ x * matrixBilinearForm (a x) (∇ ζ x) (W1p.gradient u x))
      (volume.restrict U) ∧
    Integrable (fun x => (W1p.value u x - c) *
      matrixBilinearForm (a x) (∇ φ x) (∇ ζ x)) (volume.restrict U) ∧
    Integrable (fun x => ⟪G x, ζ x • ∇ φ x + φ x • ∇ ζ x⟫_ℝ) (volume.restrict U) := by
  have hle : volume.restrict (U : Set (EuclideanSpace ℝ (Fin (n + 1)))) ≤
      volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))) :=
    Measure.restrict_mono hUΩ le_rfl
  obtain ⟨N, -, hζN, hgradN⟩ := (hζ.of_le (by simp)).exists_abs_le_and_norm_gradient_le hζc
  obtain ⟨P, hP, hφP, hgradP⟩ :=
    (φ.contDiff.of_le (by simp)).exists_abs_le_and_norm_gradient_le φ.hasCompactSupport
  have hLam : 0 ≤ Lam := (ContinuousLinearMap.opNorm_nonneg _).trans (hbd 0)
  have hBle (x : EuclideanSpace ℝ (Fin (n + 1))) (v w : EuclideanSpace ℝ (Fin (n + 1))) :
      ‖matrixBilinearForm (a x) v w‖ ≤ Lam * ‖v‖ * ‖w‖ :=
    ((matrixBilinearForm (a x)).le_opNorm₂ v w).trans (by gcongr; exact hbd x)
  have hBm : AEStronglyMeasurable (fun x => matrixBilinearForm (a x)) (volume.restrict U) :=
    (continuous_matrixBilinearForm.comp_aestronglyMeasurable ha).restrict
  have hgu : MemLp (W1p.gradient u : _ → EuclideanSpace ℝ (Fin (n + 1))) 2 (volume.restrict U) :=
    (Lp.memLp (W1p.gradient u)).mono_measure hle
  have hvu : MemLp (fun x => W1p.value u x - c) 2 (volume.restrict U) :=
    ((Lp.memLp (W1p.value u)).mono_measure hle).sub (memLp_const c)
  have hgζ := ContDiff.continuous_gradient hζ (by simp)
  have hψN := norm_smul_gradient_add_smul_gradient_le hζN hgradN hφP hgradP
  have hT1 : Integrable (fun x => matrixBilinearForm (a x) (ζ x • ∇ φ x + φ x • ∇ ζ x)
      (W1p.gradient u x)) (volume.restrict U) := by
    refine ((hgu.integrable one_le_two).norm.const_mul (Lam * (2 * N * P))).mono'
      (aestronglyMeasurable_matrixBilinearForm_apply hBm
        (Continuous.aestronglyMeasurable (by fun_prop))
        ((Lp.aestronglyMeasurable _).mono_measure hle)) (ae_of_all _ fun x => ?_)
    exact (hBle x _ _).trans (by gcongr; exact hψN x)
  have hT2 : Integrable (fun x => φ x * matrixBilinearForm (a x) (∇ ζ x) (W1p.gradient u x))
      (volume.restrict U) := by
    refine ((hgu.integrable one_le_two).norm.const_mul (P * (Lam * N))).mono'
      ((Continuous.aestronglyMeasurable (by fun_prop)).mul
        (aestronglyMeasurable_matrixBilinearForm_apply hBm
          (Continuous.aestronglyMeasurable (by fun_prop))
          ((Lp.aestronglyMeasurable _).mono_measure hle))) (ae_of_all _ fun x => ?_)
    rw [norm_mul, Real.norm_eq_abs, mul_assoc P]
    exact mul_le_mul (hφP x) ((hBle x _ _).trans (by gcongr; exact hgradN x))
      (norm_nonneg _) hP
  have hT3 : Integrable (fun x => (W1p.value u x - c) *
      matrixBilinearForm (a x) (∇ φ x) (∇ ζ x)) (volume.restrict U) := by
    refine ((hvu.integrable one_le_two).norm.mul_const (Lam * P * N)).mono'
      (hvu.aestronglyMeasurable.mul (aestronglyMeasurable_matrixBilinearForm_apply hBm
        (Continuous.aestronglyMeasurable (by fun_prop))
        (Continuous.aestronglyMeasurable (by fun_prop)))) (ae_of_all _ fun x => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left ((hBle x _ _).trans (by gcongr <;> simp_all))
      (norm_nonneg _)
  have hT4 : Integrable (fun x => ⟪G x, ζ x • ∇ φ x + φ x • ∇ ζ x⟫_ℝ) (volume.restrict U) := by
    refine ((hG.integrable one_le_two).norm.mul_const (2 * N * P)).mono'
      (hG.aestronglyMeasurable.inner (Continuous.aestronglyMeasurable (by fun_prop)))
      (ae_of_all _ fun x => ?_)
    exact (norm_inner_le_norm _ _).trans (by gcongr; exact hψN x)
  exact ⟨hT1, hT2, hT3, hT4⟩

/-- The weak equation of `u` tested against `ζ φ`, whose gradient vanishes off `U`. -/
private theorem setIntegral_cutoff_test_eq (hUΩ : U ≤ Ω) {u : W1p volume Ω 2}
    {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    (hu : ∀ φ : 𝓓(Ω, ℝ), energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume Ω 2 φ) =
      ∫ x in Ω, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ)
    {ζ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hζ : ContDiff ℝ ∞ ζ) (hζc : HasCompactSupport ζ)
    (hts : tsupport ζ ⊆ U) (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))), ℝ)) :
    ∫ x in U, matrixBilinearForm (a x) (ζ x • ∇ φ x + φ x • ∇ ζ x)
      (W1p.gradient u x) = ∫ x in U, ⟪G x, ζ x • ∇ φ x + φ x • ∇ ζ x⟫_ℝ := by
  set V := (U : Set (EuclideanSpace ℝ (Fin (n + 1))))
  have hUΩ' : V ⊆ Ω := hUΩ
  obtain ⟨ψ, -, hgradψ⟩ := exists_testFunction_mul hUΩ hζ hζc hts φ
  have hψ0 : ∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))) \ V,
      ζ x • ∇ φ x + φ x • ∇ ζ x = 0 := fun x hx => by
    have hxζ : x ∉ tsupport ζ := fun h => hx.2 (hts h)
    rw [image_eq_zero_of_notMem_tsupport hxζ, gradient_of_notMem_tsupport hxζ, zero_smul,
      smul_zero, add_zero]
  have h := hu ψ
  rw [energyFormH1_zero_zero_eq_setIntegral] at h
  rw [← setIntegral_eq_of_subset_of_forall_sdiff_eq_zero Ω.isOpen.measurableSet hUΩ'
      (fun x hx => by simp [hψ0 x hx]),
    ← setIntegral_eq_of_subset_of_forall_sdiff_eq_zero Ω.isOpen.measurableSet hUΩ'
      (fun x hx => by rw [hψ0 x hx, inner_zero_right])]
  calc ∫ x in Ω, matrixBilinearForm (a x) (ζ x • ∇ φ x + φ x • ∇ ζ x) (W1p.gradient u x)
      = ∫ x in Ω, matrixBilinearForm (a x)
          (W1p.gradient (W1p.ofTestFunctionₗ volume Ω 2 ψ) x) (W1p.gradient u x) := by
        refine integral_congr_ae ?_
        filter_upwards [gradientTestFunctionLp_apply_ae (mu := volume) 2 ψ] with x hx
        rw [W1p.gradient_ofTestFunctionₗ, hx, hgradψ]
    _ = ∫ x in Ω, ⟪G x, ∇ (ψ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ := h
    _ = _ := by simp_rw [hgradψ]

/-- **The weak equation of a cutoff of a local weak solution.** If `u` solves `-div(a ∇u) = -div G`
weakly in `Ω`, and `w` is the extension by zero of `ζ (u - c)` for a cutoff `ζ` supported in
`U ⊆ Ω`, then `w` solves on the whole space

`-div(a ∇w) = -div (ζ G + (u - c) a ∇ζ) + ⟪G, ∇ζ⟫ - ⟪∇ζ, a ∇u⟫`,

both data being supported in `U`. -/
private theorem energyFormH1_extendByZero_cutoff_eq (ha : AEStronglyMeasurable a volume)
    {Lam : ℝ} (hbd : ∀ x, ‖matrixBilinearForm (a x)‖ ≤ Lam) (hUΩ : U ≤ Ω)
    [IsFiniteMeasure (volume.restrict (U : Set (EuclideanSpace ℝ (Fin (n + 1)))))]
    {u : W1p volume Ω 2}
    {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    (hG : MemLp G 2 (volume.restrict (U : Set (EuclideanSpace ℝ (Fin (n + 1))))))
    (hu : ∀ φ : 𝓓(Ω, ℝ), energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume Ω 2 φ) =
      ∫ x in Ω, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ)
    {ζ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hζ : ContDiff ℝ ∞ ζ) (hζc : HasCompactSupport ζ)
    (hts : tsupport ζ ⊆ U) (c : ℝ)
    {w : W1p volume (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) 2}
    (hw : ∀ᵐ x, W1p.gradient w x = (U : Set (EuclideanSpace ℝ (Fin (n + 1)))).indicator
      (fun y => ζ y • W1p.gradient u y + (W1p.value u y - c) • ∇ ζ y) x)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))), ℝ)) :
    energyFormH1 a 0 0 w (W1p.ofTestFunctionₗ volume ⊤ 2 φ) =
      ∫ x in U, (⟪ζ x • G x + (W1p.value u x - c) • toEuclideanCLM (𝕜 := ℝ) (a x) (∇ ζ x),
          ∇ φ x⟫_ℝ +
        (⟪G x, ∇ ζ x⟫_ℝ - matrixBilinearForm (a x) (∇ ζ x) (W1p.gradient u x)) * φ x) := by
  set V := (U : Set (EuclideanSpace ℝ (Fin (n + 1))))
  have hUm : MeasurableSet V := U.isOpen.measurableSet
  obtain ⟨hT1, hT2, hT3, hT4⟩ := integrable_cutoff_terms ha hbd hUΩ hG hζ hζc c φ (u := u)
  have hψeq := setIntegral_cutoff_test_eq hUΩ hu hζ hζc hts φ
  -- The energy of `w` is an integral over `U`.
  have hlhs : energyFormH1 a 0 0 w (W1p.ofTestFunctionₗ volume ⊤ 2 φ) =
      ∫ x in V, matrixBilinearForm (a x) (∇ φ x)
        (ζ x • W1p.gradient u x + (W1p.value u x - c) • ∇ ζ x) := by
    rw [energyFormH1_zero_zero_eq_setIntegral, ← integral_indicator hUm]
    simp only [Opens.coe_top, Measure.restrict_univ]
    refine integral_congr_ae ?_
    have hφg := gradientTestFunctionLp_apply_ae (mu := volume)
      (Omega := (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1))))) 2 φ
    simp only [Opens.coe_top, Measure.restrict_univ] at hφg
    filter_upwards [hφg, hw] with x h1 h2
    rw [W1p.gradient_ofTestFunctionₗ, h1, h2]
    by_cases hxU : x ∈ V
    · rw [indicator_of_mem hxU, indicator_of_mem hxU]
    · rw [indicator_of_notMem hxU, indicator_of_notMem hxU, map_zero]
  rw [hlhs]
  calc ∫ x in V, matrixBilinearForm (a x) (∇ φ x)
        (ζ x • W1p.gradient u x + (W1p.value u x - c) • ∇ ζ x)
      = ∫ x in V, (matrixBilinearForm (a x) (ζ x • ∇ φ x + φ x • ∇ ζ x) (W1p.gradient u x)
          - φ x * matrixBilinearForm (a x) (∇ ζ x) (W1p.gradient u x)
          + (W1p.value u x - c) * matrixBilinearForm (a x) (∇ φ x) (∇ ζ x)) := by
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
        ring
    _ = ∫ x in V, (⟪G x, ζ x • ∇ φ x + φ x • ∇ ζ x⟫_ℝ
          - φ x * matrixBilinearForm (a x) (∇ ζ x) (W1p.gradient u x)
          + (W1p.value u x - c) * matrixBilinearForm (a x) (∇ φ x) (∇ ζ x)) := by
        have e1 := integral_add (hT1.sub hT2) hT3
        have e3 := integral_add (hT4.sub hT2) hT3
        simp only [Pi.sub_apply] at e1 e3
        rw [e1, integral_sub hT1 hT2, hψeq, e3, integral_sub hT4 hT2]
    _ = _ := by
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        simp only [inner_add_right, real_inner_smul_right, inner_toEuclideanCLM,
          ← matrixBilinearForm_apply, real_inner_comm (∇ φ x)]
        ring

/-- **The cutoff forcing has mean zero.** Testing the equation of a local weak solution with the
cutoff `ζ` itself gives `∫_U (⟪G, ∇ζ⟫ - ⟪∇ζ, a ∇u⟫) = 0`. -/
private theorem setIntegral_cutoff_forcing_eq_zero (ha : AEStronglyMeasurable a volume)
    {Lam : ℝ} (hbd : ∀ x, ‖matrixBilinearForm (a x)‖ ≤ Lam) (hUΩ : U ≤ Ω)
    [IsFiniteMeasure (volume.restrict (U : Set (EuclideanSpace ℝ (Fin (n + 1)))))]
    {u : W1p volume Ω 2}
    {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    (hG : MemLp G 2 (volume.restrict (U : Set (EuclideanSpace ℝ (Fin (n + 1))))))
    (hu : ∀ φ : 𝓓(Ω, ℝ), energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume Ω 2 φ) =
      ∫ x in Ω, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ)
    {ζ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hζ : ContDiff ℝ ∞ ζ) (hζc : HasCompactSupport ζ)
    (hts : tsupport ζ ⊆ U) :
    ∫ x in U, (⟪G x, ∇ ζ x⟫_ℝ - matrixBilinearForm (a x) (∇ ζ x) (W1p.gradient u x)) = 0 := by
  set V := (U : Set (EuclideanSpace ℝ (Fin (n + 1))))
  have hUΩ' : V ⊆ Ω := hUΩ
  have hle : volume.restrict V ≤ volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))) :=
    Measure.restrict_mono hUΩ' le_rfl
  obtain ⟨N, -, -, hgradN⟩ := (hζ.of_le (by simp)).exists_abs_le_and_norm_gradient_le hζc
  have hgζ := ContDiff.continuous_gradient hζ (by simp)
  have hgu : MemLp (W1p.gradient u : _ → EuclideanSpace ℝ (Fin (n + 1))) 2 (volume.restrict V) :=
    (Lp.memLp (W1p.gradient u)).mono_measure hle
  have hBm : AEStronglyMeasurable (fun x => matrixBilinearForm (a x)) (volume.restrict V) :=
    (continuous_matrixBilinearForm.comp_aestronglyMeasurable ha).restrict
  have hT1 : Integrable (fun x => ⟪G x, ∇ ζ x⟫_ℝ) (volume.restrict V) :=
    ((hG.integrable one_le_two).norm.mul_const N).mono'
      (hG.aestronglyMeasurable.inner hgζ.aestronglyMeasurable)
      (ae_of_all _ fun x => (norm_inner_le_norm _ _).trans (by gcongr; exact hgradN x))
  have hT2 : Integrable (fun x => matrixBilinearForm (a x) (∇ ζ x) (W1p.gradient u x))
      (volume.restrict V) :=
    ((hgu.integrable one_le_two).norm.const_mul (Lam * N)).mono'
      (aestronglyMeasurable_matrixBilinearForm_apply hBm hgζ.aestronglyMeasurable
        ((Lp.aestronglyMeasurable _).mono_measure hle))
      (ae_of_all _ fun x => ((matrixBilinearForm (a x)).le_opNorm₂ _ _).trans
        (by gcongr; exacts [(ContinuousLinearMap.opNorm_nonneg _).trans (hbd x), hbd x,
          hgradN x]))
  have h0 : ∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))) \ V, ∇ ζ x = 0 := fun x hx =>
    gradient_of_notMem_tsupport fun h => hx.2 (hts h)
  set ζΩ : 𝓓(Ω, ℝ) := ⟨ζ, hζ, hζc, hts.trans hUΩ'⟩
  have hcoe : (ζΩ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) = ζ := rfl
  have h := hu ζΩ
  rw [energyFormH1_zero_zero_eq_setIntegral, hcoe] at h
  have h' : ∫ x in Ω, matrixBilinearForm (a x) (∇ ζ x) (W1p.gradient u x) =
      ∫ x in Ω, ⟪G x, ∇ ζ x⟫_ℝ := by
    rw [← h]
    refine integral_congr_ae ?_
    filter_upwards [gradientTestFunctionLp_apply_ae (mu := volume) (Omega := Ω) 2 ζΩ] with x hx
    rw [W1p.gradient_ofTestFunctionₗ, hx, hcoe]
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero Ω.isOpen.measurableSet hUΩ'
      (fun x hx => by simp [h0 x hx]),
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero Ω.isOpen.measurableSet hUΩ'
      (fun x hx => by simp [h0 x hx])] at h'
  rw [integral_sub hT1 hT2, h', sub_self]

end Localization

section Step

variable {Ω : Opens (EuclideanSpace ℝ (Fin (n + 1)))}

/-- **Sobolev–Poincaré for a function of `W^{1,p}` on a ball.** If `u ∈ H¹(Ω)` has value and
gradient in `Lᵖ(B(x₀, R))` with `B(x₀, R) ⊆ Ω`, then on every concentric `B_t`, `t ≤ R`, and for
`q ≤ p` with `δ = 1/q - 1/p < 1/(n + 1)`,
`‖u - u_{B_t}‖_{Lᵖ(B_t)} ≤ K t |B_t|^(-δ) ‖∇u‖_{L^q(B_t)}`. -/
private theorem eLpNorm_value_sub_setAverage_le_of_memLp (u : W1p volume Ω 2)
    {x₀ : EuclideanSpace ℝ (Fin (n + 1))} {R : ℝ} (hball : ball x₀ R ⊆ (Ω : Set _))
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] (hp : p ≠ ⊤) (hqp : q ≤ p)
    (hv : MemLp (W1p.value u) p (volume.restrict (ball x₀ R)))
    (hg : MemLp (W1p.gradient u) p (volume.restrict (ball x₀ R))) {δ : ℝ}
    (hδ : q.toReal⁻¹ - p.toReal⁻¹ = δ)
    (hδn : δ < (finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) : ℝ)⁻¹) {t : ℝ} (ht : 0 < t)
    (htR : t ≤ R) :
    eLpNorm (fun x => W1p.value u x - ⨍ y in ball x₀ t, W1p.value u y) p
        (volume.restrict (ball x₀ t)) ≤
      ENNReal.ofReal (2 ^ finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) /
          finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) *
          ((1 - δ) / ((finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) : ℝ)⁻¹ - δ)) ^ (1 - δ) * t) *
        volume (ball x₀ t) ^ (-δ) * eLpNorm (W1p.gradient u) q (volume.restrict (ball x₀ t)) := by
  set BR : Opens (EuclideanSpace ℝ (Fin (n + 1))) := ⟨ball x₀ R, isOpen_ball⟩
  have hBR : BR ≤ Ω := hball
  set uB := W1p.restrictL hBR u
  have hval := W1p.value_restrictL_ae hBR u
  have hgrad := W1p.gradient_restrictL_ae hBR u
  have hv' : MemLp (W1p.value uB) p (volume.restrict (BR : Set _)) := hv.ae_eq hval.symm
  have hg' : MemLp (W1p.gradient uB) p (volume.restrict (BR : Set _)) := hg.ae_eq hgrad.symm
  set uR : W1p volume BR p := W1p.mk (hv'.toLp _) (hg'.toLp _)
    (((W1p.hasWeakFDerivOn uB).congr_ae hv'.coeFn_toLp.symm).congr_ae_deriv
      (hg'.coeFn_toLp.mono fun x hx => by simp only [hx]))
  have hvR : W1p.value uR =ᵐ[volume.restrict (ball x₀ R)] W1p.value u := by
    rw [W1p.value_mk]
    exact hv'.coeFn_toLp.trans hval
  have hgR : W1p.gradient uR =ᵐ[volume.restrict (ball x₀ R)] W1p.gradient u := by
    rw [W1p.gradient_mk]
    exact hg'.coeFn_toLp.trans hgrad
  have hpN : ((p.toNNReal : ℝ≥0) : ℝ≥0∞) = p := ENNReal.coe_toNNReal hp
  have hsub : ball x₀ t ⊆ ball x₀ R := ball_subset_ball htR
  have hle : volume.restrict (ball x₀ t) ≤ volume.restrict (ball x₀ R) :=
    Measure.restrict_mono hsub le_rfl
  have hδ' : q.toReal⁻¹ - ((p.toNNReal : ℝ≥0) : ℝ)⁻¹ = δ := by
    rw [ENNReal.coe_toNNReal_eq_toReal]; exact hδ
  have h := W1p.eLpNorm_value_sub_setAverage_le_of_ball_subset (μ := volume) (s := p.toNNReal)
    (ne_top_of_le_ne_top hp hqp) hqp (by rw [hpN]; exact hqp) hδ' hδn ht hsub uR
  have hvt : W1p.value uR =ᵐ[volume.restrict (ball x₀ t)] W1p.value u := ae_mono hle hvR
  have hgt : W1p.gradient uR =ᵐ[volume.restrict (ball x₀ t)] W1p.gradient u := ae_mono hle hgR
  have havg : ⨍ y in ball x₀ t, W1p.value uR y = ⨍ y in ball x₀ t, W1p.value u y :=
    average_congr hvt
  have h1 : (fun x => W1p.value uR x - ⨍ y in ball x₀ t, W1p.value uR y) =ᵐ[volume.restrict
      (ball x₀ t)] fun x => W1p.value u x - ⨍ y in ball x₀ t, W1p.value u y :=
    hvt.mono fun x hx => by simp only [hx, havg]
  rwa [hpN, eLpNorm_congr_ae h1, eLpNorm_congr_ae hgt] at h

/-- The field `x ↦ a(x) ξ(x)` is a.e. strongly measurable for a.e. strongly measurable `a`, `ξ`. -/
private theorem aestronglyMeasurable_toEuclideanCLM_apply
    {μ : Measure (EuclideanSpace ℝ (Fin (n + 1)))}
    {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (ha : AEStronglyMeasurable a μ)
    {ξ : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    (hξ : AEStronglyMeasurable ξ μ) :
    AEStronglyMeasurable (fun x => toEuclideanCLM (𝕜 := ℝ) (a x) (ξ x)) μ := by
  have hT : Continuous fun A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ => toEuclideanCLM (𝕜 := ℝ) A :=
    LinearMap.continuous_of_finiteDimensional
      (toEuclideanCLM (𝕜 := ℝ) (n := Fin (n + 1))).toAlgEquiv.toLinearEquiv.toLinearMap
  have hc : Continuous fun q : (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n + 1))) × EuclideanSpace ℝ (Fin (n + 1)) => q.1 q.2 := by fun_prop
  exact hc.comp_aestronglyMeasurable ((hT.comp_aestronglyMeasurable ha).prodMk hξ)

/-- The `Lᵖ` norm of the divergence datum `ζ G + v a ∇ζ` of a cutoff, for `|ζ| ≤ 1` and
`‖∇ζ‖ ≤ L`. -/
private theorem eLpNorm_indicator_cutoffField_le
    {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (ha : AEStronglyMeasurable a volume) {Lam : ℝ}
    (hbd : ∀ x, ‖matrixBilinearForm (a x)‖ ≤ Lam) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {V : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hV : MeasurableSet V)
    {ζ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hζc : Continuous ζ) (hζ1 : ∀ x, |ζ x| ≤ 1)
    (hgζ : Continuous (∇ ζ)) {L : ℝ} (hgradL : ∀ x, ‖∇ ζ x‖ ≤ L)
    {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    (hG : AEStronglyMeasurable G (volume.restrict V))
    {v : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hv : AEStronglyMeasurable v (volume.restrict V)) :
    eLpNorm (V.indicator fun y => ζ y • G y + v y • toEuclideanCLM (𝕜 := ℝ) (a y) (∇ ζ y)) p
        volume ≤
      eLpNorm G p (volume.restrict V) +
        ENNReal.ofReal (Lam * L) * eLpNorm v p (volume.restrict V) := by
  have hLam : 0 ≤ Lam := (ContinuousLinearMap.opNorm_nonneg _).trans (hbd 0)
  have hm1 : AEStronglyMeasurable (fun y => ζ y • G y) (volume.restrict V) :=
    hζc.aestronglyMeasurable.smul hG
  have hm2 : AEStronglyMeasurable (fun y => v y • toEuclideanCLM (𝕜 := ℝ) (a y) (∇ ζ y))
      (volume.restrict V) :=
    hv.smul (aestronglyMeasurable_toEuclideanCLM_apply ha.restrict hgζ.aestronglyMeasurable)
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hV.nullMeasurableSet]
  refine (eLpNorm_add_le (f := fun y => ζ y • G y) Fact.out).trans (add_le_add ?_ ?_)
  · simpa using eLpNorm_le_mul_eLpNorm_of_ae_le_mul (c := 1) hm1 (ae_of_all _ fun y => by
      rw [norm_smul, one_mul, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _) (hζ1 y)) p
  · refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul hm2 (ae_of_all _ fun y => ?_) p
    rw [norm_smul, mul_comm]
    gcongr
    exact (norm_toEuclideanCLM_apply_le _ _).trans (by gcongr; exacts [hbd y, hgradL y])

/-- The `L^q` norm of the scalar forcing `⟪G, ∇ζ⟫ - ⟪∇ζ, a ∇u⟫` of a cutoff, for `‖∇ζ‖ ≤ L`. -/
private theorem eLpNorm_indicator_cutoffForcing_le
    {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (ha : AEStronglyMeasurable a volume) {Lam : ℝ}
    (hbd : ∀ x, ‖matrixBilinearForm (a x)‖ ≤ Lam) {q : ℝ≥0∞} [Fact (1 ≤ q)]
    {V : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hV : MeasurableSet V)
    {ζ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hgζ : Continuous (∇ ζ)) {L : ℝ}
    (hgradL : ∀ x, ‖∇ ζ x‖ ≤ L)
    {G g : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    (hG : AEStronglyMeasurable G (volume.restrict V))
    (hg : AEStronglyMeasurable g (volume.restrict V)) :
    eLpNorm (V.indicator fun y => ⟪G y, ∇ ζ y⟫_ℝ - matrixBilinearForm (a y) (∇ ζ y) (g y)) q
        volume ≤
      ENNReal.ofReal L * eLpNorm G q (volume.restrict V) +
        ENNReal.ofReal (Lam * L) * eLpNorm g q (volume.restrict V) := by
  have hLam : 0 ≤ Lam := (ContinuousLinearMap.opNorm_nonneg _).trans (hbd 0)
  have hBm : AEStronglyMeasurable (fun x => matrixBilinearForm (a x)) (volume.restrict V) :=
    (continuous_matrixBilinearForm.comp_aestronglyMeasurable ha).restrict
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hV.nullMeasurableSet]
  refine (eLpNorm_sub_le (f := fun y => ⟪G y, ∇ ζ y⟫_ℝ) Fact.out).trans (add_le_add ?_ ?_)
  · refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul (hG.inner hgζ.aestronglyMeasurable)
      (ae_of_all _ fun y => ?_) q
    exact (norm_inner_le_norm _ _).trans (by rw [mul_comm]; gcongr; exact hgradL y)
  · refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul
      (aestronglyMeasurable_matrixBilinearForm_apply hBm hgζ.aestronglyMeasurable hg)
      (ae_of_all _ fun y => ?_) q
    exact ((matrixBilinearForm (a y)).le_opNorm₂ _ _).trans (by gcongr; exacts [hbd y, hgradL y])

/-- A function in `Lᵖ` paired with the gradient of a test function is integrable. -/
private theorem integrable_inner_gradient_testFunction {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {F : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))} (hF : MemLp F p volume)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))), ℝ)) :
    Integrable (fun x => ⟪F x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) := by
  have hφ : MemLp (fun x => ‖∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x‖) p.conjExponent
      volume :=
    (φ.hasCompactSupport.memLp_gradient (φ.contDiff.of_le (by simp))).norm
  exact (hF.norm.integrable_mul hφ).mono'
    (hF.aestronglyMeasurable.inner (continuous_gradient_testFunction φ).aestronglyMeasurable)
    (ae_of_all _ fun x => norm_inner_le_norm _ _)

/-- A function in `Lᵖ` times a test function is integrable. -/
private theorem integrable_mul_testFunction {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {h : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hh : MemLp h p volume)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))), ℝ)) :
    Integrable (fun x => h x * φ x) :=
  hh.integrable_mul (q := p.conjExponent)
    (φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport)

/-- Moving the scalar part of a weak equation on `V` into the divergence datum: if `-div H` is the
scalar `1_V k`, then `∫_V (⟪F, ∇φ⟫ + k φ) = ∫ ⟪1_V F + H, ∇φ⟫`. -/
private theorem setIntegral_inner_add_mul_eq {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {V : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hV : MeasurableSet V)
    {F H : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    {k : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hF : MemLp (V.indicator F) p volume)
    (hk : MemLp (V.indicator k) q volume) (hH : MemLp H p volume)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))), ℝ))
    (hHφ : ∫ x, V.indicator k x * φ x =
      ∫ x, ⟪H x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) :
    ∫ x in V, (⟪F x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ + k x * φ x) =
      ∫ x, ⟪(V.indicator F + H) x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ := by
  have h1 := integrable_inner_gradient_testFunction hF φ
  have h2 := integrable_mul_testFunction hk φ
  have hpair : ∀ x, ⟪V.indicator F x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ =
      V.indicator (fun y => ⟪F y, ∇ φ y⟫_ℝ) x := fun x => by
    by_cases hx : x ∈ V <;> simp [hx]
  have hmul : ∀ x, V.indicator k x * φ x = V.indicator (fun y => k y * φ y) x := fun x => by
    by_cases hx : x ∈ V <;> simp [hx]
  rw [integral_add ((integrable_indicator_iff hV).1 (h1.congr (ae_of_all _ hpair)))
      ((integrable_indicator_iff hV).1 (h2.congr (ae_of_all _ hmul))),
    ← integral_indicator hV, ← integral_indicator hV,
    integral_congr_ae (ae_of_all _ fun x => (hpair x).symm),
    integral_congr_ae (ae_of_all _ fun x => (hmul x).symm), hHφ,
    ← integral_add h1 (integrable_inner_gradient_testFunction hH φ)]
  simp only [Pi.add_apply, inner_add_left]

/-- **A cutoff of a local solution solves a problem on the whole space.** Let `u` solve
`-div(a ∇u) = -div G` weakly in `Ω ⊇ B = B(x₀, t)`, with `u`, `∇u`, `G` in `Lᵖ(B)`, and let `ζ` be a
cutoff supported in `B` with `|ζ| ≤ 1` and `‖∇ζ‖ ≤ L`. Given the divergence representation `hD` of
mean-zero functions on `B`, the extension by zero of `ζ (u - c)` solves `-div(a ∇w) = -div F` on
the whole space, for an explicit field `F ∈ Lᵖ`: the divergence datum of the cutoff plus a field
`H` with `-div H` the scalar forcing of the cutoff. -/
private theorem exists_wholeSpace_cutoff
    {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (ha : AEStronglyMeasurable a volume) {Lam : ℝ}
    (hbd : ∀ x, ‖matrixBilinearForm (a x)‖ ≤ Lam) {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hp2 : 2 ≤ p) (hqp : q ≤ p) {δ : ℝ} {CD : ℝ≥0}
    (hD : ∀ {x₀ : EuclideanSpace ℝ (Fin (n + 1))} {t : ℝ}, 0 < t →
      ∀ {h : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}, MemLp h q volume →
      (∀ᵐ x, x ∉ ball x₀ t → h x = 0) → ∫ x, h x = 0 →
      ∃ H : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)), MemLp H p volume ∧
        eLpNorm H p volume ≤ CD * ENNReal.ofReal t * volume (ball x₀ t) ^ (-δ) *
          eLpNorm h q volume ∧
        ∀ φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))), ℝ),
          ∫ x, h x * φ x = ∫ x, ⟪H x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ)
    {x₀ : EuclideanSpace ℝ (Fin (n + 1))} {t : ℝ} (ht : 0 < t) (hball : ball x₀ t ⊆ (Ω : Set _))
    (u : W1p volume Ω 2) {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    (hu : ∀ φ : 𝓓(Ω, ℝ), energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume Ω 2 φ) =
      ∫ x in Ω, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ)
    (hv : MemLp (W1p.value u) p (volume.restrict (ball x₀ t)))
    (hg : MemLp (W1p.gradient u) p (volume.restrict (ball x₀ t)))
    (hG : MemLp G p (volume.restrict (ball x₀ t)))
    {ζ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hζ : ContDiff ℝ ∞ ζ) (hζc : HasCompactSupport ζ)
    (hts : tsupport ζ ⊆ ball x₀ t) (hζ1 : ∀ x, |ζ x| ≤ 1) {L : ℝ} (hgradL : ∀ x, ‖∇ ζ x‖ ≤ L)
    (c : ℝ) :
    ∃ w : W1p volume (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) 2,
    ∃ F : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)),
      (∀ᵐ x, W1p.gradient w x = (ball x₀ t).indicator
        (fun y => ζ y • W1p.gradient u y + (W1p.value u y - c) • ∇ ζ y) x) ∧
      MemLp F p volume ∧
      (∀ φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))), ℝ),
        energyFormH1 a 0 0 w (W1p.ofTestFunctionₗ volume ⊤ 2 φ) =
          ∫ x, ⟪F x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) ∧
      eLpNorm F p volume ≤ eLpNorm G p (volume.restrict (ball x₀ t)) +
          ENNReal.ofReal (Lam * L) *
            eLpNorm (fun x => W1p.value u x - c) p (volume.restrict (ball x₀ t)) +
        CD * ENNReal.ofReal t * volume (ball x₀ t) ^ (-δ) *
          (ENNReal.ofReal L * eLpNorm G q (volume.restrict (ball x₀ t)) +
            ENNReal.ofReal (Lam * L) *
              eLpNorm (W1p.gradient u) q (volume.restrict (ball x₀ t))) := by
  set U : Opens (EuclideanSpace ℝ (Fin (n + 1))) := ⟨ball x₀ t, isOpen_ball⟩
  have hUΩ : U ≤ Ω := hball
  have hU : MeasurableSet (U : Set (EuclideanSpace ℝ (Fin (n + 1)))) := measurableSet_ball
  have : IsFiniteMeasure (volume.restrict (U : Set (EuclideanSpace ℝ (Fin (n + 1))))) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hgζ := ContDiff.continuous_gradient hζ (by simp)
  obtain ⟨w, hw⟩ := exists_extendByZero_cutoff hUΩ u hζ hζc hts c
  have heq := energyFormH1_extendByZero_cutoff_eq ha hbd hUΩ (hG.mono_exponent hp2) hu hζ hζc
    hts c hw
  have hmean := setIntegral_cutoff_forcing_eq_zero ha hbd hUΩ (hG.mono_exponent hp2) hu hζ hζc hts
  set G₁ := (ball x₀ t).indicator fun y =>
    ζ y • G y + (W1p.value u y - c) • toEuclideanCLM (𝕜 := ℝ) (a y) (∇ ζ y)
  set h := (ball x₀ t).indicator fun y =>
    ⟪G y, ∇ ζ y⟫_ℝ - matrixBilinearForm (a y) (∇ ζ y) (W1p.gradient u y)
  have hvc : MemLp (fun x => W1p.value u x - c) p (volume.restrict (ball x₀ t)) :=
    hv.sub (memLp_const c)
  have hG₁le := eLpNorm_indicator_cutoffField_le (p := p) ha hbd hU hζ.continuous hζ1 hgζ hgradL
    hG.aestronglyMeasurable hvc.aestronglyMeasurable
  have hhle := eLpNorm_indicator_cutoffForcing_le (q := q) ha hbd hU hgζ hgradL
    hG.aestronglyMeasurable hg.aestronglyMeasurable
  have hG₁ : MemLp G₁ p volume :=
    hG₁le.trans_lt (ENNReal.add_lt_top.2 ⟨hG.eLpNorm_lt_top,
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top hvc.eLpNorm_lt_top⟩)
  have hh : MemLp h q volume :=
    hhle.trans_lt (ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (hG.mono_exponent hqp).eLpNorm_lt_top,
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hg.mono_exponent hqp).eLpNorm_lt_top⟩)
  obtain ⟨H, hH, hHle, hHφ⟩ := hD ht hh (ae_of_all _ fun x hx => indicator_of_notMem hx _)
    (by rw [integral_indicator measurableSet_ball]; exact hmean)
  refine ⟨w, G₁ + H, hw, hG₁.add hH, fun φ => ?_, ?_⟩
  · exact (heq φ).trans (setIntegral_inner_add_mul_eq measurableSet_ball hG₁ hh hH φ (hHφ φ))
  · calc eLpNorm (G₁ + H) p volume ≤ eLpNorm G₁ p volume + eLpNorm H p volume :=
          eLpNorm_add_le Fact.out
      _ ≤ _ := add_le_add hG₁le (hHle.trans (by gcongr; exact hhle))

/-- The arithmetic of the step between concentric balls: with `L = c₀ / ((s + t) / 2 - s)` the
gradient bound of the cutoff, the bound produced by the whole-space estimate is at most
`C ((1 + t / (t - s)) A + t / (t - s) ε X)`. -/
private theorem step_bound_le {CW CD : ℝ≥0} {A At X Y Gq ε ε' : ℝ≥0∞} {c₀ Lam K s t : ℝ}
    (hc₀ : 0 ≤ c₀) (hLam : 0 ≤ Lam) (hK : 0 ≤ K) (hs : 0 < s) (hst : s < t) (hAt : At ≤ A)
    (hεε' : ε * ε' = 1) (hY : Y ≤ ENNReal.ofReal (K * t) * ε * X) (hGq : Gq ≤ At * ε') :
    (CW : ℝ≥0∞) * (At + ENNReal.ofReal (Lam * (c₀ / ((s + t) / 2 - s))) * Y +
        CD * ENNReal.ofReal t * ε * (ENNReal.ofReal (c₀ / ((s + t) / 2 - s)) * Gq +
          ENNReal.ofReal (Lam * (c₀ / ((s + t) / 2 - s))) * X)) ≤
      ((CW * (1 + (2 * c₀).toNNReal * CD + ((2 * c₀ * Lam * K).toNNReal +
          CD * (2 * c₀ * Lam).toNNReal)) : ℝ≥0) : ℝ≥0∞) *
        ((1 + ENNReal.ofReal (t / (t - s))) * A + ENNReal.ofReal (t / (t - s)) * ε * X) := by
  have hL : c₀ / ((s + t) / 2 - s) = 2 * c₀ / (t - s) := by
    rw [show (s + t) / 2 - s = (t - s) / 2 by ring]
    field_simp
  rw [hL]
  set τ := ENNReal.ofReal (t / (t - s))
  have ht : 0 ≤ t := hs.le.trans hst.le
  have e1 : ENNReal.ofReal (Lam * (2 * c₀ / (t - s))) * ENNReal.ofReal (K * t) =
      ENNReal.ofReal (2 * c₀ * Lam * K) * τ := by
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1; field_simp
  have e2 : ENNReal.ofReal t * ENNReal.ofReal (2 * c₀ / (t - s)) = ENNReal.ofReal (2 * c₀) * τ := by
    rw [← ENNReal.ofReal_mul ht, ← ENNReal.ofReal_mul (by positivity)]
    congr 1; field_simp
  have e3 : ENNReal.ofReal t * ENNReal.ofReal (Lam * (2 * c₀ / (t - s))) =
      ENNReal.ofReal (2 * c₀ * Lam) * τ := by
    rw [← ENNReal.ofReal_mul ht, ← ENNReal.ofReal_mul (by positivity)]
    congr 1; field_simp
  set S : ℝ≥0∞ := 1 + ENNReal.ofReal (2 * c₀) * CD + (ENNReal.ofReal (2 * c₀ * Lam * K) +
    CD * ENNReal.ofReal (2 * c₀ * Lam))
  have hS : ((CW * (1 + (2 * c₀).toNNReal * CD + ((2 * c₀ * Lam * K).toNNReal +
      CD * (2 * c₀ * Lam).toNNReal)) : ℝ≥0) : ℝ≥0∞) = CW * S := by
    simp only [S, ENNReal.coe_mul, ENNReal.coe_add, ENNReal.coe_one]
    rfl
  rw [hS]
  calc (CW : ℝ≥0∞) * (At + ENNReal.ofReal (Lam * (2 * c₀ / (t - s))) * Y +
        CD * ENNReal.ofReal t * ε * (ENNReal.ofReal (2 * c₀ / (t - s)) * Gq +
          ENNReal.ofReal (Lam * (2 * c₀ / (t - s))) * X))
      ≤ CW * (At + ENNReal.ofReal (Lam * (2 * c₀ / (t - s))) * (ENNReal.ofReal (K * t) * ε * X) +
        CD * ENNReal.ofReal t * ε * (ENNReal.ofReal (2 * c₀ / (t - s)) * (At * ε') +
          ENNReal.ofReal (Lam * (2 * c₀ / (t - s))) * X)) := by gcongr
    _ = CW * (At + (ENNReal.ofReal (Lam * (2 * c₀ / (t - s))) * ENNReal.ofReal (K * t)) * ε * X +
        CD * (ENNReal.ofReal t * ENNReal.ofReal (2 * c₀ / (t - s))) * (ε * ε') * At +
        CD * (ENNReal.ofReal t * ENNReal.ofReal (Lam * (2 * c₀ / (t - s)))) * ε * X) := by ring
    _ = CW * (At + ENNReal.ofReal (2 * c₀) * CD * τ * (ε * ε') * At +
        (ENNReal.ofReal (2 * c₀ * Lam * K) + CD * ENNReal.ofReal (2 * c₀ * Lam)) * τ * ε * X) := by
        rw [e1, e2, e3]
        ring
    _ ≤ CW * (S * A + S * τ * A + S * τ * ε * X) := by
        rw [hεε', mul_one]
        have h1 : 1 ≤ S := le_self_add.trans le_self_add
        have h2 : ENNReal.ofReal (2 * c₀) * CD ≤ S := le_add_self.trans le_self_add
        have h3 : ENNReal.ofReal (2 * c₀ * Lam * K) + CD * ENNReal.ofReal (2 * c₀ * Lam) ≤ S :=
          le_add_self
        gcongr CW * (?_ + ?_ + ?_)
        · exact hAt.trans (le_mul_of_one_le_left' h1)
        · calc ENNReal.ofReal (2 * c₀) * CD * τ * At ≤ S * τ * At := by gcongr
            _ ≤ S * τ * A := by gcongr
        · gcongr
    _ = CW * S * ((1 + τ) * A + τ * ε * X) := by ring

/-- A function equal to `1` on `closedBall x₀ s` has vanishing gradient on `ball x₀ s`. -/
private theorem gradient_eq_zero_of_eqOn_one {ζ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    {x₀ : EuclideanSpace ℝ (Fin (n + 1))} {s : ℝ} (hζ1 : EqOn ζ 1 (closedBall x₀ s))
    {x : EuclideanSpace ℝ (Fin (n + 1))} (hx : x ∈ ball x₀ s) : ∇ ζ x = 0 := by
  have h : ζ =ᶠ[𝓝 x] fun _ => 1 :=
    Filter.eventually_of_mem (isOpen_ball.mem_nhds hx) fun y hy => hζ1 (ball_subset_closedBall hy)
  rw [gradient_eq_zero_iff, h.fderiv_eq, fderiv_const_apply]

/-- Cutoffs between concentric balls: `ζ = 1` on `closedBall x₀ s`, supported in `B(x₀, t)`, with
values in `[0, 1]` and `‖∇ζ‖ ≤ c₀ / ((s + t)/2 - s)`. -/
private theorem exists_cutoff_ball :
    ∃ c₀ : ℝ, 0 ≤ c₀ ∧ ∀ (x₀ : EuclideanSpace ℝ (Fin (n + 1))) {s t : ℝ}, 0 < s → s < t →
      ∃ ζ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ, ContDiff ℝ ∞ ζ ∧ HasCompactSupport ζ ∧
        tsupport ζ ⊆ ball x₀ t ∧ (∀ x, |ζ x| ≤ 1) ∧ EqOn ζ 1 (closedBall x₀ s) ∧
        ∀ x, ‖∇ ζ x‖ ≤ c₀ / ((s + t) / 2 - s) := by
  obtain ⟨c₀, hc₀, hcut⟩ := exists_forall_contDiff_cutoff_closedBall
    (E := EuclideanSpace ℝ (Fin (n + 1)))
  refine ⟨c₀, hc₀, fun x₀ {s t} hs hst => ?_⟩
  obtain ⟨ζ, hζ, hζr, hζ1, hts, hgrad, -⟩ := hcut x₀ hs.le (show s < (s + t) / 2 by linarith)
  refine ⟨ζ, hζ, (isCompact_closedBall x₀ _).of_isClosed_subset (isClosed_tsupport _) hts,
    hts.trans (closedBall_subset_ball (by linarith)), fun x => ?_, hζ1, hgrad⟩
  obtain ⟨h0, h1⟩ := hζr (mem_range_self x)
  rwa [abs_of_nonneg h0]

/-- The gradient of the extended cutoff `ζ (u - c)` lies in `Lᵖ ∩ L¹` when `u`, `∇u ∈ Lᵖ(B_t)`. -/
private theorem memLp_integrable_of_ae_eq_indicator_cutoff {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {x₀ : EuclideanSpace ℝ (Fin (n + 1))} {t : ℝ} (u : W1p volume Ω 2)
    (hv : MemLp (W1p.value u) p (volume.restrict (ball x₀ t)))
    (hg : MemLp (W1p.gradient u) p (volume.restrict (ball x₀ t)))
    {ζ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hζ : ContDiff ℝ ∞ ζ) (hζ1 : ∀ x, |ζ x| ≤ 1) {L : ℝ}
    (hgrad : ∀ x, ‖∇ ζ x‖ ≤ L) (c : ℝ)
    {g : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    (hw : ∀ᵐ x, g x = (ball x₀ t).indicator
      (fun y => ζ y • W1p.gradient u y + (W1p.value u y - c) • ∇ ζ y) x) :
    MemLp g p volume ∧ Integrable g := by
  have : IsFiniteMeasure (volume.restrict (ball x₀ t)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hfp : MemLp (fun y => ζ y • W1p.gradient u y + (W1p.value u y - c) • ∇ ζ y) p
      (volume.restrict (ball x₀ t)) :=
    ((memLp_top_of_bound hζ.continuous.aestronglyMeasurable 1 (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs]; exact hζ1 x)).smul hg).add
      ((hv.sub (memLp_const _)).smul (memLp_top_of_bound
        (ContDiff.continuous_gradient hζ (by simp)).aestronglyMeasurable _ (ae_of_all _ hgrad)))
  exact ⟨((memLp_indicator_iff_restrict measurableSet_ball.nullMeasurableSet).2 hfp).ae_eq
      (Filter.EventuallyEq.symm hw),
    ((integrable_indicator_iff measurableSet_ball).2
      (hfp.integrable Fact.out)).congr (Filter.EventuallyEq.symm hw)⟩

/-- Where the cutoff is `1`, the extended cutoff of `u` has the gradient of `u`, so
`‖∇u‖_{Lᵖ(B_s)} ≤ ‖∇w‖_{Lᵖ}`. -/
private theorem eLpNorm_le_of_ae_eq_indicator_cutoff {p : ℝ≥0∞}
    {x₀ : EuclideanSpace ℝ (Fin (n + 1))} {s t : ℝ} (hst : s ≤ t) (u : W1p volume Ω 2)
    {ζ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hζ1 : EqOn ζ 1 (closedBall x₀ s)) (c : ℝ)
    {g : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    (hw : ∀ᵐ x, g x = (ball x₀ t).indicator
      (fun y => ζ y • W1p.gradient u y + (W1p.value u y - c) • ∇ ζ y) x) :
    eLpNorm (W1p.gradient u) p (volume.restrict (ball x₀ s)) ≤ eLpNorm g p volume := by
  refine le_trans (le_of_eq (eLpNorm_congr_ae ?_)) (eLpNorm_mono_measure _ Measure.restrict_le_self)
  filter_upwards [ae_restrict_of_ae hw, ae_restrict_mem measurableSet_ball] with x hx hxs
  rw [hx, indicator_of_mem (ball_subset_ball hst hxs), hζ1 (ball_subset_closedBall hxs),
    gradient_eq_zero_of_eqOn_one hζ1 hxs]
  simp

/-- **The step between concentric balls.** Let `2 < p < ∞` and `1 < q ≤ p` with
`δ = 1/q - 1/p < 1/(n + 1)`. There are `C` and `δ₀ > 0` such that, for coefficients of mean
oscillation at most `δ₀` below the radius `r₀`, every local weak solution `u` of
`-div(a ∇u) = -div G` with `u`, `∇u`, `G ∈ Lᵖ(B_R)`, `4 R ≤ r₀`, satisfies for `0 < s < t ≤ R`

`‖∇u‖_{Lᵖ(B_s)} ≤ C ((1 + t/(t - s)) ‖G‖_{Lᵖ(B_R)} + t/(t - s) |B_t|^(-δ) ‖∇u‖_{L^q(B_t)})`. -/
private theorem exists_eLpNorm_gradient_ball_le_step {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hp : 2 < p) (hp_top : p ≠ ⊤) (hq : 1 < q) (hqp : q ≤ p) {δ : ℝ}
    (hδ : q.toReal⁻¹ - p.toReal⁻¹ = δ)
    (hδn : δ < (finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) : ℝ)⁻¹) (lam Lam : ℝ) :
    ∃ C : ℝ≥0, ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {r₀ : ℝ},
        AEStronglyMeasurable a volume → (∀ x, ‖matrixBilinearForm (a x)‖ ≤ Lam) →
        (∀ (c : EuclideanSpace ℝ (Fin (n + 1))) (r : ℝ), 0 < r → r ≤ r₀ →
          ∃ A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ,
            UniformlyEllipticOn (ball c r) (fun _ => A) lam Lam ∧
              ⨍ x in ball c r, ‖matrixBilinearForm (a x) - matrixBilinearForm A‖ ≤ δ₀) →
        ∀ {Ω : Opens (EuclideanSpace ℝ (Fin (n + 1)))} {x₀ : EuclideanSpace ℝ (Fin (n + 1))}
          {R : ℝ}, 4 * R ≤ r₀ → ball x₀ R ⊆ (Ω : Set _) →
        ∀ (u : W1p volume Ω 2)
          (G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))),
          (∀ φ : 𝓓(Ω, ℝ), energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume Ω 2 φ) =
            ∫ x in Ω, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) →
          MemLp (W1p.value u) p (volume.restrict (ball x₀ R)) →
          MemLp (W1p.gradient u) p (volume.restrict (ball x₀ R)) →
          MemLp G p (volume.restrict (ball x₀ R)) →
          ∀ {s t : ℝ}, 0 < s → s < t → t ≤ R →
            eLpNorm (W1p.gradient u) p (volume.restrict (ball x₀ s)) ≤
              C * ((1 + ENNReal.ofReal (t / (t - s))) * eLpNorm G p (volume.restrict (ball x₀ R)) +
                ENNReal.ofReal (t / (t - s)) * volume (ball x₀ t) ^ (-δ) *
                  eLpNorm (W1p.gradient u) q (volume.restrict (ball x₀ t))) := by
  obtain ⟨CW, δ₀, hδ₀, hW⟩ :=
    exists_eLpNorm_gradient_le_of_setAverage_le_of_gradient_eq_zero (n := n) hp hp_top lam Lam
  obtain ⟨CD, hD⟩ := exists_memLp_forall_integral_mul_eq_integral_inner_gradient_of_integral_eq_zero
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin (n + 1))))) hq hqp hp_top hδ hδn
  obtain ⟨c₀, hc₀, hcut⟩ := exists_cutoff_ball (n := n)
  set d := finrank ℝ (EuclideanSpace ℝ (Fin (n + 1)))
  set K : ℝ := 2 ^ d / d * ((1 - δ) / ((d : ℝ)⁻¹ - δ)) ^ (1 - δ)
  have hK : 0 ≤ K := by
    have hn : (1 : ℝ) ≤ d := by exact_mod_cast finrank_pos
    have hδ1 : δ < 1 := hδn.trans_le (inv_le_one_of_one_le₀ hn)
    exact mul_nonneg (by positivity)
      (Real.rpow_nonneg (div_nonneg (by linarith) (sub_nonneg.2 hδn.le)) _)
  refine ⟨CW * (1 + (2 * c₀).toNNReal * CD + ((2 * c₀ * Lam * K).toNNReal +
    CD * (2 * c₀ * Lam).toNNReal)), δ₀, hδ₀,
    fun {a r₀} ha hbd hosc {Ω x₀ R} hRr₀ hball u G hu hv hg hG {s t} hs hst htR => ?_⟩
  have hLam : 0 ≤ Lam := (ContinuousLinearMap.opNorm_nonneg _).trans (hbd 0)
  have ht : 0 < t := hs.trans hst
  -- A cutoff between `B_s` and `B_t`.
  obtain ⟨ζ, hζ, hζc, htsb, hζabs, hζ1, hgrad⟩ := hcut x₀ hs hst
  have hballt : ball x₀ t ⊆ (Ω : Set _) := (ball_subset_ball htR).trans hball
  have hle : volume.restrict (ball x₀ t) ≤ volume.restrict (ball x₀ R) :=
    Measure.restrict_mono (ball_subset_ball htR) le_rfl
  have : IsFiniteMeasure (volume.restrict (ball x₀ t)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hv' := hv.mono_measure hle
  have hg' := hg.mono_measure hle
  have hG' := hG.mono_measure hle
  obtain ⟨w, F, hw, hF, hweq, hFle⟩ := exists_wholeSpace_cutoff ha hbd hp.le hqp hD ht hballt u hu
    hv' hg' hG' hζ hζc htsb hζabs hgrad (⨍ y in ball x₀ t, W1p.value u y)
  -- The whole-space estimate applies to `w`, and `∇w = ∇u` on `B_s`.
  obtain ⟨hwp, hwint⟩ := memLp_integrable_of_ae_eq_indicator_cutoff u hv' hg' hζ hζabs hgrad _ hw
  have hw0 : ∀ᵐ x, x ∉ ball x₀ (r₀ / 4) → W1p.gradient w x = 0 := by
    filter_upwards [hw] with x hx hxr
    rw [hx, indicator_of_notMem fun h => hxr (ball_subset_ball (by linarith) h)]
  have hlow := eLpNorm_le_of_ae_eq_indicator_cutoff (p := p) hst.le u hζ1 _ hw
  -- Sobolev–Poincaré for `u` and Hölder's inequality for `G` on `B_t`.
  have hSP := eLpNorm_value_sub_setAverage_le_of_memLp u hball hp_top hqp hv hg hδ hδn ht htR
  have hHol : eLpNorm G q (volume.restrict (ball x₀ t)) ≤
      eLpNorm G p (volume.restrict (ball x₀ t)) * volume (ball x₀ t) ^ δ := by
    have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ hqp hG'.aestronglyMeasurable
    rwa [Measure.restrict_apply_univ, one_div, one_div, hδ] at h
  have hεε' : volume (ball x₀ t) ^ (-δ) * volume (ball x₀ t) ^ δ = 1 := by
    rw [← ENNReal.rpow_add _ _ (measure_ball_pos volume x₀ ht).ne' measure_ball_lt_top.ne,
      neg_add_cancel, ENNReal.rpow_zero]
  calc eLpNorm (W1p.gradient u) p (volume.restrict (ball x₀ s))
      ≤ CW * eLpNorm F p volume := hlow.trans (hW ha hbd hosc x₀ w F hw0 hweq hwint hwp hF)
    _ ≤ _ := (mul_le_mul_right hFle _).trans
        (step_bound_le hc₀ hLam hK hs hst (eLpNorm_mono_measure _ hle) hεε' hSP hHol)

end Step

section Absorption

/-- Young's inequality in the form used for absorption:
`K X^θ F^(1-θ) ≤ F / 2 + (2 K)^(1/θ) X` for `K, X, F ≥ 0` and `0 < θ ≤ 1`. -/
private theorem mul_rpow_mul_rpow_le_half_add {K X F θ : ℝ} (hK : 0 ≤ K) (hX : 0 ≤ X)
    (hF : 0 ≤ F) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    K * (X ^ θ * F ^ (1 - θ)) ≤ F / 2 + (2 * K) ^ θ⁻¹ * X := by
  have hp₁ : 0 ≤ (2 * K) ^ θ⁻¹ * X := by positivity
  have hp₂ : 0 ≤ F / 2 := by positivity
  have hAM := Real.geom_mean_le_arith_mean2_weighted hθ0.le (sub_nonneg.2 hθ1) hp₁ hp₂
    (by ring)
  have h1 : ((2 * K) ^ θ⁻¹ * X) ^ θ = 2 * K * X ^ θ := by
    rw [Real.mul_rpow (by positivity) hX, Real.rpow_inv_rpow (by positivity) hθ0.ne']
  have h2 : (F / 2) ^ (1 - θ) = F ^ (1 - θ) / 2 ^ (1 - θ) := Real.div_rpow hF (by norm_num) _
  have h3 : (2 : ℝ) ^ (1 - θ) ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (by linarith : 1 - θ ≤ 1)
  have h4 : (0 : ℝ) < 2 ^ (1 - θ) := by positivity
  calc K * (X ^ θ * F ^ (1 - θ)) ≤ 2 * K * X ^ θ * F ^ (1 - θ) / 2 ^ (1 - θ) := by
        rw [le_div_iff₀ h4]
        have : 0 ≤ K * X ^ θ * F ^ (1 - θ) := by positivity
        nlinarith
    _ = ((2 * K) ^ θ⁻¹ * X) ^ θ * (F / 2) ^ (1 - θ) := by rw [h1, h2]; ring
    _ ≤ θ * ((2 * K) ^ θ⁻¹ * X) + (1 - θ) * (F / 2) := hAM
    _ ≤ (2 * K) ^ θ⁻¹ * X + F / 2 := by
        gcongr ?_ + ?_
        · exact mul_le_of_le_one_left hp₁ hθ1
        · exact mul_le_of_le_one_left hp₂ (by linarith)
    _ = _ := by ring

/-- One step of the absorption: Young's inequality turns the step estimate into
`f s ≤ f t / 2 + A (t - s)^(-1/θ) + B`. -/
private theorem le_half_add_of_step {θ Cs R Γ X ε : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hCs : 0 ≤ Cs) (hΓ : 0 ≤ Γ) (hX : 0 ≤ X) (hε : 0 ≤ ε) {f : ℝ → ℝ} (hf0 : ∀ σ, 0 ≤ f σ)
    {s t : ℝ} (hs : R / 2 ≤ s) (hst : s < t) (htR : t ≤ R)
    (hstep : f s ≤ Cs * ((1 + t / (t - s)) * Γ + t / (t - s) * ε * (X ^ θ * f t ^ (1 - θ)))) :
    f s ≤ 1 / 2 * f t + ((2 * Cs * ε * R) ^ θ⁻¹ * X + Cs * Γ * R * (R / 2) ^ (θ⁻¹ - 1)) *
      (t - s) ^ (-θ⁻¹) + Cs * Γ := by
  set β := θ⁻¹
  have hβ1 : 1 ≤ β := one_le_inv₀ hθ0 |>.2 hθ1
  have hR : 0 < R := by linarith
  have hts : 0 < t - s := sub_pos.2 hst
  have htsR : t - s ≤ R / 2 := by linarith
  have ht : 0 < t := by linarith
  have hτ : t / (t - s) ≤ R * (R / 2) ^ (β - 1) * (t - s) ^ (-β) := by
    have e : (t - s)⁻¹ = (t - s) ^ (β - 1) * (t - s) ^ (-β) := by
      rw [← Real.rpow_add hts, show β - 1 + -β = -1 by ring, Real.rpow_neg_one]
    calc t / (t - s) ≤ R / (t - s) := by gcongr
      _ = R * ((t - s) ^ (β - 1) * (t - s) ^ (-β)) := by rw [div_eq_mul_inv, e]
      _ ≤ R * ((R / 2) ^ (β - 1) * (t - s) ^ (-β)) := by
        gcongr
      _ = _ := by ring
  have hK : (2 * (Cs * (t / (t - s)) * ε)) ^ β ≤ (2 * Cs * ε * R) ^ β * (t - s) ^ (-β) := by
    rw [Real.rpow_neg hts.le, ← div_eq_mul_inv, ← Real.div_rpow (by positivity) hts.le]
    gcongr
    rw [le_div_iff₀ hts]
    have : t / (t - s) * (t - s) = t := div_mul_cancel₀ _ hts.ne'
    nlinarith [mul_nonneg hCs hε]
  have hY := mul_rpow_mul_rpow_le_half_add (K := Cs * (t / (t - s)) * ε)
    (mul_nonneg (mul_nonneg hCs (div_nonneg ht.le hts.le)) hε) hX (hf0 t) hθ0 hθ1
  calc f s ≤ Cs * ((1 + t / (t - s)) * Γ + t / (t - s) * ε * (X ^ θ * f t ^ (1 - θ))) :=
        hstep
    _ = Cs * Γ + Cs * Γ * (t / (t - s)) +
        Cs * (t / (t - s)) * ε * (X ^ θ * f t ^ (1 - θ)) := by ring
    _ ≤ Cs * Γ + Cs * Γ * (R * (R / 2) ^ (β - 1) * (t - s) ^ (-β)) +
        (f t / 2 + (2 * Cs * ε * R) ^ β * (t - s) ^ (-β) * X) := by
        refine add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left hτ (by positivity)))
          (hY.trans ?_)
        gcongr
    _ = _ := by ring

/-- **Absorption over concentric balls.** Fix `0 < θ ≤ 1` and `Cs ≥ 0`. If a nonnegative function
`f`, bounded on `[R/2, R]`, satisfies for `R/2 ≤ s < t ≤ R`

`f s ≤ Cs ((1 + t/(t - s)) Γ + t/(t - s) ε X^θ (f t)^(1-θ))`,

then `f (R/2) ≤ C₁ (Γ + ε^(1/θ) X)`, with `C₁` depending only on `θ` and `Cs`. -/
private theorem exists_le_mul_add_rpow_mul_of_le {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) {Cs : ℝ}
    (hCs : 0 ≤ Cs) :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ {f : ℝ → ℝ} {R Γ X ε : ℝ}, 0 < R → 0 ≤ Γ → 0 ≤ X → 0 ≤ ε →
      (∀ σ, 0 ≤ f σ) → BddAbove (f '' Icc (R / 2) R) →
      (∀ s t, R / 2 ≤ s → s < t → t ≤ R →
        f s ≤ Cs * ((1 + t / (t - s)) * Γ + t / (t - s) * ε * (X ^ θ * f t ^ (1 - θ)))) →
      f (R / 2) ≤ C₁ * (Γ + ε ^ θ⁻¹ * X) := by
  obtain ⟨Cab, hCab, habs⟩ :=
    exists_le_mul_mul_rpow_add_of_le_mul_add (θ := 1 / 2) (by norm_num) (by norm_num) θ⁻¹
  refine ⟨Cab * ((4 * Cs) ^ θ⁻¹ + 3 * Cs), by positivity,
    fun {f R Γ X ε} hR hΓ hX hε hf0 hbdd hstep => ?_⟩
  set β := θ⁻¹
  set A := (2 * Cs * ε * R) ^ β * X + Cs * Γ * R * (R / 2) ^ (β - 1)
  have hA : 0 ≤ A := by positivity
  have key : ∀ s t, R / 2 ≤ s → s < t → t ≤ R →
      f s ≤ 1 / 2 * f t + A * (t - s) ^ (-β) + Cs * Γ := fun s t hs hst htR =>
    le_half_add_of_step hθ0 hθ1 hCs hΓ hX hε hf0 hs hst htR (hstep s t hs hst htR)
  have h := habs (f := f) (r₀ := R / 2) (r₁ := R) (by linarith) hA (by positivity) hbdd key
  have hR2 : 0 < R / 2 := by positivity
  have hAR : A * (R - R / 2) ^ (-β) = (4 * Cs) ^ β * ε ^ β * X + 2 * (Cs * Γ) := by
    rw [show R - R / 2 = R / 2 by ring]
    simp only [A, add_mul]
    congr 1
    · rw [mul_comm _ X, mul_assoc, ← Real.mul_rpow (by positivity) (by positivity),
        Real.rpow_neg hR2.le, ← Real.inv_rpow hR2.le,
        ← Real.mul_rpow (by positivity) (by positivity),
        show 2 * Cs * ε * R * (R / 2)⁻¹ = 4 * Cs * ε by field_simp; ring,
        Real.mul_rpow (by positivity) hε]
      ring
    · rw [mul_assoc, ← Real.rpow_add hR2, show β - 1 + -β = -1 by ring, Real.rpow_neg_one]
      field_simp
  rw [hAR] at h
  calc f (R / 2) ≤ Cab * ((4 * Cs) ^ β * ε ^ β * X + 2 * (Cs * Γ) + Cs * Γ) := h
    _ ≤ Cab * (((4 * Cs) ^ β + 3 * Cs) * (Γ + ε ^ β * X)) := by
        gcongr
        nlinarith [mul_nonneg (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 4 * Cs) β)
          (mul_nonneg (Real.rpow_nonneg hε β) hX), mul_nonneg hCs hΓ,
          mul_nonneg hCs (mul_nonneg (Real.rpow_nonneg hε β) hX),
          mul_nonneg (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 4 * Cs) β) hΓ]
    _ = _ := by ring

/-- The intermediate exponent `q` with `1/q = θ/2 + (1 - θ)/p`, for `2 < p < ∞` and `0 < θ < 1`:
it lies in `(1, p]`, and `1/q - 1/p = θ (1/2 - 1/p)`. -/
private theorem exists_interpolation_exponent {p : ℝ≥0∞} (hp : 2 < p) (hp_top : p ≠ ⊤) {θ : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    ∃ q : ℝ≥0∞, 1 < q ∧ q ≤ p ∧
      q⁻¹ = ENNReal.ofReal θ * 2⁻¹ + ENNReal.ofReal (1 - θ) * p⁻¹ ∧
      q.toReal⁻¹ - p.toReal⁻¹ = θ * (2⁻¹ - p.toReal⁻¹) := by
  have hpR : 2 < p.toReal := by simpa using ENNReal.toReal_strict_mono hp_top hp
  set Q : ℝ := θ / 2 + (1 - θ) / p.toReal
  have hQ0 : 0 < Q := by positivity
  have hQ1 : Q < 1 := by
    have : (1 - θ) / p.toReal < (1 - θ) / 2 := by gcongr
    simp only [Q]
    linarith
  have hQp : p.toReal⁻¹ ≤ Q := by
    have : p.toReal⁻¹ < 2⁻¹ := by rw [inv_lt_inv₀ (by linarith) (by norm_num)]; exact hpR
    simp only [Q]; rw [div_eq_mul_inv, div_eq_mul_inv]; nlinarith
  refine ⟨ENNReal.ofReal Q⁻¹, ?_, ?_, ?_, ?_⟩
  · rw [← ENNReal.ofReal_one, ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    exact one_lt_inv₀ hQ0 |>.2 hQ1
  · rw [← ENNReal.ofReal_toReal hp_top, ENNReal.ofReal_le_ofReal_iff (by positivity)]
    rw [inv_le_comm₀ hQ0 (by linarith)]
    exact hQp
  · rw [← ENNReal.ofReal_inv_of_pos (inv_pos.2 hQ0), inv_inv, ← ENNReal.ofReal_toReal hp_top,
      ← ENNReal.ofReal_inv_of_pos (by linarith), ← ENNReal.ofReal_ofNat 2,
      ← ENNReal.ofReal_inv_of_pos (by norm_num), ← ENNReal.ofReal_mul hθ0.le,
      ← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_add (by positivity) (by
        have : 0 ≤ 1 - θ := by linarith
        positivity)]
    simp only [Q]
    congr 1
  · rw [ENNReal.toReal_ofReal (by positivity), inv_inv]
    simp only [Q]
    ring

end Absorption

/-- The step between concentric balls in real numbers, after interpolating the `L^q` norm of the
gradient between its `L²` and `Lᵖ` norms and comparing `|B_t|` with `|B_{R/2}|`. -/
private theorem step_toReal {p q : ℝ≥0∞} {θ δ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hqinv : q⁻¹ = ENNReal.ofReal θ * 2⁻¹ + ENNReal.ofReal (1 - θ) * p⁻¹) (hδ0 : 0 ≤ δ)
    {g G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    {x₀ : EuclideanSpace ℝ (Fin (n + 1))} {R s t : ℝ} {Cs : ℝ≥0}
    (hft : eLpNorm g p (volume.restrict (ball x₀ t)) ≠ ⊤)
    (hGfin : eLpNorm G p (volume.restrict (ball x₀ R)) ≠ ⊤)
    (hXfin : eLpNorm g 2 (volume.restrict (ball x₀ R)) ≠ ⊤) (hR : 0 < R)
    (htR' : volume.restrict (ball x₀ t) ≤ volume.restrict (ball x₀ R))
    (hs : R / 2 ≤ s) (hst : s < t) (htR : t ≤ R)
    (h : eLpNorm g p (volume.restrict (ball x₀ s)) ≤
      Cs * ((1 + ENNReal.ofReal (t / (t - s))) * eLpNorm G p (volume.restrict (ball x₀ R)) +
        ENNReal.ofReal (t / (t - s)) * volume (ball x₀ t) ^ (-δ) *
          eLpNorm g q (volume.restrict (ball x₀ t)))) :
    (eLpNorm g p (volume.restrict (ball x₀ s))).toReal ≤
      Cs * ((1 + t / (t - s)) * (eLpNorm G p (volume.restrict (ball x₀ R))).toReal +
        t / (t - s) * (volume (ball x₀ (R / 2))).toReal ^ (-δ) *
          ((eLpNorm g 2 (volume.restrict (ball x₀ R))).toReal ^ θ *
            (eLpNorm g p (volume.restrict (ball x₀ t))).toReal ^ (1 - θ))) := by
  have hτ : 0 ≤ t / (t - s) := div_nonneg (by linarith) (sub_pos.2 hst).le
  have hR2 : volume (ball x₀ (R / 2)) ≠ 0 := (measure_ball_pos volume x₀ (by positivity)).ne'
  -- Interpolation: `‖g‖_q ≤ ‖g‖₂^θ ‖g‖_p^(1-θ)` on `B_t`, and `‖g‖_{L²(B_t)} ≤ ‖g‖_{L²(B_R)}`.
  have hint : eLpNorm g q (volume.restrict (ball x₀ t)) ≤
      eLpNorm g 2 (volume.restrict (ball x₀ R)) ^ θ *
        eLpNorm g p (volume.restrict (ball x₀ t)) ^ (1 - θ) := by
    have h1 := eLpNorm_le_eLpNorm_rpow_mul_eLpNorm_rpow (f := g)
      (μ := volume.restrict (ball x₀ t)) (p₀ := 2) (p₁ := p) (θ := 1 - θ)
      ⟨by linarith, by linarith⟩ (by rw [hqinv, sub_sub_cancel])
    rw [sub_sub_cancel] at h1
    exact h1.trans (by gcongr)
  -- `|B_t|^(-δ) ≤ |B_{R/2}|^(-δ)`.
  have hεle : volume (ball x₀ t) ^ (-δ) ≤ volume (ball x₀ (R / 2)) ^ (-δ) := by
    rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
    exact ENNReal.inv_le_inv.2 (ENNReal.rpow_le_rpow (measure_mono (ball_subset_ball
      (by linarith))) hδ0)
  have h' : eLpNorm g p (volume.restrict (ball x₀ s)) ≤
      Cs * ((1 + ENNReal.ofReal (t / (t - s))) * eLpNorm G p (volume.restrict (ball x₀ R)) +
        ENNReal.ofReal (t / (t - s)) * volume (ball x₀ (R / 2)) ^ (-δ) *
          (eLpNorm g 2 (volume.restrict (ball x₀ R)) ^ θ *
            eLpNorm g p (volume.restrict (ball x₀ t)) ^ (1 - θ))) :=
    h.trans (by gcongr)
  have hε : volume (ball x₀ (R / 2)) ^ (-δ) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_ne_zero hR2 measure_ball_lt_top.ne
  have h1 : (1 + ENNReal.ofReal (t / (t - s))) * eLpNorm G p (volume.restrict (ball x₀ R)) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.ofReal_ne_top⟩) hGfin
  have h2 : ENNReal.ofReal (t / (t - s)) * volume (ball x₀ (R / 2)) ^ (-δ) *
      (eLpNorm g 2 (volume.restrict (ball x₀ R)) ^ θ *
        eLpNorm g p (volume.restrict (ball x₀ t)) ^ (1 - θ)) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hε) (ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg hθ0.le hXfin)
      (ENNReal.rpow_ne_top_of_nonneg (by linarith) hft))
  refine (ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top
    (ENNReal.add_ne_top.2 ⟨h1, h2⟩)) h').trans_eq ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_add h1 h2, ENNReal.toReal_mul, ENNReal.toReal_add
    ENNReal.one_ne_top ENNReal.ofReal_ne_top, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_mul, ENNReal.toReal_rpow, ENNReal.toReal_rpow, ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal hτ, ENNReal.toReal_one, ENNReal.coe_toReal]

/-- Halving the radius of a ball divides its volume by `2ᵈ`, so for `e ≥ -1`,
`|B_{R/2}|^e ≤ 2ᵈ |B_R|^e`. -/
private theorem toReal_volume_ball_half_rpow_le {x₀ : EuclideanSpace ℝ (Fin (n + 1))} {R : ℝ}
    (hR : 0 < R) {e : ℝ} (he1 : -1 ≤ e) :
    (volume (ball x₀ (R / 2))).toReal ^ e ≤
      2 ^ finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) * (volume (ball x₀ R)).toReal ^ e := by
  set d := finrank ℝ (EuclideanSpace ℝ (Fin (n + 1)))
  have hμR : 0 < (volume (ball x₀ R)).toReal :=
    ENNReal.toReal_pos (measure_ball_pos volume x₀ hR).ne' measure_ball_lt_top.ne
  have hμR2 : (volume (ball x₀ (R / 2))).toReal = (2 ^ d)⁻¹ * (volume (ball x₀ R)).toReal := by
    rw [Measure.addHaar_ball volume x₀ hR.le,
      Measure.addHaar_ball volume x₀ (by positivity : 0 ≤ R / 2), ENNReal.toReal_mul,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
      ENNReal.toReal_ofReal (by positivity), div_pow]
    field_simp
    ring
  rw [hμR2, Real.mul_rpow (by positivity) hμR.le, Real.inv_rpow (by positivity),
    ← Real.rpow_neg (by positivity)]
  gcongr
  calc ((2 : ℝ) ^ d) ^ (-e) ≤ ((2 : ℝ) ^ d) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ one_le_two) (by linarith)
    _ = 2 ^ d := Real.rpow_one _

/-- Returning from real numbers to `ℝ≥0∞`: a bound `A.toReal ≤ C (Γ.toReal + m.toReal^e X.toReal)`
for finite `A`, `Γ`, `X` and finite positive `m` gives `A ≤ C (Γ + m^e X)`. -/
private theorem le_mul_add_rpow_mul_of_toReal_le {A Γ X m : ℝ≥0∞} {C e : ℝ} (hC : 0 ≤ C)
    (hA : A ≠ ⊤) (hΓ : Γ ≠ ⊤) (hX : X ≠ ⊤) (hm0 : m ≠ 0) (hm : m ≠ ⊤)
    (h : A.toReal ≤ C * (Γ.toReal + m.toReal ^ e * X.toReal)) :
    A ≤ C.toNNReal * (Γ + m ^ e * X) := by
  have hmR : 0 < m.toReal := ENNReal.toReal_pos hm0 hm
  calc A = ENNReal.ofReal A.toReal := (ENNReal.ofReal_toReal hA).symm
    _ ≤ ENNReal.ofReal (C * (Γ.toReal + m.toReal ^ e * X.toReal)) := ENNReal.ofReal_le_ofReal h
    _ = _ := by
        rw [ENNReal.ofReal_mul hC, ENNReal.ofReal_add ENNReal.toReal_nonneg (by positivity),
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hΓ, ENNReal.ofReal_toReal hX,
          ← ENNReal.ofReal_rpow_of_pos hmR, ENNReal.ofReal_toReal hm]
        rfl

/-- Absorption and the return to `ℝ≥0∞` in the interior estimate: if the step estimate between
concentric balls holds for `g` on `B_R`, with the `L^q` norm on the right, then
`‖g‖_{Lᵖ(B_{R/2})} ≤ C (‖G‖_{Lᵖ(B_R)} + |B_R|^(1/p - 1/2) ‖g‖_{L²(B_R)})`. -/
private theorem eLpNorm_ball_half_le_of_step {p q : ℝ≥0∞} (hp : 2 < p)
    (hp_top : p ≠ ⊤) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hqinv : q⁻¹ = ENNReal.ofReal θ * 2⁻¹ + ENNReal.ofReal (1 - θ) * p⁻¹)
    (hδ0 : 0 ≤ θ * (2⁻¹ - p.toReal⁻¹)) {Cs : ℝ≥0} {C₁ : ℝ} (hC₁ : 0 ≤ C₁)
    (habs : ∀ {f : ℝ → ℝ} {R Γ X ε : ℝ}, 0 < R → 0 ≤ Γ → 0 ≤ X → 0 ≤ ε →
      (∀ σ, 0 ≤ f σ) → BddAbove (f '' Icc (R / 2) R) →
      (∀ s t, R / 2 ≤ s → s < t → t ≤ R →
        f s ≤ Cs * ((1 + t / (t - s)) * Γ + t / (t - s) * ε * (X ^ θ * f t ^ (1 - θ)))) →
      f (R / 2) ≤ C₁ * (Γ + ε ^ θ⁻¹ * X))
    {g G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    {x₀ : EuclideanSpace ℝ (Fin (n + 1))} {R : ℝ} (hR : 0 < R)
    (hg : MemLp g p (volume.restrict (ball x₀ R))) (hG : MemLp G p (volume.restrict (ball x₀ R)))
    (hstep : ∀ {s t : ℝ}, 0 < s → s < t → t ≤ R →
      eLpNorm g p (volume.restrict (ball x₀ s)) ≤
        Cs * ((1 + ENNReal.ofReal (t / (t - s))) * eLpNorm G p (volume.restrict (ball x₀ R)) +
          ENNReal.ofReal (t / (t - s)) * volume (ball x₀ t) ^ (-(θ * (2⁻¹ - p.toReal⁻¹))) *
            eLpNorm g q (volume.restrict (ball x₀ t)))) :
    eLpNorm g p (volume.restrict (ball x₀ (R / 2))) ≤
      (C₁ * 2 ^ finrank ℝ (EuclideanSpace ℝ (Fin (n + 1)))).toNNReal *
        (eLpNorm G p (volume.restrict (ball x₀ R)) +
          volume (ball x₀ R) ^ (p.toReal⁻¹ - 2⁻¹) * eLpNorm g 2 (volume.restrict (ball x₀ R))) := by
  set d := finrank ℝ (EuclideanSpace ℝ (Fin (n + 1)))
  have hpR : 2 < p.toReal := by simpa using ENNReal.toReal_strict_mono hp_top hp
  set δ := θ * (2⁻¹ - p.toReal⁻¹)
  have : IsFiniteMeasure (volume.restrict (ball x₀ R)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hres (σ : ℝ) (hσ : σ ≤ R) : volume.restrict (ball x₀ σ) ≤ volume.restrict (ball x₀ R) :=
    Measure.restrict_mono (ball_subset_ball hσ) le_rfl
  have hfin (σ : ℝ) (hσ : σ ≤ R) :
      eLpNorm g p (volume.restrict (ball x₀ σ)) ≠ ⊤ :=
    ((hg.mono_measure (hres σ hσ)).eLpNorm_lt_top).ne
  set f : ℝ → ℝ := fun σ => (eLpNorm g p (volume.restrict (ball x₀ σ))).toReal
  set ε : ℝ := (volume (ball x₀ (R / 2))).toReal ^ (-δ)
  have hR2pos : 0 < (volume (ball x₀ (R / 2))).toReal :=
    ENNReal.toReal_pos (measure_ball_pos volume x₀ (by positivity)).ne' measure_ball_lt_top.ne
  have hbdd : BddAbove (f '' Icc (R / 2) R) := by
    refine ⟨f R, ?_⟩
    rintro _ ⟨σ, hσ, rfl⟩
    exact ENNReal.toReal_mono (hfin R le_rfl) (eLpNorm_mono_measure _ (hres σ hσ.2))
  have hstep' : ∀ s t, R / 2 ≤ s → s < t → t ≤ R →
      f s ≤ Cs * ((1 + t / (t - s)) * (eLpNorm G p (volume.restrict (ball x₀ R))).toReal +
        t / (t - s) * ε * ((eLpNorm g 2 (volume.restrict (ball x₀ R))).toReal ^ θ *
          f t ^ (1 - θ))) := by
    intro s t hs hst htR
    exact step_toReal hθ0 hθ1 hqinv hδ0 (hfin t htR)
      (hG.eLpNorm_ne_top) ((hg.mono_exponent hp.le).eLpNorm_ne_top) hR
      (hres t htR) hs hst htR
      (hstep (by linarith) hst htR)
  have hmain := habs hR ENNReal.toReal_nonneg ENNReal.toReal_nonneg (Real.rpow_nonneg hR2pos.le _)
    (fun _ => ENNReal.toReal_nonneg) hbdd hstep'
  -- `|B_{R/2}|^(-δ/θ) ≤ 2^d |B_R|^(1/p - 1/2)`.
  set μR := (volume (ball x₀ R)).toReal
  have hεθ : ε ^ θ⁻¹ ≤ 2 ^ d * μR ^ (p.toReal⁻¹ - 2⁻¹) := by
    have he : -δ * θ⁻¹ = p.toReal⁻¹ - 2⁻¹ := by
      simp only [δ]; field_simp; ring
    rw [← Real.rpow_mul hR2pos.le, he]
    have : 0 ≤ p.toReal⁻¹ := by positivity
    exact toReal_volume_ball_half_rpow_le hR (by linarith)
  set Γ := (eLpNorm G p (volume.restrict (ball x₀ R))).toReal
  set X := (eLpNorm g 2 (volume.restrict (ball x₀ R))).toReal
  have hΓ : 0 ≤ Γ := ENNReal.toReal_nonneg
  have h2d : (1 : ℝ) ≤ 2 ^ d := one_le_pow₀ one_le_two
  refine le_mul_add_rpow_mul_of_toReal_le (by positivity) (hfin _ (by linarith)) hG.eLpNorm_ne_top
    (hg.mono_exponent hp.le).eLpNorm_ne_top (measure_ball_pos volume x₀ hR).ne'
    measure_ball_lt_top.ne (hmain.trans ?_)
  calc C₁ * (Γ + ε ^ θ⁻¹ * X) ≤ C₁ * (Γ + 2 ^ d * μR ^ (p.toReal⁻¹ - 2⁻¹) * X) := by gcongr
    _ ≤ C₁ * (2 ^ d * Γ + 2 ^ d * (μR ^ (p.toReal⁻¹ - 2⁻¹) * X)) := by
        rw [← mul_assoc (2 ^ d : ℝ)]
        gcongr
        exact le_mul_of_one_le_left hΓ h2d
    _ = _ := by ring


/-- **The interior `W^{1,p}` estimate for coefficients of small mean oscillation.** Let
`2 < p < ∞` and `0 < λ ≤ Λ`. There are constants `C` and `δ > 0`, depending only on `n`, `p`, `λ`
and `Λ`, with the following property. Let `a` be a measurable coefficient matrix on `ℝ^{n+1}`,
bounded by `Λ`, such that on every ball `B` of radius at most `r₀` some constant matrix `A`,
uniformly elliptic with constants `λ, Λ`, has mean deviation `⨍_B ‖a - A‖ ≤ δ` from `a`. Let
`u ∈ H¹(Ω)` solve `-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` weakly in `Ω`, let `B(x₀, R) ⊆ Ω` with `4 R ≤ r₀`, and
let `u`, `∇u` and `G` lie in `Lᵖ(B(x₀, R))`. Then

`‖∇u‖_{Lᵖ(B(x₀, R/2))} ≤ C (‖G‖_{Lᵖ(B(x₀, R))} + |B(x₀, R)|^(1/p - 1/2) ‖∇u‖_{L²(B(x₀, R))})`.

The coefficients need not be symmetric or continuous, and nothing is assumed about `∂Ω`. -/
theorem exists_eLpNorm_gradient_ball_le_of_setAverage_le {p : ℝ≥0∞} (hp : 2 < p)
    (hp_top : p ≠ ⊤) (lam Lam : ℝ) :
    ∃ C : ℝ≥0, ∃ δ : ℝ, 0 < δ ∧
      ∀ {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {r₀ : ℝ},
        AEStronglyMeasurable a volume → (∀ x, ‖matrixBilinearForm (a x)‖ ≤ Lam) →
        (∀ (c : EuclideanSpace ℝ (Fin (n + 1))) (r : ℝ), 0 < r → r ≤ r₀ →
          ∃ A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ,
            UniformlyEllipticOn (ball c r) (fun _ => A) lam Lam ∧
              ⨍ x in ball c r, ‖matrixBilinearForm (a x) - matrixBilinearForm A‖ ≤ δ) →
        ∀ {Ω : Opens (EuclideanSpace ℝ (Fin (n + 1)))} {x₀ : EuclideanSpace ℝ (Fin (n + 1))}
          {R : ℝ}, 0 < R → 4 * R ≤ r₀ → ball x₀ R ⊆ (Ω : Set _) →
        ∀ (u : W1p volume Ω 2)
          (G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))),
          (∀ φ : 𝓓(Ω, ℝ), energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume Ω 2 φ) =
            ∫ x in Ω, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) →
          MemLp (W1p.value u) p (volume.restrict (ball x₀ R)) →
          MemLp (W1p.gradient u) p (volume.restrict (ball x₀ R)) →
          MemLp G p (volume.restrict (ball x₀ R)) →
          eLpNorm (W1p.gradient u) p (volume.restrict (ball x₀ (R / 2))) ≤
            C * (eLpNorm G p (volume.restrict (ball x₀ R)) +
              volume (ball x₀ R) ^ (p.toReal⁻¹ - 2⁻¹) *
                eLpNorm (W1p.gradient u) 2 (volume.restrict (ball x₀ R))) := by
  have : Fact (1 ≤ p) := ⟨one_le_two.trans hp.le⟩
  set d := finrank ℝ (EuclideanSpace ℝ (Fin (n + 1)))
  have hd : (1 : ℝ) ≤ d := by exact_mod_cast finrank_pos
  set θ : ℝ := ((d : ℝ) + 1)⁻¹
  have hθ0 : 0 < θ := by positivity
  have hθ1 : θ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  obtain ⟨q, hq1, hqp, hqinv, hqδ⟩ := exists_interpolation_exponent hp hp_top hθ0 hθ1
  have : Fact (1 ≤ q) := ⟨hq1.le⟩
  have hpR : 2 < p.toReal := by simpa using ENNReal.toReal_strict_mono hp_top hp
  have hδ0 : 0 ≤ θ * (2⁻¹ - p.toReal⁻¹) := by
    have : p.toReal⁻¹ < 2⁻¹ := by rw [inv_lt_inv₀ (by linarith) (by norm_num)]; exact hpR
    nlinarith
  have hδn : θ * (2⁻¹ - p.toReal⁻¹) < (d : ℝ)⁻¹ := by
    have h1 : θ * (2⁻¹ - p.toReal⁻¹) ≤ θ := by
      have : 0 ≤ p.toReal⁻¹ := by positivity
      nlinarith
    exact h1.trans_lt (inv_strictAnti₀ (by positivity) (by linarith))
  obtain ⟨Cs, δ₀, hδ₀, hstep⟩ :=
    exists_eLpNorm_gradient_ball_le_step (n := n) hp hp_top hq1 hqp hqδ hδn lam Lam
  obtain ⟨C₁, hC₁, habs⟩ := exists_le_mul_add_rpow_mul_of_le hθ0 hθ1.le Cs.coe_nonneg
  refine ⟨(C₁ * 2 ^ d).toNNReal, δ₀, hδ₀,
    fun {a r₀} ha hbd hosc {Ω x₀ R} hR hRr₀ hball u G hu hv hg hG => ?_⟩
  exact eLpNorm_ball_half_le_of_step hp hp_top hθ0 hθ1 hqinv hδ0 hC₁ habs hR hg hG
    (fun hs hst htR => hstep ha hbd hosc hRr₀ hball u G hu hv hg hG hs hst htR)

end PDE

end TauCeti
