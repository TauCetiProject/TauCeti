/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.SmallMeanOscillation
public import TauCeti.Analysis.Sobolev.Poincare.Wirtinger.Divergence
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.PDE.Caccioppoli.Divergence
import TauCeti.Analysis.PDE.EnergyForm.Measurability
import TauCeti.Analysis.Sobolev.W1p.CompactSupport
import TauCeti.Analysis.SpecificLimits.Absorption
import TauCeti.Data.ENNReal.InterpolatedExponent
import TauCeti.MeasureTheory.Function.Lp.IntermediateExponent
import TauCeti.MeasureTheory.Function.LpSeminorm.Ball
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Interior and whole-space `W^{1,p}` estimates for coefficients of vanishing mean oscillation

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

(`TauCeti.PDE.exists_eLpNorm_gradient_ball_le_eLpNorm_two_of_setAverage_le`), with `C` and the
threshold `δ` depending only on `n`, `p`, `λ` and `Λ`, and not on `R`, `r₀`, `u` or `G`. Unlike the
interior estimate `TauCeti.PDE.exists_eLpNorm_gradient_ball_le_of_setAverage_le`, which needs
dimension at least two and bounds `∇u` by `u - m` in `Lᵖ` and `∇u` in a Sobolev exponent below `p`,
this one holds in every dimension and needs only the `L²` norm of `∇u`. The estimate is
invariant under dilations, and the factor `|B_R|^(1/p - 1/2)` turns the `L²` norm of `∇u` into its
`Lᵖ` scale. It is quantitative in `u`, as it must be: `u ↦ M u` scales both sides. The membership
`∇u ∈ Lᵖ(B_R)` is an a priori assumption: the estimate bounds the norm, it does not prove that it
is finite. For uniformly elliptic coefficients the assumption is removed, by approximation, in
`TauCeti.Analysis.PDE.Regularity.VanishingMeanOscillation.Regularity`.

If `a` is also uniformly elliptic on `B(x₀, 2R)`, Caccioppoli's inequality
(`TauCeti.PDE.exists_eLpNorm_gradient_ball_le_of_forall_testFunction`) and Hölder's inequality
(`TauCeti.measure_ball_rpow_mul_eLpNorm_restrict_ball_le`) turn the `L²` norm of `∇u` into the
`Lᵖ` norm of `u` on a larger ball: if `B(x₀, 2R) ⊆ Ω`, `4 R ≤ r₀` and `∇u ∈ Lᵖ(B_R)`, then

`‖∇u‖_{Lᵖ(B_{R/2})} ≤ C (‖G‖_{Lᵖ(B_{2R})} + R⁻¹ ‖u‖_{Lᵖ(B_{2R})})`

(`TauCeti.PDE.exists_eLpNorm_gradient_ball_le_eLpNorm_value_of_setAverage_le`). Averaging the
`p`-th powers of these interior estimates over all centres
(`TauCeti.eLpNorm_le_of_ae_eLpNorm_restrict_ball_le_add`) gives the estimate on the whole space:
for `a` uniformly elliptic on `ℝ^{n+1}` and of small mean oscillation below `r₀ > 0`, every
`u ∈ H¹(ℝ^{n+1})` solving `-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` with `∇u ∈ Lᵖ` satisfies

`‖∇u‖_{Lᵖ} ≤ C (‖G‖_{Lᵖ} + r₀⁻¹ ‖u‖_{Lᵖ})`

(`TauCeti.PDE.exists_eLpNorm_gradient_le_eLpNorm_value_of_setAverage_le`), with `C` and `δ`
depending only on `n`, `p`, `λ` and `Λ`. This is the divergence-form counterpart of the
whole-space `W^{2,p}` estimate
`TauCeti.PDE.exists_norm_iteratedGradient_le_of_sum_mul_inner_eq_of_memVMO`. When the mean
oscillation is small at every scale the term `r₀⁻¹ ‖u‖_{Lᵖ}` is absent
(`TauCeti.PDE.exists_eLpNorm_gradient_le_of_forall_energyFormH1_eq_of_setAverage_le`); for
coefficients of vanishing mean oscillation it records the radius below which the oscillation is
small. In Krylov's whole-space theorem this term is removed by a zero-order term `λ u` with `λ`
large.

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
  `‖∇u‖_q ≤ ‖∇u‖₂^θ ‖∇u‖_p^(1-θ)`. Young's inequality (`Real.mul_rpow_mul_rpow_le_half_add`)
  then gives `f(s) ≤ f(t) / 2 + A (t - s)^(-1/θ) + B` for `f(σ) = ‖∇u‖_{Lᵖ(B_σ)}`, and the
  absorption lemma `TauCeti.exists_le_mul_add_rpow_mul_of_le` bounds `f(R/2)`. The exponent `q` is
  chosen with `ε < 1/(n + 1)`, as the Sobolev–Poincaré inequality requires.

## Main declarations

* `TauCeti.PDE.exists_eLpNorm_gradient_ball_le_eLpNorm_two_of_setAverage_le`: the interior
  `W^{1,p}` estimate, `2 < p < ∞`, for coefficients of small mean oscillation below a radius, with
  the `L²` norm of `∇u` on the right.
* `TauCeti.PDE.exists_eLpNorm_gradient_ball_le_eLpNorm_value_of_setAverage_le`: the same estimate
  for uniformly elliptic coefficients, with the `Lᵖ` norm of `u` on the right.
* `TauCeti.PDE.exists_eLpNorm_gradient_le_eLpNorm_value_of_setAverage_le`: the `W^{1,p}` estimate
  on `ℝ^{n+1}` for coefficients of small mean oscillation below a radius `r₀`.
* `TauCeti.PDE.exists_extendByZero_cutoff`, `TauCeti.PDE.energyFormH1_extendByZero_cutoff_eq` and
  `TauCeti.PDE.setIntegral_cutoff_forcing_eq_zero`: the localization of a local weak solution for
  bounded measurable coefficients. A cutoff of the solution, extended by zero, solves a
  whole-space equation whose scalar forcing has mean zero.
* `TauCeti.PDE.exists_wholeSpace_cutoff`: given a divergence representation of mean-zero functions
  on a ball, that whole-space equation in pure divergence form, with an `Lᵖ` bound on its datum.

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

/-- **The extension by zero of a cutoff.** For `u ∈ H¹(Ω)`, a constant `c`, and a smooth compactly
supported `ζ` with `tsupport ζ ⊆ U ⊆ Ω`, the function `ζ (u - c)`, extended by zero, lies in
`H¹(ℝ^{n+1})`, with weak gradient `ζ ∇u + (u - c) ∇ζ` on `U` and zero outside. -/
theorem exists_extendByZero_cutoff (hUΩ : U ≤ Ω)
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

/-- Pairings with a bounded continuous field `V` that are integrable on `U`: `⟪G, V⟫` and
`⟪V, a ∇u⟫`. -/
private theorem integrable_inner_and_matrixBilinearForm (ha : AEStronglyMeasurable a volume)
    {Lam : ℝ} (hbd : ∀ x, ‖matrixBilinearForm (a x)‖ ≤ Lam) (hUΩ : U ≤ Ω)
    [IsFiniteMeasure (volume.restrict (U : Set (EuclideanSpace ℝ (Fin (n + 1)))))]
    {u : W1p volume Ω 2}
    {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    (hG : MemLp G 2 (volume.restrict (U : Set (EuclideanSpace ℝ (Fin (n + 1))))))
    {V : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))} (hV : Continuous V)
    {M : ℝ} (hVM : ∀ x, ‖V x‖ ≤ M) :
    Integrable (fun x => ⟪G x, V x⟫_ℝ) (volume.restrict U) ∧
    Integrable (fun x => matrixBilinearForm (a x) (V x) (W1p.gradient u x))
      (volume.restrict U) := by
  have hLam : 0 ≤ Lam := (ContinuousLinearMap.opNorm_nonneg _).trans (hbd 0)
  have hle : volume.restrict (U : Set (EuclideanSpace ℝ (Fin (n + 1)))) ≤
      volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))) :=
    Measure.restrict_mono hUΩ le_rfl
  have hgu : MemLp (W1p.gradient u : _ → EuclideanSpace ℝ (Fin (n + 1))) 2 (volume.restrict U) :=
    (Lp.memLp (W1p.gradient u)).mono_measure hle
  have hBm : AEStronglyMeasurable (fun x => matrixBilinearForm (a x)) (volume.restrict U) :=
    (continuous_matrixBilinearForm.comp_aestronglyMeasurable ha).restrict
  refine ⟨((hG.integrable one_le_two).norm.mul_const M).mono'
      (hG.aestronglyMeasurable.inner hV.aestronglyMeasurable)
      (ae_of_all _ fun x => (norm_inner_le_norm _ _).trans (by gcongr; exact hVM x)),
    ((hgu.integrable one_le_two).norm.const_mul (Lam * M)).mono'
      (aestronglyMeasurable_matrixBilinearForm_apply hBm hV.aestronglyMeasurable
        ((Lp.aestronglyMeasurable _).mono_measure hle))
      (ae_of_all _ fun x => ((matrixBilinearForm (a x)).le_opNorm₂ _ _).trans
        (by gcongr; exacts [hbd x, hVM x]))⟩

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
  have hLam : 0 ≤ Lam := (ContinuousLinearMap.opNorm_nonneg _).trans (hbd 0)
  have hle : volume.restrict (U : Set (EuclideanSpace ℝ (Fin (n + 1)))) ≤
      volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))) :=
    Measure.restrict_mono hUΩ le_rfl
  obtain ⟨N, -, hζN, hgradN⟩ := (hζ.of_le (by simp)).exists_abs_le_and_norm_gradient_le hζc
  obtain ⟨P, hP, hφP, hgradP⟩ :=
    (φ.contDiff.of_le (by simp)).exists_abs_le_and_norm_gradient_le φ.hasCompactSupport
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
  obtain ⟨hT4, hT1⟩ := integrable_inner_and_matrixBilinearForm ha hbd hUΩ hG (u := u)
    (V := fun x => ζ x • ∇ φ x + φ x • ∇ ζ x) (by fun_prop)
    (norm_smul_gradient_add_smul_gradient_le hζN hgradN hφP hgradP)
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
  exact ⟨hT1, hT2, hT3, hT4⟩

/-- The weak equation of `u` tested against a test function `ψ` supported in `U`, as integrals
over `U`. -/
private theorem setIntegral_test_eq (hUΩ : U ≤ Ω) {u : W1p volume Ω 2}
    {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    (hu : ∀ φ : 𝓓(Ω, ℝ), energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume Ω 2 φ) =
      ∫ x in Ω, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ)
    (ψ : 𝓓(Ω, ℝ)) (hψ : tsupport (ψ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) ⊆ U) :
    ∫ x in U, matrixBilinearForm (a x) (∇ (ψ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x)
      (W1p.gradient u x) = ∫ x in U, ⟪G x, ∇ (ψ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ := by
  have hUΩ' : (U : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ Ω := hUΩ
  have h0 : ∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))) \ U,
      ∇ (ψ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x = 0 := fun x hx =>
    gradient_of_notMem_tsupport fun h => hx.2 (hψ h)
  have h := hu ψ
  rw [energyFormH1_zero_zero_eq_setIntegral] at h
  rw [← setIntegral_eq_of_subset_of_forall_sdiff_eq_zero Ω.isOpen.measurableSet hUΩ'
      (fun x hx => by simp [h0 x hx]),
    ← setIntegral_eq_of_subset_of_forall_sdiff_eq_zero Ω.isOpen.measurableSet hUΩ'
      (fun x hx => by simp [h0 x hx]), ← h]
  refine integral_congr_ae ?_
  filter_upwards [gradientTestFunctionLp_apply_ae (mu := volume) 2 ψ] with x hx
  rw [W1p.gradient_ofTestFunctionₗ, hx]

/-- The weak equation of `u` tested against `ζ φ`, whose gradient vanishes off `U`. -/
private theorem setIntegral_cutoff_test_eq (hUΩ : U ≤ Ω) {u : W1p volume Ω 2}
    {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    (hu : ∀ φ : 𝓓(Ω, ℝ), energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume Ω 2 φ) =
      ∫ x in Ω, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ)
    {ζ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hζ : ContDiff ℝ ∞ ζ)
    (hts : tsupport ζ ⊆ U) (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))), ℝ)) :
    ∫ x in U, matrixBilinearForm (a x) (ζ x • ∇ φ x + φ x • ∇ ζ x)
      (W1p.gradient u x) = ∫ x in U, ⟪G x, ζ x • ∇ φ x + φ x • ∇ ζ x⟫_ℝ := by
  obtain ⟨ψ, hψ, hgradψ⟩ := exists_testFunction_mul hζ (hts.trans hUΩ) φ
  have h := setIntegral_test_eq hUΩ hu ψ (by rw [hψ]; exact tsupport_mul_subset_left.trans hts)
  simpa only [hgradψ] using h

/-- **The weak equation of a cutoff of a local weak solution.** Let `a` be measurable and bounded
by `Lam`, with no ellipticity or continuity assumed. If `u` solves `-div(a ∇u) = -div G` weakly in
`Ω`, and `w` is the extension by zero of `ζ (u - c)` for a cutoff `ζ` supported in `U ⊆ Ω`, then
`w` solves on the whole space

`-div(a ∇w) = -div (ζ G + (u - c) a ∇ζ) + ⟪G, ∇ζ⟫ - ⟪∇ζ, a ∇u⟫`,

both data being supported in `U`. -/
theorem energyFormH1_extendByZero_cutoff_eq (ha : AEStronglyMeasurable a volume)
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
  have hψeq := setIntegral_cutoff_test_eq hUΩ hu hζ hts φ
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

/-- **The cutoff forcing has mean zero.** For measurable coefficients `a` bounded by `Lam`, testing
the equation of a local weak solution with the cutoff `ζ` itself gives
`∫_U (⟪G, ∇ζ⟫ - ⟪∇ζ, a ∇u⟫) = 0`. -/
theorem setIntegral_cutoff_forcing_eq_zero (ha : AEStronglyMeasurable a volume)
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
  obtain ⟨N, -, -, hgradN⟩ := (hζ.of_le (by simp)).exists_abs_le_and_norm_gradient_le hζc
  obtain ⟨hT1, hT2⟩ := integrable_inner_and_matrixBilinearForm ha hbd hUΩ hG (u := u)
    (ContDiff.continuous_gradient hζ (by simp)) hgradN
  have h := setIntegral_test_eq hUΩ hu ⟨ζ, hζ, hζc, hts.trans hUΩ⟩
    (by rw [TestFunction.coe_mk]; exact hts)
  rw [TestFunction.coe_mk] at h
  rw [integral_sub hT1 hT2, h, sub_self]

end Localization

section Step

variable {Ω : Opens (EuclideanSpace ℝ (Fin (n + 1)))}

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
    hv.smul <| (continuous_uncurry_toEuclideanCLM (𝕜 := ℝ)).comp_aestronglyMeasurable
      (f := fun y => (a y, ∇ ζ y)) (ha.restrict.prodMk hgζ.aestronglyMeasurable)
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
  have h2 : Integrable (fun x => V.indicator k x * φ x) :=
    (φ.integrable_smul ((hk.locallyIntegrable Fact.out).locallyIntegrableOn _)).congr
      (ae_of_all _ fun x => by simp [smul_eq_mul, mul_comm])
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
mean-zero functions on `B`, with norm bound `K`, the extension by zero of `ζ (u - c)` solves
`-div(a ∇w) = -div F` on the whole space, for an explicit field `F ∈ Lᵖ`: the divergence datum of
the cutoff plus a field `H` with `-div H` the scalar forcing of the cutoff. -/
theorem exists_wholeSpace_cutoff
    {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (ha : AEStronglyMeasurable a volume) {Lam : ℝ}
    (hbd : ∀ x, ‖matrixBilinearForm (a x)‖ ≤ Lam) {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hp2 : 2 ≤ p) (hqp : q ≤ p) {x₀ : EuclideanSpace ℝ (Fin (n + 1))} {t : ℝ} {K : ℝ≥0∞}
    (hD : ∀ {h : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}, MemLp h q volume →
      (∀ᵐ x, x ∉ ball x₀ t → h x = 0) → ∫ x, h x = 0 →
      ∃ H : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)), MemLp H p volume ∧
        eLpNorm H p volume ≤ K * eLpNorm h q volume ∧
        ∀ φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))), ℝ),
          ∫ x, h x * φ x = ∫ x, ⟪H x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ)
    (hball : ball x₀ t ⊆ (Ω : Set _))
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
        K * (ENNReal.ofReal L * eLpNorm G q (volume.restrict (ball x₀ t)) +
          ENNReal.ofReal (Lam * L) * eLpNorm (W1p.gradient u) q (volume.restrict (ball x₀ t))) := by
  set U : Opens (EuclideanSpace ℝ (Fin (n + 1))) := ⟨ball x₀ t, isOpen_ball⟩
  have hUΩ : U ≤ Ω := hball
  have hU : MeasurableSet (U : Set (EuclideanSpace ℝ (Fin (n + 1)))) := measurableSet_ball
  have : IsFiniteMeasure (volume.restrict (U : Set (EuclideanSpace ℝ (Fin (n + 1))))) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hgζ := ContDiff.continuous_gradient hζ (by simp)
  obtain ⟨w, hw⟩ := exists_extendByZero_cutoff hUΩ u hζ hζc hts c
  have heq := energyFormH1_extendByZero_cutoff_eq ha hbd hUΩ (hG.mono_exponent hp2) hu hζ hζc
    hts c hw
  have hmean := setIntegral_cutoff_forcing_eq_zero ha hbd hUΩ (hG.mono_exponent hp2) hu hζ hζc
    hts
  set G₁ := (ball x₀ t).indicator fun y =>
    ζ y • G y + (W1p.value u y - c) • toEuclideanCLM (𝕜 := ℝ) (a y) (∇ ζ y)
  set h := (ball x₀ t).indicator fun y =>
    ⟪G y, ∇ ζ y⟫_ℝ - matrixBilinearForm (a y) (∇ ζ y) (W1p.gradient u y)
  have hvc : MemLp (fun x => W1p.value u x - c) p (volume.restrict (ball x₀ t)) :=
    hv.sub (memLp_const c)
  have hG₁le := eLpNorm_indicator_cutoffField_le (p := p) ha hbd hU hζ.continuous hζ1 hgζ
    hgradL hG.aestronglyMeasurable hvc.aestronglyMeasurable
  have hhle := eLpNorm_indicator_cutoffForcing_le (q := q) ha hbd hU hgζ hgradL
    hG.aestronglyMeasurable hg.aestronglyMeasurable
  have hG₁ : MemLp G₁ p volume :=
    hG₁le.trans_lt (ENNReal.add_lt_top.2 ⟨hG.eLpNorm_lt_top,
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top hvc.eLpNorm_lt_top⟩)
  have hh : MemLp h q volume :=
    hhle.trans_lt (ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (hG.mono_exponent hqp).eLpNorm_lt_top,
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hg.mono_exponent hqp).eLpNorm_lt_top⟩)
  obtain ⟨H, hH, hHle, hHφ⟩ := hD hh (ae_of_all _ fun x hx => indicator_of_notMem hx _)
    (by rw [integral_indicator measurableSet_ball]; exact hmean)
  refine ⟨w, G₁ + H, hw, hG₁.add hH, fun φ => ?_, ?_⟩
  · exact (heq φ).trans (setIntegral_inner_add_mul_eq measurableSet_ball hG₁ hh hH φ (hHφ φ))
  · calc eLpNorm (G₁ + H) p volume ≤ eLpNorm G₁ p volume + eLpNorm H p volume :=
          eLpNorm_add_le Fact.out
      _ ≤ _ := add_le_add hG₁le (hHle.trans (by gcongr; exact hhle))

/-- The arithmetic of the step between concentric balls: with `L = c₀ / (t - s)` the gradient
bound of the cutoff, the bound produced by the whole-space estimate is at most
`C ((1 + t / (t - s)) A + t / (t - s) ε X)`. -/
private theorem step_bound_le {CW CD : ℝ≥0} {A At X Y Gq ε ε' : ℝ≥0∞} {c₀ Lam K s t : ℝ}
    (hc₀ : 0 ≤ c₀) (hLam : 0 ≤ Lam) (hK : 0 ≤ K) (hs : 0 < s) (hst : s < t) (hAt : At ≤ A)
    (hεε' : ε * ε' = 1) (hY : Y ≤ ENNReal.ofReal (K * t) * ε * X) (hGq : Gq ≤ At * ε') :
    (CW : ℝ≥0∞) * (At + ENNReal.ofReal (Lam * (c₀ / (t - s))) * Y +
        CD * ENNReal.ofReal t * ε * (ENNReal.ofReal (c₀ / (t - s)) * Gq +
          ENNReal.ofReal (Lam * (c₀ / (t - s))) * X)) ≤
      ((CW * (1 + c₀.toNNReal * CD + ((c₀ * Lam * K).toNNReal +
          CD * (c₀ * Lam).toNNReal)) : ℝ≥0) : ℝ≥0∞) *
        ((1 + ENNReal.ofReal (t / (t - s))) * A + ENNReal.ofReal (t / (t - s)) * ε * X) := by
  set τ := ENNReal.ofReal (t / (t - s))
  have ht : 0 ≤ t := hs.le.trans hst.le
  have e1 : ENNReal.ofReal (Lam * (c₀ / (t - s))) * ENNReal.ofReal (K * t) =
      ENNReal.ofReal (c₀ * Lam * K) * τ := by
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1; field_simp
  have e2 : ENNReal.ofReal t * ENNReal.ofReal (c₀ / (t - s)) = ENNReal.ofReal c₀ * τ := by
    rw [← ENNReal.ofReal_mul ht, ← ENNReal.ofReal_mul (by positivity)]
    congr 1; field_simp
  have e3 : ENNReal.ofReal t * ENNReal.ofReal (Lam * (c₀ / (t - s))) =
      ENNReal.ofReal (c₀ * Lam) * τ := by
    rw [← ENNReal.ofReal_mul ht, ← ENNReal.ofReal_mul (by positivity)]
    congr 1; field_simp
  set S : ℝ≥0∞ := 1 + ENNReal.ofReal c₀ * CD + (ENNReal.ofReal (c₀ * Lam * K) +
    CD * ENNReal.ofReal (c₀ * Lam))
  have hS : ((CW * (1 + c₀.toNNReal * CD + ((c₀ * Lam * K).toNNReal +
      CD * (c₀ * Lam).toNNReal)) : ℝ≥0) : ℝ≥0∞) = CW * S := by
    simp only [S, ENNReal.coe_mul, ENNReal.coe_add, ENNReal.coe_one, ENNReal.ofNNReal_toNNReal]
  rw [hS]
  calc (CW : ℝ≥0∞) * (At + ENNReal.ofReal (Lam * (c₀ / (t - s))) * Y +
        CD * ENNReal.ofReal t * ε * (ENNReal.ofReal (c₀ / (t - s)) * Gq +
          ENNReal.ofReal (Lam * (c₀ / (t - s))) * X))
      ≤ CW * (At + ENNReal.ofReal (Lam * (c₀ / (t - s))) * (ENNReal.ofReal (K * t) * ε * X) +
        CD * ENNReal.ofReal t * ε * (ENNReal.ofReal (c₀ / (t - s)) * (At * ε') +
          ENNReal.ofReal (Lam * (c₀ / (t - s))) * X)) := by gcongr
    _ = CW * (At + (ENNReal.ofReal (Lam * (c₀ / (t - s))) * ENNReal.ofReal (K * t)) * ε * X +
        CD * (ENNReal.ofReal t * ENNReal.ofReal (c₀ / (t - s))) * (ε * ε') * At +
        CD * (ENNReal.ofReal t * ENNReal.ofReal (Lam * (c₀ / (t - s)))) * ε * X) := by ring
    _ = CW * (At + ENNReal.ofReal c₀ * CD * τ * (ε * ε') * At +
        (ENNReal.ofReal (c₀ * Lam * K) + CD * ENNReal.ofReal (c₀ * Lam)) * τ * ε * X) := by
        rw [e1, e2, e3]
        ring
    _ ≤ CW * (S * A + S * τ * A + S * τ * ε * X) := by
        rw [hεε', mul_one]
        have h1 : 1 ≤ S := le_self_add.trans le_self_add
        have h2 : ENNReal.ofReal c₀ * CD ≤ S := le_add_self.trans le_self_add
        have h3 : ENNReal.ofReal (c₀ * Lam * K) + CD * ENNReal.ofReal (c₀ * Lam) ≤ S :=
          le_add_self
        gcongr CW * (?_ + ?_ + ?_)
        · exact hAt.trans (le_mul_of_one_le_left' h1)
        · calc ENNReal.ofReal c₀ * CD * τ * At ≤ S * τ * At := by gcongr
            _ ≤ S * τ * A := by gcongr
        · gcongr
    _ = CW * S * ((1 + τ) * A + τ * ε * X) := by ring

/-- The gradient of the extended cutoff `ζ (u - c)` lies in `Lᵖ` when `u`, `∇u ∈ Lᵖ(B_t)`. -/
private theorem memLp_of_ae_eq_indicator_cutoff {p : ℝ≥0∞}
    {x₀ : EuclideanSpace ℝ (Fin (n + 1))} {t : ℝ} (u : W1p volume Ω 2)
    (hv : MemLp (W1p.value u) p (volume.restrict (ball x₀ t)))
    (hg : MemLp (W1p.gradient u) p (volume.restrict (ball x₀ t)))
    {ζ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hζ : ContDiff ℝ ∞ ζ) (hζ1 : ∀ x, |ζ x| ≤ 1) {L : ℝ}
    (hgrad : ∀ x, ‖∇ ζ x‖ ≤ L) (c : ℝ)
    {g : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    (hw : ∀ᵐ x, g x = (ball x₀ t).indicator
      (fun y => ζ y • W1p.gradient u y + (W1p.value u y - c) • ∇ ζ y) x) :
    MemLp g p volume := by
  have : IsFiniteMeasure (volume.restrict (ball x₀ t)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hfp : MemLp (fun y => ζ y • W1p.gradient u y + (W1p.value u y - c) • ∇ ζ y) p
      (volume.restrict (ball x₀ t)) :=
    ((memLp_top_of_bound hζ.continuous.aestronglyMeasurable 1 (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs]; exact hζ1 x)).smul hg).add
      ((hv.sub (memLp_const _)).smul (memLp_top_of_bound
        (ContDiff.continuous_gradient hζ (by simp)).aestronglyMeasurable _ (ae_of_all _ hgrad)))
  exact ((memLp_indicator_iff_restrict measurableSet_ball.nullMeasurableSet).2 hfp).ae_eq
    (Filter.EventuallyEq.symm hw)

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
    ((hasGradientAt_const x (1 : ℝ)).congr_of_eventuallyEq (Filter.eventually_of_mem
      (isOpen_ball.mem_nhds hxs) fun y hy => hζ1 (ball_subset_closedBall hy))).gradient]
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
  obtain ⟨c₀, hc₀, hcut⟩ :=
    exists_forall_contDiff_cutoff_ball (E := EuclideanSpace ℝ (Fin (n + 1)))
  set d := finrank ℝ (EuclideanSpace ℝ (Fin (n + 1)))
  set K : ℝ := sobolevPoincareConst d δ
  have hK : 0 ≤ K := sobolevPoincareConst_nonneg hδn
  refine ⟨CW * (1 + c₀.toNNReal * CD + ((c₀ * Lam * K).toNNReal + CD * (c₀ * Lam).toNNReal)),
    δ₀, hδ₀,
    fun {a r₀} ha hbd hosc {Ω x₀ R} hRr₀ hball u G hu hv hg hG {s t} hs hst htR => ?_⟩
  have hLam : 0 ≤ Lam := (ContinuousLinearMap.opNorm_nonneg _).trans (hbd 0)
  have ht : 0 < t := hs.trans hst
  -- A cutoff between `B_s` and `B_t`.
  obtain ⟨ζ, hζ, hζc, hζr, hζ1, htsb, hgrad⟩ := hcut x₀ hs.le hst
  have hζabs (x : EuclideanSpace ℝ (Fin (n + 1))) : |ζ x| ≤ 1 := by
    obtain ⟨h0, h1⟩ := hζr (mem_range_self x)
    rwa [abs_of_nonneg h0]
  have hballt : ball x₀ t ⊆ (Ω : Set _) := (ball_subset_ball htR).trans hball
  have hle : volume.restrict (ball x₀ t) ≤ volume.restrict (ball x₀ R) :=
    Measure.restrict_mono (ball_subset_ball htR) le_rfl
  have : IsFiniteMeasure (volume.restrict (ball x₀ t)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hv' := hv.mono_measure hle
  have hg' := hg.mono_measure hle
  have hG' := hG.mono_measure hle
  obtain ⟨w, F, hw, hF, hweq, hFle⟩ := exists_wholeSpace_cutoff ha hbd hp.le hqp
    (hD (x₀ := x₀) ht) hballt u hu
    hv' hg' hG' hζ hζc htsb hζabs hgrad (⨍ y in ball x₀ t, W1p.value u y)
  -- The whole-space estimate applies to `w`, and `∇w = ∇u` on `B_s`.
  have hwp := memLp_of_ae_eq_indicator_cutoff u hv' hg' hζ hζabs hgrad _ hw
  have hw0 : ∀ᵐ x, x ∉ ball x₀ (r₀ / 4) → W1p.gradient w x = 0 := by
    filter_upwards [hw] with x hx hxr
    rw [hx, indicator_of_notMem fun h => hxr (ball_subset_ball (by linarith) h)]
  have hlow := eLpNorm_le_of_ae_eq_indicator_cutoff (p := p) hst.le u hζ1 _ hw
  -- Sobolev–Poincaré for `u` and Hölder's inequality for `G` on `B_t`.
  have hSP := W1p.eLpNorm_value_sub_setAverage_le_of_memLp u hball hp_top hqp hv hg hδ hδn ht
    htR
  have hHol : eLpNorm G q (volume.restrict (ball x₀ t)) ≤
      eLpNorm G p (volume.restrict (ball x₀ t)) * volume (ball x₀ t) ^ δ := by
    have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ hqp hG'.aestronglyMeasurable
    rwa [Measure.restrict_apply_univ, one_div, one_div, hδ] at h
  have hεε' : volume (ball x₀ t) ^ (-δ) * volume (ball x₀ t) ^ δ = 1 := by
    rw [← ENNReal.rpow_add _ _ (measure_ball_pos volume x₀ ht).ne' measure_ball_lt_top.ne,
      neg_add_cancel, ENNReal.rpow_zero]
  calc eLpNorm (W1p.gradient u) p (volume.restrict (ball x₀ s))
      ≤ CW * eLpNorm F p volume := hlow.trans (hW ha hbd hosc x₀ w F hw0 hweq hwp hF)
    _ ≤ _ := (mul_le_mul_right hFle _).trans
        (step_bound_le hc₀ hLam hK hs hst (eLpNorm_mono_measure _ hle) hεε' hSP hHol)

end Step

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
  simp only [ENNReal.toReal_mul, ENNReal.toReal_add h1 h2,
    ENNReal.toReal_add ENNReal.one_ne_top ENNReal.ofReal_ne_top, ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal hτ, ENNReal.toReal_one, ENNReal.coe_toReal]

/-- Returning from real numbers to `ℝ≥0∞`: a bound `A.toReal ≤ C (Γ.toReal + m.toReal^e X.toReal)`
for finite `A`, `Γ`, `X` and finite positive `m` gives `A ≤ C (Γ + m^e X)`. -/
private theorem le_mul_add_rpow_mul_of_toReal_le {A Γ X m : ℝ≥0∞} {C e : ℝ} (hC : 0 ≤ C)
    (hA : A ≠ ⊤) (hΓ : Γ ≠ ⊤) (hX : X ≠ ⊤) (hm0 : m ≠ 0) (hm : m ≠ ⊤)
    (h : A.toReal ≤ C * (Γ.toReal + m.toReal ^ e * X.toReal)) :
    A ≤ C.toNNReal * (Γ + m ^ e * X) := by
  have hR : (C.toNNReal : ℝ≥0∞) * (Γ + m ^ e * X) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.add_ne_top.2 ⟨hΓ, ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_ne_zero hm0 hm) hX⟩)
  refine (ENNReal.toReal_le_toReal hA hR).1 (h.trans_eq ?_)
  simp only [ENNReal.toReal_mul, ENNReal.toReal_add hΓ (ENNReal.mul_ne_top
    (ENNReal.rpow_ne_top_of_ne_zero hm0 hm) hX), ENNReal.toReal_rpow, ENNReal.coe_toReal,
    Real.coe_toNNReal C hC]

/-- Absorption and the return to `ℝ≥0∞` in the interior estimate: if the step estimate between
concentric balls holds for `g` on `B_R`, with the `L^q` norm on the right, then
`‖g‖_{Lᵖ(B_{R/2})} ≤ C (‖G‖_{Lᵖ(B_R)} + |B_R|^(1/p - 1/2) ‖g‖_{L²(B_R)})`. -/
private theorem eLpNorm_ball_half_le_of_step {p q : ℝ≥0∞} (hp : 2 < p) {θ : ℝ} (hθ0 : 0 < θ)
    (hθ1 : θ < 1)
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
    simpa only [measureReal_def] using
      Measure.addHaar_real_ball_half_rpow_le volume x₀ hR (by linarith)
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
theorem exists_eLpNorm_gradient_ball_le_eLpNorm_two_of_setAverage_le {p : ℝ≥0∞} (hp : 2 < p)
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
  have hθI : θ ∈ Icc (0 : ℝ) 1 := ⟨hθ0.le, hθ1.le⟩
  have hpR : 2 < p.toReal :=
    (ENNReal.ofReal_lt_iff_lt_toReal zero_le_two hp_top).1 (by rwa [ENNReal.ofReal_ofNat])
  have hp2 : p.toReal⁻¹ < 2⁻¹ := inv_strictAnti₀ two_pos hpR
  -- The exponent `q` with `1/q = θ/2 + (1 - θ)/p` lies in `[2, p]`.
  set q : ℝ≥0∞ := (ENNReal.ofReal θ * 2⁻¹ + ENNReal.ofReal (1 - θ) * p⁻¹)⁻¹
  have hqinv : q⁻¹ = ENNReal.ofReal θ * 2⁻¹ + ENNReal.ofReal (1 - θ) * p⁻¹ := inv_inv _
  have hqinv' : q⁻¹ = ENNReal.ofReal (1 - θ) * p⁻¹ + ENNReal.ofReal θ * 2⁻¹ := by
    rw [hqinv, add_comm]
  have hq2p : q ∈ Icc 2 p := by
    have h := mem_uIcc_of_inv_eq hθI hqinv'
    rwa [uIcc_of_ge hp.le] at h
  have hq1 : 1 < q := ENNReal.one_lt_two.trans_le hq2p.1
  have : Fact (1 ≤ q) := ⟨hq1.le⟩
  have hqδ : q.toReal⁻¹ - p.toReal⁻¹ = θ * (2⁻¹ - p.toReal⁻¹) := by
    have h := inv_eq_ofReal_of_inv_eq (zero_lt_two.trans hp).ne' two_ne_zero hθI hqinv'
    rw [← ENNReal.toReal_inv q, h, ENNReal.toReal_ofReal (add_nonneg
      (mul_nonneg (by linarith) ENNReal.toReal_nonneg) (mul_nonneg hθ0.le ENNReal.toReal_nonneg))]
    simp only [ENNReal.toReal_inv, ENNReal.toReal_ofNat]
    ring
  have hδ0 : 0 ≤ θ * (2⁻¹ - p.toReal⁻¹) := mul_nonneg hθ0.le (sub_nonneg.2 hp2.le)
  have hδn : θ * (2⁻¹ - p.toReal⁻¹) < (d : ℝ)⁻¹ := by
    have h1 : θ * (2⁻¹ - p.toReal⁻¹) ≤ θ := by
      have : 0 ≤ p.toReal⁻¹ := by positivity
      nlinarith
    exact h1.trans_lt (inv_strictAnti₀ (by positivity) (by linarith))
  obtain ⟨Cs, δ₀, hδ₀, hstep⟩ :=
    exists_eLpNorm_gradient_ball_le_step (n := n) hp hp_top hq1 hq2p.2 hqδ hδn lam Lam
  obtain ⟨C₁, hC₁, habs⟩ := exists_le_mul_add_rpow_mul_of_le hθ0 hθ1.le Cs.coe_nonneg
  refine ⟨(C₁ * 2 ^ d).toNNReal, δ₀, hδ₀,
    fun {a r₀} ha hbd hosc {Ω x₀ R} hR hRr₀ hball u G hu hv hg hG => ?_⟩
  exact eLpNorm_ball_half_le_of_step hp hθ0 hθ1 hqinv hδ0 hC₁ habs hR hg hG
    (fun hs hst htR => hstep ha hbd hosc hRr₀ hball u G hu hv hg hG hs hst htR)

/-! ### The lower-order term in `Lᵖ`, and the estimate on the whole space -/

section WholeSpace

/-- The bookkeeping of the interior estimate: the `Lᵖ` norm of `G` on `B(x₀, R)`, together with
the bounds of `TauCeti.measure_ball_rpow_mul_eLpNorm_restrict_ball_le` on the two `L²` terms of
Caccioppoli's inequality, is at most `(1 + 2^(n+1) (β + α)) (Z + r Y)`. -/
private theorem add_mul_add_le {α β r Y Z : ℝ≥0∞} :
    Z + α * r * (2 ^ (n + 1) * Y) + β * (2 ^ (n + 1) * Z) ≤
      (1 + 2 ^ (n + 1) * (β + α)) * (Z + r * Y) := by
  have e : (1 + 2 ^ (n + 1) * (β + α)) * (Z + r * Y) =
      (Z + α * r * (2 ^ (n + 1) * Y) + β * (2 ^ (n + 1) * Z)) +
        (r * Y + 2 ^ (n + 1) * β * (r * Y) + 2 ^ (n + 1) * α * Z) := by ring
  rw [e]
  exact le_self_add

/-- The three estimates of the interior bound, combined: the local estimate by `Z'` and `V g₂`,
Caccioppoli's inequality `g₂ ≤ α r u₂ + β G₂` in `L²` norms, and Hölder's inequalities
`V u₂ ≤ 2^(n+1) Y`, `V G₂ ≤ 2^(n+1) Z`, give `X ≤ C (Z + r Y)` with
`C = (C₁ + 1) (1 + 2^(n+1) (β + α))`. -/
private theorem le_mul_add_of_le_mul_add_mul {C₁ : ℝ≥0} {α β : ℝ}
    {X Y Z Z' V g₂ u₂ G₂ r : ℝ≥0∞} (hloc : X ≤ C₁ * (Z' + V * g₂)) (hZ : Z' ≤ Z)
    (hL2 : g₂ ≤ ENNReal.ofReal α * r * u₂ + ENNReal.ofReal β * G₂)
    (hHu : V * u₂ ≤ 2 ^ (n + 1) * Y) (hHG : V * G₂ ≤ 2 ^ (n + 1) * Z) :
    X ≤ ((C₁ + 1) * (1 + 2 ^ (n + 1) * (β.toNNReal + α.toNNReal)) : ℝ≥0) * (Z + r * Y) := by
  calc X ≤ C₁ * (Z + V * (ENNReal.ofReal α * r * u₂ + ENNReal.ofReal β * G₂)) := by
        refine hloc.trans ?_
        gcongr
    _ = C₁ * (Z + ENNReal.ofReal α * r * (V * u₂) + ENNReal.ofReal β * (V * G₂)) := by ring
    _ ≤ C₁ * (Z + ENNReal.ofReal α * r * (2 ^ (n + 1) * Y) +
          ENNReal.ofReal β * (2 ^ (n + 1) * Z)) := by gcongr
    _ ≤ (C₁ + 1) *
          ((1 + 2 ^ (n + 1) * (ENNReal.ofReal β + ENNReal.ofReal α)) * (Z + r * Y)) := by
        gcongr
        · exact le_self_add
        · exact add_mul_add_le
    _ = _ := by
        push_cast [ENNReal.ofNNReal_toNNReal]
        ring

/-- A right side of the form `C (Z + R⁻¹ Y)` with `C ≠ 0`, `R > 0` and `Y` or `Z` infinite bounds
everything. -/
private theorem le_mul_add_ofReal_inv_mul_of_eq_top {C : ℝ≥0∞} (hC : C ≠ 0) {R : ℝ} (hR : 0 < R)
    {X Y Z : ℝ≥0∞} (h : Y = ⊤ ∨ Z = ⊤) : X ≤ C * (Z + ENNReal.ofReal R⁻¹ * Y) := by
  rcases h with rfl | rfl
  · rw [ENNReal.mul_top (ENNReal.ofReal_pos.2 (inv_pos.2 hR)).ne', add_top, ENNReal.mul_top hC]
    exact le_top
  · rw [top_add, ENNReal.mul_top hC]
    exact le_top

/-- **The interior `W^{1,p}` estimate for coefficients of small mean oscillation, with the
`Lᵖ` norm of `u` on the right.** Let `2 < p < ∞` and `0 < λ ≤ Λ`. There are constants `C` and
`δ > 0`, depending only on `n`, `p`, `λ` and `Λ`, with the following property. Let `a` be a
measurable coefficient matrix on `ℝ^{n+1}`, bounded by `Λ`, such that on every ball `B` of radius
at most `r₀` some constant matrix `A`, uniformly elliptic with constants `λ, Λ`, has mean
deviation `⨍_B ‖a - A‖ ≤ δ` from `a`. Let `u ∈ H¹(Ω)` solve `-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` weakly in
`Ω`, let `B(x₀, 2R) ⊆ Ω` with `4 R ≤ r₀`, let `a` be uniformly elliptic with constants `λ, Λ` on
`B(x₀, 2R)`, and let `∇u` lie in `Lᵖ(B(x₀, R))`. Then

`‖∇u‖_{Lᵖ(B(x₀, R/2))} ≤ C (‖G‖_{Lᵖ(B(x₀, 2R))} + R⁻¹ ‖u‖_{Lᵖ(B(x₀, 2R))})`.

The membership `∇u ∈ Lᵖ(B(x₀, R))` is an a priori assumption; nothing is assumed of `u` and `G`
beyond the equation, since the right side is infinite unless they lie in `Lᵖ(B(x₀, 2R))`. -/
theorem exists_eLpNorm_gradient_ball_le_eLpNorm_value_of_setAverage_le {p : ℝ≥0∞} (hp : 2 < p)
    (hp_top : p ≠ ⊤) (lam Lam : ℝ) :
    ∃ C : ℝ≥0, ∃ δ : ℝ, 0 < δ ∧
      ∀ {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {r₀ : ℝ},
        AEStronglyMeasurable a volume → (∀ x, ‖matrixBilinearForm (a x)‖ ≤ Lam) →
        (∀ (c : EuclideanSpace ℝ (Fin (n + 1))) (r : ℝ), 0 < r → r ≤ r₀ →
          ∃ A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ,
            UniformlyEllipticOn (ball c r) (fun _ => A) lam Lam ∧
              ⨍ x in ball c r, ‖matrixBilinearForm (a x) - matrixBilinearForm A‖ ≤ δ) →
        ∀ {Ω : Opens (EuclideanSpace ℝ (Fin (n + 1)))} {x₀ : EuclideanSpace ℝ (Fin (n + 1))}
          {R : ℝ}, UniformlyEllipticOn (ball x₀ (2 * R)) a lam Lam →
          4 * R ≤ r₀ → ball x₀ (2 * R) ⊆ (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))) →
        ∀ (u : W1p volume Ω 2)
          (G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))),
          (∀ φ : 𝓓(Ω, ℝ), energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume Ω 2 φ) =
            ∫ x in Ω, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) →
          MemLp (W1p.gradient u) p (volume.restrict (ball x₀ R)) →
          eLpNorm (W1p.gradient u) p (volume.restrict (ball x₀ (R / 2))) ≤
            C * (eLpNorm G p (volume.restrict (ball x₀ (2 * R))) + ENNReal.ofReal R⁻¹ *
              eLpNorm (W1p.value u) p (volume.restrict (ball x₀ (2 * R)))) := by
  obtain ⟨C₁, δ, hδ, h₁⟩ := exists_eLpNorm_gradient_ball_le_eLpNorm_two_of_setAverage_le hp hp_top
    lam Lam
  obtain ⟨α, β, h₂⟩ := exists_eLpNorm_gradient_ball_le_of_forall_testFunction (ι := Fin (n + 1))
    lam Lam
  refine ⟨(C₁ + 1) * (1 + 2 ^ (n + 1) * (β.toNNReal + α.toNNReal)), δ, hδ,
    fun {a r₀} ham hbd hosc {Ω x₀ R} hell hRr hball u G hu hgrad => ?_⟩
  rcases le_or_gt R 0 with hR | hR
  · rw [ball_eq_empty.2 (by linarith), Measure.restrict_empty, eLpNorm_measure_zero]
    exact zero_le
  have hsub : ball x₀ R ⊆ ball x₀ (2 * R) := ball_subset_ball (by linarith)
  have hval₂ : AEStronglyMeasurable (W1p.value u) (volume.restrict (ball x₀ (2 * R))) :=
    (Lp.aestronglyMeasurable _).mono_measure (Measure.restrict_mono hball le_rfl)
  set Y := eLpNorm (W1p.value u) p (volume.restrict (ball x₀ (2 * R)))
  set Z := eLpNorm G p (volume.restrict (ball x₀ (2 * R)))
  set r := ENNReal.ofReal R⁻¹
  -- Data outside `Lᵖ(B(x₀, 2R))` make the right side infinite.
  by_cases hfin : Y ≠ ⊤ ∧ Z ≠ ⊤
  swap
  · exact le_mul_add_ofReal_inv_mul_of_eq_top (by positivity) hR (by
      rwa [not_and_or, not_ne_iff, not_ne_iff] at hfin)
  have hG : MemLp G p (volume.restrict (ball x₀ (2 * R))) :=
    memLp_iff.2 (lt_top_iff_ne_top.2 hfin.2)
  have : IsFiniteMeasure (volume.restrict (ball x₀ (2 * R))) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hloc := h₁ ham hbd hosc hR hRr (hsub.trans hball) u G hu
    (memLp_iff.2 ((eLpNorm_mono_measure _ (Measure.restrict_mono hsub le_rfl)).trans_lt
      (lt_top_iff_ne_top.2 hfin.1))) hgrad (hG.mono_measure (Measure.restrict_mono hsub le_rfl))
  have hL2 := h₂ hell (ham.mono_measure Measure.restrict_le_self) (hG.mono_exponent hp.le) hu
    (show R < 2 * R by linarith) hball
  rw [show 2 * R - R = R by ring] at hL2
  have hHu := measure_ball_rpow_mul_eLpNorm_restrict_ball_le one_le_two hp.le one_le_two hR hval₂
  have hHG := measure_ball_rpow_mul_eLpNorm_restrict_ball_le one_le_two hp.le one_le_two hR
    hG.aestronglyMeasurable
  simp only [ENNReal.toReal_ofNat, ENNReal.ofReal_ofNat, finrank_euclideanSpace_fin] at hHu hHG
  exact le_mul_add_of_le_mul_add_mul hloc
    (eLpNorm_mono_measure _ (Measure.restrict_mono hsub le_rfl)) hL2 hHu hHG

/-- **The `W^{1,p}` estimate on `ℝ^{n+1}` for coefficients of small mean oscillation below a
radius.** Let `2 < p < ∞` and `0 < λ ≤ Λ`. There are constants `C` and `δ > 0`, depending only on
`n`, `p`, `λ` and `Λ`, with the following property. Let `a` be a measurable coefficient matrix on
`ℝ^{n+1}`, uniformly elliptic with constants `λ, Λ`, such that on every ball `B` of radius at most
`r₀ > 0` some constant matrix `A`, uniformly elliptic with the same constants, has mean deviation
`⨍_B ‖a - A‖ ≤ δ` from `a`. Then every `u ∈ H¹(ℝ^{n+1})` solving `-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` weakly,
with `∇u ∈ Lᵖ`, satisfies

`‖∇u‖_{Lᵖ} ≤ C (‖G‖_{Lᵖ} + r₀⁻¹ ‖u‖_{Lᵖ})`.

Coefficients of vanishing mean oscillation satisfy the hypothesis for every `δ > 0` with some
radius `r₀`, and the term `r₀⁻¹ ‖u‖_{Lᵖ}` records that radius; when the hypothesis holds at every
scale it can be dropped, as in
`TauCeti.PDE.exists_eLpNorm_gradient_le_of_forall_energyFormH1_eq_of_setAverage_le`. The
membership `∇u ∈ Lᵖ` is an a priori assumption. -/
theorem exists_eLpNorm_gradient_le_eLpNorm_value_of_setAverage_le {p : ℝ≥0∞} (hp : 2 < p)
    (hp_top : p ≠ ⊤) (lam Lam : ℝ) :
    ∃ C : ℝ≥0, ∃ δ : ℝ, 0 < δ ∧
      ∀ {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {r₀ : ℝ},
        0 < r₀ → AEStronglyMeasurable a volume → UniformlyEllipticOn univ a lam Lam →
        (∀ (c : EuclideanSpace ℝ (Fin (n + 1))) (r : ℝ), 0 < r → r ≤ r₀ →
          ∃ A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ,
            UniformlyEllipticOn (ball c r) (fun _ => A) lam Lam ∧
              ⨍ x in ball c r, ‖matrixBilinearForm (a x) - matrixBilinearForm A‖ ≤ δ) →
        ∀ (u : W1p volume (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) 2)
          (G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))),
          (∀ φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))), ℝ),
            energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume ⊤ 2 φ) =
              ∫ x, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) →
          MemLp (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
            p volume →
          eLpNorm (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) →
            EuclideanSpace ℝ (Fin (n + 1))) p volume ≤
            C * (eLpNorm G p volume + ENNReal.ofReal r₀⁻¹ *
              eLpNorm (W1p.value u : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) p volume) := by
  have hp1 : 1 ≤ p := one_le_two.trans hp.le
  obtain ⟨C, δ, hδ, h⟩ :=
    exists_eLpNorm_gradient_ball_le_eLpNorm_value_of_setAverage_le (n := n) hp hp_top lam Lam
  refine ⟨2 * 4 ^ (n + 1) * (4 * (C + 1)), δ, hδ,
    fun {a r₀} hr₀ ham hell hosc u G hu hgrad => ?_⟩
  -- A forcing outside `Lᵖ` makes the right side infinite.
  rcases eq_or_ne (eLpNorm G p volume) ⊤ with hGtop | hGfin
  · exact le_mul_add_ofReal_inv_mul_of_eq_top (by positivity) hr₀ (Or.inr hGtop)
  have hG : AEStronglyMeasurable G volume := (memLp_iff.2 hGfin.lt_top).aestronglyMeasurable
  set R := r₀ / 4 with hR_def
  have hR : 0 < R := by positivity
  have hval : AEStronglyMeasurable (W1p.value u : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) volume := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using Lp.aestronglyMeasurable (W1p.value u)
  set c : ℝ := 4 * ((C + 1 : ℝ≥0) : ℝ) with hc_def
  have hc0 : 0 ≤ c := by positivity
  have hC : (C : ℝ≥0∞) ≤ ENNReal.ofReal c := by
    rw [hc_def, ENNReal.ofReal_mul zero_le_four, ENNReal.ofReal_ofNat, ENNReal.ofReal_coe_nnreal]
    exact (ENNReal.coe_le_coe.2 le_self_add).trans (le_mul_of_one_le_left' (by norm_num))
  have hcR : ENNReal.ofReal (c * r₀⁻¹) = (C + 1 : ℝ≥0) * ENNReal.ofReal R⁻¹ := by
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul NNReal.zero_le_coe, hc_def, hR_def,
      inv_div]
    congr 1
    ring
  -- The interior estimate on `B(y, R/2)`, at every centre `y`.
  have hlocal : ∀ y, eLpNorm (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) →
      EuclideanSpace ℝ (Fin (n + 1))) p (volume.restrict (ball y (R / 2))) ≤
      ENNReal.ofReal c * eLpNorm G p (volume.restrict (ball y (4 * (R / 2)))) +
        ENNReal.ofReal (c * r₀⁻¹) * eLpNorm (W1p.value u : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) p
          (volume.restrict (ball y (4 * (R / 2)))) := fun y => by
    rw [show 4 * (R / 2) = 2 * R by ring, hcR, mul_assoc]
    refine (h ham (fun x => hell.opNorm_matrixBilinearForm_le (mem_univ x)) hosc (Ω := ⊤)
      (x₀ := y) (R := R) (hell.mono_set (subset_univ _)) (by rw [hR_def]; linarith)
      (subset_univ _) u G (fun φ => by rw [hu φ, Opens.coe_top, Measure.restrict_univ])
      (hgrad.restrict _)).trans ?_
    rw [mul_add]
    gcongr
    exact le_self_add
  -- Average the interior estimates over all centres.
  refine (eLpNorm_le_of_ae_eLpNorm_restrict_ball_le_add hp1 hp_top hgrad.aestronglyMeasurable hG
    hval (by norm_num) (half_pos hR) (Eventually.of_forall hlocal)).trans_eq ?_
  rw [ENNReal.ofReal_mul hc0, mul_assoc (ENNReal.ofReal c), ← mul_add, ← mul_assoc]
  congr 1
  simp [hc_def, ENNReal.ofReal_mul, ENNReal.ofReal_add]

end WholeSpace

end PDE

end TauCeti
