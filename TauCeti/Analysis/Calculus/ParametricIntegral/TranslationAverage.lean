/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Averages of translates of a function against a measure

Let `ν` be a finite measure on a parameter space `P`, let `A : P → F →L[ℝ] G` be a measurable
family of continuous linear maps with `‖A p‖ ≤ c` for almost every `p`, and let `s : P → E` be a
measurable family of displacements in a real normed space `E`. For a function `φ : E → F` the
**translation average**

`x ↦ ∫ A p (φ (x + s p)) dν(p)`

(`TauCeti.translationAverage`) averages the translates of `φ` by the vectors `s p`, weighted by the
operators `A p`. When `φ` is smooth with bounded derivatives, so is its translation average, and
derivatives pass under the integral:

`D^i (x ↦ ∫ A p (φ (x + s p)) dν) = x ↦ ∫ A p ∘ D^i φ (x + s p) dν`,

with the `i`-th derivatives bounded by `c ν(P)` times those of `φ`. If the displacements are
`ν`-almost everywhere at most `r` in norm, the average of `φ` is supported in
`supp φ + closedBall 0 r`. The induced operator on test functions is
`TestFunction.translationAverageCLM`
(`TauCeti.Analysis.Distribution.TestFunction.TranslateAverage.Basic`).

## Main declarations

* `TauCeti.translationAverage`: the translation average of a function.
* `TauCeti.contDiff_translationAverage`, `TauCeti.iteratedFDeriv_translationAverage`,
  `TauCeti.hasFDerivAt_translationAverage`: smoothness, and derivatives under the integral.
* `TauCeti.norm_translationAverage_le`, `TauCeti.norm_iteratedFDeriv_translationAverage_le`: the
  sup bounds for the translation average and its derivatives.
* `TauCeti.support_translationAverage_subset`, `TauCeti.tsupport_translationAverage_subset`: the
  support bounds.

## Implementation notes

The family `A` is assumed almost everywhere strongly measurable and almost everywhere bounded,
rather than Bochner integrable. For the operator families used for test forms, such as the
interior products `f ↦ f.curryLeft v` between spaces of continuous alternating maps,
`Integrable A ν` does not elaborate: Lean finds no `ContinuousENorm` instance on a space of
continuous linear maps whose domain or codomain is itself a space of continuous linear or
alternating maps. Measurability and a bound on `‖A p‖` need no such instance. The norm of `A p` is
never integrated, only bounded.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §1.3 and §4.1
  (regularization by convolution with test functions and with measures).
-/

public section

noncomputable section

open MeasureTheory Metric Set Filter
open scoped Pointwise ContDiff

namespace TauCeti

variable {E F G P : Type*} [NormedAddCommGroup E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [MeasurableSpace P] {ν : Measure P} {A : P → F →L[ℝ] G} {s : P → E} {φ : E → F} {c : ℝ}

/-- The **translation average** `x ↦ ∫ A p (φ (x + s p)) dν(p)` of `φ : E → F`: the average of the
translates of `φ` by the displacements `s p`, weighted by the operators `A p`, against the measure
`ν`. -/
def translationAverage (ν : Measure P) (A : P → F →L[ℝ] G) (s : P → E) (φ : E → F) (x : E) : G :=
  ∫ p, A p (φ (x + s p)) ∂ν

theorem translationAverage_apply (ν : Measure P) (A : P → F →L[ℝ] G) (s : P → E) (φ : E → F)
    (x : E) : translationAverage ν A s φ x = ∫ p, A p (φ (x + s p)) ∂ν :=
  (rfl)

/-- The translation average vanishes at `x` when `φ` vanishes at almost every displaced point
`x + s p`. -/
theorem translationAverage_eq_zero_of_ae {x : E} (h : ∀ᵐ p ∂ν, φ (x + s p) = 0) :
    translationAverage ν A s φ x = 0 :=
  integral_eq_zero_of_ae (h.mono fun p hp ↦ by simp [hp])

/-- **Support of a translation average**: if the displacements are almost everywhere at most `r`
in norm, the translation average of `φ` is supported in `support φ + closedBall 0 r`. -/
theorem support_translationAverage_subset {r : ℝ} (hsr : ∀ᵐ p ∂ν, s p ∈ closedBall (0 : E) r) :
    Function.support (translationAverage ν A s φ) ⊆ Function.support φ + closedBall (0 : E) r := by
  intro x hx
  by_contra hxr
  refine hx (translationAverage_eq_zero_of_ae (hsr.mono fun p hp ↦ ?_))
  by_contra hφ
  exact hxr ⟨x + s p, hφ, -s p, by simpa using hp, add_neg_cancel_right x (s p)⟩

/-- **Topological support of a translation average**: if `φ` has compact support and the
displacements are almost everywhere at most `r` in norm, the translation average of `φ` is
supported in `tsupport φ + closedBall 0 r`. -/
theorem tsupport_translationAverage_subset [ProperSpace E] {r : ℝ} (hφ : HasCompactSupport φ)
    (hsr : ∀ᵐ p ∂ν, s p ∈ closedBall (0 : E) r) :
    tsupport (translationAverage ν A s φ) ⊆ tsupport φ + closedBall (0 : E) r :=
  closure_minimal ((support_translationAverage_subset hsr).trans
    (add_subset_add_right (subset_tsupport _)))
    (hφ.isCompact.add (isCompact_closedBall 0 r)).isClosed

/-- The translation average commutes with real scalar multiplication. -/
theorem translationAverage_smul (c : ℝ) (φ : E → F) :
    translationAverage ν A s (c • φ) = c • translationAverage ν A s φ := by
  ext x
  simp only [translationAverage_apply, Pi.smul_apply, map_smul, integral_smul]

/-- Bounds `‖L‖ ≤ c` on an operator and `‖g‖ ≤ C` on its argument bound `‖L‖ ‖g‖` by `c C`. -/
private theorem norm_mul_norm_le {H K : Type*} [SeminormedAddCommGroup H]
    [SeminormedAddCommGroup K] {L : H} {g : K} {C : ℝ} (hL : ‖L‖ ≤ c) (hg : ‖g‖ ≤ C) :
    ‖L‖ * ‖g‖ ≤ c * C :=
  mul_le_mul hL hg (norm_nonneg _) ((norm_nonneg _).trans hL)

/-- `‖A p v‖ ≤ c C` for almost every `p` when `‖A p‖ ≤ c` almost everywhere and `‖v‖ ≤ C`. -/
private theorem ae_norm_apply_le (hAc : ∀ᵐ p ∂ν, ‖A p‖ ≤ c) {C : ℝ} {v : P → F}
    (hv : ∀ p, ‖v p‖ ≤ C) : ∀ᵐ p ∂ν, ‖A p (v p)‖ ≤ c * C :=
  hAc.mono fun p hp ↦ (ContinuousLinearMap.le_opNorm _ _).trans (norm_mul_norm_le hp (hv p))

variable [IsFiniteMeasure ν]

/-- The sup bound for a translation average: if `‖A p‖ ≤ c` almost everywhere and `‖φ‖ ≤ C`, then
the translation average of `φ` is at most `c C ν(P)`. -/
theorem norm_translationAverage_le (hAc : ∀ᵐ p ∂ν, ‖A p‖ ≤ c) {C : ℝ} (hC : ∀ x, ‖φ x‖ ≤ C)
    (x : E) : ‖translationAverage ν A s φ x‖ ≤ c * C * ν.real univ :=
  norm_integral_le_of_norm_le_const (ae_norm_apply_le hAc fun _ ↦ hC _)

/-- The integrand `p ↦ A p (φ (x + s p))` of a translation average of a bounded continuous
function is integrable. -/
theorem integrable_translationAverage_integrand (hA : AEStronglyMeasurable A ν)
    (hAc : ∀ᵐ p ∂ν, ‖A p‖ ≤ c) (hs : AEStronglyMeasurable s ν) (hφ : Continuous φ) {C : ℝ}
    (hC : ∀ x, ‖φ x‖ ≤ C) (x : E) : Integrable (fun p ↦ A p (φ (x + s p))) ν :=
  Integrable.mono' (integrable_const (c * C))
    ((continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (hA.prodMk ((hφ.comp (continuous_const.add continuous_id)).comp_aestronglyMeasurable hs)))
    (ae_norm_apply_le hAc fun _ ↦ hC _)

/-- The integrand `p ↦ A p ∘ g (x + s p)` is integrable for a bounded continuous family `g` of
operators, such as the derivative of a function with bounded derivative. -/
theorem integrable_comp_comp_add {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (hA : AEStronglyMeasurable A ν) (hAc : ∀ᵐ p ∂ν, ‖A p‖ ≤ c) (hs : AEStronglyMeasurable s ν)
    {g : E → H →L[ℝ] F} (hg : Continuous g) {C : ℝ} (hC : ∀ x, ‖g x‖ ≤ C) (x : E) :
    Integrable (fun p ↦ (A p).comp (g (x + s p))) ν :=
  Integrable.mono' (integrable_const (c * C))
    ((ContinuousLinearMap.compL ℝ H F G).continuous₂.comp_aestronglyMeasurable₂ hA
      ((hg.comp (continuous_const.add continuous_id)).comp_aestronglyMeasurable hs))
    (hAc.mono fun _ hp ↦ (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (norm_mul_norm_le hp (hC _)))

/-- The translation average is additive on bounded continuous functions. -/
theorem translationAverage_add (hA : AEStronglyMeasurable A ν) (hAc : ∀ᵐ p ∂ν, ‖A p‖ ≤ c)
    (hs : AEStronglyMeasurable s ν)
    {φ ψ : E → F} (hφ : Continuous φ) (hψ : Continuous ψ) {C D : ℝ} (hC : ∀ x, ‖φ x‖ ≤ C)
    (hD : ∀ x, ‖ψ x‖ ≤ D) :
    translationAverage ν A s (φ + ψ) = translationAverage ν A s φ + translationAverage ν A s ψ := by
  ext x
  simp only [translationAverage_apply, Pi.add_apply, map_add]
  exact integral_add (integrable_translationAverage_integrand hA hAc hs hφ hC x)
    (integrable_translationAverage_integrand hA hAc hs hψ hD x)

variable [NormedSpace ℝ E]

omit [IsFiniteMeasure ν] in
/-- Measurability in the parameter of `A p` applied to a continuous function of the displaced
point `x + s p`. -/
private theorem aestronglyMeasurable_compContinuousMultilinearMap {i : ℕ}
    {g : E → E [×i]→L[ℝ] F} (hg : Continuous g) (hA : AEStronglyMeasurable A ν)
    (hs : AEStronglyMeasurable s ν) (x : E) :
    AEStronglyMeasurable (fun p ↦ (A p).compContinuousMultilinearMap (g (x + s p))) ν :=
  (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin i ↦ E) F G).continuous₂
    |>.comp_aestronglyMeasurable₂ hA
      ((hg.comp (continuous_const.add continuous_id)).comp_aestronglyMeasurable hs)

/-- **Derivatives of a translation average.** If `φ` is smooth with bounded derivatives of every
order and `A` is measurable and almost everywhere bounded, the translation average of `φ` has the
Taylor series obtained by differentiating under the integral sign. -/
theorem hasFTaylorSeriesUpTo_translationAverage (hφ : ContDiff ℝ ∞ φ)
    (hφb : ∀ i : ℕ, ∃ C, ∀ x, ‖iteratedFDeriv ℝ i φ x‖ ≤ C) (hA : AEStronglyMeasurable A ν)
    (hAc : ∀ᵐ p ∂ν, ‖A p‖ ≤ c) (hs : AEStronglyMeasurable s ν) :
    HasFTaylorSeriesUpTo ∞ (translationAverage ν A s φ) fun x ↦ (fun i ↦
      ∫ p, (A p).compContinuousMultilinearMap (iteratedFDeriv ℝ i φ (x + s p)) ∂ν :
        FormalMultilinearSeries ℝ E G) := by
  choose C hC using hφb
  refine hasFTaylorSeriesUpToOn_univ_iff.1 <|
    hasFTaylorSeriesUpToOn_integral_of_le_bound isOpen_univ
    (bound := fun i _ ↦ c * C i) (fun x _ i _ ↦
      aestronglyMeasurable_compContinuousMultilinearMap
        (hφ.continuous_iteratedFDeriv (mod_cast le_top)) hA hs x)
    (hAc.mono fun p hp x _ i _ ↦ ?_) (fun i _ ↦ integrable_const _) (ae_of_all _ fun p ↦ ?_)
  · exact (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans
      (norm_mul_norm_le hp (hC i _))
  · have hφs : ContDiff ℝ ∞ fun y ↦ φ (y + s p) := hφ.comp (contDiff_id.add contDiff_const)
    refine (((A p).contDiff.comp hφs).ftaylorSeries.hasFTaylorSeriesUpToOn univ).congr_series
      fun i _ x _ ↦ ?_
    -- The Taylor coefficients of the translate are the translated ones, composed with `A p`.
    exact ((A p).iteratedFDeriv_comp_left hφs.contDiffAt (mod_cast le_top)).trans
      (by rw [iteratedFDeriv_comp_add_right])

/-- **Smoothness of a translation average** of a smooth function with bounded derivatives. -/
theorem contDiff_translationAverage (hφ : ContDiff ℝ ∞ φ)
    (hφb : ∀ i : ℕ, ∃ C, ∀ x, ‖iteratedFDeriv ℝ i φ x‖ ≤ C) (hA : AEStronglyMeasurable A ν)
    (hAc : ∀ᵐ p ∂ν, ‖A p‖ ≤ c) (hs : AEStronglyMeasurable s ν) :
    ContDiff ℝ ∞ (translationAverage ν A s φ) :=
  (hasFTaylorSeriesUpTo_translationAverage hφ hφb hA hAc hs).contDiff

/-- **Derivatives commute with a translation average**:
`D^i (x ↦ ∫ A p (φ (x + s p)) dν) = x ↦ ∫ A p ∘ D^i φ (x + s p) dν`. -/
theorem iteratedFDeriv_translationAverage (hφ : ContDiff ℝ ∞ φ)
    (hφb : ∀ i : ℕ, ∃ C, ∀ x, ‖iteratedFDeriv ℝ i φ x‖ ≤ C) (hA : AEStronglyMeasurable A ν)
    (hAc : ∀ᵐ p ∂ν, ‖A p‖ ≤ c) (hs : AEStronglyMeasurable s ν) (i : ℕ) (x : E) :
    iteratedFDeriv ℝ i (translationAverage ν A s φ) x =
      ∫ p, (A p).compContinuousMultilinearMap (iteratedFDeriv ℝ i φ (x + s p)) ∂ν := by
  rw [← iteratedFDerivWithin_univ]
  have h := hasFTaylorSeriesUpToOn_univ_iff.2
    (hasFTaylorSeriesUpTo_translationAverage hφ hφb hA hAc hs)
  exact (h.eq_iteratedFDerivWithin_of_uniqueDiffOn (mod_cast le_top) uniqueDiffOn_univ
    (mem_univ x)).symm

/-- **Bounds on the derivatives of a translation average**: if `‖A p‖ ≤ c` almost everywhere and
`‖D^i φ‖ ≤ C`, then the `i`-th derivative of the translation average of `φ` is at most
`c C ν(P)`. -/
theorem norm_iteratedFDeriv_translationAverage_le (hφ : ContDiff ℝ ∞ φ)
    (hφb : ∀ i : ℕ, ∃ C, ∀ x, ‖iteratedFDeriv ℝ i φ x‖ ≤ C) (hA : AEStronglyMeasurable A ν)
    (hAc : ∀ᵐ p ∂ν, ‖A p‖ ≤ c) (hs : AEStronglyMeasurable s ν) {i : ℕ} {C : ℝ}
    (hC : ∀ x, ‖iteratedFDeriv ℝ i φ x‖ ≤ C) (x : E) :
    ‖iteratedFDeriv ℝ i (translationAverage ν A s φ) x‖ ≤ c * C * ν.real univ := by
  rw [iteratedFDeriv_translationAverage hφ hφb hA hAc hs]
  exact norm_integral_le_of_norm_le_const (hAc.mono fun p hp ↦
    (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans
      (norm_mul_norm_le hp (hC _)))

/-- **The derivative of a translation average** is the translation average of the derivative:
`D (x ↦ ∫ A p (φ (x + s p)) dν) = x ↦ ∫ A p ∘ Dφ (x + s p) dν`. -/
theorem hasFDerivAt_translationAverage (hφ : ContDiff ℝ ∞ φ)
    (hφb : ∀ i : ℕ, ∃ C, ∀ x, ‖iteratedFDeriv ℝ i φ x‖ ≤ C) (hA : AEStronglyMeasurable A ν)
    (hAc : ∀ᵐ p ∂ν, ‖A p‖ ≤ c) (hs : AEStronglyMeasurable s ν) (x : E) :
    HasFDerivAt (translationAverage ν A s φ)
      (∫ p, (A p).comp (fderiv ℝ φ (x + s p)) ∂ν) x := by
  obtain ⟨C₀, hC₀⟩ := hφb 0
  obtain ⟨C, hC⟩ := hφb 1
  have hφ₀ (y : E) : ‖φ y‖ ≤ C₀ := by simpa using hC₀ y
  have hφ₁ (y : E) : ‖fderiv ℝ φ y‖ ≤ C := by simpa [norm_iteratedFDeriv_one] using hC y
  have hφ' : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by simp)
  unfold translationAverage
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ)
    (F' := fun y p ↦ (A p).comp (fderiv ℝ φ (y + s p))) (bound := fun _ ↦ c * C) univ_mem
    (Eventually.of_forall fun y ↦
      (integrable_translationAverage_integrand hA hAc hs hφ.continuous hφ₀ y).aestronglyMeasurable)
    (integrable_translationAverage_integrand hA hAc hs hφ.continuous hφ₀ x)
    (integrable_comp_comp_add hA hAc hs hφ' hφ₁ x).aestronglyMeasurable
    (hAc.mono fun p hp y _ ↦ (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (norm_mul_norm_le hp (hφ₁ _)))
    (integrable_const _) (ae_of_all _ fun p y _ ↦ ?_)
  exact (A p).hasFDerivAt.comp y
    (((hφ.differentiable (by simp)) _).hasFDerivAt.comp y ((hasFDerivAt_id y).add_const _))

end TauCeti
