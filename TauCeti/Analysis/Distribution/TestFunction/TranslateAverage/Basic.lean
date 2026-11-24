/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Distribution.TestFunction

/-!
# Averages of translates of test functions against a measure

Let `ν` be a finite measure on a parameter space `P`, let `A : P → F →L[ℝ] G` be a measurable
family of continuous linear maps with `‖A p‖ ≤ c` for almost every `p`, and let `s : P → E` be a
measurable family of displacements in a real normed space `E`. For a function `φ : E → F` the
**translation average**

`x ↦ ∫ A p (φ (x + s p)) dν(p)`

(`TauCeti.translationAverage`) averages the translates of `φ` by the vectors `s p`, weighted by the
operators `A p`. When `φ` is smooth with bounded derivatives, so is its translation average, and
derivatives pass under the integral:

`D^i (x ↦ ∫ A p (φ (x + s p)) dν) = x ↦ ∫ A p ∘ D^i φ (x + s p) dν`.

If the displacements are `ν`-almost everywhere at most `r` in norm, the average of `φ` is supported
in `supp φ + closedBall 0 r`. So the translation average maps test functions on an open set `U` to
test functions on any open set `Ω ⊇ U + closedBall 0 r`, continuously for the LF topologies
(`TestFunction.translationAverageCLM`): its `i`-th derivatives are bounded by `c ν(P)` times
those of `φ`.

Two cases are the operators used to regularize currents: with `A p = id` and `s` the identity of
`E`, the translation average is the mean `x ↦ ∫ φ (x + v) dν(v)` of the translates of `φ` against a
measure `ν` on `E`, which for `ν` given by a smooth density is the convolution of `φ` with the
reflected density; and with `A (v, t)` the interior product with `v` and `s (v, t) = t v`, it is the
averaged homotopy operator between such a mean and the identity
(`TauCeti.Analysis.Distribution.TestFunction.TranslateAverage.Homotopy`).

## Main declarations

* `TauCeti.translationAverage`: the translation average of a function.
* `TauCeti.contDiff_translationAverage`, `TauCeti.iteratedFDeriv_translationAverage`,
  `TauCeti.hasFDerivAt_translationAverage`: smoothness, and derivatives under the integral.
* `TauCeti.norm_translationAverage_le`, `TauCeti.norm_iteratedFDeriv_translationAverage_le`: the
  sup bounds for the translation average and its derivatives.
* `TauCeti.support_translationAverage_subset`: the support bound.
* `TestFunction.translationAverageCLM`: the translation average as a continuous linear map of test
  functions, with values `TestFunction.translationAverageCLM_apply` and
  `TestFunction.coe_translationAverageCLM`, and derivative
  `TestFunction.hasFDerivAt_translationAverageCLM`.

## Implementation notes

The family `A` is assumed almost everywhere strongly measurable and almost everywhere bounded,
rather than Bochner integrable. For the operator families used here, such as the interior products
`f ↦ f.curryLeft v` between spaces of continuous alternating maps, `Integrable A ν` does not
elaborate: Lean finds no `ContinuousENorm` instance on a space of continuous linear maps whose
domain or codomain is itself a space of continuous linear or alternating maps. Measurability and a
bound on `‖A p‖` need no such instance. The norm of `A p` is never integrated, only bounded.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §1.3 and §4.1
  (regularization by convolution with test functions and with measures).
-/

public section

noncomputable section

open MeasureTheory Metric Set TopologicalSpace Filter
open scoped Pointwise Distributions ContDiff

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

namespace TestFunction

open TauCeti

variable {E F G P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [MeasurableSpace P] {ν : Measure P} [IsFiniteMeasure ν] {A : P → F →L[ℝ] G} {s : P → E}
  {c r : ℝ} {U Ω : Opens E}

/-- The compact set `K + closedBall 0 r`, which contains the supports of the translation averages
of the functions supported in `K` when the displacements are at most `r`. -/
private def thickening (K : Compacts E) (r : ℝ) : Compacts E :=
  ⟨(K : Set E) + closedBall 0 r, K.isCompact.add (isCompact_closedBall 0 r)⟩

private theorem coe_thickening (K : Compacts E) (r : ℝ) :
    (thickening K r : Set E) = (K : Set E) + closedBall 0 r :=
  (rfl)

omit [FiniteDimensional ℝ E] in
/-- A smooth function with compact support has bounded derivatives of every order. -/
private theorem forall_exists_norm_iteratedFDeriv_le {φ : E → F} (h : HasCompactSupport φ)
    (hφ : ContDiff ℝ ∞ φ) (i : ℕ) : ∃ C, ∀ x, ‖iteratedFDeriv ℝ i φ x‖ ≤ C :=
  (h.exists_bound_iteratedFDeriv hφ i).imp fun _ hC ↦ hC.2 i le_rfl

variable (hA : AEStronglyMeasurable A ν) (hAc : ∀ᵐ p ∂ν, ‖A p‖ ≤ c)
  (hs : AEStronglyMeasurable s ν) (hsr : ∀ᵐ p ∂ν, s p ∈ closedBall (0 : E) r)

include hA hAc hs hsr in
/-- The translation average on smooth functions supported in a compact `K`, with values supported
in `K + closedBall 0 r`. -/
private def translationAverageSupportedInCLM (K : Compacts E) :
    𝓓_{K}(E, F) →L[ℝ] 𝓓_{thickening K r}(E, G) :=
  letI L : 𝓓_{K}(E, F) →ₗ[ℝ] 𝓓_{thickening K r}(E, G) :=
    { toFun f := ⟨translationAverage ν A s f,
        contDiff_translationAverage f.contDiff
          (forall_exists_norm_iteratedFDeriv_le f.hasCompactSupport f.contDiff) hA hAc hs,
        fun x hx ↦ Function.notMem_support.1 fun h ↦ hx <| by
          rw [coe_thickening]
          exact add_subset_add_right f.support_subset (support_translationAverage_subset hsr h)⟩
      map_add' f g := ContDiffMapSupportedIn.ext fun x ↦ by
        obtain ⟨C, hC⟩ := forall_exists_norm_iteratedFDeriv_le f.hasCompactSupport f.contDiff 0
        obtain ⟨D, hD⟩ := forall_exists_norm_iteratedFDeriv_le g.hasCompactSupport g.contDiff 0
        exact congrFun (translationAverage_add hA hAc hs f.continuous g.continuous
          (fun y ↦ by simpa using hC y) (fun y ↦ by simpa using hD y)) x
      map_smul' c f := ContDiffMapSupportedIn.ext fun x ↦
        congrFun (translationAverage_smul c (f : E → F)) x }
  { toLinearMap := L
    cont := by
      -- Each seminorm of the image is bounded by `|c| ν(P)` times the seminorm of the same order.
      refine WithSeminorms.continuous_of_isBounded (ContDiffMapSupportedIn.withSeminorms ..)
        (ContDiffMapSupportedIn.withSeminorms ..) _ (.of_real fun i ↦ ?_)
      refine ⟨{i}, |c| * ν.real univ, fun f ↦ ((L f).seminorm_le_iff ℝ
        (by positivity) i).2 fun _ x _ ↦ ?_⟩
      refine (norm_iteratedFDeriv_translationAverage_le f.contDiff
        (forall_exists_norm_iteratedFDeriv_le f.hasCompactSupport f.contDiff) hA hAc hs
        (fun y ↦ ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℝ) x).trans ?_
      rw [Finset.sup_singleton, mul_right_comm]
      gcongr
      exact le_abs_self c }

omit [IsFiniteMeasure ν] in
/-- The support of the translation average of a test function on `U` lies in `Ω` when
`U + closedBall 0 r ⊆ Ω`. -/
private theorem tsupport_translationAverage_subset (hsr : ∀ᵐ p ∂ν, s p ∈ closedBall (0 : E) r)
    (φ : 𝓓(U, F)) : tsupport (translationAverage ν A s φ) ⊆ tsupport φ + closedBall 0 r :=
  closure_minimal ((support_translationAverage_subset hsr).trans
    (add_subset_add_right (subset_tsupport _)))
    (φ.hasCompactSupport.isCompact.add (isCompact_closedBall 0 r)).isClosed

include hA hAc hs hsr in
/-- **The translation average of test functions**: the continuous linear map sending a test
function `φ` on `U` to the test function `x ↦ ∫ A p (φ (x + s p)) dν(p)` on `Ω`, for a finite
measure `ν`, a measurable family `A` of operators bounded almost everywhere, and displacements `s`
that are almost everywhere at most `r` in norm, with `U + closedBall 0 r ⊆ Ω`. -/
def translationAverageCLM (hUΩ : (U : Set E) + closedBall (0 : E) r ⊆ (Ω : Set E)) :
    𝓓(U, F) →L[ℝ] 𝓓(Ω, G) :=
  TestFunction.limitCLM ℝ
    (fun φ ↦ ⟨translationAverage ν A s φ,
      contDiff_translationAverage φ.contDiff
        (forall_exists_norm_iteratedFDeriv_le φ.hasCompactSupport φ.contDiff) hA hAc hs,
      (φ.hasCompactSupport.isCompact.add (isCompact_closedBall 0 r)).of_isClosed_subset
        (isClosed_tsupport _) (tsupport_translationAverage_subset hsr φ),
      (tsupport_translationAverage_subset hsr φ).trans
        ((add_subset_add_right φ.tsupport_subset).trans hUΩ)⟩)
    (fun K hK ↦ ofSupportedInCLM ℝ (by
        rw [coe_thickening]
        exact (add_subset_add_right hK).trans hUΩ) ∘L
      translationAverageSupportedInCLM hA hAc hs hsr K)
    (fun _ _ _ ↦ rfl)

variable {hA hAc hs hsr}

/-- The translation average of a test function, as a function, is its translation average. -/
theorem coe_translationAverageCLM (hUΩ : (U : Set E) + closedBall (0 : E) r ⊆ (Ω : Set E))
    (φ : 𝓓(U, F)) : ⇑(translationAverageCLM hA hAc hs hsr hUΩ φ) = translationAverage ν A s φ :=
  (rfl)

/-- The translation average of a test function is `x ↦ ∫ A p (φ (x + s p)) dν(p)`. -/
@[simp]
theorem translationAverageCLM_apply (hUΩ : (U : Set E) + closedBall (0 : E) r ⊆ (Ω : Set E))
    (φ : 𝓓(U, F)) (x : E) :
    translationAverageCLM hA hAc hs hsr hUΩ φ x = ∫ p, A p (φ (x + s p)) ∂ν :=
  (rfl)

/-- **The derivative of the translation average of a test function** is
`x ↦ ∫ A p ∘ Dφ (x + s p) dν(p)`. -/
theorem hasFDerivAt_translationAverageCLM
    (hUΩ : (U : Set E) + closedBall (0 : E) r ⊆ (Ω : Set E)) (φ : 𝓓(U, F)) (x : E) :
    HasFDerivAt (translationAverageCLM hA hAc hs hsr hUΩ φ)
      (∫ p, (A p).comp (fderiv ℝ φ (x + s p)) ∂ν) x := by
  rw [coe_translationAverageCLM]
  exact hasFDerivAt_translationAverage φ.contDiff
    (forall_exists_norm_iteratedFDeriv_le φ.hasCompactSupport φ.contDiff) hA hAc hs x

omit [FiniteDimensional ℝ E] in
/-- The integrand `p ↦ A p ∘ Dφ (x + s p)` of the derivative of the translation average of a test
function is integrable. -/
theorem integrable_comp_fderiv_comp_add (hA : AEStronglyMeasurable A ν)
    (hAc : ∀ᵐ p ∂ν, ‖A p‖ ≤ c) (hs : AEStronglyMeasurable s ν)
    (φ : 𝓓(U, F)) (x : E) : Integrable (fun p ↦ (A p).comp (fderiv ℝ φ (x + s p))) ν := by
  obtain ⟨C, hC⟩ := forall_exists_norm_iteratedFDeriv_le φ.hasCompactSupport φ.contDiff 1
  exact integrable_comp_comp_add hA hAc hs (φ.contDiff.continuous_fderiv (by simp))
    (fun y ↦ by simpa [norm_iteratedFDeriv_one] using hC y) x

end TestFunction
