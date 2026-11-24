/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.ParametricIntegral.TranslationAverage
public import Mathlib.Analysis.Distribution.TestFunction

/-!
# Averages of translates of test functions against a measure

Let `ν` be a finite measure on a parameter space `P`, let `A : P → F →L[ℝ] G` be a measurable
family of continuous linear maps with `‖A p‖ ≤ c` for almost every `p`, and let `s : P → E` be a
measurable family of displacements in a finite-dimensional real normed space `E`, almost
everywhere at most `r` in norm. The translation average `x ↦ ∫ A p (φ (x + s p)) dν(p)`
(`TauCeti.translationAverage`, from
`TauCeti.Analysis.Calculus.ParametricIntegral.TranslationAverage`) of a test function `φ` on an
open set `U` is supported in `supp φ + closedBall 0 r`. So the
translation average maps test functions on `U` to test functions on any open set
`Ω ⊇ U + closedBall 0 r`, continuously for the LF topologies
(`TestFunction.translationAverageCLM`): its `i`-th derivatives are bounded by `c ν(P)` times
those of `φ`.

Two cases are the operators used to regularize currents: with `A p = id` and `s` the identity of
`E`, the translation average is the mean `x ↦ ∫ φ (x + v) dν(v)` of the translates of `φ` against a
measure `ν` on `E`, which for `ν` given by a smooth density is the convolution of `φ` with the
reflected density; and with `A (v, t)` the interior product with `v` and `s (v, t) = t v`, it is the
averaged homotopy operator between such a mean and the identity
(`TauCeti.Analysis.Distribution.TestFunction.TranslateAverage.Homotopy`).

## Main declarations

* `TestFunction.translationAverageCLM`: the translation average as a continuous linear map of test
  functions, with values `TestFunction.translationAverageCLM_apply` and
  `TestFunction.coe_translationAverageCLM`, support
  `TestFunction.tsupport_translationAverageCLM_subset`, and derivative
  `TestFunction.hasFDerivAt_translationAverageCLM`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §1.3 and §4.1
  (regularization by convolution with test functions and with measures).
-/

public section

noncomputable section

open MeasureTheory Metric Set TopologicalSpace Filter
open scoped Pointwise Distributions ContDiff

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
        (isClosed_tsupport _) (tsupport_translationAverage_subset φ.hasCompactSupport hsr),
      (tsupport_translationAverage_subset φ.hasCompactSupport hsr).trans
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

/-- **Support of the translation average of a test function**: it is supported in
`tsupport φ + closedBall 0 r`. -/
theorem tsupport_translationAverageCLM_subset
    (hUΩ : (U : Set E) + closedBall (0 : E) r ⊆ (Ω : Set E)) (φ : 𝓓(U, F)) :
    tsupport (translationAverageCLM hA hAc hs hsr hUΩ φ) ⊆ tsupport φ + closedBall (0 : E) r :=
  tsupport_translationAverage_subset φ.hasCompactSupport hsr

/-- The translation average of a test function is `x ↦ ∫ A p (φ (x + s p)) dν(p)`. -/
@[simp]
theorem translationAverageCLM_apply (hUΩ : (U : Set E) + closedBall (0 : E) r ⊆ (Ω : Set E))
    (φ : 𝓓(U, F)) (x : E) :
    translationAverageCLM hA hAc hs hsr hUΩ φ x = ∫ p, A p (φ (x + s p)) ∂ν :=
  translationAverage_apply ..

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
