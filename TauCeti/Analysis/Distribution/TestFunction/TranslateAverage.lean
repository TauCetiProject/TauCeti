/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import TauCeti.Analysis.Calculus.ParametricIntegral.Basic
import TauCeti.Analysis.Distribution.Regularization
import TauCeti.Analysis.Distribution.TestFunction.Convergence

/-!
# Averages of translates of test functions

Let `Y` be a compact space with a finite measure `ν`, and let `L : Y → (F →L[ℝ] G)` and
`v : Y → E` be continuous. For a test function `φ` on the whole space `E` the **average of
translates**

`(A φ) x = ∫ L p (φ (x + v p)) ∂ν(p)`

is again a test function: it is smooth, every derivative passes under the integral, and it is
supported in `tsupport φ - v(Y)`. Its derivatives are bounded by those of `φ` times
`∫ ‖L p‖ ∂ν`, so `A` is a continuous linear map on the LF space of test functions
(`TestFunction.translateAverageCLM`).

Every continuous linear map `T` on test functions with finite-dimensional values passes under this
average: `T (A φ) = ∫ T (L p (φ (· + v p))) ∂ν(p)`
(`ContinuousLinearMap.apply_translateAverageCLM`). Mollification by a smooth bump is the average of
translates with `L p = ρ p • id` and `v p = p`; contracting with the displacement along the
straight segments `x ↦ x + t y` gives the homotopy operator between mollification and the
identity, see `TauCeti.Analysis.Distribution.TestFunction.Mollify`. The operator is only defined on
the whole space, since translates leave a proper open subset.

## Main declarations

* `TestFunction.translateAverageCLM`: the average of translates, as a continuous linear map.
* `TestFunction.translateAverageCLM_apply`: its pointwise formula.
* `TestFunction.iteratedFDeriv_translateAverageCLM`: derivatives pass under the average.
* `TestFunction.norm_iteratedFDeriv_translateAverageCLM_le`: the derivative bounds.
* `TestFunction.tsupport_translateAverageCLM_subset`: its support.
* `ContinuousLinearMap.apply_translateAverageCLM`: continuous linear maps pass under the average.
-/

public section

noncomputable section

open Set Function MeasureTheory TopologicalSpace
open scoped Distributions ContDiff

namespace TestFunction

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {Y : Type*} [TopologicalSpace Y] [CompactSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
  {ν : Measure Y} [IsFiniteMeasure ν] {L : Y → F →L[ℝ] G} {v : Y → E}

section Pointwise

variable {φ : E → F}

omit [TopologicalSpace Y] [CompactSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] in
/-- The `k`-th derivative of a translate of `φ` composed with `L p`. -/
private theorem iteratedFDeriv_clm_comp_add (hφ : ContDiff ℝ ∞ φ) (p : Y) (k : ℕ) (x : E) :
    iteratedFDeriv ℝ k (fun z ↦ L p (φ (z + v p))) x =
      (L p).compContinuousMultilinearMap (iteratedFDeriv ℝ k φ (x + v p)) := by
  have h := (L p).iteratedFDeriv_comp_left (f := fun z ↦ φ (z + v p)) (x := x)
    ((hφ.comp (contDiff_id.add contDiff_const)).contDiffAt) (i := k) (mod_cast le_top)
  rw [iteratedFDeriv_comp_add_right] at h
  exact h

omit [CompactSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] in
/-- The derivatives of the translates are jointly continuous in the parameter and the point. -/
private theorem continuous_iteratedFDeriv_clm_comp_add (hφ : ContDiff ℝ ∞ φ)
    (hL : Continuous L) (hv : Continuous v) (k : ℕ) :
    Continuous fun q : Y × E ↦ iteratedFDeriv ℝ k (fun z ↦ L q.1 (φ (z + v q.1))) q.2 := by
  simp only [iteratedFDeriv_clm_comp_add hφ]
  exact ((ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin k ↦ E) F G).continuous
    |>.comp (hL.comp continuous_fst)).clm_apply
      ((hφ.continuous_iteratedFDeriv (mod_cast le_top)).comp
        (continuous_snd.add (hv.comp continuous_fst)))

/-- The average of the translates of a smooth function is smooth. -/
private theorem contDiff_translateAverage (hφ : ContDiff ℝ ∞ φ) (hL : Continuous L)
    (hv : Continuous v) : ContDiff ℝ ∞ fun x ↦ ∫ p, L p (φ (x + v p)) ∂ν :=
  contDiffOn_univ.1 <| TauCeti.contDiffOn_integral_of_continuous_jets isOpen_univ
    (fun p ↦ ((L p).contDiff.comp (hφ.comp (contDiff_id.add contDiff_const))).contDiffOn)
    fun k ↦ (continuous_iteratedFDeriv_clm_comp_add hφ hL hv k).continuousOn

/-- Every derivative of the average of translates is the average of the derivatives. -/
private theorem iteratedFDeriv_translateAverage (hφ : ContDiff ℝ ∞ φ) (hL : Continuous L)
    (hv : Continuous v) (k : ℕ) (x : E) :
    iteratedFDeriv ℝ k (fun x ↦ ∫ p, L p (φ (x + v p)) ∂ν) x =
      ∫ p, (L p).compContinuousMultilinearMap (iteratedFDeriv ℝ k φ (x + v p)) ∂ν := by
  rw [TauCeti.iteratedFDeriv_integral_of_continuous_jets (f := fun p z ↦ L p (φ (z + v p)))
    isOpen_univ
    (fun p ↦ ((L p).contDiff.comp (hφ.comp (contDiff_id.add contDiff_const))).contDiffOn)
    (fun k ↦ (continuous_iteratedFDeriv_clm_comp_add hφ hL hv k).continuousOn) k (mem_univ x)]
  simp only [iteratedFDeriv_clm_comp_add hφ]

omit [NormedSpace ℝ E] in
/-- A pointwise bound `‖g p‖ ≤ ‖L p‖ * C` bounds `‖∫ g‖` by `(∫ ‖L p‖ ∂ν) * C`. -/
private theorem norm_integral_le_integral_norm_mul (hL : Continuous L) {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] {g : Y → H} {C : ℝ} (hg : ∀ p, ‖g p‖ ≤ ‖L p‖ * C) :
    ‖∫ p, g p ∂ν‖ ≤ (∫ p, ‖L p‖ ∂ν) * C := by
  rw [← integral_mul_const]
  exact norm_integral_le_of_norm_le (((continuous_norm.comp hL).mul continuous_const)
    |>.integrable_of_hasCompactSupport (.of_compactSpace _)) (ae_of_all _ hg)

omit [NormedSpace ℝ E] [TopologicalSpace Y] [CompactSpace Y] [OpensMeasurableSpace Y]
  [IsFiniteMeasure ν] in
/-- The average of translates vanishes off `K - v(Y)` when `φ` vanishes off `K`. -/
private theorem translateAverage_eq_zero {K : Set E} (hφK : support φ ⊆ K) {x : E}
    (hx : x ∉ (fun q : E × Y ↦ q.1 - v q.2) '' (K ×ˢ univ)) :
    ∫ p, L p (φ (x + v p)) ∂ν = 0 := by
  refine integral_eq_zero_of_ae (ae_of_all _ fun p ↦ ?_)
  have : φ (x + v p) = 0 := notMem_support.1 fun h ↦
    hx ⟨(x + v p, p), ⟨hφK h, mem_univ p⟩, by simp⟩
  simp [this]

end Pointwise

/-- The compact set `K - v(Y)` carrying the averages of the translates of tests supported in
`K`. -/
private def averageCompacts (hv : Continuous v) (K : Compacts E) : Compacts E :=
  ⟨(fun q : E × Y ↦ q.1 - v q.2) '' ((K : Set E) ×ˢ univ),
    (K.isCompact.prod isCompact_univ).image (continuous_fst.sub (hv.comp continuous_snd))⟩

omit [NormedSpace ℝ E] [MeasurableSpace Y] [OpensMeasurableSpace Y] in
private theorem coe_averageCompacts (hv : Continuous v) (K : Compacts E) :
    (averageCompacts hv K : Set E) = (fun q : E × Y ↦ q.1 - v q.2) '' ((K : Set E) ×ˢ univ) :=
  rfl

omit [MeasurableSpace Y] [OpensMeasurableSpace Y] in
/-- A function vanishing off `tsupport φ - v(Y)` is supported in `averageCompacts`. -/
private theorem tsupport_subset_averageCompacts {H : Type*} [Zero H] (hv : Continuous v)
    (φ : 𝓓((⊤ : Opens E), F)) {g : E → H}
    (hg : ∀ x ∉ (fun q : E × Y ↦ q.1 - v q.2) '' (tsupport φ ×ˢ univ), g x = 0) :
    tsupport g ⊆ averageCompacts hv ⟨tsupport φ, φ.hasCompactSupport⟩ :=
  closure_minimal (fun x hx ↦ by_contra fun h ↦ hx (hg x h))
    (averageCompacts hv ⟨tsupport φ, φ.hasCompactSupport⟩).isCompact.isClosed

variable (ν) in
/-- The average of translates on the tests supported in a compact `K`. -/
private def translateAverageSupportedInCLM (hL : Continuous L)
    (hv : Continuous v) (K : Compacts E) :
    𝓓_{K}(E, F) →L[ℝ] 𝓓_{averageCompacts hv K}(E, G) :=
  letI A : 𝓓_{K}(E, F) →ₗ[ℝ] 𝓓_{averageCompacts hv K}(E, G) :=
    { toFun φ := .of_support_subset (contDiff_translateAverage (ν := ν) φ.contDiff hL hv)
        fun x hx ↦
          by_contra fun h ↦ hx (translateAverage_eq_zero φ.support_subset
            (by rwa [coe_averageCompacts] at h))
      map_add' φ ψ := ContDiffMapSupportedIn.ext fun x ↦ by
        simp only [ContDiffMapSupportedIn.coe_of_support_subset, FunLike.coe_add,
          Pi.add_apply, map_add]
        exact integral_add
          ((hL.clm_apply (φ.continuous.comp ((continuous_const (y := x)).add hv)))
            |>.integrable_of_hasCompactSupport (.of_compactSpace _))
          ((hL.clm_apply (ψ.continuous.comp ((continuous_const (y := x)).add hv)))
            |>.integrable_of_hasCompactSupport (.of_compactSpace _))
      map_smul' c φ := ContDiffMapSupportedIn.ext fun x ↦ by
        simp only [ContDiffMapSupportedIn.coe_of_support_subset, FunLike.coe_smul,
          Pi.smul_apply, map_smul, integral_smul, RingHom.id_apply]
        -- The values of `of_support_subset` are those of the average by construction; the simp
        -- lemma does not apply since the smoothness order is stated as `∞`.
        rfl }
  { toLinearMap := A
    cont := by
      refine WithSeminorms.continuous_of_isBounded (ContDiffMapSupportedIn.withSeminorms ..)
        (ContDiffMapSupportedIn.withSeminorms ..) _ (.of_real fun i ↦ ?_)
      set C := ∫ p, ‖L p‖ ∂ν
      have hC : 0 ≤ C := integral_nonneg fun _ ↦ norm_nonneg _
      refine ⟨{i}, C, fun φ ↦ ?_⟩
      rw [Finset.sup_singleton]
      refine ((A φ).seminorm_top_le_iff ℝ (mul_nonneg hC (apply_nonneg _ _)) i).2 fun x _ ↦ ?_
      -- `A φ` is the average of the translates of `φ` by construction.
      have h : iteratedFDeriv ℝ i (A φ) x =
          ∫ p, (L p).compContinuousMultilinearMap (iteratedFDeriv ℝ i φ (x + v p)) ∂ν :=
        iteratedFDeriv_translateAverage φ.contDiff hL hv i x
      rw [h]
      exact norm_integral_le_integral_norm_mul hL fun p ↦
        ((L p).norm_compContinuousMultilinearMap_le _).trans (mul_le_mul_of_nonneg_left
          (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℝ) (norm_nonneg _)) }

variable (ν) in
/-- The **average of translates** `φ ↦ (x ↦ ∫ L p (φ (x + v p)) ∂ν(p))` of test functions on the
whole space `E`, for continuous families `L : Y → (F →L[ℝ] G)` and `v : Y → E` over a compact
space `Y` with a finite measure `ν`, as a continuous linear map. -/
def translateAverageCLM (hL : Continuous L) (hv : Continuous v) :
    𝓓((⊤ : Opens E), F) →L[ℝ] 𝓓((⊤ : Opens E), G) :=
  letI A (φ : 𝓓((⊤ : Opens E), F)) : 𝓓((⊤ : Opens E), G) :=
    ⟨fun x ↦ ∫ p, L p (φ (x + v p)) ∂ν, contDiff_translateAverage φ.contDiff hL hv,
      (averageCompacts hv ⟨tsupport φ, φ.hasCompactSupport⟩).isCompact.of_isClosed_subset
        (isClosed_tsupport _) (tsupport_subset_averageCompacts hv φ fun _ h ↦
          translateAverage_eq_zero (subset_tsupport φ) h),
      subset_univ _⟩
  TestFunction.limitCLM ℝ A
    (fun K _ ↦ ofSupportedInCLM ℝ (subset_univ _) ∘L translateAverageSupportedInCLM ν hL hv K)
    (fun _ _ _ ↦ rfl)

variable {hL : Continuous L} {hv : Continuous v}

/-- The average of translates at a point. -/
@[simp]
theorem translateAverageCLM_apply (φ : 𝓓((⊤ : Opens E), F)) (x : E) :
    translateAverageCLM ν hL hv φ x = ∫ p, L p (φ (x + v p)) ∂ν :=
  (rfl)

/-- Every derivative of an average of translates is the average of the derivatives. -/
theorem iteratedFDeriv_translateAverageCLM (φ : 𝓓((⊤ : Opens E), F)) (k : ℕ) (x : E) :
    iteratedFDeriv ℝ k (translateAverageCLM ν hL hv φ) x =
      ∫ p, (L p).compContinuousMultilinearMap (iteratedFDeriv ℝ k φ (x + v p)) ∂ν :=
  iteratedFDeriv_translateAverage φ.contDiff hL hv k x

/-- **Derivative bounds for an average of translates**: a bound `C` on the `k`-th derivative of
`φ` bounds the `k`-th derivative of its average by `(∫ ‖L p‖ ∂ν) * C`. -/
theorem norm_iteratedFDeriv_translateAverageCLM_le (φ : 𝓓((⊤ : Opens E), F)) (k : ℕ) {C : ℝ}
    (hC : ∀ y, ‖iteratedFDeriv ℝ k φ y‖ ≤ C) (x : E) :
    ‖iteratedFDeriv ℝ k (translateAverageCLM ν hL hv φ) x‖ ≤ (∫ p, ‖L p‖ ∂ν) * C := by
  rw [iteratedFDeriv_translateAverageCLM]
  exact norm_integral_le_integral_norm_mul hL fun p ↦
    ((L p).norm_compContinuousMultilinearMap_le _).trans
      (mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _))

/-- **Sup bound for an average of translates**: a bound `C` on the values of `φ` bounds its
average by `(∫ ‖L p‖ ∂ν) * C`. -/
theorem norm_translateAverageCLM_apply_le (φ : 𝓓((⊤ : Opens E), F)) {C : ℝ}
    (hC : ∀ y, ‖φ y‖ ≤ C) (x : E) :
    ‖translateAverageCLM ν hL hv φ x‖ ≤ (∫ p, ‖L p‖ ∂ν) * C :=
  norm_integral_le_integral_norm_mul hL fun p ↦
    ((L p).le_opNorm _).trans (mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _))

/-- An average of translates is supported in `tsupport φ - v(Y)`. -/
theorem tsupport_translateAverageCLM_subset (φ : 𝓓((⊤ : Opens E), F)) :
    tsupport (translateAverageCLM ν hL hv φ) ⊆
      (fun q : E × Y ↦ q.1 - v q.2) '' (tsupport φ ×ˢ univ) :=
  tsupport_subset_averageCompacts hv φ fun _ h ↦ translateAverage_eq_zero (subset_tsupport φ) h

omit [MeasurableSpace Y] [OpensMeasurableSpace Y] in
/-- The test functions `f p = L p (φ (· + v p))` are supported in `tsupport φ - v(Y)`. -/
private theorem tsupport_subset_of_apply_eq (hv : Continuous v) (φ : 𝓓((⊤ : Opens E), F))
    {f : Y → 𝓓((⊤ : Opens E), G)} (hf : ∀ p x, f p x = L p (φ (x + v p))) (p : Y) :
    tsupport (f p) ⊆ averageCompacts hv ⟨tsupport φ, φ.hasCompactSupport⟩ :=
  tsupport_subset_averageCompacts hv φ fun x h ↦ by
    rw [hf, image_eq_zero_of_notMem_tsupport fun h' ↦ h ⟨(x + v p, p), ⟨h', mem_univ p⟩, by simp⟩,
      map_zero]

omit [CompactSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] in
/-- The derivatives of the test functions `f p = L p (φ (· + v p))` are jointly continuous in the
parameter and the point. -/
private theorem continuous_iteratedFDeriv_of_apply_eq (hL : Continuous L) (hv : Continuous v)
    (φ : 𝓓((⊤ : Opens E), F)) {f : Y → 𝓓((⊤ : Opens E), G)}
    (hf : ∀ p x, f p x = L p (φ (x + v p))) (k : ℕ) :
    Continuous fun q : Y × E ↦ iteratedFDeriv ℝ k (f q.1) q.2 := by
  have hfun (p : Y) : ⇑(f p) = fun x ↦ L p (φ (x + v p)) := funext (hf p)
  simp only [hfun]
  exact continuous_iteratedFDeriv_clm_comp_add φ.contDiff hL hv k

omit [MeasurableSpace Y] [OpensMeasurableSpace Y] in
/-- **Continuity of a family of translates**: the test functions `f p = L p (φ (· + v p))`
depend continuously on `p` for the LF topology. -/
theorem continuous_of_apply_eq_apply_add (hL : Continuous L) (hv : Continuous v)
    (φ : 𝓓((⊤ : Opens E), F)) {f : Y → 𝓓((⊤ : Opens E), G)}
    (hf : ∀ p x, f p x = L p (φ (x + v p))) : Continuous f :=
  continuous_of_continuous_iteratedFDeriv
    (averageCompacts hv ⟨tsupport φ, φ.hasCompactSupport⟩).isCompact (subset_univ _)
    (tsupport_subset_of_apply_eq hv φ hf) fun k _ ↦
      continuous_iteratedFDeriv_of_apply_eq hL hv φ hf k

end TestFunction

namespace ContinuousLinearMap

open TestFunction

variable {E F G V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [FiniteDimensional ℝ G] [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  {Y : Type*} [TopologicalSpace Y] [CompactSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
  {ν : Measure Y} [IsFiniteMeasure ν] {L : Y → F →L[ℝ] G} {v : Y → E}
  {hL : Continuous L} {hv : Continuous v}

/-- **A continuous linear map passes under an integral of translates**: if the test function `ψ`
is the integral `ψ x = ∫ f p x ∂ν` of the translates `f p = L p (φ (· + v p))`, then
`T ψ = ∫ T (f p) ∂ν`. -/
theorem apply_eq_integral_of_apply_eq_apply_add (T : 𝓓((⊤ : Opens E), G) →L[ℝ] V)
    (hL : Continuous L) (hv : Continuous v) (φ : 𝓓((⊤ : Opens E), F))
    {f : Y → 𝓓((⊤ : Opens E), G)} (hf : ∀ p x, f p x = L p (φ (x + v p)))
    {ψ : 𝓓((⊤ : Opens E), G)} (hψ : ∀ x, ψ x = ∫ p, f p x ∂ν) :
    T ψ = ∫ p, T (f p) ∂ν :=
  T.apply_eq_integral_of_continuous_iteratedFDeriv
    (K := averageCompacts hv ⟨tsupport φ, φ.hasCompactSupport⟩) (subset_univ _)
    (tsupport_subset_of_apply_eq hv φ hf) (continuous_iteratedFDeriv_of_apply_eq hL hv φ hf) hψ

/-- **A continuous linear map passes under an average of translates**: if the test functions
`f p` are the translates `x ↦ L p (φ (x + v p))`, then `T (A φ) = ∫ T (f p) ∂ν`. -/
theorem apply_translateAverageCLM (T : 𝓓((⊤ : Opens E), G) →L[ℝ] V) (φ : 𝓓((⊤ : Opens E), F))
    {f : Y → 𝓓((⊤ : Opens E), G)} (hf : ∀ p x, f p x = L p (φ (x + v p))) :
    T (translateAverageCLM ν hL hv φ) = ∫ p, T (f p) ∂ν :=
  T.apply_eq_integral_of_apply_eq_apply_add hL hv φ hf fun x ↦ by simp [hf]

end ContinuousLinearMap
