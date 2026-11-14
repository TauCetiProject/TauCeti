/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import TauCeti.Analysis.Calculus.IteratedFDeriv.DirectionList
import TauCeti.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Iterated integration by parts along a list of directions

On a finite-dimensional real normed space `E` equipped with an additive Haar measure `μ`,
integrating `B (f x) (iteratedFDerivAlong ℝ vs g x)` by parts along a list `vs` of directions
moves the derivatives onto `f` in the reversed order with sign `(-1) ^ vs.length`:

`∫ x, B (f x) (iteratedFDerivAlong ℝ vs g x) ∂μ =
  (-1 : ℝ) ^ vs.length • ∫ x, B (iteratedFDerivAlong ℝ vs.reverse f x) (g x) ∂μ`.

Here `g` is `C^{vs.length}` with compact support, while `f` is only assumed to be `C^{vs.length}`
at the points of `tsupport g`: extending `f` off a neighborhood of `tsupport g` via
`ContDiffOn.exists_contDiff_eventuallyEq_on_isCompact` reduces the local statement to a globally
`C^{vs.length}` map, where induction on `vs` applies Mathlib's single-step
`integral_bilinear_fderiv_right_eq_neg_left_of_integrable`.

## Main results

* `TauCeti.tsupport_iteratedFDerivAlong_subset`, `HasCompactSupport.iteratedFDerivAlong`:
  differentiating along a list of directions shrinks the topological support and preserves compact
  support.
* `TauCeti.integral_bilinear_iteratedFDerivAlong_eq`: iterated integration by parts for a
  continuous bilinear pairing against a compactly supported test map `g`, requiring `f` to be
  `C^{vs.length}` only on `tsupport g`.
* `TauCeti.integral_smul_iteratedFDerivAlong_eq`, `TauCeti.integral_mul_iteratedFDerivAlong_eq`:
  specializations to scalar multiplication and multiplication.
* `TauCeti.setIntegral_mul_iteratedFDerivAlong_eq`: set-integral form on any domain `s` containing
  `tsupport g`.
-/

public section

namespace TauCeti

open Filter MeasureTheory Set
open scoped ContDiff Topology

section Support

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Iterated directional differentiation shrinks the topological support. -/
theorem tsupport_iteratedFDerivAlong_subset (vs : List E) (f : E → F) :
    tsupport (iteratedFDerivAlong 𝕜 vs f) ⊆ tsupport f := by
  induction vs with
  | nil => rw [iteratedFDerivAlong_nil]
  | cons v vs ih =>
    rw [iteratedFDerivAlong_cons]
    exact (tsupport_fderiv_apply_subset 𝕜 v).trans ih

/-- Iterated directional differentiation preserves compact support. -/
theorem _root_.HasCompactSupport.iteratedFDerivAlong {f : E → F} (hf : HasCompactSupport f)
    (vs : List E) :
    HasCompactSupport (iteratedFDerivAlong 𝕜 vs f) :=
  hf.of_isClosed_subset (isClosed_tsupport _) (tsupport_iteratedFDerivAlong_subset vs f)

end Support

section IntegrationByParts

variable {E V V' W : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup V'] [NormedSpace ℝ V']
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {μ : Measure E} [μ.IsAddHaarMeasure]

/-- Auxiliary global version of `integral_bilinear_iteratedFDerivAlong_eq` when `f` is `C^k` on all
of `E`. -/
private theorem integral_bilinear_iteratedFDerivAlong_eq_of_contDiff
    (B : V →L[ℝ] V' →L[ℝ] W) (vs : List E) {f : E → V} {g : E → V'}
    (hf : ContDiff ℝ vs.length f) (hg : ContDiff ℝ vs.length g) (hsupp : HasCompactSupport g) :
    ∫ x, B (f x) (iteratedFDerivAlong ℝ vs g x) ∂μ =
      (-1 : ℝ) ^ vs.length • ∫ x, B (iteratedFDerivAlong ℝ vs.reverse f x) (g x) ∂μ := by
  have hcs : ∀ (P : E → V) (Q : E → V'), HasCompactSupport Q →
      HasCompactSupport fun x ↦ B (P x) (Q x) :=
    fun P Q hQ ↦ hQ.mono fun x hx ↦ by
      simp only [Function.mem_support] at hx ⊢
      contrapose hx
      simp [hx]
  induction vs generalizing f with
  | nil => simp
  | cons v ws ih =>
    set g' : E → V' := iteratedFDerivAlong ℝ ws g
    have hg'1 : ContDiff ℝ 1 g' :=
      hg.iteratedFDerivAlong ws (by simp [List.length_cons, add_comm])
    have hg'supp : HasCompactSupport g' := hsupp.iteratedFDerivAlong ws
    have hf1 : ContDiff ℝ 1 f :=
      hf.of_le (by exact_mod_cast Nat.succ_pos ws.length)
    have hf' : ContDiff ℝ ws.length (iteratedFDerivAlong ℝ [v] f) :=
      hf.iteratedFDerivAlong [v] (by simp [List.length_cons])
    have hg_ws : ContDiff ℝ ws.length g :=
      hg.of_le (by exact_mod_cast Nat.le_succ ws.length)
    have hcv : Continuous fun x ↦ fderiv ℝ f x v :=
      (hf1.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hcg' : Continuous fun x ↦ fderiv ℝ g' x v :=
      (hg'1.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hint1 : Integrable (fun x ↦ B (fderiv ℝ f x v) (g' x)) μ :=
      Continuous.integrable_of_hasCompactSupport
        ((B.continuous.comp hcv).clm_apply hg'1.continuous) (hcs _ _ hg'supp)
    have hint2 : Integrable (fun x ↦ B (f x) (fderiv ℝ g' x v)) μ :=
      Continuous.integrable_of_hasCompactSupport
        ((B.continuous.comp hf1.continuous).clm_apply hcg')
        (hcs _ _ (hg'supp.fderiv_apply (𝕜 := ℝ) v))
    have hint3 : Integrable (fun x ↦ B (f x) (g' x)) μ :=
      Continuous.integrable_of_hasCompactSupport
        ((B.continuous.comp hf1.continuous).clm_apply hg'1.continuous) (hcs _ _ hg'supp)
    have step1 := integral_bilinear_fderiv_right_eq_neg_left_of_integrable (μ := μ) (B := B)
      (f := f) (g := g') (v := v) hint1 hint2 hint3
      (fun x _ ↦ hf1.differentiable one_ne_zero x)
      (fun x _ ↦ hg'1.differentiable one_ne_zero x)
    have step2 := ih (f := iteratedFDerivAlong ℝ [v] f) hf' hg_ws
    have hf_eq : (fun x ↦ B (fderiv ℝ f x v) (g' x)) =
        fun x ↦ B (iteratedFDerivAlong ℝ [v] f x) (iteratedFDerivAlong ℝ ws g x) := by
      ext x
      simp [g']
    simp only [iteratedFDerivAlong_cons_apply] at step1 ⊢
    rw [step1, hf_eq, step2, ← iteratedFDerivAlong_append, ← List.reverse_cons, List.length_cons,
      pow_succ', neg_one_mul, neg_smul]

/-- **Iterated integration by parts along a list of directions.** If `g` is `C^{vs.length}` with
compact support and `f` is `C^{vs.length}` at every point of `tsupport g`, then
`∫ x, B (f x) (iteratedFDerivAlong ℝ vs g x) ∂μ =
  (-1) ^ vs.length • ∫ x, B (iteratedFDerivAlong ℝ vs.reverse f x) (g x) ∂μ`. -/
theorem integral_bilinear_iteratedFDerivAlong_eq
    (B : V →L[ℝ] V' →L[ℝ] W) (vs : List E) {f : E → V} {g : E → V'}
    (hf : ∀ x ∈ tsupport g, ContDiffAt ℝ vs.length f x)
    (hg : ContDiff ℝ vs.length g) (hsupp : HasCompactSupport g) :
    ∫ x, B (f x) (iteratedFDerivAlong ℝ vs g x) ∂μ =
      (-1 : ℝ) ^ vs.length • ∫ x, B (iteratedFDerivAlong ℝ vs.reverse f x) (g x) ∂μ := by
  let U : Set E := {x | ContDiffAt ℝ vs.length f x}
  have hU : IsOpen U :=
    isOpen_iff_mem_nhds.2 fun x hx ↦ ContDiffAt.eventually hx (by simp)
  have hfU : ContDiffOn ℝ (vs.length : ℕ∞) f U :=
    fun x hx ↦ by simpa using hx.contDiffWithinAt
  obtain ⟨F, hF, -, -, -, hFf⟩ :=
    hfU.exists_contDiff_eventuallyEq_on_isCompact hsupp hU hf
  have hF' : ContDiff ℝ vs.length F := by simpa using hF
  have hlhs : (fun x ↦ B (F x) (iteratedFDerivAlong ℝ vs g x)) =
      fun x ↦ B (f x) (iteratedFDerivAlong ℝ vs g x) := by
    ext x
    by_cases hx : x ∈ tsupport g
    · rw [(hFf x hx).eq_of_nhds]
    · have hx' : x ∉ tsupport (iteratedFDerivAlong ℝ vs g) :=
        fun h ↦ hx (tsupport_iteratedFDerivAlong_subset vs g h)
      simp [image_eq_zero_of_notMem_tsupport hx']
  have hrhs : (fun x ↦ B (iteratedFDerivAlong ℝ vs.reverse F x) (g x)) =
      fun x ↦ B (iteratedFDerivAlong ℝ vs.reverse f x) (g x) := by
    ext x
    by_cases hx : x ∈ tsupport g
    · rw [((hFf x hx).iteratedFDerivAlong vs.reverse).eq_of_nhds]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  rw [← hlhs, ← hrhs]
  exact integral_bilinear_iteratedFDerivAlong_eq_of_contDiff B vs hF' hg hsupp

/-- Scalar-multiplication form of `integral_bilinear_iteratedFDerivAlong_eq`. -/
theorem integral_smul_iteratedFDerivAlong_eq
    (vs : List E) {f : E → ℝ} {g : E → V}
    (hf : ∀ x ∈ tsupport g, ContDiffAt ℝ vs.length f x)
    (hg : ContDiff ℝ vs.length g) (hsupp : HasCompactSupport g) :
    ∫ x, f x • iteratedFDerivAlong ℝ vs g x ∂μ =
      (-1 : ℝ) ^ vs.length • ∫ x, iteratedFDerivAlong ℝ vs.reverse f x • g x ∂μ := by
  simpa only [ContinuousLinearMap.lsmul_apply] using
    integral_bilinear_iteratedFDerivAlong_eq (ContinuousLinearMap.lsmul ℝ ℝ) vs hf hg hsupp

/-- Scalar-product form of `integral_bilinear_iteratedFDerivAlong_eq`. -/
theorem integral_mul_iteratedFDerivAlong_eq
    (vs : List E) {f g : E → ℝ}
    (hf : ∀ x ∈ tsupport g, ContDiffAt ℝ vs.length f x)
    (hg : ContDiff ℝ vs.length g) (hsupp : HasCompactSupport g) :
    ∫ x, f x * iteratedFDerivAlong ℝ vs g x ∂μ =
      (-1 : ℝ) ^ vs.length * ∫ x, iteratedFDerivAlong ℝ vs.reverse f x * g x ∂μ := by
  simpa only [ContinuousLinearMap.mul_apply', smul_eq_mul] using
    integral_bilinear_iteratedFDerivAlong_eq (ContinuousLinearMap.mul ℝ ℝ) vs hf hg hsupp

/-- Set-integral form of `integral_mul_iteratedFDerivAlong_eq` over any set `s` containing
`tsupport g`. -/
theorem setIntegral_mul_iteratedFDerivAlong_eq
    (vs : List E) {f g : E → ℝ} {s : Set E}
    (hf : ∀ x ∈ tsupport g, ContDiffAt ℝ vs.length f x)
    (hg : ContDiff ℝ vs.length g) (hsupp : HasCompactSupport g) (hs : tsupport g ⊆ s) :
    ∫ x in s, f x * iteratedFDerivAlong ℝ vs g x ∂μ =
      (-1 : ℝ) ^ vs.length * ∫ x in s, iteratedFDerivAlong ℝ vs.reverse f x * g x ∂μ := by
  have hlhs : ∫ x in s, f x * iteratedFDerivAlong ℝ vs g x ∂μ =
      ∫ x, f x * iteratedFDerivAlong ℝ vs g x ∂μ := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hxs ↦ ?_
    have hx' : x ∉ tsupport (iteratedFDerivAlong ℝ vs g) :=
      fun h ↦ hxs (hs (tsupport_iteratedFDerivAlong_subset vs g h))
    simp [image_eq_zero_of_notMem_tsupport hx']
  have hrhs : ∫ x in s, iteratedFDerivAlong ℝ vs.reverse f x * g x ∂μ =
      ∫ x, iteratedFDerivAlong ℝ vs.reverse f x * g x ∂μ := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hxs ↦ ?_
    have hx' : x ∉ tsupport g := fun h ↦ hxs (hs h)
    simp [image_eq_zero_of_notMem_tsupport hx']
  rw [hlhs, hrhs]
  exact integral_mul_iteratedFDerivAlong_eq vs hf hg hsupp

end IntegrationByParts

end TauCeti
