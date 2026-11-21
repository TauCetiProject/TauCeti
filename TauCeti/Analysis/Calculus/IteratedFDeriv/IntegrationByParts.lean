/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import TauCeti.Analysis.Calculus.IteratedFDeriv.DirectionList
import TauCeti.Analysis.Calculus.BumpFunction.FiniteDimension
import TauCeti.Analysis.Calculus.ContDiff.IsOpen

/-!
# Iterated integration by parts along a list of directions

On a finite-dimensional real normed space `E` equipped with an additive Haar measure `μ`,
integrating `B (f x) (iteratedFDerivAlong ℝ vs g x)` by parts along a list `vs` of directions
moves the derivatives onto `f` in the reversed order with sign `(-1) ^ vs.length`:

`∫ x, B (f x) (iteratedFDerivAlong ℝ vs g x) ∂μ =
  (-1 : ℝ) ^ vs.length • ∫ x, B (iteratedFDerivAlong ℝ vs.reverse f x) (g x) ∂μ`.

Here `g` is `C^{vs.length}` with compact support, while `f` is only assumed to be `C^{vs.length}`
at the points of `tsupport g`. Requiring smoothness of `f` only on the compact support of the test
function `g` makes the formula directly applicable to locally smooth functions on open domains, as
used for averaged Taylor polynomials and higher-order weak derivatives.

## Main results

* `TauCeti.integral_bilinear_iteratedFDerivAlong_eq`: iterated integration by parts for a
  continuous bilinear pairing against a compactly supported test map `g`, requiring `f` to be
  `C^{vs.length}` only on `tsupport g`.
* `TauCeti.integral_smul_iteratedFDerivAlong_eq`, `TauCeti.integral_mul_iteratedFDerivAlong_eq`:
  specializations to scalar multiplication and multiplication over a normed `ℝ`-algebra field `𝕜`.
* `TauCeti.setIntegral_bilinear_iteratedFDerivAlong_eq`,
  `TauCeti.setIntegral_smul_iteratedFDerivAlong_eq`,
  `TauCeti.setIntegral_mul_iteratedFDerivAlong_eq`: set-integral forms on any domain `s` containing
  `tsupport g`.
-/

public section

namespace TauCeti

open Filter MeasureTheory Set
open scoped ContDiff Topology

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
  have hcs (P : E → V) (Q : E → V') (hQ : HasCompactSupport Q) :
      HasCompactSupport fun x ↦ B (P x) (Q x) :=
    hQ.mono fun x ↦ mt fun h ↦ by simp [h]
  induction vs generalizing f with
  | nil => simp
  | cons v ws ih =>
    set g' : E → V' := iteratedFDerivAlong ℝ ws g
    have hg'1 : ContDiff ℝ 1 g' :=
      hg.iteratedFDerivAlong ws (by simp [List.length_cons, add_comm])
    have hg'supp : HasCompactSupport g' := hsupp.iteratedFDerivAlong ws
    have hf1 : ContDiff ℝ 1 f := hf.of_le (by exact_mod_cast Nat.succ_pos ws.length)
    have hcv : Continuous fun x ↦ fderiv ℝ f x v :=
      (hf1.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hcg' : Continuous fun x ↦ fderiv ℝ g' x v :=
      (hg'1.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have step1 := integral_bilinear_fderiv_right_eq_neg_left_of_integrable (μ := μ) (B := B)
      (f := f) (g := g') (v := v)
      (((B.continuous.comp hcv).clm_apply hg'1.continuous).integrable_of_hasCompactSupport
        (hcs _ _ hg'supp))
      (((B.continuous.comp hf1.continuous).clm_apply hcg').integrable_of_hasCompactSupport
        (hcs _ _ (hg'supp.fderiv_apply (𝕜 := ℝ) v)))
      (((B.continuous.comp hf1.continuous).clm_apply
        hg'1.continuous).integrable_of_hasCompactSupport (hcs _ _ hg'supp))
      (fun x _ ↦ hf1.differentiable one_ne_zero x) (fun x _ ↦ hg'1.differentiable one_ne_zero x)
    have step2 := ih (f := iteratedFDerivAlong ℝ [v] f)
      (hf.iteratedFDerivAlong [v] (by simp [List.length_cons]))
      (hg.of_le (by exact_mod_cast Nat.le_succ ws.length))
    simp only [g', iteratedFDerivAlong_cons_apply, iteratedFDerivAlong_nil] at step1 step2 ⊢
    rw [step1, step2, ← iteratedFDerivAlong_append]
    simp [pow_succ']

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
  obtain ⟨U, hU, hsU, hfU⟩ := exists_isOpen_superset_contDiffOn (by simp) hf
  have hfU' : ContDiffOn ℝ (vs.length : ℕ∞) f U := by simpa using hfU
  obtain ⟨F, hF, -, -, -, hFf⟩ := hfU'.exists_contDiff_eventuallyEq_on_isCompact hsupp hU hsU
  have hlhs : (fun x ↦ B (F x) (iteratedFDerivAlong ℝ vs g x)) =
      fun x ↦ B (f x) (iteratedFDerivAlong ℝ vs g x) := by
    ext x; by_cases hx : x ∈ tsupport g
    · rw [(hFf x hx).eq_of_nhds]
    · simp [image_eq_zero_of_notMem_tsupport (mt (tsupport_iteratedFDerivAlong_subset vs g ·) hx)]
  have hrhs : (fun x ↦ B (iteratedFDerivAlong ℝ vs.reverse F x) (g x)) =
      fun x ↦ B (iteratedFDerivAlong ℝ vs.reverse f x) (g x) := by
    ext x; by_cases hx : x ∈ tsupport g
    · rw [((hFf x hx).iteratedFDerivAlong vs.reverse).eq_of_nhds]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  rw [← hlhs, ← hrhs]
  exact integral_bilinear_iteratedFDerivAlong_eq_of_contDiff B vs (by simpa using hF) hg hsupp

/-- Scalar-multiplication form of `integral_bilinear_iteratedFDerivAlong_eq`. -/
theorem integral_smul_iteratedFDerivAlong_eq
    {𝕜 : Type*} [NormedField 𝕜] [NormedAlgebra ℝ 𝕜] [NormedSpace 𝕜 V]
    (vs : List E) {f : E → 𝕜} {g : E → V}
    (hf : ∀ x ∈ tsupport g, ContDiffAt ℝ vs.length f x)
    (hg : ContDiff ℝ vs.length g) (hsupp : HasCompactSupport g) :
    ∫ x, f x • iteratedFDerivAlong ℝ vs g x ∂μ =
      (-1 : ℝ) ^ vs.length • ∫ x, iteratedFDerivAlong ℝ vs.reverse f x • g x ∂μ := by
  simpa only [ContinuousLinearMap.lsmul_apply] using
    integral_bilinear_iteratedFDerivAlong_eq (ContinuousLinearMap.lsmul ℝ 𝕜) vs hf hg hsupp

/-- Scalar-product form of `integral_bilinear_iteratedFDerivAlong_eq`. -/
theorem integral_mul_iteratedFDerivAlong_eq
    {𝕜 : Type*} [NormedField 𝕜] [NormedAlgebra ℝ 𝕜]
    (vs : List E) {f g : E → 𝕜}
    (hf : ∀ x ∈ tsupport g, ContDiffAt ℝ vs.length f x)
    (hg : ContDiff ℝ vs.length g) (hsupp : HasCompactSupport g) :
    ∫ x, f x * iteratedFDerivAlong ℝ vs g x ∂μ =
      (-1 : 𝕜) ^ vs.length * ∫ x, iteratedFDerivAlong ℝ vs.reverse f x * g x ∂μ := by
  simpa only [ContinuousLinearMap.mul_apply', Algebra.smul_def, map_pow, map_neg, map_one] using
    integral_bilinear_iteratedFDerivAlong_eq (ContinuousLinearMap.mul ℝ 𝕜) vs hf hg hsupp

/-- Set-integral form of `integral_bilinear_iteratedFDerivAlong_eq` over any set `s` containing
`tsupport g`. -/
theorem setIntegral_bilinear_iteratedFDerivAlong_eq
    (B : V →L[ℝ] V' →L[ℝ] W) (vs : List E) {f : E → V} {g : E → V'} {s : Set E}
    (hf : ∀ x ∈ tsupport g, ContDiffAt ℝ vs.length f x)
    (hg : ContDiff ℝ vs.length g) (hsupp : HasCompactSupport g) (hs : tsupport g ⊆ s) :
    ∫ x in s, B (f x) (iteratedFDerivAlong ℝ vs g x) ∂μ =
      (-1 : ℝ) ^ vs.length • ∫ x in s, B (iteratedFDerivAlong ℝ vs.reverse f x) (g x) ∂μ := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hxs ↦ by
      simp [image_eq_zero_of_notMem_tsupport
        fun h ↦ hxs (hs (tsupport_iteratedFDerivAlong_subset vs g h))],
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hxs ↦ by
      simp [image_eq_zero_of_notMem_tsupport fun h ↦ hxs (hs h)]]
  exact integral_bilinear_iteratedFDerivAlong_eq B vs hf hg hsupp

/-- Set-integral scalar-multiplication form of `integral_bilinear_iteratedFDerivAlong_eq` over any
set `s` containing `tsupport g`. -/
theorem setIntegral_smul_iteratedFDerivAlong_eq
    {𝕜 : Type*} [NormedField 𝕜] [NormedAlgebra ℝ 𝕜] [NormedSpace 𝕜 V]
    (vs : List E) {f : E → 𝕜} {g : E → V} {s : Set E}
    (hf : ∀ x ∈ tsupport g, ContDiffAt ℝ vs.length f x)
    (hg : ContDiff ℝ vs.length g) (hsupp : HasCompactSupport g) (hs : tsupport g ⊆ s) :
    ∫ x in s, f x • iteratedFDerivAlong ℝ vs g x ∂μ =
      (-1 : ℝ) ^ vs.length • ∫ x in s, iteratedFDerivAlong ℝ vs.reverse f x • g x ∂μ := by
  simpa only [ContinuousLinearMap.lsmul_apply] using
    setIntegral_bilinear_iteratedFDerivAlong_eq (ContinuousLinearMap.lsmul ℝ 𝕜) vs hf hg hsupp hs

/-- Set-integral scalar-product form of `integral_bilinear_iteratedFDerivAlong_eq` over any set `s`
containing `tsupport g`. -/
theorem setIntegral_mul_iteratedFDerivAlong_eq
    {𝕜 : Type*} [NormedField 𝕜] [NormedAlgebra ℝ 𝕜]
    (vs : List E) {f g : E → 𝕜} {s : Set E}
    (hf : ∀ x ∈ tsupport g, ContDiffAt ℝ vs.length f x)
    (hg : ContDiff ℝ vs.length g) (hsupp : HasCompactSupport g) (hs : tsupport g ⊆ s) :
    ∫ x in s, f x * iteratedFDerivAlong ℝ vs g x ∂μ =
      (-1 : 𝕜) ^ vs.length * ∫ x in s, iteratedFDerivAlong ℝ vs.reverse f x * g x ∂μ := by
  simpa only [ContinuousLinearMap.mul_apply', Algebra.smul_def, map_pow, map_neg, map_one] using
    setIntegral_bilinear_iteratedFDerivAlong_eq (ContinuousLinearMap.mul ℝ 𝕜) vs hf hg hsupp hs

end IntegrationByParts

end TauCeti
