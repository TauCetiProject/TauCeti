/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.Alternating.Alternatization
public import TauCeti.Data.Nat.Factorial.Basic
public import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
public import TauCeti.Analysis.Calculus.ContDiff.LinearIsometry
public import TauCeti.Analysis.Normed.Operator.LinearIsometry

/-!
# Smooth pullback of continuous alternating maps

Mathlib's multilinear pullback is polynomial in the continuous linear map used on the
domain. For finite orders and `∞`, smoothness follows from Mathlib's continuous multilinear
pullback and reflection through the closed isometric inclusion. At the analytic order `ω`,
normalized alternatization recovers the alternating output when the arity factorial is nonzero.
The result is operator-valued, so it controls smooth coordinate changes of alternating-map bundles.

The regularity parameter includes the analytic order `ω`, as well as finite orders and
`∞`. The polynomial construction proves the analytic case under the factorial hypothesis.

The underlying polynomial is Mathlib's
`ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear`.
-/

public section

noncomputable section

open Set
open scoped ContDiff

variable {𝕜 E F G ι : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] [Fintype ι]

private theorem contDiff_multilinearPullback (n : WithTop ℕ∞) :
    ContDiff 𝕜 n (fun f : E →L[𝕜] F ↦
      ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear
        𝕜 (fun _ : ι ↦ E) (fun _ : ι ↦ F) G (fun _ ↦ f)) :=
  (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear
    𝕜 (fun _ : ι ↦ E) (fun _ : ι ↦ F) G).contDiff.comp
      (contDiff_pi.mpr fun _ ↦ contDiff_id)

private theorem contDiff_compContinuousLinearMapCLM_coe (n : ℕ∞) :
    ContDiff 𝕜 n
      (ContinuousAlternatingMap.compContinuousLinearMapCLM :
        (E →L[𝕜] F) → (F [⋀^ι]→L[𝕜] G) →L[𝕜] E [⋀^ι]→L[𝕜] G) := by
  classical
  -- Cache the nested operator structures before comparing the two inclusion APIs.
  let : NormedAddCommGroup ((F [⋀^ι]→L[𝕜] G) →L[𝕜] E [⋀^ι]→L[𝕜] G) := inferInstance
  let : NormedSpace 𝕜 ((F [⋀^ι]→L[𝕜] G) →L[𝕜] E [⋀^ι]→L[𝕜] G) := inferInstance
  let : NormedAddCommGroup
      ((F [⋀^ι]→L[𝕜] G) →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) G) := inferInstance
  let : NormedSpace 𝕜
      ((F [⋀^ι]→L[𝕜] G) →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) G) := inferInstance
  let J := ContinuousAlternatingMap.toContinuousMultilinearMapLI
    (𝕜 := 𝕜) (E := E) (F := G) (ι := ι)
  let I : ((F [⋀^ι]→L[𝕜] G) →L[𝕜] E [⋀^ι]→L[𝕜] G) →ₗᵢ[𝕜]
      ((F [⋀^ι]→L[𝕜] G) →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) G) :=
    LinearIsometry.postcomp J
  have hI : IsClosed (range I) :=
    J.isClosed_range_postcomp
      (ContinuousAlternatingMap.isClosed_range_toContinuousMultilinearMap
        (𝕜 := 𝕜) (E := E) (F := G) (ι := ι))
  apply (LinearIsometry.comp_contDiff_iff I hI (n := n)
    (f := ContinuousAlternatingMap.compContinuousLinearMapCLM)).mp
  let K := ContinuousAlternatingMap.toContinuousMultilinearMapCLM
    (𝕜 := 𝕜) (E := F) (F := G) (ι := ι) 𝕜
  let P := ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear
    𝕜 (fun _ : ι ↦ E) (fun _ : ι ↦ F) G
  have hP : ContDiff 𝕜 n (fun f : E →L[𝕜] F ↦ P (fun _ ↦ f)) :=
    contDiff_multilinearPullback n
  convert hP.clm_comp (contDiff_const (c := K)) using 1
  ext f a v
  simp only [Function.comp_apply, I, LinearIsometry.postcomp_apply, J, P, K,
    ContinuousAlternatingMap.toContinuousMultilinearMapLI_apply,
    ContinuousAlternatingMap.compContinuousLinearMapCLM_apply,
    ContinuousAlternatingMap.toContinuousMultilinearMapCLM_apply,
    ContinuousAlternatingMap.toContinuousMultilinearMap_compContinuousLinearMap,
    ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear_apply_apply,
    ContinuousLinearMap.comp_apply]

/-- Pullback on continuous alternating maps is smooth, as an operator-valued function of
the continuous linear map on the domain. Only the analytic order `ω` carries a factorial
hypothesis; finite orders and `∞` have no characteristic restriction. No completeness or finite
dimensionality is needed. -/
theorem ContinuousAlternatingMap.contDiff_compContinuousLinearMapCLM (n : WithTop ℕ∞)
    (hn : n = ω → ((Fintype.card ι).factorial : 𝕜) ≠ 0 := by
      intro h
      first | exact NeZero.ne _ | cases h) :
    ContDiff 𝕜 n
      (ContinuousAlternatingMap.compContinuousLinearMapCLM :
        (E →L[𝕜] F) → (F [⋀^ι]→L[𝕜] G) →L[𝕜] E [⋀^ι]→L[𝕜] G) := by
  classical
  match n with
  | ω =>
    let : NeZero ((Fintype.card ι).factorial : 𝕜) := ⟨hn rfl⟩
    let A : ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) G →L[𝕜] E [⋀^ι]→L[𝕜] G :=
      ((Fintype.card ι).factorial : 𝕜)⁻¹ • ContinuousMultilinearMap.alternatizationCLM
    let J : (F [⋀^ι]→L[𝕜] G) →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F) G :=
      ContinuousAlternatingMap.toContinuousMultilinearMapCLM 𝕜
    let P := ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear
      𝕜 (fun _ : ι ↦ E) (fun _ : ι ↦ F) G
    have hP : ContDiff 𝕜 ω (fun f : E →L[𝕜] F ↦ P (fun _ ↦ f)) :=
      contDiff_multilinearPullback ω
    have h : ContDiff 𝕜 ω (fun f : E →L[𝕜] F ↦ (A.comp (P (fun _ ↦ f))).comp J) :=
      (contDiff_const.clm_comp hP).clm_comp contDiff_const
    convert h using 1
    funext f
    ext φ : 1
    simp only [A, J, P, ContinuousLinearMap.comp_apply, _root_.smul_apply,
      ContinuousAlternatingMap.compContinuousLinearMapCLM_apply,
      ContinuousAlternatingMap.toContinuousMultilinearMapCLM_apply,
      ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear_apply_apply,
      ← ContinuousAlternatingMap.toContinuousMultilinearMap_compContinuousLinearMap,
      ContinuousAlternatingMap.inv_factorial_smul_alternatizationCLM]
  | (n : ℕ∞) => exact contDiff_compContinuousLinearMapCLM_coe n
