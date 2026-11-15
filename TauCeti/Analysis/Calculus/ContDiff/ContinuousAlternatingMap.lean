/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.Alternating.Alternatization
public import TauCeti.Data.Nat.Factorial.Basic
public import TauCeti.Analysis.Calculus.ContDiff.ContinuousMultilinearMap
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

When the family of alternating maps vanishes to first order at a point, only continuity of the
family of linear maps is needed: the pullback then also has zero value and zero derivative there
(`HasFDerivAt.compContinuousLinearMap_of_eq_zero`). This is how a zero first jet of a
differential form is read in another chart.
-/

public section

noncomputable section

open Set Filter
open scoped ContDiff Topology

variable {𝕜 E F G ι : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] [Fintype ι]

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
    ContinuousMultilinearMap.contDiff_compContinuousLinearMapContinuousMultilinear_diagonal n
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
      ContinuousMultilinearMap.contDiff_compContinuousLinearMapContinuousMultilinear_diagonal ω
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

/-- A family of alternating maps with zero value and zero derivative at `x`, precomposed with a
family of continuous linear maps that is continuous at `x`, again has zero value and zero
derivative at `x`. This is how a zero first jet of a form survives a change of coordinates
whose derivative is only continuous. -/
theorem HasFDerivAt.compContinuousLinearMap_of_eq_zero {𝕜 X X' E G ι : Type*}
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup X'] [NormedSpace 𝕜 X'] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] [Finite ι]
    {φ : X → E [⋀^ι]→L[𝕜] G} {L : X → X' →L[𝕜] E} {x : X}
    (hφ : HasFDerivAt φ (0 : X →L[𝕜] E [⋀^ι]→L[𝕜] G) x) (h₀ : φ x = 0)
    (hL : ContinuousAt L x) :
    HasFDerivAt (fun y ↦ (φ y).compContinuousLinearMap (L y))
      (0 : X →L[𝕜] X' [⋀^ι]→L[𝕜] G) x := by
  have := Fintype.ofFinite ι
  have hc : (0 : E [⋀^ι]→L[𝕜] G).compContinuousLinearMap (L x) = 0 := by ext; simp
  rw [hasFDerivAt_iff_isLittleO] at hφ ⊢
  simp only [h₀, hc, sub_zero, zero_apply] at hφ ⊢
  refine Asymptotics.IsBigO.trans_isLittleO ?_ hφ
  -- Near `x`, the norms of the linear maps stay below `‖L x‖ + 1`.
  have hb : ∀ᶠ y in 𝓝 x, ‖L y‖ ≤ ‖L x‖ + 1 :=
    (hL.norm.eventually (gt_mem_nhds (lt_add_one ‖L x‖))).mono fun _ h ↦ h.le
  refine Asymptotics.IsBigO.of_bound ((‖L x‖ + 1) ^ Fintype.card ι) ?_
  filter_upwards [hb] with y hy
  calc ‖(φ y).compContinuousLinearMap (L y)‖ ≤ ‖φ y‖ * ‖L y‖ ^ Fintype.card ι :=
        ContinuousAlternatingMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖φ y‖ * (‖L x‖ + 1) ^ Fintype.card ι := by gcongr
    _ = (‖L x‖ + 1) ^ Fintype.card ι * ‖φ y‖ := mul_comm _ _
