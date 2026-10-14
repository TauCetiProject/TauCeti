/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.Alternating.Alternatization
public import TauCeti.Topology.Algebra.Module.Alternating.Basic
public import TauCeti.Data.Nat.Factorial.Basic
public import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
public import TauCeti.Analysis.Calculus.ContDiff.LinearIsometry

/-!
# Smooth pullback of continuous alternating maps

Mathlib's multilinear pullback is polynomial in the continuous linear map used on the
domain. For finite orders and `∞`, smoothness follows from Mathlib's continuous multilinear
pullback and reflection through the closed isometric inclusion. At the analytic order `ω`,
normalized alternatization recovers the alternating output when the arity factorial is nonzero.
The result is operator-valued, so it controls smooth coordinate changes of alternating-map bundles.

The regularity parameter includes the analytic order `ω`, as well as finite orders and
`∞`. The polynomial construction proves the analytic case under the factorial hypothesis;
comparison of first derivatives alone does not establish that case.

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
  have hI : IsClosed (range I) := by
    have hr : range I = {T | ∀ a, T a ∈ range J} := by
      ext T
      constructor
      · rintro ⟨A, rfl⟩ a
        exact ⟨A a, rfl⟩
      · intro hT
        let A := ContinuousAlternatingMap.liftCLM T (by
          intro a v i j hv hij
          obtain ⟨a', ha'⟩ := hT a
          rw [← ha']
          exact a'.map_eq_zero_of_eq v hv hij)
        exact ⟨A, by ext a v; rfl⟩
    rw [hr]
    simp only [ofPred_forall]
    have hJ : IsClosed (range J) :=
      ContinuousAlternatingMap.isClosed_range_toContinuousMultilinearMap
        (𝕜 := 𝕜) (E := E) (F := G) (ι := ι)
    exact isClosed_iInter fun a ↦ hJ.preimage (continuous_eval_const a)
  apply (LinearIsometry.contDiff_comp_iff I hI (n := n)
    (f := ContinuousAlternatingMap.compContinuousLinearMapCLM)).mp
  let K := ContinuousAlternatingMap.toContinuousMultilinearMapCLM
    (𝕜 := 𝕜) (E := F) (F := G) (ι := ι) 𝕜
  let P := ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear
    𝕜 (fun _ : ι ↦ E) (fun _ : ι ↦ F) G
  have hP : ContDiff 𝕜 n (fun f : E →L[𝕜] F ↦ P (fun _ ↦ f)) :=
    P.contDiff.comp (contDiff_pi.mpr fun _ ↦ contDiff_id)
  convert hP.clm_comp (contDiff_const (c := K)) using 1
  ext f a v
  rfl

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
      P.contDiff.comp (contDiff_pi.mpr fun _ ↦ contDiff_id)
    have h : ContDiff 𝕜 ω (fun f : E →L[𝕜] F ↦ (A.comp (P (fun _ ↦ f))).comp J) :=
      (contDiff_const.clm_comp hP).clm_comp contDiff_const
    convert h using 1
    ext f φ v
    -- Both inclusions use the underlying multilinear map; normalized alternatization
    -- returns the alternating pullback itself.
    simp only [A, J, P, ContinuousLinearMap.comp_apply, _root_.smul_apply,
      ContinuousAlternatingMap.smul_apply,
      ContinuousAlternatingMap.compContinuousLinearMapCLM_apply,
      ContinuousAlternatingMap.toContinuousMultilinearMapCLM_apply,
      ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear_apply_apply]
    rw [← ContinuousAlternatingMap.toContinuousMultilinearMap_compContinuousLinearMap,
      ContinuousMultilinearMap.alternatizationCLM_apply,
      ContinuousAlternatingMap.alternatization_toContinuousMultilinearMap,
      ← Nat.cast_smul_eq_nsmul 𝕜, ContinuousAlternatingMap.smul_apply,
      inv_smul_smul₀ (NeZero.ne ((Fintype.card ι).factorial : 𝕜))]
  | (n : ℕ∞) => exact contDiff_compContinuousLinearMapCLM_coe n
