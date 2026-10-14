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
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Smooth pullback of continuous alternating maps

Pullback on alternating maps is polynomial in the continuous linear map used on the
domain. When the arity factorial is nonzero, this follows from Mathlib's continuous multilinear
pullback: normalized alternatization recovers the alternating output. The result is
operator-valued, so it controls smooth coordinate changes of alternating-map bundles.

The regularity parameter includes the analytic order `ω`, as well as finite orders and
`∞`. The polynomial construction establishes all of these orders; comparison of first
derivatives alone does not establish the analytic case.

The underlying polynomial is Mathlib's
`ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear`.
-/

public section

noncomputable section

namespace TauCeti

variable {𝕜 E F G ι : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] [Fintype ι]
  [NeZero ((Fintype.card ι).factorial : 𝕜)]

/-- Pullback on continuous alternating maps is smooth, as an operator-valued function of
the continuous linear map on the domain, including at the analytic order `ω`. The arity
factorial is assumed nonzero. No completeness or finite dimensionality is needed. -/
theorem _root_.ContinuousAlternatingMap.contDiff_compContinuousLinearMapCLM (n : WithTop ℕ∞) :
    ContDiff 𝕜 n
      (ContinuousAlternatingMap.compContinuousLinearMapCLM :
        (E →L[𝕜] F) → (F [⋀^ι]→L[𝕜] G) →L[𝕜] E [⋀^ι]→L[𝕜] G) := by
  classical
  let A : ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) G →L[𝕜] E [⋀^ι]→L[𝕜] G :=
    ((Fintype.card ι).factorial : 𝕜)⁻¹ • ContinuousMultilinearMap.alternatizationCLM
  let J : (F [⋀^ι]→L[𝕜] G) →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F) G :=
    ContinuousAlternatingMap.toContinuousMultilinearMapCLM 𝕜
  let P := ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear
    𝕜 (fun _ : ι ↦ E) (fun _ : ι ↦ F) G
  have hP : ContDiff 𝕜 n (fun f : E →L[𝕜] F ↦ P (fun _ ↦ f)) :=
    P.contDiff.comp (contDiff_pi.mpr fun _ ↦ contDiff_id)
  have h : ContDiff 𝕜 n (fun f : E →L[𝕜] F ↦ (A.comp (P (fun _ ↦ f))).comp J) :=
    (contDiff_const.clm_comp hP).clm_comp contDiff_const
  convert h using 1
  ext f φ v
  -- Both inclusions use the underlying multilinear map; normalized alternatization
  -- returns the alternating pullback itself.
  simp only [A, J, P, ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousAlternatingMap.compContinuousLinearMapCLM_apply,
    ContinuousAlternatingMap.toContinuousMultilinearMapCLM_apply,
    ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear_apply_apply]
  rw [← ContinuousAlternatingMap.toContinuousMultilinearMap_compContinuousLinearMap,
    ContinuousMultilinearMap.alternatizationCLM_apply,
    ContinuousAlternatingMap.alternatization_toContinuousMultilinearMap,
    ← Nat.cast_smul_eq_nsmul 𝕜,
    inv_smul_smul₀ (NeZero.ne ((Fintype.card ι).factorial : 𝕜))]

end TauCeti
