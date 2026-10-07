/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.Alternating.Alternatization
public import Mathlib.Analysis.Analytic.CPolynomial
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Smooth pullback of continuous alternating maps

Pullback of an alternating map along a continuous linear map depends smoothly on the
linear map, also as an operator on alternating maps. This is the flat regularity fact
needed for the smooth bundle of alternating maps.

We use Mathlib's polynomial description of multilinear pullback and recover the alternating
map by normalized alternatization. We only require the degree factorial to be nonzero in the
scalar field; no completeness or finite-dimensionality assumption is needed.
Over a characteristic-zero field, this condition follows from `Nat.factorial_ne_zero`.
In positive characteristic, it permits degrees whose factorial has nonzero cast.
-/

public noncomputable section

namespace TauCeti

open ContinuousAlternatingMap
open scoped ContDiff

variable {𝕜 ι E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] [Fintype ι]
  [NeZero ((Fintype.card ι).factorial : 𝕜)] {n : ℕ∞ω}

/-- When the degree factorial is nonzero in the scalar field, pullback depends smoothly
on the linear map, in the operator norm on alternating maps. -/
theorem contDiff_compContinuousLinearMapCLM :
    ContDiff 𝕜 n
      (compContinuousLinearMapCLM : (E →L[𝕜] F) →
        (F [⋀^ι]→L[𝕜] G) →L[𝕜] E [⋀^ι]→L[𝕜] G) := by
  classical
  let P : ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) G →L[𝕜] E [⋀^ι]→L[𝕜] G :=
    ((Fintype.card ι).factorial : 𝕜)⁻¹ • alternatizationCLM
  let Q := ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear
    𝕜 (fun _ : ι ↦ E) (fun _ ↦ F) G
  have hQ : ContDiff 𝕜 n (fun g : E →L[𝕜] F ↦ Q (fun _ ↦ g)) :=
    Q.analyticOnNhd.contDiff.comp (contDiff_pi.mpr fun _ ↦ contDiff_id)
  have h := contDiff_const (c := P) |>.clm_comp
    (hQ.clm_comp (contDiff_const (c := toContinuousMultilinearMapCLM 𝕜)))
  have hQ_apply (g : E →L[𝕜] F) (f : F [⋀^ι]→L[𝕜] G) :
      Q (fun _ ↦ g) (toContinuousMultilinearMapCLM 𝕜 f) =
        (f.compContinuousLinearMap g).toContinuousMultilinearMap := by
    ext v
    simp only [Q,
      ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear_apply_apply,
      toContinuousMultilinearMapCLM_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply, coe_toContinuousMultilinearMap,
      compContinuousLinearMap_apply, Function.comp_def]
  convert h using 1
  funext g
  ext1 f
  simp only [ContinuousLinearMap.comp_apply, P, _root_.smul_apply,
    hQ_apply, alternatizationCLM_apply, alternatization_toContinuousMultilinearMap,
    compContinuousLinearMapCLM_apply]
  rw [← Nat.cast_smul_eq_nsmul 𝕜, inv_smul_smul₀ (NeZero.ne _)]

end TauCeti
