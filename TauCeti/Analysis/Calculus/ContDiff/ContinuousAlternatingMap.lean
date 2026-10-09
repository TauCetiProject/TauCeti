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
map by normalized alternatization over `ℝ`. The polynomial regularity API is developed by
Sophie Morel in `Mathlib.Analysis.Analytic.CPolynomial`. No completeness or finite-dimensionality
assumption is needed.
The regularity parameter ranges over `ℕ∞ω`, including analytic regularity `ω`.

Use `TauCeti.contDiff_continuousAlternatingMap_compContinuousLinearMapCLM
  (ι := ι) (E := E) (F := F) (G := G)`
to obtain smoothness of the pullback operator; the regularity `n` is inferred from the goal.
-/

public noncomputable section

namespace TauCeti

open _root_.ContinuousAlternatingMap
open scoped ContDiff

variable {ι E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [Fintype ι]
  {n : ℕ∞ω}

/-- Pullback over `ℝ` depends smoothly on the linear map, in the operator norm on
alternating maps. -/
theorem contDiff_continuousAlternatingMap_compContinuousLinearMapCLM :
    ContDiff ℝ n
      (compContinuousLinearMapCLM : (E →L[ℝ] F) →
        (F [⋀^ι]→L[ℝ] G) →L[ℝ] E [⋀^ι]→L[ℝ] G) := by
  classical
  -- Alternatization restricts to factorial multiplication on alternating maps, so its
  -- normalization is a left inverse of their inclusion into multilinear maps.
  let P : ContinuousMultilinearMap ℝ (fun _ : ι ↦ E) G →L[ℝ] E [⋀^ι]→L[ℝ] G :=
    ((Fintype.card ι).factorial : ℝ)⁻¹ • continuousMultilinearMapAlternatizationCLM
  let Q := ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear
    ℝ (fun _ : ι ↦ E) (fun _ ↦ F) G
  have hQ : ContDiff ℝ n (fun g : E →L[ℝ] F ↦ Q (fun _ ↦ g)) :=
    Q.analyticOnNhd.contDiff.comp (contDiff_pi.mpr fun _ ↦ contDiff_id)
  have h := contDiff_const (c := P) |>.clm_comp
    (hQ.clm_comp (contDiff_const (c := toContinuousMultilinearMapCLM ℝ)))
  have hQ_apply (g : E →L[ℝ] F) (f : F [⋀^ι]→L[ℝ] G) :
      Q (fun _ ↦ g) (toContinuousMultilinearMapCLM ℝ f) =
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
    hQ_apply, continuousMultilinearMapAlternatizationCLM_apply,
    continuousAlternatingMap_alternatization_toContinuousMultilinearMap,
    compContinuousLinearMapCLM_apply]
  rw [← Nat.cast_smul_eq_nsmul ℝ, inv_smul_smul₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _) :
    ((Fintype.card ι).factorial : ℝ) ≠ 0)]

end TauCeti
