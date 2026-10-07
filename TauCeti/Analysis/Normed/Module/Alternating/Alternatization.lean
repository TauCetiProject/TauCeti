/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Alternating.Basic
public import Mathlib.Analysis.Normed.Module.Multilinear.Curry

/-!
# Continuous linear alternatization

Mathlib's `ContinuousMultilinearMap.alternatization` is the signed sum over permutations.
Here it is bundled as a continuous linear map, so it can transport regularity of families
of multilinear maps. Its restriction to alternating maps is multiplication by the factorial
of the number of arguments. No division or characteristic assumption is needed.

The construction uses Mathlib's alternatization, developed by Yury Kudryashov.
-/

public noncomputable section

namespace TauCeti

variable {𝕜 ι E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [Fintype ι] [DecidableEq ι]

/-- The signed permutation sum has operator norm at most the factorial of its degree. -/
theorem norm_alternatization_le (f : ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) F) :
    ‖ContinuousMultilinearMap.alternatization f‖ ≤ (Fintype.card ι).factorial * ‖f‖ := by
  rw [← ContinuousAlternatingMap.norm_toContinuousMultilinearMap]
  calc
    _ ≤ ∑ σ : Equiv.Perm ι, ‖Equiv.Perm.sign σ • f.domDomCongr σ‖ :=
      norm_sum_le _ _
    _ = (Fintype.card ι).factorial * ‖f‖ := by
      simp [ContinuousMultilinearMap.norm_domDomCongr,
        Fintype.card_perm, nsmul_eq_mul]

/-- Mathlib's unnormalized alternatization, bundled as a continuous linear map. -/
def alternatizationCLM :
    ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) F →L[𝕜] E [⋀^ι]→L[𝕜] F :=
  LinearMap.mkContinuous
    { toFun := ContinuousMultilinearMap.alternatization
      map_add' := map_add _
      map_smul' := by
        intro c f
        ext v
        simp only [ContinuousMultilinearMap.alternatization_apply_apply,
          smul_apply, ContinuousAlternatingMap.smul_apply,
          Finset.smul_sum]
        exact Finset.sum_congr rfl fun σ _ ↦ smul_comm _ _ _ }
    (Fintype.card ι).factorial norm_alternatization_le

/-- Evaluation of the continuous linear alternatization is the existing signed sum. -/
@[simp]
theorem alternatizationCLM_apply (f : ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) F) :
    alternatizationCLM f = ContinuousMultilinearMap.alternatization f := (rfl)

/-- Alternatization multiplies an already alternating map by its degree factorial. -/
@[simp]
theorem alternatization_toContinuousMultilinearMap (f : E [⋀^ι]→L[𝕜] F) :
    ContinuousMultilinearMap.alternatization f.toContinuousMultilinearMap =
      (Fintype.card ι).factorial • f := by
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  simp only [ContinuousMultilinearMap.alternatization_apply_toAlternatingMap,
    ContinuousAlternatingMap.toAlternatingMap_smul]
  exact AlternatingMap.coe_alternatization f.toAlternatingMap

end TauCeti
