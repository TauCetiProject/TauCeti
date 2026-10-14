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

Mathlib's `ContinuousMultilinearMap.alternatization` is the signed permutation sum.
Here it is bundled as a continuous linear map, with its factorial norm bound and its
value on alternating maps. Dividing by the factorial gives a retraction onto alternating
maps when the factorial is nonzero in the scalar field, useful for transporting smoothness
from multilinear maps.

The construction uses Yury Kudryashov's alternatization in
`Mathlib.Topology.Algebra.Module.Alternating.Basic`.
-/

public section

noncomputable section

namespace TauCeti

variable {𝕜 E F ι : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [Fintype ι] [DecidableEq ι]

/-- The signed permutation sum has operator norm at most the factorial of the arity. -/
theorem _root_.ContinuousMultilinearMap.norm_alternatization_le
    (f : ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) F) :
    ‖ContinuousMultilinearMap.alternatization f‖ ≤ (Fintype.card ι).factorial * ‖f‖ := by
  rw [← ContinuousAlternatingMap.norm_toContinuousMultilinearMap]
  simp only [ContinuousMultilinearMap.alternatization_apply_toContinuousMultilinearMap]
  calc
    _ ≤ ∑ σ : Equiv.Perm ι, ‖Equiv.Perm.sign σ • f.domDomCongr σ‖ := norm_sum_le _ _
    _ = (Fintype.card ι).factorial * ‖f‖ := by simp [Fintype.card_perm]

/-- Alternatization, the signed sum over permutations, as a continuous linear map. -/
def alternatizationCLM :
    ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) F →L[𝕜] E [⋀^ι]→L[𝕜] F :=
  LinearMap.mkContinuous
    { toFun := ContinuousMultilinearMap.alternatization
      map_add' := map_add _
      map_smul' := by
        intro c f
        ext v
        simp [ContinuousMultilinearMap.alternatization_apply_apply, Finset.smul_sum,
          smul_comm c] }
    (Fintype.card ι).factorial ContinuousMultilinearMap.norm_alternatization_le

/-- The continuous linear alternatization evaluates to Mathlib's signed permutation sum. -/
@[simp] theorem _root_.ContinuousMultilinearMap.alternatizationCLM_apply
    (f : ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) F) :
    alternatizationCLM f = ContinuousMultilinearMap.alternatization f := (rfl)

/-- Alternatization multiplies an alternating map by the factorial of its arity. -/
@[simp] theorem _root_.ContinuousAlternatingMap.alternatization_toContinuousMultilinearMap
    (f : E [⋀^ι]→L[𝕜] F) :
    ContinuousMultilinearMap.alternatization f.toContinuousMultilinearMap =
      (Fintype.card ι).factorial • f := by
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  simp only [ContinuousMultilinearMap.alternatization_apply_toAlternatingMap,
    ContinuousAlternatingMap.toAlternatingMap_smul]
  exact AlternatingMap.coe_alternatization f.toAlternatingMap

end TauCeti
