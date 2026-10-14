/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Alternating.Basic

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

namespace ContinuousMultilinearMap

variable {𝕜 E F ι : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] [Fintype ι] [DecidableEq ι]

/-- The signed permutation sum has operator norm at most the factorial of the arity. -/
theorem norm_alternatization_le
    (f : ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) F) :
    ‖ContinuousMultilinearMap.alternatization f‖ ≤ (Fintype.card ι).factorial * ‖f‖ := by
  rw [← ContinuousAlternatingMap.norm_toContinuousMultilinearMap]
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m ↦ ?_
  change ‖ContinuousMultilinearMap.alternatization f m‖ ≤ _
  rw [ContinuousMultilinearMap.alternatization_apply_apply]
  calc
    _ ≤ ∑ σ : Equiv.Perm ι, ‖Equiv.Perm.sign σ • f (m ∘ σ)‖ := norm_sum_le _ _
    _ = ∑ σ : Equiv.Perm ι, ‖f (m ∘ σ)‖ := by simp only [norm_units_zsmul]
    _ ≤ ∑ _σ : Equiv.Perm ι, ‖f‖ * ∏ i, ‖m i‖ := by
      apply Finset.sum_le_sum
      intro σ _
      simpa only [Function.comp_apply, Equiv.prod_comp σ (fun i ↦ ‖m i‖)] using
        f.le_opNorm (m ∘ σ)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, nsmul_eq_mul,
        mul_assoc]

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
@[simp] theorem alternatizationCLM_apply
    (f : ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) F) :
    alternatizationCLM f = ContinuousMultilinearMap.alternatization f := (rfl)


end ContinuousMultilinearMap
