/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Bases
import TauCeti.Analysis.Normed.Module.Bases.Block

/-!
# Subsequences of Schauder bases

Every strictly increasing subsequence of a Schauder basis is a Schauder basis of its
closed linear span. Its coordinate functionals are restrictions of the original coordinates,
and its initial projections agree with the original projections at the selected indices.
Consequently its basis constant is at most the original basis constant in a Banach space.

The construction is a special case of `SchauderBasis.blockBasis` with one basis vector per block.
It preserves conditional summation along initial segments and does not require completeness.

## References

* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, Chapter 1, basic sequences.
-/

public section

noncomputable section

open Set

namespace SchauderBasis

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  (b : SchauderBasis 𝕜 E) (u : ℕ → ℕ) (hu : StrictMono u)

include hu in
private theorem support_coord_subsequence (i : ℕ) :
    Function.support (fun k ↦ b.coord k (b (u i))) ⊆ Ico (u i) (u (i + 1)) := by
  intro k hk
  have heq : k = u i := by
    by_contra h
    exact hk (by simp [b.ortho, h])
  subst k
  exact ⟨le_rfl, hu (Nat.lt_succ_self i)⟩

/-- The basis of the closed span of a strictly increasing subsequence of a Schauder basis. -/
def subsequence : SchauderBasis 𝕜 (Submodule.span 𝕜 (range fun i ↦ b (u i))).topologicalClosure :=
  b.blockBasis (fun i ↦ b (u i)) u (fun i ↦ b.linearIndependent.ne_zero (u i))
    (b.support_coord_subsequence u hu)

/-- The vectors of the subsequence basis are the selected original basis vectors. -/
@[simp]
theorem coe_subsequence_apply (i : ℕ) :
    (b.subsequence u hu i : E) = b (u i) := by
  rw [subsequence, coe_blockBasis_apply]

/-- The coordinates of the subsequence basis are restrictions of the selected original
coordinates. -/
@[simp]
theorem subsequence_coord_apply
    (x : (Submodule.span 𝕜 (range fun i ↦ b (u i))).topologicalClosure) (i : ℕ) :
    (b.subsequence u hu).coord i x = b.coord (u i) (x : E) := by
  rw [subsequence, blockBasis_coord_eq_inv_mul (k := u i)]
  · simp [b.ortho]
  · simp [b.ortho]

/-- Initial projections of the subsequence basis are restrictions of the original projections
at the selected indices. -/
theorem coe_subsequence_proj (n : ℕ)
    (x : (Submodule.span 𝕜 (range fun i ↦ b (u i))).topologicalClosure) :
    ((b.subsequence u hu).proj n x : E) = b.proj (u n) (x : E) := by
  rw [subsequence, coe_blockBasis_proj]

/-- Restricting an initial projection to the subsequence span cannot increase its norm. -/
theorem norm_subsequence_proj_le (n : ℕ) :
    ‖(b.subsequence u hu).proj n‖ ≤ ‖b.proj (u n)‖ := by
  rw [subsequence]
  exact b.norm_blockBasis_proj_le ..

/-- The basis constant of a subsequence does not exceed the original basis constant. -/
theorem subsequence_nnnormProjBound_le [CompleteSpace E] :
    (b.subsequence u hu).nnNormProjBound ≤ b.nnNormProjBound := by
  rw [subsequence]
  exact b.blockBasis_nnNormProjBound_le ..

end SchauderBasis
