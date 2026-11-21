/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Bases

/-!
# Block bases of Schauder bases

A sequence of nonzero finite linear combinations of a Schauder basis, supported in
successive disjoint intervals, is a Schauder basis of its closed linear span.
`SchauderBasis.blockBasis` constructs this basis from finitely supported coefficient
vectors. Its initial projections are restrictions of the original initial projections
at the block boundaries, so its basis constant cannot increase.

The construction uses convergence along initial segments, not unconditional summation.
Neither the construction nor its projection identities requires completeness.

## References

* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, Chapter 1, basic sequences.
-/

public section

noncomputable section

open Filter Set
open scoped Topology

namespace SchauderBasis

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  (b : SchauderBasis 𝕜 E) (a : ℕ → ℕ →₀ 𝕜) (u : ℕ → ℕ)
  (hu : StrictMono u) (ha : ∀ n, a n ≠ 0)
  (hs : ∀ n, (a n).support ⊆ Finset.Ico (u n) (u (n + 1)))

private def blockFunctional (n : ℕ) : StrongDual 𝕜 E :=
  let k := ((Finsupp.support_nonempty_iff.mpr (ha n)).choose)
  (a n k)⁻¹ • b.coord k

include hu hs in
private theorem blockFunctional_apply (i j : ℕ) :
    b.blockFunctional a ha i (Finsupp.linearCombination 𝕜 b (a j)) =
      (Pi.single j (1 : 𝕜) : ℕ → 𝕜) i := by
  classical
  let k := (Finsupp.support_nonempty_iff.mpr (ha i)).choose
  have hk : k ∈ (a i).support := (Finsupp.support_nonempty_iff.mpr (ha i)).choose_spec
  have hki := Finset.mem_Ico.mp (hs i hk)
  have heval : b.coord k (Finsupp.linearCombination 𝕜 b (a j)) = a j k := by
    by_cases h : a j k = 0 <;>
      simp [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, b.ortho,
        Pi.single_apply, h]
  have hzero (hij : i ≠ j) : a j k = 0 := by
    by_contra h
    have hkj := Finset.mem_Ico.mp (hs j (Finsupp.mem_support_iff.mpr h))
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · have hun : u (i + 1) ≤ u j := hu.monotone (by omega)
      omega
    · have hun : u (j + 1) ≤ u i := hu.monotone (by omega)
      omega
  have hfinal : (a i k)⁻¹ * b.coord k (Finsupp.linearCombination 𝕜 b (a j)) =
      (Pi.single j (1 : 𝕜) : ℕ → 𝕜) i := by
    rw [heval, Pi.single_apply]
    split_ifs with hij
    · subst j
      exact inv_mul_cancel₀ (Finsupp.mem_support_iff.mp hk)
    · rw [hzero hij, mul_zero]
  simpa only [k, blockFunctional, smul_apply, smul_eq_mul] using hfinal

include hu hs in
private theorem proj_block (n j : ℕ) :
    b.proj (u n) (Finsupp.linearCombination 𝕜 b (a j)) =
      if j < n then Finsupp.linearCombination 𝕜 b (a j) else 0 := by
  classical
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul]
  split_ifs with hj
  · apply Finset.sum_congr rfl
    intro k hk
    have hku := (Finset.mem_Ico.mp (hs j hk)).2
    have hun := hu.monotone (Nat.succ_le_of_lt hj)
    rw [proj_apply_basis_mem, ite_eq_left (lt_of_lt_of_le hku hun)]
  · apply Finset.sum_eq_zero
    intro k hk
    have hku := (Finset.mem_Ico.mp (hs j hk)).1
    have hun := hu.monotone (Nat.le_of_not_gt hj)
    rw [proj_apply_basis_mem, ite_eq_right (by omega), smul_zero]

include hu hs in
private theorem sum_blockFunctional_eq_proj (n : ℕ)
    (x : (Submodule.span 𝕜 (range fun j ↦
      Finsupp.linearCombination 𝕜 b (a j))).topologicalClosure) :
    ∑ i ∈ Finset.range n, b.blockFunctional a ha i (x : E) •
      Finsupp.linearCombination 𝕜 b (a i) = b.proj (u n) x := by
  classical
  let P : E →L[𝕜] E := ∑ i ∈ Finset.range n,
    (b.blockFunctional a ha i).smulRight (Finsupp.linearCombination 𝕜 b (a i))
  have h : EqOn P (b.proj (u n))
      (range fun j ↦ Finsupp.linearCombination 𝕜 b (a j)) := by
    rintro _ ⟨j, rfl⟩
    simp [P, b.blockFunctional_apply a u hu ha hs, b.proj_block a u hu hs,
      Pi.single_apply]
  have hx := ContinuousLinearMap.eqOn_closure_span h x.property
  simpa only [P, sum_apply, ContinuousLinearMap.smulRight_apply] using hx

/-- The Schauder basis of the closed span of successive nonzero blocks of `b`.
The coefficient vector `a n` is supported in `[u n, u (n + 1))`; gaps and
unnormalized blocks are allowed. -/
def blockBasis :
    SchauderBasis 𝕜 (Submodule.span 𝕜 (range fun j ↦
      Finsupp.linearCombination 𝕜 b (a j))).topologicalClosure where
  basis j := ⟨Finsupp.linearCombination 𝕜 b (a j), Submodule.le_topologicalClosure _
    (Submodule.subset_span (mem_range_self j))⟩
  coord i := (b.blockFunctional a ha i).comp (Submodule.subtypeL _)
  ortho i j := by
    by_cases hij : i = j <;>
      simpa [Pi.single_apply, hij] using b.blockFunctional_apply a u hu ha hs i j
  expansion x := by
    rw [HasSum, SummationFilter.conditional_filter_eq_map_range, tendsto_map'_iff]
    apply tendsto_subtype_rng.mpr
    simpa only [Function.comp_def, Submodule.coe_sum, Submodule.coe_smul_of_tower,
      ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
      b.sum_blockFunctional_eq_proj a u hu ha hs] using
      (b.tendsto_proj (x : E)).comp hu.tendsto_atTop

/-- The vectors of the block basis are the prescribed finite combinations. -/
@[simp]
theorem coe_blockBasis_apply (j : ℕ) :
    (b.blockBasis a u hu ha hs j : E) = Finsupp.linearCombination 𝕜 b (a j) := (rfl)

/-- Initial projections of a block basis agree with the original projections at its
block boundaries, on the closed block span. -/
theorem coe_blockBasis_proj (n : ℕ)
    (x : (Submodule.span 𝕜 (range fun j ↦
      Finsupp.linearCombination 𝕜 b (a j))).topologicalClosure) :
    ((b.blockBasis a u hu ha hs).proj n x : E) = b.proj (u n) (x : E) := by
  rw [proj_apply]
  simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower,
    blockBasis, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
    b.sum_blockFunctional_eq_proj a u hu ha hs]

/-- A block coordinate times its block vector is the difference of the original
projections at the two endpoints. This characterizes the coordinates independently
of any choice of a nonzero coefficient within each block. -/
theorem blockBasis_coord_smul (n : ℕ)
    (x : (Submodule.span 𝕜 (range fun j ↦
      Finsupp.linearCombination 𝕜 b (a j))).topologicalClosure) :
    (b.blockBasis a u hu ha hs).coord n x • Finsupp.linearCombination 𝕜 b (a n) =
      b.proj (u (n + 1)) (x : E) - b.proj (u n) (x : E) := by
  have h : (b.blockBasis a u hu ha hs).proj (n + 1) x =
      (b.blockBasis a u hu ha hs).proj n x +
        (b.blockBasis a u hu ha hs).coord n x • b.blockBasis a u hu ha hs n := by
    simp only [proj_apply, Finset.sum_range_succ]
  have hcoe := congrArg (Submodule.subtype _) h
  simp only [Submodule.subtype_apply, Submodule.coe_add, Submodule.coe_smul_of_tower,
    coe_blockBasis_apply, coe_blockBasis_proj] at hcoe
  exact eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using hcoe.symm)

/-- Restricting an initial projection to the closed block span cannot increase its norm. -/
theorem norm_blockBasis_proj_le (n : ℕ) :
    ‖(b.blockBasis a u hu ha hs).proj n‖ ≤ ‖b.proj (u n)‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  simpa only [← Submodule.norm_coe, coe_blockBasis_proj] using
    (b.proj (u n)).le_opNorm (x : E)

/-- The basis constant of a block basis is at most the original basis constant. -/
theorem blockBasis_nnNormProjBound_le [CompleteSpace E] :
    (b.blockBasis a u hu ha hs).nnNormProjBound ≤ b.nnNormProjBound := by
  apply ciSup_le
  intro n
  exact_mod_cast (b.norm_blockBasis_proj_le a u hu ha hs n).trans
    (b.norm_proj_le_nnNormProjBound (u n))

end SchauderBasis
