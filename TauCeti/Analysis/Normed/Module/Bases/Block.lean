/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Bases

/-!
# Block bases of Schauder bases

A sequence of nonzero vectors whose Schauder coordinates are supported in successive disjoint
intervals is a Schauder basis of its closed linear span. `SchauderBasis.blockBasis` constructs
this basis. Its initial projections are restrictions of the original initial projections at the
block boundaries, so its basis constant cannot increase.

The construction uses convergence along initial segments, not unconditional summation.
Neither the construction nor its projection identities requires completeness.

## References

* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, Chapter 1, basic sequences.
* The closed-span projection argument and basis-constant estimate follow `SchauderBasis.subsequence`
  in `TauCeti/Analysis/Normed/Module/Bases/Subsequence.lean`. The basis is constructed using
  Mathlib's `SchauderBasis.RankOneDecomposition.basis`.
-/

public section

noncomputable section

open Filter Set
open scoped Topology

namespace SchauderBasis

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  (b : SchauderBasis 𝕜 E) (v : ℕ → E) (u : ℕ → ℕ)
  (hv : ∀ n, v n ≠ 0)
  (hs : ∀ n, Function.support (fun k ↦ b.coord k (v n)) ⊆ Ico (u n) (u (n + 1)))

variable (𝕜) in
private abbrev blockSpan := (Submodule.span 𝕜 (range v)).topologicalClosure

include hs in
private theorem coord_block_eq_zero (j : ℕ) {k : ℕ} (hk : k ∉ Ico (u j) (u (j + 1))) :
    b.coord k (v j) = 0 := by
  by_contra h
  exact hk (hs j h)

include hv in
private theorem exists_ne_zero_coord_block (j : ℕ) : ∃ k, b.coord k (v j) ≠ 0 := by
  by_contra! h
  have heq (n : ℕ) : b.proj n (v j) = 0 := by simp [proj_apply, h]
  exact hv j (tendsto_nhds_unique (b.tendsto_proj (v j)) (by simpa only [heq] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : E)) atTop (𝓝 0))))

include hv hs in
private theorem strictMono_blockBoundaries : StrictMono u := by
  refine strictMono_nat_of_lt_succ fun j ↦ ?_
  obtain ⟨k, hk⟩ := b.exists_ne_zero_coord_block v hv j
  exact ((hs j hk).1).trans_lt (hs j hk).2

include hv hs in
private theorem proj_block (n j : ℕ) :
    b.proj (u n) (v j) = if j < n then v j else 0 := by
  have hu := b.strictMono_blockBoundaries v u hv hs
  split_ifs with hj
  · have heq (m : ℕ) (hm : u n ≤ m) : b.proj m (v j) = b.proj (u n) (v j) := by
      simp only [proj_apply]
      symm
      apply Finset.sum_subset (Finset.range_mono hm)
      intro k _ hk
      rw [b.coord_block_eq_zero v u hs j (fun h ↦ hk (Finset.mem_range.mpr
        (h.2.trans_le (hu.monotone (Nat.succ_le_of_lt hj))))), zero_smul]
    have ht := tendsto_const_nhds.congr' <|
      (eventually_ge_atTop (u n)).mono fun m hm ↦ (heq m hm).symm
    exact (tendsto_nhds_unique (b.tendsto_proj (v j)) ht).symm
  · rw [proj_apply]
    apply Finset.sum_eq_zero
    intro k hk
    rw [b.coord_block_eq_zero v u hs j (fun h ↦
      (not_lt_of_ge ((hu.monotone (le_of_not_gt hj)).trans h.1)) (Finset.mem_range.mp hk)),
      zero_smul]

private def blockFunctional (i : ℕ) : StrongDual 𝕜 E :=
  let k := (b.exists_ne_zero_coord_block v hv i).choose
  (b.coord k (v i))⁻¹ • b.coord k

include hv hs in
private theorem blockFunctional_apply (i j : ℕ) :
    b.blockFunctional v hv i (v j) = (Pi.single j (1 : 𝕜) : ℕ → 𝕜) i := by
  let k := (b.exists_ne_zero_coord_block v hv i).choose
  have hk : b.coord k (v i) ≠ 0 := (b.exists_ne_zero_coord_block v hv i).choose_spec
  have hi := hs i hk
  have hu := b.strictMono_blockBoundaries v u hv hs
  simp only [blockFunctional, smul_apply, smul_eq_mul, Pi.single_apply]
  split_ifs with hij
  · subst j
    exact inv_mul_cancel₀ hk
  · have hout : k ∉ Ico (u j) (u (j + 1)) := by
      intro hj
      rcases lt_or_gt_of_ne hij with h | h
      · exact hi.2.not_ge ((hu.monotone (Nat.succ_le_of_lt h)).trans hj.1)
      · exact hj.2.not_ge ((hu.monotone (Nat.succ_le_of_lt h)).trans hi.1)
    rw [b.coord_block_eq_zero v u hs j hout, mul_zero]

private def blockVector (j : ℕ) : blockSpan 𝕜 v :=
  ⟨v j, Submodule.le_topologicalClosure _ (Submodule.subset_span (mem_range_self j))⟩

include hv hs in
private theorem proj_eq_sum_block (n : ℕ) (x : blockSpan 𝕜 v) :
    b.proj (u n) x = ∑ i ∈ Finset.range n, b.blockFunctional v hv i (x : E) • v i := by
  classical
  let P : E →L[𝕜] E := ∑ i ∈ Finset.range n, (b.blockFunctional v hv i).smulRight (v i)
  have h : EqOn (b.proj (u n)) P (range v) := by
    rintro _ ⟨j, rfl⟩
    simp [P, b.blockFunctional_apply v u hv hs, b.proj_block v u hv hs, Pi.single_apply]
  simpa only [P, sum_apply, ContinuousLinearMap.smulRight_apply] using
    ContinuousLinearMap.eqOn_closure_span h x.property

private def blockProj (n : ℕ) : blockSpan 𝕜 v →L[𝕜] blockSpan 𝕜 v :=
  (b.proj (u n)).restrict fun x hx ↦ by
    rw [b.proj_eq_sum_block v u hv hs n ⟨x, hx⟩]
    exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (blockVector v i).property

include hv hs in
private theorem blockProj_apply_blockVector (n j : ℕ) :
    b.blockProj v u hv hs n (blockVector v j) = if j < n then blockVector v j else 0 := by
  apply Subtype.ext
  simpa only [blockProj, ContinuousLinearMap.coe_restrict_apply, blockVector, apply_ite,
    Submodule.coe_zero] using b.proj_block v u hv hs n j

include hv hs in
private theorem finrank_blockProj (n : ℕ) :
    Module.finrank 𝕜 (b.blockProj v u hv hs n).toLinearMap.range = n := by
  let w : Fin n → blockSpan 𝕜 v := fun i ↦ blockVector v i
  have hrange : (b.blockProj v u hv hs n).toLinearMap.range = Submodule.span 𝕜 (range w) := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      have heq : b.blockProj v u hv hs n x =
          ∑ i ∈ Finset.range n, b.blockFunctional v hv i (x : E) • blockVector v i := by
        apply Subtype.ext
        simpa only [blockProj, ContinuousLinearMap.coe_restrict_apply, Submodule.coe_sum,
          Submodule.coe_smul_of_tower, blockVector] using b.proj_eq_sum_block v u hv hs n x
      rw [ContinuousLinearMap.coe_coe, heq]
      exact Submodule.sum_mem _ fun i hi ↦ Submodule.smul_mem _ _
        (Submodule.subset_span (mem_range_self (⟨i, Finset.mem_range.mp hi⟩ : Fin n)))
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact ⟨w i, by simp [w, b.blockProj_apply_blockVector v u hv hs, i.isLt]⟩
  have hind : LinearIndependent 𝕜 w := by
    let f : blockSpan 𝕜 v →ₗ[𝕜] (Fin n → 𝕜) := LinearMap.pi fun i ↦
      (b.blockFunctional v hv i).toLinearMap.comp (blockSpan 𝕜 v).subtype
    apply LinearIndependent.of_comp f
    have hf : f ∘ w = fun i ↦ Pi.single i (1 : 𝕜) := by
      funext j i
      simp [f, w, blockVector, b.blockFunctional_apply v u hv hs, Pi.single_apply, Fin.val_inj]
    rw [hf]
    exact Pi.linearIndependent_single_one _ _
  rw [hrange, finrank_span_eq_card hind, Fintype.card_fin]

private def blockDecomposition : RankOneDecomposition 𝕜 (blockSpan 𝕜 v) where
  P := b.blockProj v u hv hs
  e := blockVector v
  proj_zero := by
    ext x
    simpa only [blockProj, ContinuousLinearMap.coe_restrict_apply, zero_apply,
      Submodule.coe_zero, Finset.range_zero, Finset.sum_empty] using
      b.proj_eq_sum_block v u hv hs 0 x
  finrank_range := b.finrank_blockProj v u hv hs
  proj_comp n m x := by
    apply Subtype.ext
    simpa only [blockProj, ContinuousLinearMap.coe_restrict_apply,
      (b.strictMono_blockBoundaries v u hv hs).monotone.map_min] using
      b.proj_comp (u n) (u m) (x : E)
  proj_tendsto x := tendsto_subtype_rng.mpr <| by
    simpa only [Function.comp_def, blockProj, ContinuousLinearMap.coe_restrict_apply] using
      (b.tendsto_proj (x : E)).comp (b.strictMono_blockBoundaries v u hv hs).tendsto_atTop
  e_mem_range n := ⟨blockVector v n, by
    simp [succSub, b.blockProj_apply_blockVector v u hv hs]⟩
  e_ne_zero n h := hv n (congrArg Subtype.val h)

/-- The Schauder basis of the closed span of successive nonzero blocks of `b`.
The coordinates of `v n` vanish outside `[u n, u (n + 1))`; gaps and unnormalized blocks are
allowed. -/
def blockBasis : SchauderBasis 𝕜 (Submodule.span 𝕜 (range v)).topologicalClosure :=
  (b.blockDecomposition v u hv hs).basis

/-- The vectors of the block basis are the prescribed blocks. -/
@[simp]
theorem coe_blockBasis_apply (j : ℕ) : (b.blockBasis v u hv hs j : E) = v j := (rfl)

/-- Initial projections of a block basis agree with the original projections at its
block boundaries, on the closed block span. -/
theorem coe_blockBasis_proj (n : ℕ)
    (x : (Submodule.span 𝕜 (range v)).topologicalClosure) :
    ((b.blockBasis v u hv hs).proj n x : E) = b.proj (u n) (x : E) := by
  rw [blockBasis, RankOneDecomposition.basis_proj]
  rfl

/-- A block coordinate times its block vector is the difference of the original
projections at the two endpoints. -/
theorem blockBasis_coord_smul (n : ℕ)
    (x : (Submodule.span 𝕜 (range v)).topologicalClosure) :
    (b.blockBasis v u hv hs).coord n x • v n =
      b.proj (u (n + 1)) (x : E) - b.proj (u n) (x : E) := by
  exact congrArg Subtype.val ((b.blockDecomposition v u hv hs).basisCoeff_spec n x)

/-- Within a block interval, an ambient coordinate is the block coordinate times the
corresponding coordinate of the block vector. -/
theorem coord_eq_blockBasis_coord_mul (n : ℕ)
    (x : (Submodule.span 𝕜 (range v)).topologicalClosure) {k : ℕ}
    (hk : k ∈ Ico (u n) (u (n + 1))) :
    b.coord k (x : E) = (b.blockBasis v u hv hs).coord n x * b.coord k (v n) := by
  classical
  have h := congrArg (b.coord k) (b.blockBasis_coord_smul v u hv hs n x)
  simpa [proj_apply, map_sum, b.ortho, Pi.single_apply, Finset.mem_range, hk.2, hk.1.not_gt]
    using h.symm

include hv hs in
/-- Ambient coordinates before the first block vanish on the closed block span. -/
theorem coord_eq_zero_of_lt_block_start (x : (Submodule.span 𝕜 (range v)).topologicalClosure)
    {k : ℕ} (hk : k < u 0) :
    b.coord k (x : E) = 0 := by
  have hu := b.strictMono_blockBoundaries v u hv hs
  have h : EqOn (b.coord k) (0 : StrongDual 𝕜 E) (range v) := by
    rintro _ ⟨j, rfl⟩
    exact b.coord_block_eq_zero v u hs j fun hj ↦
      (not_lt_of_ge ((hu.monotone (Nat.zero_le j)).trans hj.1)) hk
  exact ContinuousLinearMap.eqOn_closure_span h x.property

/-- A block coordinate can be recovered from any ambient coordinate on which its block vector
has a nonzero coefficient. -/
theorem blockBasis_coord_eq_inv_mul (n : ℕ)
    (x : (Submodule.span 𝕜 (range v)).topologicalClosure) {k : ℕ} (hk : b.coord k (v n) ≠ 0) :
    (b.blockBasis v u hv hs).coord n x = (b.coord k (v n))⁻¹ * b.coord k (x : E) := by
  rw [b.coord_eq_blockBasis_coord_mul v u hv hs n x (hs n hk),
    mul_left_comm, inv_mul_cancel₀ hk, mul_one]

/-- Restricting an initial projection to the closed block span cannot increase its norm. -/
theorem norm_blockBasis_proj_le (n : ℕ) :
    ‖(b.blockBasis v u hv hs).proj n‖ ≤ ‖b.proj (u n)‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  simpa only [← Submodule.norm_coe, coe_blockBasis_proj] using
    (b.proj (u n)).le_opNorm (x : E)

/-- The basis constant of a block basis is at most the original basis constant. -/
theorem blockBasis_nnNormProjBound_le [CompleteSpace E] :
    (b.blockBasis v u hv hs).nnNormProjBound ≤ b.nnNormProjBound := by
  apply ciSup_le
  intro n
  exact_mod_cast (b.norm_blockBasis_proj_le v u hv hs n).trans
    (b.norm_proj_le_nnNormProjBound (u n))

end SchauderBasis
