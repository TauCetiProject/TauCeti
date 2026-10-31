/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Bases
public import Mathlib.Order.SuccPred.IntervalSucc

/-!
# Block bases of Schauder bases

Nonzero successive finite linear combinations of a Schauder basis form a Schauder basis
of their closed linear span. The construction uses increasing cut points `u` and coefficients
`a`, with the `n`-th block supported on `[u n, u (n + 1))`. Zero coefficients permit gaps
inside or between blocks. No normalization of the blocks is required.

The initial projections of the block basis are restrictions of the original projections
at the cut points. In a Banach space, its basis constant is therefore at most the original
basis constant. The construction and projection identities do not require completeness,
and convergence is along initial segments, without an unconditionality assumption.

The construction adapts `SchauderBasis.subsequence` from
`TauCeti.Analysis.Normed.Module.Bases.Subsequence`.

## References

* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, Chapter 1, block basic sequences.
-/

public section

noncomputable section

open Filter Set
open scoped Topology

namespace SchauderBasis

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  (b : SchauderBasis 𝕜 E) (u : ℕ → ℕ) (a : ℕ → 𝕜)

/-- The finite linear combination on the interval between successive cut points. -/
def blockVector (n : ℕ) : E :=
  ∑ k ∈ Finset.Ico (u n) (u (n + 1)), a k • b k

/-- The block vector as a finite sum over its defining interval. -/
theorem blockVector_def (n : ℕ) :
    b.blockVector u a n = ∑ k ∈ Finset.Ico (u n) (u (n + 1)), a k • b k := (rfl)

/-- The coordinates of a block vector vanish outside its defining interval. -/
@[simp]
theorem coord_blockVector (n k : ℕ) :
    b.coord k (b.blockVector u a n) =
      if u n ≤ k ∧ k < u (n + 1) then a k else 0 := by
  classical
  simp [blockVector, b.ortho, Pi.single_apply, Finset.mem_Ico]

/-- A block is nonzero exactly when one of its coefficients in the block interval is nonzero. -/
theorem blockVector_ne_zero_iff (n : ℕ) :
    b.blockVector u a n ≠ 0 ↔ ∃ k ∈ Finset.Ico (u n) (u (n + 1)), a k ≠ 0 := by
  classical
  constructor
  · intro h
    by_contra! hzero
    exact h (Finset.sum_eq_zero fun k hk ↦ by simp [hzero k hk])
  · rintro ⟨k, hk, ha⟩ h
    have := congrArg (b.coord k) h
    simp only [coord_blockVector, Finset.mem_Ico.mp hk, and_self, ↓reduceIte, map_zero] at this
    exact ha this

/-- Nonzero successive block vectors force the cut points to be strictly increasing. -/
theorem strictMono_of_blockVector_ne_zero (h : ∀ n, b.blockVector u a n ≠ 0) :
    StrictMono u := by
  apply strictMono_nat_of_lt_succ
  intro n
  obtain ⟨k, hk, _⟩ := (b.blockVector_ne_zero_iff u a n).mp (h n)
  exact (Finset.mem_Ico.mp hk).1.trans_lt (Finset.mem_Ico.mp hk).2

/-- At a cut point, an original initial projection retains exactly the preceding blocks. -/
theorem proj_blockVector (hu : Monotone u) (n j : ℕ) :
    b.proj (u n) (b.blockVector u a j) = if j < n then b.blockVector u a j else 0 := by
  classical
  rw [blockVector, map_sum]
  by_cases h : j < n
  · rw [ite_eq_left h]
    apply Finset.sum_congr rfl
    intro k hk
    have hkn : k < u n := (Finset.mem_Ico.mp hk).2.trans_le
      (hu (by omega))
    simp [map_smul, b.proj_apply_basis_mem, hkn]
  · rw [ite_eq_right h]
    apply Finset.sum_eq_zero
    intro k hk
    have hnk : u n ≤ k := (hu (by omega)).trans (Finset.mem_Ico.mp hk).1
    simp [map_smul, b.proj_apply_basis_mem, not_lt.mpr hnk]

variable (ha : ∀ n, ∃ k ∈ Finset.Ico (u n) (u (n + 1)), a k ≠ 0)

private def blockCoord (n : ℕ) : StrongDual 𝕜 E :=
  (a (ha n).choose)⁻¹ • b.coord (ha n).choose

private theorem blockCoord_blockVector (i j : ℕ) :
    b.blockCoord u a ha i (b.blockVector u a j) = (Pi.single j (1 : 𝕜) : ℕ → 𝕜) i := by
  classical
  have hu := b.strictMono_of_blockVector_ne_zero u a
    (fun n ↦ (b.blockVector_ne_zero_iff u a n).mpr (ha n))
  obtain ⟨hki, hki'⟩ := Finset.mem_Ico.mp (ha i).choose_spec.1
  have hai := (ha i).choose_spec.2
  simp only [blockCoord, _root_.smul_apply, coord_blockVector, smul_eq_mul,
    Pi.single_apply]
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left ⟨hki, hki'⟩, inv_mul_cancel₀ hai]
    simp
  · have hout : ¬ (u j ≤ (ha i).choose ∧ (ha i).choose < u (j + 1)) := by
      exact Set.disjoint_left.mp (hu.monotone.pairwise_disjoint_on_Ico_succ hij)
        ⟨hki, hki'⟩
    rw [ite_eq_right hout, ite_eq_right hij]
    simp

private theorem sum_blockCoord_eq_proj (n : ℕ)
    (x : (Submodule.span 𝕜 (range (b.blockVector u a))).topologicalClosure) :
    ∑ i ∈ Finset.range n, b.blockCoord u a ha i (x : E) • b.blockVector u a i =
      b.proj (u n) (x : E) := by
  classical
  have hu := b.strictMono_of_blockVector_ne_zero u a
    (fun n ↦ (b.blockVector_ne_zero_iff u a n).mpr (ha n))
  have h : EqOn (∑ i ∈ Finset.range n,
      (b.blockCoord u a ha i).smulRight (b.blockVector u a i) : E →L[𝕜] E)
      (b.proj (u n)) (range (b.blockVector u a)) := by
    rintro _ ⟨j, rfl⟩
    rw [b.proj_blockVector u a hu.monotone]
    simp [_root_.sum_apply, b.blockCoord_blockVector u a ha, Pi.single_apply]
  simpa only [_root_.sum_apply, ContinuousLinearMap.smulRight_apply] using
    ContinuousLinearMap.eqOn_closure_span h x.property

/-- The Schauder basis of the closed span of nonzero successive blocks of `b`.
The hypothesis `ha` requires a nonzero coefficient in each block interval. -/
def blockBasis :
    SchauderBasis 𝕜 (Submodule.span 𝕜 (range (b.blockVector u a))).topologicalClosure where
  basis i := ⟨b.blockVector u a i, Submodule.le_topologicalClosure _
    (Submodule.subset_span (mem_range_self i))⟩
  coord i := (b.blockCoord u a ha i).comp (Submodule.subtypeL _)
  ortho i j := by
    classical
    by_cases hij : i = j <;>
      simpa [Pi.single_apply, hij] using b.blockCoord_blockVector u a ha i j
  expansion x := by
    have hu := b.strictMono_of_blockVector_ne_zero u a
      (fun n ↦ (b.blockVector_ne_zero_iff u a n).mpr (ha n))
    rw [HasSum, SummationFilter.conditional_filter_eq_map_range, tendsto_map'_iff]
    apply tendsto_subtype_rng.mpr
    simpa only [Function.comp_def, Submodule.coe_sum, Submodule.coe_smul_of_tower,
      ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
      b.sum_blockCoord_eq_proj u a ha] using
      (b.tendsto_proj (x : E)).comp hu.tendsto_atTop

/-- The vectors of the constructed basis are the prescribed blocks. -/
@[simp]
theorem coe_blockBasis_apply (i : ℕ) :
    (b.blockBasis u a ha i : E) = b.blockVector u a i := (rfl)

/-- Initial projections of a block basis agree with the original projections at the cut points
on the closed block span. -/
theorem coe_blockBasis_proj (n : ℕ)
    (x : (Submodule.span 𝕜 (range (b.blockVector u a))).topologicalClosure) :
    ((b.blockBasis u a ha).proj n x : E) = b.proj (u n) (x : E) := by
  rw [proj_apply]
  -- Unfold only the constructed basis to recover the finite sum of the chosen coordinates.
  simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower,
    blockBasis, ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply, b.sum_blockCoord_eq_proj u a ha]

/-- Every original coordinate in a block is the corresponding coefficient times the block
coordinate. This characterizes block coordinates without choosing a distinguished index. -/
theorem coord_eq_mul_blockBasis_coord (n k : ℕ)
    (hk : k ∈ Finset.Ico (u n) (u (n + 1)))
    (x : (Submodule.span 𝕜 (range (b.blockVector u a))).topologicalClosure) :
    b.coord k (x : E) = a k * (b.blockBasis u a ha).coord n x := by
  classical
  have hu := b.strictMono_of_blockVector_ne_zero u a
    (fun n ↦ (b.blockVector_ne_zero_iff u a n).mpr (ha n))
  have h : EqOn (b.coord k) (a k • b.blockCoord u a ha n : StrongDual 𝕜 E)
      (range (b.blockVector u a)) := by
    rintro _ ⟨j, rfl⟩
    simp only [coord_blockVector, _root_.smul_apply,
      b.blockCoord_blockVector u a ha, Pi.single_apply, smul_eq_mul]
    by_cases hnj : n = j
    · subst j
      simp [Finset.mem_Ico.mp hk]
    · have hout : ¬ (u j ≤ k ∧ k < u (j + 1)) := by
        exact Set.disjoint_left.mp (hu.monotone.pairwise_disjoint_on_Ico_succ hnj)
          (Finset.mem_Ico.mp hk)
      simp [hnj, hout]
  exact ContinuousLinearMap.eqOn_closure_span h x.property

/-- Restricting an initial projection to the block span cannot increase its norm. -/
theorem norm_blockBasis_proj_le (n : ℕ) :
    ‖(b.blockBasis u a ha).proj n‖ ≤ ‖b.proj (u n)‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  simpa only [← Submodule.norm_coe, coe_blockBasis_proj] using
    (b.proj (u n)).le_opNorm (x : E)

/-- In a Banach space the basis constant of a block basis is at most that of the original basis. -/
theorem blockBasis_nnnormProjBound_le [CompleteSpace E] :
    (b.blockBasis u a ha).nnnormProjBound ≤ b.nnnormProjBound := by
  apply ciSup_le
  intro n
  exact_mod_cast (b.norm_blockBasis_proj_le u a ha n).trans
    (b.norm_proj_le_nnnormProjBound (u n))

end SchauderBasis
