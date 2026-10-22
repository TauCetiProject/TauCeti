/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Bases

/-!
# Subsequences of Schauder bases

Every strictly increasing subsequence of a Schauder basis is a Schauder basis of its
closed linear span. Its coordinate functionals are restrictions of the original coordinates,
and its initial projections agree with the original projections at the selected indices.
Consequently its basis constant is at most the original basis constant in a Banach space.

The construction preserves conditional summation along initial segments. In particular it
does not require the original basis to be unconditional. The construction and projection
identities require no completeness assumption.

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
  (b : SchauderBasis 𝕜 E) (u : ℕ → ℕ) (hu : StrictMono u)

include hu in
private theorem sum_subsequence_eq_proj (n : ℕ)
    (x : (Submodule.span 𝕜 (range fun i ↦ b (u i))).topologicalClosure) :
    ∑ i ∈ Finset.range n, b.coord (u i) (x : E) • b (u i) = b.proj (u n) x := by
  classical
  have h : EqOn (GeneralSchauderBasis.proj b ((Finset.range n).image u))
      (b.proj (u n)) (range fun i ↦ b (u i)) := by
    rintro _ ⟨j, rfl⟩
    rw [GeneralSchauderBasis.proj_apply_basis_mem, proj_apply_basis_mem]
    simp [hu.injective.eq_iff, hu.lt_iff_lt]
  have hx := ContinuousLinearMap.eqOn_closure_span h x.property
  simpa only [GeneralSchauderBasis.proj_apply,
    Finset.sum_image hu.injective.injOn] using hx

/-- The basis of the closed span of a strictly increasing subsequence of a Schauder basis. -/
def subsequence :
    SchauderBasis 𝕜 (Submodule.span 𝕜 (range fun i ↦ b (u i))).topologicalClosure where
  basis i := ⟨b (u i), Submodule.le_topologicalClosure _
    (Submodule.subset_span (mem_range_self i))⟩
  coord i := (b.coord (u i)).comp (Submodule.subtypeL _)
  ortho i j := by
    classical
    simp [b.ortho, hu.injective.eq_iff, Pi.single_apply]
  expansion x := by
    rw [HasSum, SummationFilter.conditional_filter_eq_map_range, tendsto_map'_iff]
    apply tendsto_subtype_rng.mpr
    simpa only [Function.comp_def, Submodule.coe_sum, Submodule.coe_smul_of_tower,
      ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
      b.sum_subsequence_eq_proj u hu] using (b.tendsto_proj (x : E)).comp hu.tendsto_atTop

@[simp]
theorem coe_subsequence_apply (i : ℕ) :
    (b.subsequence u hu i : E) = b (u i) := (rfl)

@[simp]
theorem subsequence_coord_apply
    (x : (Submodule.span 𝕜 (range fun i ↦ b (u i))).topologicalClosure) (i : ℕ) :
    (b.subsequence u hu).coord i x = b.coord (u i) (x : E) := (rfl)

/-- Initial projections of the subsequence basis are restrictions of the original projections
at the selected indices. -/
theorem coe_subsequence_proj (n : ℕ)
    (x : (Submodule.span 𝕜 (range fun i ↦ b (u i))).topologicalClosure) :
    ((b.subsequence u hu).proj n x : E) = b.proj (u n) (x : E) := by
  rw [proj_apply]
  simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower,
    coe_subsequence_apply, subsequence_coord_apply, b.sum_subsequence_eq_proj u hu]

/-- Restricting an initial projection to the subsequence span cannot increase its norm. -/
theorem norm_subsequence_proj_le (n : ℕ) :
    ‖(b.subsequence u hu).proj n‖ ≤ ‖b.proj (u n)‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  simpa only [← Submodule.norm_coe, coe_subsequence_proj] using
    (b.proj (u n)).le_opNorm (x : E)

/-- The basis constant of a subsequence does not exceed the original basis constant. -/
theorem subsequence_nnnormProjBound_le [CompleteSpace E] :
    (b.subsequence u hu).nnnormProjBound ≤ b.nnnormProjBound := by
  apply ciSup_le
  intro n
  exact_mod_cast (b.norm_subsequence_proj_le u hu n).trans
    (b.norm_proj_le_nnnormProjBound (u n))

end SchauderBasis
