/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
module

public import TauCeti.LinearAlgebra.Matrix.Rank
import TauCeti.LinearAlgebra.Matrix.Range

/-!
# Uniqueness of exact-rank matrix factorizations

Suppose a matrix `M` admits two factorizations through an intermediate index type whose
cardinality equals the rank of `M`. The two left factors differ by multiplication by an
invertible matrix on the intermediate space, and the two right factors differ by the inverse.

The imported matrix rank results provide existence and rank bounds for factorizations;
this module proves uniqueness of an exact-rank factorization.

## Main result

* `Matrix.exists_unit_eq_mul_of_rank_factorization`: two exact-rank factorizations
  differ by a unit on the intermediate space.

## Provenance

Adapted from `ForTauCeti/LinearAlgebra/Matrix/RankFactorization.lean` in
[Kitware's DKPS formalization](https://github.com/AIQ-Kitware/aiq-dkps-formalization),
originally developed by Jon Crall and Claude Fable 5 (Apache-2.0).
-/

public section

namespace Matrix

variable {𝕜 m n : Type*} [Field 𝕜] [Fintype n]

section Uniqueness

/-- Two factorizations of the same matrix through any finite intermediate type `ι`,
when the rank equals `Fintype.card ι`, differ by an invertible change of basis.
The decidable equality instance supplies the identity matrix and square-matrix units. -/
theorem exists_unit_eq_mul_of_rank_factorization {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix m n 𝕜} (hM : M.rank = Fintype.card ι)
    {L L' : Matrix m ι 𝕜} {R R' : Matrix ι n 𝕜}
    (h : M = L * R) (h' : M = L' * R') :
    ∃ g : (Matrix ι ι 𝕜)ˣ,
      L' = L * (g : Matrix ι ι 𝕜) ∧
        R' = ((g⁻¹ : (Matrix ι ι 𝕜)ˣ) : Matrix ι ι 𝕜) * R := by
  classical
  have hrange : LinearMap.range L'.mulVecLin = LinearMap.range L.mulVecLin := by
    rw [range_left_factor_eq hM h', range_left_factor_eq hM h]
  have hcols : ∀ j : ι, L'.col j ∈ LinearMap.range L.mulVecLin := by
    intro j
    rw [← hrange, Matrix.range_mulVecLin]
    exact Submodule.subset_span (Set.mem_range_self j)
  have hcols' : ∀ j : ι, L.col j ∈ LinearMap.range L'.mulVecLin := by
    intro j
    rw [hrange, Matrix.range_mulVecLin]
    exact Submodule.subset_span (Set.mem_range_self j)
  obtain ⟨G, hG⟩ := exists_mul_eq_of_range_le (L := L) (L' := L') hcols
  obtain ⟨G', hG'⟩ := exists_mul_eq_of_range_le (L := L') (L' := L) hcols'
  have hLinj : Function.Injective L.mulVec :=
    (rank_eq_card_iff_mulVec_injective L).mp (rank_left_factor_eq hM h)
  have hGG' : G * G' = 1 := by
    apply mul_left_cancel_of_mulVec_injective hLinj
    calc
      L * (G * G') = (L * G) * G' := (Matrix.mul_assoc L G G').symm
      _ = L := by rw [hG, hG']
      _ = L * 1 := (Matrix.mul_one L).symm
  have hG'G : G' * G = 1 := mul_eq_one_comm.mp hGG'
  refine ⟨⟨G, G', hGG', hG'G⟩, hG.symm, ?_⟩
  have hR : R = G * R' := by
    apply mul_left_cancel_of_mulVec_injective hLinj
    calc
      L * R = M := h.symm
      _ = L' * R' := h'
      _ = (L * G) * R' := by rw [hG]
      _ = L * (G * R') := Matrix.mul_assoc L G R'
  rw [hR, ← Matrix.mul_assoc]
  simp [hG'G]

end Uniqueness

end Matrix
