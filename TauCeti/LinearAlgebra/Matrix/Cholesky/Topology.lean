/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Cholesky.Equiv
public import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-!
# Continuity and measurability of the Cholesky equivalence

This file proves that Cholesky factorization is a homeomorphism between the positive-definite
symmetric matrices and the positive-diagonal lower-triangular matrices, both carrying their
subtype topologies, and hence a measurable equivalence for the corresponding Borel structures.

Reconstruction `L ↦ L * Lᵀ` is visibly continuous. The continuity of the factorization itself is
deduced from a properness argument rather than from formulas for the Cholesky entries: a compact
set `K` of positive-definite matrices has bounded diagonal entries, and the `i`-th row of a Gram
factor of `A` has squared norm `A i i`, so the factors of the matrices in `K` form a bounded set.
It is also closed, since a lower-triangular limit with nonnegative diagonal and positive-definite
Gram matrix has nonzero determinant, hence positive diagonal. Reconstruction is therefore a
continuous proper bijection, hence closed, hence a homeomorphism.

## Main results

* `TauCeti.continuous_choleskyReconstruction` — reconstruction is continuous.
* `TauCeti.isProperMap_choleskyReconstruction` — reconstruction is a proper map.
* `TauCeti.continuous_cholesky` — Cholesky factorization is continuous.
* `TauCeti.choleskyHomeomorph` — the resulting homeomorphism.
* `TauCeti.measurable_cholesky`, `TauCeti.measurable_choleskyReconstruction` — measurability in
  both directions.
* `TauCeti.choleskyMeasurableEquiv` — the resulting measurable equivalence.

## References

* R. A. Horn and C. R. Johnson, *Matrix Analysis*, second edition, Cambridge University Press,
  2013, Section 7.2.
-/

public section

noncomputable section

open scoped Matrix

namespace TauCeti

variable {p : ℕ}

/-- Reconstructing a positive-definite matrix from its lower-triangular factor is continuous. -/
theorem continuous_choleskyReconstruction :
    Continuous (@choleskyReconstruction p) := by
  refine continuous_induced_rng.2 (continuous_induced_rng.2 ?_)
  exact (continuous_subtype_val.matrix_mul continuous_subtype_val.matrix_transpose).congr
    fun L ↦ (choleskyReconstruction_coe L).symm

/-- Reconstruction from positive-diagonal lower-triangular factors is a proper map: the factors of
a compact set of positive-definite matrices form a compact set. -/
theorem isProperMap_choleskyReconstruction :
    IsProperMap (@choleskyReconstruction p) := by
  refine isProperMap_iff_isCompact_preimage.2 ⟨continuous_choleskyReconstruction, fun K hK ↦ ?_⟩
  set K' := (fun A : PosDefMatrix p ↦ (A.1 : Matrix (Fin p) (Fin p) ℝ)) '' K
  have hK'c : IsCompact K' := hK.image (continuous_subtype_val.comp continuous_subtype_val)
  obtain ⟨c, hc⟩ := hK'c.bddAbove_image (continuous_id.matrix_trace).continuousOn
  -- The factors of the matrices in `K` are the lower-triangular matrices with nonnegative diagonal
  -- whose Gram matrix lies in `K'`; the positivity of the diagonal is then automatic.
  set T : Set (Matrix (Fin p) (Fin p) ℝ) :=
    {L | L.IsLowerTriangular ∧ (∀ i, 0 ≤ L i i) ∧ L * Lᵀ ∈ K'}
  have himage : Subtype.val '' (choleskyReconstruction ⁻¹' K) = T := by
    ext L
    constructor
    · rintro ⟨L, hL, rfl⟩
      exact ⟨L.2.1, fun i ↦ (L.2.2 i).le, _, hL, choleskyReconstruction_coe L⟩
    · rintro ⟨htri, hdiag, A, hA, hAL⟩
      have hdet : (∏ i, L i i) ^ 2 ≠ 0 := by
        have hAL' : (A.1 : Matrix (Fin p) (Fin p) ℝ) = L * Lᵀ := hAL
        have h := A.2.det_pos
        rw [hAL', Matrix.det_mul,
          Matrix.det_transpose, Matrix.det_of_isLowerTriangular L htri, ← sq] at h
        exact h.ne'
      have hpos : ∀ i, 0 < L i i := fun i ↦ (hdiag i).lt_of_ne
        (Finset.prod_ne_zero_iff.1 ((pow_ne_zero_iff two_ne_zero).1 hdet) i
          (Finset.mem_univ i)).symm
      refine ⟨⟨L, htri, hpos⟩, ?_, rfl⟩
      have hrec : choleskyReconstruction ⟨L, htri, hpos⟩ = A :=
        Subtype.ext (Subtype.ext ((choleskyReconstruction_coe _).trans hAL.symm))
      rw [Set.mem_preimage, hrec]
      exact hA
  have hTclosed : IsClosed T := by
    have htri : IsClosed {L : Matrix (Fin p) (Fin p) ℝ | L.IsLowerTriangular} := by
      simp only [Matrix.IsLowerTriangular, Matrix.BlockTriangular, Set.ofPred_forall]
      exact isClosed_iInter fun i ↦ isClosed_iInter fun j ↦ isClosed_iInter fun _ ↦
        isClosed_eq (continuous_id.matrix_elem i j) continuous_const
    have hdiag : IsClosed {L : Matrix (Fin p) (Fin p) ℝ | ∀ i, 0 ≤ L i i} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun i ↦ isClosed_le continuous_const (continuous_id.matrix_elem i i)
    exact htri.inter (hdiag.inter
      (hK'c.isClosed.preimage (continuous_id.matrix_mul continuous_id.matrix_transpose)))
  -- Each entry of a factor is bounded by the square root of the trace of its Gram matrix.
  have hTbox : T ⊆ Set.pi Set.univ fun _ ↦ Set.pi Set.univ fun _ ↦ Set.Icc (-√c) √c := by
    rintro L ⟨-, -, hL⟩ i - j -
    refine abs_le.1 (Real.abs_le_sqrt ?_)
    have htrace : (L * Lᵀ).trace = ∑ i, ∑ k, L i k * L i k := by
      simp [Matrix.trace, Matrix.mul_apply]
    calc L i j ^ 2 = L i j * L i j := sq _
      _ ≤ ∑ k, L i k * L i k :=
        Finset.single_le_sum (fun k _ ↦ mul_self_nonneg (L i k)) (Finset.mem_univ j)
      _ ≤ ∑ i, ∑ k, L i k * L i k :=
        Finset.single_le_sum (f := fun i ↦ ∑ k, L i k * L i k)
          (fun i _ ↦ Finset.sum_nonneg fun k _ ↦ mul_self_nonneg (L i k)) (Finset.mem_univ i)
      _ = (L * Lᵀ).trace := htrace.symm
      _ ≤ c := hc ⟨_, hL, rfl⟩
  have hTc : IsCompact T :=
    (isCompact_univ_pi fun _ ↦ isCompact_univ_pi fun _ ↦ isCompact_Icc).of_isClosed_subset
      hTclosed hTbox
  exact Topology.IsInducing.subtypeVal.isCompact_iff.2 (himage ▸ hTc)

/-- Cholesky factorization is continuous. -/
theorem continuous_cholesky : Continuous (@cholesky p) := by
  refine continuous_iff_isClosed.2 fun s hs ↦ ?_
  have h : cholesky ⁻¹' s = choleskyReconstruction '' s := by
    ext A
    exact ⟨fun hA ↦ ⟨cholesky A, hA, choleskyReconstruction_cholesky A⟩,
      fun ⟨L, hL, hLA⟩ ↦ by
        subst hLA
        simpa using hL⟩
  exact h ▸ isProperMap_choleskyReconstruction.isClosedMap s hs

/-- Cholesky factorization as a homeomorphism between positive-definite symmetric matrices and
positive-diagonal lower-triangular matrices. -/
def choleskyHomeomorph : PosDefMatrix p ≃ₜ PosDiagLowerTriangular p where
  toFun := cholesky
  invFun := choleskyReconstruction
  left_inv := choleskyReconstruction_cholesky
  right_inv := cholesky_choleskyReconstruction
  continuous_toFun := continuous_cholesky
  continuous_invFun := continuous_choleskyReconstruction

/-- The equivalence underlying `choleskyHomeomorph` is `choleskyEquiv`. -/
@[simp]
theorem choleskyHomeomorph_toEquiv :
    (choleskyHomeomorph (p := p)).toEquiv = choleskyEquiv :=
  Equiv.ext fun A ↦ (choleskyEquiv_apply A).symm

@[simp]
theorem choleskyHomeomorph_apply (A : PosDefMatrix p) : choleskyHomeomorph A = cholesky A :=
  (rfl)

@[simp]
theorem choleskyHomeomorph_symm_apply (L : PosDiagLowerTriangular p) :
    choleskyHomeomorph.symm L = choleskyReconstruction L :=
  (rfl)

/-- Cholesky factorization is measurable. -/
theorem measurable_cholesky : Measurable (@cholesky p) :=
  continuous_cholesky.measurable

/-- Reconstructing a positive-definite matrix from its lower-triangular factor is measurable. -/
theorem measurable_choleskyReconstruction : Measurable (@choleskyReconstruction p) :=
  continuous_choleskyReconstruction.measurable

/-- Cholesky factorization as a measurable equivalence between positive-definite symmetric
matrices and positive-diagonal lower-triangular matrices. -/
def choleskyMeasurableEquiv : PosDefMatrix p ≃ᵐ PosDiagLowerTriangular p :=
  choleskyHomeomorph.toMeasurableEquiv

@[simp]
theorem choleskyMeasurableEquiv_apply (A : PosDefMatrix p) :
    choleskyMeasurableEquiv A = cholesky A :=
  (rfl)

@[simp]
theorem choleskyMeasurableEquiv_symm_apply (L : PosDiagLowerTriangular p) :
    choleskyMeasurableEquiv.symm L = choleskyReconstruction L :=
  (rfl)

end TauCeti
