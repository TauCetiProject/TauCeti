/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Elementary
public import TauCeti.LinearAlgebra.Matrix.Idempotent.Equivalence

import TauCeti.Data.Matrix.Block

/-!
# Elementary conjugacy of equivalent idempotents

Let `A` be a ring, not necessarily commutative. Idempotent matrices `e` and `f`, possibly of
different sizes, are equivalent (`Matrix.IdempotentEquivalent`) exactly when `e ⊕ 0` and `0 ⊕ f`
are conjugate by an invertible matrix
(`Matrix.idempotentEquivalent_iff_exists_units_conj_fromBlocks_zero`).
This file shows that, after adding one more zero block, the conjugating matrix can be taken in the
elementary subgroup `TauCeti.elementarySubgroup`.

The reason is Whitehead's lemma: for invertible `g` the block diagonal matrix `g ⊕ g⁻¹` is
elementary, and it conjugates `M ⊕ 0` to `g M g⁻¹ ⊕ 0`
(`TauCeti.exists_mem_elementarySubgroup_conj_fromBlocks_zero`). So conjugate matrices become
conjugate by an elementary matrix once they are padded by a zero block of the same size.

Elementary conjugators matter because elementary matrices lift along every surjective ring
homomorphism (`RingHom.map_elementarySubgroup_eq_of_surjective`), whereas invertible matrices do
not. This is how idempotent matrices over the two legs of a fibre product of rings, whose images
in the common quotient are equivalent, are aligned so that they glue to an idempotent over the
fibre product, as in the Mayer–Vietoris sequence of `K₀` for a Milnor square.

## Main results

* `Matrix.IdempotentEquivalent.exists_mem_elementarySubgroup_conj_fromBlocks_zero`: for
  equivalent idempotents `e ∼ f`, the matrices `(e ⊕ 0) ⊕ 0` and `(0 ⊕ f) ⊕ 0` are conjugate by an
  elementary matrix.
* `Matrix.idempotentEquivalent_iff_exists_mem_elementarySubgroup_conj_fromBlocks_zero`: the
  converse, so that this elementary conjugacy characterizes equivalence of idempotents.
* `Matrix.IdempotentEquivalent.exists_idempotentEquivalent_map_eq`: along a surjective ring
  homomorphism `φ`, an idempotent `e` with `φ(e) ∼ f` is equivalent to an idempotent whose image
  under `φ` is exactly `(0 ⊕ f) ⊕ 0`.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, Chapter III, §4, for equivalence and stable
  similarity of idempotents.
* C. Weibel, *The K-book*, Chapter II, §2, for idempotent matrices, and Chapter III, Lemma 1.3.3
  (Whitehead's lemma) and Theorem 2.6 (the Mayer–Vietoris sequence).
-/

public section

open Matrix

namespace Matrix

open TauCeti

variable {A : Type*} [Ring A] {ι κ : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq κ]
  [Fintype κ] {e : Matrix ι ι A} {f : Matrix κ κ A}

/-- An idempotent `e` is equivalent to every conjugate of `(e ⊕ 0) ⊕ 0`, the padding being the
shape in which `Matrix.IdempotentEquivalent.exists_mem_elementarySubgroup_conj_fromBlocks_zero`
produces elementary conjugators. -/
private theorem idempotentEquivalent_conj_fromBlocks_zero (he : IsIdempotentElem e)
    (u : GL ((ι ⊕ κ) ⊕ (ι ⊕ κ)) A) :
    IdempotentEquivalent e ((u : Matrix ((ι ⊕ κ) ⊕ (ι ⊕ κ)) ((ι ⊕ κ) ⊕ (ι ⊕ κ)) A) *
      Matrix.fromBlocks (Matrix.fromBlocks e 0 0 (0 : Matrix κ κ A)) 0 0 0 *
      (↑u⁻¹ : Matrix ((ι ⊕ κ) ⊕ (ι ⊕ κ)) ((ι ⊕ κ) ⊕ (ι ⊕ κ)) A)) := by
  have he₀ := he.fromBlocks_zero₁₂_zero₂₁ (IsIdempotentElem.zero (M₀ := Matrix κ κ A))
  exact ((he.idempotentEquivalent_fromBlocks_zero_right κ).symm.trans
    (he₀.idempotentEquivalent_fromBlocks_zero_right (ι ⊕ κ)).symm).trans
    (idempotentEquivalent_conj (he₀.fromBlocks_zero₁₂_zero₂₁ .zero) u)

/-- **Equivalent idempotents are elementarily conjugate after stabilization.** If `e ∼ f`, then
`(e ⊕ 0) ⊕ 0` and `(0 ⊕ f) ⊕ 0` are conjugate by an elementary matrix: an invertible matrix
conjugates `e ⊕ 0` to `0 ⊕ f`, and Whitehead's lemma makes the conjugator elementary after one
more zero block. -/
theorem IdempotentEquivalent.exists_mem_elementarySubgroup_conj_fromBlocks_zero
    (h : IdempotentEquivalent e f) :
    ∃ ε ∈ elementarySubgroup ((ι ⊕ κ) ⊕ (ι ⊕ κ)) A,
      (ε : Matrix ((ι ⊕ κ) ⊕ (ι ⊕ κ)) ((ι ⊕ κ) ⊕ (ι ⊕ κ)) A) *
          Matrix.fromBlocks (Matrix.fromBlocks e 0 0 0) 0 0 0 *
          (↑ε⁻¹ : Matrix ((ι ⊕ κ) ⊕ (ι ⊕ κ)) ((ι ⊕ κ) ⊕ (ι ⊕ κ)) A) =
        Matrix.fromBlocks (Matrix.fromBlocks 0 0 0 f) 0 0 0 := by
  obtain ⟨u, hu⟩ := h.exists_units_conj_fromBlocks_zero
  obtain ⟨ε, hε, hconj⟩ :=
    TauCeti.exists_mem_elementarySubgroup_conj_fromBlocks_zero u (Matrix.fromBlocks e 0 0 0)
  exact ⟨ε, hε, hconj.trans (by rw [hu])⟩

/-- **Elementary conjugacy characterizes equivalence of idempotents.** An idempotent matrix `e`
is equivalent to a square matrix `f` exactly when `(e ⊕ 0) ⊕ 0` and `(0 ⊕ f) ⊕ 0` are conjugate by
an elementary matrix. -/
theorem idempotentEquivalent_iff_exists_mem_elementarySubgroup_conj_fromBlocks_zero
    (he : IsIdempotentElem e) :
    IdempotentEquivalent e f ↔ ∃ ε ∈ elementarySubgroup ((ι ⊕ κ) ⊕ (ι ⊕ κ)) A,
      (ε : Matrix ((ι ⊕ κ) ⊕ (ι ⊕ κ)) ((ι ⊕ κ) ⊕ (ι ⊕ κ)) A) *
          Matrix.fromBlocks (Matrix.fromBlocks e 0 0 0) 0 0 0 *
          (↑ε⁻¹ : Matrix ((ι ⊕ κ) ⊕ (ι ⊕ κ)) ((ι ⊕ κ) ⊕ (ι ⊕ κ)) A) =
        Matrix.fromBlocks (Matrix.fromBlocks 0 0 0 f) 0 0 0 := by
  refine ⟨IdempotentEquivalent.exists_mem_elementarySubgroup_conj_fromBlocks_zero,
    fun ⟨ε, _, hε⟩ ↦ ?_⟩
  -- `e` is equivalent to the conjugate `(0 ⊕ f) ⊕ 0` of `(e ⊕ 0) ⊕ 0`, which is equivalent to `f`.
  have h := idempotentEquivalent_conj_fromBlocks_zero he ε
  rw [hε] at h
  have hf₀ := (isIdempotentElem_fromBlocks_zero₁₂_zero₂₁_iff.1 h.isIdempotentElem_right).1
  have hf := (isIdempotentElem_fromBlocks_zero₁₂_zero₂₁_iff.1 hf₀).2
  exact h.trans ((hf.idempotentEquivalent_fromBlocks_zero_left ι).symm.trans
    (hf₀.idempotentEquivalent_fromBlocks_zero_right (ι ⊕ κ)).symm).symm

omit [DecidableEq ι] [DecidableEq κ] in
/-- **Aligning an idempotent along a surjection.** Let `φ : A →+* B` be a surjective ring
homomorphism, `e` an idempotent matrix over `A` and `f` a square matrix over `B` with `φ(e) ∼ f`.
Then `e` is equivalent to a matrix `e'` over `A` whose entrywise image under `φ` is exactly
`(0 ⊕ f) ⊕ 0`: `e'` is the conjugate of `(e ⊕ 0) ⊕ 0` by a lift of an elementary matrix
conjugating `(φ(e) ⊕ 0) ⊕ 0` to `(0 ⊕ f) ⊕ 0`. -/
theorem IdempotentEquivalent.exists_idempotentEquivalent_map_eq {B : Type*} [Ring B]
    {φ : A →+* B} (hφ : Function.Surjective φ) (he : IsIdempotentElem e) {f : Matrix κ κ B}
    (h : IdempotentEquivalent (e.map φ) f) :
    ∃ e' : Matrix ((ι ⊕ κ) ⊕ (ι ⊕ κ)) ((ι ⊕ κ) ⊕ (ι ⊕ κ)) A,
      IdempotentEquivalent e e' ∧
        e'.map φ = Matrix.fromBlocks (Matrix.fromBlocks 0 0 0 f) 0 0 0 := by
  classical
  obtain ⟨ε, hε, hconj⟩ := h.exists_mem_elementarySubgroup_conj_fromBlocks_zero
  obtain ⟨δ, -, rfl⟩ := φ.exists_mem_elementarySubgroup_unitsMap_mapMatrix_eq hφ hε
  refine ⟨_, idempotentEquivalent_conj_fromBlocks_zero he δ, ?_⟩
  rw [← hconj, ← map_inv]
  simp [Matrix.map_mul, Matrix.fromBlocks_map]

end Matrix
