/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Examples.RepresentationTheory.GroupAlgebra.Block.Basic
public import TauCeti.LinearAlgebra.Matrix.TensorProduct
public import TauCeti.RepresentationTheory.GroupAlgebra.Block.Algebra
public import TauCeti.RepresentationTheory.GroupAlgebra.DefectGroup.Basic

/-!
# The defect-zero criterion needs a splitting field

Over a field `k` of characteristic `p` that splits `G`, a block of `k[G]` has defect group `1`
exactly when its block algebra is a matrix algebra over `k`. The splitting hypothesis is needed:

* over `𝔽₂`, the block `r + r²` of `𝔽₂[C₃]` has defect group `1`, since `1` is the only
  `2`-subgroup of `C₃` and `Br_1` is the identity, but its block algebra `(r + r²) 𝔽₂[C₃]` has
  dimension `2`, which is not a square, so it is not a matrix algebra over `𝔽₂`;
* over a field `K` of characteristic `2` containing a root `α` of `X² + X + 1`, for instance
  `𝔽₄`, which splits `C₃`, the two blocks `1 + α² r + α r²` and `1 + α r + α² r²` into which
  `r + r²` splits (`TauCeti.GroupAlgebraBlockExamples.centerMapRingHom_r_add_r_sq`) have block
  algebras isomorphic to `K = M₁(K)`.
-/

public section

namespace TauCeti.DefectZeroSplittingExamples

open _root_.MonoidAlgebra Module GroupAlgebraBlockExamples

/-! ### The block `r + r²` of `𝔽₂[C₃]` -/

/-- Every `2`-subgroup of `C₃` is trivial: its order is a power of `2` dividing `3`. -/
theorem eq_bot_of_isPGroup_two {Q : Subgroup C₃} (hQ : IsPGroup 2 Q) : Q = ⊥ := by
  obtain ⟨n, hn⟩ := hQ.exists_card_eq
  have h3 : Nat.card Q ∣ 3 := by
    simpa using Subgroup.card_subgroup_dvd_card Q
  rw [hn] at h3
  exact Subgroup.eq_bot_of_card_eq Q <| hn.trans <|
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_left n (by norm_num)) h3

/-- **Check.** The block `r + r²` of `𝔽₂[C₃]` has defect group `1`: `1` is the only
`2`-subgroup of `C₃`, and `Br_1` is the identity. -/
theorem isDefectGroup_r_add_r_sq_bot :
    IsDefectGroup (ZMod 2) 2 (of (ZMod 2) C₃ r + of (ZMod 2) C₃ (r ^ 2)) ⊥ := by
  refine isDefectGroup_iff.2 ⟨IsPGroup.of_bot, ?_, fun Q hQ _ _ ↦ eq_bot_of_isPGroup_two hQ⟩
  rw [Ne, brauerProjection_bot_eq_zero_iff]
  intro h
  have := congrArg (fun x ↦ x.coeff r) h
  simp +decide at this

/-- In characteristic `2`, `r + r² = 1 - (1 + r + r²)` in the centre of `𝔽₂[C₃]`. -/
theorem toCenter_r_add_r_sq_eq_one_sub :
    toCenter (of (ZMod 2) C₃ r + of (ZMod 2) C₃ (r ^ 2)) =
      1 - toCenter (1 + of (ZMod 2) C₃ r + of (ZMod 2) C₃ (r ^ 2)) := by
  refine Subtype.ext (ext (Finsupp.ext fun h ↦ ?_))
  fin_cases h <;> simp +decide [Finsupp.single_apply, one_def]

/-- The blocks `1 + r + r²` and `r + r²` of `𝔽₂[C₃]`. -/
noncomputable abbrev blocksF₂ : Fin 2 → Subalgebra.center (ZMod 2) (MonoidAlgebra (ZMod 2) C₃) :=
  ![toCenter (1 + of (ZMod 2) C₃ r + of (ZMod 2) C₃ (r ^ 2)),
    toCenter (of (ZMod 2) C₃ r + of (ZMod 2) C₃ (r ^ 2))]

/-- The blocks `1 + r + r²` and `r + r²` of `𝔽₂[C₃]` form a complete orthogonal family. -/
theorem completeOrthogonalIdempotents_blocksF₂ : CompleteOrthogonalIdempotents blocksF₂ :=
  CompleteOrthogonalIdempotents.pair_iff.2
    ⟨isBlockIdempotent_one_add_r_add_r_sq.isIdempotentElem, toCenter_r_add_r_sq_eq_one_sub⟩

/-- Each member of `blocksF₂` is a block idempotent. -/
theorem isBlockIdempotent_blocksF₂ (i : Fin 2) : IsBlockIdempotent (blocksF₂ i) := by
  fin_cases i
  exacts [isBlockIdempotent_one_add_r_add_r_sq, isBlockIdempotent_r_add_r_sq]

/-- The block algebra of `r + r²` contains two linearly independent elements, its identity
`r + r²` and `(r + r²) r = 1 + r²`. -/
theorem two_le_finrank_blockAlgebra_r_add_r_sq :
    2 ≤ finrank (ZMod 2) isBlockIdempotent_r_add_r_sq.BlockAlgebra := by
  set hb := isBlockIdempotent_r_add_r_sq
  have hc : (hb.isIdempotentElem_val.compress (of (ZMod 2) C₃ r)).val =
      1 + of (ZMod 2) C₃ (r ^ 2) := by
    rw [IsIdempotentElem.val_compress, coe_toCenter]
    simp only [add_mul, mul_add, of_apply, single_mul_single]
    refine ext (Finsupp.ext fun h ↦ ?_)
    fin_cases h <;> simp +decide [Finsupp.single_apply, one_def]
  have hli : LinearIndependent (ZMod 2)
      ![(1 : hb.BlockAlgebra), hb.isIdempotentElem_val.compress (of (ZMod 2) C₃ r)] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h := congrArg Subtype.val hst
    simp only [IsIdempotentElem.Corner.val_add, IsIdempotentElem.Corner.val_smul,
      IsIdempotentElem.Corner.val_one, IsIdempotentElem.Corner.val_zero, hc, coe_toCenter] at h
    have h1 := congrArg (fun x ↦ x.coeff 1) h
    have hr := congrArg (fun x ↦ x.coeff r) h
    exact ⟨by simpa +decide [one_def] using hr, by simpa +decide [one_def] using h1⟩
  simpa using hli.fintype_card_le_finrank

/-- **Check.** The block algebra `(r + r²) 𝔽₂[C₃]` has dimension `2` over `𝔽₂`. -/
theorem finrank_blockAlgebra_r_add_r_sq :
    finrank (ZMod 2) isBlockIdempotent_r_add_r_sq.BlockAlgebra = 2 := by
  have h3 : finrank (ZMod 2) (MonoidAlgebra (ZMod 2) C₃) = 3 := by
    rw [(coeffLinearEquiv (ZMod 2)).finrank_eq, finrank_finsupp_self,
      Fintype.card_multiplicative, ZMod.card]
  rw [(algEquivPiBlockAlgebra completeOrthogonalIdempotents_blocksF₂
    isBlockIdempotent_blocksF₂).toLinearEquiv.finrank_eq, finrank_pi_fintype,
    Fin.sum_univ_two] at h3
  have h0 : 0 < finrank (ZMod 2) (isBlockIdempotent_blocksF₂ 0).BlockAlgebra :=
    finrank_pos
  have h1 := two_le_finrank_blockAlgebra_r_add_r_sq
  -- `blocksF₂ 1` is `toCenter (r + r²)` by `Matrix.cons_val_one`, definitionally, so the block
  -- algebras of `isBlockIdempotent_blocksF₂ 1` and `isBlockIdempotent_r_add_r_sq` coincide; the
  -- dependent type of the block algebra blocks rewriting with that equation, hence `change`.
  change _ + finrank (ZMod 2) isBlockIdempotent_r_add_r_sq.BlockAlgebra = 3 at h3
  omega

/-- **Check.** The block algebra `(r + r²) 𝔽₂[C₃]` of the defect-zero block `r + r²` is not a
matrix algebra over `𝔽₂`: its dimension `2` is not a square. -/
theorem isEmpty_algEquiv_matrix_blockAlgebra_r_add_r_sq (n : ℕ) :
    IsEmpty (isBlockIdempotent_r_add_r_sq.BlockAlgebra ≃ₐ[ZMod 2]
      Matrix (Fin n) (Fin n) (ZMod 2)) := by
  refine ⟨fun e ↦ ?_⟩
  have h := e.toLinearEquiv.finrank_eq
  rw [finrank_blockAlgebra_r_add_r_sq, finrank_matrix, finrank_self, Fintype.card_fin,
    mul_one] at h
  rcases n with _ | _ | n
  · simp at h
  · simp at h
  · nlinarith

/-! ### Over a field containing a primitive cube root of unity -/

section Split

variable {K : Type*} [Field K] [CharP K 2] {α : K}

/-- **Check.** Over a field `K` of characteristic `2` containing a root `α` of `X² + X + 1`, for
instance `𝔽₄`, the block algebra of `1 + α² r + α r²` is isomorphic to `K = M₁(K)`. -/
noncomputable def blockAlgebraEOneAlgEquivMatrix (hα : α ^ 2 + α + 1 = 0) :
    (isBlockIdempotent_eOne hα).BlockAlgebra ≃ₐ[K] Matrix (Fin 1) (Fin 1) K :=
  (blockAlgebraAlgEquivOfMulOfEqSmul _ (by simpa only [coe_toCenter] using eOne_mul_of hα)).trans
    (Matrix.finOneAlgEquiv K K)

/-- **Check.** Over a field `K` of characteristic `2` containing a root `α` of `X² + X + 1`, for
instance `𝔽₄`, the block algebra of `1 + α r + α² r²` is isomorphic to `K = M₁(K)`. -/
noncomputable def blockAlgebraETwoAlgEquivMatrix (hα : α ^ 2 + α + 1 = 0) :
    (isBlockIdempotent_eTwo hα).BlockAlgebra ≃ₐ[K] Matrix (Fin 1) (Fin 1) K :=
  (blockAlgebraAlgEquivOfMulOfEqSmul _ (by simpa only [coe_toCenter] using eTwo_mul_of hα)).trans
    (Matrix.finOneAlgEquiv K K)

end Split

end TauCeti.DefectZeroSplittingExamples
