/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LittleWedderburn
public import TauCeti.Examples.RepresentationTheory.GroupAlgebra.Block.Defect.Symmetric
public import TauCeti.RepresentationTheory.GroupAlgebra.Block.Algebra
public import TauCeti.RepresentationTheory.GroupAlgebra.DefectGroup.DefectZero.Simple

/-!
# The defect-zero block of `𝔽₂[S₃]` is `M₂(𝔽₂)`

The Check of the defect-zero criterion on `S₃ = Equiv.Perm (Fin 3)` over `𝔽₂`, which splits `S₃`:
the block `ρ + ρ²` of `𝔽₂[S₃]` (`ρ` a `3`-cycle), of defect group `1`, has block algebra
isomorphic to `M₂(𝔽₂)`, of dimension `4`.

The argument: a block of defect group `1` has block algebra `M_n(D)` for a finite-dimensional
division algebra `D` over `𝔽₂`
(`TauCeti.IsBlockIdempotent.exists_algEquiv_matrix_divisionRing_of_isDefectGroup_bot`), and `D`
is finite, hence commutative (`littleWedderburn`). The block algebra of `ρ + ρ²` is not
commutative, since `ρ` and the transposition `τ = (0 1)` act there without commuting, so `n ≥ 2`;
and it has dimension at most `4`, since `𝔽₂[S₃]` has dimension `6` and the block algebra of the
other block `1 + ρ + ρ²` contains the independent elements `1 + ρ + ρ²` and `(1 + ρ + ρ²) τ`. So
`n² dim D ≤ 4` forces `n = 2` and `D = 𝔽₂`.
-/

public section

namespace TauCeti.DefectZeroSymmetricExamples

open _root_.MonoidAlgebra Module GroupAlgebraBlockExamples Examples.BlockDefectSymmetric
  PrincipalBlockDefectExamples

/-- The blocks `1 + ρ + ρ²` and `ρ + ρ²` of `𝔽₂[S₃]`. -/
noncomputable abbrev blocksS₃ : Fin 2 → Subalgebra.center (ZMod 2) (MonoidAlgebra (ZMod 2) S₃) :=
  ![blockOneS₃, blockTwoS₃]

/-- The blocks `1 + ρ + ρ²` and `ρ + ρ²` of `𝔽₂[S₃]` form a complete orthogonal family. -/
theorem completeOrthogonalIdempotents_blocksS₃ : CompleteOrthogonalIdempotents blocksS₃ :=
  CompleteOrthogonalIdempotents.pair_iff.2
    ⟨isBlockIdempotent_blockOneS₃.isIdempotentElem, eq_sub_of_add_eq' blockOneS₃_add_blockTwoS₃⟩

/-- Each member of `blocksS₃` is a block idempotent. -/
theorem isBlockIdempotent_blocksS₃ (i : Fin 2) : IsBlockIdempotent (blocksS₃ i) := by
  fin_cases i
  exacts [isBlockIdempotent_blockOneS₃, isBlockIdempotent_blockTwoS₃]

/-- The block algebra of `1 + ρ + ρ²` contains two linearly independent elements, its identity
`1 + ρ + ρ²` and `(1 + ρ + ρ²) τ (1 + ρ + ρ²)`. -/
theorem two_le_finrank_blockAlgebra_blockOneS₃ :
    2 ≤ finrank (ZMod 2) isBlockIdempotent_blockOneS₃.BlockAlgebra := by
  set hb := isBlockIdempotent_blockOneS₃
  have hli : LinearIndependent (ZMod 2)
      ![(1 : hb.BlockAlgebra), hb.isIdempotentElem_val.compress (of (ZMod 2) S₃ τ)] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h := congrArg Subtype.val hst
    simp only [IsIdempotentElem.Corner.val_add, IsIdempotentElem.Corner.val_smul,
      IsIdempotentElem.Corner.val_one, IsIdempotentElem.Corner.val_zero,
      IsIdempotentElem.val_compress, coe_blockOneS₃] at h
    have h1 := congrArg (fun x ↦ x.coeff 1) h
    have hτ := congrArg (fun x ↦ x.coeff τ) h
    simp only [add_mul, mul_add, one_mul, mul_one, of_apply, single_mul_single, one_def] at h1 hτ
    -- The coefficient of `(1 + ρ + ρ²) τ (1 + ρ + ρ²)` at `τ` is `3 = 1`.
    have key : ∀ u : ZMod 2, u + u + u = 0 → u = 0 := by decide
    exact ⟨by simpa +decide [Finsupp.single_apply] using h1,
      key t (by simpa +decide [Finsupp.single_apply] using hτ)⟩
  simpa using hli.fintype_card_le_finrank

/-- The block algebra of `ρ + ρ²` has dimension at most `4`: `𝔽₂[S₃]` has dimension `6`, and
the block algebra of `1 + ρ + ρ²` has dimension at least `2`. -/
theorem finrank_blockAlgebra_blockTwoS₃_le :
    finrank (ZMod 2) isBlockIdempotent_blockTwoS₃.BlockAlgebra ≤ 4 := by
  have h6 : finrank (ZMod 2) (MonoidAlgebra (ZMod 2) S₃) = 6 := by
    rw [(coeffLinearEquiv (ZMod 2)).finrank_eq, finrank_finsupp_self, Fintype.card_perm,
      Fintype.card_fin]
    rfl
  rw [(algEquivPiBlockAlgebra completeOrthogonalIdempotents_blocksS₃
    isBlockIdempotent_blocksS₃).toLinearEquiv.finrank_eq, finrank_pi_fintype,
    Fin.sum_univ_two] at h6
  have h0 := two_le_finrank_blockAlgebra_blockOneS₃
  -- `blocksS₃ i` is the `i`-th block definitionally, so the block algebras coincide; the
  -- dependent type of the block algebra blocks rewriting with that equation, hence `change`.
  change finrank (ZMod 2) isBlockIdempotent_blockOneS₃.BlockAlgebra +
    finrank (ZMod 2) isBlockIdempotent_blockTwoS₃.BlockAlgebra = 6 at h6
  omega

/-- The block algebra of `ρ + ρ²` is not commutative: `ρ` and `τ` act there without commuting,
since `(ρ + ρ²) ρ τ` has coefficient `1` at `ρ² τ` and `(ρ + ρ²) τ ρ` has coefficient `0`. -/
theorem not_commute_blockAlgebra_blockTwoS₃ :
    ¬ ∀ x y : isBlockIdempotent_blockTwoS₃.BlockAlgebra, x * y = y * x := by
  set hb := isBlockIdempotent_blockTwoS₃
  intro h
  have h' := congrArg (fun x ↦ (Subtype.val x).coeff (ρ ^ 2 * τ))
    (h (hb.isIdempotentElem_val.compress (of (ZMod 2) S₃ ρ))
      (hb.isIdempotentElem_val.compress (of (ZMod 2) S₃ τ)))
  simp only [IsIdempotentElem.Corner.val_mul, IsIdempotentElem.val_compress, coe_blockTwoS₃,
    add_mul, mul_add, of_apply, single_mul_single] at h'
  simp +decide [Finsupp.single_apply] at h'

/-- **Check.** The defect-zero block `ρ + ρ²` of `𝔽₂[S₃]` is a matrix algebra over `𝔽₂`: its block
algebra is isomorphic to `M₂(𝔽₂)`. -/
theorem nonempty_algEquiv_matrix_blockAlgebra_blockTwoS₃ :
    Nonempty (isBlockIdempotent_blockTwoS₃.BlockAlgebra ≃ₐ[ZMod 2]
      Matrix (Fin 2) (Fin 2) (ZMod 2)) := by
  obtain ⟨n, hn, D, _, _, _, ⟨e⟩⟩ :=
    isBlockIdempotent_blockTwoS₃.exists_algEquiv_matrix_divisionRing_of_isDefectGroup_bot
      isDefectGroup_blockTwoS₃_bot
  have : Finite D := Module.finite_of_finite (ZMod 2)
  let : Field D := littleWedderburn D
  have hdim := e.toLinearEquiv.finrank_eq
  rw [finrank_matrix, Fintype.card_fin] at hdim
  have hD : 0 < finrank (ZMod 2) D := finrank_pos
  have hle := finrank_blockAlgebra_blockTwoS₃_le
  -- `n ≠ 1`: otherwise the block algebra would be commutative.
  have hn1 : n ≠ 1 := by
    rintro rfl
    refine not_commute_blockAlgebra_blockTwoS₃ fun x y ↦ e.injective ?_
    rw [map_mul, map_mul]
    ext i j
    fin_cases i
    fin_cases j
    simp [Matrix.mul_apply, mul_comm]
  have hn0 : n ≠ 0 := NeZero.ne n
  obtain rfl : n = 2 := by
    rcases n with _ | _ | _ | n
    · exact absurd rfl hn0
    · exact absurd rfl hn1
    · rfl
    · nlinarith
  have hD1 : finrank (ZMod 2) D = 1 := by omega
  have eD : D ≃ₐ[ZMod 2] ZMod 2 :=
    (Subalgebra.topEquiv.symm.trans
      (Subalgebra.equivOfEq _ _ (Subalgebra.bot_eq_top_of_finrank_eq_one hD1).symm)).trans
      (Algebra.botEquiv (ZMod 2) D)
  exact ⟨e.trans eD.mapMatrix⟩

/-- **Check.** The block algebra of the defect-zero block `ρ + ρ²` of `𝔽₂[S₃]` has dimension
`4`. -/
theorem finrank_blockAlgebra_blockTwoS₃ :
    finrank (ZMod 2) isBlockIdempotent_blockTwoS₃.BlockAlgebra = 4 := by
  obtain ⟨e⟩ := nonempty_algEquiv_matrix_blockAlgebra_blockTwoS₃
  rw [e.toLinearEquiv.finrank_eq, finrank_matrix, Fintype.card_fin, finrank_self]

end TauCeti.DefectZeroSymmetricExamples
