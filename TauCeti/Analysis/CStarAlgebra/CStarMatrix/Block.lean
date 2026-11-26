/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Topology.Connected.PathConnected
public import TauCeti.Analysis.CStarAlgebra.CStarMatrix.Rectangular
import Mathlib.Analysis.CStarAlgebra.Hom
import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.Block

/-!
# Block calculus, block norms, and rotations for C⋆-matrices

Block-matrix calculus (`fromBlocks`, `toBlocks₁₁`, `toBlocks₁₂`, `toBlocks₂₁`, `toBlocks₂₂`),
corner embeddings, block-diagonal embeddings, block C⋆-norms and positivity, reindexing identities,
and continuous 2×2 block rotations for `CStarMatrix` over a (possibly non-unital) C⋆-algebra `A`.

Corner embeddings (`inlCornerHom`, `inrCornerHom`) provide zero-padding maps placing smaller matrix
algebras inside block-diagonal sums, while the continuous rotation path (`blockRotationPath`) swaps
equal-sized diagonal blocks through unitaries connected to the identity
(`joined_one_blockRotation`).
Together these form the stabilization primitives for Murray–von Neumann equivalence and projection
homotopies.

## Main definitions and results

* `CStarMatrix.fromBlocks`, `toBlocks₁₁`, `toBlocks₁₂`, `toBlocks₂₁`, `toBlocks₂₂`,
  `fromBlocks_toBlocks`: block assembly, block projections, and reconstruction.
* `inlCornerHom`, `inrCornerHom`, `blockDiagNonUnitalStarAlgHom`, `blockDiagStarAlgHom`:
  corner zero-padding maps and non-unital/unital block-diagonal embeddings.
* `norm_fromBlocks_zero₁₂_zero₂₁`, `norm_fromBlocks_zero₁₁_zero₂₁_zero₂₂`,
  `norm_conjTranspose_mul_self`, `norm_self_mul_conjTranspose`, `norm_conjTranspose`,
  `conjTranspose_mul_self_nonneg`, `self_mul_conjTranspose_nonneg`: block/rectangular norms and
  positivity.
* `reindexₐ_sumAssoc_fromBlocks`, `reindexₐ_sumComm_fromBlocks`, `blockRotation`,
  `blockRotationPath`, `blockRotation_pi_div_two_conj`, `joined_one_blockRotation`:
  block reindexing and continuous rotation unitaries.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., Cambridge University Press, 1998, §4.6.
-/

public section

open Matrix
open scoped ComplexOrder InnerProductSpace Matrix NNReal WithCStarModule

namespace CStarMatrix

/-! ### Block matrices -/

section FromBlocks

variable {m₁ m₂ n₁ n₂ o₁ o₂ R A B : Type*}

/-- Block matrix construction on `CStarMatrix`, delegating to `Matrix.fromBlocks`. -/
def fromBlocks (M : CStarMatrix m₁ n₁ A) (N : CStarMatrix m₁ n₂ A)
    (P : CStarMatrix m₂ n₁ A) (Q : CStarMatrix m₂ n₂ A) :
    CStarMatrix (m₁ ⊕ m₂) (n₁ ⊕ n₂) A :=
  ofMatrix (Matrix.fromBlocks (ofMatrix.symm M) (ofMatrix.symm N)
    (ofMatrix.symm P) (ofMatrix.symm Q))

/-- Upper-left block projection on block C⋆-matrices. -/
def toBlocks₁₁ (M : CStarMatrix (m₁ ⊕ m₂) (n₁ ⊕ n₂) A) : CStarMatrix m₁ n₁ A :=
  ofMatrix (ofMatrix.symm M).toBlocks₁₁

/-- Upper-right block projection on block C⋆-matrices. -/
def toBlocks₁₂ (M : CStarMatrix (m₁ ⊕ m₂) (n₁ ⊕ n₂) A) : CStarMatrix m₁ n₂ A :=
  ofMatrix (ofMatrix.symm M).toBlocks₁₂

/-- Lower-left block projection on block C⋆-matrices. -/
def toBlocks₂₁ (M : CStarMatrix (m₁ ⊕ m₂) (n₁ ⊕ n₂) A) : CStarMatrix m₂ n₁ A :=
  ofMatrix (ofMatrix.symm M).toBlocks₂₁

/-- Lower-right block projection on block C⋆-matrices. -/
def toBlocks₂₂ (M : CStarMatrix (m₁ ⊕ m₂) (n₁ ⊕ n₂) A) : CStarMatrix m₂ n₂ A :=
  ofMatrix (ofMatrix.symm M).toBlocks₂₂

section Apply

variable (M : CStarMatrix m₁ n₁ A) (N : CStarMatrix m₁ n₂ A)
  (P : CStarMatrix m₂ n₁ A) (Q : CStarMatrix m₂ n₂ A)

@[simp] theorem ofMatrix_symm_fromBlocks :
    ofMatrix.symm (fromBlocks M N P Q) =
      Matrix.fromBlocks (ofMatrix.symm M) (ofMatrix.symm N)
        (ofMatrix.symm P) (ofMatrix.symm Q) := (rfl)

@[simp] theorem ofMatrix_symm_toBlocks₁₁ (X : CStarMatrix (m₁ ⊕ m₂) (n₁ ⊕ n₂) A) :
    ofMatrix.symm X.toBlocks₁₁ = (ofMatrix.symm X).toBlocks₁₁ := (rfl)

@[simp] theorem ofMatrix_symm_toBlocks₁₂ (X : CStarMatrix (m₁ ⊕ m₂) (n₁ ⊕ n₂) A) :
    ofMatrix.symm X.toBlocks₁₂ = (ofMatrix.symm X).toBlocks₁₂ := (rfl)

@[simp] theorem ofMatrix_symm_toBlocks₂₁ (X : CStarMatrix (m₁ ⊕ m₂) (n₁ ⊕ n₂) A) :
    ofMatrix.symm X.toBlocks₂₁ = (ofMatrix.symm X).toBlocks₂₁ := (rfl)

@[simp] theorem ofMatrix_symm_toBlocks₂₂ (X : CStarMatrix (m₁ ⊕ m₂) (n₁ ⊕ n₂) A) :
    ofMatrix.symm X.toBlocks₂₂ = (ofMatrix.symm X).toBlocks₂₂ := (rfl)

@[simp] theorem toBlocks₁₁_apply (X : CStarMatrix (m₁ ⊕ m₂) (n₁ ⊕ n₂) A) (i : m₁) (j : n₁) :
    X.toBlocks₁₁ i j = X (Sum.inl i) (Sum.inl j) := (rfl)

@[simp] theorem toBlocks₁₂_apply (X : CStarMatrix (m₁ ⊕ m₂) (n₁ ⊕ n₂) A) (i : m₁) (j : n₂) :
    X.toBlocks₁₂ i j = X (Sum.inl i) (Sum.inr j) := (rfl)

@[simp] theorem toBlocks₂₁_apply (X : CStarMatrix (m₁ ⊕ m₂) (n₁ ⊕ n₂) A) (i : m₂) (j : n₁) :
    X.toBlocks₂₁ i j = X (Sum.inr i) (Sum.inl j) := (rfl)

@[simp] theorem toBlocks₂₂_apply (X : CStarMatrix (m₁ ⊕ m₂) (n₁ ⊕ n₂) A) (i : m₂) (j : n₂) :
    X.toBlocks₂₂ i j = X (Sum.inr i) (Sum.inr j) := (rfl)

@[simp] theorem fromBlocks_apply₁₁ (i : m₁) (j : n₁) :
    fromBlocks M N P Q (Sum.inl i) (Sum.inl j) = M i j := (rfl)

@[simp] theorem fromBlocks_apply₁₂ (i : m₁) (j : n₂) :
    fromBlocks M N P Q (Sum.inl i) (Sum.inr j) = N i j := (rfl)

@[simp] theorem fromBlocks_apply₂₁ (i : m₂) (j : n₁) :
    fromBlocks M N P Q (Sum.inr i) (Sum.inl j) = P i j := (rfl)

@[simp] theorem fromBlocks_apply₂₂ (i : m₂) (j : n₂) :
    fromBlocks M N P Q (Sum.inr i) (Sum.inr j) = Q i j := (rfl)

@[simp] theorem toBlocks₁₁_fromBlocks : (fromBlocks M N P Q).toBlocks₁₁ = M := by ext i j; simp

@[simp] theorem toBlocks₁₂_fromBlocks : (fromBlocks M N P Q).toBlocks₁₂ = N := by ext i j; simp

@[simp] theorem toBlocks₂₁_fromBlocks : (fromBlocks M N P Q).toBlocks₂₁ = P := by ext i j; simp

@[simp] theorem toBlocks₂₂_fromBlocks : (fromBlocks M N P Q).toBlocks₂₂ = Q := by ext i j; simp

/-- Reconstruction of a block C⋆-matrix from its four block projections. -/
@[simp] theorem fromBlocks_toBlocks (X : CStarMatrix (m₁ ⊕ m₂) (n₁ ⊕ n₂) A) :
    fromBlocks X.toBlocks₁₁ X.toBlocks₁₂ X.toBlocks₂₁ X.toBlocks₂₂ = X := by
  ext (i | i) (j | j) <;> rfl

end Apply

@[simp] theorem fromBlocks_inj {M M' : CStarMatrix m₁ n₁ A} {N N' : CStarMatrix m₁ n₂ A}
    {P P' : CStarMatrix m₂ n₁ A} {Q Q' : CStarMatrix m₂ n₂ A} :
    fromBlocks M N P Q = fromBlocks M' N' P' Q' ↔ M = M' ∧ N = N' ∧ P = P' ∧ Q = Q' := by
  simp only [← ofMatrix.symm.injective.eq_iff, ofMatrix_symm_fromBlocks, Matrix.fromBlocks_inj]

@[simp] theorem fromBlocks_zero [Zero A] :
    fromBlocks (0 : CStarMatrix m₁ n₁ A) (0 : CStarMatrix m₁ n₂ A)
      (0 : CStarMatrix m₂ n₁ A) (0 : CStarMatrix m₂ n₂ A) = 0 := by
  apply ofMatrix.symm.injective
  simp [Matrix.fromBlocks_zero]

@[simp] theorem fromBlocks_one [DecidableEq m₁] [DecidableEq m₂] [Zero A] [One A] :
    fromBlocks (1 : CStarMatrix m₁ m₁ A) (0 : CStarMatrix m₁ m₂ A)
      (0 : CStarMatrix m₂ m₁ A) (1 : CStarMatrix m₂ m₂ A) = 1 := by
  apply ofMatrix.symm.injective
  simp [Matrix.fromBlocks_one]

@[simp] theorem fromBlocks_add [Add A] (M M' : CStarMatrix m₁ n₁ A) (N N' : CStarMatrix m₁ n₂ A)
    (P P' : CStarMatrix m₂ n₁ A) (Q Q' : CStarMatrix m₂ n₂ A) :
    fromBlocks M N P Q + fromBlocks M' N' P' Q' =
      fromBlocks (M + M') (N + N') (P + P') (Q + Q') := by
  apply ofMatrix.symm.injective
  simp [Matrix.fromBlocks_add]

@[simp] theorem fromBlocks_neg [Neg A] (M : CStarMatrix m₁ n₁ A) (N : CStarMatrix m₁ n₂ A)
    (P : CStarMatrix m₂ n₁ A) (Q : CStarMatrix m₂ n₂ A) :
    -fromBlocks M N P Q = fromBlocks (-M) (-N) (-P) (-Q) := by
  apply ofMatrix.symm.injective
  simp [Matrix.fromBlocks_neg]

@[simp] theorem fromBlocks_sub [Sub A] (M M' : CStarMatrix m₁ n₁ A) (N N' : CStarMatrix m₁ n₂ A)
    (P P' : CStarMatrix m₂ n₁ A) (Q Q' : CStarMatrix m₂ n₂ A) :
    fromBlocks M N P Q - fromBlocks M' N' P' Q' =
      fromBlocks (M - M') (N - N') (P - P') (Q - Q') := by
  ext (i | i) (j | j) <;> rfl

@[simp] theorem fromBlocks_smul [SMul R A] (r : R) (M : CStarMatrix m₁ n₁ A)
    (N : CStarMatrix m₁ n₂ A) (P : CStarMatrix m₂ n₁ A) (Q : CStarMatrix m₂ n₂ A) :
    r • fromBlocks M N P Q = fromBlocks (r • M) (r • N) (r • P) (r • Q) := by
  apply ofMatrix.symm.injective
  simp [Matrix.fromBlocks_smul]

@[simp] theorem fromBlocks_conjTranspose [Star A] (M : CStarMatrix m₁ n₁ A)
    (N : CStarMatrix m₁ n₂ A) (P : CStarMatrix m₂ n₁ A) (Q : CStarMatrix m₂ n₂ A) :
    (fromBlocks M N P Q).conjTranspose =
      fromBlocks M.conjTranspose P.conjTranspose N.conjTranspose Q.conjTranspose := by
  apply ofMatrix.symm.injective
  simp [Matrix.fromBlocks_conjTranspose]

@[simp] theorem fromBlocks_star [Star A] (M : CStarMatrix m₁ m₁ A) (N : CStarMatrix m₁ m₂ A)
    (P : CStarMatrix m₂ m₁ A) (Q : CStarMatrix m₂ m₂ A) :
    star (fromBlocks M N P Q) = fromBlocks (star M) P.conjTranspose N.conjTranspose (star Q) :=
  fromBlocks_conjTranspose M N P Q

@[simp] theorem fromBlocks_mul [Fintype n₁] [Fintype n₂] [NonUnitalNonAssocSemiring A]
    (M₁₁ : CStarMatrix m₁ n₁ A) (M₁₂ : CStarMatrix m₁ n₂ A)
    (M₂₁ : CStarMatrix m₂ n₁ A) (M₂₂ : CStarMatrix m₂ n₂ A)
    (N₁₁ : CStarMatrix n₁ o₁ A) (N₁₂ : CStarMatrix n₁ o₂ A)
    (N₂₁ : CStarMatrix n₂ o₁ A) (N₂₂ : CStarMatrix n₂ o₂ A) :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ * fromBlocks N₁₁ N₁₂ N₂₁ N₂₂ =
      fromBlocks (M₁₁ * N₁₁ + M₁₂ * N₂₁) (M₁₁ * N₁₂ + M₁₂ * N₂₂)
        (M₂₁ * N₁₁ + M₂₂ * N₂₁) (M₂₁ * N₁₂ + M₂₂ * N₂₂) := by
  apply ofMatrix.symm.injective
  simp [Matrix.fromBlocks_multiply]

@[simp] theorem fromBlocks_map (f : A → B) (M : CStarMatrix m₁ n₁ A) (N : CStarMatrix m₁ n₂ A)
    (P : CStarMatrix m₂ n₁ A) (Q : CStarMatrix m₂ n₂ A) :
    (fromBlocks M N P Q).map f = fromBlocks (M.map f) (N.map f) (P.map f) (Q.map f) := by
  ext (i | i) (j | j) <;> rfl

/-- A block-diagonal C⋆-matrix is unitary iff both diagonal blocks are unitary. -/
@[simp] theorem fromBlocks_zero₁₂_zero₂₁_mem_unitary_iff [Fintype m₁] [Fintype m₂]
    [DecidableEq m₁] [DecidableEq m₂] [Semiring A] [StarRing A]
    {u : CStarMatrix m₁ m₁ A} {v : CStarMatrix m₂ m₂ A} :
    fromBlocks u 0 0 v ∈ unitary (CStarMatrix (m₁ ⊕ m₂) (m₁ ⊕ m₂) A) ↔
      u ∈ unitary (CStarMatrix m₁ m₁ A) ∧ v ∈ unitary (CStarMatrix m₂ m₂ A) := by
  rw [← ofMatrix_symm_mem_unitary_iff, ofMatrix_symm_fromBlocks, ofMatrix_symm_zero,
    ofMatrix_symm_zero, Matrix.fromBlocks_zero_zero_mem_unitary_iff,
    ofMatrix_symm_mem_unitary_iff (M := u), ofMatrix_symm_mem_unitary_iff (M := v)]

end FromBlocks

/-! ### Corner inclusions and block direct sums -/

section Homomorphisms

section NonUnitalCorners

variable {R m n A : Type*} [Fintype m] [Fintype n] [Semiring R] [NonUnitalNonAssocSemiring A]
  [Module R A] [StarAddMonoid A]

/-- The block-diagonal embedding `(M, N) ↦ diag(M, N)` as a non-unital ⋆-algebra homomorphism. -/
def blockDiagNonUnitalStarAlgHom (R m n A : Type*) [Fintype m] [Fintype n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A] :
    CStarMatrix m m A × CStarMatrix n n A →⋆ₙₐ[R] CStarMatrix (m ⊕ n) (m ⊕ n) A :=
  { toFun := fun p => fromBlocks p.1 0 0 p.2, map_smul' := by simp, map_zero' := by simp,
    map_add' := by simp, map_mul' := by simp, map_star' := by simp }

@[simp] theorem blockDiagNonUnitalStarAlgHom_apply (p : CStarMatrix m m A × CStarMatrix n n A) :
    blockDiagNonUnitalStarAlgHom R m n A p = fromBlocks p.1 0 0 p.2 := (rfl)

theorem blockDiagNonUnitalStarAlgHom_injective :
    Function.Injective (blockDiagNonUnitalStarAlgHom R m n A) := fun ⟨_, _⟩ ⟨_, _⟩ h => by
  simp only [blockDiagNonUnitalStarAlgHom_apply, fromBlocks_inj, true_and] at h
  exact Prod.ext h.1 h.2

/-- The upper-left corner embedding `M ↦ diag(M, 0)` as a non-unital ⋆-algebra homomorphism. -/
def inlCornerHom (R m n A : Type*) [Fintype m] [Fintype n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A] :
    CStarMatrix m m A →⋆ₙₐ[R] CStarMatrix (m ⊕ n) (m ⊕ n) A :=
  (blockDiagNonUnitalStarAlgHom R m n A).comp
    (NonUnitalStarAlgHom.inl R (CStarMatrix m m A) (CStarMatrix n n A))

@[simp] theorem inlCornerHom_apply (M : CStarMatrix m m A) :
    inlCornerHom R m n A M = fromBlocks M 0 0 0 := (rfl)

theorem inlCornerHom_injective : Function.Injective (inlCornerHom R m n A) :=
  (blockDiagNonUnitalStarAlgHom_injective (R := R)).comp fun _ _ h => congrArg Prod.fst h

/-- The lower-right corner embedding `N ↦ diag(0, N)` as a non-unital ⋆-algebra homomorphism. -/
def inrCornerHom (R m n A : Type*) [Fintype m] [Fintype n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A] :
    CStarMatrix n n A →⋆ₙₐ[R] CStarMatrix (m ⊕ n) (m ⊕ n) A :=
  (blockDiagNonUnitalStarAlgHom R m n A).comp
    (NonUnitalStarAlgHom.inr R (CStarMatrix m m A) (CStarMatrix n n A))

@[simp] theorem inrCornerHom_apply (N : CStarMatrix n n A) :
    inrCornerHom R m n A N = fromBlocks 0 0 0 N := (rfl)

theorem inrCornerHom_injective : Function.Injective (inrCornerHom R m n A) :=
  (blockDiagNonUnitalStarAlgHom_injective (R := R)).comp fun _ _ h => congrArg Prod.snd h

end NonUnitalCorners

section UnitalCorners

variable {R m n A : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  [CommSemiring R] [Semiring A] [Algebra R A] [StarAddMonoid A]

/-- The block-diagonal embedding `(M, N) ↦ diag(M, N)` as a unital ⋆-algebra homomorphism. -/
def blockDiagStarAlgHom (R m n A : Type*) [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [CommSemiring R] [Semiring A] [Algebra R A] [StarAddMonoid A] :
    CStarMatrix m m A × CStarMatrix n n A →⋆ₐ[R] CStarMatrix (m ⊕ n) (m ⊕ n) A :=
  let g := blockDiagNonUnitalStarAlgHom R m n A
  { toFun := g
    map_one' := fromBlocks_one
    map_mul' := _root_.map_mul g
    map_zero' := _root_.map_zero g
    map_add' := _root_.map_add g
    commutes' := fun _ => by ext (i | i) (j | j) <;> simp [g, algebraMap_apply]
    map_star' := map_star g }

@[simp] theorem blockDiagStarAlgHom_apply (p : CStarMatrix m m A × CStarMatrix n n A) :
    blockDiagStarAlgHom R m n A p = fromBlocks p.1 0 0 p.2 := (rfl)

theorem blockDiagStarAlgHom_injective :
    Function.Injective (blockDiagStarAlgHom R m n A) :=
  blockDiagNonUnitalStarAlgHom_injective (R := R) (m := m) (n := n) (A := A)

end UnitalCorners

end Homomorphisms

/-! ### Block C⋆-norms and positivity -/

section Norms

variable {m n A : Type*} [Fintype m] [Fintype n] [NonUnitalCStarAlgebra A]
  [PartialOrder A] [StarOrderedRing A]

/-- The norm of a block-diagonal C⋆-matrix is the maximum of the norms of its diagonal blocks. -/
@[simp] theorem norm_fromBlocks_zero₁₂_zero₂₁ (M : CStarMatrix m m A) (N : CStarMatrix n n A) :
    ‖fromBlocks M 0 0 N‖ = max ‖M‖ ‖N‖ := by
  simpa [Prod.norm_def] using NonUnitalStarAlgHom.norm_map (blockDiagNonUnitalStarAlgHom ℂ m n A)
    (blockDiagNonUnitalStarAlgHom_injective (R := ℂ)) (M, N)

/-- Embedding a rectangular matrix into the upper-right off-diagonal block preserves the norm. -/
@[simp] theorem norm_fromBlocks_zero₁₁_zero₂₁_zero₂₂ (V : CStarMatrix m n A) :
    ‖fromBlocks (0 : CStarMatrix m m A) V (0 : CStarMatrix n m A) (0 : CStarMatrix n n A)‖ =
      ‖V‖ := by
  let B : CStarMatrix (m ⊕ n) (m ⊕ n) A := fromBlocks 0 V 0 0
  have hnorm_out (x : C⋆ᵐᵒᵈ(A, (m ⊕ n) → A)) :
      ‖toCLM B x‖ =
        ‖toCLM V ((WithCStarModule.equiv A (m → A)).symm (fun i => x (Sum.inl i)))‖ := by
    rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := A) (toCLM B x),
      CStarModule.norm_eq_sqrt_norm_inner_self (A := A) (toCLM V _)]
    congr 2
    simp only [toCLM_apply_eq_sum, WithCStarModule.pi_inner, WithCStarModule.equiv_symm_pi_apply,
      Fintype.sum_sum_type, B, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
      fromBlocks_apply₂₂, zero_apply, mul_zero, Finset.sum_const_zero, add_zero, zero_add,
      CStarModule.inner_zero_right]
  refine le_antisymm ?_ ?_
  · rw [norm_def]
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg V) fun x => ?_
    let xₗ : C⋆ᵐᵒᵈ(A, m → A) := (WithCStarModule.equiv A (m → A)).symm (fun i => x (Sum.inl i))
    have hnorm_le : ‖xₗ‖ ≤ ‖x‖ := by
      rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := A) xₗ,
        CStarModule.norm_eq_sqrt_norm_inner_self (A := A) x]
      refine Real.sqrt_le_sqrt (CStarAlgebra.norm_le_norm_of_le_of_nonneg ?_
        (CStarModule.inner_self_nonneg (E := C⋆ᵐᵒᵈ(A, m → A))))
      rw [WithCStarModule.pi_inner, WithCStarModule.pi_inner, Fintype.sum_sum_type]
      exact le_add_of_le_of_nonneg le_rfl (Finset.sum_nonneg fun _ _ =>
        CStarModule.inner_self_nonneg (E := A))
    rw [hnorm_out x]
    exact ((toCLM V).le_opNorm xₗ).trans (mul_le_mul_of_nonneg_left hnorm_le (norm_nonneg V))
  · rw [norm_def]
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun y => ?_
    let x : C⋆ᵐᵒᵈ(A, (m ⊕ n) → A) :=
      (WithCStarModule.equiv A ((m ⊕ n) → A)).symm (Sum.elim (fun i => y i) 0)
    have hnorm_in : ‖x‖ = ‖y‖ := by
      rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := A) x,
        CStarModule.norm_eq_sqrt_norm_inner_self (A := A) y]
      congr 2
      simp only [WithCStarModule.pi_inner, WithCStarModule.equiv_symm_pi_apply,
        Fintype.sum_sum_type, x, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply,
        CStarModule.inner_zero_right, Finset.sum_const_zero, add_zero]
    have hproj : (WithCStarModule.equiv A (m → A)).symm (fun i => x (Sum.inl i)) = y := by
      ext i; simp [x]
    rw [← hnorm_in, ← hproj, ← hnorm_out x]
    exact (toCLM B).le_opNorm x

/-- Rectangular C⋆-identity `‖Vᴴ * V‖ = ‖V‖ * ‖V‖`. -/
@[simp] theorem norm_conjTranspose_mul_self (V : CStarMatrix m n A) :
    ‖V.conjTranspose * V‖ = ‖V‖ * ‖V‖ := by
  simpa only [fromBlocks_star, star_zero, conjTranspose_zero, fromBlocks_mul, CStarMatrix.mul_zero,
    CStarMatrix.zero_mul, add_zero, zero_add, norm_fromBlocks_zero₁₂_zero₂₁, norm_zero,
    max_eq_right (norm_nonneg _), norm_fromBlocks_zero₁₁_zero₂₁_zero₂₂] using
    CStarRing.norm_star_mul_self
      (x := fromBlocks (0 : CStarMatrix m m A) V 0 (0 : CStarMatrix n n A))

/-- Rectangular C⋆-identity `‖V * Vᴴ‖ = ‖V‖ * ‖V‖`. -/
@[simp] theorem norm_self_mul_conjTranspose (V : CStarMatrix m n A) :
    ‖V * V.conjTranspose‖ = ‖V‖ * ‖V‖ := by
  simpa only [fromBlocks_star, star_zero, conjTranspose_zero, fromBlocks_mul, CStarMatrix.mul_zero,
    CStarMatrix.zero_mul, add_zero, zero_add, norm_fromBlocks_zero₁₂_zero₂₁, norm_zero,
    max_eq_left (norm_nonneg _), norm_fromBlocks_zero₁₁_zero₂₁_zero₂₂] using
    CStarRing.norm_self_mul_star
      (x := fromBlocks (0 : CStarMatrix m m A) V 0 (0 : CStarMatrix n n A))

/-- Conjugate transpose is isometric on rectangular C⋆-matrices. -/
@[simp] theorem norm_conjTranspose (V : CStarMatrix m n A) : ‖V.conjTranspose‖ = ‖V‖ := by
  have hsq : ‖V.conjTranspose‖ * ‖V.conjTranspose‖ = ‖V‖ * ‖V‖ := by
    rw [← norm_conjTranspose_mul_self, conjTranspose_conjTranspose, norm_self_mul_conjTranspose]
  nlinarith [norm_nonneg V, norm_nonneg V.conjTranspose]

/-- For every rectangular C⋆-matrix `V`, `Vᴴ * V` is positive in the spectral order. -/
theorem conjTranspose_mul_self_nonneg (V : CStarMatrix m n A) : 0 ≤ V.conjTranspose * V := by
  rw [← NonUnitalStarAlgHom.map_le_map_iff (inrCornerHom ℂ m n A)
    (inrCornerHom_injective (R := ℂ)), _root_.map_zero, inrCornerHom_apply]
  have h : fromBlocks (0 : CStarMatrix m m A) 0 0 (V.conjTranspose * V) =
      star (fromBlocks (0 : CStarMatrix m m A) V 0 0) * fromBlocks (0 : CStarMatrix m m A) V 0 0 :=
    by simp
  exact h ▸ star_mul_self_nonneg _

/-- For every rectangular C⋆-matrix `V`, `V * Vᴴ` is positive in the spectral order. -/
theorem self_mul_conjTranspose_nonneg (V : CStarMatrix m n A) : 0 ≤ V * V.conjTranspose := by
  simpa only [conjTranspose_conjTranspose] using conjTranspose_mul_self_nonneg V.conjTranspose

end Norms

/-! ### Reindexing, associativity, and commutativity -/

section Reindexing

variable {m₁ m₂ m₃ R A : Type*}

/-- Reindexing along `Equiv.sumAssoc` reassociates block-diagonal direct sums. -/
theorem reindexₐ_sumAssoc_fromBlocks [Fintype m₁] [Fintype m₂] [Fintype m₃]
    [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A] [Star A]
    (M : CStarMatrix m₁ m₁ A) (N : CStarMatrix m₂ m₂ A) (P : CStarMatrix m₃ m₃ A) :
    reindexₐ R A (Equiv.sumAssoc m₁ m₂ m₃) (fromBlocks (fromBlocks M 0 0 N) 0 0 P) =
      fromBlocks M 0 0 (fromBlocks N 0 0 P) := by
  ext (i | (i | i)) (j | (j | j)) <;> rfl

/-- Reindexing along `Equiv.sumComm` swaps the diagonal blocks of a block-diagonal matrix. -/
theorem reindexₐ_sumComm_fromBlocks [Fintype m₁] [Fintype m₂]
    [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A] [Star A]
    (M : CStarMatrix m₁ m₁ A) (N : CStarMatrix m₂ m₂ A) :
    reindexₐ R A (Equiv.sumComm m₁ m₂) (fromBlocks M 0 0 N) = fromBlocks N 0 0 M := by
  ext (i | i) (j | j) <;> rfl

end Reindexing

/-! ### Explicit 2×2 block rotation unitaries and path -/

section BlockRotation

open scoped unitInterval

variable {n A : Type*} [Fintype n] [DecidableEq n]

section RingRotation

variable [Ring A] [StarRing A] [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
  [StarModule ℝ A]

/-- The 2×2 block rotation unitary `[[cos θ, -sin θ], [sin θ, cos θ]]` in
`unitary (CStarMatrix (n ⊕ n) (n ⊕ n) A)`. -/
noncomputable def blockRotation (θ : ℝ) : unitary (CStarMatrix (n ⊕ n) (n ⊕ n) A) :=
  ⟨fromBlocks (Real.cos θ • (1 : CStarMatrix n n A)) (-(Real.sin θ • 1))
    (Real.sin θ • 1) (Real.cos θ • 1), by
    have htrig : Real.cos θ * Real.cos θ + Real.sin θ * Real.sin θ = 1 := by
      simpa [sq] using Real.cos_sq_add_sin_sq θ
    have htrig' : Real.sin θ * Real.sin θ + Real.cos θ * Real.cos θ = 1 :=
      (add_comm _ _).trans htrig
    constructor <;>
    · simp only [fromBlocks_star, star_smul, star_trivial, star_one, conjTranspose_neg,
        conjTranspose_smul, conjTranspose_one, fromBlocks_mul, CStarMatrix.neg_mul,
        CStarMatrix.mul_neg, smul_neg, neg_neg, CStarMatrix.smul_mul, CStarMatrix.mul_smul,
        smul_smul, CStarMatrix.one_mul, ← fromBlocks_one, fromBlocks_inj]
      simp only [← add_smul, ← neg_smul, mul_comm (Real.cos θ) (Real.sin θ), neg_add_cancel,
        add_neg_cancel, zero_smul, htrig, htrig', one_smul, and_self]⟩

@[simp] theorem coe_blockRotation (θ : ℝ) :
    (blockRotation (n := n) (A := A) θ : CStarMatrix (n ⊕ n) (n ⊕ n) A) =
      fromBlocks (Real.cos θ • (1 : CStarMatrix n n A)) (-(Real.sin θ • 1))
        (Real.sin θ • 1) (Real.cos θ • 1) := (rfl)

@[simp] theorem blockRotation_zero : blockRotation (n := n) (A := A) 0 = 1 :=
  Subtype.ext <| by simp

/-- Rotation by `π / 2` is the signed block swap `[[0, -1], [1, 0]]`. -/
theorem coe_blockRotation_pi_div_two :
    (blockRotation (n := n) (A := A) (Real.pi / 2) : CStarMatrix (n ⊕ n) (n ⊕ n) A) =
      fromBlocks 0 (-1) 1 0 := by simp [Real.cos_pi_div_two, Real.sin_pi_div_two]

/-- Conjugating `diag(M, N)` by the `π / 2` rotation swaps the diagonal blocks to `diag(N, M)`. -/
theorem blockRotation_pi_div_two_conj (M N : CStarMatrix n n A) :
    (blockRotation (n := n) (A := A) (Real.pi / 2) : CStarMatrix (n ⊕ n) (n ⊕ n) A) *
        fromBlocks M 0 0 N *
        star (blockRotation (n := n) (A := A) (Real.pi / 2) : CStarMatrix (n ⊕ n) (n ⊕ n) A) =
      fromBlocks N 0 0 M := by
  rw [coe_blockRotation_pi_div_two]; simp

end RingRotation

section CStarRotation

variable [CStarAlgebra A]

/-- The real-angle map `θ ↦ blockRotation θ` into the unitary group of the block matrix algebra
`CStarMatrix (n ⊕ n) (n ⊕ n) A` is continuous. -/
theorem continuous_blockRotation : Continuous (blockRotation (n := n) (A := A)) := by
  rw [continuous_induced_rng]
  have h : Subtype.val ∘ blockRotation (n := n) (A := A) =
      fun θ => ofMatrixL (Matrix.fromBlocks (Real.cos θ • (1 : Matrix n n A))
        (-(Real.sin θ • 1)) (Real.sin θ • 1) (Real.cos θ • 1)) := by
    funext θ
    apply ofMatrix.symm.injective
    simp [Function.comp_apply, coe_blockRotation, ← ofMatrix_eq_ofMatrixL]
  rw [h]
  exact ofMatrixL.continuous.comp
    (Continuous.matrix_fromBlocks (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop))

/-- The continuous path `t ↦ blockRotation (t * θ)` joining `1` to `blockRotation θ`. -/
noncomputable def blockRotationPath (θ : ℝ) :
    Path (1 : unitary (CStarMatrix (n ⊕ n) (n ⊕ n) A)) (blockRotation θ) where
  toFun t := blockRotation ((t : ℝ) * θ)
  continuous_toFun := continuous_blockRotation.comp (continuous_subtypeVal.mul continuous_const)
  source' := by simp
  target' := by simp

@[simp] theorem blockRotationPath_apply (θ : ℝ) (t : I) :
    blockRotationPath (n := n) (A := A) θ t = blockRotation ((t : ℝ) * θ) := (rfl)

/-- Every `blockRotation θ` lies in the identity path component of the unitary group. -/
theorem joined_one_blockRotation (θ : ℝ) :
    Joined (1 : unitary (CStarMatrix (n ⊕ n) (n ⊕ n) A)) (blockRotation θ) :=
  ⟨blockRotationPath θ⟩

end CStarRotation

end BlockRotation

end CStarMatrix
