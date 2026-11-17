/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.CompletelyBounded
public import TauCeti.Analysis.CStarAlgebra.CompletelyPositiveMap

/-!
# Completely positive maps are completely bounded

For finite types `m` and `n`, an `m × m` matrix of `n × n` matrices over a C⋆-algebra `A` is an
`(m × n) × (m × n)` matrix over `A`, and the two C⋆-algebras `M_m(M_n(A))` and `M_{m × n}(A)`
are star isomorphic. So the amplification `φₙ : M_n(A) → M_n(B)` of a completely positive map
`φ : A → B` is again completely positive.

When `A` is unital, the bound `‖ψ a‖ ≤ ‖ψ 1‖ ‖a‖` for the `2`-positive map `ψ = φₙ` on the unital
C⋆-algebra `M_n(A)`, together with `‖φₙ 1‖ ≤ ‖φ 1‖`, gives the matrix bound
`‖φₙ x‖ ≤ ‖φ 1‖ ‖x‖` at every level. Hence `φ` is completely bounded and
`‖φ‖_cb = ‖φ‖ = ‖φ 1‖`.

## Main declarations

* `CStarMatrix.compStarAlgEquiv`: the star algebra isomorphism
  `M_m(M_n(A)) ≃ M_{m × n}(A)`.
* `CStarMatrix.diagonalNonUnitalStarAlgHom`: the diagonal embedding `b ↦ diag(b, …, b)` of `B`
  in `M_n(B)`.
* `CompletelyPositiveMap.mapCStarMatrix`: the amplification of a completely positive map, as a
  completely positive map.
* `CompletelyPositiveMapClass.norm_map_cstarMatrix_le`: the matrix bound `‖φₙ x‖ ≤ ‖φ 1‖ ‖x‖`
  for a completely positive map with unital domain.
* `CompletelyPositiveMapClass.isCompletelyBounded` and
  `CompletelyPositiveMapClass.cbNorm_eq_norm_map_one`: such a map is completely bounded with
  `‖φ‖_cb = ‖φ 1‖`, and `CompletelyPositiveMapClass.cbNorm_eq_opNorm_ofClass`: `‖φ‖_cb = ‖φ‖`.

## References

* B. Blackadar, *Operator Algebras*, II.6.9.4.
* V. Paulsen, *Completely Bounded Maps and Operator Algebras*, Proposition 3.6.
-/

public section

open scoped CStarAlgebra

namespace CStarMatrix

section Comp

variable (R m n A : Type*) [Fintype m] [Fintype n] [AddCommMonoid A] [Mul A] [Star A] [SMul R A]

/-- An `m × m` matrix of `n × n` matrices is an `(m × n) × (m × n)` matrix: `Matrix.comp` as a
star algebra isomorphism of C⋆-matrices. -/
def compStarAlgEquiv :
    CStarMatrix m m (CStarMatrix n n A) ≃⋆ₐ[R] CStarMatrix (m × n) (m × n) A where
  toFun M := ofMatrix (Matrix.comp m m n n A M)
  invFun M := (Matrix.comp m m n n A).symm (ofMatrix.symm M)
  left_inv := (Matrix.comp m m n n A).left_inv
  right_inv := (Matrix.comp m m n n A).right_inv
  map_add' _ _ := rfl
  map_mul' M N := by
    ext ⟨i, k⟩ ⟨j, l⟩
    change (M * N) i j k l = ∑ x : m × n, M i x.1 k x.2 * N x.1 j x.2 l
    simp only [mul_apply, sum_apply, Fintype.sum_prod_type]
  map_smul' _ _ := rfl
  map_star' M := by
    ext ⟨i, k⟩ ⟨j, l⟩
    change (star M) i j k l = star (M j i l k)
    simp only [star_apply]

variable {R m n A}

@[simp]
theorem compStarAlgEquiv_apply (M : CStarMatrix m m (CStarMatrix n n A)) (i j : m × n) :
    compStarAlgEquiv R m n A M i j = M i.1 j.1 i.2 j.2 :=
  (rfl)

/-- Applying a map entrywise commutes with `compStarAlgEquiv`. -/
theorem compStarAlgEquiv_map {B : Type*} [AddCommMonoid B] [Mul B] [Star B] [SMul R B]
    (M : CStarMatrix m m (CStarMatrix n n A)) (f : A → B) :
    compStarAlgEquiv R m n B (M.map (·.map f)) = (compStarAlgEquiv R m n A M).map f :=
  (rfl)

end Comp

section Diagonal

variable (R n B : Type*) [Fintype n] [DecidableEq n] [Monoid R] [NonUnitalNonAssocSemiring B]
  [StarAddMonoid B] [DistribMulAction R B]

/-- The diagonal embedding `b ↦ diag(b, …, b)` of `B` in `CStarMatrix n n B`. -/
def diagonalNonUnitalStarAlgHom : B →⋆ₙₐ[R] CStarMatrix n n B where
  toFun b := ofMatrix (Matrix.diagonal fun _ => b)
  map_smul' c b := by
    ext i j
    by_cases h : i = j <;> simp [ofMatrix_apply, h]
  map_zero' := by
    ext i j
    simp [ofMatrix_apply]
  map_add' a b := by
    ext i j
    by_cases h : i = j <;> simp [ofMatrix_apply, h]
  map_mul' a b := by
    ext i j
    simp only [ofMatrix_apply, mul_apply, Matrix.diagonal_apply, ite_mul, zero_mul, mul_ite,
      mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  map_star' b := by
    ext i j
    by_cases h : i = j
    · simp [ofMatrix_apply, star_apply, h]
    · simp [ofMatrix_apply, star_apply, h, Ne.symm h]

variable {R n B}

@[simp]
theorem diagonalNonUnitalStarAlgHom_apply (b : B) (i j : n) :
    diagonalNonUnitalStarAlgHom R n B b i j = if i = j then b else 0 :=
  Matrix.diagonal_apply ..

end Diagonal

/-- The diagonal matrix `diag(b, …, b)` has norm at most `‖b‖`. -/
theorem norm_diagonalNonUnitalStarAlgHom_le {n B : Type*} [Fintype n] [DecidableEq n]
    [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B] (b : B) :
    ‖diagonalNonUnitalStarAlgHom ℂ n B b‖ ≤ ‖b‖ :=
  NonUnitalStarAlgHom.norm_apply_le _ b

end CStarMatrix

namespace CompletelyPositiveMap

variable {A B : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- The amplification `φₙ : M_n(A) → M_n(B)` of a completely positive map `φ : A → B`, applying
`φ` entrywise, is completely positive. -/
def mapCStarMatrix (φ : A →CP B) (n : Type*) [Fintype n] :
    CStarMatrix n n A →CP CStarMatrix n n B where
  toLinearMap := CStarMatrix.mapₗ φ.toLinearMap
  map_cstarMatrix_nonneg' k M hM := by
    let eA := CStarMatrix.compStarAlgEquiv ℂ (Fin k) n A
    let eB := CStarMatrix.compStarAlgEquiv ℂ (Fin k) n B
    have hM' : 0 ≤ eA M := by simpa using (map_le_map_iff eA).mpr hM
    rw [← map_le_map_iff eB, map_zero]
    exact φ.map_cstarMatrix_nonneg _ hM'

@[simp]
theorem mapCStarMatrix_apply (φ : A →CP B) {n : Type*} [Fintype n] (x : CStarMatrix n n A) :
    mapCStarMatrix φ n x = x.map φ :=
  (rfl)

end CompletelyPositiveMap

namespace CompletelyPositiveMapClass

open LinearMap

variable {A B F : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B] [FunLike F A B]
  [LinearMapClass F ℂ A B] [CompletelyPositiveMapClass F A B]

/-- The matrix bound for a completely positive map with unital domain: every amplification of
`φ` is bounded by `‖φ 1‖`, so `‖φₙ x‖ ≤ ‖φ 1‖ ‖x‖`. -/
theorem norm_map_cstarMatrix_le (φ : F) {n : Type*} [Fintype n] (x : CStarMatrix n n A) :
    ‖x.map φ‖ ≤ ‖φ 1‖ * ‖x‖ := by
  classical
  let ψ := CompletelyPositiveMap.mapCStarMatrix (φ : A →CP B) n
  have h1 : ψ 1 = CStarMatrix.diagonalNonUnitalStarAlgHom ℂ n B (φ 1) := by
    ext i j
    change φ ((1 : CStarMatrix n n A) i j) = _
    by_cases h : i = j <;> simp [CStarMatrix.one_apply, h]
  calc ‖x.map φ‖ = ‖ψ x‖ := rfl
    _ ≤ ‖ψ 1‖ * ‖x‖ := norm_apply_le ψ x
    _ ≤ ‖φ 1‖ * ‖x‖ := by
      rw [h1]
      gcongr
      exact CStarMatrix.norm_diagonalNonUnitalStarAlgHom_le _

/-- A completely positive map with unital domain is completely bounded. -/
theorem isCompletelyBounded (φ : F) : (φ : A →ₗ[ℂ] B).IsCompletelyBounded :=
  isCompletelyBounded_iff_exists_bound.mpr ⟨‖φ 1‖, fun _ x => norm_map_cstarMatrix_le φ x⟩

/-- The cb norm of a completely positive map with unital domain is `‖φ 1‖`. -/
theorem cbNorm_eq_norm_map_one (φ : F) : (φ : A →ₗ[ℂ] B).cbNorm = ‖φ 1‖ := by
  refine le_antisymm (cbNorm_le_of_bound (norm_nonneg _) fun _ x =>
    norm_map_cstarMatrix_le φ x) ?_
  rcases subsingleton_or_nontrivial A with hA | hA
  · simp [Subsingleton.elim (1 : A) 0]
  simpa using norm_apply_le_cbNorm_mul (isCompletelyBounded φ) (1 : A)

/-- The cb norm of a completely positive map with unital domain is its operator norm, for the
continuous linear map `PositiveContinuousLinearMap.ofClass φ`. -/
theorem cbNorm_eq_opNorm_ofClass (φ : F) :
    (φ : A →ₗ[ℂ] B).cbNorm =
      ‖((PositiveContinuousLinearMap.ofClass φ : A →P[ℂ] B) : A →L[ℂ] B)‖ := by
  rw [cbNorm_eq_norm_map_one, opNorm_ofClass_eq_norm_map_one]

end CompletelyPositiveMapClass
