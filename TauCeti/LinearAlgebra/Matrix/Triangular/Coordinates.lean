/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.Block
import TauCeti.LinearAlgebra.Matrix.Triangular
import TauCeti.LinearAlgebra.Pi

/-!
# Triangular matrix coordinates

Split a square matrix into its upper triangular and strict lower entries. For an upper
triangular matrix, the strict lower part of its commutator depends only on the strict lower
entries of the other matrix, and its determinant is a product of diagonal gaps.
-/

public section

noncomputable section

namespace TauCeti

open Matrix

/-- A strict lower entry indexed by its transposed position. -/
abbrev SchurLowerIndex (ι : Type*) [LT ι] := {ij : ι × ι // ij.1 < ij.2}

/-- The upper triangular entries, including the diagonal, and the strict lower entries,
with the latter indexed by their transposed positions. -/
abbrev SchurCoordinates (ι : Type*) [LE ι] [LT ι] (R : Type*) :=
  ({ij : ι × ι // ij.1 ≤ ij.2} → R) × (SchurLowerIndex ι → R)

variable {ι : Type*} [LinearOrder ι] {R : Type*} [Semiring R]

/-- Transpose a strict upper position to index the complementary strict lower entries. -/
def schurLowerIndexEquiv (ι : Type*) [LinearOrder ι] :
    SchurLowerIndex ι ≃ {ij : ι × ι // ¬ij.1 ≤ ij.2} :=
  (Equiv.prodComm _ _).subtypeEquiv fun _ ↦ not_le.symm

/-- The lower index has the transposed pair as its underlying value. -/
@[simp] theorem schurLowerIndexEquiv_apply_val (ij : SchurLowerIndex ι) :
    (schurLowerIndexEquiv ι ij).val = (ij.val.2, ij.val.1) := (rfl)

/-- The inverse lower index reindexing swaps the entries of the underlying pair. -/
@[simp] theorem schurLowerIndexEquiv_symm_apply_val (ij : {ij : ι × ι // ¬ij.1 ≤ ij.2}) :
    ((schurLowerIndexEquiv ι).symm ij).val = (ij.val.2, ij.val.1) := (rfl)

/-- Assemble a matrix from the two parts of its Schur coordinates. -/
def schurMatrixEquiv : SchurCoordinates ι R ≃ₗ[R] Matrix ι ι R :=
  ((Matrix.ofLinearEquiv R).symm.trans <|
    (LinearEquiv.curry R R ι ι).symm.trans <|
      (LinearEquiv.piEquivPiSubtypeProd R (fun ij : ι × ι ↦ ij.1 ≤ ij.2)
        (fun _ ↦ R)).trans <|
        (LinearEquiv.refl R _).prodCongr
          (LinearEquiv.funCongrLeft R R (schurLowerIndexEquiv ι))).symm

/-- The first coordinate reads the upper triangular entries. -/
@[simp] theorem _root_.Matrix.schurMatrixEquiv_symm_fst (A : Matrix ι ι R)
    (ij : {ij : ι × ι // ij.1 ≤ ij.2}) :
    (schurMatrixEquiv.symm A).1 ij = A ij.val.1 ij.val.2 := by
  simp [schurMatrixEquiv, Function.uncurry]

/-- The second coordinate reads the strict lower entries. -/
@[simp] theorem _root_.Matrix.schurMatrixEquiv_symm_snd (A : Matrix ι ι R)
    (ij : SchurLowerIndex ι) :
    (schurMatrixEquiv.symm A).2 ij = A ij.val.2 ij.val.1 := by
  simp [schurMatrixEquiv, Function.uncurry]

/-- At an upper triangular position the assembled matrix reads the first coordinate. -/
@[simp] theorem schurMatrixEquiv_apply_of_le (x : SchurCoordinates ι R) {i j : ι}
    (h : i ≤ j) : schurMatrixEquiv x i j = x.1 ⟨(i, j), h⟩ := by
  have he := schurMatrixEquiv_symm_fst (schurMatrixEquiv x) ⟨(i, j), h⟩
  rw [LinearEquiv.symm_apply_apply] at he
  exact he.symm

/-- At a strict lower position the assembled matrix reads the second coordinate. -/
@[simp] theorem schurMatrixEquiv_apply_of_gt (x : SchurCoordinates ι R) {i j : ι}
    (h : j < i) : schurMatrixEquiv x i j = x.2 ⟨(j, i), h⟩ := by
  have he := schurMatrixEquiv_symm_snd (schurMatrixEquiv x) ⟨(j, i), h⟩
  rw [LinearEquiv.symm_apply_apply] at he
  exact he.symm

/-- The assembled matrix is upper triangular exactly when its strict lower coordinates vanish. -/
@[simp] theorem isUpperTriangular_schurMatrixEquiv_iff (x : SchurCoordinates ι R) :
    (schurMatrixEquiv x).IsUpperTriangular ↔ x.2 = 0 := by
  constructor
  · intro hx
    funext ij
    rw [← schurMatrixEquiv_apply_of_gt x ij.property]
    exact hx ij.property
  · intro hx i j h
    rw [schurMatrixEquiv_apply_of_gt x (by simpa only [id_eq] using h), hx]
    rfl

/-- A singleton in the upper coordinates assembles to a single matrix entry. -/
@[simp] theorem schurMatrixEquiv_single_upper (ij : {ij : ι × ι // ij.1 ≤ ij.2}) (a : R) :
    schurMatrixEquiv (Pi.single ij a, 0) = Matrix.single ij.val.1 ij.val.2 a := by
  ext i j
  rcases le_or_gt i j with h | h
  · have he : (⟨(i, j), h⟩ : {ij : ι × ι // ij.1 ≤ ij.2}) = ij ↔
        ij.val.1 = i ∧ ij.val.2 = j := by
      rw [eq_comm, Subtype.ext_iff, Prod.ext_iff]
    simp only [schurMatrixEquiv_apply_of_le _ h, Pi.single_apply, Matrix.single_apply, he]
  · simp only [schurMatrixEquiv_apply_of_gt _ h, Pi.zero_apply, Matrix.single_apply]
    split_ifs with he
    · exact (h.not_ge (he.1 ▸ he.2 ▸ ij.property)).elim
    · rfl

/-- A singleton in the strict lower coordinates assembles to the transposed matrix entry. -/
@[simp] theorem schurMatrixEquiv_single_lower (ij : SchurLowerIndex ι) (a : R) :
    schurMatrixEquiv (0, Pi.single ij a) = Matrix.single ij.val.2 ij.val.1 a := by
  ext i j
  by_cases h : j < i
  · have he : (⟨(j, i), h⟩ : SchurLowerIndex ι) = ij ↔
        ij.val.2 = i ∧ ij.val.1 = j := by
      rw [eq_comm, Subtype.ext_iff]
      exact Prod.ext_iff.trans and_comm
    simp only [schurMatrixEquiv_apply_of_gt _ h, Pi.single_apply, Matrix.single_apply, he]
  · simp only [schurMatrixEquiv_apply_of_le _ (le_of_not_gt h), Pi.zero_apply,
      Matrix.single_apply]
    split_ifs with he
    · exact (h (he.2 ▸ he.1 ▸ ij.property)).elim
    · rfl

section CommRing

variable [Fintype ι] {S : Type*} [CommRing S]

/-- For any matrix `T`, extend the strict lower entries `x` by zero on the upper triangle to form
`K = schurMatrixEquiv (0, x)`, then read the strict lower entries of `K * T - T * K`.
When `T` is upper triangular, any matrix with strict lower entries `x` gives the same result by
`Matrix.IsUpperTriangular.schurLowerCommutator_eq`. -/
def _root_.Matrix.schurLowerCommutator (T : Matrix ι ι S) :
    (SchurLowerIndex ι → S) →ₗ[S] (SchurLowerIndex ι → S) :=
  let L := schurMatrixEquiv.toLinearMap.comp (LinearMap.inr S _ _)
  let P := (LinearMap.snd S _ _).comp schurMatrixEquiv.symm.toLinearMap
  P.comp (((LinearMap.mulRight S T).comp L) - ((LinearMap.mulLeft S T).comp L))

/-- Evaluate the strict-lower commutator at the entry indexed by the transposed position `ij`. -/
theorem _root_.Matrix.schurLowerCommutator_apply (T : Matrix ι ι S)
    (x : SchurLowerIndex ι → S) (ij : SchurLowerIndex ι) :
    schurLowerCommutator T x ij =
      (schurMatrixEquiv (0, x) * T - T * schurMatrixEquiv (0, x)) ij.val.2 ij.val.1 := by
  simp only [schurLowerCommutator, LinearMap.comp_apply, LinearMap.snd_apply,
    LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.inr_apply, LinearMap.mulRight_apply,
    LinearMap.mulLeft_apply, schurMatrixEquiv_symm_snd]

private theorem toMatrix'_schurLowerCommutator (T : Matrix ι ι S)
    (ij kl : SchurLowerIndex ι) :
    LinearMap.toMatrix' (schurLowerCommutator T) ij kl =
      (if ij.val.2 = kl.val.2 then T kl.val.1 ij.val.1 else 0) -
        (if ij.val.1 = kl.val.1 then T ij.val.2 kl.val.2 else 0) := by
  simp only [LinearMap.toMatrix'_apply, schurLowerCommutator_apply, schurMatrixEquiv_single_lower,
    Matrix.sub_apply]
  obtain ⟨⟨i, j⟩, hij⟩ := ij
  obtain ⟨⟨k, l⟩, hkl⟩ := kl
  dsimp only
  by_cases hj : j = l
  · subst l
    by_cases hi : i = k
    · subst k
      simp [single_mul_apply_same, mul_single_apply_same]
    · simp [hi, single_mul_apply_same, mul_single_apply_of_ne]
  · by_cases hi : i = k
    · subst k
      simp [hj, mul_single_apply_same, single_mul_apply_of_ne]
    · simp [hi, hj, mul_single_apply_of_ne, single_mul_apply_of_ne]

/-- The determinant of the strict-lower commutator with an upper triangular matrix is
the product of the differences of its diagonal entries. -/
theorem _root_.Matrix.IsUpperTriangular.det_schurLowerCommutator
    {T : Matrix ι ι S} (hT : T.IsUpperTriangular) :
    (schurLowerCommutator T).det = ∏ ij : SchurLowerIndex ι,
      (T ij.val.1 ij.val.1 - T ij.val.2 ij.val.2) := by
  -- Order lower positions by row and, within each row, by decreasing column.
  let rank (ij : SchurLowerIndex ι) : ι ×ₗ ιᵒᵈ :=
    toLex (ij.val.2, OrderDual.toDual ij.val.1)
  have hrank : Function.Injective rank := by
    intro ij kl h
    obtain ⟨h₁, h₂⟩ := Prod.mk.inj (congrArg ofLex h)
    exact Subtype.ext (Prod.ext h₂ h₁)
  have htri : (LinearMap.toMatrix' (schurLowerCommutator T)).BlockTriangular rank := by
    intro ij kl h
    rw [toMatrix'_schurLowerCommutator]
    have h' : kl.val.2 < ij.val.2 ∨
        (kl.val.2 = ij.val.2 ∧ ij.val.1 < kl.val.1) := by
      simpa only [rank, Prod.Lex.toLex_lt_toLex, OrderDual.toDual_lt_toDual] using h
    rcases h' with h' | ⟨he, h'⟩
    · simp [h'.ne', hT h']
    · simp [he, h'.ne, hT h']
  rw [← LinearMap.det_toMatrix', htri.det_eq_prod_diag hrank]
  exact Finset.prod_congr rfl fun ij _ ↦ by
    rw [toMatrix'_schurLowerCommutator]
    simp only [ite_true]

/-- The strict lower entries of the commutator with an upper triangular matrix depend
only on the strict lower entries of its first factor. -/
theorem _root_.Matrix.IsUpperTriangular.schurLowerCommutator_eq
    {T K : Matrix ι ι S} (hT : T.IsUpperTriangular) (ij : SchurLowerIndex ι) :
    schurLowerCommutator T (schurMatrixEquiv.symm K).2 ij =
      (K * T - T * K) ij.val.2 ij.val.1 := by
  let S := schurMatrixEquiv (0, (schurMatrixEquiv.symm K).2)
  have hS : (K - S).IsUpperTriangular := by
    intro i j h
    have hij : j < i := by simpa only [id_eq] using h
    dsimp only [S]
    rw [Matrix.sub_apply, schurMatrixEquiv_apply_of_gt _ hij, schurMatrixEquiv_symm_snd,
      sub_self]
  have hzero := ((hS.mul hT).sub (hT.mul hS)) ij.property
  rw [sub_mul, mul_sub] at hzero
  simp only [Matrix.sub_apply] at hzero
  rw [schurLowerCommutator_apply]
  rw [sub_sub_sub_comm] at hzero
  exact (sub_eq_zero.mp hzero).symm

end CommRing

end TauCeti
