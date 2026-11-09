/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.CommBialgCat
public import Mathlib.LinearAlgebra.Matrix.MvPolynomial
public import Mathlib.RingTheory.Coalgebra.GroupLike

/-!
# The matrix-monoid coordinate bialgebra

For a commutative semiring `R` and a finite type `ι`, this file equips the polynomial coordinate
algebra `R[Xᵢⱼ]` of square matrices indexed by `ι` with the explicit bialgebra structure dual to
matrix multiplication. Its comultiplication and counit satisfy

`Δ(Xᵢⱼ) = ∑ₖ Xᵢₖ ⊗ Xₖⱼ` and `ε(Xᵢⱼ) = if i = j then 1 else 0`.

The structure is a named `Bialgebra` value rather than a global instance. This distinction is
essential: `MvPolynomial` is definitionally an additive monoid algebra, and importing the
monoid-algebra bialgebra gives its variables a different, group-like comultiplication. Over a
commutative ring, `coordinateBialgebra` locally selects the matrix-coordinate structure and
stores it in a `CommBialgCat` object, providing a collision-free boundary for statements using
typeclass-selected coalgebra operations.

The determinant of the generic matrix is group-like for this bundled structure. This is the
algebraic input for subsequently localizing at the determinant to construct the coordinate Hopf
algebra of `GLₙ`; localization and the antipode are deliberately not constructed here.

The construction allows an empty index type and requires no nontriviality hypothesis on the
base.

## Main declarations

* `TauCeti.MatrixMonoid.comul`: matrix-multiplication comultiplication on `R[Xᵢⱼ]`.
* `TauCeti.MatrixMonoid.counit`: identity-matrix counit on `R[Xᵢⱼ]`.
* `TauCeti.MatrixMonoid.bialgebra`: the explicit matrix-coordinate bialgebra dictionary.
* `TauCeti.MatrixMonoid.coordinateBialgebra`: the selected commutative bialgebra object.
* `TauCeti.MatrixMonoid.isGroupLikeElem_determinant`: the generic determinant is group-like.

## References

The coordinate formulas are standard; see J. S. Milne, *Algebraic Groups*, §§3.3--3.6 and
4.2. The same construction appears in the Stacks Project, Example 39.5.4,
[Tag 022W](https://stacks.math.columbia.edu/tag/022W). The role of determinant localization in
constructing `GLₙ` is described in Milne, §2.8.
-/

public section

open scoped TensorProduct

namespace TauCeti

namespace MatrixMonoid

open Algebra.TensorProduct

universe u v

/-- The polynomial coordinate algebra of the monoid of square matrices over `R` indexed by `ι`. -/
abbrev CoordinateRing (R : Type u) [CommSemiring R] (ι : Type v) :=
  MvPolynomial (ι × ι) R

section Semiring

variable (R : Type u) [CommSemiring R] (ι : Type v) [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The comultiplication dual to multiplication of square matrices. -/
noncomputable def comul :
    CoordinateRing R ι →ₐ[R] CoordinateRing R ι ⊗[R] CoordinateRing R ι :=
  MvPolynomial.aeval fun ij : ι × ι =>
    ∑ k : ι, MvPolynomial.X (ij.1, k) ⊗ₜ[R] MvPolynomial.X (k, ij.2)

omit [Fintype ι] in
/-- The counit dual to the identity matrix. -/
noncomputable def counit : CoordinateRing R ι →ₐ[R] R :=
  MvPolynomial.aeval fun ij : ι × ι =>
    (1 : Matrix ι ι R) ij.1 ij.2

omit [DecidableEq ι] in
/-- The matrix-coordinate comultiplication sends a generic entry to the corresponding entry of
the product of the generic matrices in the two tensor factors. -/
@[simp]
theorem comul_X (i j : ι) :
    comul R ι (MvPolynomial.X (i, j)) =
      ∑ k : ι, MvPolynomial.X (i, k) ⊗ₜ[R] MvPolynomial.X (k, j) := by
  simp [comul]

omit [Fintype ι] in
/-- The matrix-coordinate counit sends a generic entry to the corresponding identity-matrix
entry. -/
@[simp]
theorem counit_X (i j : ι) :
    counit R ι (MvPolynomial.X (i, j)) = if i = j then 1 else 0 := by
  simp [counit, Matrix.one_apply]

omit [Fintype ι] in
/-- Applying the counit entrywise to the generic matrix gives the identity matrix. -/
@[simp]
theorem map_counit_genericMatrix :
    (Matrix.mvPolynomialX ι ι R).map (counit R ι) = 1 := by
  ext i j
  simp [Matrix.one_apply]

omit [DecidableEq ι] in
/-- Applying the comultiplication entrywise to the generic matrix gives the product of its
left-tensor and right-tensor copies. The order represents ordinary matrix multiplication, not
the opposite monoid. -/
@[simp]
theorem map_comul_genericMatrix :
    (Matrix.mvPolynomialX ι ι R).map (comul R ι) =
      (Matrix.mvPolynomialX ι ι R).map
          (includeLeft : CoordinateRing R ι →ₐ[R]
            CoordinateRing R ι ⊗[R] CoordinateRing R ι) *
        (Matrix.mvPolynomialX ι ι R).map
          (includeRight : CoordinateRing R ι →ₐ[R]
            CoordinateRing R ι ⊗[R] CoordinateRing R ι) := by
  ext i j
  simp [Matrix.mul_apply]

/-- The matrix-coordinate bialgebra structure on the polynomial algebra `R[Xᵢⱼ]`.

This is intentionally a named value, not an instance. Callers that need typeclass-selected
coalgebra operations should use `coordinateBialgebra`, or install this value in a deliberately
local scope. -/
@[instance_reducible]
noncomputable def bialgebra : Bialgebra R (CoordinateRing R ι) :=
  Bialgebra.ofAlgHom (comul R ι) (counit R ι)
    (by
      ext ⟨i, j⟩
      simpa [TensorProduct.sum_tmul, TensorProduct.tmul_sum] using Finset.sum_comm)
    (by ext ⟨i, j⟩; simp [TensorProduct.ite_tmul])
    (by ext ⟨i, j⟩; simp [TensorProduct.tmul_ite, eq_comm])

/-- Selecting `bialgebra R ι` makes its comultiplication the explicit matrix-multiplication map
`comul R ι`. The equality is heterogeneous because opacity also hides the dictionary's stored
module structure. -/
theorem bialgebra_comul :
    HEq (letI : Module R (CoordinateRing R ι) := (bialgebra R ι).toAlgebra.toModule
      letI : Coalgebra R (CoordinateRing R ι) := (bialgebra R ι).toCoalgebra
      Coalgebra.comul (R := R) (A := CoordinateRing R ι)) (comul R ι).toLinearMap :=
  heq_of_eq rfl

/-- Selecting `bialgebra R ι` makes its counit the explicit identity-matrix map `counit R ι`.
As for `bialgebra_comul`, opacity makes the map equality heterogeneous. -/
theorem bialgebra_counit :
    HEq (letI : Module R (CoordinateRing R ι) := (bialgebra R ι).toAlgebra.toModule
      letI : Coalgebra R (CoordinateRing R ι) := (bialgebra R ι).toCoalgebra
      Coalgebra.counit (R := R) (A := CoordinateRing R ι)) (counit R ι).toLinearMap :=
  heq_of_eq rfl

/-- Under `bialgebra R ι`, comultiplication has the matrix-multiplication formula on generators. -/
@[simp]
theorem bialgebra_comul_X (i j : ι) :
    letI : Module R (CoordinateRing R ι) := (bialgebra R ι).toAlgebra.toModule
    letI : Coalgebra R (CoordinateRing R ι) := (bialgebra R ι).toCoalgebra
    Coalgebra.comul (R := R) (A := CoordinateRing R ι) (MvPolynomial.X (i, j)) =
      ∑ k : ι, MvPolynomial.X (i, k) ⊗ₜ[R] MvPolynomial.X (k, j) := by
  rw [eq_of_heq (bialgebra_comul R ι), AlgHom.toLinearMap_apply, comul_X]

/-- Under `bialgebra R ι`, the counit has the identity-matrix formula on generators. -/
@[simp]
theorem bialgebra_counit_X (i j : ι) :
    letI : Module R (CoordinateRing R ι) := (bialgebra R ι).toAlgebra.toModule
    letI : Coalgebra R (CoordinateRing R ι) := (bialgebra R ι).toCoalgebra
    Coalgebra.counit (R := R) (A := CoordinateRing R ι) (MvPolynomial.X (i, j)) =
      if i = j then 1 else 0 := by
  rw [eq_of_heq (bialgebra_counit R ι), AlgHom.toLinearMap_apply, counit_X]

end Semiring

section Ring

variable (R : Type u) [CommRing R] (ι : Type v) [Fintype ι] [DecidableEq ι]

/-- Evaluating the generic determinant at the identity-matrix counit gives one. -/
@[simp]
theorem counit_determinant :
    counit R ι (Matrix.det (Matrix.mvPolynomialX ι ι R)) = 1 := by
  simp [AlgHom.map_det]

/-- Matrix-multiplication comultiplication sends the generic determinant to its tensor square. -/
@[simp]
theorem comul_determinant :
    comul R ι (Matrix.det (Matrix.mvPolynomialX ι ι R)) =
      Matrix.det (Matrix.mvPolynomialX ι ι R) ⊗ₜ[R]
        Matrix.det (Matrix.mvPolynomialX ι ι R) := by
  rw [AlgHom.map_det, AlgHom.mapMatrix_apply, map_comul_genericMatrix, Matrix.det_mul]
  simp [← AlgHom.mapMatrix_apply, ← AlgHom.map_det]

/-- The polynomial coordinate algebra of the matrix monoid, bundled with the selected
matrix-coordinate bialgebra structure.

The object stores `bialgebra R ι`; it does not depend on whichever bialgebra instance may be
available globally for the raw `MvPolynomial` carrier. -/
noncomputable def coordinateBialgebra : CommBialgCat R :=
  letI : Bialgebra R (CoordinateRing R ι) := bialgebra R ι
  CommBialgCat.of R (CoordinateRing R ι)

/-- The canonical algebra equivalence from the polynomial coordinate ring to the carrier of its
bundled matrix-coordinate bialgebra. -/
noncomputable def coordinateBialgebraAlgEquiv :
    CoordinateRing R ι ≃ₐ[R] coordinateBialgebra R ι :=
  letI : Bialgebra R (CoordinateRing R ι) := bialgebra R ι
  AlgEquiv.refl

/-- Mathlib has no `CommBialgCat.of_comul` lemma exposing the comultiplication stored by
`CommBialgCat.of`. This bridge isolates the two definitional equalities needed here:
`coordinateBialgebra` stores `(bialgebra R ι).toCoalgebra` on the raw coordinate ring, and
`coordinateBialgebraAlgEquiv` is the identity algebra equivalence on that carrier. After those
reductions, transporting the stored comultiplication is `Algebra.TensorProduct.map_id`. -/
private theorem coordinateBialgebra_comul_transport (x : CoordinateRing R ι) :
    Coalgebra.comul (R := R) (A := coordinateBialgebra R ι)
        (coordinateBialgebraAlgEquiv R ι x) =
      Algebra.TensorProduct.map (coordinateBialgebraAlgEquiv R ι).toAlgHom
          (coordinateBialgebraAlgEquiv R ι).toAlgHom
          ((bialgebra R ι).toCoalgebra.toCoalgebraStruct.comul x) :=
  (DFunLike.congr_fun Algebra.TensorProduct.map_id _).symm

/-- Mathlib has no `CommBialgCat.of_counit` lemma exposing the counit stored by
`CommBialgCat.of`. This bridge isolates the definitional equalities that `coordinateBialgebra`
stores `(bialgebra R ι).toCoalgebra` on the raw coordinate ring and that
`coordinateBialgebraAlgEquiv` is the identity algebra equivalence on that carrier. -/
private theorem coordinateBialgebra_counit_transport (x : CoordinateRing R ι) :
    Coalgebra.counit (R := R) (A := coordinateBialgebra R ι)
        (coordinateBialgebraAlgEquiv R ι x) =
      (bialgebra R ι).toCoalgebra.toCoalgebraStruct.counit x :=
  rfl

/-- Comultiplication on the bundled coordinate bialgebra agrees with the explicit
matrix-multiplication comultiplication after transport through `coordinateBialgebraAlgEquiv`. -/
@[simp low]
theorem coordinateBialgebra_comul_apply (x : CoordinateRing R ι) :
    Coalgebra.comul (R := R) (A := coordinateBialgebra R ι)
        (coordinateBialgebraAlgEquiv R ι x) =
      Algebra.TensorProduct.map (coordinateBialgebraAlgEquiv R ι).toAlgHom
          (coordinateBialgebraAlgEquiv R ι).toAlgHom (comul R ι x) := by
  rw [coordinateBialgebra_comul_transport, eq_of_heq (bialgebra_comul R ι),
    AlgHom.toLinearMap_apply]

/-- The counit on the bundled coordinate bialgebra agrees with the explicit identity-matrix
counit after transport through `coordinateBialgebraAlgEquiv`. -/
@[simp]
theorem coordinateBialgebra_counit_apply (x : CoordinateRing R ι) :
    Coalgebra.counit (R := R) (A := coordinateBialgebra R ι)
        (coordinateBialgebraAlgEquiv R ι x) = counit R ι x := by
  rw [coordinateBialgebra_counit_transport, eq_of_heq (bialgebra_counit R ι),
    AlgHom.toLinearMap_apply]

/-- The bundled coordinate bialgebra retains the matrix-multiplication comultiplication on its
generic entries. -/
@[simp]
theorem coordinateBialgebra_comul_X (i j : ι) :
    Coalgebra.comul (R := R) (A := coordinateBialgebra R ι)
        (coordinateBialgebraAlgEquiv R ι (MvPolynomial.X (i, j))) =
      (∑ k : ι,
        coordinateBialgebraAlgEquiv R ι (MvPolynomial.X (i, k)) ⊗ₜ[R]
          coordinateBialgebraAlgEquiv R ι (MvPolynomial.X (k, j)) :
        coordinateBialgebra R ι ⊗[R] coordinateBialgebra R ι) := by
  simp [coordinateBialgebra_comul_apply]

/-- The bundled coordinate bialgebra retains the identity-matrix counit on its generic
entries. -/
@[simp high]
theorem coordinateBialgebra_counit_X (i j : ι) :
    Coalgebra.counit (R := R) (A := coordinateBialgebra R ι)
        (coordinateBialgebraAlgEquiv R ι (MvPolynomial.X (i, j))) =
      if i = j then 1 else 0 := by
  rw [coordinateBialgebra_counit_apply, counit_X]

/-- The determinant of the generic matrix is group-like in the matrix-coordinate bialgebra. -/
theorem isGroupLikeElem_determinant :
    IsGroupLikeElem (A := coordinateBialgebra R ι) R
      (coordinateBialgebraAlgEquiv R ι
        (Matrix.det (Matrix.mvPolynomialX ι ι R))) := by
  constructor <;> simp [coordinateBialgebra_comul_apply]

end Ring

end MatrixMonoid

end TauCeti
