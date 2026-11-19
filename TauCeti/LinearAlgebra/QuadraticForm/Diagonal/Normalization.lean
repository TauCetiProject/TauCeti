/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.SesquilinearForm.Orthogonal
public import TauCeti.LinearAlgebra.QuadraticForm.Diagonal.Basic

/-!
# Normalized bases and the sum-of-squares normalization

Let `Q` be a quadratic form over a commutative ring `R` in which `2` is invertible. A basis `b` of
its module is *normalized* when it is orthogonal for `Q` and every `Q (b i)` equals `1`, that is,
when its Gram matrix `Q.toMatrix b` is the identity. Coordinates in such a basis are an isometry
from `Q` to the standard sum of squares `QuadraticMap.weightedSumSquares R 1`, and conversely every
isometry to the sum of squares arises in this way, from the preimage of the standard basis.

Any orthogonal basis `b` becomes normalized once each `b i` is divided by a chosen unit square root
`c i` of `Q (b i)`. The resulting isometry to the sum of squares is the *specified normalization*
of the data `(b, c)`: it sends `b i` to `c i` times the `i`-th coordinate vector. Different square
roots give different isometries, so the choice is part of the data and is retained in every
statement. Over a separably closed field of characteristic different from two such square roots
always exist, so a finite-dimensional nondegenerate form has a normalized basis; this is
`QuadraticForm.exists_toMatrix_eq_one_of_isSepClosed` in
`TauCeti.LinearAlgebra.QuadraticForm.SepClosed`.

Normalized bases are the input of the coordinate comparisons for Clifford algebras: in a
normalized basis the Clifford generators square to `1`, and transporting along the specified
normalization identifies the Clifford algebra of `Q` with that of the sum of squares.

## Main definitions

* `QuadraticForm.isometryEquivSumSquaresOfIsOrthoᵢ`: the isometry from `Q` to the sum of squares
  given by the coordinates in a normalized basis.
* `QuadraticForm.isometryEquivSumSquaresOfMulSelf`: the specified normalization of an orthogonal
  basis together with chosen unit square roots of its values.

## Main results

* `QuadraticForm.apply_inv_smul_eq_one_of_mul_self`: dividing a vector by a unit square root of
  its value normalizes that value to `1`.
* `QuadraticForm.toMatrix_eq_diagonal_iff`, `QuadraticForm.toMatrix_eq_one_iff`: the Gram matrix of
  a basis is diagonal with prescribed entries exactly when the basis is orthogonal with those
  values; it is the identity exactly when the basis is normalized.
* `QuadraticForm.toMatrix_unitsSMul_inv`: dividing an orthogonal basis by square roots of its
  values gives a basis with identity Gram matrix.
* `QuadraticForm.isometryEquivSumSquaresOfMulSelf_apply_basis`: the specified normalization sends
  `b i` to `c i • Pi.single i 1`.
* `QuadraticForm.equivalent_weightedSumSquares_one_iff_exists_toMatrix_eq_one`: a form is
  equivalent to the sum of squares on `ι → R` exactly when it has a basis indexed by `ι` with
  identity Gram matrix.

## References

* The coordinate isometry reuses Mathlib's `QuadraticMap.isometryEquivBasisRepr` and
  `QuadraticForm.basisRepr_eq_of_iIsOrtho`, following Mathlib's
  `QuadraticForm.isometryEquivWeightedSumSquares`, which treats bases indexed by
  `Fin (finrank K V)` over a field and lands in the weighted sum of squares; here any finite index
  type over a commutative ring is allowed and the basis is normalized first. The rescaling by
  chosen unit square roots follows Mathlib's
  `QuadraticForm.isometryEquivWeightedSumSquaresWeightedSumSquares`, carried out at the level of
  bases so that the chosen square roots remain visible.
-/

public section

open Module QuadraticMap

namespace QuadraticForm

section CommSemiring

variable {R M ι : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- Dividing a vector by a unit square root of its value normalizes that value to `1`. -/
theorem apply_inv_smul_eq_one_of_mul_self {Q : QuadraticForm R M} {x : M} {c : Rˣ}
    (hc : (c : R) * c = Q x) : Q (c⁻¹ • x) = 1 := by
  rw [Units.smul_def, QuadraticMap.map_smul, ← hc, smul_eq_mul, mul_mul_mul_comm, Units.inv_mul,
    one_mul]

/-- Dividing a basis vector by a square root of its value normalizes that value to `1`. -/
theorem apply_unitsSMul_inv_eq_one {Q : QuadraticForm R M} {b : Basis ι R M} {c : ι → Rˣ}
    (hc : ∀ i, (c i : R) * c i = Q (b i)) (i : ι) :
    Q (b.unitsSMul (fun j => (c j)⁻¹) i) = 1 := by
  rw [Basis.unitsSMul_apply]
  exact apply_inv_smul_eq_one_of_mul_self (hc i)

end CommSemiring

variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Invertible (2 : R)]
  [Fintype ι]

/-- Coordinates in a basis `b` that is orthogonal for `Q` with `Q (b i) = 1` for every `i`, as an
isometry from `Q` to the standard sum of squares. -/
noncomputable def isometryEquivSumSquaresOfIsOrthoᵢ (Q : QuadraticForm R M) (b : Basis ι R M)
    (hb : (associated Q).IsOrthoᵢ b) (hQ : ∀ i, Q (b i) = 1) :
    Q.IsometryEquiv (weightedSumSquares R (1 : ι → R)) where
  toLinearEquiv := (Q.isometryEquivBasisRepr b).toLinearEquiv
  map_app' x := by
    have hw : (fun i => Q (b i)) = 1 := funext hQ
    have h : Q.basisRepr b = weightedSumSquares R (1 : ι → R) := by
      rw [basisRepr_eq_of_iIsOrtho Q b hb, hw]
    rw [← h]
    exact (Q.isometryEquivBasisRepr b).map_app x

/-- The specified sum-of-squares normalization of an orthogonal basis `b` of `Q` together with a
chosen unit square root `c i` of each value `Q (b i)`: coordinates in the normalized basis
`(c i)⁻¹ • b i`. It sends `b i` to `c i • Pi.single i 1`; another choice of square roots gives
another isometry. -/
noncomputable def isometryEquivSumSquaresOfMulSelf (Q : QuadraticForm R M) (b : Basis ι R M)
    (hb : (associated Q).IsOrthoᵢ b) (c : ι → Rˣ) (hc : ∀ i, (c i : R) * c i = Q (b i)) :
    Q.IsometryEquiv (weightedSumSquares R (1 : ι → R)) :=
  Q.isometryEquivSumSquaresOfIsOrthoᵢ (b.unitsSMul fun i => (c i)⁻¹) (hb.unitsSMul _)
    (apply_unitsSMul_inv_eq_one hc)

section isometryEquivSumSquaresOfIsOrthoᵢ

variable {Q : QuadraticForm R M} {b : Basis ι R M} (hb : (associated Q).IsOrthoᵢ b)
  (hQ : ∀ i, Q (b i) = 1)

@[simp]
theorem toLinearEquiv_isometryEquivSumSquaresOfIsOrthoᵢ :
    (Q.isometryEquivSumSquaresOfIsOrthoᵢ b hb hQ).toLinearEquiv = b.equivFun :=
  (rfl)

@[simp]
theorem isometryEquivSumSquaresOfIsOrthoᵢ_apply (x : M) :
    Q.isometryEquivSumSquaresOfIsOrthoᵢ b hb hQ x = b.equivFun x :=
  (rfl)

@[simp]
theorem isometryEquivSumSquaresOfIsOrthoᵢ_symm_apply (w : ι → R) :
    (Q.isometryEquivSumSquaresOfIsOrthoᵢ b hb hQ).symm w = ∑ i, w i • b i :=
  b.equivFun_symm_apply w

end isometryEquivSumSquaresOfIsOrthoᵢ

/-- The specified normalization is the coordinate isometry of the normalized basis
`(c i)⁻¹ • b i`. -/
theorem isometryEquivSumSquaresOfMulSelf_def {Q : QuadraticForm R M} {b : Basis ι R M}
    (hb : (associated Q).IsOrthoᵢ b) {c : ι → Rˣ} (hc : ∀ i, (c i : R) * c i = Q (b i)) :
    Q.isometryEquivSumSquaresOfMulSelf b hb c hc =
      Q.isometryEquivSumSquaresOfIsOrthoᵢ (b.unitsSMul fun i => (c i)⁻¹)
        (hb.unitsSMul _) (apply_unitsSMul_inv_eq_one hc) :=
  (rfl)

variable [DecidableEq ι]

/-- The Gram matrix of `Q` in a basis `b` is the diagonal matrix of `w` exactly when `b` is
orthogonal for `Q` and `Q (b i) = w i` for every `i`. -/
theorem toMatrix_eq_diagonal_iff (Q : QuadraticForm R M) (b : Basis ι R M) (w : ι → R) :
    Q.toMatrix b = Matrix.diagonal w ↔ (associated Q).IsOrthoᵢ b ∧ ∀ i, Q (b i) = w i := by
  simp only [← Matrix.ext_iff, toMatrix, LinearMap.toMatrix₂_apply, Matrix.diagonal_apply,
    LinearMap.isOrthoᵢ_def]
  constructor
  · intro h
    refine ⟨fun i j hij => by simpa [hij] using h i j, fun i => ?_⟩
    simpa [associated_eq_self_apply] using h i i
  · rintro ⟨ho, hw⟩ i j
    by_cases hij : i = j
    · subst hij
      simp [associated_eq_self_apply, hw]
    · simp [hij, ho i j hij]

/-- The Gram matrix of `Q` in a basis `b` is the identity exactly when `b` is orthogonal for `Q`
and every `Q (b i)` equals `1`. -/
theorem toMatrix_eq_one_iff (Q : QuadraticForm R M) (b : Basis ι R M) :
    Q.toMatrix b = 1 ↔ (associated Q).IsOrthoᵢ b ∧ ∀ i, Q (b i) = 1 := by
  rw [← Matrix.diagonal_one, toMatrix_eq_diagonal_iff]

/-- Dividing an orthogonal basis by square roots of its values gives a basis whose Gram matrix is
the identity. -/
theorem toMatrix_unitsSMul_inv {Q : QuadraticForm R M} {b : Basis ι R M} {c : ι → Rˣ}
    (hb : (associated Q).IsOrthoᵢ b)
    (hc : ∀ i, (c i : R) * c i = Q (b i)) :
    Q.toMatrix (b.unitsSMul fun i => (c i)⁻¹) = 1 :=
  (toMatrix_eq_one_iff Q _).2 ⟨hb.unitsSMul _, apply_unitsSMul_inv_eq_one hc⟩

section isometryEquivSumSquaresOfIsOrthoᵢ

variable {Q : QuadraticForm R M} {b : Basis ι R M} (hb : (associated Q).IsOrthoᵢ b)
  (hQ : ∀ i, Q (b i) = 1)

/-- The coordinate isometry of a normalized basis sends each basis vector to the corresponding
standard coordinate vector. -/
theorem isometryEquivSumSquaresOfIsOrthoᵢ_apply_basis (i : ι) :
    Q.isometryEquivSumSquaresOfIsOrthoᵢ b hb hQ (b i) = Pi.single i 1 := by
  ext j
  simp [Basis.equivFun_self, Pi.single_apply, eq_comm]

/-- The inverse of the coordinate isometry of a normalized basis sends each standard coordinate
vector to the corresponding basis vector. -/
theorem isometryEquivSumSquaresOfIsOrthoᵢ_symm_single (i : ι) :
    (Q.isometryEquivSumSquaresOfIsOrthoᵢ b hb hQ).symm (Pi.single i 1) = b i := by
  rw [IsometryEquiv.symm_apply_eq, isometryEquivSumSquaresOfIsOrthoᵢ_apply_basis]

end isometryEquivSumSquaresOfIsOrthoᵢ

section MulSelf

variable {Q : QuadraticForm R M} {b : Basis ι R M} {c : ι → Rˣ}

/-- The specified normalization sends the `i`-th orthogonal basis vector to the chosen square root
`c i` times the `i`-th standard coordinate vector. -/
@[simp]
theorem isometryEquivSumSquaresOfMulSelf_apply_basis (hb : (associated Q).IsOrthoᵢ b)
    (hc : ∀ i, (c i : R) * c i = Q (b i)) (i : ι) :
    Q.isometryEquivSumSquaresOfMulSelf b hb c hc (b i) = (c i : R) • Pi.single i 1 := by
  have h : b i = (c i : R) • b.unitsSMul (fun j => (c j)⁻¹) i := by
    rw [Basis.unitsSMul_apply, ← Units.smul_def, smul_inv_smul]
  rw [h, map_smul, isometryEquivSumSquaresOfMulSelf_def,
    isometryEquivSumSquaresOfIsOrthoᵢ_apply_basis]

/-- The inverse of the specified normalization sends the `i`-th standard coordinate vector to the
normalized basis vector `(c i)⁻¹ • b i`. -/
@[simp]
theorem isometryEquivSumSquaresOfMulSelf_symm_single (hb : (associated Q).IsOrthoᵢ b)
    (hc : ∀ i, (c i : R) * c i = Q (b i)) (i : ι) :
    (Q.isometryEquivSumSquaresOfMulSelf b hb c hc).symm (Pi.single i 1) =
      ((c i)⁻¹ : Rˣ) • b i := by
  rw [isometryEquivSumSquaresOfMulSelf_def, isometryEquivSumSquaresOfIsOrthoᵢ_symm_single,
    Basis.unitsSMul_apply]

end MulSelf

/-- A quadratic form is equivalent to the standard sum of squares on `ι → R` exactly when it has a
basis indexed by `ι` whose Gram matrix is the identity. -/
theorem equivalent_weightedSumSquares_one_iff_exists_toMatrix_eq_one (Q : QuadraticForm R M) :
    Q.Equivalent (weightedSumSquares R (1 : ι → R)) ↔ ∃ b : Basis ι R M, Q.toMatrix b = 1 := by
  constructor
  · rintro ⟨e⟩
    refine ⟨(Pi.basisFun R ι).map e.symm.toLinearEquiv, (toMatrix_eq_one_iff Q _).2 ⟨?_, ?_⟩⟩
    · intro i j hij
      have h := isOrthoᵢ_associated_weightedSumSquares (R := R) (1 : ι → R) hij
      simp only [Function.onFun, Basis.map_apply, IsometryEquiv.coe_toLinearEquiv] at h ⊢
      rw [← h]
      simp only [associated_apply, ← map_add, IsometryEquiv.map_app]
    · intro i
      simp [weightedSumSquares_apply, Pi.single_apply]
  · rintro ⟨b, hb⟩
    obtain ⟨ho, hQ⟩ := (toMatrix_eq_one_iff Q b).1 hb
    exact ⟨Q.isometryEquivSumSquaresOfIsOrthoᵢ b ho hQ⟩

end QuadraticForm
