/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `Module.End`, `Matrix` and `algEquivMatrix` occur in the statement and the body below; this is
-- also the Mathlib file that `algEquivMatrix` itself lives in.
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
-- `Module.Free`, `Module.Finite` and `Module.finrank` occur in the statement, and
-- `Module.finBasisOfFinrankEq`, which this import defines, in the body.
public import Mathlib.LinearAlgebra.Dimension.Free
-- `LinearMap.det` occurs in the statement of `TauCeti.Algebra.det_endAlgEquivMatrix`.
public import Mathlib.LinearAlgebra.Determinant

/-!
# Matrix realizations of endomorphisms and their action on a basis

Mathlib's `algEquivMatrix` turns `Module.End R M` into matrices indexed by the index type of a
chosen basis of `M`. This file records the form of it that is wanted when `M` is finite free of
known *rank* but no particular basis is: for `Module.finrank R M = n`, an isomorphism

`Module.End R M ≃ₐ[R] Matrix (Fin n) (Fin n) R`.

In the other direction it records how a matrix unit acts on the basis it is read in, which is the
computation every matrix model of a Lie algebra performs on its root vectors.

## Main results

* `TauCeti.Algebra.endAlgEquivMatrix`: the above, read off the basis
  `Module.finBasisOfFinrankEq`.
* `TauCeti.Algebra.endAlgEquivMatrix_apply`: its evaluation as `LinearMap.toMatrix` in that basis.
* `TauCeti.Algebra.det_endAlgEquivMatrix`: its matrices compute determinants of endomorphisms.
* `Module.Basis.toLinAlgEquiv_single_apply_basis`: the endomorphism of a matrix unit sends a basis
  vector to a single coordinate.
* `TauCeti.matrixGeneralLinearEquiv`: matrix `GL` and the linear automorphisms of coordinate
  vectors are equivalent over a commutative semiring.
* `Module.Basis.toMatrixAlgEquiv_eq_single_of_apply_basis`: an endomorphism with one matrix-unit
  coordinate action has the corresponding single-entry matrix.
* `LinearMap.vecMul_toMatrixRight'` and `LinearMap.isIdempotentElem_toMatrixRight'_iff`: over a
  possibly noncommutative semiring, linear maps of coordinate vectors are matrices acting on row
  vectors, and idempotent endomorphisms correspond to idempotent matrices.
* `LinearMap.of_apply_single_mulVec`: over a possibly noncommutative semiring, right-linear maps of
  coordinate vectors are matrices acting on column vectors.
* `LinearMap.isIdempotentElem_toMatrixRight'_comp` and
  `LinearMap.exists_toMatrixRight'_comp_eq_fromBlocks`: a direct summand of `m → R` is presented
  by an idempotent matrix, and a split short exact sequence of such summands presents its middle
  term by the block-diagonal sum of the idempotent matrices of its outer terms.
* `LinearMap.apply_eq_sum_apply_single_one_mul`: over a possibly noncommutative semiring, maps of
  free right modules of coordinate vectors are matrices acting on column vectors.
* `LinearMap.toMatrix_mulVec_eq_repr`: the coordinate vector of `φ (∑ j, x j • v j)` is the
  matrix of `φ` applied to `x`.
* `LinearMap.toMatrixAlgEquiv_eq_toMatrix`: `LinearMap.toMatrixAlgEquiv b f` agrees with
  `LinearMap.toMatrix b b f`.
* `LinearMap.sum_toMatrix_mulVec_smul`: the vector whose coordinates are the matrix of `φ` applied
  to `x` is `φ (∑ j, x j • v j)`.
* `LinearMap.toLin'_toMatrix_comp_equivFun` and `LinearMap.equivFun_symm_comp_toLin'_toMatrix`:
  the coordinate equivalences of two bases intertwine a linear map with its matrix.
* `LinearMap.isUnit_toMatrix_iff_bijective`, `LinearMap.isUnit_det_toMatrix_iff_bijective`,
  `Matrix.toLin_bijective_iff`, and `Matrix.toLin_bijective_iff_isUnit_det`: for bases of two
  modules indexed by the same finite type, the representing matrix (and, over a commutative ring,
  its determinant) is a unit if and only if the linear map is bijective.
* `LinearEquiv.map_toMatrix_mul_map_toMatrix_symm`: even after applying a ring homomorphism to
  their entries, the matrix of a linear equivalence is a left inverse of the matrix of its inverse;
  applying the lemma to `T.symm` gives the product in the other order.
* `Matrix.linearIndependent_row_one`: over any semiring, the rows of an identity matrix are
  linearly independent.
* `Matrix.mulVecBilin_mul` and `IsIdempotentElem.mulVecBilin`: over a possibly noncommutative
  semiring, the action of matrices on column vectors is multiplicative, so idempotent matrices act
  by idempotent endomorphisms.
* `Algebra.toLin_leftMulMatrix`: the linear map of the left multiplication matrix of `x` is left
  multiplication by `x`.
* `Algebra.leftMulMatrix_algebraMap`: the left multiplication matrix of an element of the base ring
  is the corresponding scalar matrix.
* `Module.Basis.equivFun_list_prod_smul`: the coordinates of a product of linear automorphisms
  applied to a vector are the product of their matrices applied to its coordinates.

The first is used to turn the Azumaya isomorphism of a finite-dimensional central simple algebra
into a matrix algebra in `TauCeti/Algebra/CentralSimple/Opposite.lean`.
-/

public section

namespace TauCeti

/-- The matrix general linear group is the group of linear automorphisms of coordinate vectors
over a commutative semiring. Mathlib's `Matrix.GeneralLinearGroup.toLin` requires a commutative
ring. -/
def matrixGeneralLinearEquiv {R : Type*} [CommSemiring R] {n : Type*} [Fintype n]
    [DecidableEq n] :
    Matrix.GeneralLinearGroup n R ≃* LinearMap.GeneralLinearGroup R (n → R) :=
  Units.mapEquiv Matrix.toLinAlgEquiv'.toMulEquiv

/-- A general linear matrix acts on coordinate vectors by matrix-vector multiplication. -/
@[simp]
theorem matrixGeneralLinearEquiv_apply {R : Type*} [CommSemiring R] {n : Type*}
    [Fintype n] [DecidableEq n] (A : Matrix.GeneralLinearGroup n R) (v : n → R) :
    (LinearMap.GeneralLinearGroup.generalLinearEquiv R (n → R)
      (matrixGeneralLinearEquiv A)) v = Matrix.mulVec (A : Matrix n n R) v := by
  rw [LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv,
    matrixGeneralLinearEquiv, Units.coe_mapEquiv]
  exact Matrix.toLinAlgEquiv'_apply _ _

end TauCeti

namespace Module.Basis

/-- **A matrix unit acts on a basis by a single coordinate.** The endomorphism attached to
`Matrix.single p q v` sends the basis vector indexed by the column `q` to `v • bas p`, and every
other basis vector to `0`. -/
theorem toLinAlgEquiv_single_apply_basis {R : Type*} [CommSemiring R] {M : Type*}
    [AddCommMonoid M] [Module R M] {n : Type*} [Fintype n] [DecidableEq n]
    (bas : Module.Basis n R M) (p q : n) (v : R) (c : n) :
    Matrix.toLinAlgEquiv bas (Matrix.single p q v) (bas c) =
      (if q = c then v else 0) • bas p := by
  rw [Matrix.toLinAlgEquiv_self]
  simp [Matrix.single_apply, ite_and, ite_smul]

/-- **An endomorphism with a matrix-unit action has a single-entry matrix.** If an endomorphism
sends the basis vector indexed by `q` to `v • bas p` and every other basis vector to zero, its
matrix in `bas` is `Matrix.single p q v`. -/
theorem toMatrixAlgEquiv_eq_single_of_apply_basis {R : Type*} [CommSemiring R] {M : Type*}
    [AddCommMonoid M] [Module R M] {n : Type*} [Fintype n] [DecidableEq n]
    (bas : Module.Basis n R M) (f : Module.End R M) (p q : n) (v : R)
    (h : ∀ c, f (bas c) = (if q = c then v else 0) • bas p) :
    LinearMap.toMatrixAlgEquiv bas f = Matrix.single p q v := by
  apply (Matrix.toLinAlgEquiv bas).injective
  rw [Matrix.toLinAlgEquiv_toMatrixAlgEquiv]
  apply bas.ext
  intro c
  rw [toLinAlgEquiv_single_apply_basis]
  exact h c

open Matrix in
/-- **Coordinates of a product of linear automorphisms.** In a basis `b`, the coordinates of
`(∏ G a) • x` are the ordered product of the matrices of the `G a` applied to the coordinates of
`x`. -/
theorem equivFun_list_prod_smul {R : Type*} [CommSemiring R] {M : Type*} [AddCommMonoid M]
    [Module R M] {n α : Type*} [Fintype n] [DecidableEq n] (b : Module.Basis n R M) (l : List α)
    (G : α → LinearMap.GeneralLinearGroup R M) (x : M) :
    b.equivFun ((l.map G).prod • x) =
      (l.map fun a ↦ LinearMap.toMatrixAlgEquiv b (G a : Module.End R M)).prod *ᵥ
        b.equivFun x := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, mul_smul, List.map_cons, List.prod_cons,
      ← mulVec_mulVec, ← ih, Units.smul_def, Module.End.smul_def]
    exact (LinearMap.toMatrix_mulVec_repr b b _ _).symm

end Module.Basis

namespace LinearMap

variable {R : Type*} [Semiring R] {m n : Type*} [Fintype m] [DecidableEq m]

/-- Multiplying a row vector by the matrix `f.toMatrixRight'` applies the linear map `f`. -/
@[simp]
theorem vecMul_toMatrixRight' (f : (m → R) →ₗ[R] n → R) (v : m → R) :
    Matrix.vecMul v f.toMatrixRight' = f v := by
  rw [← Matrix.toLinearMapRight'_apply, LinearEquiv.symm_apply_apply]

/-- **A right-linear map of coordinate vectors is a matrix acting on column vectors.** Over a
possibly noncommutative semiring, an `Rᵐᵒᵖ`-linear map `f : (m → R) → (n → R)` (one commuting with
right scalar multiplication) is `Matrix.mulVec` by the matrix whose `j`-th column is the image
`f eⱼ` of the `j`-th standard basis vector. -/
@[simp]
theorem of_apply_single_mulVec (f : (m → R) →ₗ[Rᵐᵒᵖ] n → R) (v : m → R) :
    Matrix.mulVec (Matrix.of fun i j ↦ f (Pi.single j 1) i) v = f v := by
  -- Both sides are `Rᵐᵒᵖ`-linear in `v`, and they agree on the `eⱼ`.
  have h : Matrix.mulVecBilin R Rᵐᵒᵖ (Matrix.of fun i j ↦ f (Pi.single j 1) i) = f :=
    LinearMap.pi_ext' fun j ↦ LinearMap.ext_ring_op <| by
      ext i
      simp
  exact LinearMap.congr_fun h v

/-- The matrix of an endomorphism of `m → R`, acting on row vectors, is idempotent exactly when
the endomorphism is. -/
theorem isIdempotentElem_toMatrixRight'_iff (f : Module.End R (m → R)) :
    IsIdempotentElem f.toMatrixRight' ↔ IsIdempotentElem f := by
  rw [IsIdempotentElem, IsIdempotentElem, ← toMatrixRight'_comp, Module.End.mul_eq_comp]
  exact toMatrixRight'.injective.eq_iff

/-- A direct summand `s ∘ i = id` of `m → R` is the image of the idempotent matrix of `i ∘ s`,
acting on row vectors. -/
theorem isIdempotentElem_toMatrixRight'_comp {P : Type*} [AddCommMonoid P] [Module R P]
    {s : (m → R) →ₗ[R] P} {i : P →ₗ[R] m → R} (h : s ∘ₗ i = LinearMap.id) :
    IsIdempotentElem (i ∘ₗ s).toMatrixRight' :=
  (isIdempotentElem_toMatrixRight'_iff _).2 <|
    LinearMap.ext fun x ↦ congrArg i (LinearMap.congr_fun h (s x))

/-- A split short exact sequence `X₁ → X₂ → X₃` whose outer terms are direct summands of `m → R`
and `n → R` presents its middle term as a direct summand of `m ⊕ n → R`, whose idempotent matrix
is the block-diagonal sum of the idempotent matrices of the outer terms. -/
theorem exists_toMatrixRight'_comp_eq_fromBlocks [Fintype n] [DecidableEq n]
    {X₁ X₂ X₃ : Type*} [AddCommMonoid X₁] [Module R X₁] [AddCommMonoid X₂] [Module R X₂]
    [AddCommMonoid X₃] [Module R X₃]
    {f : X₁ →ₗ[R] X₂} {g : X₂ →ₗ[R] X₃} {r : X₂ →ₗ[R] X₁} {σ : X₃ →ₗ[R] X₂}
    (hfr : r ∘ₗ f = LinearMap.id) (hσg : g ∘ₗ σ = LinearMap.id)
    (hid : f ∘ₗ r + σ ∘ₗ g = LinearMap.id) (hfg : g ∘ₗ f = 0) (hσr : r ∘ₗ σ = 0)
    {s₁ : (m → R) →ₗ[R] X₁} {i₁ : X₁ →ₗ[R] m → R} (h₁ : s₁ ∘ₗ i₁ = LinearMap.id)
    {s₃ : (n → R) →ₗ[R] X₃} {i₃ : X₃ →ₗ[R] n → R} (h₃ : s₃ ∘ₗ i₃ = LinearMap.id) :
    ∃ (s₂ : (m ⊕ n → R) →ₗ[R] X₂) (i₂ : X₂ →ₗ[R] m ⊕ n → R), s₂ ∘ₗ i₂ = LinearMap.id ∧
      (i₂ ∘ₗ s₂).toMatrixRight' =
        Matrix.fromBlocks (i₁ ∘ₗ s₁).toMatrixRight' 0 0 (i₃ ∘ₗ s₃).toMatrixRight' := by
  have hrf (x : X₁) : r (f x) = x := LinearMap.congr_fun hfr x
  have hgσ (x : X₃) : g (σ x) = x := LinearMap.congr_fun hσg x
  have hgf (x : X₁) : g (f x) = 0 := LinearMap.congr_fun hfg x
  have hrσ (x : X₃) : r (σ x) = 0 := LinearMap.congr_fun hσr x
  have hs₁ (x : X₁) : s₁ (i₁ x) = x := LinearMap.congr_fun h₁ x
  have hs₃ (x : X₃) : s₃ (i₃ x) = x := LinearMap.congr_fun h₃ x
  let e := LinearEquiv.sumArrowLequivProdArrow m n R R
  have hl (u : m → R) (v : n → R) : LinearMap.funLeft R R Sum.inl (e.symm (u, v)) = u :=
    funext fun _ ↦ by simp [e, LinearMap.funLeft_apply]
  have hr (u : m → R) (v : n → R) : LinearMap.funLeft R R Sum.inr (e.symm (u, v)) = v :=
    funext fun _ ↦ by simp [e, LinearMap.funLeft_apply]
  have hl' (x : m ⊕ n → R) : LinearMap.funLeft R R Sum.inl x = x ∘ Sum.inl := (rfl)
  have hr' (x : m ⊕ n → R) : LinearMap.funLeft R R Sum.inr x = x ∘ Sum.inr := (rfl)
  refine ⟨f ∘ₗ s₁ ∘ₗ LinearMap.funLeft R R Sum.inl + σ ∘ₗ s₃ ∘ₗ LinearMap.funLeft R R Sum.inr,
    e.symm.toLinearMap ∘ₗ (i₁ ∘ₗ r).prod (i₃ ∘ₗ g), ?_, ?_⟩
  · refine LinearMap.ext fun x ↦ ?_
    have hx := LinearMap.congr_fun hid x
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply] at hx
    simpa [hl, hr, hs₁, hs₃] using hx
  · apply Matrix.toLinearMapRight'.injective
    refine LinearMap.ext fun x ↦ funext fun q ↦ ?_
    rcases q with b | d <;>
      simp [e, Matrix.vecMul_fromBlocks, hl', hr', hrf, hgσ, hgf, hrσ]

/-- A linear map of coordinate vectors over `Rᵐᵒᵖ`, that is, a map of free right `R`-modules,
is left multiplication of column vectors by the matrix with entries `f (Pi.single j 1) i`. -/
theorem apply_eq_sum_apply_single_one_mul (f : (m → R) →ₗ[Rᵐᵒᵖ] n → R) (x : m → R) (i : n) :
    f x i = ∑ j, f (Pi.single j 1) i * x j := by
  have hx : x = ∑ j, MulOpposite.op (x j) • (Pi.single j 1 : m → R) := by
    ext l
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hx]
  simp [map_sum, Finset.sum_apply]

end LinearMap

namespace LinearMap

open Matrix

/-- **Coordinates through the coefficient matrix.** The coordinate vector of
`φ (∑ j, x j • v j)` in the basis `b` is the coefficient matrix `LinearMap.toMatrix v b φ` applied
to `x`. -/
theorem toMatrix_mulVec_eq_repr {R V M ι κ : Type*} [CommSemiring R] [AddCommMonoid V]
    [Module R V] [AddCommMonoid M] [Module R M] [Fintype κ] [DecidableEq κ] [Finite ι]
    (v : Module.Basis κ R V) (b : Module.Basis ι R M) (φ : V →ₗ[R] M) (x : κ → R) :
    toMatrix v b φ *ᵥ x = b.repr (φ (∑ j, x j • v j)) := by
  rw [← v.equivFun_symm_apply, ← toMatrix_mulVec_repr v b, ← v.equivFun_apply,
    LinearEquiv.apply_symm_apply]

/-- `LinearMap.toMatrixAlgEquiv b f` agrees with `LinearMap.toMatrix b b f`. -/
theorem toMatrixAlgEquiv_eq_toMatrix {R V ι : Type*} [CommSemiring R] [AddCommMonoid V]
    [Module R V] [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R V) (f : Module.End R V) :
    toMatrixAlgEquiv b f = toMatrix b b f := by
  ext i j
  rw [toMatrixAlgEquiv_apply, toMatrix_apply]

/-- **Vectors through the coefficient matrix.** The vector whose coordinates in the basis `b` are
the coefficient matrix `LinearMap.toMatrix v b φ` applied to `x` is `φ (∑ j, x j • v j)`. -/
theorem sum_toMatrix_mulVec_smul {R V M ι κ : Type*} [CommSemiring R] [AddCommMonoid V]
    [Module R V] [AddCommMonoid M] [Module R M] [Fintype κ] [DecidableEq κ] [Fintype ι]
    (v : Module.Basis κ R V) (b : Module.Basis ι R M) (φ : V →ₗ[R] M) (x : κ → R) :
    ∑ c, (toMatrix v b φ *ᵥ x) c • b c = φ (∑ j, x j • v j) := by
  rw [toMatrix_mulVec_eq_repr, b.sum_repr]

/-- In the coordinates of bases `v` and `b`, a linear map `φ` acts by its matrix
`LinearMap.toMatrix v b φ`. -/
theorem toLin'_toMatrix_comp_equivFun {R V M ι κ : Type*} [CommSemiring R] [AddCommMonoid V]
    [Module R V] [AddCommMonoid M] [Module R M] [Fintype κ] [DecidableEq κ] [Finite ι]
    (v : Module.Basis κ R V) (b : Module.Basis ι R M) (φ : V →ₗ[R] M) :
    toLin' (toMatrix v b φ) ∘ₗ v.equivFun.toLinearMap = b.equivFun.toLinearMap ∘ₗ φ := by
  refine LinearMap.ext fun x ↦ ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
    toLin'_apply, v.equivFun_apply, b.equivFun_apply, toMatrix_mulVec_repr]

/-- The inverse coordinate equivalences of bases `v` and `b` turn the matrix
`LinearMap.toMatrix v b φ` back into the linear map `φ`. -/
theorem equivFun_symm_comp_toLin'_toMatrix {R V M ι κ : Type*} [CommSemiring R]
    [AddCommMonoid V] [Module R V] [AddCommMonoid M] [Module R M] [Fintype κ] [DecidableEq κ]
    [Finite ι] (v : Module.Basis κ R V) (b : Module.Basis ι R M) (φ : V →ₗ[R] M) :
    b.equivFun.symm.toLinearMap ∘ₗ toLin' (toMatrix v b φ) =
      φ ∘ₗ v.equivFun.symm.toLinearMap := by
  refine LinearMap.ext fun x ↦ b.equivFun.injective ?_
  have h := LinearMap.congr_fun (toLin'_toMatrix_comp_equivFun v b φ) (v.equivFun.symm x)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h ⊢
  exact h

/-- **Invertibility of a representing matrix.** For bases `v` and `b` indexed by the same finite
type, `LinearMap.toMatrix v b φ` is a unit matrix if and only if `φ` is bijective. This extends
`LinearMap.isUnit_toMatrix_iff` from endomorphisms in a single basis to linear maps between two
modules. -/
theorem isUnit_toMatrix_iff_bijective {R V M ι : Type*} [CommSemiring R] [AddCommMonoid V]
    [Module R V] [AddCommMonoid M] [Module R M] [Fintype ι] [DecidableEq ι]
    (v : Module.Basis ι R V) (b : Module.Basis ι R M) (φ : V →ₗ[R] M) :
    IsUnit (toMatrix v b φ) ↔ Function.Bijective φ := by
  have h : toMatrix v b φ =
      toMatrix' (b.equivFun.toLinearMap ∘ₗ φ ∘ₗ v.equivFun.symm.toLinearMap) := by
    ext i j
    simp [toMatrix_apply, toMatrix'_apply]
  rw [h, isUnit_toMatrix'_iff, Module.End.isUnit_iff, LinearMap.coe_comp, LinearMap.coe_comp,
    LinearEquiv.coe_coe, LinearEquiv.coe_coe, EquivLike.comp_bijective _ b.equivFun,
    EquivLike.bijective_comp v.equivFun.symm]

/-- **Invertible-determinant criterion for bijectivity.** Over a commutative ring, for bases `v`
and `b` indexed by the same finite type, `(LinearMap.toMatrix v b φ).det` is a unit if and only if
`φ` is bijective. -/
theorem isUnit_det_toMatrix_iff_bijective {R V M ι : Type*} [CommRing R] [AddCommMonoid V]
    [Module R V] [AddCommMonoid M] [Module R M] [Fintype ι] [DecidableEq ι]
    (v : Module.Basis ι R V) (b : Module.Basis ι R M) (φ : V →ₗ[R] M) :
    IsUnit (toMatrix v b φ).det ↔ Function.Bijective φ := by
  rw [← Matrix.isUnit_iff_isUnit_det, isUnit_toMatrix_iff_bijective]

end LinearMap

namespace LinearEquiv

/-- **Matrices of a linear equivalence and its inverse.** For bases `v` and `b`, the image under a
ring homomorphism `f` of the matrix `LinearMap.toMatrix v b T` of a linear equivalence `T` is a
left inverse of the image of the matrix `LinearMap.toMatrix b v T.symm` of its inverse. -/
theorem map_toMatrix_mul_map_toMatrix_symm {R S V M ι κ : Type*} [CommSemiring R] [Semiring S]
    [AddCommMonoid V] [Module R V] [AddCommMonoid M] [Module R M] [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (v : Module.Basis ι R V) (b : Module.Basis κ R M) (T : V ≃ₗ[R] M)
    (f : R →+* S) :
    (LinearMap.toMatrix v b T.toLinearMap).map f *
      (LinearMap.toMatrix b v T.symm.toLinearMap).map f = 1 := by
  rw [← Matrix.map_mul, ← LinearMap.toMatrix_comp, comp_symm, LinearMap.toMatrix_id,
    Matrix.map_one _ (map_zero f) (map_one f)]

end LinearEquiv

namespace Matrix

/-- The rows of an identity matrix are linearly independent: they are the standard basis
vectors `Pi.single i 1`. -/
theorem linearIndependent_row_one {R m : Type*} [Semiring R] [DecidableEq m] :
    LinearIndependent R (1 : Matrix m m R).row := by
  convert Pi.linearIndependent_single_one m R using 1
  ext i j
  exact one_eq_pi_single

/-- For bases `v` and `b` indexed by the same finite type, `Matrix.toLin v b A` is bijective if and
only if `A` is a unit matrix. -/
theorem toLin_bijective_iff {R V M ι : Type*} [CommSemiring R] [AddCommMonoid V]
    [Module R V] [AddCommMonoid M] [Module R M] [Fintype ι] [DecidableEq ι]
    (v : Module.Basis ι R V) (b : Module.Basis ι R M) (A : Matrix ι ι R) :
    Function.Bijective (Matrix.toLin v b A) ↔ IsUnit A := by
  rw [← LinearMap.isUnit_toMatrix_iff_bijective v b, LinearMap.toMatrix_toLin]

/-- Over a commutative ring, for bases `v` and `b` indexed by the same finite type,
`Matrix.toLin v b A` is bijective if and only if `A.det` is a unit. -/
theorem toLin_bijective_iff_isUnit_det {R V M ι : Type*} [CommRing R] [AddCommMonoid V]
    [Module R V] [AddCommMonoid M] [Module R M] [Fintype ι] [DecidableEq ι]
    (v : Module.Basis ι R V) (b : Module.Basis ι R M) (A : Matrix ι ι R) :
    Function.Bijective (Matrix.toLin v b A) ↔ IsUnit A.det := by
  rw [toLin_bijective_iff, isUnit_iff_isUnit_det]

section Bilinear

variable {R S A l m n : Type*} [Semiring R] [Semiring S] [NonUnitalSemiring A] [Module R A]
  [Module S A] [SMulCommClass S R A] [SMulCommClass S A A] [IsScalarTower R A A]

/-- `Matrix.mulVecBilin` is multiplicative: over a possibly noncommutative semiring, the action
on column vectors of a product of matrices is the composite of their actions. -/
@[simp]
theorem mulVecBilin_mul [Fintype m] [Fintype n] (M : Matrix l m A) (N : Matrix m n A) :
    mulVecBilin R S (M * N) = mulVecBilin R S M ∘ₗ mulVecBilin R S N :=
  LinearMap.ext fun _ ↦ (mulVec_mulVec _ _ _).symm

end Bilinear

end Matrix

/-- Left multiplication of column vectors by an idempotent matrix is an idempotent endomorphism. -/
theorem IsIdempotentElem.mulVecBilin {A n : Type*} (R S : Type*) [Semiring R] [Semiring S]
    [NonUnitalSemiring A] [Module R A] [Module S A] [SMulCommClass S R A] [SMulCommClass S A A]
    [IsScalarTower R A A] [Fintype n] {e : Matrix n n A} (he : IsIdempotentElem e) :
    IsIdempotentElem (Matrix.mulVecBilin R S e) := by
  rw [IsIdempotentElem, Module.End.mul_eq_comp, ← Matrix.mulVecBilin_mul, he.eq]

namespace Algebra

/-- The linear map of the left multiplication matrix of `x` in a basis `b` is left multiplication
by `x`. -/
@[simp]
theorem toLin_leftMulMatrix {R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S]
    {m : Type*} [Fintype m] [DecidableEq m] (b : Module.Basis m R S) (x : S) :
    Matrix.toLin b b (leftMulMatrix b x) = LinearMap.mulLeft R x := by
  rw [← toMatrix_lmul_eq, Matrix.toLin_toMatrix]

-- Not a `simp` lemma: `simp` rewrites the left-hand side through `AlgHom.commutes` first, into
-- `algebraMap R (Matrix ι ι R) r`, so this lemma would never fire.
/-- Left multiplication by an element of the base ring is the corresponding scalar matrix. -/
theorem leftMulMatrix_algebraMap {R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R S) (r : R) :
    leftMulMatrix b (algebraMap R S r) = Matrix.scalar ι r := by
  simp [Matrix.algebraMap_eq_diagonal, Matrix.scalar_apply]

/-- The matrix of multiplication by `ψ x` in the image of a basis is the image of the matrix of
multiplication by `x`. -/
lemma leftMulMatrix_map {R B R' B' : Type*} [CommSemiring R] [Semiring B]
    [Algebra R B] [CommSemiring R'] [Semiring B'] [Algebra R' B']
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι R B)
    (b' : Module.Basis ι R' B') (σ : R →+* R') (ψ : B →+* B')
    (hψ : ∀ r, ψ (algebraMap R B r) = algebraMap R' B' (σ r))
    (hb : ∀ i, b' i = ψ (b i))
    (x : B) : leftMulMatrix b' (ψ x) = (leftMulMatrix b x).map σ := by
  have hrepr (y : B) : b'.repr (ψ y) = Finsupp.mapRange σ σ.map_zero (b.repr y) := by
    conv_lhs => rw [← b.sum_repr y]
    rw [map_sum]
    simp_rw [Algebra.smul_def, map_mul, hψ, ← hb, ← Algebra.smul_def]
    ext i
    rw [b'.repr_sum_self, Finsupp.mapRange_apply]
  ext i j
  rw [Matrix.map_apply, leftMulMatrix_eq_repr_mul, leftMulMatrix_eq_repr_mul, hb, ← map_mul,
    hrepr, Finsupp.mapRange_apply]


end Algebra

namespace TauCeti.Algebra

section CommSemiring

variable (R : Type*) [CommSemiring R] [StrongRankCondition R] (M : Type*) [AddCommMonoid M]
  [Module R M] [Module.Free R M] [Module.Finite R M]

/-- A finite free `R`-module `M` of rank `n` has `Module.End R M ≃ₐ[R] Matrix (Fin n) (Fin n) R`,
read off a chosen `R`-basis of `M`.

This is Mathlib's `algEquivMatrix` at the basis `Module.finBasisOfFinrankEq`, named here because it
is wanted wherever the endomorphism algebra of a finite free module has to be turned into
matrices of a known size, including the second half of the opposite isomorphism
`TauCeti.Algebra.tensorOpAlgEquivMatrix`.

The basis is a choice: beyond `endAlgEquivMatrix_apply`, which reads the matrix in
`Module.finBasisOfFinrankEq`, this file proves nothing about which basis that is. -/
noncomputable def endAlgEquivMatrix {n : ℕ} (hn : Module.finrank R M = n) :
    Module.End R M ≃ₐ[R] Matrix (Fin n) (Fin n) R :=
  algEquivMatrix (Module.finBasisOfFinrankEq R M hn)

/-- The chosen-basis matrix of an endomorphism is its `LinearMap.toMatrix` in
`Module.finBasisOfFinrankEq`. This is the stable unfolding rule for `endAlgEquivMatrix`; it does
not compute the entries of the chosen basis. -/
@[simp]
theorem endAlgEquivMatrix_apply {n : ℕ} (hn : Module.finrank R M = n) (f : Module.End R M) :
    endAlgEquivMatrix R M hn f =
      LinearMap.toMatrix (Module.finBasisOfFinrankEq R M hn)
        (Module.finBasisOfFinrankEq R M hn) f := by
  ext i j
  simp [endAlgEquivMatrix, algEquivMatrix, algEquivMatrix',
    LinearEquiv.conjAlgEquiv_apply, LinearMap.toMatrix_apply]

end CommSemiring

section CommRing

-- `LinearMap.det` needs a commutative ring and an additive group.
variable (R : Type*) [CommRing R] [StrongRankCondition R] (M : Type*) [AddCommGroup M]
  [Module R M] [Module.Free R M] [Module.Finite R M]

/-- The chosen-basis matrix of an endomorphism has the determinant of the endomorphism. Since
`endAlgEquivMatrix` is an algebra isomorphism, this computes the determinant of every polynomial
expression in `f`, such as `det (1 - f ^ n)`, as that of the same expression in its matrix. -/
theorem det_endAlgEquivMatrix {n : ℕ} (hn : Module.finrank R M = n) (f : Module.End R M) :
    (endAlgEquivMatrix R M hn f).det = LinearMap.det f := by
  rw [endAlgEquivMatrix_apply, LinearMap.det_toMatrix]

end CommRing

end TauCeti.Algebra
