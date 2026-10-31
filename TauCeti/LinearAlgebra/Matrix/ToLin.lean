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
-- `FiniteDimensional` and `Module.finrank` occur in the statement, and
-- `Module.finBasisOfFinrankEq` in the body.
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Matrix realizations of endomorphisms and their action on a basis

Mathlib's `algEquivMatrix` turns `Module.End K M` into matrices indexed by the index type of a
chosen basis of `M`. This file records the form of it that is wanted when the *dimension* of `M` is
known but no particular basis is: for `Module.finrank K M = n`, an isomorphism

`Module.End K M ≃ₐ[K] Matrix (Fin n) (Fin n) K`.

In the other direction it records how a matrix unit acts on the basis it is read in, which is the
computation every matrix model of a Lie algebra performs on its root vectors.

## Main results

* `TauCeti.Algebra.endAlgEquivMatrix`: the above, read off the basis
  `Module.finBasisOfFinrankEq`.
* `TauCeti.Algebra.endAlgEquivMatrix_apply`: its evaluation as `LinearMap.toMatrix` in that basis.
* `Module.Basis.toLinAlgEquiv_single_apply_basis`: the endomorphism of a matrix unit sends a basis
  vector to a single coordinate.
* `TauCeti.matrixGeneralLinearEquiv`: matrix `GL` and the linear automorphisms of coordinate
  vectors are equivalent over a commutative semiring.
* `Module.Basis.toMatrixAlgEquiv_eq_single_of_apply_basis`: an endomorphism with one matrix-unit
  coordinate action has the corresponding single-entry matrix.
* `LinearMap.vecMul_toMatrixRight'` and `LinearMap.isIdempotentElem_toMatrixRight'_iff`: over a
  possibly noncommutative semiring, linear maps of coordinate vectors are matrices acting on row
  vectors, and idempotent endomorphisms correspond to idempotent matrices.
* `LinearMap.isIdempotentElem_toMatrixRight'_comp` and
  `LinearMap.exists_toMatrixRight'_comp_eq_fromBlocks`: a direct summand of `m → R` is presented
  by an idempotent matrix, and a split short exact sequence of such summands presents its middle
  term by the block-diagonal sum of the idempotent matrices of its outer terms.
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
  have hl' (x : m ⊕ n → R) : LinearMap.funLeft R R Sum.inl x = x ∘ Sum.inl := rfl
  have hr' (x : m ⊕ n → R) : LinearMap.funLeft R R Sum.inr x = x ∘ Sum.inr := rfl
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

end LinearMap

namespace TauCeti.Algebra

variable (K : Type*) [Field K] (M : Type*) [AddCommGroup M] [Module K M] [FiniteDimensional K M]

/-- A `K`-vector space `M` of dimension `n` has `Module.End K M ≃ₐ[K] Matrix (Fin n) (Fin n) K`,
read off a chosen `K`-basis of `M`.

This is Mathlib's `algEquivMatrix` at the basis `Module.finBasisOfFinrankEq`, named here because it
is wanted wherever a finite-dimensional endomorphism algebra has to be turned into matrices of a
known size, including the second half of the opposite isomorphism
`TauCeti.Algebra.tensorOpAlgEquivMatrix`.

The basis is a choice, and nothing downstream should depend on which one it is; there is
deliberately no lemma computing the matrix entries. -/
noncomputable def endAlgEquivMatrix {n : ℕ} (hn : Module.finrank K M = n) :
    Module.End K M ≃ₐ[K] Matrix (Fin n) (Fin n) K :=
  algEquivMatrix (Module.finBasisOfFinrankEq K M hn)

/-- The chosen-basis matrix of an endomorphism is its `LinearMap.toMatrix` in
`Module.finBasisOfFinrankEq`. This is the stable unfolding rule for `endAlgEquivMatrix`; it does
not compute the entries of the chosen basis. -/
@[simp]
theorem endAlgEquivMatrix_apply {n : ℕ} (hn : Module.finrank K M = n) (f : Module.End K M) :
    endAlgEquivMatrix K M hn f =
      LinearMap.toMatrix (Module.finBasisOfFinrankEq K M hn)
        (Module.finBasisOfFinrankEq K M hn) f :=
  by
    ext i j
    simp [endAlgEquivMatrix, algEquivMatrix, algEquivMatrix',
      LinearEquiv.conjAlgEquiv_apply, LinearMap.toMatrix_apply]

end TauCeti.Algebra
