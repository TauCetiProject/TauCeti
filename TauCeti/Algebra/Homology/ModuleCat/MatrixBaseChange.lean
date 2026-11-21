/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.LinearAlgebra.Matrix.ToLin
import TauCeti.Algebra.Homology.ModuleCat.Finrank

/-!
# The coordinate base change of a based complex

Let `C` be a homological complex of modules over a commutative ring `A`, of any shape, with an
ordered basis `c i : Basis (Fin (n i)) A (C.X i)` in each degree. For a ring homomorphism
`φ : A →+* K` into a commutative ring `K`, the *coordinate base change*
`HomologicalComplex.matrixBaseChange c φ` is the complex of free `K`-modules `Kⁿ⁽ⁱ⁾`, of the same
shape, whose differentials are the matrices of the differentials of `C` in the bases `c`, with `φ`
applied to every entry (`HomologicalComplex.toMatrix_matrixBaseChange_d`). The matrices of its
differentials are the images of those of `C` by definition, for complexes in every universe. The
shapes in use are `ℤ`-graded chain complexes and two-periodic complexes, graded by `ZMod 2`.

When `K` is a field, the base changes along `φ` and along `ψ ∘ φ`, for a homomorphism of fields
`ψ : K →+* L`, are acyclic together (`HomologicalComplex.acyclic_matrixBaseChange_comp_iff`). Over
a field `F`, the base change along the identity of `F` is acyclic exactly when `C` is
(`HomologicalComplex.acyclic_matrixBaseChange_id_iff`).

## Main definitions

* `HomologicalComplex.matrixBaseChange c φ`: the base change of a based complex along a ring
  homomorphism into a commutative ring, in coordinates.
* `HomologicalComplex.matrixBaseChangeBasis c φ`: its standard bases.

## Main results

* `HomologicalComplex.toMatrix_matrixBaseChange_d`: the matrices of the differentials of the
  coordinate base change.
* `HomologicalComplex.acyclic_matrixBaseChange_comp_iff`: acyclicity of the coordinate base change
  to a field is invariant under homomorphisms of fields.
-/

public section

open CategoryTheory Module

namespace HomologicalComplex

variable {A : Type*} [CommRing A] {ι : Type*} {s : ComplexShape ι}
  (C : HomologicalComplex (ModuleCat A) s) {n : ι → ℕ} (c : ∀ i, Basis (Fin (n i)) A (C.X i))

/-- The matrices of two consecutive differentials of a based complex multiply to zero. -/
theorem toMatrix_d_mul_toMatrix_d (i j k : ι) :
    LinearMap.toMatrix (c j) (c k) (C.d j k).hom * LinearMap.toMatrix (c i) (c j) (C.d i j).hom =
      0 := by
  simp [← LinearMap.toMatrix_comp, ← ModuleCat.hom_comp]

section CommRing

variable {K : Type*} [CommRing K] (φ : A →+* K)

/-- The base change of a based complex `C` along a ring homomorphism `φ : A →+* K`, in
coordinates: the complex of free `K`-modules `Kⁿ⁽ⁱ⁾`, of the same shape as `C`, whose
differentials are the matrices of the differentials of `C` in the bases `c i`, with `φ` applied to
every entry. -/
noncomputable def matrixBaseChange : HomologicalComplex (ModuleCat K) s where
  X i := ModuleCat.of K (Fin (n i) → K)
  d i j := ModuleCat.ofHom (Matrix.toLin'
    ((LinearMap.toMatrix (c i) (c j) (C.d i j).hom).map φ))
  shape i j hij := by
    rw [C.shape i j hij]
    ext1
    simp only [ModuleCat.hom_zero, ConcreteCategory.hom_ofHom, EmbeddingLike.map_eq_zero_iff]
    convert Matrix.map_zero _ φ.map_zero
    exact map_zero _
  d_comp_d' i j k _ _ := by
    ext1
    simp [← Matrix.toLin'_mul, ← Matrix.map_mul, toMatrix_d_mul_toMatrix_d]

/-- The module of the coordinate base change in degree `i` is `Kⁿ⁽ⁱ⁾`. -/
theorem matrixBaseChange_X (i : ι) :
    (C.matrixBaseChange c φ).X i = ModuleCat.of K (Fin (n i) → K) := by
  simp [matrixBaseChange]

/-- The standard basis of the coordinate base change `HomologicalComplex.matrixBaseChange c φ` in
degree `i`. -/
noncomputable def matrixBaseChangeBasis (i : ι) :
    Basis (Fin (n i)) K ((C.matrixBaseChange c φ).X i) :=
  Pi.basisFun K (Fin (n i))

/-- The matrices of the differentials of the coordinate base change, in the standard bases, are
the images under `φ` of the matrices of the differentials of `C`. -/
@[simp]
theorem toMatrix_matrixBaseChange_d (i j : ι) :
    LinearMap.toMatrix (C.matrixBaseChangeBasis c φ i) (C.matrixBaseChangeBasis c φ j)
        ((C.matrixBaseChange c φ).d i j).hom =
      (LinearMap.toMatrix (c i) (c j) (C.d i j).hom).map φ := by
  simp only [matrixBaseChange, ModuleCat.hom_ofHom]
  -- This is `LinearMap.toMatrix_toLin` in the standard bases, up to two definitional equalities:
  -- `matrixBaseChangeBasis c φ i` is `Pi.basisFun K (Fin (n i))` by definition, and `Matrix.toLin'`
  -- is `Matrix.toLin` in the standard bases (`Matrix.toLin_eq_toLin'`). The module structure on
  -- `(C.matrixBaseChange c φ).X i` is that of `Fin (n i) → K` only after unfolding `ModuleCat.of`,
  -- so the lemma is applied with `exact` rather than rewritten with.
  exact LinearMap.toMatrix_toLin (Pi.basisFun K (Fin (n i))) (Pi.basisFun K (Fin (n j))) _

/-- The differential of the coordinate base change from degree `i` to degree `j` is the linear map
whose matrix in the standard bases is the image under `φ` of the matrix of the differential of
`C`. -/
theorem hom_matrixBaseChange_d (i j : ι) :
    ((C.matrixBaseChange c φ).d i j).hom =
      Matrix.toLin (C.matrixBaseChangeBasis c φ i) (C.matrixBaseChangeBasis c φ j)
        ((LinearMap.toMatrix (c i) (c j) (C.d i j).hom).map φ) := by
  rw [← toMatrix_matrixBaseChange_d, Matrix.toLin_toMatrix]

end CommRing

section Field

/-! ### The coordinate base change to a field -/

variable {C c} {K L : Type*} [Field K] [Field L] (φ : A →+* K) (ψ : K →+* L)

/-- The coordinate base changes of `C` along `φ` and along `ψ ∘ φ`, for a homomorphism of fields
`ψ : K →+* L`, are acyclic together. -/
@[simp]
theorem acyclic_matrixBaseChange_comp_iff :
    (C.matrixBaseChange c (ψ.comp φ)).Acyclic ↔ (C.matrixBaseChange c φ).Acyclic :=
  acyclic_iff_of_toMatrix_eq (e := C.matrixBaseChangeBasis c _)
    (c := C.matrixBaseChangeBasis c φ) ψ fun i j _ ↦ by
      rw [toMatrix_matrixBaseChange_d, toMatrix_matrixBaseChange_d, Matrix.map_map,
        RingHom.coe_comp]

/-- The coordinate base change of a based complex `C` over a field `F` along the identity of `F`
is acyclic exactly when `C` is. -/
@[simp]
theorem acyclic_matrixBaseChange_id_iff {F : Type*} [Field F]
    {C : HomologicalComplex (ModuleCat F) s} {c : ∀ i, Basis (Fin (n i)) F (C.X i)} :
    (C.matrixBaseChange c (RingHom.id F)).Acyclic ↔ C.Acyclic :=
  acyclic_iff_of_toMatrix_eq (e := C.matrixBaseChangeBasis c _) (c := c) (RingHom.id F)
    fun i j _ ↦ toMatrix_matrixBaseChange_d C c _ i j

end Field

end HomologicalComplex
