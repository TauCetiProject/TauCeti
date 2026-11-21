/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import TauCeti.LinearAlgebra.Basis.Semilinear
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

A chain map `f : D ⟶ C` between based complexes has the coordinate base change
`HomologicalComplex.matrixBaseChangeMap c φ e f`, whose components are the matrices of the
components of `f`, with `φ` applied to every entry
(`HomologicalComplex.toMatrix_matrixBaseChangeMap_f`); it preserves identities and composites. The
coordinate maps `Module.Basis.semilinearMap φ (c i) _ : C.X i → Kⁿ⁽ⁱ⁾`, which apply `φ` to the
coordinates in the basis `c i`, intertwine the differentials of `C` and of its base change
(`HomologicalComplex.matrixBaseChange_d_apply_semilinearMap`), and the components of `f` and of
its base change (`HomologicalComplex.matrixBaseChangeMap_f_apply_semilinearMap`). So a relation
among vectors of `C` built from its differentials, from `f` and from its basis vectors holds in the
base change as well.

When `K` is a field, the base changes along `φ` and along `ψ ∘ φ`, for a homomorphism of fields
`ψ : K →+* L`, are acyclic together (`HomologicalComplex.acyclic_matrixBaseChange_comp_iff`). Over
a field `F`, the base change along the identity of `F` is acyclic exactly when `C` is
(`HomologicalComplex.acyclic_matrixBaseChange_id_iff`).

## Main definitions

* `HomologicalComplex.matrixBaseChange c φ`: the base change of a based complex along a ring
  homomorphism into a commutative ring, in coordinates.
* `HomologicalComplex.matrixBaseChangeBasis c φ`: its standard bases.
* `HomologicalComplex.matrixBaseChangeMap c φ e f`: the coordinate base change of a chain map.

## Main results

* `HomologicalComplex.toMatrix_matrixBaseChange_d`: the matrices of the differentials of the
  coordinate base change.
* `HomologicalComplex.toMatrix_matrixBaseChangeMap_f`: the matrices of the components of the
  coordinate base change of a chain map.
* `HomologicalComplex.matrixBaseChangeMap_id`, `HomologicalComplex.matrixBaseChangeMap_comp`: the
  coordinate base change of chain maps preserves identities and composites.
* `HomologicalComplex.matrixBaseChange_d_apply_semilinearMap`,
  `HomologicalComplex.matrixBaseChangeMap_f_apply_semilinearMap`: the coordinate maps intertwine the
  differentials and the chain maps with their base changes.
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

/-- The coordinate maps `C.X i → Kⁿ⁽ⁱ⁾`, which apply `φ` to the coordinates in the basis `c i`,
intertwine the differentials of `C` and of its coordinate base change. -/
theorem matrixBaseChange_d_apply_semilinearMap (i j : ι) (x : C.X i) :
    ((C.matrixBaseChange c φ).d i j).hom
        ((c i).semilinearMap φ (C.matrixBaseChangeBasis c φ i) x) =
      (c j).semilinearMap φ (C.matrixBaseChangeBasis c φ j) ((C.d i j).hom x) :=
  Basis.semilinearMap_comp_apply_of_toMatrix_eq (toMatrix_matrixBaseChange_d C c φ i j) x

section Map

/-! ### The coordinate base change of a chain map -/

variable {C} {D : HomologicalComplex (ModuleCat A) s} {m : ι → ℕ}
  (e : ∀ i, Basis (Fin (m i)) A (D.X i))

/-- The coordinate base change of a chain map `f : D ⟶ C` between based complexes along a ring
homomorphism `φ : A →+* K`: the chain map `Kᵐ⁽ⁱ⁾ → Kⁿ⁽ⁱ⁾` whose components are the matrices of
the components of `f` in the bases `e i` and `c i`, with `φ` applied to every entry. -/
noncomputable def matrixBaseChangeMap (f : D ⟶ C) :
    D.matrixBaseChange e φ ⟶ C.matrixBaseChange c φ where
  f i := ModuleCat.ofHom (Matrix.toLin' ((LinearMap.toMatrix (e i) (c i) (f.f i).hom).map φ))
  comm' i j _ := by
    ext1
    simp only [matrixBaseChange, ModuleCat.hom_comp, ModuleCat.hom_ofHom, ← Matrix.toLin'_mul,
      ← Matrix.map_mul, ← LinearMap.toMatrix_comp]
    rw [← ModuleCat.hom_comp, ← ModuleCat.hom_comp, f.comm]

/-- The matrices of the components of the coordinate base change of a chain map, in the standard
bases, are the images under `φ` of the matrices of the components of the chain map. -/
@[simp]
theorem toMatrix_matrixBaseChangeMap_f (f : D ⟶ C) (i : ι) :
    LinearMap.toMatrix (D.matrixBaseChangeBasis e φ i) (C.matrixBaseChangeBasis c φ i)
        ((matrixBaseChangeMap c φ e f).f i).hom =
      (LinearMap.toMatrix (e i) (c i) (f.f i).hom).map φ := by
  simp only [matrixBaseChangeMap, matrixBaseChange, ModuleCat.hom_ofHom]
  -- As in `toMatrix_matrixBaseChange_d`, this is `LinearMap.toMatrix_toLin` in the standard bases,
  -- which are `Pi.basisFun` by definition; the module structures agree only after unfolding
  -- `ModuleCat.of`, so the lemma is applied with `exact`.
  exact LinearMap.toMatrix_toLin (Pi.basisFun K (Fin (m i))) (Pi.basisFun K (Fin (n i))) _

/-- The coordinate base change of the identity is the identity. -/
@[simp]
theorem matrixBaseChangeMap_id :
    matrixBaseChangeMap c φ c (𝟙 C) = 𝟙 (C.matrixBaseChange c φ) := by
  ext i : 2
  apply (LinearMap.toMatrix (C.matrixBaseChangeBasis c φ i)
    (C.matrixBaseChangeBasis c φ i)).injective
  simp

/-- The coordinate base change of a composite of chain maps is the composite of their coordinate
base changes. -/
@[reassoc]
theorem matrixBaseChangeMap_comp {E : HomologicalComplex (ModuleCat A) s} {p : ι → ℕ}
    (b : ∀ i, Basis (Fin (p i)) A (E.X i)) (h : E ⟶ D) (f : D ⟶ C) :
    matrixBaseChangeMap c φ b (h ≫ f) =
      matrixBaseChangeMap e φ b h ≫ matrixBaseChangeMap c φ e f := by
  ext i : 2
  apply (LinearMap.toMatrix (E.matrixBaseChangeBasis b φ i)
    (C.matrixBaseChangeBasis c φ i)).injective
  simp [LinearMap.toMatrix_comp _ (D.matrixBaseChangeBasis e φ i), Matrix.map_mul,
    LinearMap.toMatrix_comp _ (e i)]

/-- The coordinate maps intertwine a chain map `f : D ⟶ C` and its coordinate base change. -/
theorem matrixBaseChangeMap_f_apply_semilinearMap (f : D ⟶ C) (i : ι) (y : D.X i) :
    ((matrixBaseChangeMap c φ e f).f i).hom
        ((e i).semilinearMap φ (D.matrixBaseChangeBasis e φ i) y) =
      (c i).semilinearMap φ (C.matrixBaseChangeBasis c φ i) ((f.f i).hom y) :=
  Basis.semilinearMap_comp_apply_of_toMatrix_eq (toMatrix_matrixBaseChangeMap_f c φ e f i) y

end Map

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
