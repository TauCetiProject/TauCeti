/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.AntidiagonalSpecialOrthogonal.UpperTriangular
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.Yoneda

/-!
# Root subgroups of `SO_l^J`

Let `J_l` be the antidiagonal matrix and `SO_l^J = {g ∈ SL_l : g J_l gᵀ = J_l}`
(`TauCeti.AntidiagonalSpecialOrthogonal`). Write `i' = l - 1 - i` (`Fin.rev i`) for the mirror
image of an index. For indices `i ≠ j` with `j ≠ i'`, neither of which is the middle index of
odd `l`, put

```text
N_ij = E_ij - E_{j' i'},    x_ij(a) = 1 + a N_ij.
```

Then `N_ij J_l` is antisymmetric, `N_ij J_l N_ijᵀ = 0` and `N_ij² = 0`, so `x_ij(a)` preserves
`J_l`, has determinant one, and `a ↦ x_ij(a)` is a homomorphism `𝔾ₐ → SO_l^J`. This file promotes
it to a morphism of affine group schemes over every commutative ring. For `i, j < l / 2`, `x_ij` is
the root subgroup of the root `ε_i - ε_j` of the diagonal torus
(`TauCeti.AntidiagonalSpecialOrthogonal.diagonalTorus`); for `i < l / 2 ≤ j` (so `j' < l / 2`) it
is that of `ε_i + ε_{j'}`, and for `j < l / 2 ≤ i` that of `-(ε_{i'} + ε_j)`. Since
`N_{j' i'} = -N_ij`, the pairs `(i, j)` and `(j', i')` give the same root subgroup with opposite
parameter, `x_{j' i'}(a) = x_ij(-a)`; this covers the pairs with `i, j ≥ l / 2`. In `1`-indexed
notation, `x_{ε_i - ε_j}(a) = I + a(E_ij - E_{l+1-j, l+1-i})`.

Each root subgroup is a closed subgroup scheme of `SO_l^J`. For `i < j` the matrix `x_ij(a)` is
upper triangular, and the root subgroup factors through the upper triangular subgroup of `SO_l^J`
as a closed subgroup scheme.

The construction follows `TauCeti.Algebra.AlgebraicGroup.Symplectic.RootSubgroup.Basic`: the
natural homomorphism on algebra-valued points determines the coordinate Hopf-algebra morphism by
full faithfulness of the functor of points. The factorization through the upper triangular
subgroup follows `TauCeti.Algebra.AlgebraicGroup.Symplectic.IsotropicFlag.RootSubgroup`.

## Main declarations

* `TauCeti.AntidiagonalSpecialOrthogonal.RootSubgroupIndex`: an index pair `(i, j)` as above.
* `TauCeti.AntidiagonalSpecialOrthogonal.rootMatrix`: the matrix `x_ij(a)`, with
  `rootMatrix_mul_formMatrix_mul_transpose` and `det_rootMatrix`.
* `TauCeti.AntidiagonalSpecialOrthogonal.rootSubgroupCoordinateMap` and
  `TauCeti.AntidiagonalSpecialOrthogonal.rootSubgroup`: the coordinate morphism and the
  group-scheme morphism `𝔾ₐ → SO_l^J`, a closed immersion, with
  `pointsMulEquiv_rootSubgroupPoints` on points.
* `TauCeti.AntidiagonalSpecialOrthogonal.UpperTriangular.rootSubgroup`: for `i < j`, the factored
  morphism `𝔾ₐ → B`, a closed immersion, with `rootSubgroup_comp_inclusion` and
  `pointsMulEquiv_rootSubgroupCoordinateMap` on points.

## References

* J. E. Humphreys, *Linear Algebraic Groups* (1975), §26.3, for the root subgroups of the
  orthogonal groups in the antidiagonal model.
-/

public section

open AlgebraicGeometry CategoryTheory Matrix WithConv

namespace TauCeti.AntidiagonalSpecialOrthogonal

universe u v w

/-! ### The matrices -/

/-- **An index pair for a root subgroup of `SO_l^J`**: two distinct indices `i ≠ j`, neither of
which is the middle index `i = l - 1 - i` of odd `l`, with `j ≠ l - 1 - i`, so that
`E_ij ≠ E_{j' i'}`. -/
structure RootSubgroupIndex (l : ℕ) where
  /-- The row index of the elementary matrix `E_ij`. -/
  i : Fin l
  /-- The column index of the elementary matrix `E_ij`. -/
  j : Fin l
  ne : i ≠ j
  i_ne_rev : i ≠ Fin.rev i
  j_ne_rev : j ≠ Fin.rev j
  j_ne_rev_i : j ≠ Fin.rev i

section Matrices

variable {A : Type w} [CommRing A] {l : ℕ}

/-- `E_ij J_l = E_{i j'}`. -/
theorem single_mul_formMatrix (i j : Fin l) :
    Matrix.single i j (1 : A) * formMatrix A l = Matrix.single i (Fin.rev j) 1 := by
  ext p q
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · simp only [single_apply, formMatrix_apply, and_true, mul_ite, mul_one, mul_zero]
    split_ifs <;> simp_all
  · intro b _ hb
    simp [hb.symm]
  · simp

/-- The nilpotent matrix `N_ij = E_ij - E_{j' i'}`. -/
def rootNilpotent (i j : Fin l) : Matrix (Fin l) (Fin l) A :=
  Matrix.single i j 1 - Matrix.single (Fin.rev j) (Fin.rev i) 1

/-- The nilpotent matrix `N_ij` is `E_ij - E_{j' i'}`. -/
theorem rootNilpotent_def (i j : Fin l) :
    rootNilpotent (A := A) i j = Matrix.single i j 1 - Matrix.single (Fin.rev j) (Fin.rev i) 1 :=
  (rfl)

/-- `N_ij J_l = E_{i j'} - E_{j' i}`. -/
theorem rootNilpotent_mul_formMatrix (i j : Fin l) :
    rootNilpotent (A := A) i j * formMatrix A l =
      Matrix.single i (Fin.rev j) 1 - Matrix.single (Fin.rev j) i 1 := by
  rw [rootNilpotent, sub_mul, single_mul_formMatrix, single_mul_formMatrix, Fin.rev_rev]

/-- `J_l N_ijᵀ = -(N_ij J_l)`: the matrix `N_ij J_l` is antisymmetric. -/
theorem formMatrix_mul_transpose_rootNilpotent (i j : Fin l) :
    formMatrix A l * (rootNilpotent (A := A) i j)ᵀ = -(rootNilpotent i j * formMatrix A l) := by
  rw [← transpose_formMatrix A l, ← transpose_mul, transpose_formMatrix,
    rootNilpotent_mul_formMatrix, transpose_sub, transpose_single, transpose_single, neg_sub]

variable (r : RootSubgroupIndex l)

/-- `N_ij J_l N_ijᵀ = 0`. -/
theorem rootNilpotent_mul_formMatrix_mul_transpose :
    rootNilpotent (A := A) r.i r.j * formMatrix A l * (rootNilpotent r.i r.j)ᵀ = 0 := by
  have hrev : Fin.rev r.j ≠ Fin.rev r.i := fun h => r.ne (Fin.rev_injective h).symm
  rw [rootNilpotent_mul_formMatrix, rootNilpotent, transpose_sub, transpose_single,
    transpose_single, sub_mul, mul_sub, mul_sub,
    single_mul_single_of_ne _ _ _ _ (Ne.symm r.j_ne_rev),
    single_mul_single_of_ne _ _ _ _ hrev,
    single_mul_single_of_ne _ _ _ _ r.ne,
    single_mul_single_of_ne _ _ _ _ r.i_ne_rev]
  simp

/-- `N_ij² = 0`. -/
theorem rootNilpotent_mul_self :
    rootNilpotent (A := A) r.i r.j * rootNilpotent r.i r.j = 0 := by
  have hrev : Fin.rev r.i ≠ Fin.rev r.j := fun h => r.ne (Fin.rev_injective h)
  rw [rootNilpotent, sub_mul, mul_sub, mul_sub,
    single_mul_single_of_ne _ _ _ _ (Ne.symm r.ne),
    single_mul_single_of_ne _ _ _ _ r.j_ne_rev,
    single_mul_single_of_ne _ _ _ _ (Ne.symm r.i_ne_rev),
    single_mul_single_of_ne _ _ _ _ hrev]
  simp

/-- **The root matrix** `x_ij(a) = 1 + a N_ij = 1 + a(E_ij - E_{j' i'})`. -/
def rootMatrix (a : A) : Matrix (Fin l) (Fin l) A :=
  1 + a • rootNilpotent r.i r.j

/-- The root matrix is `1 + a N_ij`. -/
theorem rootMatrix_def (a : A) : rootMatrix r a = 1 + a • rootNilpotent r.i r.j :=
  (rfl)

/-- `x_ij(0) = 1`. -/
@[simp]
theorem rootMatrix_zero : rootMatrix r (0 : A) = 1 := by
  rw [rootMatrix, zero_smul, add_zero]

/-- `x_ij(a + b) = x_ij(a) x_ij(b)`. -/
theorem rootMatrix_add (a b : A) : rootMatrix r (a + b) = rootMatrix r a * rootMatrix r b := by
  simp only [rootMatrix, add_mul, mul_add, one_mul, mul_one, smul_mul_smul, rootNilpotent_mul_self,
    smul_zero, add_smul]
  abel

/-- **`x_ij(a)` preserves `J_l`**: `x_ij(a) J_l x_ij(a)ᵀ = J_l`. -/
theorem rootMatrix_mul_formMatrix_mul_transpose (a : A) :
    rootMatrix r a * formMatrix A l * (rootMatrix r a)ᵀ = formMatrix A l := by
  simp [rootMatrix, add_mul, mul_add, formMatrix_mul_transpose_rootNilpotent,
    rootNilpotent_mul_formMatrix_mul_transpose]

/-- `x_ij(a)` is the product of the two commuting transvections `1 + a E_ij` and
`1 - a E_{j' i'}`. -/
theorem rootMatrix_eq_transvection_mul_transvection (a : A) :
    rootMatrix r a = transvection r.i r.j a * transvection (Fin.rev r.j) (Fin.rev r.i) (-a) := by
  simp [transvection, rootMatrix, rootNilpotent, mul_add, add_mul,
    single_mul_single_of_ne _ _ _ _ r.j_ne_rev, single_neg, sub_eq_add_neg, add_assoc]

/-- **`x_ij(a)` has determinant one.** -/
@[simp]
theorem det_rootMatrix (a : A) : (rootMatrix r a).det = 1 := by
  rw [rootMatrix_eq_transvection_mul_transvection, det_mul, det_transvection_of_ne _ _ r.ne,
    det_transvection_of_ne _ _ fun h => r.ne (Fin.rev_injective h).symm, mul_one]

/-- For `i < j`, the root matrix `x_ij(a)` is upper triangular. -/
theorem isUpperTriangular_rootMatrix (h : r.i < r.j) (a : A) :
    (rootMatrix r a).IsUpperTriangular := by
  intro p q hpq
  have h1 := blockTriangular_single (b := id) h.le (1 : A) hpq
  have h2 := blockTriangular_single (b := id) (i := Fin.rev r.j) (j := Fin.rev r.i)
    (Fin.rev_le_rev.mpr h.le) (1 : A) hpq
  simp [rootMatrix, rootNilpotent, Matrix.one_apply_ne (show p ≠ q from hpq.ne'), h1, h2]

/-- The entry of `x_ij(a)` at `(i, j)` is `a`. -/
@[simp]
theorem rootMatrix_apply_i_j (a : A) : rootMatrix r a r.i r.j = a := by
  have h : ¬(Fin.rev r.j = r.i ∧ Fin.rev r.i = r.j) := fun h =>
    r.j_ne_rev_i (by rw [← h.1, Fin.rev_rev])
  simp [rootMatrix, rootNilpotent, Matrix.one_apply_ne r.ne, h]

/-- Mapping a root matrix entrywise along a ring homomorphism gives the root matrix of the image
parameter. -/
theorem map_rootMatrix {B : Type v} [CommRing B] (f : A →+* B) (a : A) :
    (rootMatrix r a).map f = rootMatrix r (f a) := by
  ext p q
  simp [rootMatrix, rootNilpotent, Matrix.one_apply, Matrix.single_apply, apply_ite f]

end Matrices

/-! ### The homomorphism on points -/

section Points

variable {l : ℕ} (r : RootSubgroupIndex l) (A : Type w) [CommRing A]

/-- The root subgroup `a ↦ x_ij(a)` as a homomorphism into `GL_l(A)`. -/
def rootHom : Multiplicative A →* GL (Fin l) A where
  toFun a :=
    ⟨rootMatrix r a.toAdd, rootMatrix r (-a.toAdd),
      by rw [← rootMatrix_add, add_neg_cancel, rootMatrix_zero],
      by rw [← rootMatrix_add, neg_add_cancel, rootMatrix_zero]⟩
  map_one' := Units.ext (rootMatrix_zero r)
  map_mul' a b := Units.ext (rootMatrix_add r a.toAdd b.toAdd)

variable {A}

/-- The matrix of `rootHom` at `a` is the root matrix `x_ij(a)`. -/
@[simp]
theorem coe_rootHom (a : Multiplicative A) :
    (rootHom r A a : Matrix (Fin l) (Fin l) A) = rootMatrix r a.toAdd :=
  (rfl)

/-- The root subgroup lands in the points of `SO_l^J`. -/
theorem rootHom_mem_pointsSubgroup (a : Multiplicative A) :
    rootHom r A a ∈ pointsSubgroup l A :=
  (mem_pointsSubgroup_iff _).mpr
    ⟨det_rootMatrix r _, rootMatrix_mul_formMatrix_mul_transpose r _⟩

/-- **The root subgroup on points**, `a ↦ x_ij(a)`, as a homomorphism into the points of
`SO_l^J`. -/
def rootPoints : Multiplicative A →* pointsSubgroup l A :=
  (rootHom r A).codRestrict _ (rootHom_mem_pointsSubgroup r)

/-- The underlying invertible matrix of `rootPoints` at `a` is `rootHom` at `a`. -/
@[simp]
theorem coe_rootPoints (a : Multiplicative A) :
    ((rootPoints r a : pointsSubgroup l A) : GL (Fin l) A) = rootHom r A a :=
  (rfl)

/-- The root subgroup on points is natural in the value ring. -/
theorem pointsSubgroupMap_rootPoints {B : Type v} [CommRing B] (f : A →+* B)
    (a : Multiplicative A) :
    pointsSubgroupMap f (rootPoints r a) = rootPoints r (Multiplicative.ofAdd (f a.toAdd)) := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_pointsSubgroupMap, coe_rootPoints, coe_rootPoints]
  ext p q
  rw [Matrix.GeneralLinearGroup.map_apply, coe_rootHom, coe_rootHom, toAdd_ofAdd,
    ← map_rootMatrix, Matrix.map_apply]

end Points

/-! ### Hopf points and the group-scheme morphism -/

section HopfPoints

variable {R : Type u} [CommRing R] {l : ℕ} (r : RootSubgroupIndex l)
variable {A : Type w} [CommRing A] [Algebra R A]
variable {B : Type v} [CommRing B] [Algebra R B]

/-- The root subgroup on Hopf points: an `A`-point of `𝔾ₐ` goes to the `A`-point of `SO_l^J` given
by its root matrix. -/
noncomputable def rootSubgroupPoints :
    WithConv (AdditiveGroup.coordinateHopfAlgebra R →ₐ[R] A) →*
      WithConv (coordinateHopfAlgebra R l →ₐ[R] A) :=
  (pointsMulEquiv R l (A := A)).symm.toMonoidHom.comp
    ((rootPoints r).comp (AdditiveGroup.gaPointsMulEquiv (R := R) (A := A)).toMonoidHom)

/-- Under the point equivalence of `SO_l^J`, a root point is the root matrix of its additive
parameter. -/
@[simp↓]
theorem pointsMulEquiv_rootSubgroupPoints
    (q : WithConv (AdditiveGroup.coordinateHopfAlgebra R →ₐ[R] A)) :
    pointsMulEquiv R l (A := A) (rootSubgroupPoints r q) =
      rootPoints r (AdditiveGroup.gaPointsMulEquiv (R := R) (A := A) q) := by
  rw [rootSubgroupPoints, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]

/-- The root subgroup on Hopf points is natural in the value algebra. -/
theorem mapValue_rootSubgroupPoints (φ : A →ₐ[R] B)
    (q : WithConv (AdditiveGroup.coordinateHopfAlgebra R →ₐ[R] A)) :
    AlgHom.mapValue (H := coordinateHopfAlgebra R l) φ (rootSubgroupPoints r q) =
      rootSubgroupPoints r (AlgHom.mapValue (H := AdditiveGroup.coordinateHopfAlgebra R) φ q) := by
  apply (pointsMulEquiv R l (A := B)).injective
  rw [pointsMulEquiv_mapValue, pointsMulEquiv_rootSubgroupPoints,
    pointsMulEquiv_rootSubgroupPoints, pointsSubgroupMap_rootPoints]
  congr 1
  apply Multiplicative.toAdd.injective
  rw [toAdd_ofAdd, AdditiveGroup.toAdd_gaPointsMulEquiv_mapValue, AlgHom.coe_toRingHom]

/-- The natural transformation of group-valued points given by the root subgroup. -/
noncomputable def rootSubgroupPointsMap :
    HopfAlgebra.pointsFunctor (R := R) (H := AdditiveGroup.coordinateHopfAlgebra R) ⟶
      HopfAlgebra.pointsFunctor (R := R) (H := coordinateHopfAlgebra R l) where
  app A := GrpCat.ofHom (rootSubgroupPoints (A := A) r)
  naturality _ _ φ := by
    ext q
    exact (mapValue_rootSubgroupPoints r φ.hom q).symm

/-- A component of the natural root points map is the root point homomorphism. -/
@[simp]
theorem rootSubgroupPointsMap_app (A : CommAlgCat.{w} R) :
    (rootSubgroupPointsMap (R := R) r).app A = GrpCat.ofHom (rootSubgroupPoints r) :=
  (rfl)

end HopfPoints

section Scheme

variable {R : Type u} [CommRing R] {l : ℕ} (r : RootSubgroupIndex l)

/-- **The coordinate morphism `O(SO_l^J) → O(𝔾ₐ)` of the root subgroup**, recovered from its
natural action on points. -/
noncomputable def rootSubgroupCoordinateMap :
    coordinateHopfAlgebra R l ⟶ AdditiveGroup.coordinateHopfAlgebra R :=
  CommHopfAlgCat.homOfPointsMap (rootSubgroupPointsMap.{u, u} (R := R) r)

/-- Precomposition by the root coordinate morphism is the natural root map on points. -/
theorem mapPointsFunctor_rootSubgroupCoordinateMap :
    (CommHopfAlgCat.Hom.mapPointsFunctor.{u, u, u}
      (rootSubgroupCoordinateMap (R := R) r) :
      HopfAlgebra.pointsFunctor (R := R) (H := AdditiveGroup.coordinateHopfAlgebra R) ⟶
        HopfAlgebra.pointsFunctor (R := R) (H := coordinateHopfAlgebra R l)) =
      rootSubgroupPointsMap.{u, u} r :=
  CommHopfAlgCat.mapPointsFunctor_homOfPointsMap _

/-- Over any value-algebra universe, the root coordinate morphism induces the root point
homomorphism. -/
@[simp↓]
theorem mapPointsFunctor_rootSubgroupCoordinateMap_app (A : CommAlgCat.{w} R)
    (q : HopfAlgebra.points (R := R) (H := AdditiveGroup.coordinateHopfAlgebra R) A) :
    (CommHopfAlgCat.Hom.mapPointsFunctor (rootSubgroupCoordinateMap (R := R) r)).app A q =
      rootSubgroupPoints r q := by
  rw [rootSubgroupCoordinateMap, CommHopfAlgCat.mapPointsFunctor_homOfPointsMap_app,
    rootSubgroupPointsMap_app]
  -- Applying `GrpCat.ofHom (rootSubgroupPoints r)` is applying `rootSubgroupPoints r`;
  -- `GrpCat.ofHom_apply` does not fire because the source is spelled `pointsFunctor.obj`.
  refine (mapValue_rootSubgroupPoints r q.ofConv _).trans ?_
  rw [AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_id, toConv_ofConv]

/-- **The root subgroup `x_ij : 𝔾ₐ → SO_l^J`**, as a morphism of affine group schemes over the
base ring. -/
noncomputable def rootSubgroup : AdditiveGroup.groupScheme R ⟶ groupScheme R l :=
  eqToHom (AdditiveGroup.groupScheme_def R) ≫
    (hopfSpec (CommRingCat.of R)).map (rootSubgroupCoordinateMap r).op ≫
    eqToHom (groupScheme_def R l).symm

/-- The root subgroup is relative spectrum applied contravariantly to its coordinate morphism. -/
theorem rootSubgroup_def :
    rootSubgroup (R := R) r =
      eqToHom (AdditiveGroup.groupScheme_def R) ≫
        (hopfSpec (CommRingCat.of R)).map (rootSubgroupCoordinateMap r).op ≫
        eqToHom (groupScheme_def R l).symm :=
  (rfl)

/-- **The generic point of the root subgroup**: restricting functions from `GL_l` to `SO_l^J` and
then to the root subgroup sends the generic matrix to the root matrix of the coordinate of
`𝔾ₐ`. -/
theorem pointToGeneralLinear_coordinateMap_comp_rootSubgroupCoordinateMap :
    ((GeneralLinear.pointToGeneralLinear l
        (toConv (coordinateMap R l ≫ rootSubgroupCoordinateMap r).hom.toAlgHom) :
        GL (Fin l) (AdditiveGroup.coordinateHopfAlgebra R)) :
      Matrix (Fin l) (Fin l) (AdditiveGroup.coordinateHopfAlgebra R)) =
      rootMatrix r (SymmetricAlgebra.ι R R 1) := by
  let q₀ : WithConv (AdditiveGroup.coordinateHopfAlgebra R →ₐ[R]
      AdditiveGroup.coordinateHopfAlgebra R) := toConv (AlgHom.id R _)
  have happ := mapPointsFunctor_rootSubgroupCoordinateMap_app r
    (CommAlgCat.of R (AdditiveGroup.coordinateHopfAlgebra R)) q₀
  rw [CommHopfAlgCat.Hom.mapPointsFunctor_app_apply, AlgHom.id_comp] at happ
  have hpt : GeneralLinear.pointToGeneralLinear l
      (toConv (coordinateMap R l ≫ rootSubgroupCoordinateMap r).hom.toAlgHom) =
      (pointsMulEquiv R l (A := AdditiveGroup.coordinateHopfAlgebra R)
        (rootSubgroupPoints r q₀) : GL (Fin l) _) := by
    rw [← pointsMulEquiv_coe, ← happ, CommHopfAlgCat.quotientPointsHom_apply,
      ← GeneralLinear.pointsMulEquiv_apply, coordinateMap_def, CommHopfAlgCat.hom_comp,
      BialgHom.comp_toAlgHom, WithConv.ofConv_toConv]
  rw [hpt, pointsMulEquiv_rootSubgroupPoints, coe_rootPoints, coe_rootHom]
  simp [q₀]

/-- The root coordinate morphism sends the coordinate at `(a, b)` to the `(a, b)` entry of the root
matrix of the coordinate of `𝔾ₐ`. -/
@[simp↓]
theorem rootSubgroupCoordinateMap_coordinateMap_genericMatrix (a b : Fin l) :
    (rootSubgroupCoordinateMap r).hom
        ((coordinateMap R l).hom (GeneralLinear.genericMatrix R l a b)) =
      rootMatrix r (SymmetricAlgebra.ι R R 1) a b := by
  rw [← pointToGeneralLinear_coordinateMap_comp_rootSubgroupCoordinateMap,
    GeneralLinear.pointToGeneralLinear_apply, GeneralLinear.genericMatrix_apply,
    WithConv.ofConv_toConv, CommHopfAlgCat.hom_comp, BialgHom.comp_toAlgHom, AlgHom.comp_apply,
    BialgHom.coe_toAlgHom, BialgHom.coe_toAlgHom]

/-- The root coordinate morphism is surjective: the entry at `(i, j)` restricts to the coordinate
of `𝔾ₐ`. -/
theorem rootSubgroupCoordinateMap_surjective :
    Function.Surjective (rootSubgroupCoordinateMap (R := R) r).hom := by
  apply (rootSubgroupCoordinateMap (R := R) r).hom.toAlgHom.surjective_of_ι_one_mem_range
  exact ⟨_, (rootSubgroupCoordinateMap_coordinateMap_genericMatrix r r.i r.j).trans
    (rootMatrix_apply_i_j r _)⟩

/-- **The root subgroup is a closed subgroup scheme of `SO_l^J`.** -/
instance isClosedImmersion_rootSubgroup :
    IsClosedImmersion (rootSubgroup (R := R) r).hom.hom.left := by
  rw [rootSubgroup_def]
  exact (CommHopfAlgCat.isClosedImmersion_eqToHom_comp_hopfSpec_map_comp_eqToHom_iff
    (AdditiveGroup.groupScheme_def R) (groupScheme_def R l) _).mpr
    (rootSubgroupCoordinateMap_surjective r)

end Scheme

/-! ### Positive roots and the upper triangular subgroup -/

namespace UpperTriangular

variable (R : Type u) [CommRing R] {l : ℕ} (r : RootSubgroupIndex l)

/-- For `i < j`, restricting functions from `GL_l` to `SO_l^J` and then to the root subgroup kills
the defining Hopf ideal of the upper triangular subgroup of `SO_l^J`. -/
theorem definingHopfIdeal_toIdeal_le_ker_rootSubgroupCoordinateMap (h : r.i < r.j) :
    (definingHopfIdeal R l).toIdeal ≤
      RingHom.ker (AntidiagonalSpecialOrthogonal.coordinateMap R l ≫
        rootSubgroupCoordinateMap r).hom.toAlgHom.toRingHom := by
  rw [← GeneralLinear.pointToGeneralLinear_mem_hopfIdealPointsSubgroup_iff_toIdeal_le_ker,
    hopfIdealPointsSubgroup_definingHopfIdeal, mem_pointsSubgroup_iff,
    AntidiagonalSpecialOrthogonal.mem_pointsSubgroup_iff,
    pointToGeneralLinear_coordinateMap_comp_rootSubgroupCoordinateMap]
  exact ⟨⟨det_rootMatrix r _, rootMatrix_mul_formMatrix_mul_transpose r _⟩,
    isUpperTriangular_rootMatrix r h _⟩

/-- **The coordinate morphism `O(B) → O(𝔾ₐ)` of a positive root subgroup**, for `i < j`, where
`B` is the upper triangular subgroup of `SO_l^J`. -/
noncomputable def rootSubgroupCoordinateMap (h : r.i < r.j) :
    coordinateHopfAlgebra R l ⟶ AdditiveGroup.coordinateHopfAlgebra R :=
  CommHopfAlgCat.liftQuotient (definingHopfIdeal R l)
    (AntidiagonalSpecialOrthogonal.coordinateMap R l ≫
      AntidiagonalSpecialOrthogonal.rootSubgroupCoordinateMap r)
    (definingHopfIdeal_toIdeal_le_ker_rootSubgroupCoordinateMap R r h)

/-- Restricting from `SO_l^J` to the upper triangular subgroup and then to a positive root
subgroup is restriction to that root subgroup. -/
@[reassoc (attr := simp)]
theorem coordinateMap_comp_rootSubgroupCoordinateMap (h : r.i < r.j) :
    coordinateMap R l ≫ rootSubgroupCoordinateMap R r h =
      AntidiagonalSpecialOrthogonal.rootSubgroupCoordinateMap r := by
  rw [coordinateMap_def]
  exact CommHopfAlgCat.quotientMapOfLe_comp_liftQuotient_eq _ _ _ _ _
    (by rw [AntidiagonalSpecialOrthogonal.coordinateMap_def])

/-- The coordinate morphism of a positive root subgroup of the upper triangular subgroup is
surjective, since its composite with restriction from `SO_l^J` is. -/
theorem rootSubgroupCoordinateMap_surjective (h : r.i < r.j) :
    Function.Surjective (rootSubgroupCoordinateMap R r h).hom := by
  have hs := AntidiagonalSpecialOrthogonal.rootSubgroupCoordinateMap_surjective (R := R) r
  rw [← coordinateMap_comp_rootSubgroupCoordinateMap R r h, _root_.CommHopfAlgCat.hom_comp,
    BialgHom.coe_comp] at hs
  exact hs.of_comp

/-- **The positive root subgroup `x_ij : 𝔾ₐ → B`**, for `i < j`, where `B` is the upper
triangular subgroup of `SO_l^J`. -/
noncomputable def rootSubgroup (h : r.i < r.j) : AdditiveGroup.groupScheme R ⟶ groupScheme R l :=
  eqToHom (AdditiveGroup.groupScheme_def R) ≫
    (hopfSpec (CommRingCat.of R)).map (rootSubgroupCoordinateMap R r h).op

/-- A positive root subgroup is relative spectrum applied to its coordinate morphism. -/
theorem rootSubgroup_def (h : r.i < r.j) :
    rootSubgroup R r h =
      eqToHom (AdditiveGroup.groupScheme_def R) ≫
        (hopfSpec (CommRingCat.of R)).map (rootSubgroupCoordinateMap R r h).op :=
  (rfl)

/-- **A positive root subgroup of `SO_l^J` factors through the upper triangular subgroup.** -/
@[reassoc (attr := simp)]
theorem rootSubgroup_comp_inclusion (h : r.i < r.j) :
    rootSubgroup R r h ≫ inclusion R l = AntidiagonalSpecialOrthogonal.rootSubgroup r := by
  rw [rootSubgroup_def, inclusion_def, CommHopfAlgCat.quotientSpecMapOfLe_def,
    AntidiagonalSpecialOrthogonal.rootSubgroup_def, Category.assoc, ← Functor.map_comp,
    ← op_comp, ← coordinateMap_def, coordinateMap_comp_rootSubgroupCoordinateMap]
  simp only [eqToHom_refl, Category.comp_id]

/-- A positive root subgroup is a closed subgroup scheme of the upper triangular subgroup. -/
instance isClosedImmersion_rootSubgroup (h : r.i < r.j) :
    IsClosedImmersion (rootSubgroup R r h).hom.hom.left := by
  rw [rootSubgroup]
  exact (CommHopfAlgCat.isClosedImmersion_eqToHom_comp_hopfSpec_map_iff
    (AdditiveGroup.groupScheme_def R) _).mpr (rootSubgroupCoordinateMap_surjective R r h)

/-- **A positive root subgroup of the upper triangular subgroup on points**: the factored root map
gives the same root matrix `x_ij(a)` on algebra-valued points. -/
@[simp]
theorem pointsMulEquiv_rootSubgroupCoordinateMap {A : Type w} [CommRing A] [Algebra R A]
    (h : r.i < r.j)
    (f : HopfAlgebra.points (R := R) (H := AdditiveGroup.coordinateHopfAlgebra R)
      (CommAlgCat.of R A)) :
    (pointsMulEquiv R l (A := A)
        (toConv (f.ofConv.comp (rootSubgroupCoordinateMap R r h).hom)) : GL (Fin l) A) =
      rootHom r A (AdditiveGroup.gaPointsMulEquiv f) := by
  have hquot := CommHopfAlgCat.mapPointsFunctor_eq_quotientPointsHom_of_mkQuotient_comp
    (definingHopfIdeal R l) (rootSubgroupCoordinateMap R r h)
    (AntidiagonalSpecialOrthogonal.coordinateMap R l ≫
      AntidiagonalSpecialOrthogonal.rootSubgroupCoordinateMap r)
    (by rw [← coordinateMap_comp_coordinateMap, Category.assoc,
      coordinateMap_comp_rootSubgroupCoordinateMap]) (CommAlgCat.of R A) f
  have hSO := CommHopfAlgCat.mapPointsFunctor_eq_quotientPointsHom_of_mkQuotient_comp
    (AntidiagonalSpecialOrthogonal.definingHopfIdeal R l)
    (AntidiagonalSpecialOrthogonal.rootSubgroupCoordinateMap r)
    (AntidiagonalSpecialOrthogonal.coordinateMap R l ≫
      AntidiagonalSpecialOrthogonal.rootSubgroupCoordinateMap r)
    (by rw [AntidiagonalSpecialOrthogonal.coordinateMap_def]) (CommAlgCat.of R A) f
  rw [CommHopfAlgCat.Hom.mapPointsFunctor_app_apply (rootSubgroupCoordinateMap R r h)
    (CommAlgCat.of R A) f] at hquot
  rw [← pointsMulEquiv_coe, ← hquot, hSO, mapPointsFunctor_rootSubgroupCoordinateMap_app,
    AntidiagonalSpecialOrthogonal.pointsMulEquiv_coe, pointsMulEquiv_rootSubgroupPoints,
    coe_rootPoints]

end UpperTriangular

end TauCeti.AntidiagonalSpecialOrthogonal
