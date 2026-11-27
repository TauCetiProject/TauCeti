/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.ConstantForm.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.ConstantForm.PointsSubgroup
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Coordinate.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Basic
public import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# The special orthogonal group of the antidiagonal form

For a commutative ring `R` and `l : ℕ`, let `J_l` be the antidiagonal permutation matrix, with
`1` at the entries `(i, l - 1 - i)` and `0` elsewhere. This file constructs

```text
SO_l^J = {g ∈ SL_l : g J_l gᵀ = J_l}
```

as a closed subgroup scheme of `GL_l` over `R`: the defining Hopf ideal is the join of the
constant-form Hopf ideal of `J_l` (`TauCeti.ConstantForm.definingHopfIdeal`) and the determinant
kernel (`TauCeti.SpecialLinear.definingHopfIdeal`), exactly as `TauCeti.SpecialOrthogonal` does for
the identity form. No closure computation is repeated: the join of Hopf ideals is a Hopf ideal,
and on points it cuts out the intersection of the two point subgroups.

Since `J_l` is symmetric with `J_l² = 1`, the row convention `g J_l gᵀ = J_l` used by
`TauCeti.ConstantForm` and the column convention `gᵀ J_l g = J_l` cut out the same subgroup. Over
a field of characteristic not two, `SO_l^J` is the split special orthogonal group of the quadratic
form `x ↦ ½ xᵀ J_l x`. No smoothness is claimed here; the comparison with the special
orthogonal group of the split quadratic form over `ℤ[1/2]` is a separate step.
The diagonal torus `diag(t₁, …, tₙ, (1), tₙ⁻¹, …, t₁⁻¹)` is in
`TauCeti.Algebra.AlgebraicGroup.AntidiagonalSpecialOrthogonal.DiagonalTorus`.

## Main declarations

* `TauCeti.AntidiagonalSpecialOrthogonal.formMatrix`: the antidiagonal matrix `J_l`.
* `TauCeti.AntidiagonalSpecialOrthogonal.pointsSubgroup`: the subgroup
  `{g ∈ GL_l(A) : det g = 1, g J_l gᵀ = J_l}`, with its maps along ring homomorphisms.
* `TauCeti.AntidiagonalSpecialOrthogonal.definingHopfIdeal`,
  `TauCeti.AntidiagonalSpecialOrthogonal.coordinateHopfAlgebra`,
  `TauCeti.AntidiagonalSpecialOrthogonal.groupScheme` and
  `TauCeti.AntidiagonalSpecialOrthogonal.inclusion`: the subgroup scheme and its closed
  immersion into `GL_l`.
* `TauCeti.AntidiagonalSpecialOrthogonal.pointsMulEquiv`: its algebra-valued points are
  `pointsSubgroup l A`, naturally in `A` (`pointsMulEquiv_mapValue`).
* `TauCeti.AntidiagonalSpecialOrthogonal.coordinateHopfAlgebraBaseChangeIso`: the coordinate
  Hopf algebra commutes with base change along every `R → K`.
* `TauCeti.AntidiagonalSpecialOrthogonal.groupSchemeBaseChangeIso`: so does the group scheme,
  compatibly with the inclusions into `GL_l`
  (`map_inclusion_comp_groupSchemeBaseChangeIso_hom`).

## References

* J. S. Milne, *Algebraic Groups* (2017), 2.10, for groups preserving a constant bilinear form.
* Y. Cai, S. Friedberg, E. Kaplan, *Doubling constructions: local and global theory, with an
  application to global functoriality for non-generic cuspidal representations*, Ann. of Math.
  §1, for the split `SO_l` defined by `J_l`.
* The Stacks Project, [Tag 022W](https://stacks.math.columbia.edu/tag/022W), for the ambient
  general linear group scheme.

The construction is assembled from `TauCeti.ConstantForm` and `TauCeti.SpecialLinear` through the
Hopf-ideal join, following `TauCeti.SpecialOrthogonal`.
-/

public section

open CategoryTheory Matrix WithConv
open scoped TensorProduct

namespace TauCeti.AntidiagonalSpecialOrthogonal

universe u v w

/-! ### The antidiagonal matrix -/

section FormMatrix

variable (α : Type*) [Zero α] [One α] (l : ℕ)

/-- **The antidiagonal permutation matrix `J_l`**: the permutation matrix of `Fin.revPerm`, whose
entry at `(i, j)` is `1` when `j = l - 1 - i` and `0` otherwise. -/
def formMatrix : Matrix (Fin l) (Fin l) α :=
  (Fin.revPerm : Equiv.Perm (Fin l)).permMatrix α

variable {α l} in
/-- The entries of `J_l`. -/
@[simp]
theorem formMatrix_apply (i j : Fin l) :
    formMatrix α l i j = if j = Fin.rev i then 1 else 0 := by
  rw [formMatrix, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    Fin.revPerm_apply]
  exact if_congr (Option.mem_def.trans (Option.some_inj.trans eq_comm)) rfl rfl

variable {α l} in
/-- The entry of `J_l` at `(i, k)` vanishes when `i + k ≥ l`. -/
theorem formMatrix_apply_eq_zero {i k : Fin l} (hik : l ≤ (i : ℕ) + k) :
    formMatrix α l i k = 0 := by
  rw [formMatrix_apply, ite_eq_right]
  rintro rfl
  rw [Fin.val_rev] at hik
  omega

/-- `J_l` is symmetric. -/
@[simp]
theorem transpose_formMatrix : (formMatrix α l)ᵀ = formMatrix α l := by
  rw [formMatrix, transpose_permMatrix, Equiv.Perm.inv_def, Fin.revPerm_symm]

/-- Mapping `J_l` entrywise along a map preserving `0` and `1` gives `J_l`. -/
theorem map_formMatrix {β : Type*} [Zero β] [One β] (f : α → β) (h0 : f 0 = 0) (h1 : f 1 = 1) :
    (formMatrix α l).map f = formMatrix β l := by
  ext i j
  simp only [map_apply, formMatrix_apply]
  split_ifs <;> assumption

end FormMatrix

section FormMatrixRing

variable {T : Type*} [NonAssocSemiring T] {l : ℕ}

/-- `J_l² = 1`. -/
@[simp]
theorem formMatrix_mul_self : formMatrix T l * formMatrix T l = 1 := by
  rw [formMatrix, ← permMatrix_mul,
    show (Fin.revPerm : Equiv.Perm (Fin l)) * Fin.revPerm = 1 from Equiv.ext Fin.rev_rev,
    permMatrix_one]

/-- Right multiplication by `J_l` reverses the columns. -/
@[simp]
theorem mul_formMatrix_apply {m : Type*} (M : Matrix m (Fin l) T) (i : m) (j : Fin l) :
    (M * formMatrix T l) i j = M i (Fin.rev j) := by
  rw [formMatrix, Equiv.Perm.permMatrix, PEquiv.mul_toMatrix_toPEquiv, Fin.revPerm_symm,
    submatrix_apply, id, Fin.revPerm_apply]

/-- Left multiplication by `J_l` reverses the rows. -/
@[simp]
theorem formMatrix_mul_apply {n : Type*} (M : Matrix (Fin l) n T) (i : Fin l) (j : n) :
    (formMatrix T l * M) i j = M (Fin.rev i) j := by
  rw [formMatrix, Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul, submatrix_apply, id,
    Fin.revPerm_apply]

/-- Framing `J_l` by a diagonal matrix: `diag(d) J_l diag(d)ᵀ` has the entry `d i d (l - 1 - i)` at
`(i, l - 1 - i)` and `0` elsewhere. -/
theorem diagonal_mul_formMatrix_mul_transpose_diagonal (d : Fin l → T) (i j : Fin l) :
    (diagonal d * formMatrix T l * (diagonal d)ᵀ) i j =
      if j = Fin.rev i then d i * d (Fin.rev i) else 0 := by
  rw [diagonal_transpose, mul_diagonal, diagonal_mul, formMatrix_apply]
  split_ifs with h
  · rw [h, mul_one]
  · rw [mul_zero, zero_mul]

/-- A diagonal matrix preserves `J_l` exactly when each diagonal entry is inverse to the entry in
the mirror-image position. -/
theorem diagonal_mul_formMatrix_mul_transpose_diagonal_eq_iff (d : Fin l → T) :
    diagonal d * formMatrix T l * (diagonal d)ᵀ = formMatrix T l ↔
      ∀ i, d i * d (Fin.rev i) = 1 := by
  constructor
  · intro h i
    have hi := congrFun (congrFun h i) (Fin.rev i)
    simpa only [diagonal_mul_formMatrix_mul_transpose_diagonal, formMatrix_apply,
      ite_true] using hi
  · intro h
    ext i j
    rw [diagonal_mul_formMatrix_mul_transpose_diagonal, formMatrix_apply, h]

end FormMatrixRing

/-- The determinant of `J_l` is a unit, as `J_l² = 1`. -/
theorem isUnit_det_formMatrix {T : Type*} [CommRing T] {l : ℕ} : IsUnit (formMatrix T l).det :=
  isUnit_det_of_left_inverse formMatrix_mul_self

/-! ### The point groups -/

section PointsSubgroup

variable (l : ℕ) (A : Type w) [CommRing A]

/-- **The points of `SO_l^J` over `A`**: the invertible matrices of determinant one that preserve
`J_l` in the row convention, `g J_l gᵀ = J_l`. -/
def pointsSubgroup : Subgroup (GL (Fin l) A) :=
  (Matrix.GeneralLinearGroup.det : GL (Fin l) A →* Aˣ).ker ⊓
    ConstantForm.pointsSubgroup (formMatrix A l)

variable {l A} in
/-- Membership in the points of `SO_l^J`: determinant one and `g J_l gᵀ = J_l`. -/
@[simp]
theorem mem_pointsSubgroup_iff (g : GL (Fin l) A) :
    g ∈ pointsSubgroup l A ↔ (g : Matrix (Fin l) (Fin l) A).det = 1 ∧
      (g : Matrix (Fin l) (Fin l) A) * formMatrix A l * (g : Matrix (Fin l) (Fin l) A)ᵀ =
        formMatrix A l := by
  rw [pointsSubgroup, Subgroup.mem_inf, MonoidHom.mem_ker, ConstantForm.mem_pointsSubgroup_iff,
    Units.ext_iff, Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]

variable {l A} {B : Type v} [CommRing B]

/-- Entrywise mapping along a ring homomorphism preserves the points of `SO_l^J`. -/
theorem map_mem_pointsSubgroup (f : A →+* B) {g : GL (Fin l) A} (hg : g ∈ pointsSubgroup l A) :
    Matrix.GeneralLinearGroup.map f g ∈ pointsSubgroup l B := by
  rw [pointsSubgroup, Subgroup.mem_inf, MonoidHom.mem_ker] at hg ⊢
  obtain ⟨hg₁, hg₂⟩ := hg
  refine ⟨?_, ?_⟩
  · rw [Matrix.GeneralLinearGroup.map_det, hg₁, map_one]
  · rw [← map_formMatrix A l f f.map_zero f.map_one]
    exact ConstantForm.map_mem_pointsSubgroup f hg₂

/-- The homomorphism of point groups of `SO_l^J` induced by a ring homomorphism. -/
def pointsSubgroupMap (f : A →+* B) : pointsSubgroup l A →* pointsSubgroup l B :=
  ((Matrix.GeneralLinearGroup.map f).comp (pointsSubgroup l A).subtype).codRestrict _
    fun g => map_mem_pointsSubgroup f g.property

/-- The induced map on points of `SO_l^J` is entrywise mapping of matrices. -/
@[simp]
theorem coe_pointsSubgroupMap (f : A →+* B) (g : pointsSubgroup l A) :
    (pointsSubgroupMap f g : GL (Fin l) B) = Matrix.GeneralLinearGroup.map f (g : GL (Fin l) A) :=
  (rfl)

end PointsSubgroup

/-! ### The defining Hopf ideal and quotient -/

variable (R : Type u) [CommRing R] (l : ℕ)

/-- **The defining Hopf ideal of `SO_l^J`**: the join of the constant-form Hopf ideal of `J_l`,
generated by the entries of `X J_l Xᵀ - J_l`, and the determinant kernel. -/
noncomputable def definingHopfIdeal :
    HopfIdeal R (GeneralLinear.coordinateHopfAlgebra R l) :=
  ConstantForm.definingHopfIdeal R l (formMatrix R l) ⊔ SpecialLinear.definingHopfIdeal R l

/-- The defining Hopf ideal of `SO_l^J` is the join of the form and determinant Hopf ideals. -/
theorem definingHopfIdeal_def :
    definingHopfIdeal R l =
      ConstantForm.definingHopfIdeal R l (formMatrix R l) ⊔ SpecialLinear.definingHopfIdeal R l :=
  (rfl)

/-- The underlying ideal of the defining Hopf ideal is generated by the entries of
`X J_l Xᵀ - J_l` together with the localized generic determinant minus one. -/
@[simp]
theorem definingHopfIdeal_toIdeal :
    (definingHopfIdeal R l).toIdeal =
      Ideal.span (ConstantForm.relationSet R l (formMatrix R l)) ⊔
        Ideal.span
          {(GeneralLinear.determinantGroupLike R l :
              GeneralLinear.coordinateHopfAlgebra R l) - 1} := by
  rw [definingHopfIdeal, HopfIdeal.sup_toIdeal, ConstantForm.definingHopfIdeal_toIdeal,
    SpecialLinear.definingHopfIdeal_toIdeal]

/-- A coordinate morphism kills the defining ideal of `SO_l^J` exactly when its generic matrix
`X` satisfies `X J_l Xᵀ = J_l` and has determinant one. -/
theorem definingHopfIdeal_toIdeal_le_ker_iff {T : Type*} [CommRing T] [Algebra R T]
    (phi : GeneralLinear.coordinateHopfAlgebra R l →ₐ[R] T) :
    (definingHopfIdeal R l).toIdeal ≤ RingHom.ker (phi : _ →+* T) ↔
      (GeneralLinear.genericMatrix R l).map phi * formMatrix T l *
          ((GeneralLinear.genericMatrix R l).map phi)ᵀ = formMatrix T l ∧
        phi (GeneralLinear.determinantGroupLike R l) = 1 := by
  rw [definingHopfIdeal, HopfIdeal.sup_toIdeal, sup_le_iff,
    ConstantForm.definingHopfIdeal_toIdeal_le_ker_iff,
    map_formMatrix R l _ (map_zero _) (map_one _)]
  exact Iff.rfl.and (SpecialLinear.definingHopfIdeal_toIdeal_le_ker_iff R l (phi : _ →+* T))

/-- The coordinate Hopf algebra of `SO_l^J`. -/
noncomputable abbrev coordinateHopfAlgebra : _root_.CommHopfAlgCat.{u} R :=
  CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra R l) (definingHopfIdeal R l)

/-- The quotient coordinate morphism `O(GL_l) ⟶ O(SO_l^J)`. -/
noncomputable def coordinateMap :
    GeneralLinear.coordinateHopfAlgebra R l ⟶ coordinateHopfAlgebra R l :=
  CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra R l) (definingHopfIdeal R l)

/-- The coordinate morphism of `SO_l^J` is the quotient by its defining Hopf ideal. -/
theorem coordinateMap_def :
    coordinateMap R l =
      CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra R l)
        (definingHopfIdeal R l) := by
  rw [coordinateMap]

/-- The coordinate morphism of `SO_l^J` sends an ambient coordinate to its quotient class. -/
theorem coordinateMap_apply (h : GeneralLinear.coordinateHopfAlgebra R l) :
    (coordinateMap R l).hom h = Ideal.Quotient.mkₐ R (definingHopfIdeal R l).toIdeal h := by
  rw [coordinateMap_def]
  exact CommHopfAlgCat.mkQuotient_apply _ _ h

/-- Every entry of `X J_l Xᵀ - J_l` vanishes in the coordinate Hopf algebra of `SO_l^J`. -/
@[simp]
theorem coordinateMap_relationMatrix (i j : Fin l) :
    (coordinateMap R l).hom (ConstantForm.relationMatrix R l (formMatrix R l) i j) = 0 := by
  rw [coordinateMap_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem,
    definingHopfIdeal_toIdeal]
  exact Ideal.mem_sup_left
    (Ideal.subset_span (ConstantForm.relationMatrix_mem_relationSet R l _ i j))

/-- The generic determinant is one in the coordinate Hopf algebra of `SO_l^J`. -/
@[simp↓]
theorem coordinateMap_determinantGroupLike :
    (coordinateMap R l).hom (GeneralLinear.determinantGroupLike R l) = 1 := by
  rw [coordinateMap_apply]
  apply sub_eq_zero.mp
  rw [← map_one (Ideal.Quotient.mkₐ R (definingHopfIdeal R l).toIdeal), ← map_sub,
    Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, definingHopfIdeal_toIdeal]
  exact Ideal.mem_sup_right (Ideal.subset_span rfl)

/-- **The group scheme `SO_l^J`**, the closed subgroup scheme of `GL_l` preserving `J_l` with
determinant one. -/
noncomputable abbrev groupScheme :=
  CommHopfAlgCat.quotientSpec (GeneralLinear.coordinateHopfAlgebra R l) (definingHopfIdeal R l)

/-- `SO_l^J` is the quotient spectrum of its coordinate Hopf algebra. -/
theorem groupScheme_def :
    groupScheme R l =
      CommHopfAlgCat.quotientSpec (GeneralLinear.coordinateHopfAlgebra R l)
        (definingHopfIdeal R l) :=
  rfl

/-- The closed-subgroup inclusion of `SO_l^J` into the general linear group scheme. -/
noncomputable def inclusion : groupScheme R l ⟶ GeneralLinear.groupScheme R l :=
  GeneralLinear.hopfIdealInclusion R l (definingHopfIdeal R l)

/-- The inclusion is the generic Hopf-ideal closed immersion at the defining Hopf ideal. -/
theorem inclusion_def :
    inclusion R l = GeneralLinear.hopfIdealInclusion R l (definingHopfIdeal R l) := by
  rw [inclusion]

/-- The inclusion of `SO_l^J` into `GL_l` is a closed immersion. -/
instance isClosedImmersion_inclusion :
    AlgebraicGeometry.IsClosedImmersion (inclusion R l).hom.hom.left := by
  rw [inclusion_def]
  infer_instance

/-- The coordinate Hopf algebra of `SO_l^J`, bundled with its finite-type property. -/
noncomputable def finiteTypeCoordinateHopfAlgebra : FiniteTypeCommHopfAlgCat R :=
  FiniteTypeCommHopfAlgCat.quotient
    (⟨GeneralLinear.coordinateHopfAlgebra R l,
      inferInstanceAs (Algebra.FiniteType R (GeneralLinear.coordinateHopfAlgebra R l))⟩ :
      FiniteTypeCommHopfAlgCat R)
    (definingHopfIdeal R l)

/-- The finite-type package has the coordinate Hopf algebra of `SO_l^J` as its underlying
object. -/
@[simp]
theorem finiteTypeCoordinateHopfAlgebra_obj :
    (finiteTypeCoordinateHopfAlgebra R l).obj = coordinateHopfAlgebra R l := by
  rw [finiteTypeCoordinateHopfAlgebra]

/-! ### Algebra-valued points -/

section Points

variable {A : Type w} [CommRing A] [Algebra R A]

/-- The matrix subgroup of `GL_l(A)` cut out by the defining Hopf ideal is `pointsSubgroup l A`. -/
theorem hopfIdealPointsSubgroup_definingHopfIdeal :
    GeneralLinear.hopfIdealPointsSubgroup l (definingHopfIdeal R l) A = pointsSubgroup l A := by
  rw [definingHopfIdeal, GeneralLinear.hopfIdealPointsSubgroup_sup,
    ConstantForm.hopfIdealPointsSubgroup_definingHopfIdeal,
    SpecialLinear.hopfIdealPointsSubgroup_definingHopfIdeal,
    map_formMatrix R l _ (map_zero _) (map_one _), pointsSubgroup, inf_comm]

/-- **The points of `SO_l^J`**: the group of algebra-valued points of its coordinate Hopf algebra
is `pointsSubgroup l A`, the determinant-one matrices preserving `J_l`. -/
noncomputable def pointsMulEquiv :
    HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R l) (CommAlgCat.of R A) ≃*
      pointsSubgroup l A :=
  (GeneralLinear.hopfIdealPointsSubgroupMulEquiv l (definingHopfIdeal R l)
    (CommAlgCat.of R A)).trans
    (MulEquiv.subgroupCongr (hopfIdealPointsSubgroup_definingHopfIdeal R l))

/-- Under the `SO_l^J` and general-linear point equivalences, the quotient-point inclusion is the
inclusion of `pointsSubgroup l A` into `GL_l(A)`. -/
theorem pointsMulEquiv_coe
    (f : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R l) (CommAlgCat.of R A)) :
    GeneralLinear.pointsMulEquiv l
        (CommHopfAlgCat.quotientPointsHom
          (GeneralLinear.coordinateHopfAlgebra R l) (definingHopfIdeal R l)
          (CommAlgCat.of R A) f) =
      (pointsMulEquiv R l (A := A) f : GL (Fin l) A) := by
  rw [pointsMulEquiv, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
    GeneralLinear.coe_hopfIdealPointsSubgroupMulEquiv_apply]

/-- The ambient point attached to a point of `SO_l^J` is the general-linear point of its
matrix. -/
@[simp↓]
theorem quotientPointsHom_pointsMulEquiv_symm (g : pointsSubgroup l A) :
    CommHopfAlgCat.quotientPointsHom
        (GeneralLinear.coordinateHopfAlgebra R l) (definingHopfIdeal R l)
        (CommAlgCat.of R A) ((pointsMulEquiv R l (A := A)).symm g) =
      (GeneralLinear.pointsMulEquiv (R := R) (A := A) l).symm (g : GL (Fin l) A) := by
  apply (GeneralLinear.pointsMulEquiv (R := R) (A := A) l).injective
  rw [pointsMulEquiv_coe, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]

variable {B : Type v} [CommRing B] [Algebra R B]

/-- **The points of `SO_l^J` are natural in the value algebra**: postcomposition of Hopf points
agrees with entrywise mapping of matrices. -/
theorem pointsMulEquiv_mapValue (phi : A →ₐ[R] B)
    (f : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R l) (CommAlgCat.of R A)) :
    pointsMulEquiv R l (A := B) (AlgHom.mapValue (H := coordinateHopfAlgebra R l) phi f) =
      pointsSubgroupMap (phi : A →+* B) (pointsMulEquiv R l (A := A) f) := by
  apply Subtype.ext
  rw [coe_pointsSubgroupMap, ← pointsMulEquiv_coe, ← pointsMulEquiv_coe,
    ← CommHopfAlgCat.mapValue_quotientPointsHom, GeneralLinear.pointsMulEquiv_mapValue]

/-- Naturality of the inverse point equivalence of `SO_l^J` in the value algebra. -/
theorem mapValue_pointsMulEquiv_symm_apply (phi : A →ₐ[R] B) (g : pointsSubgroup l A) :
    AlgHom.mapValue (H := coordinateHopfAlgebra R l) phi ((pointsMulEquiv R l (A := A)).symm g) =
      (pointsMulEquiv R l (A := B)).symm (pointsSubgroupMap (phi : A →+* B) g) := by
  apply (pointsMulEquiv R l (A := B)).injective
  rw [pointsMulEquiv_mapValue, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]

end Points

/-! ### Base change -/

section BaseChange

variable (K : Type max u v) [CommRing K] [Algebra R K]

/-- The defining ideal is the span of the form relations and the determinant-one relation. -/
private theorem definingHopfIdeal_toIdeal_eq_span_union (S : Type*) [CommRing S] :
    (definingHopfIdeal S l).toIdeal =
      Ideal.span (ConstantForm.relationSet S l (formMatrix S l) ∪
        {(GeneralLinear.determinantGroupLike S l :
          GeneralLinear.coordinateHopfAlgebra S l) - 1}) := by
  rw [definingHopfIdeal_toIdeal, Ideal.span_union]

/-- The general-linear base-change isomorphism carries the base-changed defining Hopf ideal of
`SO_l^J` onto the defining Hopf ideal over the new base. -/
theorem map_baseChangeHopfIdeal_definingHopfIdeal :
    (CommHopfAlgCat.baseChangeHopfIdeal (K := K) (definingHopfIdeal R l)).map
        (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K l).hom.hom =
      definingHopfIdeal K l := by
  refine CommHopfAlgCat.map_baseChangeHopfIdeal_of_toIdeal_eq_span
    (definingHopfIdeal R l) (definingHopfIdeal K l)
    (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K l)
    (definingHopfIdeal_toIdeal_eq_span_union l R)
    (definingHopfIdeal_toIdeal_eq_span_union l K) ?_
  rw [Set.image_union, ConstantForm.image_relationSet_baseChange
    (map_formMatrix R l _ (map_zero _) (map_one _))]
  congr 1
  · have hdet :=
      GeneralLinear.coordinateHopfAlgebraBaseChangeIso_hom_determinantGroupLike R K l
    simp only [Set.image_singleton, TensorProduct.tmul_sub,
      ← Algebra.TensorProduct.one_def, map_sub, map_one]
    congr 1
    exact congrArg (fun x ↦ x - 1) hdet

/-- **Base change of `SO_l^J`**: scalar extension of its coordinate Hopf algebra along `R → K` is
canonically the coordinate Hopf algebra of `SO_l^J` over `K`. -/
noncomputable def coordinateHopfAlgebraBaseChangeIso :
    CommHopfAlgCat.baseChange (K := K) (coordinateHopfAlgebra R l) ≅
      coordinateHopfAlgebra K l :=
  CommHopfAlgCat.quotientBaseChangeIsoOfMapEq
    (definingHopfIdeal R l) (definingHopfIdeal K l)
    (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K l)
    (map_baseChangeHopfIdeal_definingHopfIdeal R l K)

/-- The base-change isomorphism of `SO_l^J` is compatible with the quotient coordinate morphisms
from the corresponding general-linear coordinate Hopf algebras. -/
@[simp]
theorem baseChangeMap_coordinateMap_comp_coordinateHopfAlgebraBaseChangeIso_hom :
    CommHopfAlgCat.baseChangeMap (K := K) (coordinateMap R l) ≫
        (coordinateHopfAlgebraBaseChangeIso R l K).hom =
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K l).hom ≫ coordinateMap K l := by
  rw [coordinateMap_def, coordinateMap_def]
  exact CommHopfAlgCat.baseChangeMap_mkQuotient_comp_quotientBaseChangeIsoOfMapEq_hom
    (definingHopfIdeal R l) (definingHopfIdeal K l)
    (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K l)
    (map_baseChangeHopfIdeal_definingHopfIdeal R l K)

/-- The inverse base-change isomorphism of `SO_l^J` is compatible with the quotient coordinate
morphisms. -/
@[reassoc]
theorem coordinateMap_comp_coordinateHopfAlgebraBaseChangeIso_inv :
    coordinateMap K l ≫ (coordinateHopfAlgebraBaseChangeIso R l K).inv =
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K l).inv ≫
        CommHopfAlgCat.baseChangeMap (K := K) (coordinateMap R l) := by
  rw [coordinateMap_def, coordinateMap_def, coordinateHopfAlgebraBaseChangeIso]
  exact CommHopfAlgCat.mkQuotient_comp_quotientBaseChangeIsoOfMapEq_inv _ _ _ _

/-- The finite-type coordinate Hopf algebra of `SO_l^J` commutes with base change. -/
noncomputable def finiteTypeCoordinateHopfAlgebraBaseChangeIso :
    FiniteTypeCommHopfAlgCat.baseChange (K := K) (finiteTypeCoordinateHopfAlgebra R l) ≅
      finiteTypeCoordinateHopfAlgebra K l :=
  FiniteTypeCommHopfAlgCat.baseChangeIsoOfObjIso
    (finiteTypeCoordinateHopfAlgebra_obj R l)
    (finiteTypeCoordinateHopfAlgebra_obj K l)
    (coordinateHopfAlgebraBaseChangeIso R l K)

end BaseChange

/-! ### Base change of the group scheme -/

section GroupSchemeBaseChange

open _root_.AlgebraicGeometry

variable (K : Type u) [CommRing K] [Algebra R K]

/-- **Base change of the group scheme `SO_l^J`**: its base change to `K` is the group scheme
`SO_l^J` over `K`, the Hopf-ideal base-change comparison of `GL_l` at the defining Hopf ideals. -/
noncomputable def groupSchemeBaseChangeIso :
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).mapGrp.obj
        (groupScheme R l) ≅ groupScheme K l :=
  GeneralLinear.hopfIdealBaseChangeIso R K l (definingHopfIdeal R l) (definingHopfIdeal K l)
    (coordinateHopfAlgebraBaseChangeIso R l K).symm

/-- The base-change isomorphism of `SO_l^J` is the Hopf-ideal base-change comparison of `GL_l`
for the inverse base-change isomorphism of coordinate Hopf algebras. -/
theorem groupSchemeBaseChangeIso_def :
    groupSchemeBaseChangeIso R l K =
      GeneralLinear.hopfIdealBaseChangeIso R K l (definingHopfIdeal R l)
        (definingHopfIdeal K l) (coordinateHopfAlgebraBaseChangeIso R l K).symm :=
  (rfl)

/-- **Base change of `SO_l^J` is compatible with the inclusions.** Along the base-change
isomorphisms, the base change of the inclusion of `SO_l^J` into `GL_l` over `R` is the inclusion
over `K`. -/
@[reassoc]
theorem map_inclusion_comp_groupSchemeBaseChangeIso_hom :
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).mapGrp.map
          (inclusion R l) ≫ (GeneralLinear.groupSchemeBaseChangeIso R K l).hom =
      (groupSchemeBaseChangeIso R l K).hom ≫ inclusion K l := by
  have he := coordinateMap_comp_coordinateHopfAlgebraBaseChangeIso_inv R l K
  rw [coordinateMap_def, coordinateMap_def] at he
  rw [inclusion_def, inclusion_def, groupSchemeBaseChangeIso_def]
  exact GeneralLinear.map_hopfIdealInclusion_comp_groupSchemeBaseChangeIso R K l _ _
    (coordinateHopfAlgebraBaseChangeIso R l K).symm he

end GroupSchemeBaseChange

end TauCeti.AntidiagonalSpecialOrthogonal
