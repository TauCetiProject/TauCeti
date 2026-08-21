/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.FunctorOfPoints
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Scheme
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Naturality
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Scheme.Basic

/-!
# The subgroup scheme of `GLₙ` preserving a constant matrix

For a commutative ring `R`, a natural number `n`, and a **constant** matrix
`C : Matrix (Fin n) (Fin n) R`, the entries of the matrix relation

```text
X C Xᵀ - C
```

— `X` the localized generic matrix of `GL n`, `C` read in the coordinate Hopf algebra through
the structure morphism — generate a Hopf ideal in the coordinate Hopf algebra of `GL n`. Its
quotient represents the closed subgroup scheme of `GL n` preserving `C`. On every commutative
`R`-algebra `A`, its points are the invertible matrices `M` with `M C Mᵀ = C`.

Nothing is assumed of `C`: it is an arbitrary square matrix over the base, not required to be
invertible, symmetric, alternating, or nondegenerate, and the construction includes `n = 0` and
the zero ring. The classical families are the specializations at a constant form:
`TauCeti.Orthogonal` takes `C = 1` and `TauCeti.Symplectic` takes `C = Jₘ`, each adding its own
identification of the points with the corresponding matrix group. This file supplies everything
those specializations share: the relation matrix, the Hopf ideal with its three closure
conditions, the quotient, the group scheme with its closed immersion into `GLₙ`, local finite
type, and the ambient membership criterion `M C Mᵀ = C`.

The three Hopf-ideal closure conditions are proved by matrix algebra rather than coordinate by
coordinate. Writing `f := X C Xᵀ - C` for the matrix of generators and mapping it entrywise
through the relevant algebra morphisms — each of which fixes `C`, being an `R`-algebra
morphism:

* the counit sends `X` to the identity matrix, so it sends `f` to `1 C 1ᵀ - C = 0`;
* the comultiplication sends `X` to `Y Z`, where `Y` and `Z` are the two tensor inclusions of
  `X`, and

  ```text
  (Y Z) C (Y Z)ᵀ - C = Y (Z C Zᵀ - C) Yᵀ + (Y C Yᵀ - C),
  ```

  whose two summands are the right and left tensor inclusions of `f` framed by matrices, so
  every entry lies in the right or left tensor ideal;
* the antipode sends `X` to its inverse matrix, and

  ```text
  X⁻¹ C (X⁻¹)ᵀ - C = -(X⁻¹ (X C Xᵀ - C) (X⁻¹)ᵀ),
  ```

  so every entry of the antipode image is a combination of the generators.

That each identity holds for an arbitrary constant `C` is what makes the classical examples
specializations rather than separate constructions: no step inverts `C`, transposes it, or uses
a relation between `C` and `Cᵀ`.

## Main declarations

* `TauCeti.ConstantForm.relationMatrix`: the matrix of defining relations `X C Xᵀ - C`.
* `TauCeti.ConstantForm.definingHopfIdeal`: the Hopf ideal its entries generate.
* `TauCeti.ConstantForm.coordinateHopfAlgebra`: the quotient coordinate Hopf algebra.
* `TauCeti.ConstantForm.groupScheme` and `TauCeti.ConstantForm.inclusion`: the subgroup scheme
  preserving `C` and its closed immersion into the general linear group scheme.
* `TauCeti.ConstantForm.mem_definingPointsSubgroup_iff`: an ambient point is cut out exactly
  when its matrix `M` satisfies `M C Mᵀ = C`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §2.3, where the orthogonal and symplectic groups are
  introduced as the subgroups of `GLₙ` cut out by the entries of a form relation.
* W. C. Waterhouse, *Introduction to Affine Group Schemes* (1979), Chapter 1, for such groups
  as representable functors on commutative rings.
* The Stacks Project, [Tag 022W](https://stacks.math.columbia.edu/tag/022W), for the ambient
  general linear group scheme.

The matrix form of the closure computations is standard, and the framing identities above are
not adapted from either reference. The proofs themselves are those of the merged worked
examples `TauCeti.Symplectic` (for `C = Jₘ`) and `TauCeti.Orthogonal` (for `C = 1`),
generalized here to an arbitrary `C`: the declaration order and proof plan are theirs, and
those two files now consume this one rather than repeating it. `TauCeti.Symplectic` recorded
the generalization in its own module docstring — that the computations "apply verbatim to
`X C Xᵀ - C` for any constant matrix `C`" — before it was carried out.
-/

public section

open CategoryTheory Matrix WithConv

namespace TauCeti.ConstantForm

universe u w

variable (R : Type u) [CommRing R] (n : ℕ)

/-! ### The generic matrix and the constant form -/

/-- The localized generic matrix of `GL n`, read in the bundled coordinate Hopf algebra. -/
noncomputable def genericMatrix :
    Matrix (Fin n) (Fin n) (GeneralLinear.coordinateHopfAlgebra R n) :=
  (GeneralLinear.localizedGenericMatrix R n).map
    (GeneralLinear.coordinateHopfAlgebraAlgEquiv R n)

/-- An entry of the bundled generic matrix is the bundled image of the corresponding polynomial
generator. -/
@[simp]
theorem genericMatrix_apply (i j : Fin n) :
    genericMatrix R n i j =
      GeneralLinear.coordinateHopfAlgebraAlgEquiv R n
        (GeneralLinear.coordinateRingMap R n (MvPolynomial.X (i, j))) := by
  rw [genericMatrix, Matrix.map_apply, GeneralLinear.localizedGenericMatrix_apply]

/-- The inverse of the localized generic matrix, read in the bundled coordinate Hopf algebra. -/
private noncomputable def genericMatrixInv :
    Matrix (Fin n) (Fin n) (GeneralLinear.coordinateHopfAlgebra R n) :=
  ((GeneralLinear.localizedGenericMatrix R n)⁻¹).map
    (GeneralLinear.coordinateHopfAlgebraAlgEquiv R n)

/-- The bundled generic matrix and its bundled inverse multiply to the identity. -/
private theorem genericMatrix_mul_genericMatrixInv :
    genericMatrix R n * genericMatrixInv R n = 1 := by
  rw [genericMatrix, genericMatrixInv, ← Matrix.map_mul,
    Matrix.mul_nonsing_inv _ (GeneralLinear.isUnit_det_localizedGenericMatrix R n)]
  exact Matrix.map_one _ (map_zero _) (map_one _)

/-- The bundled inverse and the bundled generic matrix multiply to the identity. -/
private theorem genericMatrixInv_mul_genericMatrix :
    genericMatrixInv R n * genericMatrix R n = 1 := by
  rw [genericMatrix, genericMatrixInv, ← Matrix.map_mul,
    Matrix.nonsing_inv_mul _ (GeneralLinear.isUnit_det_localizedGenericMatrix R n)]
  exact Matrix.map_one _ (map_zero _) (map_one _)

variable (C : Matrix (Fin n) (Fin n) R)

/-- The constant form read in an `R`-algebra through its structure morphism. -/
noncomputable abbrev formMatrix (T : Type*) [CommRing T] [Algebra R T] :
    Matrix (Fin n) (Fin n) T :=
  C.map (algebraMap R T)

/-- An `R`-algebra morphism fixes the constant form: it commutes with the structure
morphisms. -/
theorem formMatrix_map {T S : Type*} [CommRing T] [Algebra R T] [CommRing S] [Algebra R S]
    (phi : T →ₐ[R] S) : (formMatrix R n C T).map phi = formMatrix R n C S := by
  rw [formMatrix, formMatrix, Matrix.map_map]
  exact congrArg _ (funext fun r => phi.commutes r)

/-- The constant form read in the base ring itself is the matrix it started as. -/
@[simp]
theorem formMatrix_self : formMatrix R n C R = C := by
  rw [formMatrix, Algebra.algebraMap_self, RingHom.coe_id, Matrix.map_id]

/-! ### The defining relation matrix -/

/-- **The matrix of defining relations** of the subgroup scheme preserving `C`:
`X C Xᵀ - C` over the coordinate Hopf algebra of `GL n`. -/
noncomputable def relationMatrix :
    Matrix (Fin n) (Fin n) (GeneralLinear.coordinateHopfAlgebra R n) :=
  genericMatrix R n * formMatrix R n C (GeneralLinear.coordinateHopfAlgebra R n) *
      (genericMatrix R n)ᵀ -
    formMatrix R n C (GeneralLinear.coordinateHopfAlgebra R n)

/-- The set of defining relations: the entries of the relation matrix. -/
def relationSet : Set (GeneralLinear.coordinateHopfAlgebra R n) :=
  Set.range fun ij : Fin n × Fin n => relationMatrix R n C ij.1 ij.2

/-- Every entry of the relation matrix is a defining relation. -/
theorem relationMatrix_mem_relationSet (i j : Fin n) :
    relationMatrix R n C i j ∈ relationSet R n C :=
  ⟨(i, j), rfl⟩

/-- Mapping the relation matrix through an algebra morphism gives the relation of the images:
the generic matrix maps entrywise, and the constant form maps to the constant form. -/
private theorem relationMatrix_map {T : Type*} [CommRing T] [Algebra R T]
    (phi : GeneralLinear.coordinateHopfAlgebra R n →ₐ[R] T) :
    (relationMatrix R n C).map phi =
      (genericMatrix R n).map phi * formMatrix R n C T *
          ((genericMatrix R n).map phi)ᵀ -
        formMatrix R n C T := by
  rw [relationMatrix, Matrix.map_sub, Matrix.map_mul, Matrix.map_mul,
    formMatrix_map R n C phi, Matrix.transpose_map]
  exact fun a b => map_sub phi a b

/-- An entry of a framed relation matrix `P (X C Xᵀ - C) Q` lies in any ideal containing the
entries of the middle factor. This is the only membership computation the closure proofs
need. -/
private theorem entry_mul_mul_mem {S : Type*} [CommRing S] (K : Ideal S) {μ : ℕ}
    {M : Matrix (Fin μ) (Fin μ) S} (hM : ∀ k l, M k l ∈ K)
    (P Q : Matrix (Fin μ) (Fin μ) S) (i j : Fin μ) : (P * M * Q) i j ∈ K := by
  rw [Matrix.mul_apply]
  refine Ideal.sum_mem _ fun k _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul]
  refine Ideal.sum_mem _ fun t _ => ?_
  exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (hM t k))

/-! ### The three Hopf-ideal closure conditions -/

/-- The counit sends the bundled generic matrix to the identity matrix. -/
private theorem genericMatrix_map_counit :
    (genericMatrix R n).map
        (Bialgebra.counitAlgHom R (GeneralLinear.coordinateHopfAlgebra R n)) = 1 := by
  ext i j
  rw [Matrix.map_apply, genericMatrix_apply, Bialgebra.counitAlgHom_apply,
    GeneralLinear.coordinateHopfAlgebra_counit_X, Matrix.one_apply]

/-- The counit vanishes on every defining relation. -/
private theorem counit_relationMatrix (i j : Fin n) :
    Coalgebra.counit (R := R) (relationMatrix R n C i j) = 0 := by
  have h := congrFun (congrFun (relationMatrix_map R n C
    (Bialgebra.counitAlgHom R (GeneralLinear.coordinateHopfAlgebra R n))) i) j
  rw [Matrix.map_apply, Bialgebra.counitAlgHom_apply] at h
  rw [h, genericMatrix_map_counit, formMatrix_self, Matrix.transpose_one, Matrix.one_mul,
    Matrix.mul_one, sub_self, Matrix.zero_apply]

/-- The comultiplication sends the bundled generic matrix to the product of its two tensor
inclusions: `Δ X = (X ⊗ 1)(1 ⊗ X)`. -/
private theorem genericMatrix_map_comul :
    (genericMatrix R n).map
        (Bialgebra.comulAlgHom R (GeneralLinear.coordinateHopfAlgebra R n)) =
      (genericMatrix R n).map
          (Algebra.TensorProduct.includeLeft (R := R) (S := R)) *
        (genericMatrix R n).map (Algebra.TensorProduct.includeRight (R := R)) := by
  ext i j
  rw [Matrix.map_apply, genericMatrix_apply, Bialgebra.comulAlgHom_apply,
    GeneralLinear.coordinateHopfAlgebra_comul_X, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.map_apply, Matrix.map_apply, genericMatrix_apply, genericMatrix_apply,
    Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

/-- The comultiplication of the relation matrix decomposes as a right-tensor-framed copy of the
relations plus the left tensor inclusion of the relations. -/
private theorem relationMatrix_map_comul :
    (relationMatrix R n C).map
        (Bialgebra.comulAlgHom R (GeneralLinear.coordinateHopfAlgebra R n)) =
      (genericMatrix R n).map (Algebra.TensorProduct.includeLeft (R := R) (S := R)) *
          (relationMatrix R n C).map (Algebra.TensorProduct.includeRight (R := R)) *
          ((genericMatrix R n).map
            (Algebra.TensorProduct.includeLeft (R := R) (S := R)))ᵀ +
        (relationMatrix R n C).map
          (Algebra.TensorProduct.includeLeft (R := R) (S := R)) := by
  rw [relationMatrix_map R n C, relationMatrix_map R n C, relationMatrix_map R n C,
    genericMatrix_map_comul, Matrix.transpose_mul]
  conv_rhs => rw [Matrix.mul_sub, Matrix.sub_mul, sub_add_sub_cancel]
  simp only [Matrix.mul_assoc]

/-- The comultiplication of every defining relation lies in the sum of the left and right tensor
ideals of the span of the relations. -/
private theorem comul_relationMatrix_mem (i j : Fin n) :
    Coalgebra.comul (R := R) (relationMatrix R n C i j) ∈
      HopfIdeal.leftTensorIdeal (R := R)
          (H := GeneralLinear.coordinateHopfAlgebra R n)
          (Ideal.span (relationSet R n C)) ⊔
        HopfIdeal.rightTensorIdeal (R := R)
          (H := GeneralLinear.coordinateHopfAlgebra R n)
          (Ideal.span (relationSet R n C)) := by
  have h := congrFun (congrFun (relationMatrix_map_comul R n C) i) j
  rw [Matrix.map_apply, Bialgebra.comulAlgHom_apply] at h
  rw [h, Matrix.add_apply]
  refine Ideal.add_mem _ (Ideal.mem_sup_right ?_) (Ideal.mem_sup_left ?_)
  · refine entry_mul_mul_mem _ (fun k l => ?_) _ _ i j
    rw [Matrix.map_apply]
    exact HopfIdeal.includeRight_mem_rightTensorIdeal (R := R)
      (H := GeneralLinear.coordinateHopfAlgebra R n)
      (Ideal.subset_span (relationMatrix_mem_relationSet R n C k l))
  · rw [Matrix.map_apply]
    exact HopfIdeal.includeLeft_mem_leftTensorIdeal (R := R)
      (H := GeneralLinear.coordinateHopfAlgebra R n)
      (Ideal.subset_span (relationMatrix_mem_relationSet R n C i j))

/-- The antipode sends the bundled generic matrix to its bundled inverse. -/
private theorem genericMatrix_map_antipode :
    (genericMatrix R n).map
        (HopfAlgebra.antipodeAlgHom (R := R)
          (A := GeneralLinear.coordinateHopfAlgebra R n)) =
      genericMatrixInv R n := by
  ext i j
  rw [Matrix.map_apply, genericMatrix_apply, HopfAlgebra.antipodeAlgHom_apply,
    GeneralLinear.coordinateHopfAlgebra_antipode_X, genericMatrixInv, Matrix.map_apply]

/-- The antipode image of the relation matrix is the negative of the relation matrix framed by
the bundled inverse: `X⁻¹ C (X⁻¹)ᵀ - C = -(X⁻¹ (X C Xᵀ - C) (X⁻¹)ᵀ)`. -/
private theorem relationMatrix_map_antipode :
    (relationMatrix R n C).map
        (HopfAlgebra.antipodeAlgHom (R := R)
          (A := GeneralLinear.coordinateHopfAlgebra R n)) =
      -(genericMatrixInv R n * relationMatrix R n C * (genericMatrixInv R n)ᵀ) := by
  have ht : (genericMatrix R n)ᵀ * (genericMatrixInv R n)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, genericMatrixInv_mul_genericMatrix, Matrix.transpose_one]
  have hkey : genericMatrixInv R n * relationMatrix R n C * (genericMatrixInv R n)ᵀ =
      formMatrix R n C (GeneralLinear.coordinateHopfAlgebra R n) -
        genericMatrixInv R n *
          formMatrix R n C (GeneralLinear.coordinateHopfAlgebra R n) *
          (genericMatrixInv R n)ᵀ := by
    rw [relationMatrix, Matrix.mul_sub, Matrix.sub_mul]
    congr 1
    calc genericMatrixInv R n *
          (genericMatrix R n * formMatrix R n C (GeneralLinear.coordinateHopfAlgebra R n) *
            (genericMatrix R n)ᵀ) * (genericMatrixInv R n)ᵀ
        = genericMatrixInv R n * genericMatrix R n *
            formMatrix R n C (GeneralLinear.coordinateHopfAlgebra R n) *
            ((genericMatrix R n)ᵀ * (genericMatrixInv R n)ᵀ) := by
          simp only [Matrix.mul_assoc]
      _ = formMatrix R n C (GeneralLinear.coordinateHopfAlgebra R n) := by
          rw [genericMatrixInv_mul_genericMatrix, ht, Matrix.one_mul, Matrix.mul_one]
  rw [relationMatrix_map R n C, genericMatrix_map_antipode, hkey, neg_sub]

/-- The antipode carries every defining relation into the span of the relations. -/
private theorem antipode_relationMatrix_mem (i j : Fin n) :
    HopfAlgebra.antipode R (relationMatrix R n C i j) ∈ Ideal.span (relationSet R n C) := by
  have h := congrFun (congrFun (relationMatrix_map_antipode R n C) i) j
  rw [Matrix.map_apply, HopfAlgebra.antipodeAlgHom_apply] at h
  rw [h, Matrix.neg_apply]
  exact neg_mem (entry_mul_mul_mem _
    (fun k l => Ideal.subset_span (relationMatrix_mem_relationSet R n C k l)) _ _ i j)

/-! ### The defining Hopf ideal and quotient -/

/-- **The Hopf ideal preserving `C`**: the ideal of the coordinate Hopf algebra of `GL n`
generated by the entries of `X C Xᵀ - C`, with the three closure conditions extended from the
generators across the span. -/
noncomputable def definingHopfIdeal :
    HopfIdeal R (GeneralLinear.coordinateHopfAlgebra R n) :=
  HopfIdeal.ofIdeal (Ideal.span (relationSet R n C))
    (fun x hx => by
      induction hx using Submodule.span_induction with
      | mem y hy => obtain ⟨ij, rfl⟩ := hy; exact comul_relationMatrix_mem R n C ij.1 ij.2
      | zero => rw [map_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
      | smul h x _ hx =>
          rw [smul_eq_mul, Bialgebra.comul_mul]
          exact Ideal.mul_mem_left _ _ hx)
    (fun x hx => by
      induction hx using Submodule.span_induction with
      | mem y hy => obtain ⟨ij, rfl⟩ := hy; exact counit_relationMatrix R n C ij.1 ij.2
      | zero => rw [map_zero]
      | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
      | smul h x _ hx => rw [smul_eq_mul, Bialgebra.counit_mul, hx, mul_zero])
    (fun x hx => by
      induction hx using Submodule.span_induction with
      | mem y hy => obtain ⟨ij, rfl⟩ := hy; exact antipode_relationMatrix_mem R n C ij.1 ij.2
      | zero => rw [map_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
      | smul h x _ hx =>
          rw [smul_eq_mul, HopfAlgebra.antipode_mul_distrib]
          exact Ideal.mul_mem_left _ _ hx)

/-- The underlying ideal of the defining Hopf ideal is the span of the defining relations. -/
@[simp]
theorem definingHopfIdeal_toIdeal :
    (definingHopfIdeal R n C).toIdeal = Ideal.span (relationSet R n C) := by
  rw [HopfIdeal.toIdeal_carrier, definingHopfIdeal, HopfIdeal.ofIdeal_carrier]

/-- The coordinate Hopf algebra of the subgroup scheme of `GL n` preserving `C`. -/
noncomputable abbrev coordinateHopfAlgebra : _root_.CommHopfAlgCat.{u} R :=
  CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra R n)
    (definingHopfIdeal R n C)

/-- The quotient coordinate morphism from `O(GL n)` to the coordinate Hopf algebra of the
subgroup scheme preserving `C`. -/
noncomputable def coordinateMap :
    GeneralLinear.coordinateHopfAlgebra R n ⟶ coordinateHopfAlgebra R n C :=
  CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra R n)
    (definingHopfIdeal R n C)

/-- The coordinate morphism sends an ambient coordinate to its quotient class. -/
theorem coordinateMap_apply (h : GeneralLinear.coordinateHopfAlgebra R n) :
    (coordinateMap R n C).hom h =
      Ideal.Quotient.mkₐ R (definingHopfIdeal R n C).toIdeal h := by
  unfold coordinateMap
  exact CommHopfAlgCat.mkQuotient_apply
    (GeneralLinear.coordinateHopfAlgebra R n) (definingHopfIdeal R n C) h

/-- Every defining relation vanishes in the quotient coordinate Hopf algebra. -/
@[simp]
theorem coordinateMap_relationMatrix (i j : Fin n) :
    (coordinateMap R n C).hom (relationMatrix R n C i j) = 0 := by
  rw [coordinateMap_apply, Ideal.Quotient.mkₐ_eq_mk]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    (definingHopfIdeal_toIdeal R n C ▸
      Ideal.subset_span (relationMatrix_mem_relationSet R n C i j))

/-! ### The group scheme and its closed immersion -/

/-- The subgroup scheme of `GL n` preserving `C`. -/
noncomputable def groupScheme :=
  CommHopfAlgCat.quotientSpec (GeneralLinear.coordinateHopfAlgebra R n)
    (definingHopfIdeal R n C)

private noncomputable def groupSchemeι :=
  CommHopfAlgCat.quotientSpecι (GeneralLinear.coordinateHopfAlgebra R n)
    (definingHopfIdeal R n C)

/-- The closed-subgroup inclusion into the named general linear group scheme. -/
noncomputable def inclusion : groupScheme R n C ⟶ GeneralLinear.groupScheme R n :=
  groupSchemeι R n C ≫ (eqToIso (GeneralLinear.groupScheme_def R n).symm).hom

private theorem inclusion_hom_left :
    (inclusion R n C).hom.hom.left =
      (CommHopfAlgCat.quotientSpecι
        (GeneralLinear.coordinateHopfAlgebra R n)
        (definingHopfIdeal R n C)).hom.hom.left ≫
      ((eqToIso (GeneralLinear.groupScheme_def R n).symm).hom).hom.hom.left := by
  rw [inclusion]
  unfold groupSchemeι
  rfl

/-- The inclusion into the named general linear group scheme is a closed immersion. -/
instance isClosedImmersion_inclusion :
    AlgebraicGeometry.IsClosedImmersion (inclusion R n C).hom.hom.left := by
  let c := (CommHopfAlgCat.quotientSpecι
    (GeneralLinear.coordinateHopfAlgebra R n) (definingHopfIdeal R n C)).hom.hom.left
  let e₂ := ((eqToIso (GeneralLinear.groupScheme_def R n).symm).hom).hom.hom.left
  have he₂ : IsIso e₂ :=
    ((Over.forget (AlgebraicGeometry.Spec (CommRingCat.of R))).mapIso
      ((Grp.forget (Over (AlgebraicGeometry.Spec (CommRingCat.of R)))).mapIso
        (eqToIso (GeneralLinear.groupScheme_def R n).symm))).isIso_hom
  have hc : AlgebraicGeometry.IsClosedImmersion c := by
    infer_instance
  have hc₂ : AlgebraicGeometry.IsClosedImmersion (c ≫ e₂) :=
    (@MorphismProperty.cancel_right_of_respectsIso
      _ _ @AlgebraicGeometry.IsClosedImmersion inferInstance _ _ _ c e₂ he₂).2 hc
  rw [inclusion_hom_left]
  exact hc₂

/-- The quotient coordinate Hopf algebra, bundled with its finite-type property. -/
noncomputable def finiteTypeCoordinateHopfAlgebra : FiniteTypeCommHopfAlgCat R :=
  FiniteTypeCommHopfAlgCat.quotient
    (⟨GeneralLinear.coordinateHopfAlgebra R n, by
      rw [← GeneralLinear.finiteTypeCoordinateHopfAlgebra_obj]
      exact (GeneralLinear.finiteTypeCoordinateHopfAlgebra R n).property⟩ :
      FiniteTypeCommHopfAlgCat R)
    (definingHopfIdeal R n C)

/-- The finite-type package has the quotient coordinate Hopf algebra as its underlying
object. -/
@[simp]
theorem finiteTypeCoordinateHopfAlgebra_obj :
    (finiteTypeCoordinateHopfAlgebra R n C).obj = coordinateHopfAlgebra R n C := by
  rw [finiteTypeCoordinateHopfAlgebra]

/-- The structural morphism of the subgroup scheme preserving `C` is locally of finite type. -/
instance locallyOfFiniteType_groupScheme :
    AlgebraicGeometry.LocallyOfFiniteType (groupScheme R n C).X.hom := by
  unfold groupScheme
  exact FiniteTypeCommHopfAlgCat.locallyOfFiniteType_quotientSpec
    (⟨GeneralLinear.coordinateHopfAlgebra R n, by
        rw [← GeneralLinear.finiteTypeCoordinateHopfAlgebra_obj]
        exact (GeneralLinear.finiteTypeCoordinateHopfAlgebra R n).property⟩ :
      FiniteTypeCommHopfAlgCat R)
    (definingHopfIdeal R n C)

/-! ### Algebra-valued points -/

section Points

variable {A : Type w} [CommRing A] [Algebra R A]

/-- Evaluating the relation matrix at a point gives the form relation of its matrix. -/
private theorem ofConv_relationMatrix
    (g : HopfAlgebra.points (R := R)
      (H := GeneralLinear.coordinateHopfAlgebra R n) (CommAlgCat.of R A)) :
    (relationMatrix R n C).map g.ofConv =
      (GeneralLinear.pointToGeneralLinear n g : Matrix (Fin n) (Fin n) A) *
          formMatrix R n C A *
          (GeneralLinear.pointToGeneralLinear n g : Matrix (Fin n) (Fin n) A)ᵀ -
        formMatrix R n C A := by
  have hg : (genericMatrix R n).map g.ofConv =
      (GeneralLinear.pointToGeneralLinear n g : Matrix (Fin n) (Fin n) A) := by
    ext i j
    rw [Matrix.map_apply, genericMatrix_apply]
    exact (GeneralLinear.pointToGeneralLinear_apply n g i j).symm
  rw [relationMatrix_map R n C g.ofConv, hg]

/-- **The ambient membership criterion**: an ambient point belongs to the subgroup cut out by
the defining Hopf ideal exactly when its matrix `M` satisfies `M C Mᵀ = C`.

This is the criterion the classical specializations consume: `TauCeti.Orthogonal` reads it as
membership in `Matrix.orthogonalGroup` and `TauCeti.Symplectic` as membership in
`TauCeti.GLSymplecticFin`. It is deliberately not a `simp` lemma — the specializations state
the normal form a user wants, and their left-hand sides are this one. -/
theorem mem_definingPointsSubgroup_iff
    (g : HopfAlgebra.points (R := R)
      (H := GeneralLinear.coordinateHopfAlgebra R n) (CommAlgCat.of R A)) :
    g ∈ CommHopfAlgCat.quotientPointsSubgroup
        (GeneralLinear.coordinateHopfAlgebra R n) (definingHopfIdeal R n C)
        (CommAlgCat.of R A) ↔
      (GeneralLinear.pointsMulEquiv n g : Matrix (Fin n) (Fin n) A) * formMatrix R n C A *
          (GeneralLinear.pointsMulEquiv n g : Matrix (Fin n) (Fin n) A)ᵀ =
        formMatrix R n C A := by
  rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff, GeneralLinear.pointsMulEquiv_apply]
  constructor
  · intro h
    have hzero : (relationMatrix R n C).map g.ofConv = 0 := by
      ext i j
      rw [Matrix.map_apply, Matrix.zero_apply]
      exact h _ (HopfIdeal.mem_toIdeal.mp
        (definingHopfIdeal_toIdeal R n C ▸
          Ideal.subset_span (relationMatrix_mem_relationSet R n C i j)))
    rw [ofConv_relationMatrix R n C g] at hzero
    exact sub_eq_zero.mp hzero
  · intro h y hy
    have hzero : (relationMatrix R n C).map g.ofConv = 0 := by
      rw [ofConv_relationMatrix R n C g]
      exact sub_eq_zero.mpr h
    have hle : Ideal.span (relationSet R n C) ≤
        RingHom.ker (g.ofConv :
          GeneralLinear.coordinateHopfAlgebra R n →ₐ[R] A) := by
      rw [Ideal.span_le]
      rintro _ ⟨ij, rfl⟩
      have := congrFun (congrFun hzero ij.1) ij.2
      rw [Matrix.map_apply, Matrix.zero_apply] at this
      exact this
    exact hle (definingHopfIdeal_toIdeal R n C ▸ HopfIdeal.mem_toIdeal.mpr hy)

end Points

end TauCeti.ConstantForm
