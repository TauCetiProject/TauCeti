/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Fppf.Quotient.Homogeneous.Basic
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.RootSubgroup.ClosedImmersion
public import TauCeti.AlgebraicGeometry.PuncturedAffineSpace
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Transvection
import TauCeti.RingTheory.Ideal.Operations

/-!
# `SL₂` modulo its upper unipotent subgroup is the punctured plane

Let `N⁺ ⊆ SL₂` be the upper unipotent subgroup, the root subgroup `x₀₁(𝔾ₐ)` of the matrices
`n(t) = [[1, t], [0, 1]]`. Right multiplication by `n(t)` fixes the first column of a matrix, so
the first column is a map from `SL₂` to the punctured plane `𝔸²_R \ 0`, whose points with values
in `A` are the pairs `(a, c)` generating the unit ideal of `A`. This file proves that this map
identifies the fppf homogeneous quotient `SL₂ / N⁺` with the punctured plane, over every
commutative base ring `R`:

```text
SL₂ / N⁺ ≅ 𝔸²_R \ 0.
```

On points with values in `A`, every unimodular pair `(a, c)` is the first column of a matrix
`[[a, -y], [c, x]]` of determinant one, where `x a + y c = 1`, and two matrices of determinant
one with the same first column differ by right multiplication by an element of `N⁺(A)`. In
particular every section of the quotient over an affine scheme lifts to `SL₂` without passing to
a cover.

For nonzero `R` the punctured plane is quasi-affine but not affine. Its ring of global functions
is `R[a, c]`, the ring of right `N⁺`-invariant functions on `SL₂`
(`TauCeti.SpecialLinear.coinvariants_rootSubgroupHopfIdeal_two_eq_adjoin`), whose spectrum `𝔸²_R`
is only the affinization of the quotient.

## Main declarations

* `TauCeti.SpecialLinear.firstColumn`: the first column of a point of `SL₂`, as a point of the
  punctured plane.
* `TauCeti.SpecialLinear.firstColumn_eq_firstColumn_iff`: two points of `SL₂` have the same first
  column exactly when they differ by a point of `N⁺`.
* `TauCeti.SpecialLinear.firstColumn_surjective`: every point of the punctured plane is a first
  column.
* `TauCeti.SpecialLinear.fppfHomogeneousQuotientIsoPuncturedPlane`: **`SL₂ / N⁺` is represented
  by the punctured plane.**

## References

* J. S. Milne, *Algebraic Groups* (2017), §5, homogeneous spaces and quotient sheaves.
* I. Hedén, *Affine extensions of principal additive bundles over a punctured surface*,
  arXiv:1407.7638, §§1 and 3, for the rank-one torsor `SL₂ → 𝔸² \ 0`.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite

namespace TauCeti.SpecialLinear

universe u

variable {R : Type u} [CommRing R] {A : CommAlgCat.{u} R}

/-- The first column of a point of `SL₂` with values in `A`, as a point of the punctured plane
`𝔸²_R \ 0` with values in `A`. -/
noncomputable def firstColumn
    (g : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R 2) A) :
    (algSpec (.of R)).obj (op A) ⟶ puncturedAffineSpace R (Fin 2) :=
  PuncturedAffineSpace.ofUnimodular
    ((pointsMulEquiv (R := R) (A := A) 2 g : Matrix (Fin 2) (Fin 2) A).col 0)
    ((Ideal.span_range_fin_two_eq_top_iff _).mpr (Matrix.SpecialLinearGroup.isCoprime_col _ 0))

/-- The coordinates of the first column of a point `g` of `SL₂` are the entries of the first
column of its matrix. -/
@[simp]
theorem coordinateAlgHom_firstColumn
    (g : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R 2) A) (i : Fin 2) :
    PuncturedAffineSpace.coordinateAlgHom (firstColumn g) (MvPolynomial.X i) =
      (pointsMulEquiv (R := R) (A := A) 2 g : Matrix (Fin 2) (Fin 2) A) i 0 := by
  rw [firstColumn, PuncturedAffineSpace.coordinateAlgHom_ofUnimodular, MvPolynomial.aeval_X,
    Matrix.col_apply]

/-- Two points of `SL₂` have the same first column exactly when their matrices have the same
first column. -/
theorem firstColumn_eq_firstColumn_iff_col_zero_eq
    (g g' : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R 2) A) :
    firstColumn g = firstColumn g' ↔
      (pointsMulEquiv (R := R) (A := A) 2 g : Matrix (Fin 2) (Fin 2) A).col 0 =
        (pointsMulEquiv (R := R) (A := A) 2 g' : Matrix (Fin 2) (Fin 2) A).col 0 := by
  refine ⟨fun h ↦ funext fun i ↦ ?_, fun h ↦ PuncturedAffineSpace.hom_ext fun i ↦ ?_⟩
  · have hi := congrArg (fun s ↦ PuncturedAffineSpace.coordinateAlgHom s (MvPolynomial.X i)) h
    rw [coordinateAlgHom_firstColumn, coordinateAlgHom_firstColumn] at hi
    exact hi
  · rw [coordinateAlgHom_firstColumn, coordinateAlgHom_firstColumn]
    exact congrFun h i

/-- **The fibres of the first column are the cosets of `N⁺`.** Two points of `SL₂` have the same
first column exactly when they differ by right multiplication by a point of the upper unipotent
subgroup. -/
theorem firstColumn_eq_firstColumn_iff
    (g g' : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R 2) A) :
    firstColumn g = firstColumn g' ↔
      g⁻¹ * g' ∈ CommHopfAlgCat.quotientPointsSubgroup (coordinateHopfAlgebra R 2)
        (rootSubgroupHopfIdeal (zero_ne_one : (0 : Fin 2) ≠ 1)) A := by
  rw [firstColumn_eq_firstColumn_iff_col_zero_eq]
  constructor
  · intro h
    obtain ⟨t, ht⟩ := Matrix.SpecialLinearGroup.exists_eq_mul_transvection_of_col_zero_eq h
    refine (mem_quotientPointsSubgroup_rootSubgroupHopfIdeal_iff (A := A) _ _).mpr ⟨t, ?_⟩
    rw [map_mul, map_inv, ht, inv_mul_cancel_left]
  · intro h
    obtain ⟨t, ht⟩ := (mem_quotientPointsSubgroup_rootSubgroupHopfIdeal_iff (A := A) _ _).mp h
    have hg' : pointsMulEquiv (R := R) (A := A) 2 g' =
        pointsMulEquiv (R := R) (A := A) 2 g *
          Matrix.SpecialLinearGroup.transvection (zero_ne_one : (0 : Fin 2) ≠ 1) t := by
      rw [← ht, ← map_mul, mul_inv_cancel_left]
    rw [hg']
    funext i
    rw [Matrix.col_apply, Matrix.col_apply, Matrix.SpecialLinearGroup.coe_mul]
    exact (Matrix.mul_transvection_apply_of_ne _ _ _ _ (zero_ne_one : (0 : Fin 2) ≠ 1) _ _).symm

/-- The first column is invariant under right multiplication by the upper unipotent subgroup. -/
theorem firstColumn_mul
    (g : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R 2) A)
    (n : CommHopfAlgCat.quotientPointsSubgroup (coordinateHopfAlgebra R 2)
      (rootSubgroupHopfIdeal (zero_ne_one : (0 : Fin 2) ≠ 1)) A) :
    firstColumn (g * n.val) = firstColumn g :=
  ((firstColumn_eq_firstColumn_iff _ _).mpr (by simp)).symm

/-- **Every point of the punctured plane is a first column.** Every unimodular pair `(a, c)` in
`A` is the first column of a matrix of determinant one, so the first column is surjective on
points with values in every algebra. -/
theorem firstColumn_surjective :
    Function.Surjective
      (firstColumn : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R 2) A → _) := by
  intro s
  obtain ⟨M, h0, h1⟩ := ((Ideal.span_range_fin_two_eq_top_iff _).mp
    ((PuncturedAffineSpace.homEquiv R (Fin 2) A) s).2).exists_SL2_col 0
  refine ⟨(pointsMulEquiv (R := R) (A := A) 2).symm M,
    PuncturedAffineSpace.hom_ext fun i ↦ ?_⟩
  rw [coordinateAlgHom_firstColumn, MulEquiv.apply_symm_apply,
    ← PuncturedAffineSpace.coe_homEquiv_apply]
  fin_cases i
  exacts [h0, h1]

/-- The first column is natural in the value algebra: the first column of the image of `g`
under `φ : A ⟶ B` is the restriction of the first column of `g` along `Spec B ⟶ Spec A`. -/
theorem firstColumn_mapValue {B : CommAlgCat.{u} R} (φ : A ⟶ B)
    (g : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R 2) A) :
    firstColumn (AlgHom.mapValue (H := coordinateHopfAlgebra R 2) φ.hom g) =
      (algSpec (.of R)).map φ.op ≫ firstColumn g :=
  PuncturedAffineSpace.hom_ext fun i ↦ by
    simp only [coordinateAlgHom_firstColumn, PuncturedAffineSpace.coordinateAlgHom_comp,
      AlgHom.comp_apply]
    rw [pointsMulEquiv_mapValue]
    simp

variable (R) in
/-- The first-column map from `SL₂` to the punctured plane, as a natural map of functors of
points over all `R`-algebras. -/
noncomputable def firstColumnPoints :
    HopfAlgebra.pointsPresheaf (coordinateHopfAlgebra R 2) ⋙ uliftFunctor.{u + 1, u} ⟶
      (CommAlgCat.pointsSheaf (puncturedAffineSpace R (Fin 2))).obj where
  app A := ↾fun g ↦ ULift.up (firstColumn (A := A.unop.unop) (ULift.down g))
  naturality A B χ := by
    ext ⟨g⟩
    exact congrArg ULift.up (firstColumn_mapValue χ.unop.unop g)

/-- The first-column map of functors of points sends a point `g` of `SL₂` to its first column. -/
theorem firstColumnPoints_app_apply (A : (CommAlgCat.{u} R)ᵒᵖᵒᵖ)
    (g : ULift (HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R 2) A.unop.unop)) :
    (firstColumnPoints R).app A g = ULift.up (firstColumn g.down) :=
  (rfl)

/-- Every point of the punctured plane lifts to `SL₂`, so the first-column map is locally
surjective for the fppf topology, without passing to a cover. -/
instance isLocallySurjective_firstColumnPoints :
    Presheaf.IsLocallySurjective (CommAlgCat.fppfTopology R) (firstColumnPoints R) :=
  Presheaf.isLocallySurjective_of_surjective _ _ fun A ⟨s⟩ ↦
    let ⟨g, hg⟩ := firstColumn_surjective (A := A.unop.unop) s
    ⟨ULift.up g, congrArg ULift.up hg⟩

variable (R) in
/-- The first-column map, descended to the fppf homogeneous quotient `SL₂ / N⁺`. -/
noncomputable def fppfHomogeneousQuotientToPuncturedPlane :
    CommHopfAlgCat.fppfHomogeneousQuotient (coordinateHopfAlgebra R 2)
        (rootSubgroupHopfIdeal (zero_ne_one : (0 : Fin 2) ≠ 1)) ⟶
      CommAlgCat.pointsSheaf (puncturedAffineSpace R (Fin 2)) :=
  (CommHopfAlgCat.fppfHomogeneousQuotientHomEquiv _ _ _).symm
    ⟨firstColumnPoints R, fun _ g n ↦ congrArg ULift.up (firstColumn_mul g n)⟩

/-- The descended map restricts to the first-column map along the projection `SL₂ ⟶ SL₂ / N⁺`. -/
@[reassoc (attr := simp)]
theorem fppfHomogeneousQuotientProjection_comp_toPuncturedPlane :
    CommHopfAlgCat.fppfHomogeneousQuotientProjection (coordinateHopfAlgebra R 2)
        (rootSubgroupHopfIdeal (zero_ne_one : (0 : Fin 2) ≠ 1)) ≫
      (fppfHomogeneousQuotientToPuncturedPlane R).hom = firstColumnPoints R :=
  CommHopfAlgCat.fppfHomogeneousQuotientHomEquiv_symm_apply _ _ _ _ _

/-- The first column identifies `SL₂ / N⁺` with the punctured plane. -/
instance isIso_fppfHomogeneousQuotientToPuncturedPlane :
    IsIso (fppfHomogeneousQuotientToPuncturedPlane R) :=
  -- The fibres of the first column are exactly the cosets of `N⁺`.
  CommHopfAlgCat.isIso_fppfHomogeneousQuotientHomEquiv_symm _ _ _ _ _ fun _ g g' h ↦
    (firstColumn_eq_firstColumn_iff g g').mp (congrArg ULift.down h)

variable (R) in
/-- **`SL₂ / N⁺` is the punctured plane.** Over every commutative ring `R`, the first column of a
matrix identifies the fppf homogeneous quotient of `SL₂` by its upper unipotent subgroup
`N⁺ = {[[1, t], [0, 1]]}` with the sheaf of points of the punctured plane `𝔸²_R \ 0`. -/
noncomputable def fppfHomogeneousQuotientIsoPuncturedPlane :
    CommHopfAlgCat.fppfHomogeneousQuotient (coordinateHopfAlgebra R 2)
        (rootSubgroupHopfIdeal (zero_ne_one : (0 : Fin 2) ≠ 1)) ≅
      CommAlgCat.pointsSheaf (puncturedAffineSpace R (Fin 2)) :=
  asIso (fppfHomogeneousQuotientToPuncturedPlane R)

@[simp]
theorem fppfHomogeneousQuotientIsoPuncturedPlane_hom :
    (fppfHomogeneousQuotientIsoPuncturedPlane R).hom = fppfHomogeneousQuotientToPuncturedPlane R :=
  (rfl)

end TauCeti.SpecialLinear
