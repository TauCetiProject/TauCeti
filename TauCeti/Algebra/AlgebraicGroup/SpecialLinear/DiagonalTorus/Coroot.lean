/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Cocharacter
public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeGroup.Tangent
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.DiagonalTorus.Basic
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Tangent.Basic
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Diagonal.Basic
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Differential

/-!
# Simple-coroot cocharacters of the special linear group

`SpecialLinear.diagonalTorusCoordinateMap r R` parametrizes the determinant-one diagonal torus of
`SL_{r+1}` in fundamental-weight coordinates, whose dual basis is the basis of simple coroots.
Restricting to the `i`-th torus coordinate defines `simpleCorootCocharacter r R i :
O(SL_{r+1}) →ₐc[R] R[T;T⁻¹]` over any commutative ring `R`, sending `u : Aˣ` on `A`-points to
`Matrix.SpecialLinearGroup.diag2nUnit _ u` (`pointsMulEquiv_pointsHom_simpleCorootCocharacter`) and
sending a tangent vector `d` of `𝔾ₘ` to `singleSubSingle i.castSucc i.succ _`
(`tangentMatrix_derivationComp_simpleCorootCocharacter`). Downstream,
`TauCeti/Algebra/AlgebraicGroup/Tangent/Lie/Sl2Triple/Cocharacter.lean` specializes `r = 1, i = 0`
to attach the neutral cocharacter `𝔾ₘ ⟶ G` to an integrated `sl₂` triple.

## References

* J. S. Milne, *Algebraic Groups* (2017), Ch. 12, 21; J. E. Humphreys, *Linear Algebraic Groups*,
  §26.3.
-/

public section

open CategoryTheory TauCeti TauCeti.Cocharacter WithConv
open scoped LaurentPolynomial

namespace TauCeti.SpecialLinear

universe u v

variable (r : ℕ) (R : Type u) [CommRing R]

/-- **The `i`-th simple-coroot cocharacter of `SL_{r+1}`**, restricting the `i`-th coordinate of
`diagonalTorusCoordinateMap r R`. -/
noncomputable def simpleCorootCocharacter (i : Fin r) :
    coordinateHopfAlgebra R (r + 1) →ₐc[R] LaurentPolynomial R :=
  (diagonalTorusCoordinateMap r R).hom.cocharacter
    (Finsupp.applyAddHom (ULift.up i)).toMultiplicative

/-- Unfolding `simpleCorootCocharacter` via `diagonalTorusCoordinateMap`. -/
theorem simpleCorootCocharacter_def (i : Fin r) : simpleCorootCocharacter r R i =
    (diagonalTorusCoordinateMap r R).hom.cocharacter
      (Finsupp.applyAddHom (ULift.up i)).toMultiplicative := by rfl

variable {r R}

/-- On `A`-points, `simpleCorootCocharacter r R i` sends `u : Aˣ` to `diag2nUnit _ u`. -/
@[simp] theorem pointsMulEquiv_pointsHom_simpleCorootCocharacter {A : Type v} [CommRing A]
    [Algebra R A] (i : Fin r) (u : Aˣ) : pointsMulEquiv (R := R) (A := A) (r + 1)
      (Cocharacter.pointsHom A (simpleCorootCocharacter r R i) u) =
      Matrix.SpecialLinearGroup.diag2nUnit
        ((Fin.castSucc_lt_succ_iff (a := i) (b := i)).mpr le_rfl).ne u := by
  have hne : i.castSucc ≠ i.succ := ((Fin.castSucc_lt_succ_iff (a := i) (b := i)).mpr le_rfl).ne
  let ψ := (Finsupp.applyAddHom (M := ℤ) (ULift.up.{u} i)).toMultiplicative
  let q := DiagonalizableGroup.cocharPoints ψ
    ((DiagonalizableGroup.pointsMulEquiv (R := R) (A := A)).symm (zpowersHom Aˣ u))
  have hmap : BialgHom.mapDomain (diagonalTorusCoordinateMap r R).hom q =
      diagonalTorusPoints r R A q := by
    rw [BialgHom.mapDomain_apply, diagonalTorusPoints_apply,
      CommHopfAlgCat.Hom.mapPointsFunctor_app_apply]
  apply Matrix.SpecialLinearGroup.ext
  have hGL : Matrix.SpecialLinearGroup.toGL (pointsMulEquiv (R := R) (A := A) (r + 1)
        (Cocharacter.pointsHom A (simpleCorootCocharacter r R i) u)) =
      Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.diag2nUnit hne u) := by
    rw [simpleCorootCocharacter, BialgHom.pointsHom_cocharacter, hmap,
      toGL_pointsMulEquiv_diagonalTorusPoints, Matrix.SpecialLinearGroup.toGL_diag2nUnit]
    congr 1; funext a; rw [torusCharacter_diagonalTorusWeight, torusCharacter_def]
    have hcoord (j : Fin r) : SplitTorus.pointsMulEquiv q (ULift.up j) =
        u ^ (if j = i then (1 : ℤ) else 0) := by
      rw [SplitTorus.pointsMulEquiv_eq_freeAbelianCharEquiv, freeAbelianCharEquiv_apply,
        DiagonalizableGroup.pointsMulEquiv_cocharPoints, MulEquiv.apply_symm_apply,
        zpowersHom_apply, toAdd_ofAdd, zpow_one]
      congr 1; simp only [ψ, AddMonoidHom.coe_toMultiplicative, Function.comp_apply, toAdd_ofAdd,
        Finsupp.applyAddHom_apply, Finsupp.single_apply, ULift.up.injEq]
    simp_rw [hcoord, ← zpow_mul]
    rw [Finset.prod_eq_single i (fun j _ hji ↦ by simp [hji])
      (fun hi ↦ (hi (Finset.mem_univ i)).elim)]
    simp only [↓reduceIte, one_mul, SlStd.weight_def]
    by_cases h1 : a = i.castSucc; · subst h1; simp [hne]
    · by_cases h2 : a = i.succ <;> [subst h2; skip] <;> simp [*]
  exact fun a b ↦ congr_fun (congr_fun
    (congrArg (fun g : GL (Fin (r + 1)) A ↦ (g : Matrix (Fin (r + 1)) (Fin (r + 1)) A)) hGL) a) b

/-- Differential of `simpleCorootCocharacter r R i` on tangent vectors of `𝔾ₘ`. -/
@[simp] theorem tangentMatrix_derivationComp_simpleCorootCocharacter {B : Type v} [CommRing B]
    [Algebra R B] (i : Fin r)
    (d : Derivation R (LaurentPolynomial R) (Bialgebra.CounitAlgebra R (LaurentPolynomial R) B)) :
    tangentMatrix (r + 1) (derivationComp (B := B) (simpleCorootCocharacter r R i) d) =
      LieAlgebra.SpecialLinear.singleSubSingle i.castSucc i.succ
        (MultiplicativeGroup.tangentLinearEquiv d) := by
  have hne : i.castSucc ≠ i.succ := ((Fin.castSucc_lt_succ_iff (a := i) (b := i)).mpr le_rfl).ne
  have hcomp : (diagonalTorusCoordinateMap r R).hom.comp (coordinateMap R (r + 1)).hom =
      GeneralLinear.weightTorusCoordinateBialgHom (S := R) (diagonalTorusWeight.{u} r) := by
    simpa only [CommHopfAlgCat.hom_comp, GeneralLinear.hom_weightTorusCoordinateMap] using
      congrArg CommHopfAlgCat.Hom.hom (coordinateMap_comp_diagonalTorusCoordinateMap r R)
  apply Subtype.ext
  rw [LieAlgebra.SpecialLinear.val_singleSubSingle, tangentMatrix_apply_coe,
    HopfIdeal.quotientLieHom_apply, ← CommHopfAlgCat.hom_mkQuotient, ← coordinateMap,
    simpleCorootCocharacter, GeneralLinear.tangentMatrix_derivationComp_cocharacter_of_weightTorus
      (coordinateMap R (r + 1)).hom (diagonalTorusCoordinateMap r R).hom
      (diagonalTorusWeight.{u} r) hcomp _ d]
  ext a b; rw [Matrix.diagonal_apply, Matrix.sub_apply, Matrix.single_apply, Matrix.single_apply]
  by_cases hab : a = b
  · subst hab; simp only [↓reduceIte, and_self, AddMonoidHom.coe_toMultiplicative,
      Function.comp_apply, toAdd_ofAdd, Finsupp.applyAddHom_apply,
      Finsupp.coe_equivFunOnFinite_symm, diagonalTorusWeight_apply, SlStd.weight_def]
    by_cases h1 : a = i.castSucc
    · subst h1; simp only [↓reduceIte, hne, hne.symm, sub_zero, one_zsmul]
    · by_cases h2 : a = i.succ
      · subst h2; simp only [↓reduceIte, h1, hne, zero_sub, neg_one_zsmul]
      · simp only [↓reduceIte, h1, h2, Ne.symm h1, Ne.symm h2, sub_zero, zero_zsmul]
  · have hno (x) : ¬(x = a ∧ x = b) := fun ⟨ha, hb⟩ ↦ hab (ha.symm.trans hb)
    simp only [hab, hno i.castSucc, hno i.succ, ↓reduceIte, sub_zero]

end TauCeti.SpecialLinear
