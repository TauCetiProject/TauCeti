/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.AB
public import TauCeti.Algebra.Category.GradedVectorSpace.LaurentK0
public import TauCeti.CategoryTheory.GrothendieckGroup.FiniteDimensionalVectorSpace
public import TauCeti.CategoryTheory.GrothendieckGroup.ForgetGrading

/-!
# Forgetting the grading of finite graded vector spaces

Let `k` be a field. Forgetting the grading of a finite graded vector space `V` is the
finite-dimensional vector space `U V = ⨁ⱼ Vⱼ`. This is an exact functor `U` from finite graded
vector spaces to `FGModuleCat k`, and it is invariant under the grading shift, `{1} ⋙ U ≅ U`.
These are exactly the data from which forgetting the grading induces a map on Grothendieck groups
that factors through the specialization of the graded Grothendieck group at `q = 1`
(`TauCeti.LaurentK0.forgetGradingMap`).

For finite graded vector spaces this factor map is an isomorphism

```text
K₀^gr ⊗ ℤ[q = 1] ≃ K₀(fd vector spaces),    [V] ↦ [⨁ⱼ Vⱼ],
```

because both sides are free of rank one and dimension matches the graded dimension at `q = 1`:
`dim_k(⨁ⱼ Vⱼ) = gdim(V)(1)`. Before specialization the map is not injective. The one-dimensional
space `M = k` in degree `0` and its shift `M{1}` have the distinct classes `[M]` and `q[M]`, but
both forget to `k`. Shift compatibility of `U` alone therefore does not make the map on graded
`K₀` an isomorphism; the specialization at `q = 1` is needed.

## Main definitions

* `TauCeti.GradedVectorSpace.finiteForget`: the forgetful functor `V ↦ ⨁ⱼ Vⱼ` into
  `FGModuleCat k`.
* `TauCeti.GradedVectorSpace.shiftCompFiniteForgetIso`: its invariance `{1} ⋙ U ≅ U`.
* `TauCeti.GradedVectorSpace.forgetGradingEquiv`: the isomorphism from graded `K₀` specialized at
  `q = 1` to abelian `K₀` of finite-dimensional vector spaces induced by forgetting the grading.

## Main results

* `TauCeti.GradedVectorSpace.isConflationExact_finiteForget`: forgetting the grading is
  conflation-exact.
* `TauCeti.GradedVectorSpace.toExactK0_forgetGradingEquiv`: the isomorphism is the general
  comparison map `TauCeti.LaurentK0.forgetGradingMap` for this functor.
* `TauCeti.GradedVectorSpace.finrank_forgetGradingEquiv_mk`: the dimension of the forgotten class
  is the graded dimension at `q = 1`.
* `TauCeti.GradedVectorSpace.not_injective_forgetGradingUnderlyingMap`: before specializing at
  `q = 1`, forgetting the grading is not injective on graded `K₀`.

## References

* Zsuzsanna Dancso and Anthony Licata, "Koszul algebras and flow lattices", *Journal of
  Combinatorial Theory, Series A* **185** (2022), Section 2.2, for graded Grothendieck groups and
  specialization at `q = 1`.
* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II, Section 6,
  for the Grothendieck group of finite-dimensional vector spaces.
-/

public section

open scoped DirectSum

namespace TauCeti

open CategoryTheory CategoryTheory.Limits LaurentPolynomial

universe u

variable (k : Type u) [Field k]

namespace GradedVectorSpace

/-! ### The forgetful functor -/

/-- The direct sum of the pieces of a finite graded vector space is finite-dimensional. -/
theorem isFG_total_obj (V : (finite k).FullSubcategory) :
    ModuleCat.isFG k ((GradedObject.total ℤ (ModuleCat.{u} k)).obj V.obj) := by
  have := ((finite_iff _).1 V.property).finiteDimensional_directSum
  exact Module.Finite.equiv (ModuleCat.coprodIsoDirectSum _).toLinearEquiv.symm

/-- **Forgetting the grading** of a finite graded vector space `V`: the finite-dimensional vector
space `⨁ⱼ Vⱼ`, given by Mathlib's `GradedObject.total`. -/
noncomputable def finiteForget : (finite k).FullSubcategory ⥤ FGModuleCat.{u} k :=
  (ModuleCat.isFG k).lift ((finite k).ι ⋙ GradedObject.total ℤ (ModuleCat.{u} k))
    (isFG_total_obj k)

/-- The vector space underlying a forgotten finite graded vector space is its total space. -/
noncomputable def finiteForgetCompιIso :
    finiteForget k ⋙ (ModuleCat.isFG k).ι ≅
      (finite k).ι ⋙ GradedObject.total ℤ (ModuleCat.{u} k) :=
  (ModuleCat.isFG k).liftCompιIso _ _

/-- Forgetting the grading is additive. -/
noncomputable instance : (finiteForget k).Additive :=
  inferInstanceAs ((ModuleCat.isFG k).lift _ (isFG_total_obj k)).Additive

/-- The dimension of the forgotten space is the dimension of the direct sum of the pieces. -/
theorem finrank_finiteForget_obj (V : (finite k).FullSubcategory) :
    Module.finrank k ((finiteForget k).obj V) = Module.finrank k (⨁ j, (V.obj j : Type u)) :=
  (ModuleCat.coprodIsoDirectSum _).toLinearEquiv.finrank_eq

/-- The dimension of the forgotten space is the graded dimension at `q = 1`. -/
theorem natCast_finrank_finiteForget_obj (V : (finite k).FullSubcategory) :
    (Module.finrank k ((finiteForget k).obj V) : ℤ) =
      laurentEval (1 : ℤˣ)
        (gradedDimension k (fun j ↦ (V.obj j : Type u)) ((finite_iff _).1 V.property)) := by
  rw [finrank_finiteForget_obj, laurentEval_one_gradedDimension]

/-- **Forgetting the grading is exact**: it sends short exact sequences of finite graded vector
spaces to short exact sequences of finite-dimensional vector spaces. Coproducts of vector spaces
are exact. -/
theorem isConflationExact_finiteForget :
    (finiteExactStructure k).toExactStructure.IsConflationExact
      (ExactStructure.abelian (FGModuleCat.{u} k)) (finiteForget k) where
  map_conflation {S} hS := by
    apply (ExactStructure.reflectsConflations_abelian_of_faithful
      (ModuleCat.isFG k).ι).reflects_conflation
    have h := (ExactStructure.isConflationExact_abelian
      (GradedObject.total ℤ (ModuleCat.{u} k))).map_conflation
      ((ExactStructure.abelian_conflation _).2 ((finiteExactStructure_conflation_iff k S).1 hS))
    rw [← ShortComplex.map_comp] at h
    exact (ExactStructure.abelian _).conflation_of_iso
      (S.mapNatIso (finiteForgetCompιIso k)).symm h

/-- **Forgetting the grading is invariant under the grading shift**: `{1} ⋙ U ≅ U`. -/
noncomputable def shiftCompFiniteForgetIso :
    (finiteExactStructure k).shift.functor ⋙ finiteForget k ≅ finiteForget k :=
  ((ModuleCat.isFG k).fullyFaithfulι.whiskeringRight _).preimageIso <|
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (finiteForgetCompιIso k) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (finiteShiftFunctorCompιIso k) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (shiftCompTotalIso k) ≪≫
      (finiteForgetCompιIso k).symm

/-! ### Forgetting the grading on Grothendieck groups -/

/-- The forgotten one-dimensional space `M = k` in degree `0` is one-dimensional. -/
theorem finrank_finiteForget_obj_unitFinite :
    Module.finrank k ((finiteForget k).obj (unitFinite k)) = 1 := by
  have h := natCast_finrank_finiteForget_obj k (unitFinite k)
  rw [gradedDimension_unit, map_one] at h
  exact_mod_cast h

/-- The inverse of `TauCeti.GradedVectorSpace.forgetGradingEquiv`: a class of dimension `n` goes
to `n` times the specialized class of `M = k` in degree `0`. -/
private noncomputable def forgetGradingInv :
    AbelianK0 (FGModuleCat.{u} k) →ₗ[ℤ]
      LaurentSpecialization (1 : ℤˣ) (LaurentK0.{u} (finiteExactStructure k)) :=
  (AbelianK0.finrank k).toIntLinearMap.smulRight
    (LaurentSpecialization.mk 1 (LaurentK0.of.{u} (finiteExactStructure k) (unitFinite k)))

/-- **Forgetting the grading identifies graded `K₀` at `q = 1` with ordinary `K₀`.** The
isomorphism sends the specialized class of a finite graded vector space `V` to the class of
`⨁ⱼ Vⱼ` in abelian `K₀` of finite-dimensional vector spaces
(`TauCeti.GradedVectorSpace.forgetGradingEquiv_mk_of`); it is the comparison map
`TauCeti.LaurentK0.forgetGradingMap` of the forgetful functor
(`TauCeti.GradedVectorSpace.toExactK0_forgetGradingEquiv`). -/
noncomputable def forgetGradingEquiv :
    LaurentSpecialization (1 : ℤˣ) (LaurentK0.{u} (finiteExactStructure k)) ≃ₗ[ℤ]
      AbelianK0 (FGModuleCat.{u} k) :=
  LinearEquiv.ofLinearMap
    ((AbelianK0.toExactK0 _).symm.toIntLinearEquiv.toLinearMap ∘ₗ
      LaurentK0.forgetGradingMap (isConflationExact_finiteForget k) (shiftCompFiniteForgetIso k))
    (forgetGradingInv k)
    (LinearMap.toAddMonoidHom_injective <| AbelianK0.hom_ext fun X ↦ by
      have hX := AbelianK0.of_eq_finrank_nsmul k ((finiteForget k).obj (unitFinite k)) X
        (finrank_finiteForget_obj_unitFinite k)
      simp [forgetGradingInv, hX, finrank_finiteForget_obj_unitFinite])
    (LaurentK0.hom_ext_laurentSpecialization 1 fun V ↦ by
      simp only [LinearMap.comp_apply, LaurentK0.forgetGradingMap_mk_of, forgetGradingInv,
        LinearMap.smulRight_apply, LinearEquiv.coe_coe, LinearMap.id_apply]
      conv_rhs => rw [of_eq_gradedDimension_smul k V, map_smul, LaurentSpecialization.mk_smul,
        ← natCast_finrank_finiteForget_obj]
      simp)

/-- The isomorphism `TauCeti.GradedVectorSpace.forgetGradingEquiv` is the comparison map
`TauCeti.LaurentK0.forgetGradingMap` of the forgetful functor, read in abelian `K₀`. -/
theorem toExactK0_forgetGradingEquiv
    (x : LaurentSpecialization (1 : ℤˣ) (LaurentK0.{u} (finiteExactStructure k))) :
    AbelianK0.toExactK0 _ (forgetGradingEquiv k x) =
      LaurentK0.forgetGradingMap.{u, u, u + 1, u + 1, u, u} (isConflationExact_finiteForget k)
        (shiftCompFiniteForgetIso k) x := by
  simp [forgetGradingEquiv]

/-- **The comparison map after forgetting the grading is an isomorphism** for finite graded vector
spaces. -/
theorem forgetGradingMap_bijective :
    Function.Bijective (LaurentK0.forgetGradingMap.{u, u, u + 1, u + 1, u, u}
      (isConflationExact_finiteForget k) (shiftCompFiniteForgetIso k)) := by
  have h : ⇑(LaurentK0.forgetGradingMap.{u, u, u + 1, u + 1, u, u}
      (isConflationExact_finiteForget k) (shiftCompFiniteForgetIso k)) =
        AbelianK0.toExactK0 _ ∘ forgetGradingEquiv k :=
    funext fun x ↦ (toExactK0_forgetGradingEquiv k x).symm
  rw [h]
  exact (AbelianK0.toExactK0 _).bijective.comp (forgetGradingEquiv k).bijective

/-- Forgetting the grading sends the specialized class of `V` to the class of `⨁ⱼ Vⱼ`. -/
@[simp]
theorem forgetGradingEquiv_mk_of (V : (finite k).FullSubcategory) :
    forgetGradingEquiv k
        (LaurentSpecialization.mk 1 (LaurentK0.of.{u} (finiteExactStructure k) V)) =
      AbelianK0.of ((finiteForget k).obj V) := by
  simp [forgetGradingEquiv]

/-- The inverse isomorphism sends a class of dimension `n` to `n` times the specialized class of
`M = k` in degree `0`. -/
theorem forgetGradingEquiv_symm_apply (x : AbelianK0 (FGModuleCat.{u} k)) :
    (forgetGradingEquiv k).symm x =
      AbelianK0.finrank k x •
        LaurentSpecialization.mk 1 (LaurentK0.of.{u} (finiteExactStructure k) (unitFinite k)) :=
  (rfl)

/-- **The dimension of a forgotten class is its graded dimension at `q = 1`.** -/
theorem finrank_forgetGradingEquiv_mk (x : LaurentK0.{u} (finiteExactStructure k)) :
    AbelianK0.finrank k (forgetGradingEquiv k (LaurentSpecialization.mk 1 x)) =
      laurentEval (1 : ℤˣ) (laurentK0Equiv k x) := by
  obtain ⟨p, rfl⟩ := (laurentK0Equiv k).symm.surjective x
  rw [LinearEquiv.apply_symm_apply, laurentK0Equiv_symm_apply, map_smul,
    LaurentSpecialization.mk_smul, map_zsmul, forgetGradingEquiv_mk_of, map_zsmul,
    AbelianK0.finrank_of, finrank_finiteForget_obj_unitFinite]
  simp

/-- **Forgetting the grading is not injective on graded `K₀`.** The classes `[M{1}] = q[M]` and
`[M]` of `M = k` in degree `0` are distinct, but both forget to the class of `k`. Hence a
shift-invariant conflation-exact functor need not induce an isomorphism before specialization at
`q = 1`. -/
theorem not_injective_forgetGradingUnderlyingMap :
    ¬ Function.Injective
      (LaurentK0.forgetGradingUnderlyingMap.{u, u, u + 1, u + 1, u, u}
        (isConflationExact_finiteForget k)) := by
  intro h
  have hT := congrArg (laurentK0Equiv k) <| h <|
    LaurentK0.forgetGradingUnderlyingMap_T_one (isConflationExact_finiteForget k)
      (shiftCompFiniteForgetIso k) (LaurentK0.of.{u} (finiteExactStructure k) (unitFinite k))
  rw [map_smul, laurentK0Equiv_of, gradedDimension_unit, smul_eq_mul, mul_one] at hT
  -- `q ≠ 1`, as their values at `q = -1` differ.
  have h₁ := congrArg (laurentEval (-1 : ℤˣ)) hT
  simp at h₁

end GradedVectorSpace

end TauCeti
