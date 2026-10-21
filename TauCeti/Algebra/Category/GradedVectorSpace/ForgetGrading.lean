/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import TauCeti.Algebra.Category.GradedVectorSpace.LaurentK0
public import TauCeti.CategoryTheory.GrothendieckGroup.FiniteDimensionalVectorSpace

/-!
# Forgetting the grading on finite graded vector spaces

Let `k` be a field. Forgetting the grading of a finite graded vector space `V` is taking its total
space `U V = ⨁ⱼ Vⱼ`, a finite-dimensional vector space (`TauCeti.GradedVectorSpace.finiteTotal`).
This functor is exact, and it is invariant under the grading shift, `{1} ⋙ U ≅ U`. Hence it
induces a map from the graded Grothendieck group specialized at `q = 1` to the Grothendieck group
of finite-dimensional vector spaces (`TauCeti.LaurentK0.forgetGrading`).

For graded vector spaces this map is an isomorphism. Both sides are free of rank one: the
specialization of `K₀^gr ≃ ℤ[q,q⁻¹]` at any `q = ε` is free on the class of `M = k` placed in
degree `0`, and `K₀` of finite-dimensional vector spaces is `ℤ` by dimension. The forgetful map
sends a specialized class to the integer obtained by evaluating its graded dimension at `q = 1`,
which is the total dimension. Thus, at `q = 1`, the specialized graded class of `V` is identified
with the ordinary class of its underlying vector space.

The ungraded category is `FGModuleCat k` rather than all of `ModuleCat k`, so that it has a
Grothendieck group; it is the essentially small category of finite-dimensional vector spaces in
which the total spaces of finite graded vector spaces lie.

At `q = -1` the specialized group is still free on the class of `M`, so the sign `[M{1}] = -[M]`
produced by a single shift is a genuine change of class.

## Main definitions

* `TauCeti.GradedVectorSpace.finiteTotal`: the total space of a finite graded vector space, as a
  functor to `FGModuleCat k`.
* `TauCeti.GradedVectorSpace.finiteTotalCommShift`: its invariance under the grading shift.
* `TauCeti.GradedVectorSpace.laurentSpecializationBasis`: the basis `[M]` of `K₀^gr` specialized
  at `q = ε`.
* `TauCeti.GradedVectorSpace.forgetGradingK0Equiv`: forgetting the grading identifies `K₀^gr`
  specialized at `q = 1` with `K₀` of finite-dimensional vector spaces.

## Main results

* `TauCeti.GradedVectorSpace.isConflationExact_finiteTotal`: forgetting the grading is exact.
* `TauCeti.GradedVectorSpace.finrank_forgetGrading`: the dimension of the forgotten class is the
  graded dimension at `q = 1`.
* `TauCeti.GradedVectorSpace.forgetGradingK0Equiv_toLinearMap`: the equivalence is the map induced
  by forgetting the grading.
* `TauCeti.GradedVectorSpace.mk_neg_one_of_shift_unitFinite_ne`: at `q = -1` the classes of `M{1}`
  and `M` differ.

## References

* Zsuzsanna Dancso and Anthony Licata, "Koszul algebras and flow lattices", *Journal of
  Combinatorial Theory, Series A* **185** (2022), Section 2.2, for graded Grothendieck groups and
  their specialization at `q = 1`.
* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II, Section 6,
  for Grothendieck groups of finite-dimensional vector spaces.
-/

public section

open scoped DirectSum

namespace TauCeti

open CategoryTheory CategoryTheory.Limits LaurentPolynomial

universe u

variable (k : Type u) [Field k]

namespace GradedVectorSpace

/-! ### The forgetful functor -/

/-- The total space of a finite graded vector space is finite-dimensional. -/
private theorem isFG_total_obj (V : (finite k).FullSubcategory) :
    ModuleCat.isFG k ((GradedObject.total ℤ (ModuleCat.{u} k)).obj V.obj) := by
  have := ((finite_iff _).1 V.property).finiteDimensional_directSum
  exact Module.Finite.equiv (ModuleCat.coprodIsoDirectSum V.obj).toLinearEquiv.symm

/-- **Forgetting the grading** of a finite graded vector space `V`: its total space `⨁ⱼ Vⱼ`, as a
finite-dimensional vector space. -/
noncomputable def finiteTotal : (finite k).FullSubcategory ⥤ FGModuleCat.{u} k :=
  (ModuleCat.isFG k).lift ((finite k).ι ⋙ GradedObject.total ℤ (ModuleCat.{u} k))
    (isFG_total_obj k)

/-- Forgetting the grading followed by the inclusion into all vector spaces is totalizing. -/
noncomputable def finiteTotalCompιIso :
    finiteTotal k ⋙ (ModuleCat.isFG k).ι ≅
      (finite k).ι ⋙ GradedObject.total ℤ (ModuleCat.{u} k) :=
  (ModuleCat.isFG k).liftCompιIso _ _

/-- Forgetting the grading is additive, as totalizing is. -/
instance : (finiteTotal k).Additive :=
  have : (finiteTotal k ⋙ (ModuleCat.isFG k).ι).Additive :=
    Functor.additive_of_iso (finiteTotalCompιIso k).symm
  Functor.additive_of_comp_faithful _ (ModuleCat.isFG k).ι

/-- The vector space underlying a finite graded vector space `V` is the direct sum `⨁ⱼ Vⱼ` of its
pieces. -/
noncomputable def finiteTotalObjLinearEquiv (V : (finite k).FullSubcategory) :
    (finiteTotal k).obj V ≃ₗ[k] ⨁ j, (V.obj j : Type u) :=
  ((finiteTotalCompιIso k).app V ≪≫ ModuleCat.coprodIsoDirectSum V.obj).toLinearEquiv

/-- The dimension of the vector space underlying `V` is the sum of the dimensions of its pieces. -/
@[simp]
theorem finrank_finiteTotal_obj (V : (finite k).FullSubcategory) :
    Module.finrank k ((finiteTotal k).obj V) = Module.finrank k (⨁ j, (V.obj j : Type u)) :=
  (finiteTotalObjLinearEquiv k V).finrank_eq

/-- **Forgetting the grading is exact**: it sends short exact sequences of finite graded vector
spaces to short exact sequences of vector spaces, because coproducts of vector spaces are exact. -/
theorem isConflationExact_finiteTotal :
    (finiteExactStructure k).toExactStructure.IsConflationExact
      (ExactStructure.abelian (FGModuleCat.{u} k)) (finiteTotal k) where
  map_conflation {S} hS := by
    rw [ExactStructure.abelian_conflation]
    apply CategoryTheory.ShortExact.reflects_shortExact_of_faithful (ModuleCat.isFG k).ι
    rw [← ShortComplex.map_comp]
    refine ShortComplex.shortExact_of_iso (S.mapNatIso (finiteTotalCompιIso k)).symm ?_
    rw [ShortComplex.map_comp]
    exact ((finiteExactStructure_conflation_iff k S).1 hS).map_of_exact _

/-- **Forgetting the grading is invariant under the shift**: `{1} ⋙ U ≅ U`, restricted from the
totalization of all graded vector spaces. -/
noncomputable def finiteTotalCommShift :
    (finiteExactStructure k).shift.functor ⋙ finiteTotal k ≅ finiteTotal k := by
  rw [finiteExactStructure_def]
  exact GradedExactStructure.liftCommShift _ _ _ _ _
    (by rw [GradedExactStructure.abelian_shift]; exact shiftCompTotalIso k)

/-! ### Specializations of the graded Grothendieck group -/

/-- The specialization of the graded Grothendieck group of finite graded vector spaces at `q = ε`
is free of rank one, on the class of `M = k` placed in degree `0`. -/
noncomputable def laurentSpecializationBasis (ε : ℤˣ) :
    Module.Basis Unit ℤ (LaurentSpecialization ε (LaurentK0.{u} (finiteExactStructure k))) :=
  LaurentSpecialization.basis ε
    ((Module.Basis.singleton Unit (LaurentPolynomial ℤ)).map (laurentK0Equiv k).symm)

/-- The vector of `TauCeti.GradedVectorSpace.laurentSpecializationBasis` is the specialized class
of `M`. -/
@[simp]
theorem laurentSpecializationBasis_apply (ε : ℤˣ) (i : Unit) :
    laurentSpecializationBasis k ε i =
      LaurentSpecialization.mk ε (LaurentK0.of.{u} (finiteExactStructure k) (unitFinite k)) := by
  simp [laurentSpecializationBasis]

/-- The coordinate of a specialized class is its graded dimension evaluated at `q = ε`. -/
@[simp]
theorem laurentSpecializationBasis_repr_mk (ε : ℤˣ)
    (x : LaurentK0.{u} (finiteExactStructure k)) (i : Unit) :
    (laurentSpecializationBasis k ε).repr (LaurentSpecialization.mk ε x) i =
      laurentEval ε (laurentK0Equiv k x) := by
  simp [laurentSpecializationBasis]

/-- **At `q = -1` a single shift changes the class**: the specialized class of `M{1}`, which is
`-[M]` by `TauCeti.LaurentK0.mk_of_shift_functor_obj`, differs from that of `M`. -/
theorem mk_neg_one_of_shift_unitFinite_ne :
    LaurentSpecialization.mk (-1 : ℤˣ) (LaurentK0.of.{u} (finiteExactStructure k)
        ((finiteExactStructure k).shift.functor.obj (unitFinite k))) ≠
      LaurentSpecialization.mk (-1 : ℤˣ)
        (LaurentK0.of.{u} (finiteExactStructure k) (unitFinite k)) := by
  intro h
  have := congrArg (fun x ↦ (laurentSpecializationBasis k (-1 : ℤˣ)).repr x ()) h
  simp at this

/-! ### Forgetting the grading at `q = 1` -/

/-- **Forgetting the grading computes the total dimension**: the dimension of the ungraded class
of a graded class, specialized at `q = 1`, is its graded dimension evaluated at `q = 1`. -/
theorem finrank_forgetGrading (x : LaurentK0.{u} (finiteExactStructure k)) :
    AbelianK0.finrank k ((AbelianK0.toExactK0 (FGModuleCat.{u} k)).symm
        (LaurentK0.forgetGrading.{u, u} (isConflationExact_finiteTotal k) (finiteTotalCommShift k)
          (LaurentSpecialization.mk 1 x))) =
      laurentEval 1 (laurentK0Equiv k x) := by
  obtain ⟨x, rfl⟩ := (LaurentK0.ofExactK0.{u} _).surjective x
  induction x using ExactK0.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | neg x hx => simp only [map_neg, hx]
  | of V =>
    simp [finrank_finiteTotal_obj]

/-- **Forgetting the grading is an isomorphism at `q = 1`**: the graded Grothendieck group of
finite graded vector spaces, specialized at `q = 1`, is identified with the Grothendieck group of
finite-dimensional vector spaces. Both are `ℤ`, by the specialized coordinate of `[M]` and by
dimension. -/
noncomputable def forgetGradingK0Equiv :
    LaurentSpecialization (1 : ℤˣ) (LaurentK0.{u} (finiteExactStructure k)) ≃ₗ[ℤ]
      ExactK0.{u} (ExactStructure.abelian (FGModuleCat.{u} k)) :=
  ((laurentSpecializationBasis k 1).equivFun.trans (LinearEquiv.funUnique Unit ℤ ℤ)).trans
    ((AbelianK0.toExactK0 (FGModuleCat.{u} k)).symm.trans
      (AbelianK0.finrankEquiv k)).toIntLinearEquiv.symm

/-- The forward map of `TauCeti.GradedVectorSpace.forgetGradingK0Equiv` is the map induced by
forgetting the grading. -/
@[simp]
theorem forgetGradingK0Equiv_toLinearMap :
    (forgetGradingK0Equiv k).toLinearMap =
      LaurentK0.forgetGrading.{u, u} (isConflationExact_finiteTotal k)
        (finiteTotalCommShift k) := by
  refine LinearMap.ext fun x ↦ ?_
  obtain ⟨x, rfl⟩ := LaurentSpecialization.mk_surjective 1 x
  apply ((AbelianK0.toExactK0 (FGModuleCat.{u} k)).symm.trans
    (AbelianK0.finrankEquiv k)).injective
  simp [forgetGradingK0Equiv, finrank_forgetGrading]

/-- At `q = 1`, the specialized class of a finite graded vector space is sent to the class of its
underlying vector space. -/
@[simp]
theorem forgetGradingK0Equiv_mk_of (V : (finite k).FullSubcategory) :
    forgetGradingK0Equiv k (LaurentSpecialization.mk 1 (LaurentK0.of.{u} _ V)) =
      ExactK0.of ((finiteTotal k).obj V) := by
  rw [← LinearEquiv.coe_coe, forgetGradingK0Equiv_toLinearMap, LaurentK0.forgetGrading_mk_of]

/-- The inverse of `TauCeti.GradedVectorSpace.forgetGradingK0Equiv` sends an ungraded class to its
dimension times the specialized class of `M`. -/
theorem forgetGradingK0Equiv_symm_apply
    (x : ExactK0.{u} (ExactStructure.abelian (FGModuleCat.{u} k))) :
    (forgetGradingK0Equiv k).symm x =
      AbelianK0.finrank k ((AbelianK0.toExactK0 (FGModuleCat.{u} k)).symm x) •
        LaurentSpecialization.mk 1 (LaurentK0.of.{u} (finiteExactStructure k) (unitFinite k)) := by
  rw [← laurentSpecializationBasis_apply k 1 (), ← (laurentSpecializationBasis k 1).sum_repr
    ((forgetGradingK0Equiv k).symm x)]
  simp [forgetGradingK0Equiv]

end GradedVectorSpace

end TauCeti
