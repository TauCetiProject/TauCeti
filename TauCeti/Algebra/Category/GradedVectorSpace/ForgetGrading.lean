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

For graded vector spaces this map is an isomorphism, by the sufficient hypotheses of
`TauCeti.LaurentK0.forgetGradingEquiv`, which are verified here directly. First, every short exact
sequence of finite-dimensional vector spaces splits, and each of its terms is the total space of
itself placed in degree `0`, so it lifts term by term to a split sequence of finite graded vector
spaces. Second, the forgetful map sends a specialized class to the integer obtained by evaluating
its graded dimension at `q = 1`, which is the total dimension; since the specialization of
`K₀^gr ≃ ℤ[q,q⁻¹]` at `q = 1` is free on the class of `M = k` placed in degree `0`, graded vector
spaces with isomorphic total spaces have the same class at `q = 1`. Thus, at `q = 1`, the
specialized graded class of `V` is identified with the ordinary class of its underlying vector
space.

The ungraded category is `FGModuleCat k` rather than all of `ModuleCat k`, so that it has a
Grothendieck group; it is the essentially small category of finite-dimensional vector spaces in
which the total spaces of finite graded vector spaces lie.

## Main definitions

* `TauCeti.GradedVectorSpace.finiteTotal`: the total space of a finite graded vector space, as a
  functor to `FGModuleCat k`.
* `TauCeti.GradedVectorSpace.finiteTotalCommShift`: its invariance under the grading shift.
* `TauCeti.GradedVectorSpace.forgetGradingK0Equiv`: forgetting the grading identifies `K₀^gr`
  specialized at `q = 1` with `K₀` of finite-dimensional vector spaces.

## Main results

* `TauCeti.GradedVectorSpace.isConflationExact_finiteTotal`: forgetting the grading is exact.
* `TauCeti.GradedVectorSpace.finrank_forgetGrading`: the dimension of the forgotten class is the
  graded dimension at `q = 1`.
* `TauCeti.GradedVectorSpace.exists_lift_conflation_finiteTotal` and
  `TauCeti.GradedVectorSpace.mk_one_of_eq_of_finiteTotal_iso`: the comparison hypotheses of
  `TauCeti.LaurentK0.forgetGradingEquiv` for forgetting the grading.
* `TauCeti.GradedVectorSpace.forgetGradingK0Equiv_toLinearMap`: the equivalence is the map induced
  by forgetting the grading.

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

/-! ### The comparison hypotheses -/

/-- The total space of a vector space placed in degree `0` is that vector space. -/
private noncomputable def totalObjSingleIso (Y : ModuleCat.{u} k) :
    (∐ fun i : ℤ ↦ (GradedObject.single₀ ℤ).obj Y i) ≅ Y where
  hom := Sigma.desc fun i ↦ if hi : i = 0 then
    eqToHom (congrArg ((GradedObject.single₀ ℤ).obj Y) hi) ≫
      (GradedObject.singleObjApplyIso 0 Y).hom
    else 0
  inv := (GradedObject.singleObjApplyIso 0 Y).inv ≫ Sigma.ι _ 0
  hom_inv_id := by
    apply Sigma.hom_ext
    intro i
    by_cases hi : i = 0
    · subst i
      simp only [colimit.ι_desc_assoc, Discrete.functor_obj_eq_as, Cofan.mk_pt, Cofan.mk_ι_app,
        ↓reduceDIte, eqToHom_refl, Category.id_comp, Iso.hom_inv_id_assoc, Category.comp_id]
    · exact (GradedObject.isInitialSingleObjApply 0 Y i hi).isZero.eq_of_src _ _
  inv_hom_id := by
    rw [Category.assoc, Sigma.ι_comp_desc]
    simp

/-- A finite-dimensional vector space placed in degree `0` is a finite graded vector space. -/
private theorem finite_single (Y : FGModuleCat.{u} k) :
    finite k ((GradedObject.single₀ ℤ).obj Y.obj) := by
  refine (finite_iff _).2 <| HasFiniteLaurentSupport.of_finset (fun i ↦ ?_) {0} fun i hi ↦
    ModuleCat.subsingleton_of_isZero
      (GradedObject.isInitialSingleObjApply 0 Y.obj i (by simpa using hi)).isZero
  by_cases hi : i = 0
  · have : Module.Finite k Y.obj := Y.property
    exact Module.Finite.equiv (R := k)
      (GradedObject.singleObjApplyIsoOfEq 0 Y.obj i hi).toLinearEquiv.symm
  · have := ModuleCat.subsingleton_of_isZero
      (GradedObject.isInitialSingleObjApply 0 Y.obj i hi).isZero
    infer_instance

/-- Every finite-dimensional vector space is, up to isomorphism, the underlying vector space of a
finite graded vector space: place it in degree `0`. -/
private theorem exists_finiteTotal_obj_iso (Y : FGModuleCat.{u} k) :
    ∃ V : (finite k).FullSubcategory, Nonempty ((finiteTotal k).obj V ≅ Y) :=
  ⟨⟨_, finite_single k Y⟩, ⟨(ModuleCat.isFG k).fullyFaithfulι.preimageIso
    ((finiteTotalCompιIso k).app _ ≪≫ totalObjSingleIso k Y.obj)⟩⟩

/-- **Short exact sequences of vector spaces lift along forgetting the grading**: every short exact
sequence `Y₁ ↪ Y₂ ↠ Y₃` of finite-dimensional vector spaces is, term by term, the underlying
sequence of a short exact sequence of finite graded vector spaces. Since `Y₁ ↪ Y₂ ↠ Y₃` splits, it
lifts to the split sequence `V₁ ↪ V₁ ⊞ V₃ ↠ V₃`, where `Vᵢ` lifts `Yᵢ`. This is the first
comparison hypothesis of `TauCeti.LaurentK0.forgetGradingEquiv`. -/
theorem exists_lift_conflation_finiteTotal (S : ShortComplex (FGModuleCat.{u} k))
    (hS : (ExactStructure.abelian (FGModuleCat.{u} k)).Conflation S) :
    ∃ S' : ShortComplex (finite k).FullSubcategory,
      (finiteExactStructure k).Conflation S' ∧ Nonempty ((finiteTotal k).obj S'.X₁ ≅ S.X₁) ∧
        Nonempty ((finiteTotal k).obj S'.X₂ ≅ S.X₂) ∧
          Nonempty ((finiteTotal k).obj S'.X₃ ≅ S.X₃) := by
  obtain ⟨s⟩ := FGModuleCat.nonempty_splitting_of_shortExact k
    ((ExactStructure.abelian_conflation S).1 hS)
  obtain ⟨V₁, ⟨e₁⟩⟩ := exists_finiteTotal_obj_iso k S.X₁
  obtain ⟨V₃, ⟨e₃⟩⟩ := exists_finiteTotal_obj_iso k S.X₃
  have := preservesBinaryBiproducts_of_preservesBiproducts (finiteTotal k)
  exact ⟨_, (finiteExactStructure k).conflation_of_splitting
    (ShortComplex.Splitting.ofHasBinaryBiproduct V₁ V₃), ⟨e₁⟩,
    ⟨(finiteTotal k).mapBiprod V₁ V₃ ≪≫ biprod.mapIso e₁ e₃ ≪≫ s.isoBinaryBiproduct.symm⟩, ⟨e₃⟩⟩

/-- **Isomorphic underlying vector spaces give equal classes at `q = 1`**: if two finite graded
vector spaces have isomorphic underlying vector spaces, then their specialized classes at `q = 1`
agree, since both are the common total dimension times the class of `M`. This is the second
comparison hypothesis of `TauCeti.LaurentK0.forgetGradingEquiv`. -/
theorem mk_one_of_eq_of_finiteTotal_iso (V W : (finite k).FullSubcategory)
    (e : Nonempty ((finiteTotal k).obj V ≅ (finiteTotal k).obj W)) :
    LaurentSpecialization.mk (1 : ℤˣ) (LaurentK0.of.{u} (finiteExactStructure k) V) =
      LaurentSpecialization.mk 1 (LaurentK0.of.{u} (finiteExactStructure k) W) := by
  refine (laurentSpecializationBasis k 1).ext_elem fun i ↦ ?_
  rw [laurentSpecializationBasis_repr_mk, laurentSpecializationBasis_repr_mk,
    ← finrank_forgetGrading, ← finrank_forgetGrading, LaurentK0.forgetGrading_mk_of,
    LaurentK0.forgetGrading_mk_of, ExactK0.of_congr e.some]

/-- **Forgetting the grading is an isomorphism at `q = 1`**: the graded Grothendieck group of
finite graded vector spaces, specialized at `q = 1`, is identified with the Grothendieck group of
finite-dimensional vector spaces. This instantiates `TauCeti.LaurentK0.forgetGradingEquiv`, whose
comparison hypotheses are `TauCeti.GradedVectorSpace.exists_lift_conflation_finiteTotal` and
`TauCeti.GradedVectorSpace.mk_one_of_eq_of_finiteTotal_iso`. -/
noncomputable def forgetGradingK0Equiv :
    LaurentSpecialization (1 : ℤˣ) (LaurentK0.{u} (finiteExactStructure k)) ≃ₗ[ℤ]
      ExactK0.{u} (ExactStructure.abelian (FGModuleCat.{u} k)) :=
  LaurentK0.forgetGradingEquiv (isConflationExact_finiteTotal k) (finiteTotalCommShift k)
    (exists_lift_conflation_finiteTotal k) (mk_one_of_eq_of_finiteTotal_iso k)

/-- The forward map of `TauCeti.GradedVectorSpace.forgetGradingK0Equiv` is the map induced by
forgetting the grading. -/
@[simp]
theorem forgetGradingK0Equiv_toLinearMap :
    (forgetGradingK0Equiv k).toLinearMap =
      LaurentK0.forgetGrading.{u, u} (isConflationExact_finiteTotal k)
        (finiteTotalCommShift k) :=
  LaurentK0.forgetGradingEquiv_toLinearMap ..

/-- `TauCeti.GradedVectorSpace.forgetGradingK0Equiv` forgets the grading of a specialized class. -/
@[simp]
theorem forgetGradingK0Equiv_apply
    (x : LaurentSpecialization (1 : ℤˣ) (LaurentK0.{u} (finiteExactStructure k))) :
    forgetGradingK0Equiv k x =
      LaurentK0.forgetGrading.{u, u} (isConflationExact_finiteTotal k)
        (finiteTotalCommShift k) x := by
  rw [← LinearEquiv.coe_coe, forgetGradingK0Equiv_toLinearMap]

/-- At `q = 1`, the specialized class of a finite graded vector space is sent to the class of its
underlying vector space. -/
theorem forgetGradingK0Equiv_mk_of (V : (finite k).FullSubcategory) :
    forgetGradingK0Equiv k (LaurentSpecialization.mk 1 (LaurentK0.of.{u} _ V)) =
      ExactK0.of ((finiteTotal k).obj V) := by
  simp

/-- The inverse of `TauCeti.GradedVectorSpace.forgetGradingK0Equiv` sends an ungraded class to its
dimension times the specialized class of `M`. -/
theorem forgetGradingK0Equiv_symm_apply
    (x : ExactK0.{u} (ExactStructure.abelian (FGModuleCat.{u} k))) :
    (forgetGradingK0Equiv k).symm x =
      AbelianK0.finrank k ((AbelianK0.toExactK0 (FGModuleCat.{u} k)).symm x) •
        LaurentSpecialization.mk 1 (LaurentK0.of.{u} (finiteExactStructure k) (unitFinite k)) := by
  obtain ⟨y, rfl⟩ := (forgetGradingK0Equiv k).surjective x
  obtain ⟨y, rfl⟩ := LaurentSpecialization.mk_surjective 1 y
  rw [LinearEquiv.symm_apply_apply, forgetGradingK0Equiv_apply, finrank_forgetGrading,
    ← laurentSpecializationBasis_repr_mk k 1 _ (), ← laurentSpecializationBasis_apply k 1 ()]
  simpa using ((laurentSpecializationBasis k 1).sum_repr (LaurentSpecialization.mk 1 y)).symm

end GradedVectorSpace

end TauCeti
