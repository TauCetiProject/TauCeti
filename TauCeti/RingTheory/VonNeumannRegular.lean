/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Ring.BooleanRing
public import Mathlib.CategoryTheory.Preadditive.SingleObj
public import Mathlib.RingTheory.SimpleModule.Basic
public import TauCeti.CategoryTheory.Preadditive.VonNeumannRegular

import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.RingTheory.Jacobson.Radical
import TauCeti.CategoryTheory.Preadditive.ModCat.SingleObj
import TauCeti.CategoryTheory.Preadditive.ModCat.VonNeumannRegular
import TauCeti.CategoryTheory.SingleObj
import TauCeti.RingTheory.Semisimple.Regular

/-!
# Von Neumann regular rings and their one-object categories

A ring is von Neumann regular when each element `a` has an inner inverse `b`
satisfying `a * b * a = a`. The categorical criterion applies to both
`SingleObj A` and `SingleObj Aᵐᵒᵖ`, the latter being the source category
for left modules. In particular, regularity is preserved by reversing
multiplication, and regular rings have zero Jacobson radical.

See T. Y. Lam, *A First Course in Noncommutative Rings*, §4, (4.23)–(4.24).

The comparison between ring regularity and regularity of `SingleObj A` adapts the argument from
[Tau Ceti PR #47044](https://github.com/TauCetiProject/TauCeti/pull/47044).
-/

public section

open CategoryTheory

universe u

namespace TauCeti

/-- A von Neumann regular ring has an inner inverse for every element. -/
class IsVonNeumannRegularRing (A : Type*) [Ring A] : Prop where
  exists_mul_mul_eq_self (a : A) : ∃ b : A, a * b * a = a

/-- The one-object category of a ring is regular exactly when the ring is. -/
@[simp] theorem isVonNeumannRegularCategory_singleObj_iff (A : Type*) [Ring A] :
    IsVonNeumannRegularCategory (SingleObj A) ↔ IsVonNeumannRegularRing A := by
  refine ⟨fun h ↦ ⟨fun a ↦ ?_⟩, fun h ↦ ⟨fun {_ _} f ↦ ?_⟩⟩
  · obtain ⟨b, hb⟩ := h.exists_comp_comp_eq_self
      (X := SingleObj.star A) (Y := SingleObj.star A) a
    exact ⟨b, by simpa only [SingleObj.comp_as_mul, mul_assoc] using hb⟩
  · obtain ⟨g, hg⟩ := h.exists_mul_mul_eq_self f
    exact ⟨g, by simpa only [SingleObj.comp_as_mul, mul_assoc] using hg⟩

/-- The one-object category associated to left modules is regular exactly when the ring is. -/
theorem isVonNeumannRegularCategory_singleObj_mulOpposite_iff (A : Type*) [Ring A] :
    IsVonNeumannRegularCategory (SingleObj Aᵐᵒᵖ) ↔ IsVonNeumannRegularRing A := by
  rw [← isVonNeumannRegularCategory_singleObj_iff]
  refine ⟨fun h ↦ IsVonNeumannRegularCategory.op_iff.mp ?_, fun h ↦ ?_⟩
  · exact (SingleObj.mulOppositeEquiv A).inverse.isVonNeumannRegularCategory_of_fullyFaithful
  · exact (SingleObj.mulOppositeEquiv A).functor.isVonNeumannRegularCategory_of_fullyFaithful

/-- A ring is von Neumann regular exactly when every finitely presented left module
in the ring universe is projective. -/
theorem isVonNeumannRegularRing_iff_finitelyPresented_projective (A : Type u) [Ring A] :
    IsVonNeumannRegularRing A ↔
      ∀ (M : Type u) [AddCommGroup M] [Module A M], Module.FinitePresentation A M →
        Module.Projective A M := by
  let E := moduleCatEquivModCat.{u} A
  rw [← isVonNeumannRegularCategory_singleObj_mulOpposite_iff,
    ModCat.isVonNeumannRegularCategory_iff_finitelyPresented_projective]
  constructor
  · intro h M _ _ hM
    let N := ModuleCat.of A M
    apply (IsProjective.iff_projective M).mpr
    exact (E.map_projective_iff N).mp
      (h _ ((ModuleCat.isFinitelyPresentedFunctor_moduleCatEquivModCat_iff N).mpr hM))
  · intro h F hF
    let M := E.inverse.obj F
    let e : E.functor.obj M ≅ F := E.counitIso.app F
    have hF' : IsFinitelyPresentedFunctor (E.functor.obj M).obj :=
      (isFinitelyPresentedFunctor (SingleObj Aᵐᵒᵖ)).prop_of_iso
        ((additiveFunctor _ _).ι.mapIso e.symm) hF
    have : Module.Projective A M :=
      h M ((ModuleCat.isFinitelyPresentedFunctor_moduleCatEquivModCat_iff M).mp hF')
    exact Projective.of_iso e ((E.map_projective_iff M).mpr inferInstance)

namespace IsVonNeumannRegularRing

variable {A : Type*} [Ring A]

/-- Von Neumann regularity is invariant under reversing multiplication. -/
@[simp] theorem mulOpposite_iff : IsVonNeumannRegularRing Aᵐᵒᵖ ↔ IsVonNeumannRegularRing A :=
  (isVonNeumannRegularCategory_singleObj_iff Aᵐᵒᵖ).symm.trans
    (isVonNeumannRegularCategory_singleObj_mulOpposite_iff A)

/-- Reversing multiplication preserves von Neumann regularity. -/
instance mulOpposite [IsVonNeumannRegularRing A] : IsVonNeumannRegularRing Aᵐᵒᵖ :=
  mulOpposite_iff.mpr inferInstance

/-- The one-object category of a von Neumann regular ring is von Neumann regular. -/
instance singleObj [IsVonNeumannRegularRing A] : IsVonNeumannRegularCategory (SingleObj A) :=
  (isVonNeumannRegularCategory_singleObj_iff A).mpr inferInstance

/-- The Jacobson radical of a von Neumann regular ring is zero. -/
@[simp] theorem jacobson_eq_bot [IsVonNeumannRegularRing A] : Ring.jacobson A = ⊥ := by
  let X := SingleObj.star A
  let e : End X ≃+* A :=
    { End.addEquiv with
      map_mul' := fun f g ↦ SingleObj.comp_as_mul A g.asHom f.asHom }
  refine eq_bot_iff.mpr fun a ha ↦ (Submodule.mem_bot A).mpr ?_
  let : RingHomSurjective e.symm.toRingHom := ⟨e.symm.surjective⟩
  have ha' : e.symm a ∈ Ring.jacobson (End X) :=
    Ring.le_comap_jacobson (f := e.symm.toRingHom) ha
  have hr := mem_jacobsonRadical_self_iff_mem_jacobson.mpr ha'
  rw [IsVonNeumannRegularCategory.jacobsonRadical_eq_bot, AddSubgroup.mem_bot] at hr
  apply e.symm.injective
  rw [map_zero]
  apply End.ext
  simpa only [End.zero_asHom] using hr

end IsVonNeumannRegularRing

/-- A finitely generated left ideal in a von Neumann regular ring is generated by an idempotent. -/
theorem _root_.Ideal.exists_isIdempotentElem_span_singleton_eq_of_fg {A : Type*} [Ring A]
    [IsVonNeumannRegularRing A] (I : Ideal A) (hI : I.FG) :
    ∃ e : A, IsIdempotentElem e ∧ Ideal.span {e} = I := by
  obtain ⟨n, β, hβ⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hI
  let X := SingleObj.star A
  let b (j : Fin n) : X ⟶ X := β j
  obtain ⟨g, hg⟩ := IsVonNeumannRegularCategory.exists_sum_comp_comp_eq_self
    (Y := fun _ ↦ X) b
  let e : A := ∑ j, g j * β j
  have hfix (j : Fin n) : β j * e = β j := by
    simpa only [b, e, SingleObj.comp_as_mul] using hg j
  have he : IsIdempotentElem e := calc
    e * e = (∑ j, g j * β j) * e := rfl
    _ = ∑ j, g j * (β j * e) := by simp only [Finset.sum_mul, mul_assoc]
    _ = e := by simp only [hfix, e]
  refine ⟨e, he, le_antisymm ((Ideal.span_singleton_le_iff_mem I).mpr ?_) ?_⟩
  · exact I.sum_mem fun j _ ↦
      I.mul_mem_left (g j) (hβ ▸ Submodule.subset_span (Set.mem_range_self j))
  · rw [← hβ]
    exact Submodule.span_le.mpr fun _ ⟨j, hj⟩ ↦
      Ideal.mem_span_singleton'.mpr ⟨β j, (hfix j).trans hj⟩

/-- Boolean rings are von Neumann regular. -/
instance {A : Type*} [BooleanRing A] : IsVonNeumannRegularRing A := by
  apply (isVonNeumannRegularCategory_singleObj_iff A).mp
  constructor
  intro X Y f
  exact ⟨1, by simp only [SingleObj.comp_as_mul, mul_one, BooleanRing.mul_self]⟩

/-- Semisimple rings are von Neumann regular. -/
instance (priority := 100) {A : Type*} [Ring A] [IsSemisimpleRing A] :
    IsVonNeumannRegularRing A :=
  ⟨IsSemisimpleRing.exists_mul_mul_eq_self⟩

end TauCeti
