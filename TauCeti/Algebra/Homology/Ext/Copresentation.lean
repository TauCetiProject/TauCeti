/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Ext.Basic
public import TauCeti.CategoryTheory.Linear.HomCokernel.Basic
import Mathlib.Algebra.Exact.Basic

/-!
# Computing Ext¹ from an injective copresentation

For a short exact sequence `S : 0 → M → I₀ → I₁ → 0` with `I₀` injective, the Hom cokernel
`Hom(X, I₁) / im(Hom(X, I₀))` computes `Ext¹(X, M)`. A map to `I₁` represents the pullback
of the copresentation along that map. This is the covariant counterpart of
`TauCeti.homCokernelEquivExt`.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Abelian

universe u v w t

variable (R : Type t) [Ring R] {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]
  [HasExt.{w} C] {S : ShortComplex C} (hS : S.ShortExact) (X : C)

/-- The Hom connecting map into `Ext¹(X, S.X₁)` pulls back the extension class of `S`. -/
noncomputable def covariantHomBoundary : (X ⟶ S.X₃) →ₗ[R] Ext.{w} X S.X₁ 1 where
  toFun f := (Ext.mk₀ f).comp hS.extClass (zero_add 1)
  map_add' := by simp [Ext.mk₀_add]
  map_smul' := by simp [Ext.mk₀_smul]

/-- The Hom connecting map evaluates to the pullback extension class. -/
@[simp]
theorem covariantHomBoundary_apply (f : X ⟶ S.X₃) :
    covariantHomBoundary R hS X f = (Ext.mk₀ f).comp hS.extClass (zero_add 1) :=
  (rfl)

/-- The maps in the kernel of the Hom connecting map are exactly the maps lifting to `S.X₂`. -/
theorem ker_covariantHomBoundary :
    (covariantHomBoundary R hS X).ker = (Linear.rightComp R X S.g).range := by
  apply Function.Exact.linearMap_ker_eq
  let e₂ : (X ⟶ S.X₂) ≃+ Ext.{w} X S.X₂ 0 := Ext.addEquiv₀.symm
  let e₃ : (X ⟶ S.X₃) ≃+ Ext.{w} X S.X₃ 0 := Ext.addEquiv₀.symm
  refine (AddMonoidHom.exact_iff_of_surjective_of_bijective_of_injective
    (Linear.rightComp R X S.g).toAddMonoidHom (covariantHomBoundary R hS X).toAddMonoidHom
    ((Ext.mk₀ S.g).postcomp X (add_zero 0)) (hS.extClass.postcomp X (zero_add 1))
    e₂.toAddMonoidHom e₃.toAddMonoidHom (AddMonoidHom.id _)
    ?_ ?_ e₂.surjective e₃.bijective Function.injective_id).2
    (exact_postcomp₃ hS X 0 1 (zero_add 1))
  · ext f
    simp [e₂, e₃]
  · ext f
    simp [e₃]

/-- When the middle term is injective, every extension class is the pullback along a map. -/
theorem covariantHomBoundary_surjective [Injective S.X₂] :
    Function.Surjective (covariantHomBoundary R hS X) := by
  intro e
  obtain ⟨f, hf⟩ := Ext.covariant_sequence_exact₁ X hS e (Ext.eq_zero_of_injective _) (zero_add 1)
  exact ⟨Ext.linearEquiv₀ (R := R) f, by simpa using hf⟩

/-- The Hom cokernel of an injective copresentation computes `Ext¹`. -/
noncomputable def covariantHomCokernelEquivExt [Injective S.X₂] :
    CovariantHomCokernel R S.g X ≃ₗ[R] Ext.{w} X S.X₁ 1 :=
  (Submodule.quotEquivOfEq _ _ (ker_covariantHomBoundary R hS X).symm).trans
    ((covariantHomBoundary R hS X).quotKerEquivOfSurjective
      (covariantHomBoundary_surjective R hS X))

/-- Under the copresentation comparison, a map represents its pullback extension class. -/
@[simp]
theorem covariantHomCokernelEquivExt_mk [Injective S.X₂] (f : X ⟶ S.X₃) :
    covariantHomCokernelEquivExt R hS X (Submodule.Quotient.mk f) =
      (Ext.mk₀ f).comp hS.extClass (zero_add 1) := by
  simp [covariantHomCokernelEquivExt]

/-- Under the inverse comparison, a pullback extension is represented by its defining map. -/
@[simp]
theorem covariantHomCokernelEquivExt_symm_mk₀_comp [Injective S.X₂] (f : X ⟶ S.X₃) :
    (covariantHomCokernelEquivExt R hS X).symm
        ((Ext.mk₀ f).comp hS.extClass (zero_add 1)) = Submodule.Quotient.mk f := by
  rw [← covariantHomCokernelEquivExt_mk R hS X, LinearEquiv.symm_apply_apply]

/-- The Hom-cokernel computation of `Ext¹` is natural in the source object. -/
@[simp]
theorem covariantHomCokernelEquivExt_naturality [Injective S.X₂] {X' : C} (g : X' ⟶ X)
    (x : CovariantHomCokernel R S.g X) :
    covariantHomCokernelEquivExt R hS X' (CovariantHomCokernel.map R S.g g x) =
      (Ext.mk₀ g).comp (covariantHomCokernelEquivExt R hS X x) (zero_add 1) := by
  induction x using Submodule.Quotient.induction_on with
  | _ f => simp

end TauCeti
