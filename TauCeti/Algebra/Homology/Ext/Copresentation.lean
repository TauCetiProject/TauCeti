/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Ext.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives

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
noncomputable def homCoboundary : (X ⟶ S.X₃) →ₗ[R] Ext.{w} X S.X₁ 1 where
  toFun f := (Ext.mk₀ f).comp hS.extClass (zero_add 1)
  map_add' := by simp [Ext.mk₀_add]
  map_smul' := by simp [Ext.mk₀_smul]

/-- The Hom connecting map evaluates to the pullback extension class. -/
@[simp]
theorem homCoboundary_apply (f : X ⟶ S.X₃) :
    homCoboundary R hS X f = (Ext.mk₀ f).comp hS.extClass (zero_add 1) :=
  (rfl)

/-- The maps in the kernel of the Hom connecting map are exactly the maps lifting to `S.X₂`. -/
theorem ker_homCoboundary :
    (homCoboundary R hS X).ker = (Linear.rightComp R X S.g).range := by
  ext f
  simp only [LinearMap.mem_ker, homCoboundary_apply, LinearMap.mem_range, Linear.rightComp_apply]
  constructor
  · intro hf
    obtain ⟨g, hg⟩ := Ext.covariant_sequence_exact₃ X hS (Ext.mk₀ f) (zero_add 1) hf
    refine ⟨Ext.linearEquiv₀ (R := R) g, ?_⟩
    apply (Ext.mk₀_bijective _ _).1
    rwa [← Ext.mk₀_comp_mk₀, Ext.mk₀_linearEquiv₀_apply]
  · rintro ⟨g, rfl⟩
    rw [← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass, Ext.comp_zero]

/-- When the middle term is injective, every extension class is the pullback along a map. -/
theorem homCoboundary_surjective [Injective S.X₂] :
    Function.Surjective (homCoboundary R hS X) := by
  intro e
  obtain ⟨f, hf⟩ := Ext.covariant_sequence_exact₁ X hS e (Ext.eq_zero_of_injective _) (zero_add 1)
  exact ⟨Ext.linearEquiv₀ (R := R) f, by simpa using hf⟩

/-- The Hom cokernel of an injective copresentation computes `Ext¹`. -/
noncomputable def homCokernelEquivExtOfInjective [Injective S.X₂] :
    ((X ⟶ S.X₃) ⧸ (Linear.rightComp R X S.g).range) ≃ₗ[R] Ext.{w} X S.X₁ 1 :=
  (Submodule.quotEquivOfEq _ _ (ker_homCoboundary R hS X).symm).trans
    ((homCoboundary R hS X).quotKerEquivOfSurjective (homCoboundary_surjective R hS X))

/-- Under the copresentation comparison, a map represents its pullback extension class. -/
@[simp]
theorem homCokernelEquivExtOfInjective_mk [Injective S.X₂] (f : X ⟶ S.X₃) :
    homCokernelEquivExtOfInjective R hS X (Submodule.Quotient.mk f) =
      (Ext.mk₀ f).comp hS.extClass (zero_add 1) := by
  simp [homCokernelEquivExtOfInjective]

end TauCeti
