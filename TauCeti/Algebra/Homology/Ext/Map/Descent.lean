/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Ext.Coproduct
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Reduction criteria for descent of extensions

For an exact functor between abelian categories with enough injectives that preserves the
coproduct, surjectivity on degree-one extensions passes from the summands to the coproduct.
It also passes from the middle term of a short exact presentation to its quotient
when the functor is surjective on Hom from the kernel and injective on Ext¹ from that kernel.
Together these criteria reduce descent of extensions to a class of presenting objects.

## References

* The Stacks Project, Lemma 15.91.8 (05EG), for the reduction to cyclic presentations in
  formal glueing.
-/

public section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

universe u v u' v' w w' t

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  [HasExt.{w} C] [HasExt.{w'} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- Surjectivity of an exact functor on extensions passes from the summands to a coproduct
that the functor preserves. -/
theorem mapExt_one_surjective_of_coproduct [EnoughInjectives C] [EnoughInjectives D]
    {J : Type t} {X : J → C} {c : Cofan X} (hc : IsColimit c)
    [PreservesColimit (Discrete.functor X) F] (Y : C)
    (hX : ∀ i, Function.Surjective (F.mapExtAddHom.{w, w'} (X i) Y 1)) :
    Function.Surjective (F.mapExtAddHom.{w, w'} c.pt Y 1) := by
  let hc' := isColimitCofanMkObjOfIsColimit F X c.inj hc
  intro e
  choose a ha using fun i ↦ hX i ((Ext.coproductAddEquiv₁ hc' (F.obj Y) e) i)
  obtain ⟨b, hb⟩ := (Ext.coproductAddEquiv₁ hc Y).surjective a
  refine ⟨b, (Ext.coproductAddEquiv₁ hc' (F.obj Y)).injective ?_⟩
  ext i
  have hi := congrFun hb i
  simp only [Ext.coproductAddEquiv₁_apply] at hi
  simpa only [Ext.coproductAddEquiv₁_apply, cofan_mk_inj,
    mapExtAddHom_apply, ← Ext.mapExactFunctor_mk₀, ← Ext.mapExactFunctor_comp, hi] using ha i

/-- Descent of extensions passes to the quotient in a short exact presentation if Hom from
its kernel descends and degree-one extension classes from that kernel are detected. -/
theorem mapExt_one_surjective_of_shortExact {S : ShortComplex C} (hS : S.ShortExact) (Y : C)
    (hHom : Function.Surjective (F.map : (S.X₁ ⟶ Y) → _))
    (hKer : Function.Injective (F.mapExtAddHom.{w, w'} S.X₁ Y 1))
    (hMid : Function.Surjective (F.mapExtAddHom.{w, w'} S.X₂ Y 1)) :
    Function.Surjective (F.mapExtAddHom.{w, w'} S.X₃ Y 1) := by
  intro e
  obtain ⟨a, ha⟩ := hMid ((Ext.mk₀ (F.map S.g)).comp e (zero_add 1))
  have hzero : (Ext.mk₀ S.f).comp a (zero_add 1) = 0 := by
    apply hKer
    simp only [mapExtAddHom_apply] at ha
    simp [mapExtAddHom_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
      ha, ← F.map_comp]
  obtain ⟨b, hb⟩ := Ext.contravariant_sequence_exact₂ hS Y a hzero
  have hdiff : (Ext.mk₀ (F.map S.g)).comp (e - F.mapExtAddHom S.X₃ Y 1 b) (zero_add 1) = 0 := by
    have hmap := congrArg (F.mapExtAddHom S.X₂ Y 1) hb
    simpa [sub_eq_add_neg, ha, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀] using
      sub_eq_zero.mpr hmap.symm
  obtain ⟨d, hd⟩ := Ext.contravariant_sequence_exact₃ (hS.map_of_exact F) (F.obj Y)
    (e - F.mapExtAddHom S.X₃ Y 1 b) hdiff (n₀ := 0) rfl
  obtain ⟨d, rfl⟩ := (Ext.mk₀_bijective _ _).2 d
  obtain ⟨q, hq⟩ := hHom d
  refine ⟨b + hS.extClass.comp (Ext.mk₀ q) (add_zero 1), ?_⟩
  simp only [AddMonoidHom.map_add, mapExtAddHom_apply, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_extClass, Ext.mapExactFunctor_mk₀, hq]
  rw [hd]
  simp only [mapExtAddHom_apply]
  abel

end CategoryTheory.Functor
