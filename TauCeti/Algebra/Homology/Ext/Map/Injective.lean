/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import TauCeti.Algebra.Homology.Ext.Realization

/-!
# Detecting degree-one extension classes by an exact functor

An exact functor is injective on extensions out of `X` if maps out of `F(X)` lift
and the functor is injective on endomorphisms of `X`. A splitting of the image of an
extension then descends to a splitting of the original extension.

This criterion only asks for fullness on maps with source `X`, not on the whole
category. In particular, it applies to scalar extension on ideal-power torsion modules.
-/

public section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

universe u v u' v' w w'

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughProjectives C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  [HasExt.{w} C] [HasExt.{w'} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- An exact functor detects degree-one extension classes out of `X` if every map
`F(X) → F(E)` lifts to `X → E` and the functor is injective on endomorphisms of `X`. -/
theorem mapExt_one_injective_of_map_surjective (X Y : C)
    (hsurj : ∀ E : C, Function.Surjective (F.map : (X ⟶ E) → _))
    (hinj : Function.Injective (F.map : (X ⟶ X) → _)) :
    Function.Injective (F.mapExtAddHom.{w, w'} X Y 1) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro α hα
  -- Realize the extension using a projective presentation of `X`.
  let P := Classical.choice (EnoughProjectives.presentation X)
  have hP : (ShortComplex.mk (kernel.ι P.f) P.f (kernel.condition P.f)).ShortExact :=
    ShortComplex.ShortExact.mk (ShortComplex.exact_kernel P.f)
  obtain ⟨E, i, p, hip, hT, rfl⟩ := hP.exists_extClass_eq Y α
  rw [mapExtAddHom_apply, Ext.mapExactFunctor_extClass] at hα
  -- Vanishing of the image class gives a section of the image epimorphism.
  obtain ⟨s, hs⟩ := Ext.covariant_sequence_exact₃ (F.obj X) (hT.map_of_exact F)
    (Ext.mk₀ (𝟙 (F.obj X))) (n₁ := 1) rfl (by simpa using hα)
  obtain ⟨s, rfl⟩ := (Ext.mk₀_bijective _ _).2 s
  have hs' : s ≫ F.map p = 𝟙 (F.obj X) := by
    apply (Ext.mk₀_bijective _ _).1
    simpa using hs
  obtain ⟨t, ht⟩ := hsurj E s
  have ht' : t ≫ p = 𝟙 X := hinj (by simp [ht, hs'])
  calc
    hT.extClass = (Ext.mk₀ (t ≫ p)).comp hT.extClass (zero_add 1) := by simp [ht']
    _ = 0 := by
      rw [← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_second_deg_zero,
        hT.comp_extClass, Ext.comp_zero]

end CategoryTheory.Functor
