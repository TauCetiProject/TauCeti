/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import Mathlib.Algebra.Homology.ShortComplex.Pullback
public import Mathlib.Algebra.Homology.ShortComplex.Pushout
public import TauCeti.Algebra.Homology.ShortComplex.ShortExact

/-!
# Baer sums and native extension classes

The Baer sum of two short exact sequences with common endpoints is formed by
pulling their componentwise direct sum back along the diagonal and pushing out
along the codiagonal. Its native `ShortComplex.ShortExact.extClass` is the sum of
the two extension classes. The construction reuses Mathlib's `ShortComplex.pull` and
`ShortComplex.push`, together with `TauCeti.shortComplexBiprod`; the comparison uses
`ShortComplex.ShortExact.extClass_naturality`. This identifies the geometric pullback and pushout
construction with addition in the derived-category definition of `Ext¹`.
-/

public section

namespace CategoryTheory.ShortComplex

open Limits Abelian

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The Baer sum of `S` and `S.X₁ ⟶ E ⟶ S.X₃`, formed by pulling the componentwise
sum back along the diagonal and then pushing out along the codiagonal.

The body is exposed because the literal endpoint and middle-object carriers are
needed when composing the canonical pullback and pushout maps. -/
@[expose, simps! X₁ X₂ f g]
noncomputable def baerSum (S : ShortComplex C) {E : C}
    (i : S.X₁ ⟶ E) (p : E ⟶ S.X₃) (w : i ≫ p = 0) : ShortComplex C :=
  ((TauCeti.shortComplexBiprod S (ShortComplex.mk i p w)).pull
    (biprod.lift (𝟙 _) (𝟙 _))).push (biprod.desc (𝟙 _) (𝟙 _))

/-- The Baer sum retains the common quotient object. -/
@[simp]
lemma baerSum_X₃ (S : ShortComplex C) {E : C}
    (i : S.X₁ ⟶ E) (p : E ⟶ S.X₃) (w : i ≫ p = 0) :
    (S.baerSum i p w).X₃ = S.X₃ := (rfl)

/-- The pullback and pushout defining a Baer sum preserve short exactness. -/
lemma ShortExact.baerSum {S : ShortComplex C} (hS : S.ShortExact)
    {E : C} {i : S.X₁ ⟶ E} {p : E ⟶ S.X₃} {w : i ≫ p = 0}
    (hT : (ShortComplex.mk i p w).ShortExact) : (S.baerSum i p w).ShortExact :=
  ((hS.biprod hT).pull (biprod.lift (𝟙 _) (𝟙 _))).push (biprod.desc (𝟙 _) (𝟙 _))

variable [HasExt.{w} C]

/-- Pullback of a short exact sequence pulls its extension class back in the first
variable of `Ext`. -/
@[simp]
lemma ShortExact.extClass_pull {S : ShortComplex C} (hS : S.ShortExact)
    {Y : C} (f : Y ⟶ S.X₃) :
    (hS.pull f).extClass = (Ext.mk₀ f).comp hS.extClass (zero_add 1) := by
  let φ : S.pull f ⟶ S :=
    ⟨𝟙 _, pullback.snd _ _, f, by simp, pullback.condition.symm⟩
  simpa only [φ, Ext.comp_mk₀_id] using (hS.pull f).extClass_naturality hS φ

/-- Pushout of a short exact sequence pushes its extension class forward in the
second variable of `Ext`. -/
@[simp]
lemma ShortExact.extClass_push {S : ShortComplex C} (hS : S.ShortExact)
    {Y : C} (f : S.X₁ ⟶ Y) :
    (hS.push f).extClass = hS.extClass.comp (Ext.mk₀ f) (add_zero 1) := by
  let φ : S ⟶ S.push f :=
    ⟨f, pushout.inl _ _, 𝟙 _, pushout.condition.symm, by simp⟩
  simpa only [φ, Ext.mk₀_id_comp] using (hS.extClass_naturality (hS.push f) φ).symm

/-- The extension class of a componentwise direct sum is block diagonal. -/
@[simp]
lemma ShortExact.extClass_biprod {S T : ShortComplex C}
    (hS : S.ShortExact) (hT : T.ShortExact) :
    (hS.biprod hT).extClass =
      (Ext.mk₀ biprod.fst).comp
          (hS.extClass.comp (Ext.mk₀ biprod.inl) (add_zero 1)) (zero_add 1) +
        (Ext.mk₀ biprod.snd).comp
          (hT.extClass.comp (Ext.mk₀ biprod.inr) (add_zero 1)) (zero_add 1) := by
  let ιS : S ⟶ TauCeti.shortComplexBiprod S T :=
    ⟨biprod.inl, biprod.inl, biprod.inl, biprod.inl_map _ _, biprod.inl_map _ _⟩
  let ιT : T ⟶ TauCeti.shortComplexBiprod S T :=
    ⟨biprod.inr, biprod.inr, biprod.inr, biprod.inr_map _ _, biprod.inr_map _ _⟩
  -- Normalize the component carriers before applying the dependent Ext API.
  dsimp only [TauCeti.shortComplexBiprod]
  apply Ext.biprod_ext
  · have h := hS.extClass_naturality (hS.biprod hT) ιS
    dsimp only [ιS, TauCeti.shortComplexBiprod] at h
    simpa using h.symm
  · have h := hT.extClass_naturality (hS.biprod hT) ιT
    dsimp only [ιT, TauCeti.shortComplexBiprod] at h
    simpa using h.symm

/-- The pullback and pushout Baer sum represents addition of the native extension
classes, in every abelian category with `HasExt`. -/
@[simp]
lemma ShortExact.extClass_baerSum {S : ShortComplex C} (hS : S.ShortExact)
    {E : C} {i : S.X₁ ⟶ E} {p : E ⟶ S.X₃} {w : i ≫ p = 0}
    (hT : (ShortComplex.mk i p w).ShortExact) :
    (hS.baerSum hT).extClass = hS.extClass + hT.extClass := by
  have hpush := ((hS.biprod hT).pull (biprod.lift (𝟙 _) (𝟙 _))).extClass_push
    (biprod.desc (𝟙 _) (𝟙 _))
  have hpull := (hS.biprod hT).extClass_pull (biprod.lift (𝟙 _) (𝟙 _))
  have hsum := hS.extClass_biprod hT
  -- Normalize the component and endpoint carriers in these dependent Ext equations.
  dsimp only [ShortComplex.baerSum, ShortComplex.pull, ShortComplex.push,
    TauCeti.shortComplexBiprod] at hpush hpull hsum ⊢
  rw [hpush, hpull, hsum]
  simp

end CategoryTheory.ShortComplex
