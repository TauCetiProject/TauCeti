/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Exactness in functor categories

A short complex of functors into an abelian category is exact if and only if its
value at each object is exact. This allows sectionwise exact sequences of
presheaves to be sheafified using exactness of sheafification.

Additive functors are stable under extensions: when the source category has binary biproducts,
the middle term of an exact sequence `F' ⟶ F ⟶ F''` with `F'` and `F''` additive is additive.
-/

public section

open CategoryTheory.Limits

namespace CategoryTheory.ShortComplex

variable {J C : Type*} [Category* J] [Category* C] [Abelian C]

/-- Exactness of a short complex in an abelian functor category is objectwise. -/
lemma exact_iff_evaluation (S : ShortComplex (J ⥤ C)) :
    S.Exact ↔ ∀ j, (S.map ((evaluation J C).obj j)).Exact := by
  have h : JointlyFaithful (fun j ↦ (evaluation J C).obj j) :=
    ⟨fun h ↦ NatTrans.ext (funext h)⟩
  exact h.jointlyReflectsIsomorphisms.exact_iff S

/-- The middle term of an exact sequence `F' ⟶ F ⟶ F''` of functors into an abelian category is
additive when `F'` and `F''` are, provided the source category has binary biproducts. -/
theorem Exact.additive_X₂ [Preadditive J] [HasBinaryBiproducts J] {S : ShortComplex (J ⥤ C)}
    (hS : S.Exact) [S.X₁.Additive] [S.X₃.Additive] : S.X₂.Additive := by
  -- An endomorphism `x` of `F j` killed by `g` is zero as soon as it is killed by some `t` fixing
  -- the image of `f`: up to a refinement, `x` factors through `f`, so `x = x ≫ t`.
  have key {j : J} (x t : S.X₂.obj j ⟶ S.X₂.obj j) (hx : x ≫ S.g.app j = 0)
      (ht : S.f.app j ≫ t = S.f.app j) (hxt : x ≫ t = 0) : x = 0 := by
    obtain ⟨A, π, _, c, hc⟩ := ((exact_iff_evaluation S).1 hS j).exact_up_to_refinements x hx
    dsimp at c hc
    have h : π ≫ x = π ≫ x ≫ t := by simp [hc, reassoc_of% hc, ht]
    rw [← cancel_epi π, h, hxt]
  -- `F` kills the zero endomorphism of `j`, taking `t = 𝟙 - F(0)`.
  have hzero (j : J) : S.X₂.map (0 : j ⟶ j) = 0 := by
    refine key _ (𝟙 _ - S.X₂.map 0) ?_ ?_ ?_
    · simp
    · simp [Preadditive.comp_sub, ← S.f.naturality]
    · simp [Preadditive.comp_sub, ← Functor.map_comp]
  -- `F` respects the decomposition of the identity of `j ⊞ k` into the two complementary
  -- idempotents `p₁` and `p₂`, taking `t = F(p₁) + F(p₂)`.
  have hsum (j k : J) : S.X₂.map (𝟙 (j ⊞ k)) =
      S.X₂.map (biprod.fst ≫ biprod.inl) + S.X₂.map (biprod.snd ≫ biprod.inr) := by
    have h₀ (j k : J) : S.X₂.map (0 : j ⟶ k) = 0 := by
      rw [← comp_zero (f := (0 : j ⟶ j)), S.X₂.map_comp, hzero, zero_comp]
    refine sub_eq_zero.1 (key _ (S.X₂.map (biprod.fst ≫ biprod.inl) +
      S.X₂.map (biprod.snd ≫ biprod.inr)) ?_ ?_ ?_)
    · simp only [Preadditive.sub_comp, Preadditive.add_comp, S.g.naturality, ← Preadditive.comp_add,
        ← Functor.map_add, biprod.total, sub_self]
    · simp only [Preadditive.comp_add, ← S.f.naturality, ← Preadditive.add_comp, ← Functor.map_add,
        biprod.total, Functor.map_id, Category.id_comp]
    · simp [Preadditive.sub_comp, Preadditive.add_comp, Preadditive.comp_add, ← Functor.map_comp,
        h₀]
  have hmap {j k : J} {a b : j ⟶ k} : S.X₂.map (a + b) = S.X₂.map a + S.X₂.map b := by
    have h : a + b = biprod.lift (𝟙 j) (𝟙 j) ≫ 𝟙 _ ≫ biprod.desc a b := by simp
    rw [h, S.X₂.map_comp, S.X₂.map_comp, hsum]
    simp [Preadditive.add_comp, Preadditive.comp_add, ← Functor.map_comp]
  exact ⟨hmap⟩

end CategoryTheory.ShortComplex
