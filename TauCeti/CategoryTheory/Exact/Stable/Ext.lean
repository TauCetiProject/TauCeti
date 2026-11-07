/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Stable.Basic
public import TauCeti.CategoryTheory.Exact.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives

/-!
# `Ext` in positive degrees on the projective stable category

In an abelian category, a morphism factoring through a projective object induces zero on `Ext` in
positive degrees, since `Ext^{n+1}(P, Z) = 0` for projective `P`. So `Ext^{n+1}(-, Z)` only depends
on objects up to isomorphism in the projective stable category: if `X` and `Y` become isomorphic
there, then `Ext^{n+1}(X, Z)` vanishes exactly when `Ext^{n+1}(Y, Z)` does.

## Main results

* `TauCeti.ext_mk₀_comp_eq_zero_of_factorsThrough`: precomposition with a morphism factoring
  through a projective object is zero on `Ext` in positive degrees.
* `TauCeti.ext_eq_zero_of_projectiveStableFunctor_iso`: vanishing of `Ext^{n+1}(-, Z)` is
  invariant under isomorphism in the projective stable category.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Abelian

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- **Maps through projectives vanish on positive `Ext`**: if `f : X ⟶ Y` factors through a
projective object, then composing with `f` kills `Ext^{n+1}(Y, Z)`. -/
theorem ext_mk₀_comp_eq_zero_of_factorsThrough {X Y : C} {f : X ⟶ Y}
    (hf : (ExactStructure.abelian C).isProjective.FactorsThrough f) {Z : C} {n : ℕ}
    (x : Ext.{w} Y Z (n + 1)) : (Ext.mk₀ f).comp x (zero_add _) = 0 := by
  obtain ⟨Q, hQ, i, p, rfl⟩ := (ObjectProperty.factorsThrough_iff _ _).1 hf
  have := (ExactStructure.abelian_isProjective_iff Q).1 hQ
  rw [← Ext.mk₀_comp_mk₀_assoc, Ext.eq_zero_of_projective ((Ext.mk₀ p).comp x (zero_add _)),
    Ext.comp_zero]

/-- **`Ext` vanishing is a stable invariant**: if `X` and `Y` are isomorphic in the projective
stable category, then `Ext^{n+1}(X, Z) = 0` as soon as `Ext^{n+1}(Y, Z) = 0`. -/
theorem ext_eq_zero_of_projectiveStableFunctor_iso {X Y : C}
    (e : (ExactStructure.abelian C).projectiveStableFunctor.obj X ≅
      (ExactStructure.abelian C).projectiveStableFunctor.obj Y) {Z : C} {n : ℕ}
    (h : ∀ y : Ext.{w} Y Z (n + 1), y = 0) (x : Ext.{w} X Z (n + 1)) : x = 0 := by
  let S := (ExactStructure.abelian C).projectiveStableFunctor
  obtain ⟨f, hf⟩ := S.map_surjective e.hom
  obtain ⟨g, hg⟩ := S.map_surjective e.inv
  have hfg : S.map (f ≫ g) = S.map (𝟙 X) := by simp [S, hf, hg]
  rw [MorphismIdeal.quotientFunctor_map_eq_iff,
    ExactStructure.mem_projectiveStableIdeal_iff] at hfg
  have h₀ := ext_mk₀_comp_eq_zero_of_factorsThrough hfg x
  rw [sub_eq_add_neg, Ext.mk₀_add, Ext.add_comp, Ext.mk₀_neg, Ext.neg_comp, Ext.mk₀_id_comp,
    ← Ext.mk₀_comp_mk₀_assoc, h ((Ext.mk₀ g).comp x _), Ext.comp_zero, zero_add,
    neg_eq_zero] at h₀
  exact h₀

end TauCeti
