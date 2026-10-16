/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
import TauCeti.CategoryTheory.Exact.Abelian
import TauCeti.CategoryTheory.Exact.BaseChange

/-!
# Realizing Ext¹ by short exact sequences

Given a short exact sequence with projective middle term, every class in `Ext¹` out of
its final term is represented by a short exact sequence with the prescribed endpoints.
The middle term is obtained by pushing out the given presentation.

This uses Mathlib's `Ext.contravariant_sequence_exact₃` to express a class as a boundary,
and `ShortComplex.ShortExact.extClass_naturality` to identify the pushout class. In
particular, the result can turn extension classes with annihilation properties into
sequences with lifting properties.

## References

* Charles A. Weibel, *An Introduction to Homological Algebra*, Section 3.4.
-/

public section

namespace CategoryTheory.ShortComplex.ShortExact

open CategoryTheory.Abelian CategoryTheory.Limits TauCeti

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {S : ShortComplex C}

/-- Every degree-one extension class out of the last term of a projective presentation
has a short exact representative with exactly the specified endpoints. -/
theorem exists_extClass_eq (hS : S.ShortExact) [Projective S.X₂]
    (Y : C) (α : Ext.{w} S.X₃ Y 1) :
    ∃ (E : C) (i : Y ⟶ E) (p : E ⟶ S.X₃) (h : i ≫ p = 0)
      (hT : (ShortComplex.mk i p h).ShortExact), hT.extClass = α := by
  obtain ⟨x, hx⟩ := Ext.contravariant_sequence_exact₃ hS Y α (n₀ := 0)
    (Ext.eq_zero_of_projective _) rfl
  obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective S.X₁ Y).surjective x
  let sq := IsPushout.of_hasPushout S.f f
  have hT : (cobaseChange S sq).ShortExact :=
    (ExactStructure.abelian_conflation _).mp
      ((ExactStructure.abelian C).conflation_cobaseChange
        ((ExactStructure.abelian_conflation S).mpr hS) sq)
  rw [cobaseChange_def] at hT
  refine ⟨pushout S.f f, pushout.inr S.f f, cobaseChangeπ S sq, by simp, hT, ?_⟩
  let φ : S ⟶ ShortComplex.mk (pushout.inr S.f f) (cobaseChangeπ S sq) (by simp) :=
    ⟨f, pushout.inl S.f f, 𝟙 S.X₃, pushout.condition.symm, by simp⟩
  calc
    hT.extClass = hS.extClass.comp (Ext.mk₀ f) (add_zero 1) := by
      simpa only [φ, Ext.mk₀_id_comp] using (hS.extClass_naturality hT φ).symm
    _ = α := hx

end CategoryTheory.ShortComplex.ShortExact
