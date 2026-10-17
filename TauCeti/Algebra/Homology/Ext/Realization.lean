/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Ext.Presentation
import TauCeti.CategoryTheory.Exact.Abelian

/-!
# Realizing Ext¹ by short exact sequences

Given a short exact sequence with projective middle term, every class in `Ext¹` out of
its final term is represented by a short exact sequence with the prescribed endpoints.
The middle term is obtained by pushing out the given presentation.

This uses `TauCeti.homBoundary_surjective` to express a class as a boundary,
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
  obtain ⟨f, rfl⟩ := homBoundary_surjective ℤ hS Y α
  let sq := IsPushout.of_hasPushout S.f f
  have hT := shortExact_cobaseChange hS sq
  refine ⟨pushout S.f f, pushout.inr S.f f, cobaseChangeπ S sq, by simp, hT, ?_⟩
  let φ : S ⟶ ShortComplex.mk (pushout.inr S.f f) (cobaseChangeπ S sq) (by simp) :=
    ⟨f, pushout.inl S.f f, 𝟙 S.X₃, pushout.condition.symm, by simp⟩
  calc
    hT.extClass = hS.extClass.comp (Ext.mk₀ f) (add_zero 1) := by
      simpa only [φ, Ext.mk₀_id_comp] using (hS.extClass_naturality hT φ).symm
    _ = homBoundary ℤ hS Y f := (homBoundary_apply ℤ hS Y f).symm

end CategoryTheory.ShortComplex.ShortExact
