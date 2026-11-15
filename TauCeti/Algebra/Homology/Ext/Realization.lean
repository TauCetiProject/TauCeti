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

A pair of maps on the endpoints of two short exact sequences extends to a map of
sequences exactly when it respects their extension classes. In particular, equal
extension classes give isomorphic sequences with the identity on both endpoints.

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

/-- Maps on the endpoints extend to a morphism of short exact sequences if and only if
they respect the associated degree-one extension classes. -/
theorem exists_hom_iff_extClass_comp_eq {T : ShortComplex C}
    (hS : S.ShortExact) (hT : T.ShortExact) (a : S.X₁ ⟶ T.X₁) (c : S.X₃ ⟶ T.X₃) :
    (∃ φ : S ⟶ T, φ.τ₁ = a ∧ φ.τ₃ = c) ↔
      hS.extClass.comp (Ext.mk₀ a) (add_zero 1) =
        (Ext.mk₀ c).comp hT.extClass (zero_add 1) := by
  constructor
  · rintro ⟨φ, rfl, rfl⟩
    exact hS.extClass_naturality hT φ
  · intro h
    let := HasDerivedCategory.standard C
    have hδ : hS.singleδ ≫ ((DerivedCategory.singleFunctor C 0).map a)⟦(1 : ℤ)⟧' =
        (DerivedCategory.singleFunctor C 0).map c ≫ hT.singleδ := by
      simpa only [Ext.comp_hom, Ext.mk₀_hom, extClass_hom,
        CategoryTheory.ShiftedHom.comp_mk₀, CategoryTheory.ShiftedHom.mk₀_comp] using!
          congrArg Ext.hom h
    obtain ⟨b, hb₁, hb₂⟩ := Pretriangulated.complete_distinguished_triangle_morphism₂
      hS.singleTriangle hT.singleTriangle hS.singleTriangle_distinguished
      hT.singleTriangle_distinguished ((DerivedCategory.singleFunctor C 0).map a)
      ((DerivedCategory.singleFunctor C 0).map c) hδ
    let b₀ := (DerivedCategory.singleFunctor C 0).preimage b
    have hb₀ : (DerivedCategory.singleFunctor C 0).map b₀ = b :=
      Functor.map_preimage _ _
    refine ⟨⟨a, b₀, c, ?_, ?_⟩, rfl, rfl⟩
    · apply (DerivedCategory.singleFunctor C 0).map_injective
      simpa only [Functor.map_comp, hb₀, singleTriangle_mor₁] using hb₁.symm
    · apply (DerivedCategory.singleFunctor C 0).map_injective
      simpa only [Functor.map_comp, hb₀, singleTriangle_mor₂] using hb₂.symm

/-- Isomorphisms on the endpoints extend to an isomorphism of short exact sequences if
and only if they respect the associated degree-one extension classes. -/
theorem exists_iso_iff_extClass_comp_eq {T : ShortComplex C}
    (hS : S.ShortExact) (hT : T.ShortExact) (a : S.X₁ ≅ T.X₁) (c : S.X₃ ≅ T.X₃) :
    (∃ e : S ≅ T, e.hom.τ₁ = a.hom ∧ e.hom.τ₃ = c.hom) ↔
      hS.extClass.comp (Ext.mk₀ a.hom) (add_zero 1) =
        (Ext.mk₀ c.hom).comp hT.extClass (zero_add 1) := by
  constructor
  · rintro ⟨e, h₁, h₃⟩
    exact (hS.exists_hom_iff_extClass_comp_eq hT a.hom c.hom).mp ⟨e.hom, h₁, h₃⟩
  · intro h
    obtain ⟨φ, h₁, h₃⟩ := (hS.exists_hom_iff_extClass_comp_eq hT a.hom c.hom).mpr h
    have : IsIso φ.τ₁ := h₁ ▸ inferInstance
    have : IsIso φ.τ₃ := h₃ ▸ inferInstance
    have : IsIso φ.τ₂ := ShortComplex.isIso₂_of_shortExact_of_isIso₁₃ φ hS hT
    have : IsIso φ := ShortComplex.isIso_of_isIso φ
    exact ⟨asIso φ, h₁, h₃⟩

end CategoryTheory.ShortComplex.ShortExact
