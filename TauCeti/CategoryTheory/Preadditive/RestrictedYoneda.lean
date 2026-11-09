/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import TauCeti.Algebra.Homology.ShortComplex.ShortExact
public import TauCeti.CategoryTheory.ObjectProperty.Presented
public import TauCeti.CategoryTheory.Preadditive.Yoneda

/-!
# The restricted Yoneda functor on presentations by projective objects

Let `P` be a property of objects of `C` satisfied only by projective objects, and consider the
functor `X ↦ (-, X)|_P`, `P.restrictedPreadditiveYoneda : C ⥤ P.FullSubcategoryᵒᵖ ⥤ AddCommGrpCat`.
It is fully faithful on morphisms out of an object with a presentation by objects of `P`. When `C`
is abelian, `Hom(Q, -)` is exact for `Q` projective, so the functor preserves exactness of short
complexes and sends a presentation `A ⟶ B ⟶ X ⟶ 0` of `X` by objects of `P` to a presentation
`(-, A) ⟶ (-, B) ⟶ (-, X)|_P ⟶ 0` by representable functors.

## Main declarations

* `CategoryTheory.ObjectProperty.bijective_restrictedPreadditiveYoneda_map`: the functor
  `X ↦ (-, X)|_P` is fully faithful on morphisms out of a `P`-presented object.
* `CategoryTheory.ObjectProperty.exact_map_restrictedPreadditiveYoneda`: restriction to projective
  objects preserves exactness of short complexes.
* `CategoryTheory.ObjectProperty.isColimitRestrictedPreadditiveYoneda`: a presentation by objects of
  `P` gives a presentation of `(-, X)|_P` by representable functors on `P`.
-/

public section

universe v u

open CategoryTheory Limits Opposite

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C] {P : ObjectProperty C}

section Preadditive

variable [Preadditive C]

/-- The functor `X ↦ (-, X)|_P` is fully faithful on morphisms out of a `P`-presented object: a
natural transformation `θ : (-, X)|_P ⟶ (-, Y)|_P` is `(-, g)` for the unique `g : X ⟶ Y` extending
`θ π : B ⟶ Y` along the epimorphism `π : B ⟶ X`, where `B` is an object of `P`. -/
theorem bijective_restrictedPreadditiveYoneda_map (hP : P ≤ isProjective C) {X : C}
    (hX : P.presented X) (Y : C) :
    Function.Bijective (P.restrictedPreadditiveYoneda.map : (X ⟶ Y) → _) := by
  obtain ⟨f, c, hc, hA, hB⟩ := hX
  have : Epi c.π := Cofork.IsColimit.epi hc
  let B : P.FullSubcategory := ⟨_, hB⟩
  constructor
  · intro g g' h
    rw [← cancel_epi c.π]
    exact congr($(h).app (op B) (c.π : B.obj ⟶ c.pt))
  · intro θ
    let t : B.obj ⟶ Y := θ.app (op B) c.π
    -- Naturality of `θ` says that `θ (u ≫ π) = u ≫ θ π` for `u` between objects of `P`.
    have hnat (Q : P.FullSubcategory) (u : Q.obj ⟶ B.obj) :
        θ.app (op Q) (u ≫ c.π) = u ≫ t :=
      NatTrans.naturality_apply θ (P.homMk u : Q ⟶ B).op (c.π : B.obj ⟶ c.pt)
    have hf : f ≫ t = 0 := by
      rw [← hnat ⟨_, hA⟩ f, CokernelCofork.condition]
      exact map_zero (θ.app (op ⟨_, hA⟩)).hom
    obtain ⟨g, hg⟩ := CokernelCofork.IsColimit.desc' hc t hf
    refine ⟨g, ?_⟩
    ext Q (u : Q.unop.obj ⟶ c.pt)
    have : Projective Q.unop.obj := hP _ Q.unop.property
    obtain ⟨v, rfl⟩ : ∃ v, v ≫ c.π = u :=
      ⟨_, Projective.factorThru_comp (P := Q.unop.obj) u c.π⟩
    simpa [hg] using (hnat Q.unop v).symm

end Preadditive

section Abelian

variable [Abelian C]

/-- Restriction to projective objects preserves exactness of short complexes. -/
theorem exact_map_restrictedPreadditiveYoneda (hP : P ≤ isProjective C) {S : ShortComplex C}
    (hS : S.Exact) : (S.map P.restrictedPreadditiveYoneda).Exact := by
  refine ShortComplex.exact_of_forall_evaluation _ fun Q ↦ ?_
  rw [ShortComplex.ab_exact_iff]
  intro (v : Q.unop.obj ⟶ S.X₂) hv
  have : Projective Q.unop.obj := hP _ Q.unop.property
  exact ⟨hS.liftFromProjective (P := Q.unop.obj) v hv,
    hS.liftFromProjective_comp (P := Q.unop.obj) v hv⟩

/-- A presentation `A ⟶ B ⟶ X ⟶ 0` by objects of `P`, which are projective, gives a presentation
`(-, A) ⟶ (-, B) ⟶ (-, X)|_P ⟶ 0` of `(-, X)|_P` by representable functors on `P`. -/
noncomputable def isColimitRestrictedPreadditiveYoneda (hP : P ≤ isProjective C)
    {A B : P.FullSubcategory} (f : A ⟶ B) {X : C} {π : B.obj ⟶ X} {w : f.hom ≫ π = 0}
    (hc : IsColimit (CokernelCofork.ofπ π w)) :
    IsColimit (CokernelCofork.ofπ (f := preadditiveYoneda.map f)
      (P.preadditiveYonedaIsoRestricted.hom.app B ≫ P.restrictedPreadditiveYoneda.map π) (by
        rw [reassoc_of% P.preadditiveYoneda_map_comp_preadditiveYonedaIsoRestricted_hom f,
          ← Functor.map_comp, w, Functor.map_zero, comp_zero])) := by
  have : Epi π := Cofork.IsColimit.epi hc
  let S : ShortComplex C := .mk f.hom π w
  have : Epi (S.map P.restrictedPreadditiveYoneda).g := epi_map_restrictedPreadditiveYoneda hP π
  have hS := exact_map_restrictedPreadditiveYoneda hP (ShortComplex.exact_of_g_is_cokernel S hc)
  refine CokernelCofork.isColimitOfIsColimitOfIff hS.gIsCokernel _
    (P.preadditiveYonedaIsoRestricted.app B) fun W φ ↦ ?_
  rw [Iso.app_hom, reassoc_of% P.preadditiveYoneda_map_comp_preadditiveYonedaIsoRestricted_hom f]
  exact (Preadditive.IsIso.comp_left_eq_zero _ _).symm

end Abelian

end CategoryTheory.ObjectProperty
