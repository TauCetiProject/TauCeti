/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.CategoryTheory.ObjectProperty.EpiMono
public import Mathlib.RingTheory.Length
public import TauCeti.CategoryTheory.Abelian.Length
import Mathlib.Algebra.Category.ModuleCat.Subobject
import TauCeti.Algebra.Category.ModuleCat.Length
import TauCeti.CategoryTheory.Subobject.FullSubcategory

/-!
# The length of a finitely generated module as an object of `FGModuleCat`

The length `CategoryTheory.length X` of a finitely generated module `X` as an object of
`FGModuleCat A` is its length as a module (`FGModuleCat.length_eq`), over any ring `A`. Over a left
Noetherian ring, submodules of finitely generated modules are finitely generated, so the finitely
generated modules are closed under subobjects in `ModuleCat A`
(`ModuleCat.isFG_isClosedUnderSubobjects`).

## Main results

* `FGModuleCat.preservesMonomorphisms_ι`: a monomorphism of `FGModuleCat A` is injective.
* `ModuleCat.isFG_isClosedUnderSubobjects`: over a left Noetherian ring, finitely generated modules
  are closed under subobjects.
* `FGModuleCat.length_eq`: `CategoryTheory.length X = Module.length A X.obj`.

## Implementation notes

A monomorphism `f` of `FGModuleCat A` is injective: an element of its kernel spans a cyclic, hence
finitely generated, submodule whose inclusion `f` kills. So the subobjects of `X` in
`FGModuleCat A` embed into the submodules of `X.obj`
(`CategoryTheory.ObjectProperty.subobjectOrderEmbedding`), giving
`length X ≤ Module.length A X.obj`, and every finitely generated submodule is in the image.
If `X.obj` is Noetherian, all its submodules are finitely generated, so the two lengths agree.
Otherwise the finitely generated submodules contain a strictly increasing sequence
(`isNoetherian_iff_fg_wellFounded`), so both lengths are infinite.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Chapter VI, Section 1.
-/

public section

open CategoryTheory

universe w v

variable {A : Type v} [Ring A]

/-- **A monomorphism of finitely generated modules is injective**: the inclusion
`FGModuleCat A ⥤ ModuleCat A` preserves monomorphisms, over any ring `A`. -/
instance FGModuleCat.preservesMonomorphisms_ι :
    (ModuleCat.isFG.{w} A).ι.PreservesMonomorphisms where
  preserves {X Y} f _ := by
    refine (ModuleCat.mono_iff_injective _).2 ((injective_iff_map_eq_zero _).2 fun x hx ↦ ?_)
    let N := Submodule.span A {x}
    let Z : FGModuleCat.{w} A :=
      ⟨ModuleCat.of A N, Module.Finite.iff_fg.2 (Submodule.fg_span_singleton x)⟩
    have h : (ObjectProperty.homMk (ModuleCat.ofHom N.subtype) : Z ⟶ X) =
        ObjectProperty.homMk 0 := by
      refine (cancel_mono f).1 (ObjectProperty.hom_ext _ (ModuleCat.hom_ext (LinearMap.ext ?_)))
      intro y
      simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom,
        ModuleCat.hom_comp, ConcreteCategory.hom_ofHom, LinearMap.coe_comp, Function.comp_apply,
        ObjectProperty.homMk_zero, Limits.zero_comp, ObjectProperty.zero_hom, ModuleCat.hom_zero,
        LinearMap.zero_apply]
      -- `N.subtype y` is `y`, and `ConcreteCategory.hom` of a morphism of modules is its
      -- underlying linear map, both definitionally.
      exact LinearMap.mem_ker.1
        ((Submodule.span_singleton_le_iff_mem _ _).2 (LinearMap.mem_ker.2 hx) y.property)
    simpa [Z] using congr_arg (fun g ↦ g.hom.hom ⟨x, Submodule.mem_span_singleton_self x⟩) h

/-- **Over a left Noetherian ring, finitely generated modules are closed under subobjects**: a
submodule of a finitely generated module is finitely generated. -/
instance ModuleCat.isFG_isClosedUnderSubobjects [IsNoetherianRing A] :
    (ModuleCat.isFG.{w} A).IsClosedUnderSubobjects where
  prop_of_mono f _ hY := by
    rw [ModuleCat.isFG_iff] at hY ⊢
    exact Module.Finite.of_injective f.hom ((ModuleCat.mono_iff_injective f).1 inferInstance)

/-- **The length of a finitely generated module as an object of `FGModuleCat A`** is its length as
a module, over any ring `A`. -/
theorem FGModuleCat.length_eq (X : FGModuleCat.{w} A) : length X = Module.length A X.obj := by
  let e := (ModuleCat.isFG.{w} A).subobjectOrderEmbedding X
  -- The finitely generated submodules of `X.obj`, as subobjects of `X`.
  let φ (N : {N : Submodule A X.obj // N.FG}) : Subobject X :=
    Subobject.mk (ObjectProperty.homMk (ModuleCat.ofHom N.val.subtype) :
      (⟨ModuleCat.of A N.val, Module.Finite.iff_fg.2 N.property⟩ : FGModuleCat.{w} A) ⟶ X)
  have hφ : StrictMono φ := fun N N' h ↦ by
    rw [← e.lt_iff_lt, ObjectProperty.subobjectOrderEmbedding_mk,
      ObjectProperty.subobjectOrderEmbedding_mk]
    exact (ModuleCat.subobjectModule X.obj).symm.strictMono h
  rw [← ModuleCat.length_eq, ← WithBot.coe_inj]
  refine le_antisymm (by
    rw [coe_length, coe_length]; exact Order.krullDim_le_of_strictMono _ e.strictMono) ?_
  rw [coe_length, coe_length,
    ← Order.krullDim_eq_of_orderIso (ModuleCat.subobjectModule X.obj).symm]
  by_cases hX : IsNoetherian A X.obj
  · exact Order.krullDim_le_of_strictMono (fun N ↦ φ ⟨N, IsNoetherian.noetherian N⟩)
      fun _ _ h ↦ hφ h
  · rw [isNoetherian_iff_fg_wellFounded, WellFoundedGT,
      RelEmbedding.wellFounded_iff_isEmpty, not_isEmpty_iff] at hX
    obtain ⟨f⟩ := hX
    exact le_top.trans (Order.krullDim_nat ▸ Order.krullDim_le_of_strictMono _
      (hφ.comp fun _ _ h ↦ f.map_rel_iff.2 h))
