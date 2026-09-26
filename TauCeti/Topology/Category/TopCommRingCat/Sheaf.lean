/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Topology.Category.TopCommRingCat

/-!
# Sheaves of topological rings from sheaves of sets

A presheaf `F` of topological commutative rings on a site is a sheaf as soon as its underlying
presheaf of sets is a sheaf and, for every covering sieve `S` on `X`, the map sending `x ∈ F(X)`
to its family of restrictions along the arrows of `S` is inducing for the product topology. The
topological half of the sheaf condition is thereby reduced to one statement about the topology of
each `F(X)`.

For a presheaf with values in a full subcategory of `TopCommRingCat`, such as the complete
separated rings in which the adic structure presheaf takes its values, the sheaf property descends
along the inclusion by `CategoryTheory.Presheaf.isSheaf_of_isSheaf_comp`, since a fully faithful
functor reflects limits.

## Main results

* `TauCeti.TopCommRingCat.isSheafFor_of_isSheafFor_forget`: the sheaf condition for a single
  sieve, tested against every topological commutative ring.
* `TauCeti.TopCommRingCat.isSheaf_of_isSheaf_forget`: the sheaf property for a Grothendieck
  topology.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Remark 8.20, which
  characterises sheaves of topological rings on a topological space by the sheaf condition on
  rings together with topological embeddings into products. `isSheaf_of_isSheaf_forget` is the
  sufficient direction, for presheaves on an arbitrary site.
-/

public section

open CategoryTheory Opposite

universe u w v

namespace TauCeti.TopCommRingCat

variable {C : Type u} [Category.{w} C] (F : Cᵒᵖ ⥤ _root_.TopCommRingCat.{v})

private theorem exists_isAmalgamation_of_isSheafFor_forget {X : C} {S : Sieve X}
    {E : _root_.TopCommRingCat.{v}}
    (hS : Presieve.IsSheafFor (F ⋙ forget _root_.TopCommRingCat) S.arrows)
    (hind : Topology.IsInducing fun (x : F.obj (op X)) (g : (Y : C) × { f : Y ⟶ X // S f }) ↦
      (F.map g.2.1.op).1 x) (φ : Presieve.FamilyOfElements (F ⋙ coyoneda.obj (op E)) S.arrows)
    (hφ : φ.Compatible) : ∃ t, φ.IsAmalgamation t := by
  -- Evaluating the family at `e : E` gives a compatible family of elements of the underlying
  -- presheaf of sets, which `hS` glues to `a e`.
  let ψ (e : E) : Presieve.FamilyOfElements (F ⋙ forget _root_.TopCommRingCat) S.arrows :=
    fun _ f hf ↦ (φ f hf).1 e
  have hψ (e : E) : (ψ e).Compatible := fun _ _ _ g₁ g₂ _ _ h₁ h₂ w ↦
    ConcreteCategory.congr_hom (hφ g₁ g₂ h₁ h₂ w) e
  let a (e : E) : F.obj (op X) := hS.amalgamate (ψ e) (hψ e)
  have ha (e : E) {Y : C} (f : Y ⟶ X) (hf : S f) : (F.map f.op).1 (a e) = (φ f hf).1 e :=
    hS.valid_glue (hψ e) f hf
  have hsep {x y : F.obj (op X)}
      (h : ∀ ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f → (F.map f.op).1 x = (F.map f.op).1 y) : x = y :=
    hS.isSeparatedFor.ext h
  -- The restriction maps are ring homs, so both sides of each ring-hom identity for `a` have the
  -- same restrictions, and separatedness identifies them.
  let aR : E →+* F.obj (op X) :=
    { toFun := a
      map_one' := hsep fun _ f hf ↦ by simp [ha _ f hf]
      map_mul' e e' := hsep fun _ f hf ↦ by simp [ha _ f hf]
      map_zero' := hsep fun _ f hf ↦ by simp [ha _ f hf]
      map_add' e e' := hsep fun _ f hf ↦ by simp [ha _ f hf] }
  refine ⟨⟨aR, ?_⟩, fun _ f hf ↦ ConcreteCategory.ext_apply (ha · f hf)⟩
  -- `F(X)` carries the topology induced from the product, and each coordinate of `aR` is the
  -- continuous map `φ f hf`.
  exact hind.continuous_iff.mpr <| continuous_pi fun g ↦
    (φ g.2.1 g.2.2).2.congr fun e ↦ (ha e g.2.1 g.2.2).symm

/-- **The sheaf condition for one sieve.** Let `S` be a sieve on `X` for which the presheaf of
sets underlying `F` satisfies the sheaf condition, and such that the map sending `x ∈ F(X)` to
its restrictions along the arrows `Y ⟶ X` of `S` is inducing for the product topology. Then, for
every topological commutative ring `E`, the presheaf `F ⋙ coyoneda.obj (op E)` of morphisms out
of `E` satisfies the sheaf condition for `S`. See `isSheaf_of_isSheaf_forget` for the sheaf
property over a Grothendieck topology. -/
theorem isSheafFor_of_isSheafFor_forget {X : C} (S : Sieve X)
    (hS : Presieve.IsSheafFor (F ⋙ forget _root_.TopCommRingCat) S.arrows)
    (hind : Topology.IsInducing
      fun (x : F.obj (op X)) (g : (Y : C) × { f : Y ⟶ X // S f }) ↦ (F.map g.2.1.op).1 x)
    (E : _root_.TopCommRingCat.{v}) :
    Presieve.IsSheafFor (F ⋙ coyoneda.obj (op E)) S.arrows :=
  -- Two morphisms out of `E` with the same restrictions agree at every `e : E`, by separatedness
  -- of the presheaf of sets; so it remains to glue each compatible family.
  Presieve.IsSeparatedFor.isSheafFor (fun _ _ _ h₁ h₂ ↦ ConcreteCategory.ext_apply fun e ↦
    hS.isSeparatedFor.ext fun _ f hf ↦
      ConcreteCategory.congr_hom ((h₁ f hf).trans (h₂ f hf).symm) e)
    (exists_isAmalgamation_of_isSheafFor_forget F hS hind)

/-- **Sheaves from sheaves of sets.** A presheaf `F` of topological commutative rings on a site
`(C, J)` is a sheaf once its underlying presheaf of sets is a sheaf and, for every covering sieve
`S` on `X`, the map sending `x ∈ F(X)` to its restrictions along the arrows `Y ⟶ X` of `S` is
inducing for the product topology. The single-sieve form is `isSheafFor_of_isSheafFor_forget`.
Compare `CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget`, which covers forgetful functors that
preserve limits and reflect isomorphisms; here the inducing hypothesis `hind` supplies the
topological half of the sheaf condition. -/
theorem isSheaf_of_isSheaf_forget (J : GrothendieckTopology C)
    (hF : Presheaf.IsSheaf J (F ⋙ forget _root_.TopCommRingCat))
    (hind : ∀ ⦃X : C⦄ (S : Sieve X), S ∈ J X →
      Topology.IsInducing fun (x : F.obj (op X)) (g : (Y : C) × { f : Y ⟶ X // S f }) ↦
        (F.map g.2.1.op).1 x) : Presheaf.IsSheaf J F := fun E _ S hS ↦
  isSheafFor_of_isSheafFor_forget F S (hF.isSheafFor S hS) (hind S hS) E

end TauCeti.TopCommRingCat
