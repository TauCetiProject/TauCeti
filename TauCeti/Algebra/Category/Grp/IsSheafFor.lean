/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import Mathlib.CategoryTheory.Sites.IsSheafFor

/-!
# The sheaf condition for one presieve, for presheaves of abelian groups

For a presheaf `P` with values in an arbitrary category, the sheaf condition for a presieve `R` is
expressed through the presheaves of types `P ⋙ coyoneda.obj E` (as in `Presheaf.IsSheaf`, or in
`Presheaf.isLimit_iff_isSheafFor_presieve`). For a presheaf of abelian groups this is the same as
the sheaf condition for `R` on the underlying presheaf of sets: a compatible family of
homomorphisms out of `E` glues pointwise, and the glued map is additive because restriction to the
members of `R` is jointly injective. Mathlib's `Presheaf.isSheaf_iff_isSheaf_forget` is the
analogous statement for all covering sieves of a Grothendieck topology at once.

## Main results

* `TauCeti.AddCommGrpCat.isSheafFor_forget_iff`: a presheaf of abelian groups satisfies the
  sheaf condition for a presieve `R` against every abelian group exactly when its underlying
  presheaf of sets satisfies the sheaf condition for `R`.
-/

public section

namespace TauCeti

open CategoryTheory Opposite

universe w v u

namespace AddCommGrpCat

variable {C : Type u} [Category.{v} C] {X : C}

/-- **The sheaf condition for a presheaf of abelian groups is checked on underlying sets.** A
presheaf `P` of abelian groups satisfies the sheaf condition for a presieve `R` on the underlying
presheaf of sets exactly when, for every abelian group `E`, the presheaf of homomorphisms
`P ⋙ coyoneda.obj E` satisfies it. -/
theorem isSheafFor_forget_iff (R : Presieve X) (P : Cᵒᵖ ⥤ _root_.AddCommGrpCat.{w}) :
    R.IsSheafFor (P ⋙ forget _root_.AddCommGrpCat) ↔
      ∀ E : _root_.AddCommGrpCat.{w}ᵒᵖ, R.IsSheafFor (P ⋙ coyoneda.obj E) := by
  refine ⟨fun h E x hx ↦ ?_, fun h ↦ (Presieve.isSheafFor_iff_of_iso
    (Functor.isoWhiskerLeft P _root_.AddCommGrpCat.coyonedaObjIsoForget)).1 (h _)⟩
  -- restriction to the members of `R` is jointly injective on underlying sets
  have hsep {s t : P.obj (op X)} (hst : ∀ ⦃Y : C⦄ ⦃g : Y ⟶ X⦄ (hg : R g),
      P.map g.op s = P.map g.op t) : s = t :=
    h.isSeparatedFor.ext hst
  -- glue the values of the family at each `e : E`
  let y (e : E.unop) : Presieve.FamilyOfElements (P ⋙ forget _) R := fun _ g hg ↦ (x g hg).hom e
  have hy (e : E.unop) : (y e).Compatible := fun _ _ _ g₁ g₂ f₁ f₂ hf₁ hf₂ hw ↦
    ConcreteCategory.congr_hom (hx g₁ g₂ hf₁ hf₂ hw) e
  let t (e : E.unop) : P.obj (op X) := h.amalgamate (y e) (hy e)
  have ht (e : E.unop) ⦃Y : C⦄ ⦃g : Y ⟶ X⦄ (hg : R g) : P.map g.op (t e) = (x g hg).hom e :=
    h.valid_glue (hy e) g hg
  let φ : E.unop →+ P.obj (op X) :=
    { toFun := t
      map_zero' := hsep fun _ g hg ↦ by simp [ht _ hg]
      map_add' e e' := hsep fun _ g hg ↦ by simp [ht _ hg] }
  refine ⟨_root_.AddCommGrpCat.ofHom φ, fun _ g hg ↦ ConcreteCategory.ext_apply (ht · hg),
    fun ψ hψ ↦ ConcreteCategory.ext_apply fun e ↦ hsep fun _ g hg ↦ ?_⟩
  -- `ψ` and the glued map have the same restrictions at each `e`
  exact (ConcreteCategory.congr_hom (hψ g hg) e).trans (ht e hg).symm

end AddCommGrpCat

end TauCeti
