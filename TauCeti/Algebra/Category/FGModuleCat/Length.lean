/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.RingTheory.Length
public import TauCeti.CategoryTheory.Subobject.Length
import Mathlib.Algebra.Category.ModuleCat.Subobject
import TauCeti.Algebra.Category.FGModuleCat.Basic
import TauCeti.Algebra.Category.ModuleCat.Length
import TauCeti.CategoryTheory.Subobject.FullSubcategory

/-!
# The length of a finitely generated module as an object of `FGModuleCat`

The length `CategoryTheory.length X` of a finitely generated module `X` as an object of
`FGModuleCat A` is its length as a module (`FGModuleCat.length_eq`), over any ring `A`.

## Main results

* `FGModuleCat.length_eq`: `CategoryTheory.length X = Module.length A X.obj`.

## Implementation notes

A monomorphism of `FGModuleCat A` is injective (`FGModuleCat.preservesMonomorphisms_ι`), so the
subobjects of `X` in `FGModuleCat A` embed into the submodules of `X.obj`
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
