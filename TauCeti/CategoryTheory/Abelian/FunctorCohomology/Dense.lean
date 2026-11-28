/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Abelian.FunctorCohomology.Basic

import Mathlib.CategoryTheory.Subfunctor.Image

/-!
# Pullback stability and range comparisons for dense subfunctors

This file adds basic structural lemmas on top of
`TauCeti.CategoryTheory.Abelian.FunctorCohomology.Basic`:

* `TauCeti.isDenseFor_preimage`: the preimage of a dense subfunctor along any natural
  transformation is dense.
* `TauCeti.isDenseFor_of_top_le`: any subfunctor containing `⊤` is dense.
* `TauCeti.isExtEquivFor_free_iff_range`: a monomorphism `g : E ⟶ Y` induces an Ext-equivalence
  on free abelian functors if and only if the inclusion of its range subfunctor does.
* `TauCeti.isExtEquivFor_free_range_comp_iff_of_epi`: precomposing with an epimorphism does not
  change whether the range inclusion induces an Ext-equivalence on free abelian functors.

## References

* `grh-lean`, https://github.com/lsernau/grh-lean (commit
  `72fead102f663d5c7a407964a13dc0cf9d977207`), files
  `src/Lib/Cohomology/Etale/DenseSubfunctors.lean` (declarations
  `New.Variety.IsCohomDense.preimage`, `New.Variety.IsCohomDense.of_top_le`) and
  `src/Lib/Cohomology/Etale/Basic.lean` (declaration `New.Variety.isCohomEquiv_iff_range`);
  Apache 2.0, Copyright 2026 Anthropic, PBC.
-/

public section

open CategoryTheory Abelian

universe t w v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [HasExt.{t} (C ⥤ AddCommGrpCat.{w})]
  {F : C ⥤ AddCommGrpCat.{w}}

/-- The preimage of a dense subfunctor `U` of `Y` under any natural transformation `p : E ⟶ Y` is
dense in `E`. -/
theorem isDenseFor_preimage {E Y : C ⥤ Type w} {U : Subfunctor Y}
    (h : U.IsDenseFor.{t} F) (p : E ⟶ Y) :
    (U.preimage p).IsDenseFor.{t} F := by
  rw [Subfunctor.isDenseFor_iff_forall_subsingleton_ext] at h ⊢
  exact fun _ _ y n ↦ h (y ≫ p) n

/-- A subfunctor `U` of `Y` satisfying `⊤ ≤ U` is dense for every coefficient functor `F`. -/
theorem isDenseFor_of_top_le {Y : C ⥤ Type w} {U : Subfunctor Y} (h : ⊤ ≤ U) :
    U.IsDenseFor.{t} F := by
  obtain rfl : U = ⊤ := top_unique h
  exact Subfunctor.isDenseFor_top Y

/-- A monomorphism `g : E ⟶ Y` induces an Ext-equivalence on free abelian functors if and only if
the inclusion of `Subfunctor.range g` does. -/
theorem isExtEquivFor_free_iff_range {E Y : C ⥤ Type w} (g : E ⟶ Y) [Mono g]
    {U : Subfunctor Y} (hU : Subfunctor.range g = U) :
    IsExtEquivFor.{t} F (Functor.whiskerRight g AddCommGrpCat.free) ↔
      IsExtEquivFor.{t} F (Functor.whiskerRight U.ι AddCommGrpCat.free) := by
  subst hU
  let e : E ⟶ (Subfunctor.range g).toFunctor := Subfunctor.toRange g
  have hfac : e ≫ (Subfunctor.range g).ι = g := Subfunctor.toRange_ι g
  have : ∀ X, IsIso (e.app X) := fun X ↦ (isIso_iff_bijective _).mpr
    ⟨fun x y hxy ↦ (mono_iff_injective (g.app X)).mp inferInstance (congrArg Subtype.val hxy),
      fun ⟨_, x, hx⟩ ↦ ⟨x, Subtype.ext hx⟩⟩
  have : IsIso e := NatIso.isIso_of_isIso_app e
  have hfree : Functor.whiskerRight g AddCommGrpCat.free =
      Functor.whiskerRight e AddCommGrpCat.free ≫
        Functor.whiskerRight (Subfunctor.range g).ι AddCommGrpCat.free := by
    rw [← Functor.whiskerRight_comp, hfac]
  rw [hfree]
  exact (isExtEquivFor_of_isIso (F := F)
    (Functor.whiskerRight e AddCommGrpCat.free)).comp_iff_right _

/-- Precomposing with an epimorphism `p : E' ⟶ E` preserves and reflects whether the range
inclusion induces an Ext-equivalence on free abelian functors. -/
theorem isExtEquivFor_free_range_comp_iff_of_epi {E' E Y : C ⥤ Type w} (p : E' ⟶ E)
    (q : E ⟶ Y) [Epi p] :
    IsExtEquivFor.{t} F (Functor.whiskerRight (Subfunctor.range (p ≫ q)).ι AddCommGrpCat.free) ↔
      IsExtEquivFor.{t} F (Functor.whiskerRight (Subfunctor.range q).ι AddCommGrpCat.free) := by
  have hrange : Subfunctor.range (p ≫ q) = Subfunctor.range q := by
    rw [Subfunctor.range_comp, Subfunctor.range_eq_top p, Subfunctor.image_top]
  rw [hrange]

end TauCeti
