/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic

/-!
# Pasting categorical pullbacks

For functors `F : A ⥤ B`, `G : C ⥤ B` and `F' : A' ⥤ A`, the categorical pullback of `F'` along
the first projection `π₁ F G : F ⊡ G ⥤ A` is equivalent to the categorical pullback of the
composite `F' ⋙ F` along `G`. An object of `F' ⊡ π₁ F G` is a triple `(a', (a, c, e), e')` with
`e : F a ≅ G c` and `e' : F' a' ≅ a`; it corresponds to `(a', c, F e' ≪≫ e)`. This is the pasting
law for pullbacks, in the (2,1)-category of categories: the analogue of Mathlib's
`CategoryTheory.Limits.pullbackRightPullbackFstIso` for ordinary pullbacks.

## Main declarations

* `CategoryTheory.Limits.CategoricalPullback.pullbackRightPullbackFstEquiv`: the equivalence
  `F' ⊡ π₁ F G ≌ (F' ⋙ F) ⊡ G`.

## References

* [Kerodon, Tag 032Y](https://kerodon.net/tag/032Y) (categorical pullbacks).
-/

public section

namespace CategoryTheory.Limits.CategoricalPullback

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {A : Type u₁} {B : Type u₂} {C : Type u₃} {A' : Type u₄}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] [Category.{v₄} A']
  (F : A ⥤ B) (G : C ⥤ B) (F' : A' ⥤ A)

/-- The pasting equivalence `F' ⊡ π₁ F G ≌ (F' ⋙ F) ⊡ G`. Its functor sends `(a', (a, c, e), e')`
to `(a', c, F e' ≪≫ e)`, and its inverse sends `(a', c, e)` to `(a', (F' a', c, e), 𝟙)`. -/
-- The body is exposed: the structure isomorphism of an object in the image depends on its
-- components, so stating its characteristic equation requires unfolding the functor.
@[expose, simps! functor_obj_fst functor_obj_snd functor_obj_iso functor_map_fst functor_map_snd
  inverse_obj_fst inverse_obj_snd_fst inverse_obj_snd_snd inverse_obj_snd_iso inverse_obj_iso
  inverse_map_fst inverse_map_snd_fst inverse_map_snd_snd]
def pullbackRightPullbackFstEquiv : F' ⊡ (π₁ F G) ≌ (F' ⋙ F) ⊡ G where
  functor :=
    { obj x := ⟨x.fst, x.snd.snd, F.mapIso x.iso ≪≫ x.snd.iso⟩
      map f :=
        { fst := f.fst
          snd := f.snd.snd
          w := by
            -- `x.iso` ends in `(π₁ F G).obj x.snd`, which is `x.snd.fst` only after unfolding
            -- `π₁`, so the steps are glued by unification rather than by rewriting.
            calc
              _ = F.map (F'.map f.fst ≫ _) ≫ _ := (F.map_comp_assoc _ _ _).symm
              _ = F.map (_ ≫ f.snd.fst) ≫ _ := congrArg (fun g ↦ F.map g ≫ _) f.w
              _ = _ ≫ F.map f.snd.fst ≫ _ := F.map_comp_assoc _ _ _
              _ = _ ≫ _ ≫ G.map f.snd.snd := congrArg (_ ≫ ·) f.snd.w
              _ = _ := (Category.assoc _ _ _).symm } }
  inverse :=
    { obj x := ⟨x.fst, ⟨F'.obj x.fst, x.snd, x.iso⟩, Iso.refl _⟩
      map f :=
        { fst := f.fst
          snd := ⟨F'.map f.fst, f.snd, f.w⟩
          w := (Category.comp_id _).trans (Category.id_comp _).symm } }
  -- As in `functor.map.w`, the structure isomorphisms below compose `x.iso`, which ends in
  -- `(π₁ F G).obj x.snd`, with isomorphisms out of `x.snd.fst`; the composites typecheck only
  -- after unfolding `π₁`. So `simp` cannot rewrite them (even `Iso.trans_hom` does not fire, and
  -- `simp` leaves `F.map x.iso.inv ≫ (F.mapIso x.iso ≪≫ x.snd.iso).hom = x.snd.iso.hom` open),
  -- and the identity cancellations are glued by unification instead.
  unitIso := NatIso.ofComponents
    (fun x ↦ mkIso (Iso.refl _) (mkIso x.iso.symm (Iso.refl _)
      ((F.map_comp_assoc x.iso.inv x.iso.hom x.snd.iso.hom).symm.trans (by
        rw [x.iso.inv_hom_id, F.map_id]
        exact (Category.id_comp _).trans
          ((Category.comp_id _).symm.trans (congrArg (_ ≫ ·) (G.map_id _).symm)))))
      ((Category.comp_id _).trans ((F'.map_id _).trans x.iso.hom_inv_id.symm)))
    (fun f ↦ by
      have h : F'.map f.fst ≫ _ = _ ≫ f.snd.fst := f.w
      ext
      · exact (Category.comp_id _).trans (Category.id_comp _).symm
      · exact (Iso.comp_inv_eq _).2
          (((Iso.eq_inv_comp _).2 h.symm).trans (Category.assoc _ _ _).symm)
      · exact (Category.comp_id _).trans (Category.id_comp _).symm)
  counitIso := NatIso.ofComponents (fun x ↦ mkIso (Iso.refl _) (Iso.refl _) (by
    simp only [Functor.comp_obj, Functor.comp_map, Iso.refl_hom, Functor.map_id,
      Category.id_comp, Category.comp_id]
    exact (Category.id_comp _).symm.trans (congrArg (· ≫ x.iso.hom) (F.map_id _).symm)))
  functor_unitIso_comp x := hom_ext (Category.id_comp _) (Category.id_comp _)

end CategoryTheory.Limits.CategoricalPullback
