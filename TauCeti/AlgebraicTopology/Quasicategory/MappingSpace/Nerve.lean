/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Quasicategory.Postcomposition
public import TauCeti.AlgebraicTopology.SimplicialSet.Nerve.Basic

/-!
# Relative right mapping spaces of nerves

For a functor `F : E ⥤ B`, the vertices of the right mapping space over an edge `e` of `N(B)`
are the morphisms of `E` mapped by `F` to the morphism of `e`
(`SSet.rightMappingSpaceOver.obj₀EquivNerve`). Postcomposition with an edge of `N(E)` corresponds
to composition of these morphisms (`SSet.rightMappingSpaceOver.obj₀EquivNerve_postcomp`).
-/

public section

universe u

open CategoryTheory Opposite Simplicial

namespace SSet.rightMappingSpaceOver

variable {E B : Type u} [SmallCategory E] [SmallCategory B]

/-- The vertices of the space `Hom^R(x, y)_e` of maps lying over an edge `e`, for the map of nerves
induced by a functor `F`, are the morphisms `nerveEquiv x ⟶ nerveEquiv y` sent by `F` to the
morphism of `e`. -/
noncomputable def obj₀EquivNerve (F : E ⥤ B) {x y : (nerve E) _⦋0⦌}
    (e : Edge ((nerveMap F).app _ x) ((nerveMap F).app _ y)) :
    (rightMappingSpaceOver (nerveMap F) e : SSet.{u}) _⦋0⦌ ≃
      {g : nerveEquiv x ⟶ nerveEquiv y // F.map g = nerve.homEquiv e} where
  toFun v := ⟨nerve.homEquiv (rightMappingSpace.obj₀Equiv v.val), by
    rw [← nerve.homEquiv_map_nerveMap, (rightMappingSpaceOver.mem_obj₀_iff e v.val).1
      v.property]⟩
  invFun g := ⟨rightMappingSpace.obj₀Equiv.symm (nerve.homEquiv.symm g.val),
    (rightMappingSpaceOver.mem_obj₀_iff e _).2 (nerve.homEquiv.injective (by
      rw [Equiv.apply_symm_apply, nerve.homEquiv_map_nerveMap, Equiv.apply_symm_apply,
        g.property]))⟩
  left_inv v := by simp
  right_inv g := by simp

/-- The forward equivalence reads a relative mapping-space vertex as its morphism. -/
@[simp]
lemma obj₀EquivNerve_apply_coe (F : E ⥤ B) {x y : (nerve E) _⦋0⦌}
    (e : Edge ((nerveMap F).app _ x) ((nerveMap F).app _ y))
    (v : (rightMappingSpaceOver (nerveMap F) e : SSet.{u}) _⦋0⦌) :
    dsimp% (obj₀EquivNerve F e v).val = nerve.homEquiv (rightMappingSpace.obj₀Equiv v.val) :=
  (rfl)

/-- The inverse equivalence regards a morphism lift as a relative mapping-space vertex. -/
@[simp]
lemma obj₀EquivNerve_symm_apply_coe (F : E ⥤ B) {x y : (nerve E) _⦋0⦌}
    (e : Edge ((nerveMap F).app _ x) ((nerveMap F).app _ y))
    (g : {g : nerveEquiv x ⟶ nerveEquiv y // F.map g = nerve.homEquiv e}) :
    dsimp% ((obj₀EquivNerve F e).symm g).val =
      rightMappingSpace.obj₀Equiv.symm (nerve.homEquiv.symm g.val) :=
  (rfl)

/-- Postcomposition with an edge `g` of the nerve composes the corresponding morphisms. -/
lemma obj₀EquivNerve_postcomp (F : E ⥤ B) {x y z : (nerve E) _⦋0⦌} (g : Edge y z)
    {e : Edge ((nerveMap F).app _ x) ((nerveMap F).app _ y)}
    {e' : Edge ((nerveMap F).app _ x) ((nerveMap F).app _ z)}
    (h : nerve.homEquiv e ≫ nerve.homEquiv (g.map (nerveMap F)) = nerve.homEquiv e')
    (v : (rightMappingSpaceOver (nerveMap F) e : SSet.{u}) _⦋0⦌) :
    dsimp% (obj₀EquivNerve F e' ((rightMappingSpaceOver.postcomp g h).app _ v)).val =
      (obj₀EquivNerve F e v).val ≫ nerve.homEquiv g := by
  simp only [obj₀EquivNerve_apply_coe]
  obtain ⟨c⟩ := rightMappingSpace.postcomp_compStruct g (rightMappingSpace.obj₀Equiv v.val)
  rw [Equiv.symm_apply_apply] at c
  have hv := ConcreteCategory.congr_hom
    (NatTrans.congr_app (rightMappingSpaceOver.postcomp_ι g h) (op ⦋0⦌)) v
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at hv
  -- The inclusion of `Hom^R(x, z)_{e'}` into `Hom^R(x, z)` takes a vertex to its underlying vertex.
  exact (congrArg (fun w ↦ nerve.homEquiv (rightMappingSpace.obj₀Equiv w)) hv).trans
    (nerve.homEquiv_comp c).symm

end SSet.rightMappingSpaceOver
