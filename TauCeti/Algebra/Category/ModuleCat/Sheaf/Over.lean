/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Defs
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

/-!
# Module structures on restrictions to slice sites

Restricting a sheaf of modules to the slice over an object preserves its section modules.
For a commutative coefficient sheaf, these sections retain the action of the original
commutative ring of sections after forgetting commutativity in the coefficient sheaf.

Since `𝟙 X` is a terminal object of the slice over `X`, a global section of the restriction
`M.over X` is the same as a section of `M` over `X`.

## Main declarations

* `SheafOfModules.overSectionModule`: the original commutative-ring action on sections of
  a sheaf of modules restricted to a slice site;
* `SheafOfModules.overSectionsEquiv`: global sections of `M.over X` are sections of `M` over `X`;
* `PresheafOfModules.map_sum_smul_map`: restriction of a linear combination of restricted sections.
-/

public section

open CategoryTheory Opposite

namespace TauCeti

universe u v v₁ u₁

noncomputable section

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}

/-- Restriction to a slice uses the original commutative-ring action on each section module. -/
instance _root_.SheafOfModules.overSectionModule
    {R : Sheaf J CommRingCat.{u}} [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
    (P : _root_.SheafOfModules.{v} (ringCatSheaf R)) (U V : C) (g : V ⟶ U) :
    Module (R.obj.obj (Opposite.op V)) ((P.over U).val.obj (Opposite.op (Over.mk g))) :=
  inferInstanceAs (Module (R.obj.obj (Opposite.op V)) (P.val.obj (Opposite.op V)))

section Sections

variable {R : Sheaf J RingCat.{u}} (M : _root_.SheafOfModules.{v} R) (X : C)

/-- Global sections of the restriction `M.over X` are the sections of `M` over `X`: a global
section is determined by its value over the terminal object `𝟙 X`, and a section `s` over `X`
gives the global section whose value over `f : Y ⟶ X` is the restriction of `s` along `f`. -/
def _root_.SheafOfModules.overSectionsEquiv : (M.over X).sections ≃ M.val.obj (op X) where
  toFun s := s.eval (op (Over.mk (𝟙 X)))
  invFun s := PresheafOfModules.sectionsMk (fun Y ↦ M.val.map Y.unop.hom.op s)
    (fun Y Y' g ↦ by
      refine (PresheafOfModules.map_comp_apply M.val Y.unop.hom.op g.unop.left.op s).symm.trans ?_
      rw [← op_comp, Over.w g.unop])
  left_inv s := by
    ext Y
    exact s.property (Over.homMk Y.unop.hom : Y.unop ⟶ Over.mk (𝟙 X)).op
  right_inv s := by
    refine (PresheafOfModules.presheaf_map_apply_coe M.val _ s).symm.trans ?_
    simp only [PresheafOfModules.presheaf_obj_coe, Over.mk_left, Over.mk_hom, op_id,
      CategoryTheory.Functor.map_id, AddCommGrpCat.hom_id]
    rfl

/-- The section of `M` over `X` attached to a global section of `M.over X` is its value over
the terminal object `𝟙 X`. -/
@[simp]
theorem _root_.SheafOfModules.overSectionsEquiv_apply (s : (M.over X).sections) :
    M.overSectionsEquiv X s = s.eval (op (Over.mk (𝟙 X))) :=
  (rfl)

/-- The global section of `M.over X` attached to a section `s` of `M` over `X` takes the value
`M.val.map f.op s` over `f : Y ⟶ X`. -/
@[simp]
theorem _root_.SheafOfModules.overSectionsEquiv_symm_apply_eval (s : M.val.obj (op X))
    (Y : Over X) : ((M.overSectionsEquiv X).symm s).eval (op Y) = M.val.map Y.hom.op s :=
  (rfl)

end Sections

section Restriction

variable {R : Cᵒᵖ ⥤ RingCat.{u}} (N : PresheafOfModules.{v} R)

/-- Restricting a linear combination of restricted sections along `h₀` gives the corresponding
combination with the composite restriction maps. -/
theorem _root_.PresheafOfModules.map_sum_smul_map {U V₀ V : C} (f₀ : V₀ ⟶ U) (h₀ : V ⟶ V₀)
    {ι : Type*} [Fintype ι] {W : ι → C} (g₀ : ∀ k, V₀ ⟶ W k) (n : ∀ k, N.obj (op (W k)))
    (a : ι → R.obj (op U)) :
    N.map h₀.op (∑ k, R.map f₀.op (a k) • N.map (g₀ k).op (n k)) =
      ∑ k, R.map (h₀ ≫ f₀).op (a k) • N.map (h₀ ≫ g₀ k).op (n k) := by
  refine (map_sum _ _ _).trans (Finset.sum_congr rfl fun k _ ↦ ?_)
  refine (PresheafOfModules.map_smul N h₀.op _ _).trans ?_
  have er : R.map (h₀ ≫ f₀).op (a k) = R.map h₀.op (R.map f₀.op (a k)) := by
    rw [show (h₀ ≫ f₀).op = f₀.op ≫ h₀.op from rfl, Functor.map_comp]
    -- A composite of ring maps applied to `a k` is the iterated application.
    rfl
  rw [er]
  exact congrArg _ (PresheafOfModules.map_comp_apply N (g₀ k).op h₀.op (n k)).symm

end Restriction

end SheafOfModules

end

end TauCeti
