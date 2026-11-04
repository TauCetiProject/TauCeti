/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.RelativeCellComplex.AttachCells

/-!
# Constructions of cell attachments

An isomorphism `f : X₁ ⟶ X₂` is obtained by attaching an empty family of cells
(`HomotopicalAlgebra.AttachCells.ofIsIso`): the pushout of the identity of an initial object along
any morphism is an isomorphism. This fills the stages of a relative cell complex at which nothing
is attached, for instance when all cells are attached at a single stage.

A cell attachment is carried across a pushout square by pasting it with the square
(`HomotopicalAlgebra.AttachCells.ofIsPushout`): the cobase change of a morphism obtained by
attaching cells is obtained by attaching the same cells.

## References

* R. Fritsch and R. Piccinini, *Cellular Structures in Topology*, Cambridge University Press,
  1990.
-/

public section

open CategoryTheory Limits

universe w t v u

namespace HomotopicalAlgebra.AttachCells

variable {C : Type u} [Category.{v} C] [HasColimitsOfShape (Discrete PEmpty.{w + 1}) C]
  {α : Type*} {A B : α → C} (g : ∀ a, A a ⟶ B a) {X₁ X₂ : C} (f : X₁ ⟶ X₂) [IsIso f]

/-- An isomorphism is obtained by attaching no cells. -/
noncomputable def ofIsIso : AttachCells.{w} g f where
  ι := PEmpty.{w + 1}
  π := PEmpty.elim
  cofan₁ := Cofan.mk _ (Sigma.ι fun i : PEmpty.{w + 1} ↦ A i.elim)
  cofan₂ := Cofan.mk _ (Sigma.ι fun i : PEmpty.{w + 1} ↦ B i.elim)
  isColimit₁ := coproductIsCoproduct _
  isColimit₂ := coproductIsCoproduct _
  m := Sigma.desc fun i ↦ i.elim
  hm i := i.elim
  g₁ := Sigma.desc fun i ↦ i.elim
  g₂ := Sigma.desc fun i ↦ i.elim
  isPushout := by
    -- Both coproducts are empty, so the left vertical map is an isomorphism, as is `f`.
    refine @IsPushout.of_vert_isIso _ _ _ _ _ _ _ _ _ _ ?_ _ ⟨Sigma.hom_ext _ _ fun i ↦ i.elim⟩
    exact ⟨Sigma.desc fun i ↦ i.elim, Sigma.hom_ext _ _ fun i ↦ i.elim,
      Sigma.hom_ext _ _ fun i ↦ i.elim⟩

/-- No cells are attached in `AttachCells.ofIsIso`. -/
instance : IsEmpty (ofIsIso.{w} g f).ι :=
  ⟨fun i ↦ i.elim⟩

section ofIsPushout

variable {C : Type u} [Category.{v} C] {α : Type t} {A B : α → C} {g : ∀ a, A a ⟶ B a}
  {X₁ X₂ Y₁ Y₂ : C} {f : X₁ ⟶ X₂} (c : AttachCells.{w} g f)
  {p : X₁ ⟶ Y₁} {f' : Y₁ ⟶ Y₂} {b : X₂ ⟶ Y₂} (sq : IsPushout p f f' b)

/-- **Cobase change of a cell attachment.** If `X₂` is obtained from `X₁` by attaching cells along
`f` and the square formed by `p`, `f`, `f'` and `b` is a pushout, then `Y₂` is obtained from `Y₁`
by attaching the same cells along `f'`, with attaching maps composed with `p`. -/
@[expose] def ofIsPushout : AttachCells.{w} g f' where
  ι := c.ι
  π := c.π
  cofan₁ := c.cofan₁
  cofan₂ := c.cofan₂
  isColimit₁ := c.isColimit₁
  isColimit₂ := c.isColimit₂
  m := c.m
  hm := c.hm
  g₁ := c.g₁ ≫ p
  g₂ := c.g₂ ≫ b
  isPushout := c.isPushout.paste_horiz sq

/-- The inclusion of a cell after cobase change is the original inclusion followed by `b`. -/
@[simp, reassoc]
lemma ofIsPushout_cell (i : c.ι) : (c.ofIsPushout sq).cell i = c.cell i ≫ b :=
  -- Both sides are `c.cofan₂.inj i ≫ c.g₂ ≫ b` by definition, up to associativity.
  (Category.assoc _ _ _).symm

end ofIsPushout

end HomotopicalAlgebra.AttachCells
