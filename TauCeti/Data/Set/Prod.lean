/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Prod
public import Mathlib.Basic.Finite.Defs

/-!
# Graphs and fibre products of functions

This file adds to Mathlib's API for graphs of functions over a set and for the fibre product
`Function.Pullback f g` of two functions with a common codomain.

## Main results

* `Set.graphOn_const`: the graph of a constant function over `s` is a horizontal slice `s ×ˢ {b}`.
* `Function.Pullback.ext`: a point of the fibre product is determined by its two coordinates.
* `Function.Pullback.fstPreimageEquiv`: the fibre of the projection `X ×_Y Z → X` over `x` is the
  fibre of `g` over `f x`.
-/

public section

open Function

/-- The graph of a constant function over a set `s` is the slice `s ×ˢ {b}`. -/
@[simp]
theorem Set.graphOn_const {α β : Type*} (s : Set α) (b : β) :
    s.graphOn (Function.const α b) = s ×ˢ {b} := by
  ext ⟨x, y⟩
  simp [eq_comm]

variable {X Y Z : Type*} {f : X → Y} {g : Z → Y}

/-- A point of the fibre product `X ×_Y Z` is determined by its two coordinates. -/
@[ext]
theorem Function.Pullback.ext {p q : f.Pullback g} (h₁ : p.fst = q.fst) (h₂ : p.snd = q.snd) :
    p = q :=
  Subtype.ext (Prod.ext h₁ h₂)

/-- The fibre over `x` of the projection `X ×_Y Z → X` of the fibre product of `f` and `g` is the
fibre of `g` over `f x`. -/
def Function.Pullback.fstPreimageEquiv (x : X) :
    (Pullback.fst : f.Pullback g → X) ⁻¹' {x} ≃ g ⁻¹' {f x} where
  toFun y := ⟨y.val.snd, y.val.property.symm.trans (congrArg f y.property)⟩
  invFun z := ⟨⟨(x, z.val), z.property.symm⟩, rfl⟩
  left_inv y := Subtype.ext (Pullback.ext y.property.symm rfl)
  right_inv _ := rfl

/-- The fibre of the first pullback projection over `x` is finite exactly when the original
fibre over `f x` is finite. -/
@[simp]
theorem Function.Pullback.finite_preimage_fst_singleton_iff (x : X) :
    Finite ((Pullback.fst : f.Pullback g → X) ⁻¹' {x}) ↔ Finite (g ⁻¹' {f x}) :=
  (Pullback.fstPreimageEquiv x).finite_iff

@[simp]
theorem Function.Pullback.fstPreimageEquiv_apply_coe (x : X)
    (y : (Pullback.fst : f.Pullback g → X) ⁻¹' {x}) :
    (Pullback.fstPreimageEquiv x y : Z) = y.val.snd :=
  (rfl)

@[simp]
theorem Function.Pullback.fst_fstPreimageEquiv_symm_apply (x : X) (z : g ⁻¹' {f x}) :
    ((Pullback.fstPreimageEquiv x).symm z : f.Pullback g).fst = x :=
  (rfl)

@[simp]
theorem Function.Pullback.snd_fstPreimageEquiv_symm_apply (x : X) (z : g ⁻¹' {f x}) :
    ((Pullback.fstPreimageEquiv x).symm z : f.Pullback g).snd = z :=
  (rfl)

/-- The first pullback projection is surjective exactly when the range of the base map is
contained in the range of the other map. -/
@[simp]
theorem Function.Pullback.fst_surjective_iff :
    Surjective (Pullback.fst : f.Pullback g → X) ↔ Set.range f ⊆ Set.range g := by
  rw [Set.range_subset_iff]
  apply forall_congr'
  intro x
  simpa [Set.mem_range] using (Pullback.fstPreimageEquiv (f := f) (g := g) x).nonempty_congr
