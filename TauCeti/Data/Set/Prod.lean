/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Prod

/-!
# Graphs and fibre products of functions

This file adds to Mathlib's API for graphs of functions over a set and for the fibre product
`Function.Pullback f g` of two functions with a common codomain.

## Main results

* `Set.graphOn_const`: the graph of a constant function over `s` is a horizontal slice `s ×ˢ {b}`.
* `Set.mem_image_prodMk_self_snd_iff`: membership in the swapped graph over a set.
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

/-- Membership in the swapped graph of `f` over `s` is determined by the second coordinate
and the graph equation. -/
theorem Set.mem_image_prodMk_self_snd_iff {N M : Type*} (f : N → M) (s : Set N)
    (x : M × N) :
    x ∈ (fun n => (f n, n)) '' s ↔ x.2 ∈ s ∧ x.1 = f x.2 := by
  have himage : (fun n => (f n, n)) '' s = Prod.swap '' s.graphOn f :=
    (Set.image_image Prod.swap (fun n => (n, f n)) s).symm
  rw [himage, Set.image_swap_eq_preimage_swap, Set.mem_preimage, Set.mem_graphOn]
  exact and_congr_right fun _ => eq_comm

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
