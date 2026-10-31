/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Prod

/-!
# Fibre products of functions

This file adds to Mathlib's API for the fibre product `Function.Pullback f g` of two functions with
a common codomain.

## Main results

* `Function.Pullback.ext`: a point of the fibre product is determined by its two coordinates.
* `Function.Pullback.fstPreimageEquiv`: the fibre of the projection `X ×_Y Z → X` over `x` is the
  fibre of `g` over `f x`.
-/

public section

open Function

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
  toFun y := ⟨y.1.snd, y.1.2.symm.trans (congrArg f y.2)⟩
  invFun z := ⟨⟨(x, z.1), z.2.symm⟩, rfl⟩
  left_inv y := Subtype.ext (Pullback.ext y.2.symm rfl)
  right_inv _ := rfl

@[simp]
theorem Function.Pullback.fstPreimageEquiv_apply_coe (x : X)
    (y : (Pullback.fst : f.Pullback g → X) ⁻¹' {x}) :
    (Pullback.fstPreimageEquiv x y : Z) = y.1.snd :=
  (rfl)

@[simp]
theorem Function.Pullback.fst_fstPreimageEquiv_symm_apply (x : X) (z : g ⁻¹' {f x}) :
    ((Pullback.fstPreimageEquiv x).symm z : f.Pullback g).fst = x :=
  (rfl)

@[simp]
theorem Function.Pullback.snd_fstPreimageEquiv_symm_apply (x : X) (z : g ⁻¹' {f x}) :
    ((Pullback.fstPreimageEquiv x).symm z : f.Pullback g).snd = z :=
  (rfl)
