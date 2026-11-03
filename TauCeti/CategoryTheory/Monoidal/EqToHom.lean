/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Functor

/-!
# Tensor products of transports along object equalities

The tensor product of two morphisms `eqToHom h` and `eqToHom h'` is the transport along the induced
equality of tensor products. This complements Mathlib's `MonoidalCategory.whiskerLeft_eqToHom` and
`MonoidalCategory.eqToHom_whiskerRight`, which treat whiskering.

Likewise, the inverse of an invertible tensor comparison `δ F a b` of an oplax monoidal functor
followed by `F` applied to a transport of `a ⊗ b` is the transport of `F a ⊗ F b` followed by the
inverse tensor comparison at the transported factors.

## Main results

* `TauCeti.eqToHom_tensorHom_eqToHom`: `eqToHom h ⊗ₘ eqToHom h' = eqToHom _`.
* `TauCeti.inv_δ_comp_map_eqToHom`: transporting `inv (δ F a b)` along `a = a'` and `b = b'`.
-/

public section

open CategoryTheory MonoidalCategory

universe v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The tensor product of two transports along object equalities is the transport along the
induced equality of tensor products. -/
@[simp]
theorem eqToHom_tensorHom_eqToHom {X X' Y Y' : C} (h : X = X') (h' : Y = Y') :
    (eqToHom h ⊗ₘ eqToHom h') = eqToHom (congrArg₂ (· ⊗ ·) h h') := by
  subst h h'
  simp

/-- The inverse tensor comparison of an oplax monoidal functor commutes with transports along
identifications of the factors. -/
@[reassoc]
theorem inv_δ_comp_map_eqToHom {D : Type*} [Category D] [MonoidalCategory D] (F : C ⥤ D)
    [F.OplaxMonoidal] {a a' b b' : C} [IsIso (Functor.OplaxMonoidal.δ F a b)]
    [IsIso (Functor.OplaxMonoidal.δ F a' b')] (ha : a = a') (hb : b = b') (h : a ⊗ b = a' ⊗ b') :
    inv (Functor.OplaxMonoidal.δ F a b) ≫ F.map (eqToHom h) =
      eqToHom (by rw [ha, hb]) ≫ inv (Functor.OplaxMonoidal.δ F a' b') := by
  subst ha hb
  simp

end TauCeti
