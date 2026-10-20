/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Preadditive.Radical.Basic
public import TauCeti.CategoryTheory.Preadditive.MorphismIdeal.Mul

/-!
# The radical of a preadditive category as an ideal

The radical `TauCeti.jacobsonRadical` of a preadditive category is a two-sided ideal
(`TauCeti.jacobsonRadicalIdeal`). Its powers in the monoid of ideals are the powers `radⁿ` of the
radical. The square agrees with the existing `TauCeti.jacobsonRadicalSq`
(`TauCeti.jacobsonRadicalIdeal_sq_hom`), so `rad²` is the case `n = 2` of the general powers.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995).
-/

public section

namespace TauCeti

open CategoryTheory

universe v u

variable (C : Type u) [Category.{v} C] [Preadditive C]

/-- The radical of a preadditive category, as a two-sided ideal. -/
def jacobsonRadicalIdeal : MorphismIdeal C where
  hom := jacobsonRadical
  comp_mem_left := fun f _ hg ↦ comp_mem_jacobsonRadical_left f hg
  comp_mem_right := fun g hf ↦ comp_mem_jacobsonRadical_right hf g

variable {C}

@[simp]
theorem jacobsonRadicalIdeal_hom (X Y : C) :
    (jacobsonRadicalIdeal C).hom X Y = jacobsonRadical X Y :=
  (rfl)

/-- The square of the radical ideal is the square of the radical, `rad²`. -/
theorem jacobsonRadicalIdeal_sq_hom (X Y : C) :
    (jacobsonRadicalIdeal C ^ 2).hom X Y = jacobsonRadicalSq X Y := by
  rw [pow_two]
  exact le_antisymm
    (MorphismIdeal.mul_hom_le_iff.mpr fun _ _ _ ha hb ↦ comp_mem_jacobsonRadicalSq ha hb)
    (jacobsonRadicalSq_le_iff.mpr fun _ _ _ ha hb ↦ MorphismIdeal.comp_mem_mul ha hb)

end TauCeti
