/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-!
# Faithful functors reflect zero objects

A faithful functor preserving zero morphisms reflects zero objects: if `F.obj X` is a zero object
then `F` sends `𝟙 X` and `0` to the same morphism, so `𝟙 X = 0`. This complements Mathlib's
`CategoryTheory.Functor.map_isZero`, and Mathlib's
`CategoryTheory.Limits.IsZero.of_full_of_faithful_of_isZero`, which asks for fullness instead of
the preservation of zero morphisms.
-/

public section

namespace CategoryTheory.Functor

open Limits

universe v v' u u'

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  {D : Type u'} [Category.{v'} D] [HasZeroMorphisms D]

/-- A faithful functor preserving zero morphisms reflects zero objects. -/
theorem isZero_of_isZero_obj (F : C ⥤ D) [F.PreservesZeroMorphisms] [F.Faithful] {X : C}
    (hX : IsZero (F.obj X)) : IsZero X :=
  (IsZero.iff_id_eq_zero X).2 (F.map_injective (by simpa using hX.eq_of_src _ _))

end CategoryTheory.Functor
