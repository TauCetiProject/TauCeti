/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Preadditive.Radical.IrreducibleMorphismQuiver.Translation
public import TauCeti.RepresentationTheory.Quiver.AuslanderReiten.Quiver
public import TauCeti.RepresentationTheory.Quiver.Representation.Translate

/-!
# Translation on the quiver of irreducible morphisms of a quiver

For a quiver with finitely many paths, the Auslander–Reiten translate `D Tr` of pointwise
finite-dimensional representations, `TauCeti.arTranslate`, is an Auslander–Reiten translation
in the sense of `TauCeti.ARTranslation` (`TauCeti.arTranslation`). Its partial translation
`(arTranslation k Q).translate` on the quiver of irreducible morphisms is therefore undefined
exactly at projective classes, and it is a bijection from the non-projective classes onto the
non-injective ones (`TauCeti.ARTranslation.existsUnique_translate_eq_some_iff`).

No algebraic closedness or representation-finiteness assumption is needed.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Sections IV.1 and VII.1.
-/

public section

namespace TauCeti

open CategoryTheory

universe u v w t

variable (k : Type u) (Q : Type v) [Field k] [Quiver.{w} Q] [Finite (Quiver.TotalPath Q)]

/-- The Auslander–Reiten translate of pointwise finite-dimensional representations, as a
translation on their isomorphism classes. -/
noncomputable def arTranslation : ARTranslation (IsFinDim.{u, v, w, max u v w t} k Q) where
  obj := arTranslate.{u, v, w, t} k Q
  prop_obj := isFinDim_arTranslate.{u, v, w, t} k Q
  nonempty_iso_obj_of_iso := nonempty_iso_arTranslate_of_iso.{u, v, w, t} k Q
  indecomposable_obj_iff := indecomposable_arTranslate_iff.{u, v, w, t} k Q
  injective_obj_iff := injective_arTranslate_iff.{u, v, w, t} k Q
  nonempty_iso_of_nonempty_iso_obj hM hN hiM hiN hpM :=
    (nonempty_iso_arTranslate_iff.{u, v, w, t} k Q hM hN hiM hiN hpM).mp
  exists_nonempty_iso_obj := exists_nonempty_iso_arTranslate.{u, v, w, t} k Q

@[simp]
theorem arTranslation_obj (M : QuiverRep.{u, v, w, max u v w t} k Q) (hM : IsFinDim k Q M) :
    (arTranslation.{u, v, w, t} k Q).obj M hM = arTranslate.{u, v, w, t} k Q M hM :=
  (rfl)

end TauCeti
