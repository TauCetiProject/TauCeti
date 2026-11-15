/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Algebra.DualNumber
import TauCeti.AlgebraicGeometry.AlgebraicSpace.Basic

/-!
# Examples of algebraic spaces

The functor of points of every scheme is an algebraic space: the spectrum of a field, the empty
scheme and the nonreduced spectrum of the dual numbers alike. The identity of a functor of points
is an étale atlas, including for the empty scheme. On the other hand no morphism from the empty
scheme to the spectrum of a field is an étale atlas, as it is not surjective, and the constant
presheaf with two values is not an algebraic space, as it is not an fppf sheaf: an fppf sheaf has
a single section over the empty scheme.
-/

open CategoryTheory Limits Opposite AlgebraicGeometry TauCeti.AlgebraicGeometry Spaces

universe u

-- The spectrum of a field is an algebraic space.
example (k : Type u) [Field k] : IsAlgebraicSpace (yoneda.obj (Spec (.of k))) :=
  .yoneda_obj _

-- The empty scheme is an algebraic space, with the identity as an étale atlas.
example : IsAlgebraicSpace (yoneda.obj (∅ : Scheme.{u})) := .yoneda_obj _

example : EtaleAtlas (𝟙 (yoneda.obj (∅ : Scheme.{u}))) := .of_isIso _

-- Nilpotents are allowed: the spectrum of the dual numbers is an algebraic space.
example (k : Type u) [Field k] :
    IsAlgebraicSpace (yoneda.obj (Spec (.of (DualNumber k)))) :=
  .yoneda_obj _

-- The diagonal of every scheme is representable, with no separatedness hypothesis.
example (X : Scheme.{u}) : RepresentableDiagonal (yoneda.obj X) := .yoneda_obj X

-- No morphism from the empty scheme to the spectrum of a field is an étale atlas: it is not
-- surjective.
example (k : Type u) [Field k] (a : yoneda.obj (∅ : Scheme.{u}) ⟶ yoneda.obj (Spec (.of k))) :
    ¬ EtaleAtlas a := by
  rw [← yoneda.map_preimage a, etaleAtlas_yoneda_map_iff]
  rintro ⟨-, h⟩
  obtain ⟨x, -⟩ := (yoneda.preimage a).surjective (Nonempty.some inferInstance)
  exact IsEmpty.elim inferInstance x

-- The constant presheaf with two values is not an algebraic space: it has two sections over the
-- empty scheme.
example : ¬ IsAlgebraicSpace ((Functor.const Scheme.{u}ᵒᵖ).obj (ULift.{u} Bool)) := fun h ↦ by
  -- The empty family covers the empty scheme, so an fppf sheaf has a single section over it.
  have e := Types.isTerminalEquivUnique _ (Sheaf.isTerminalOfBotCover ⟨_, h.isSheaf⟩ ∅
    (Scheme.bot_mem_grothendieckTopology (∅ : Scheme.{u})))
  simpa using (e.uniq (ULift.up true)).trans (e.uniq (ULift.up false)).symm
