/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.EssentiallySmall
public import TauCeti.Algebra.Category.FiniteHopfModuleCat.Basic

/-!
# Finite-dimensional algebra modules form an essentially small category

For a field `k : Type u` and a `k`-algebra `H : Type v`, the category
`FiniteHopfModuleCat k H` is essentially small in the universe `max u v`. Its morphism types
already lie in `Type u`, so the point is that its isomorphism classes form a small set.

A module finite-dimensional over `k` is finitely generated over `H`, so the inclusion into
`ModuleCat H` lifts to a fully faithful functor into Mathlib's `FGModuleCat H`, which Mathlib
proves essentially small in the universe of `H`.

Essential smallness is what split Grothendieck groups `TauCeti.SplitK0` of the category, such as
representation rings of Hopf algebras, require.
-/

public noncomputable section

open CategoryTheory

namespace TauCeti.FiniteHopfModuleCat

universe u v

variable {k : Type u} [Field k] {H : Type v} [Ring H] [Algebra k H]

/-- **Finite-dimensional modules over a `k`-algebra form an essentially small category**, in
the universe `max u v` of the field `k : Type u` and the algebra `H : Type v`. -/
instance essentiallySmall : EssentiallySmall.{max u v} (FiniteHopfModuleCat k H) := by
  have : EssentiallySmall.{v} (FiniteHopfModuleCat k H) :=
    essentiallySmall_of_fully_faithful
      ((ModuleCat.isFG H).lift (incl k H) fun M =>
        (ModuleCat.isFG_iff _).2 (Module.Finite.of_restrictScalars_finite k H M))
  exact (essentiallySmall_iff _).2 ⟨small_lift _, locallySmall_max⟩

end TauCeti.FiniteHopfModuleCat
