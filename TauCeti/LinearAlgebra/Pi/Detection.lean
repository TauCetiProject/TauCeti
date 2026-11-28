/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs

/-!
# Modules of functions detected by a set of points

A submodule `Z` of the module of functions `G → B` is *detected* by a set `s ⊆ G` if its only
member vanishing on `s` is zero: a member of `Z` is determined by its values on `s`. A module of
functions detected by a finite set `s` embeds, after restriction, in `s → B`, which bounds its
length (`Submodule.IsDetectedBy.length_le`, in `TauCeti.RingTheory.Length`).

## Main definitions

* `Submodule.IsDetectedBy Z s`: the only member of `Z` vanishing on `s` is zero.

## Main results

* `Submodule.isDetectedBy_iff`: unfolding `Submodule.IsDetectedBy`.
-/

public section

namespace Submodule

variable {O G B : Type*} [Semiring O] [AddCommMonoid B] [Module O B]

/-- A module `Z` of functions on `G` is *detected* by `s ⊆ G` if its only member vanishing on `s`
is zero. -/
def IsDetectedBy (Z : Submodule O (G → B)) (s : Set G) : Prop :=
  ∀ c ∈ Z, (∀ g ∈ s, c g = 0) → c = 0

/-- Unfolding `Submodule.IsDetectedBy`. -/
theorem isDetectedBy_iff {Z : Submodule O (G → B)} {s : Set G} :
    Z.IsDetectedBy s ↔ ∀ c ∈ Z, (∀ g ∈ s, c g = 0) → c = 0 :=
  Iff.rfl

end Submodule
