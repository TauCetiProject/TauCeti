/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Free.ProP

/-!
# The free pro-`p` group on no generators

The free pro-`p` group on an empty type is trivial. Its universal property makes every
continuous endomorphism equal: two such maps agree on the empty set of generators. In
particular it is topologically isomorphic to the one-element group.

This is the zero-generator case of the free pro-`p` construction used in finite-rank
presentations. The argument works for any empty type and does not require `p` to be prime.
-/

public section

namespace TauCeti

universe u

variable (p : ℕ) (X : Type u) [IsEmpty X]

namespace freeProP

private noncomputable def trivialEndomorphism : freeProP p X →ₜ* freeProP p X :=
  ⟨(1 : freeProP p X →* freeProP p X), continuous_const⟩

/-- A free pro-`p` group on an empty type has only one element. -/
instance instSubsingletonOfIsEmpty : Subsingleton (freeProP p X) := by
  apply Subsingleton.intro
  intro x y
  have h : ContinuousMonoidHom.id (freeProP p X) = trivialEndomorphism p X := by
    apply hom_ext
    intro i
    exact isEmptyElim i
  calc
    x = (trivialEndomorphism p X) x := congrFun (congrArg DFunLike.coe h) x
    _ = (trivialEndomorphism p X) y := rfl
    _ = y := (congrFun (congrArg DFunLike.coe h) y).symm

/-- The free pro-`p` group on an empty type is the one-element group, including its topology. -/
noncomputable def equivPUnitOfIsEmpty : freeProP p X ≃ₜ* PUnit := by
  letI : Unique (freeProP p X) := uniqueOfSubsingleton 1
  exact ContinuousMulEquiv.ofUnique

end freeProP

end TauCeti
