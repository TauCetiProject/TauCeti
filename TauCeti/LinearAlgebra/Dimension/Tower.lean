/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.RankNullity

/-!
# Rank is additive along a tower of submodules

For submodules `p ≤ q ≤ r` of a module `M`, the relative quotient `r / p` is filtered by `q / p`,
and `TauCeti.rank_quotient_submoduleOf_tower` records that its rank is the sum of the ranks of the
two steps.  Relative quotients are spelled with `Submodule.submoduleOf`, so that `q / p` means
`↥q ⧸ p.submoduleOf q`.

It is the case of Mathlib's `LinearMap.rank_quot_submodule_map_eq` for the inclusion `q → r`,
which rests on rank–nullity; this is why the base ring is asked only for `HasRankNullity`.
-/

public section

universe u v

namespace TauCeti

/-- Rank is additive along a tower `p ≤ q ≤ r` of submodules: the relative quotients of the two
steps add up to the relative quotient of the composite. -/
theorem rank_quotient_submoduleOf_tower {R : Type v} {M : Type u} [Ring R] [AddCommGroup M]
    [Module R M] [HasRankNullity.{u} R] {p q r : Submodule R M} (hpq : p ≤ q) (hqr : q ≤ r) :
    Module.rank R (↥r ⧸ p.submoduleOf r) =
      Module.rank R (↥q ⧸ p.submoduleOf q) + Module.rank R (↥r ⧸ q.submoduleOf r) := by
  have hp : (p.submoduleOf q).map (Submodule.inclusion hqr) = p.submoduleOf r := by
    ext ⟨x, hx⟩
    simpa [Submodule.submoduleOf, Subtype.ext_iff] using fun h => hpq h
  rw [← hp, LinearMap.rank_quot_submodule_map_eq, add_comm]
  congr 1
  · refine (Submodule.Quotient.equiv _ _
      (LinearEquiv.ofInjective _ (Submodule.inclusion_injective hqr)) ?_).rank_eq.symm
    exact congrArg (Submodule.map · _) (by ext; simp)
  · rw [Submodule.range_inclusion, Submodule.submoduleOf]

end TauCeti
