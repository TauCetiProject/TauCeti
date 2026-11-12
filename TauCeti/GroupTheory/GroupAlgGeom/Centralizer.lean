/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.FreeGroup.IsFreeGroup
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import TauCeti.GroupTheory.GroupAlgGeom.AlgebraicSet
public import TauCeti.GroupTheory.ProperPower
import TauCeti.GroupTheory.FreeGroup.MaximalRoot.Basic

/-!
# Centralizers as algebraic sets

Let `H` be a group receiving coefficients from `G` through `ι : G →* H`. The centralizer in `H`
of the image of a set `M` of coefficients is algebraic: it is the set of solutions of the
commutator equations `[x, m] = 1`, `m ∈ M`, in one variable `x`.

Over a free group `H`, the centralizer of an element that is not a proper power is the cyclic
group it generates. So when `ι g` is not a proper power, the solutions of the single equation
`[x, g] = 1` are the powers of `ι g`; this applies to every free generator `a` of a free group.

## Main results

* `TauCeti.GroupAlgGeom.V_image_commutatorElement`: centralizers of sets of coefficients are
  algebraic, cut out by the commutator equations `[x, m] = 1`.
* `TauCeti.GroupAlgGeom.V_singleton_commutatorElement_of_not_isProperPower`: over a free group,
  the solutions of `[x, g] = 1` for a coefficient `g` whose image is not a proper power are the
  powers of that image.
* `TauCeti.GroupAlgGeom.V_singleton_commutatorElement_of`: over a free group, the solutions of
  `[x, a] = 1` for a free generator `a` are the powers of `a`.

## References

* G. Baumslag, A. Myasnikov, V. Remeslennikov, *Algebraic geometry over groups I. Algebraic sets
  and ideal theory*, J. Algebra 219 (1999), §3.1, Example 3.
-/

public section

namespace TauCeti.GroupAlgGeom

open FreeGroup Monoid.Coprod Subgroup
open scoped commutatorElement

variable {G H X : Type*} [Group G] [Group H] {ι : G →* H}

/-- The centralizer of a set of coefficients is algebraic: the solutions of the commutator
equations `[x, m] = 1`, `m ∈ M`, in the variable `x` are the points whose `x`-coordinate
centralizes the image of `M` in `H`. -/
theorem V_image_commutatorElement (x : X) (M : Set G) :
    V ι ((fun m => ⁅(inr (of x) : GX G X), inl m⁆) '' M) = {v | v x ∈ centralizer (ι '' M)} := by
  ext v
  simp only [mem_V, Set.forall_mem_image, map_commutatorElement, eval_inr_of, eval_inl,
    commutatorElement_eq_one_iff_mul_comm, Set.mem_ofPred_eq, mem_centralizer_iff]
  exact forall₂_congr fun _ _ => eq_comm

/-- The solutions of the commutator equation `[x, g] = 1` in the variable `x` are the points whose
`x`-coordinate centralizes the image of the coefficient `g` in `H`. -/
theorem V_singleton_commutatorElement (x : X) (g : G) :
    V ι {⁅(inr (of x) : GX G X), inl g⁆} = {v | v x ∈ centralizer {ι g}} := by
  simpa using V_image_commutatorElement (ι := ι) x {g}

/-- Over a free group `H`, if the image `ι g` of the coefficient `g` is not a proper power, the
solutions of the commutator equation `[x, g] = 1` in the variable `x` are the points whose
`x`-coordinate is a power of `ι g`. -/
theorem V_singleton_commutatorElement_of_not_isProperPower [IsFreeGroup H] (x : X) {g : G}
    (hg : ¬Group.IsProperPower (ι g)) :
    V ι {⁅(inr (of x) : GX G X), inl g⁆} = {v | v x ∈ zpowers (ι g)} := by
  rw [V_singleton_commutatorElement, IsFreeGroup.centralizer_singleton_eq_zpowers_self hg]

/-- Over a free group `F`, the solutions of the commutator equation `[x, a] = 1` for a free
generator `a` are the points whose `x`-coordinate is a power of `a`. -/
theorem V_singleton_commutatorElement_of {α : Type*} (x : X) (a : α) :
    V (.id (FreeGroup α)) {⁅(inr (of x) : GX (FreeGroup α) X), inl (of a)⁆} =
      {v | v x ∈ zpowers (of a)} :=
  V_singleton_commutatorElement_of_not_isProperPower x (not_isProperPower_of a)

end TauCeti.GroupAlgGeom
