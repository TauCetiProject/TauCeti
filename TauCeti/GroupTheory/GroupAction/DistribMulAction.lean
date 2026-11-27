/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.Basic
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Negation under an action by additive automorphisms

When a group `G` acts on an additive group `α` by additive automorphisms
(`DistribMulAction G α`), negation commutes with the action (`smul_neg`). Hence `-a` and `a`
have the same stabilizer, and negation descends to an involution of the orbit space, computed on
representatives.

## Main declarations

* `MulAction.stabilizer_neg`: `-a` and `a` have the same stabilizer;
* `MulAction.orbitRel.Quotient.instInvolutiveNeg`: negation of orbits;
* `MulAction.orbitRel.Quotient.neg_mk`: the negative of the orbit of `a` is the orbit of `-a`.
-/

public section

namespace MulAction

variable {G α : Type*} [Group G] [AddGroup α] [DistribMulAction G α]

/-- Under an action by additive automorphisms, `-a` and `a` have the same stabilizer. -/
@[simp]
theorem stabilizer_neg (a : α) : stabilizer G (-a) = stabilizer G a := by
  ext g
  simp only [mem_stabilizer_iff, smul_neg, neg_inj]

namespace orbitRel.Quotient

/-- Under an action by additive automorphisms, negation maps orbits to orbits, so it descends to
an involution of the orbit space. -/
instance instInvolutiveNeg : InvolutiveNeg (orbitRel.Quotient G α) where
  neg := Quotient.map' (-·) fun a b h ↦ by
    obtain ⟨g, hg⟩ := mem_orbit_iff.mp (orbitRel_apply.mp h)
    exact orbitRel_apply.mpr (mem_orbit_iff.mpr ⟨g, by rw [smul_neg, hg]⟩)
  neg_neg q := Quotient.inductionOn' q fun a ↦ congrArg Quotient.mk'' (neg_neg a)

/-- The negative of the orbit of `a` is the orbit of `-a`. -/
@[simp]
theorem neg_mk (a : α) :
    -(Quotient.mk'' a : orbitRel.Quotient G α) = Quotient.mk'' (-a) :=
  (rfl)

end orbitRel.Quotient

end MulAction
