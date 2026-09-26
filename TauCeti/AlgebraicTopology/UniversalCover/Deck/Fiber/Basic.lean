/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Deck.Basic
public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.GroupTheory.GroupAction.SubMulAction

/-!
# The action of deck transformations on a fibre

A deck transformation preserves every fibre of the projection, so each fibre of `p` is a
`deck p`-stable subset of the total space. This file records that fibre as a `SubMulAction`,
so that the action of `deck p` on it is the restriction of the tautological action on the total
space and the two agree on underlying points by definition, and packages the same restriction as
a multiplicative homomorphism to the homeomorphism group of the fibre.

The comparison between deck transformations and the fundamental group, and the regular-cover
statements, use the action of deck transformations on individual fibres rather than only on the
total space.

## Main definitions

* `TauCeti.Deck.fiberHomeomorphHom`: the homomorphism
  `deck p →* (p ⁻¹' {b} ≃ₜ p ⁻¹' {b})`.
* `TauCeti.Deck.fiberSubMulAction`: the fibre over `b` as a `deck p`-stable subset of the
  total space, and `TauCeti.Deck.instFiberMulAction`: the action of `deck p` it carries.
* `deck.fiber_stabilizer_eq_stabilizer_coe`: the stabilizer of a fibre point is the
  stabilizer of the underlying point of the total space, and
  `deck.mem_fiber_stabilizer_iff_coe`: membership in a fibre stabilizer is equality on the
  underlying point.
-/

public section

namespace TauCeti

namespace Deck

variable {E B : Type*} [TopologicalSpace E] {p : E → B} {b : B}

/-- The homomorphism from deck transformations to homeomorphisms of the fibre over `b`.

It sends a deck transformation to its restriction to the subtype `p ⁻¹' {b}`. -/
def fiberHomeomorphHom (p : E → B) (b : B) : deck p →* (p ⁻¹' {b} ≃ₜ p ⁻¹' {b}) where
  toFun φ := deck.fiberHomeomorph φ b
  map_one' := by
    ext e
    simp
  map_mul' φ ψ := by
    ext e
    simp

/-- The fibre homomorphism evaluates by applying the deck transformation to the underlying
point of the fibre. -/
@[simp]
lemma _root_.deck.fiberHomeomorphHom_apply (φ : deck p) (e : p ⁻¹' {b}) :
    fiberHomeomorphHom p b φ e = deck.fiberHomeomorph φ b e :=
  (rfl)

/-- The fibre homeomorphism associated to the identity deck transformation is the identity. -/
@[simp]
lemma _root_.deck.fiberHomeomorph_one :
    deck.fiberHomeomorph (1 : deck p) b = 1 :=
  map_one (fiberHomeomorphHom p b)

/-- The fibre homeomorphism associated to a product is the product of the associated fibre
homeomorphisms. -/
@[simp]
lemma _root_.deck.fiberHomeomorph_mul (φ ψ : deck p) :
    deck.fiberHomeomorph (φ * ψ) b = deck.fiberHomeomorph φ b * deck.fiberHomeomorph ψ b :=
  map_mul (fiberHomeomorphHom p b) φ ψ

/-- The fibre homeomorphism associated to an inverse is the inverse of the associated fibre
homeomorphism. -/
@[simp]
lemma _root_.deck.fiberHomeomorph_inv (φ : deck p) :
    deck.fiberHomeomorph φ⁻¹ b = (deck.fiberHomeomorph φ b)⁻¹ :=
  map_inv (fiberHomeomorphHom p b) φ

/-- The fibre homeomorphism associated to a natural-number power is the corresponding power
of the associated fibre homeomorphism. -/
@[simp]
lemma _root_.deck.fiberHomeomorph_pow (φ : deck p) (n : ℕ) :
    deck.fiberHomeomorph (φ ^ n) b = deck.fiberHomeomorph φ b ^ n :=
  map_pow (fiberHomeomorphHom p b) φ n

/-- The fibre homeomorphism associated to an integer power is the corresponding power of the
associated fibre homeomorphism. -/
@[simp]
lemma _root_.deck.fiberHomeomorph_zpow (φ : deck p) (n : ℤ) :
    deck.fiberHomeomorph (φ ^ n) b = deck.fiberHomeomorph φ b ^ n :=
  map_zpow (fiberHomeomorphHom p b) φ n

/-- The fibre of `p` over `b`, as a `deck p`-stable subset of the total space: a deck
transformation fixes the value of `p`, hence maps the fibre over `b` to itself.

The body is exposed because the subtype it denotes has to be recognised as the fibre
`p ⁻¹' {b}` itself, which is what lets the generic `SubMulAction` API apply to the fibre
action. -/
@[expose]
def fiberSubMulAction (p : E → B) (b : B) : SubMulAction (deck p) E where
  carrier := p ⁻¹' {b}
  smul_mem' φ _ he := (deck.proj_smul φ _).trans he

/-- Deck transformations act on each fibre by restricting their action on the total space. -/
instance instFiberMulAction : MulAction (deck p) (p ⁻¹' {b}) :=
  (fiberSubMulAction p b).mulAction

/-- On underlying points, the fibre action is evaluation of the underlying deck
transformation. -/
@[simp]
lemma _root_.deck.fiber_smul_coe (φ : deck p) (e : p ⁻¹' {b}) :
    ((φ • e : p ⁻¹' {b}) : E) = φ.1 e.1 :=
  (SubMulAction.val_smul (p := fiberSubMulAction p b) φ e).trans (deck.smul_eq_apply φ e.1)

/-- The fibre action is evaluation of the fibre homeomorphism. -/
lemma _root_.deck.fiber_smul_eq_fiberHomeomorph (φ : deck p) (e : p ⁻¹' {b}) :
    φ • e = deck.fiberHomeomorph φ b e :=
  Subtype.ext ((deck.fiber_smul_coe φ e).trans (deck.fiberHomeomorph_apply φ b e).symm)

/-- The stabilizer of a point of the fibre is the stabilizer of the underlying point of the
total space. -/
lemma _root_.deck.fiber_stabilizer_eq_stabilizer_coe (e : p ⁻¹' {b}) :
    MulAction.stabilizer (deck p) e = MulAction.stabilizer (deck p) (e : E) :=
  SubMulAction.stabilizer_of_subMul (p := fiberSubMulAction p b) e

/-- Membership in the stabilizer of a fibre point is equality on the underlying point. -/
@[grind =]
lemma _root_.deck.mem_fiber_stabilizer_iff_coe (φ : deck p) (e : p ⁻¹' {b}) :
    φ ∈ MulAction.stabilizer (deck p) e ↔ φ.1 e.1 = e.1 := by
  rw [deck.fiber_stabilizer_eq_stabilizer_coe]
  simp

end Deck

end TauCeti
