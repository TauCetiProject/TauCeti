/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Deck.Basic
public import Mathlib.GroupTheory.GroupAction.Basic

/-!
# The action of deck transformations on a fibre

A deck transformation preserves every fibre of the projection. This file packages that
restriction as a multiplicative homomorphism from the deck transformation group to the
homeomorphism group of a chosen fibre, and records the induced action on that fibre.

The comparison between deck transformations and the fundamental group, and the regular-cover
statements, use the action of deck transformations on individual fibres rather than only on the
total space.

## Main definitions

* `TauCeti.Deck.fiberHomeomorphHom`: the homomorphism
  `deck p →* (p ⁻¹' {b} ≃ₜ p ⁻¹' {b})`.
* `TauCeti.Deck.instFiberMulAction`: the induced action of `deck p` on the fibre over `b`.
* `deck.mem_fiber_stabilizer_iff_coe`: membership in a fibre stabilizer is equality
  on the underlying point.
-/

public section

namespace TauCeti

namespace Deck

variable {E B : Type*} [TopologicalSpace E] {p : E → B} {b : B}

/-- The homomorphism from deck transformations to homeomorphisms of the fibre over `b`.

It sends a deck transformation to its restriction to the subtype `p ⁻¹' {b}`. -/
@[expose] def fiberHomeomorphHom (p : E → B) (b : B) : deck p →* (p ⁻¹' {b} ≃ₜ p ⁻¹' {b}) where
  toFun φ := deck.fiberHomeomorph φ b
  map_one' := by
    ext e
    rfl
  map_mul' φ ψ := by
    ext e
    rfl

/-- The fibre homomorphism evaluates by applying the deck transformation to the underlying
point of the fibre. -/
@[simp]
lemma _root_.deck.fiberHomeomorphHom_apply (φ : deck p) (e : p ⁻¹' {b}) :
    fiberHomeomorphHom p b φ e = deck.fiberHomeomorph φ b e :=
  rfl

/-- On underlying points, the fibre homomorphism is evaluation of the underlying
homeomorphism. -/
@[simp]
lemma _root_.deck.fiberHomeomorphHom_apply_coe (φ : deck p) (e : p ⁻¹' {b}) :
    (fiberHomeomorphHom p b φ e : E) = φ.1 e.1 :=
  rfl

/-- The fibre homomorphism sends the identity deck transformation to the identity
homeomorphism of the fibre. -/
@[simp]
lemma fiberHomeomorphHom_one :
    fiberHomeomorphHom p b (1 : deck p) = 1 := by
  exact (fiberHomeomorphHom p b).map_one

/-- The fibre homomorphism sends products of deck transformations to products of fibre
homeomorphisms. -/
@[simp]
lemma _root_.deck.fiberHomeomorphHom_mul (φ ψ : deck p) :
    fiberHomeomorphHom p b (φ * ψ) = fiberHomeomorphHom p b φ * fiberHomeomorphHom p b ψ := by
  exact (fiberHomeomorphHom p b).map_mul φ ψ

/-- The fibre homomorphism sends inverses of deck transformations to inverses of fibre
homeomorphisms. -/
@[simp]
lemma _root_.deck.fiberHomeomorphHom_inv (φ : deck p) :
    fiberHomeomorphHom p b φ⁻¹ = (fiberHomeomorphHom p b φ)⁻¹ := by
  exact (fiberHomeomorphHom p b).map_inv φ

/-- The fibre homeomorphism associated to the identity deck transformation is the identity. -/
@[simp]
lemma fiberHomeomorph_one :
    deck.fiberHomeomorph (1 : deck p) b = 1 := by
  exact fiberHomeomorphHom_one

/-- The fibre homeomorphism associated to a product is the product of the associated fibre
homeomorphisms. -/
@[simp]
lemma _root_.deck.fiberHomeomorph_mul (φ ψ : deck p) :
    deck.fiberHomeomorph (φ * ψ) b = deck.fiberHomeomorph φ b * deck.fiberHomeomorph ψ b := by
  exact deck.fiberHomeomorphHom_mul φ ψ

/-- The fibre homeomorphism associated to an inverse is the inverse of the associated fibre
homeomorphism. -/
@[simp]
lemma _root_.deck.fiberHomeomorph_inv (φ : deck p) :
    deck.fiberHomeomorph φ⁻¹ b = (deck.fiberHomeomorph φ b)⁻¹ := by
  exact deck.fiberHomeomorphHom_inv φ

/-- The fibre homeomorphism associated to a natural-number power is the corresponding power
of the associated fibre homeomorphism. -/
@[simp]
lemma _root_.deck.fiberHomeomorph_pow (φ : deck p) (n : ℕ) :
    deck.fiberHomeomorph (φ ^ n) b = deck.fiberHomeomorph φ b ^ n := by
  exact (fiberHomeomorphHom p b).map_pow φ n

/-- The fibre homeomorphism associated to an integer power is the corresponding power of the
associated fibre homeomorphism. -/
@[simp]
lemma _root_.deck.fiberHomeomorph_zpow (φ : deck p) (n : ℤ) :
    deck.fiberHomeomorph (φ ^ n) b = deck.fiberHomeomorph φ b ^ n := by
  exact (fiberHomeomorphHom p b).map_zpow φ n

/-- Deck transformations act on each fibre by restricting their action on the total space. -/
instance instFiberMulAction : MulAction (deck p) (p ⁻¹' {b}) :=
  MulAction.compHom (p ⁻¹' {b}) (fiberHomeomorphHom p b)

/-- The fibre action is evaluation of the fibre homeomorphism. -/
lemma _root_.deck.fiber_smul_eq_fiberHomeomorph (φ : deck p) (e : p ⁻¹' {b}) :
    φ • e = deck.fiberHomeomorph φ b e :=
  rfl

/-- On underlying points, the fibre action is evaluation of the underlying deck
transformation. -/
@[simp]
lemma _root_.deck.fiber_smul_coe (φ : deck p) (e : p ⁻¹' {b}) :
    ((φ • e : p ⁻¹' {b}) : E) = φ.1 e.1 :=
  rfl

/-- The projection value of a point in the fibre is unchanged after the restricted deck
action. -/
lemma _root_.deck.map_fiber_smul (φ : deck p) (e : p ⁻¹' {b}) :
    p (φ • e : E) = b := by
  exact (φ • e).2

/-- The restricted deck action keeps points in the fibre over `b`. -/
lemma _root_.deck.fiber_smul_mem (φ : deck p) (e : p ⁻¹' {b}) : (φ • e : E) ∈ p ⁻¹' {b} := by
  exact deck.map_fiber_smul φ e

/-- The restricted fibre action agrees with the ambient action on the total space after
coercing out of the fibre subtype. -/
lemma _root_.deck.fiber_smul_coe_eq_smul (φ : deck p) (e : p ⁻¹' {b}) :
    ((φ • e : p ⁻¹' {b}) : E) = φ • (e : E) := by
  trans φ.1 e.1
  · exact deck.fiber_smul_coe φ e
  · exact (deck.smul_eq_apply φ (e : E)).symm

/-- Membership in the stabilizer of a fibre point is equality on the underlying point. -/
@[grind =]
lemma _root_.deck.mem_fiber_stabilizer_iff_coe (φ : deck p) (e : p ⁻¹' {b}) :
    φ ∈ MulAction.stabilizer (deck p) e ↔ φ.1 e.1 = e.1 := by
  simp [Subtype.ext_iff, deck.fiber_smul_eq_fiberHomeomorph]

end Deck

end TauCeti
