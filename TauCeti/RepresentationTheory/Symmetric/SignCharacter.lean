/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Perm.Sign

/-!
# The sign character of a symmetric group

Mathlib's `Equiv.Perm.sign` is valued in `ℤˣ`. Representation theory wants the *linear character*
it induces over a coefficient ring: the homomorphism `Equiv.Perm α →* kˣ` obtained by pushing the
sign forward along `ℤ → k`. That is `TauCeti.signLinearCharacter`, and it is the `sgn` of the
character tables and of the induction examples -- the one-dimensional representation it carries is
`FDRep.ofLinearCharacter (signLinearCharacter k α)`, and restricting it along a subgroup inclusion
is precomposition, so a subgroup meets it as `(signLinearCharacter k α).comp H.subtype`.

The facts needed to compute with it are recorded here: its value in `k` is the sign cast into `k`,
it sends a transposition to `-1`, and over a commutative ring it squares to the trivial character.
In characteristic two `-1 = 1`, so the character is trivial; every statement that needs it to be
nontrivial has to say so by excluding that characteristic.

## Main definitions

* `TauCeti.signLinearCharacter`: the sign of a permutation, as a linear character valued in `kˣ`.

## Main statements

* `TauCeti.coe_signLinearCharacter_apply`: its value in `k` is the sign of the permutation, cast.
* `TauCeti.signLinearCharacter_swap`: it sends a transposition to `-1`.
* `TauCeti.signLinearCharacter_mul_self`: its square is the trivial character.
-/

public section

namespace TauCeti

universe u v

/-- **The sign character of a symmetric group**: the linear character of `Equiv.Perm α` sending a
permutation to its sign, read in the units of `k` along the ring homomorphism `ℤ → k`. -/
def signLinearCharacter (k : Type u) [Ring k] (α : Type v) [DecidableEq α] [Fintype α] :
    Equiv.Perm α →* kˣ :=
  (Units.map (Int.castRingHom k).toMonoidHom).comp Equiv.Perm.sign

variable {k : Type u} [Ring k] {α : Type v} [DecidableEq α] [Fintype α]

/-- **The value of the sign character in `k` is the sign, cast into `k`.** This is the defining
equation: the definition itself is not exposed, and every computation with the character goes
through this lemma and `TauCeti.signLinearCharacter_swap`. -/
@[simp]
theorem coe_signLinearCharacter_apply (σ : Equiv.Perm α) :
    (signLinearCharacter k α σ : k) = ((Equiv.Perm.sign σ : ℤ) : k) :=
  -- `(rfl)`, not `rfl`: the body of `signLinearCharacter` is not `@[expose]`d, so this must not
  -- be inferred `@[defeq]`.
  (rfl)

/-- **The sign character sends a transposition to `-1`.** Over a ring of characteristic two this
value is `1`, which is why nontriviality of the character always carries a hypothesis on the
characteristic. -/
@[simp]
theorem signLinearCharacter_swap {i j : α} (h : i ≠ j) :
    signLinearCharacter k α (Equiv.swap i j) = -1 := by
  ext
  simp [h]

/-- **The sign character squares to the trivial character.** -/
@[simp]
theorem signLinearCharacter_mul_self {k : Type u} [CommRing k] :
    signLinearCharacter k α * signLinearCharacter k α = 1 := by
  ext
  simp [← Int.cast_mul]

end TauCeti
