/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.AddChar

/-!
# Automorphisms as permutations, powers of indexed endomorphisms, and commuting self-maps

The permutation underlying an automorphism, `MulAut.toPerm`, acts as the automorphism does, and
it determines the automorphism by `MulEquiv.toEquiv_injective`. This moves `orderOf` and cycle
arguments from automorphisms to permutations.

A permutation representation `ρ : Γ →* Equiv.Perm α` restricts, through Mathlib's
`Equiv.Perm.subtypePerm`, to every subset that each `ρ g` preserves (`MonoidHom.subtypePerm`).

A family `f : ℕ → M →* M` of endomorphisms of a type with multiplication and a distinguished
one, indexed additively so that `f 0` is the identity and `f (a + b)` is the composite of `f a`
and `f b`, is an additive character `AddChar ℕ (Monoid.End M)`. Thus multiplication of indices
corresponds to powers in the endomorphism monoid: the `m`-th power of `f k` is `f (k * m)`.
No associativity or identity laws for multiplication on `M` are needed.

This is the shape of the iteration laws of an iterated Frobenius, `Frob_0 = id` and
`Frob_(a + b) = Frob_a ∘ Frob_b`, and the lemma packages Mathlib's `AddChar.map_nsmul_eq_pow`
for that shape once, so that each Chevalley carrier only supplies its two iteration laws.

Multiplication in `Monoid.End M` and `AddMonoid.End M` is composition, recorded as
`IsMulApplyEqComp` instances so that Mathlib's `mul_apply_eq_comp` applies to them. Commuting
elements of any such type of self-maps commute on each point (`Commute.apply_apply`).

## Main definitions

* `MonoidHom.subtypePerm`: the restriction of a permutation representation to an invariant
  subset.

## Main results

* `MulAut.toPerm_apply`: the permutation underlying an automorphism applies as the automorphism.
* `TauCeti.Monoid.End.pow_eq_of_add_eq_comp`: `f k ^ m = f (k * m)` in `Monoid.End M`.
* `Commute.apply_apply`: if `f * g = g * f` and multiplication is composition, then
  `f (g x) = g (f x)`.
-/

public section

namespace MulAut

/-- The permutation underlying an automorphism acts as the automorphism does. -/
@[simp]
theorem toPerm_apply {M : Type*} [Mul M] (f : MulAut M) (x : M) : toPerm M f x = f x := rfl

end MulAut

namespace MonoidHom

open Equiv

variable {Γ α : Type*} [MulOneClass Γ]

/-- The restriction of a permutation representation to a subset that every `ρ g` preserves. -/
def subtypePerm (ρ : Γ →* Perm α) (p : α → Prop) (h : ∀ g x, p (ρ g x) ↔ p x) :
    Γ →* Perm {x // p x} where
  toFun g := (ρ g).subtypePerm (h g)
  map_one' := by ext; simp
  map_mul' g g' := by ext x; exact DFunLike.congr_fun (map_mul ρ g g') (x : α)

@[simp]
theorem subtypePerm_apply (ρ : Γ →* Perm α) (p : α → Prop) (h : ∀ g x, p (ρ g x) ↔ p x)
    (g : Γ) : ρ.subtypePerm p h g = (ρ g).subtypePerm (h g) :=
  (rfl)

theorem subtypePerm_apply_coe (ρ : Γ →* Perm α) (p : α → Prop) (h : ∀ g x, p (ρ g x) ↔ p x)
    (g : Γ) (x : {x // p x}) : (ρ.subtypePerm p h g x : α) = ρ g x :=
  (rfl)

end MonoidHom

instance Monoid.End.instIsMulApplyEqComp {M : Type*} [MulOne M] :
    IsMulApplyEqComp (Monoid.End M) where

instance AddMonoid.End.instIsMulApplyEqComp {M : Type*} [AddZero M] :
    IsMulApplyEqComp (AddMonoid.End M) where

/-- Commuting self-maps, multiplied by composition, commute on each point. -/
theorem Commute.apply_apply {F α : Type*} [FunLike F α α] [Mul F] [IsMulApplyEqComp F]
    {f g : F} (h : Commute f g) (x : α) : f (g x) = g (f x) := by
  rw [← mul_apply_eq_comp, h.eq, mul_apply_eq_comp]

namespace TauCeti

variable {M : Type*} [MulOne M]

/-- **Indices multiply under taking powers** in the endomorphism monoid: if `f 0` is the identity
and `f (a + b) = f a ∘ f b`, then the `m`-th power of `f k` is `f (k * m)`. -/
-- `Monoid.End` is definitionally a bundled `MonoidHom`; the `show` picks its composition monoid
-- structure before the power is elaborated.
theorem Monoid.End.pow_eq_of_add_eq_comp (f : ℕ → M →* M) (h0 : f 0 = MonoidHom.id M)
    (hadd : ∀ a b, f (a + b) = (f a).comp (f b)) (k m : ℕ) :
    (show Monoid.End M from f k) ^ m = f (k * m) := by
  let ψ : AddChar ℕ (Monoid.End M) :=
    { toFun := fun j => f j
      map_zero_eq_one' := h0
      map_add_eq_mul' := hadd }
  have hpow := AddChar.map_nsmul_eq_pow ψ m k
  -- Expose the function supplied to `AddChar.mk` and the natural-number scalar action.
  change f (m * k) = (show Monoid.End M from f k) ^ m at hpow
  rw [Nat.mul_comm] at hpow
  exact hpow.symm

end TauCeti
