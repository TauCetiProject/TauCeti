/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Action.End
import Mathlib.Algebra.Group.AddChar

/-!
# Automorphisms as permutations, inner automorphisms, and powers of endomorphism families

The permutation underlying an automorphism, `MulAut.toPerm`, acts as the automorphism does, and
it determines the automorphism by `MulEquiv.toEquiv_injective`. This moves `orderOf` and cycle
arguments from automorphisms to permutations.

For groups, conjugating the inner automorphism `MulAut.conj g` by an automorphism `φ` gives
`MulAut.conj (φ g)`, and transport of automorphisms along an isomorphism, `MulAut.congr`, is
functorial and carries `MulAut.conj g` to `MulAut.conj (e g)`.

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

## Main definitions

* `MonoidHom.subtypePerm`: the restriction of a permutation representation to an invariant
  subset.

## Main results

* `MulAut.toPerm_apply`: the permutation underlying an automorphism applies as the automorphism.
* `List.prod_smul`, `List.inv_prod_smul`: evaluation of a list product and its inverse in a monoid
  or group action as a right fold and a left fold of inverse actions.
* `List.prod_mulAut_apply`, `List.inv_prod_mulAut_apply`: evaluation of a list product of
  automorphisms and its inverse as a right fold and a left fold of inverse applications.
* `MulAut.mul_conj_mul_inv`: `φ * conj g * φ⁻¹ = conj (φ g)`.
* `MulAut.congr_conj`: transport along an isomorphism `e` sends `conj g` to `conj (e g)`.
* `MulAut.congr_refl`, `MulAut.congr_symm`, `MulAut.congr_trans`: functoriality of `MulAut.congr`.
* `TauCeti.Monoid.End.pow_eq_of_add_eq_comp`: `f k ^ m = f (k * m)` in `Monoid.End M`.
-/

public section

namespace List

/-- Evaluating a list product in a monoid action applies the factors from right to left. -/
theorem prod_smul {M α : Type*} [Monoid M] [MulAction M α] (l : List M) (a : α) :
    l.prod • a = l.foldr (· • ·) a := by
  induction l with
  | nil => simp
  | cons m l ih => simp [mul_smul, ih]

/-- Evaluating the inverse of a list product in a group action applies the inverse factors from
left to right. -/
theorem inv_prod_smul {G α : Type*} [Group G] [MulAction G α] (l : List G) (a : α) :
    (l.prod)⁻¹ • a = l.foldl (fun x g => g⁻¹ • x) a := by
  induction l generalizing a with
  | nil => simp
  | cons g l ih => simp [mul_inv_rev, mul_smul, ih]

/-- Evaluating a list product of automorphisms applies them from right to left. -/
theorem prod_mulAut_apply {M : Type*} [Monoid M] (fs : List (MulAut M)) (x : M) :
    fs.prod x = fs.foldr (fun f y => f y) x := by
  simpa only [MulAut.smul_def] using fs.prod_smul x

/-- Evaluating the inverse of a list product of automorphisms applies the inverse automorphisms from
left to right. -/
theorem inv_prod_mulAut_apply {M : Type*} [Monoid M] (fs : List (MulAut M)) (x : M) :
    (fs.prod)⁻¹ x = fs.foldl (fun y f => f⁻¹ y) x := by
  simpa only [MulAut.smul_def] using fs.inv_prod_smul x

end List

namespace MulAut

/-- The permutation underlying an automorphism acts as the automorphism does. -/
@[simp]
theorem toPerm_apply {M : Type*} [Mul M] (f : MulAut M) (x : M) : toPerm M f x = f x := rfl

section Group

variable {G H K : Type*} [Group G] [Group H] [Group K]

/-- Conjugating the inner automorphism by `g` by an automorphism `φ` gives the inner automorphism
by `φ g`. -/
theorem mul_conj_mul_inv (φ : MulAut G) (g : G) : φ * conj g * φ⁻¹ = conj (φ g) := by
  ext x
  simp

/-- Transporting the inner automorphism by `g` along an isomorphism `e` gives the inner
automorphism by `e g`. -/
theorem congr_conj (e : G ≃* H) (g : G) : congr e (conj g) = conj (e g) := by
  ext x
  simp

@[simp]
theorem congr_refl : congr (MulEquiv.refl G) = MulEquiv.refl (MulAut G) := by
  ext φ x
  simp

@[simp]
theorem congr_symm (e : G ≃* H) : (congr e).symm = congr e.symm :=
  (rfl)

@[simp]
theorem congr_trans (e : G ≃* H) (f : H ≃* K) : congr (e.trans f) = (congr e).trans (congr f) := by
  ext φ x
  simp

end Group

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
