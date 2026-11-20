/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.ExponentialGroup.Basic

/-!
# Homomorphisms commuting with exponentiation

For monoids `G` and `H` with exponentiations `g ^ a` by the elements of a type `A`, a
`ExponentialHom A G H` is a monoid homomorphism `f : G →* H` with `f (g ^ a) = f g ^ a`. Between
groups with exponents in a ring `A` (`TauCeti.IsExponentialGroup`) these are the
*`A`-homomorphisms*, the morphisms of the category of `A`-groups in which the `A`-completion of a
group is defined.

## Main definitions

* `TauCeti.ExponentialHom A G H`: the monoid homomorphisms `G →* H` commuting with exponentiation
  by `A`.
* `TauCeti.ExponentialHom.id`, `TauCeti.ExponentialHom.comp`: identity and composition.
* `TauCeti.IsExponentialGroup.powHom g`: the `A`-homomorphism `Multiplicative A → G`,
  `ofAdd a ↦ g ^ a`, for an element `g` of an `A`-group over a commutative semiring `A`.

## Implementation notes

`powHom` uses the exponentiation `ofAdd a ^ b = ofAdd (b * a)` of `Multiplicative A` by `A`, a
scoped instance activated by `open scoped TauCeti.IsExponentialGroup.MultiplicativePow`.

## References

* A. G. Myasnikov, V. N. Remeslennikov, D. E. Serbin, *Regular free length functions on Lyndon's
  free `ℤ[t]`-group `F^{ℤ[t]}`*, §2.1.
-/

public section

namespace TauCeti

/-- A monoid homomorphism commuting with exponentiation by the elements of `A`. Between
`A`-groups, these are the `A`-homomorphisms. -/
structure ExponentialHom (A G H : Type*) [MulOneClass G] [MulOneClass H] [Pow G A] [Pow H A]
    extends G →* H where
  /-- The homomorphism commutes with exponentiation. -/
  map_pow' (g : G) (a : A) : toFun (g ^ a) = toFun g ^ a

namespace ExponentialHom

variable {A G H K L : Type*} [MulOneClass G] [MulOneClass H] [MulOneClass K] [MulOneClass L]
  [Pow G A] [Pow H A] [Pow K A] [Pow L A]

instance : FunLike (ExponentialHom A G H) G H where
  coe f := f.toFun
  coe_injective f g h := by
    obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := f
    obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := g
    congr

instance : MonoidHomClass (ExponentialHom A G H) G H where
  map_mul f := f.map_mul'
  map_one f := f.map_one'

@[ext]
theorem ext {f f' : ExponentialHom A G H} (h : ∀ g, f g = f' g) : f = f' :=
  DFunLike.ext f f' h

@[simp]
theorem coe_toMonoidHom (f : ExponentialHom A G H) : ⇑f.toMonoidHom = f := by
  rfl

@[simp]
theorem coe_mk (f : G →* H) (hf : ∀ (g : G) (a : A), f (g ^ a) = f g ^ a) :
    ⇑(⟨f, hf⟩ : ExponentialHom A G H) = f := by
  rfl

theorem toMonoidHom_injective : Function.Injective (toMonoidHom : ExponentialHom A G H → G →* H) :=
  fun _ _ h => ext fun g => DFunLike.congr_fun h g

/-- An `A`-homomorphism commutes with exponentiation. -/
@[simp]
protected theorem map_pow (f : ExponentialHom A G H) (g : G) (a : A) : f (g ^ a) = f g ^ a :=
  f.map_pow' g a

variable (A G) in
/-- The identity, as a homomorphism commuting with exponentiation. -/
protected def id : ExponentialHom A G G where
  toMonoidHom := MonoidHom.id G
  map_pow' _ _ := rfl

@[simp]
theorem coe_id : ⇑(ExponentialHom.id A G) = id := by
  rfl

@[simp]
theorem toMonoidHom_id : (ExponentialHom.id A G).toMonoidHom = MonoidHom.id G := by
  rfl

/-- The composite of two homomorphisms commuting with exponentiation. -/
def comp (f : ExponentialHom A H K) (f' : ExponentialHom A G H) : ExponentialHom A G K where
  toMonoidHom := f.toMonoidHom.comp f'.toMonoidHom
  map_pow' g a := by simp

@[simp]
theorem coe_comp (f : ExponentialHom A H K) (f' : ExponentialHom A G H) :
    ⇑(f.comp f') = f ∘ f' := by
  rfl

theorem comp_apply (f : ExponentialHom A H K) (f' : ExponentialHom A G H) (g : G) :
    f.comp f' g = f (f' g) := by
  rfl

@[simp]
theorem toMonoidHom_comp (f : ExponentialHom A H K) (f' : ExponentialHom A G H) :
    (f.comp f').toMonoidHom = f.toMonoidHom.comp f'.toMonoidHom := by
  rfl

@[simp]
theorem comp_id (f : ExponentialHom A G H) : f.comp (ExponentialHom.id A G) = f := by
  rfl

@[simp]
theorem id_comp (f : ExponentialHom A G H) : (ExponentialHom.id A H).comp f = f := by
  rfl

theorem comp_assoc (f : ExponentialHom A K L) (f' : ExponentialHom A H K)
    (f'' : ExponentialHom A G H) : (f.comp f').comp f'' = f.comp (f'.comp f'') := by
  rfl

end ExponentialHom

namespace IsExponentialGroup

open scoped MultiplicativePow

variable (A : Type*) {G : Type*} [CommSemiring A] [Group G] [Pow G A] [IsExponentialGroup A G]

/-- For an element `g` of an `A`-group over a commutative semiring `A`, the homomorphism
`Multiplicative A → G`, `ofAdd a ↦ g ^ a`; it commutes with exponentiation, where
`Multiplicative A` carries `ofAdd a ^ b = ofAdd (b * a)`. -/
def powHom (g : G) : ExponentialHom A (Multiplicative A) G where
  toFun x := g ^ x.toAdd
  map_one' := by rw [toAdd_one, IsExponentialGroup.pow_zero]
  map_mul' x y := by rw [toAdd_mul, IsExponentialGroup.pow_add]
  map_pow' x a := by
    rw [Multiplicative.toAdd_multiplicativePow, smul_eq_mul, mul_comm, IsExponentialGroup.pow_mul]

@[simp]
theorem powHom_apply (g : G) (x : Multiplicative A) : powHom A g x = g ^ x.toAdd := by
  rfl

end IsExponentialGroup

end TauCeti
