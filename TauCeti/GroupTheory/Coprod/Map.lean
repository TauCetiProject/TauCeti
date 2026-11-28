/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Coprod.Basic
import Mathlib.Algebra.Ring.Int.Defs
import TauCeti.Algebra.Group.ULift
import TauCeti.GroupTheory.Coprod.Factors
import TauCeti.GroupTheory.CoprodI.Word

/-!
# Free products of injective homomorphisms

Injective homomorphisms `f : M →* M'` and `g : N →* N'` into monoids induce an injective
homomorphism `Monoid.Coprod.map f g : M ∗ N →* M' ∗ N'` of free products. This is the case of two
factors of `Monoid.CoprodI.lift_of_comp_injective`, which rests on the normal form of free products:
every element is the product of exactly one reduced word, and injective homomorphisms send reduced
words to reduced words. For instance, doubling on both factors of `ℤ ∗ ℤ` is injective, and the free
monoid `ℕ ∗ ℕ` on two letters embeds in the free group `ℤ ∗ ℤ` on two letters.

## Main results

* `Monoid.Coprod.map_injective`: the free product of injective homomorphisms is injective.

## References

* R. C. Lyndon, P. E. Schupp, *Combinatorial group theory*, Springer, 1977, Chapter IV, §1
  (the normal form theorem for free products of groups).
* J. M. Howie, *Fundamentals of semigroup theory*, Oxford University Press, 1995, §8.2 (the normal
  form for free products of monoids).
-/

public section

universe u v u' v'

namespace Monoid.Coprod

variable {M : Type u} {N : Type v} {M' : Type u'} {N' : Type v'} [MulOneClass M] [MulOneClass N]
  [Monoid M'] [Monoid N']

/-- The free product `Monoid.Coprod.map f g : M ∗ N →* M' ∗ N'` of two injective homomorphisms
into monoids, sending `inl x` to `inl (f x)` and `inr y` to `inr (g y)`, is injective. Only `M'` and
`N'` are assumed associative: `M` and `N` then are too, since they embed in them. The version for an
arbitrary family of factors is `Monoid.CoprodI.lift_of_comp_injective`. -/
theorem map_injective {f : M →* M'} {g : N →* N'} (hf : Function.Injective f)
    (hg : Function.Injective g) : Function.Injective (map f g) := by
  -- `M` and `N` are monoids, since they embed in the monoids `M'` and `N'`.
  let _ : Monoid M := { ‹MulOneClass M› with mul_assoc a b c := hf (by simp [mul_assoc]) }
  let _ : Monoid N := { ‹MulOneClass N› with mul_assoc a b c := hg (by simp [mul_assoc]) }
  -- Through `equivCoprodI`, `map f g` is the free product of the family of maps of factors over
  -- `Bool` that is `f` at `false` and `g` at `true`, lifted to common universes.
  let F (b : Bool) : Factors M N b →* Factors M' N' b :=
    Bool.rec (motive := fun b => Factors M N b →* Factors M' N' b)
      (MulEquiv.ulift.symm.toMonoidHom.comp (f.comp MulEquiv.ulift.toMonoidHom))
      (MulEquiv.ulift.symm.toMonoidHom.comp (g.comp MulEquiv.ulift.toMonoidHom)) b
  have key : map f g = equivCoprodI.symm.toMonoidHom.comp
      ((CoprodI.lift fun b => CoprodI.of.comp (F b)).comp equivCoprodI.toMonoidHom) := by
    ext <;> simp [F]
  rw [key]
  exact equivCoprodI.symm.injective.comp ((CoprodI.lift_of_comp_injective fun b => by
    cases b
    exacts [MulEquiv.ulift.symm.injective.comp (hf.comp MulEquiv.ulift.injective),
      MulEquiv.ulift.symm.injective.comp (hg.comp MulEquiv.ulift.injective)]).comp
    equivCoprodI.injective)

/-- Doubling `n ↦ 2 n` on both factors of `ℤ ∗ ℤ` (written multiplicatively, `x ↦ x ^ 2`) is
injective. -/
example : Function.Injective
    (map (powMonoidHom 2 : Multiplicative ℤ →* _) (powMonoidHom 2 : Multiplicative ℤ →* _)) :=
  have h : Function.Injective (powMonoidHom 2 : Multiplicative ℤ →* _) :=
    fun a b hab => by simpa using congrArg Multiplicative.toAdd hab
  map_injective h h

/-- The free monoid `ℕ ∗ ℕ` on two letters embeds in the free group `ℤ ∗ ℤ` on two letters. -/
example : Function.Injective
    (map (Nat.castAddMonoidHom ℤ).toMultiplicative (Nat.castAddMonoidHom ℤ).toMultiplicative) :=
  have h : Function.Injective (Nat.castAddMonoidHom ℤ).toMultiplicative :=
    fun a b hab => by simpa using congrArg Multiplicative.toAdd hab
  map_injective h h

end Monoid.Coprod
