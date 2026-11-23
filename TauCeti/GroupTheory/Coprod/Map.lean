/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Coprod.Basic
import Mathlib.Algebra.Group.ULift
import Mathlib.Algebra.Ring.Int.Defs
import TauCeti.GroupTheory.CoprodI
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

-- The case of `map_injective` for two families of monoids indexed by `Bool`.
private theorem map_injective_of_bool {A B : Bool → Type*} [∀ b, Monoid (A b)] [∀ b, Monoid (B b)]
    {f : A false →* B false} {g : A true →* B true} (hf : Function.Injective f)
    (hg : Function.Injective g) : Function.Injective (map f g) := by
  let F (b : Bool) : A b →* B b := Bool.rec f g b
  have key : map f g = (CoprodI.boolEquivCoprod B).toMonoidHom.comp
      ((CoprodI.lift fun b => CoprodI.of.comp (F b)).comp
        (CoprodI.boolEquivCoprod A).symm.toMonoidHom) := by
    ext <;> simp [F]
  rw [key]
  exact (CoprodI.boolEquivCoprod B).injective.comp
    ((CoprodI.lift_of_comp_injective fun b => by cases b; exacts [hf, hg]).comp
      (CoprodI.boolEquivCoprod A).symm.injective)

variable {M : Type u} {N : Type v} {M' : Type u'} {N' : Type v'} [MulOneClass M] [MulOneClass N]
  [Monoid M'] [Monoid N']

-- Injectivity of `map` is invariant under isomorphisms of the four factors.
private theorem map_injective_of_mulEquiv {M₁ N₁ M₁' N₁' : Type*} [MulOneClass M₁] [MulOneClass N₁]
    [MulOneClass M₁'] [MulOneClass N₁'] (eM : M₁ ≃* M) (eN : N₁ ≃* N) (eM' : M₁' ≃* M')
    (eN' : N₁' ≃* N') {f : M →* M'} {g : N →* N'}
    (h : Function.Injective (map (eM'.symm.toMonoidHom.comp (f.comp eM.toMonoidHom))
      (eN'.symm.toMonoidHom.comp (g.comp eN.toMonoidHom)))) :
    Function.Injective (map f g) := by
  have key : map f g = (MulEquiv.coprodCongr eM' eN').toMonoidHom.comp
      ((map (eM'.symm.toMonoidHom.comp (f.comp eM.toMonoidHom))
        (eN'.symm.toMonoidHom.comp (g.comp eN.toMonoidHom))).comp
          (MulEquiv.coprodCongr eM.symm eN.symm).toMonoidHom) := by
    ext <;> simp
  rw [key]
  exact (MulEquiv.coprodCongr eM' eN').injective.comp
    (h.comp (MulEquiv.coprodCongr eM.symm eN.symm).injective)

/-- The free product `Monoid.Coprod.map f g : M ∗ N →* M' ∗ N'` of two injective homomorphisms
into monoids, sending `inl x` to `inl (f x)` and `inr y` to `inr (g y)`, is injective. Only `M'` and
`N'` are assumed associative: `M` and `N` then are too, since they embed in them. The version for an
arbitrary family of factors is `Monoid.CoprodI.lift_of_comp_injective`. -/
theorem map_injective {f : M →* M'} {g : N →* N'} (hf : Function.Injective f)
    (hg : Function.Injective g) : Function.Injective (map f g) := by
  -- `M` and `N` are monoids, since they embed in the monoids `M'` and `N'`.
  let _ : Monoid M := { ‹MulOneClass M› with mul_assoc a b c := hf (by simp [mul_assoc]) }
  let _ : Monoid N := { ‹MulOneClass N› with mul_assoc a b c := hg (by simp [mul_assoc]) }
  -- Lift the factors to common universes, so that `M`, `N` and `M'`, `N'` are families over `Bool`.
  let _ : ∀ b, Monoid (cond b (ULift.{u} N) (ULift.{v} M))
    | false => inferInstanceAs (Monoid (ULift M))
    | true => inferInstanceAs (Monoid (ULift N))
  let _ : ∀ b, Monoid (cond b (ULift.{u'} N') (ULift.{v'} M'))
    | false => inferInstanceAs (Monoid (ULift M'))
    | true => inferInstanceAs (Monoid (ULift N'))
  refine map_injective_of_mulEquiv MulEquiv.ulift MulEquiv.ulift MulEquiv.ulift MulEquiv.ulift
    (map_injective_of_bool (A := fun b => cond b (ULift.{u} N) (ULift.{v} M))
      (B := fun b => cond b (ULift.{u'} N') (ULift.{v'} M')) ?_ ?_)
  exacts [MulEquiv.ulift.symm.injective.comp (hf.comp MulEquiv.ulift.injective),
    MulEquiv.ulift.symm.injective.comp (hg.comp MulEquiv.ulift.injective)]

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
