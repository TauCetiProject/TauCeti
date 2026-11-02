/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.NoncommPiCoprod

/-!
# Homomorphisms out of `ℤ^ι`

A homomorphism out of the free abelian group `ι → Multiplicative ℤ` on a finite type `ι` is
determined by the images of the standard generators `Pi.mulSingle i (ofAdd 1)`
(`MonoidHom.pi_ext_mint`), and any family of pairwise commuting elements `τ i` of a group `K` is
the image of the standard generators under `TauCeti.zpowersPiHom τ`, built from Mathlib's
`MonoidHom.noncommPiCoprod` and `zpowersHom`.

## Main declarations

* `MonoidHom.pi_ext_mint`: homomorphisms out of `ι → Multiplicative ℤ` agreeing on the standard
  generators are equal.
* `TauCeti.zpowersPiHom τ`: the homomorphism `(ι → Multiplicative ℤ) →* K` sending the `i`-th
  standard generator to `τ i`.
* `TauCeti.commute_zpowersPiHom`: an element commuting with every `τ i` commutes with the image of
  `zpowersPiHom τ`.
-/

public section

variable {ι : Type*}

namespace MonoidHom

/-- Homomorphisms out of `ι → Multiplicative ℤ` agree when they agree on the standard
generators. -/
theorem pi_ext_mint [Finite ι] [DecidableEq ι] {M : Type*} [Monoid M]
    {f g : (ι → Multiplicative ℤ) →* M}
    (h : ∀ i, f (Pi.mulSingle i (.ofAdd 1)) = g (Pi.mulSingle i (.ofAdd 1))) : f = g :=
  pi_ext fun i x => by
    simpa using DFunLike.congr_fun
      (ext_mint (f := f.comp (mulSingle (fun _ => Multiplicative ℤ) i))
        (g := g.comp (mulSingle (fun _ => Multiplicative ℤ) i)) (h i)) x

end MonoidHom

namespace TauCeti

variable [Fintype ι] {K : Type*} [Group K]

/-- The homomorphism `(ι → Multiplicative ℤ) →* K` sending the `i`-th standard generator to `τ i`,
for pairwise commuting `τ i`. -/
def zpowersPiHom (τ : ι → K) (hτ : ∀ i j, Commute (τ i) (τ j)) :
    (ι → Multiplicative ℤ) →* K :=
  MonoidHom.noncommPiCoprod (fun i => zpowersHom K (τ i)) <| by
    intro i j _ x y
    simpa only [zpowersHom_apply] using (hτ i j).zpow_zpow x.toAdd y.toAdd

@[simp] theorem zpowersPiHom_mulSingle [DecidableEq ι] (τ : ι → K)
    (hτ : ∀ i j, Commute (τ i) (τ j)) (i : ι) :
    zpowersPiHom τ hτ (Pi.mulSingle i (.ofAdd 1)) = τ i :=
  -- `simp` does not unify the `ι`-indexed family of `noncommPiCoprod_mulSingle` with the constant
  -- family `ι → Multiplicative ℤ`, so apply it directly.
  (MonoidHom.noncommPiCoprod_mulSingle _ i _).trans (by simp)

/-- An element commuting with every `τ i` commutes with the whole image of `zpowersPiHom τ`. -/
theorem commute_zpowersPiHom {τ : ι → K} {hτ : ∀ i j, Commute (τ i) (τ j)} {x : K}
    (hx : ∀ i, Commute x (τ i)) (v : ι → Multiplicative ℤ) :
    Commute x (zpowersPiHom τ hτ v) :=
  MonoidHom.commute_noncommPiCoprod _ (fun i k => by
    simpa only [zpowersHom_apply] using (hx i).zpow_right k.toAdd) v

end TauCeti
