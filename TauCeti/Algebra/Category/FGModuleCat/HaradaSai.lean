/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.Length
public import TauCeti.Algebra.Category.FGModuleCat.Basic
public import TauCeti.CategoryTheory.Preadditive.Radical.Basic
import Mathlib.RingTheory.HopkinsLevitzki
import TauCeti.Algebra.Category.FGModuleCat.KrullSchmidt
import TauCeti.Algebra.Category.FGModuleCat.Length
import TauCeti.CategoryTheory.Abelian.HaradaSai

/-!
# The nilpotency index of the radical of `mod A`

Let `A` be a left Artinian ring, for instance an Artin algebra, and suppose that every finitely
generated indecomposable `A`-module has length at most `b`. Then the `(2 ^ b - 1)`-th power of the
radical of the category `FGModuleCat A` of finitely generated `A`-modules vanishes
(`FGModuleCat.jacobsonRadicalIdeal_pow_eq_bot_of_length_le`).

The motivating case is a representation-finite algebra `A`, whose finitely generated
indecomposable modules have bounded length (`TauCeti.IsRepresentationFinite.exists_length_le`), so
that the radical of `mod A` is nilpotent with an explicit bound on the exponent. The theorem itself
assumes only the length bound, not representation-finiteness.

## Main results

* `FGModuleCat.jacobsonRadicalIdeal_pow_eq_bot_of_length_le`: over a left Artinian ring whose
  finitely generated indecomposable modules have length at most `b`, the `(2 ^ b - 1)`-th power
  of the radical of `FGModuleCat A` vanishes.

## Implementation notes

Over a left Artinian ring, hence left Noetherian ring (Hopkins–Levitzki), `FGModuleCat A` is
abelian, and it is Krull-Schmidt (`FGModuleCat.isKrullSchmidt_of_isArtinianRing`). The radical
bound is the case of `FGModuleCat A` of the bound for Krull-Schmidt abelian categories whose
indecomposable objects have bounded length (`TauCeti.jacobsonRadicalIdeal_pow_eq_bot_of_length_le`),
which rests on the Harada–Sai lemma. The length of a finitely generated module as an object of
`FGModuleCat A` is its length as a module (`FGModuleCat.length_eq`).

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Corollary VI.1.3 and the discussion after it.
* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras, Vol. 1*, Cambridge University Press (2006), Lemma IV.5.2.
* M. Harada and Y. Sai, *On categories of indecomposable modules. I*, Osaka J. Math. 7 (1970),
  323–344.
-/

public section

namespace FGModuleCat

open CategoryTheory CategoryTheory.Limits TauCeti

universe w v

/-- **The radical of `mod A` is nilpotent of index at most `2 ^ b - 1`** when every finitely
generated indecomposable module over the left Artinian ring `A` has length at most `b`: the
`(2 ^ b - 1)`-th power of the radical of `FGModuleCat A` vanishes. -/
theorem jacobsonRadicalIdeal_pow_eq_bot_of_length_le {A : Type v} [Ring A] [IsArtinianRing A]
    {b : ℕ} (h : ∀ X : FGModuleCat.{w} A, Indecomposable X.obj → Module.length A X.obj ≤ b) :
    jacobsonRadicalIdeal (FGModuleCat.{w} A) ^ (2 ^ b - 1) = ⊥ :=
  TauCeti.jacobsonRadicalIdeal_pow_eq_bot_of_length_le
    fun X hX ↦ (length_eq X).trans_le (h X ((indecomposable_obj_iff X).mpr hX))

end FGModuleCat
