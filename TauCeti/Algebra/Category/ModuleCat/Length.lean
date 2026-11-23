/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.RingTheory.Length
public import TauCeti.CategoryTheory.Subobject.Length
import Mathlib.Algebra.Category.ModuleCat.Subobject

/-!
# The length of a module as an object of `ModuleCat`

The length `CategoryTheory.length M` of a module `M` as an object of the abelian category
`ModuleCat A` is its length `Module.length A M` as a module (`ModuleCat.length_eq`): both are the
Krull dimension of the lattice of subobjects, which is the lattice of submodules. Through it, the
statements about lengths of objects of abelian categories, such as the Harada–Sai lemma
(`TauCeti.map_eq_zero_of_length_le`), apply to modules.

## Main results

* `ModuleCat.length_eq`: `CategoryTheory.length M = Module.length A M`.

## Implementation notes

Mathlib's `ModuleCat.subobjectModule` identifies the subobjects of `M` with its submodules.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Chapter VI, Section 1.
-/

public section

open CategoryTheory

universe v u

/-- **The length of a module as an object of `ModuleCat A` is its length as a module.** -/
theorem ModuleCat.length_eq {A : Type u} [Ring A] (M : ModuleCat.{v} A) :
    length M = Module.length A M :=
  WithBot.coe_injective (by
    rw [coe_length, Module.coe_length, Order.krullDim_eq_of_orderIso (subobjectModule M)])
