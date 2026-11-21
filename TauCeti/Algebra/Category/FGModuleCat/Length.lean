/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.CategoryTheory.ObjectProperty.EpiMono
public import Mathlib.RingTheory.Length
public import TauCeti.CategoryTheory.Abelian.Length
import Mathlib.Algebra.Category.FGModuleCat.Limits
import TauCeti.Algebra.Category.ModuleCat.Length
import TauCeti.CategoryTheory.Subobject.FullSubcategory

/-!
# The length of a finitely generated module as an object of `FGModuleCat`

Over a left Noetherian ring `A`, submodules of finitely generated modules are finitely generated,
so the finitely generated modules are closed under subobjects in `ModuleCat A`
(`ModuleCat.isFG_isClosedUnderSubobjects`). Hence the subobjects of a finitely generated module in
`FGModuleCat A` are its submodules, and its length `CategoryTheory.length X` as an object of
`FGModuleCat A` is its length as a module (`FGModuleCat.length_eq`).

## Main results

* `ModuleCat.isFG_isClosedUnderSubobjects`: over a left Noetherian ring, finitely generated modules
  are closed under subobjects.
* `FGModuleCat.length_eq`: over a left Noetherian ring,
  `CategoryTheory.length X = Module.length A X.obj`.

## Implementation notes

The subobject lattices of `X` in `FGModuleCat A` and in `ModuleCat A` are identified by
`CategoryTheory.ObjectProperty.subobjectOrderIso`, and the length in `ModuleCat A` is compared with
the length of modules by `ModuleCat.length_eq`.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Chapter VI, Section 1.
-/

public section

open CategoryTheory

universe w v

variable {A : Type v} [Ring A] [IsNoetherianRing A]

/-- **Over a left Noetherian ring, finitely generated modules are closed under subobjects**: a
submodule of a finitely generated module is finitely generated. -/
instance ModuleCat.isFG_isClosedUnderSubobjects :
    (ModuleCat.isFG.{w} A).IsClosedUnderSubobjects where
  prop_of_mono f _ hY := by
    rw [ModuleCat.isFG_iff] at hY ⊢
    exact Module.Finite.of_injective f.hom ((ModuleCat.mono_iff_injective f).1 inferInstance)

/-- **The length of a finitely generated module as an object of `FGModuleCat A`** is its length as
a module, over a left Noetherian ring `A`. -/
theorem FGModuleCat.length_eq (X : FGModuleCat.{w} A) : length X = Module.length A X.obj :=
  have : (ModuleCat.isFG.{w} A).ι.PreservesMonomorphisms :=
    inferInstanceAs (forget₂ (FGModuleCat.{w} A) (ModuleCat.{w} A)).PreservesMonomorphisms
  (length_eq_of_orderIso ((ModuleCat.isFG A).subobjectOrderIso X)).trans (ModuleCat.length_eq X.obj)
