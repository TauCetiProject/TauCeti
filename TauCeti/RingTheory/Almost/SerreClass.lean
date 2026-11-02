/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Abelian.SerreClass.MorphismProperty
public import TauCeti.Algebra.Category.ModuleCat.Annihilated
public import TauCeti.RingTheory.Almost.BasicSetup

/-!
# The Serre class of almost zero modules

For a basic setup `(V, m)`, the almost zero `V`-modules, those killed by the idempotent ideal `m`,
form a Serre class of the abelian category `ModuleCat V`: they contain `0` and are closed under
submodules, quotients and extensions. Closure under extensions is where `m * m = m` enters; the
flatness of `m ⊗[V] m` is not used. The category of almost `V`-modules is the Serre quotient of
`ModuleCat V` by this class, that is, its localization at the morphism property
`S.almostZero.isoModSerre` of morphisms whose categorical kernel and cokernel are almost zero.

This file registers the Serre class and identifies `S.almostZero.isoModSerre` with the almost
isomorphisms of `TauCeti.Almost.BasicSetup.IsAlmostIso`, which are defined through the
module-theoretic kernel and cokernel. For the classical setup `(V, V)` these morphisms are exactly
the isomorphisms, so the Serre quotient changes nothing, and for the zero setup `(V, 0)` every
morphism is one.

## Main results

* `TauCeti.Almost.BasicSetup.almostZero_isSerreClass`: almost zero modules form a Serre class.
* `TauCeti.Almost.BasicSetup.isAlmostIso_iff_isoModSerre`: a morphism of `V`-modules is an almost
  isomorphism iff it is an isomorphism modulo almost zero modules.
* `TauCeti.Almost.BasicSetup.isoModSerre_classical` and
  `TauCeti.Almost.BasicSetup.isoModSerre_zero`: the isomorphisms modulo almost zero modules for
  the classical and the zero setups.

## References

* O. Gabber, L. Ramero, *Almost ring theory*, Lecture Notes in Mathematics 1800, §2.2, (2.2.2).
* P. Scholze, *Perfectoid spaces*, Publ. Math. IHÉS 116 (2012), §4, Lemma 4.2.
-/

public section

universe u v

open CategoryTheory

namespace TauCeti.Almost.BasicSetup

variable {V : Type u} [CommRing V] (S : BasicSetup V)

/-- **Almost zero modules form a Serre class** of `ModuleCat V` (Gabber–Ramero (2.2.2), Scholze,
*Perfectoid spaces*, Lemma 4.2). The category of almost `V`-modules is the Serre quotient of
`ModuleCat V` by this class. -/
instance almostZero_isSerreClass :
    (S.almostZero : ObjectProperty (ModuleCat.{v} V)).IsSerreClass := by
  have : (S.almostZero : ObjectProperty (ModuleCat.{v} V)) =
      fun M : ModuleCat.{v} V ↦ Module.IsTorsionBySet V M (S.ideal : Set V) :=
    funext fun M ↦ propext ((S.almostZero_iff M).trans isAlmostZero_iff_isTorsionBySet)
  rw [this]
  exact S.ideal.isSerreClass_isTorsionBySet S.isIdempotentElem

/-- **A morphism of `V`-modules is an almost isomorphism iff it is an isomorphism modulo almost
zero modules**, that is, iff it is inverted by the Serre quotient by almost zero modules. -/
theorem isAlmostIso_iff_isoModSerre {M N : ModuleCat.{v} V} (f : M ⟶ N) :
    S.IsAlmostIso f.hom ↔ S.almostZero.isoModSerre f := by
  rw [ObjectProperty.isoModSerre_iff, ObjectProperty.monoModSerre_iff,
    ObjectProperty.epiModSerre_iff, S.almostZero.prop_iff_of_iso (ModuleCat.kernelIsoKer f),
    S.almostZero.prop_iff_of_iso (ModuleCat.cokernelIsoRangeQuotient f), almostZero_iff,
    almostZero_iff]
  exact isAlmostIso_iff

/-- For the classical setup, the isomorphisms modulo almost zero modules are exactly the
isomorphisms of `V`-modules. -/
@[simp]
theorem isoModSerre_classical :
    (classical V).almostZero.isoModSerre = MorphismProperty.isomorphisms (ModuleCat.{v} V) := by
  ext M N f
  rw [← isAlmostIso_iff_isoModSerre, isAlmostIso_classical_iff,
    MorphismProperty.isomorphisms.iff, ConcreteCategory.isIso_iff_bijective]

/-- For the zero setup, every morphism of `V`-modules is an isomorphism modulo almost zero
modules. -/
@[simp]
theorem isoModSerre_zero :
    (zero V).almostZero.isoModSerre = (⊤ : MorphismProperty (ModuleCat.{v} V)) := by
  ext M N f
  simpa only [MorphismProperty.top_apply, iff_true] using
    (isAlmostIso_iff_isoModSerre _ f).mp (isAlmostIso_zero f.hom)

end TauCeti.Almost.BasicSetup
