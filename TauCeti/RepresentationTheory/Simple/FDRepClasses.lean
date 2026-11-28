/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.AsModule
public import TauCeti.RepresentationTheory.Simple.Basic
public import TauCeti.RingTheory.Semisimple.RegularIsotypicComponent

/-!
# Comparing the isomorphism classes of simple objects with the module-level classes

A classification of representations is a bijection onto isomorphism classes, and the same group can
be classified in two languages: over the isomorphism classes of simple objects of `FDRep k G`,
which is `TauCeti.SimpleClasses (FDRep k G)`, and over the isomorphism classes of simple
`k[G]`-modules, which over a semisimple group algebra is
`TauCeti.SimpleSubmoduleClasses k[G] k[G]`. Two bijections onto two targets are not yet one
theorem read twice; what makes them one is a comparison of the targets.

`TauCeti.SimpleClasses.toSimpleSubmoduleClasses` is that comparison: it sends a simple object
to the isomorphism class of the `k[G]`-module it carries. It is well defined because isomorphic
objects carry isomorphic modules, by `TauCeti.nonempty_fdRepIso_iff` followed by
`TauCeti.Representation.nonempty_equiv_iff`, and injective because that chain of equivalences runs
backwards just as well. See `TauCeti.coe_simpleFDRepClassesEquivSimpleModuleClasses` for the
symmetric group, where the comparison identifies the two classifications by the partitions of `n`.

## Main results

* `TauCeti.SimpleClasses.toSimpleSubmoduleClasses`: over a semisimple group algebra, the
  isomorphism class of the `k[G]`-module a simple object carries.
* `TauCeti.SimpleClasses.toSimpleSubmoduleClasses_injective`: distinct classes of simple objects
  carry distinct classes of modules, so the comparison identifies the categorical classification
  with a part of the module-level one.
-/

public section

open CategoryTheory

namespace TauCeti

open scoped MonoidAlgebra

universe u v

namespace SimpleClasses

section Field

variable {k : Type u} {G : Type v} [Field k] [Monoid G]

/-- **The isomorphism class of the `k[G]`-module a simple object of `FDRep k G` carries.** Over a
semisimple group algebra this compares the categorical classification with the module-level one of
`TauCeti.SimpleSubmoduleClasses`. -/
noncomputable def toSimpleSubmoduleClasses [IsSemisimpleRing k[G]]
    (S : SimpleClasses (FDRep k G)) : SimpleSubmoduleClasses k[G] k[G] :=
  simpleModuleClass k[G] (_root_.Representation.asModule S.repr.ρ)

@[simp]
theorem toSimpleSubmoduleClasses_classOf [IsSemisimpleRing k[G]] (X : FDRep k G) [Simple X] :
    toSimpleSubmoduleClasses (classOf X) =
      simpleModuleClass k[G] (_root_.Representation.asModule X.ρ) := by
  rw [toSimpleSubmoduleClasses, simpleModuleClass_eq_iff]
  exact Representation.nonempty_equiv_iff.mp (nonempty_fdRepIso_iff.mp ⟨classOfReprIso X⟩)

/-- **The comparison is injective**: two simple objects of `FDRep k G` carrying isomorphic
`k[G]`-modules are isomorphic, so the fibres of the comparison are single classes. This is the
well-definedness argument run backwards. -/
theorem toSimpleSubmoduleClasses_injective [IsSemisimpleRing k[G]] :
    Function.Injective (toSimpleSubmoduleClasses : SimpleClasses (FDRep k G) → _) := by
  intro S T h
  rw [toSimpleSubmoduleClasses, toSimpleSubmoduleClasses, simpleModuleClass_eq_iff,
    ← Representation.nonempty_equiv_iff, ← nonempty_fdRepIso_iff] at h
  exact (eq_iff_nonempty_iso S T).mpr h

end Field

end SimpleClasses

end TauCeti
