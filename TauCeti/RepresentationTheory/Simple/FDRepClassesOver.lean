/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Induction.LiesOver
public import TauCeti.RepresentationTheory.Simple.Basic

/-!
# The isomorphism classes of the simple representations lying over a constituent

Fix a homomorphism `φ : N →* H` and an `N`-representation `V`.  The simple objects of `FDRep k H`
lying over `V` along `φ` (`FDRep.LiesOver`) span a full subcategory, and this file names its
skeleton: the isomorphism classes of those representations, written `Irr(H ∣ V)` in the literature.

The type needs no new device.  `TauCeti.SimpleFDRepClasses` is already the skeleton of the full
subcategory of simple objects of `FDRep k H`; here the cutting property is the conjunction of
simplicity with `FDRep.LiesOver`, so the same constructions of
`TauCeti.RepresentationTheory.Simple.Basic` and `TauCeti.CategoryTheory.Skeletal` apply verbatim.
The classes come with the constructor `mk`, the comparison `mk_eq_mk_iff`, the eliminator `ind`,
the lift `lift` of an isomorphism-invariant function, and the injection `toSimpleFDRepClasses` that
forgets the constituent.

## Main definitions

* `TauCeti.simpleLiesOver`: being a simple representation lying over a fixed constituent, as a
  property of objects of `FDRep k H`.
* `TauCeti.SimpleFDRepClassesOver`: the isomorphism classes of those representations, `Irr(H ∣ V)`.

## Main statements

* `TauCeti.SimpleFDRepClassesOver.mk_eq_mk_iff`: two representations lying over `V` have the same
  class exactly when they are isomorphic.
* `TauCeti.SimpleFDRepClassesOver.toSimpleFDRepClasses_injective`: the classes over `V` inject into
  all simple-object classes, so no information is lost by remembering the constituent.
-/

public section

open CategoryTheory

attribute [local instance] isIsomorphicSetoid

universe u v w

namespace TauCeti

section Classes

variable {k : Type u} {N : Type v} {H : Type w} [Field k] [Group N] [Group H]

/-- Being a **simple representation lying over `V`** along `φ : N →* H`, as a property of objects
of `FDRep k H`: the property whose full subcategory has `Irr(H ∣ V)` as its skeleton. -/
def simpleLiesOver (φ : N →* H) (V : FDRep k N) : ObjectProperty (FDRep k H) :=
  fun U => Simple U ∧ U.LiesOver φ V

variable {φ : N →* H} {V : FDRep k N}

/-- An object has the property `TauCeti.simpleLiesOver φ V` exactly when it is simple and lies
over `V` along `φ`. -/
@[simp]
theorem simpleLiesOver_iff (U : FDRep k H) :
    simpleLiesOver φ V U ↔ Simple U ∧ U.LiesOver φ V :=
  (Iff.rfl)

/-- **The isomorphism classes of the simple representations lying over a fixed constituent**,
written `Irr(H ∣ V)` in the literature: the skeleton of the full subcategory of `FDRep k H` they
span.  It is the indexing type of the Clifford correspondence
`FDRep.cliffordCorrespondence`. -/
def SimpleFDRepClassesOver (φ : N →* H) (V : FDRep k N) : Type _ :=
  Skeleton (ObjectProperty.FullSubcategory (simpleLiesOver φ V))

namespace SimpleFDRepClassesOver

/-- The class of a simple representation lying over `V`. -/
def mk (U : FDRep k H) [hU : Simple U] (h : U.LiesOver φ V) : SimpleFDRepClassesOver φ V :=
  toSkeleton (⟨U, hU, h⟩ : ObjectProperty.FullSubcategory (simpleLiesOver φ V))

/-- Two simple representations lying over `V` have the same class exactly when they are
isomorphic. -/
@[simp]
theorem mk_eq_mk_iff (U U' : FDRep k H) [Simple U] [Simple U']
    (h : U.LiesOver φ V) (h' : U'.LiesOver φ V) : mk U h = mk U' h' ↔ Nonempty (U ≅ U') :=
  ObjectProperty.toSkeleton_eq_toSkeleton_iff_nonempty_iso (simpleLiesOver φ V) _ _

/-- To prove a property of every class over `V`, it suffices to prove it on the class of each
simple representation lying over `V`. -/
@[elab_as_elim]
theorem ind {motive : SimpleFDRepClassesOver φ V → Prop}
    (h : ∀ (U : FDRep k H) (hU : Simple U) (hlies : U.LiesOver φ V),
      motive (mk U (hU := hU) hlies))
    (c : SimpleFDRepClassesOver φ V) : motive c :=
  Quotient.ind (fun U ↦ h U.obj U.property.1 U.property.2) c

/-- Define a function on the classes over `V` from a function on simple representations lying over
`V` that is invariant under isomorphism. -/
noncomputable def lift {α : Sort*} (f : ∀ (U : FDRep k H) [Simple U], U.LiesOver φ V → α)
    (hf : ∀ (U U' : FDRep k H) [Simple U] [Simple U'] (h : U.LiesOver φ V)
      (h' : U'.LiesOver φ V), Nonempty (U ≅ U') → f U h = f U' h') :
    SimpleFDRepClassesOver φ V → α :=
  ObjectProperty.skeletonLift _ (fun U ↦ @f U.obj U.property.1 U.property.2)
    fun U U' e ↦ @hf U.obj U'.obj U.property.1 U'.property.1 U.property.2 U'.property.2 e

@[simp]
theorem lift_mk {α : Sort*} {f : ∀ (U : FDRep k H) [Simple U], U.LiesOver φ V → α} {hf}
    (U : FDRep k H) [Simple U] (h : U.LiesOver φ V) : lift f hf (mk U h) = f U h :=
  ObjectProperty.skeletonLift_toSkeleton _ _

/-- Forgetting the constituent: the class of a simple representation lying over `V`, read as a
class of simple representations. -/
noncomputable def toSimpleFDRepClasses :
    SimpleFDRepClassesOver φ V → SimpleFDRepClasses k H :=
  lift (fun U _ _ ↦ SimpleFDRepClasses.mk U)
    fun U U' _ _ _ _ e ↦ (SimpleFDRepClasses.mk_eq_mk_iff U U').mpr e

@[simp]
theorem toSimpleFDRepClasses_mk (U : FDRep k H) [Simple U] (h : U.LiesOver φ V) :
    toSimpleFDRepClasses (mk U h) = SimpleFDRepClasses.mk U :=
  lift_mk (f := fun U _ _ ↦ SimpleFDRepClasses.mk U) U h

/-- **Forgetting the constituent is injective**: the classes over `V` are a subfamily of all
simple-object classes, not a quotient of one. -/
theorem toSimpleFDRepClasses_injective :
    Function.Injective (toSimpleFDRepClasses (φ := φ) (V := V)) := by
  intro a
  induction a using ind with
  | _ U hU hlies =>
  intro b
  induction b using ind with
  | _ U' hU' hlies' =>
  intro hab
  rw [toSimpleFDRepClasses_mk, toSimpleFDRepClasses_mk, SimpleFDRepClasses.mk_eq_mk_iff] at hab
  exact (mk_eq_mk_iff U U' hlies hlies').mpr hab

end SimpleFDRepClassesOver

end Classes

end TauCeti
