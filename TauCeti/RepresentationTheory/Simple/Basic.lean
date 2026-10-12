/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Simple
public import Mathlib.RepresentationTheory.FDRep
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RepresentationTheory.Rep.Iso
public import TauCeti.CategoryTheory.Skeletal
public import TauCeti.RepresentationTheory.Rep.Subrepresentation

/-!
# Simple objects of `Rep k G` and `FDRep k G`, and their isomorphism classes

Two notions of "irreducible representation" coexist. `Representation.IsIrreducible ρ` says that the
lattice of subrepresentations of `ρ` has exactly two elements, and it is the notion in which the
representation-theoretic arguments of this repository are phrased.
`CategoryTheory.Simple X` says that `X` is nonzero and every monomorphism `f` into `X` satisfies
`IsIso f ↔ f ≠ 0`; it is the notion in which the categorical machinery is phrased -- Schur's lemma
`FDRep.finrank_hom_simple_simple`, the characters of simple objects, semisimple categories. This
file supplies the dictionary between them.

Over `Rep k G` the dictionary is bookkeeping. `Rep k G` is equivalent to the category of
`k[G]`-modules (`Rep.equivalenceModuleMonoidAlgebra`), an equivalence transports simplicity in both
directions, and a module is a simple object exactly when it is a simple module
(`simple_iff_isSimpleModule`).

Mathlib does not identify `FDRep k G` with a module category, so it needs an argument in each
direction. One is formal: the forgetful functor to `Rep k G` is faithful, preserves zero morphisms
and monomorphisms, and reflects isomorphisms, and such a functor reflects simplicity
(`CategoryTheory.Functor.simple_of_simple_obj`). The other uses finite-dimensionality, and is where
the restriction to `FDRep` earns its keep: a subrepresentation of a finite-dimensional
representation is again finite-dimensional, so it is again an object of `FDRep k G`, and its
inclusion is a monomorphism which is nonzero exactly when the subrepresentation is nonzero and an
isomorphism exactly when the subrepresentation is everything. Simplicity of the object therefore
says precisely that the lattice of subrepresentations is `{⊥, ⊤}` with `⊥ ≠ ⊤`.

The irreducible-to-simple directions are registered as instances. The converse directions are the
theorems `Rep.isIrreducible_of_simple` and `FDRep.isIrreducible_of_simple`; they are deliberately
not instances, since with the forward directions they would close a cycle in the instance graph.
One consequence of the converse directions not being instances is that inference cannot get from
`Simple X` to the simplicity of the `k[G]`-module `X.ρ.asModule`, even though Mathlib registers
that module as simple whenever `X.ρ` is irreducible. The single composite
`FDRep.isSimpleModule_asModule_of_simple` is therefore registered as an instance as well, so that
`Simple X` alone suffices for the module-level API.

A classification statement is valued in a type of *isomorphism classes*, and for simple objects of
`FDRep k G` that type needs no device: unlike abstract simple modules, which range over every
universe, the objects of `FDRep k G` already form a type, and Mathlib already quotients the objects
of a category by isomorphism. `TauCeti.SimpleFDRepClasses` is that quotient, namely
`CategoryTheory.Skeleton` of the full subcategory of simple objects, together with the constructor,
eliminator and lift a consumer needs. It lives here rather than beside its comparison with the
module-level quotient (`TauCeti.SimpleFDRepClasses.toSimpleSubmoduleClasses`, in
`TauCeti.RepresentationTheory.Simple.FDRepClasses`) so that naming the isomorphism classes does not
drag in the semisimple isotypic-component theory that only the comparison needs.

## Main results

* `Rep.simple_iff_isIrreducible`: an object of `Rep k G` is simple exactly when the
  representation it carries is irreducible.
* `Rep.simple_of_isIrreducible` and `Rep.isIrreducible_of_simple`: the two directions as an
  instance and a theorem, respectively.
* `FDRep.simple_iff_isIrreducible`: the same for `FDRep k G`.
* `FDRep.simple_of_isIrreducible` and `FDRep.isIrreducible_of_simple`: the corresponding instance
  and theorem for `FDRep`.
* `FDRep.isSimpleModule_asModule_of_simple`: the instance making Mathlib's simple-module API on
  `X.ρ.asModule` available from `Simple X` alone.
* `TauCeti.SimpleFDRepClasses`: the isomorphism classes of simple objects of `FDRep k G`.
* `TauCeti.SimpleFDRepClasses.mk_eq_mk_iff`: two simple objects have the same class exactly when
  they are isomorphic in `FDRep k G`.
* `TauCeti.SimpleFDRepClasses.ind` and `TauCeti.SimpleFDRepClasses.lift`: the eliminator and the
  lift of an isomorphism-invariant function.
-/

public section

open CategoryTheory

open scoped MonoidAlgebra

universe u v w

/-- **An object of `Rep k G` is simple exactly when the representation it carries is
irreducible.** -/
theorem Rep.simple_iff_isIrreducible {k : Type u} {G : Type v} [Field k] [Monoid G]
    (A : Rep.{w} k G) : Simple A ↔ Representation.IsIrreducible A.ρ := by
  rw [Representation.irreducible_iff_isSimpleModule_asModule,
    ← simple_iff_isSimpleModule' (ModuleCat.of k[G] A.ρ.asModule)]
  exact (simple_obj_iff (Rep.toModuleMonoidAlgebra (k := k) (G := G)) A).symm

/-- An irreducible representation is a simple object of `Rep k G`. -/
instance Rep.simple_of_isIrreducible {k : Type u} {G : Type v} [Field k] [Monoid G]
    (A : Rep.{w} k G) [Representation.IsIrreducible A.ρ] : Simple A :=
  (Rep.simple_iff_isIrreducible A).mpr ‹_›

/-- A simple object of `Rep k G` carries an irreducible representation. -/
theorem Rep.isIrreducible_of_simple {k : Type u} {G : Type v} [Field k] [Monoid G]
    (A : Rep.{w} k G) [Simple A] : Representation.IsIrreducible A.ρ :=
  (Rep.simple_iff_isIrreducible A).mp ‹_›

section FDRep

variable {k : Type u} {G : Type v} [Field k] [Monoid G]

/-- The inclusion of a subrepresentation of a finite-dimensional representation, as a morphism of
`FDRep k G`: the monomorphism whose behaviour witnesses simplicity of the object. Its image in
`Rep k G` is `Rep.ofHom W.subtype`, which is where its properties are read off. -/
private noncomputable def subInclusion (X : FDRep k G) (W : Subrepresentation X.ρ) :
    FDRep.of W.toRepresentation ⟶ X :=
  -- `FDRep.of` and `forget₂` preserve the carried representations definitionally here, so the
  -- source and target of this preimage are the objects displayed in the type.
  (forget₂ (FDRep k G) (Rep k G)).preimage (Rep.ofHom W.subtype)

private theorem map_subInclusion (X : FDRep k G) (W : Subrepresentation X.ρ) :
    (forget₂ (FDRep k G) (Rep k G)).map (subInclusion X W) = Rep.ofHom W.subtype :=
  (forget₂ (FDRep k G) (Rep k G)).map_preimage _

private instance (X : FDRep k G) (W : Subrepresentation X.ρ) : Mono (subInclusion X W) :=
  (forget₂ (FDRep k G) (Rep k G)).mono_of_mono_map (by
    rw [map_subInclusion]
    exact W.mono_ofHom_subtype)

/-- The inclusion of a subrepresentation is the zero morphism exactly when the subrepresentation is
zero. -/
private theorem subInclusion_eq_zero_iff (X : FDRep k G) (W : Subrepresentation X.ρ) :
    subInclusion X W = 0 ↔ W = ⊥ := by
  rw [← (forget₂ (FDRep k G) (Rep k G)).map_eq_zero_iff, map_subInclusion]
  exact W.ofHom_subtype_eq_zero_iff

/-- The inclusion of a subrepresentation is an isomorphism exactly when the subrepresentation is
everything. -/
private theorem isIso_subInclusion_iff (X : FDRep k G) (W : Subrepresentation X.ρ) :
    IsIso (subInclusion X W) ↔ W = ⊤ := by
  rw [← isIso_iff_of_reflects_iso _ (forget₂ (FDRep k G) (Rep k G)), map_subInclusion]
  exact W.isIso_ofHom_subtype_iff

/-- **An object of `FDRep k G` is simple exactly when the representation it carries is
irreducible.** -/
theorem FDRep.simple_iff_isIrreducible (X : FDRep k G) :
    Simple X ↔ Representation.IsIrreducible X.ρ := by
  constructor
  · intro
    -- A subrepresentation is everything exactly when it is nonzero: this is simplicity of `X`,
    -- read through the inclusion of the subrepresentation.
    have key : ∀ W : Subrepresentation X.ρ, W = ⊤ ↔ ¬W = ⊥ := fun W => by
      rw [← isIso_subInclusion_iff, ← subInclusion_eq_zero_iff]
      exact Simple.mono_isIso_iff_nonzero _
    have : Nontrivial (Subrepresentation X.ρ) := ⟨⟨⊥, ⊤, fun h => (key ⊥).mp h rfl⟩⟩
    exact ⟨fun W => (em (W = ⊥)).imp_right (key W).mpr⟩
  · intro
    have : Simple ((forget₂ (FDRep k G) (Rep k G)).obj X) := by
      rwa [Rep.simple_iff_isIrreducible, FDRep.forget₂_ρ]
    exact Functor.simple_of_simple_obj (forget₂ (FDRep k G) (Rep k G)) X

/-- An irreducible finite-dimensional representation is a simple object of `FDRep k G`. -/
instance FDRep.simple_of_isIrreducible (X : FDRep k G)
    [Representation.IsIrreducible X.ρ] : Simple X :=
  (FDRep.simple_iff_isIrreducible X).mpr ‹_›

/-- A simple object of `FDRep k G` carries an irreducible representation. -/
theorem FDRep.isIrreducible_of_simple (X : FDRep k G) [Simple X] :
    Representation.IsIrreducible X.ρ :=
  (FDRep.simple_iff_isIrreducible X).mp ‹_›

/-- The module carried by a simple object of `FDRep k G` is a simple module over the group
algebra. Registered so that Mathlib's simple-module API on `X.ρ.asModule` is available from
`Simple X` alone, since `FDRep.isIrreducible_of_simple` is deliberately not an instance. -/
instance FDRep.isSimpleModule_asModule_of_simple (X : FDRep k G) [Simple X] :
    IsSimpleModule k[G] (Representation.asModule X.ρ) :=
  haveI := FDRep.isIrreducible_of_simple X
  inferInstance

end FDRep

namespace TauCeti

attribute [local instance] isIsomorphicSetoid

section Classes

variable (k : Type u) (G : Type v) [Ring k] [Monoid G]

/-- **The isomorphism classes of simple objects of `FDRep k G`**: the skeleton of the full
subcategory they span. -/
def SimpleFDRepClasses : Type _ :=
  Skeleton (ObjectProperty.FullSubcategory (Simple : ObjectProperty (FDRep k G)))

variable {k G}

namespace SimpleFDRepClasses

/-- The isomorphism class of a simple object of `FDRep k G`. -/
def mk (X : FDRep k G) [Simple X] : SimpleFDRepClasses k G :=
  toSkeleton (⟨X, inferInstance⟩ :
    ObjectProperty.FullSubcategory (Simple : ObjectProperty (FDRep k G)))

/-- Two simple objects have the same class exactly when they are isomorphic. -/
@[simp]
theorem mk_eq_mk_iff (X Y : FDRep k G) [Simple X] [Simple Y] :
    mk X = mk Y ↔ Nonempty (X ≅ Y) :=
  ObjectProperty.toSkeleton_eq_toSkeleton_iff_nonempty_iso
    (Simple : ObjectProperty (FDRep k G)) _ _

/-- To prove a property of every simple-object class, it suffices to prove it on the class of each
simple object. -/
@[elab_as_elim]
theorem ind {motive : SimpleFDRepClasses k G → Prop}
    (h : ∀ (X : FDRep k G) (hX : Simple X), motive (@mk k G _ _ X hX))
    (c : SimpleFDRepClasses k G) :
    motive c :=
  Quotient.ind (fun X ↦ h X.obj X.property) c

/-- Define a function on simple-object classes from an isomorphism-invariant function on simple
objects. -/
noncomputable def lift {α : Sort*} (f : ∀ (X : FDRep k G) [Simple X], α)
    (h : ∀ (X Y : FDRep k G) [Simple X] [Simple Y], Nonempty (X ≅ Y) → f X = f Y) :
    SimpleFDRepClasses k G → α :=
  ObjectProperty.skeletonLift _ (fun X ↦ @f X.obj X.property)
    fun X Y e ↦ @h X.obj Y.obj X.property Y.property e

/-- The lift of an isomorphism-invariant function, evaluated at the class of a simple object. -/
@[simp]
theorem lift_mk {α : Sort*} {f : ∀ (X : FDRep k G) [Simple X], α} {h}
    (X : FDRep k G) [Simple X] : lift f h (mk X) = f X :=
  ObjectProperty.skeletonLift_toSkeleton _ _

end SimpleFDRepClasses

end Classes

end TauCeti
