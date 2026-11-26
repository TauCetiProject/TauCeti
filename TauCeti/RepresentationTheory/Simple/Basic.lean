/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Simple
public import Mathlib.RepresentationTheory.FDRep
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RepresentationTheory.Rep.Iso
public import TauCeti.CategoryTheory.Simple.Classes
public import TauCeti.CategoryTheory.Skeletal
public import TauCeti.RepresentationTheory.Rep.Subrepresentation
import TauCeti.CategoryTheory.Action.Restriction
import TauCeti.CategoryTheory.Linear.Biproduct
import TauCeti.RepresentationTheory.AsModule
import TauCeti.RepresentationTheory.FDRep.Basic
import TauCeti.RepresentationTheory.Irreducible

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
eliminator and lift a consumer needs, as well as the dimension `SimpleFDRepClasses.finrank`, the
trivial class `SimpleFDRepClasses.trivial`, and the Hom-dimension
`SimpleFDRepClasses.finrankHom` over a field. It lives here rather than beside its comparison with
the module-level quotient (`TauCeti.SimpleFDRepClasses.toSimpleSubmoduleClasses`, in
`TauCeti.RepresentationTheory.Simple.FDRepClasses`) so that naming the isomorphism classes does not
drag in the semisimple isotypic-component theory that only the comparison needs.

## Main results

* `Rep.simple_iff_isIrreducible`: an object of `Rep k G` is simple exactly when the
  representation it carries is irreducible.
* `Rep.simple_of_isIrreducible` and `Rep.isIrreducible_of_simple`: the two directions as an
  instance and a theorem, respectively.
* `FDRep.simple_iff_isIrreducible`: the same for `FDRep k G`.
* `FDRep.simple_of_isIrreducible`, `FDRep.simple_of`, `FDRep.simple_of_trivial`,
  `FDRep.simple_tensorUnit`, and `FDRep.isIrreducible_of_simple`: the corresponding instances (for
  an object of `FDRep k G`, `FDRep.of ρ`, the trivial representation, and `𝟙_ (FDRep k G)`) and
  theorem for `FDRep`.
* `FDRep.isSimpleModule_asModule_of_simple`: the instance making Mathlib's simple-module API on
  `X.ρ.asModule` available from `Simple X` alone.
* `TauCeti.SimpleFDRepClasses`: the isomorphism classes of simple objects of `FDRep k G`.
* `TauCeti.SimpleFDRepClasses.mk_eq_mk_iff`: two simple objects have the same class exactly when
  they are isomorphic in `FDRep k G`.
* `TauCeti.SimpleFDRepClasses.ind` and `TauCeti.SimpleFDRepClasses.lift`: the eliminator and the
  lift of an isomorphism-invariant function.
* `TauCeti.SimpleFDRepClasses.equivSimpleClasses`: canonical identification of
  `SimpleFDRepClasses k G` with `SimpleClasses (FDRep k G)`.
* `TauCeti.SimpleFDRepClasses.resEquiv`: induced bijection on simple isomorphism classes along a
  monoid isomorphism.
* `TauCeti.SimpleFDRepClasses.finrank`, `TauCeti.SimpleFDRepClasses.trivial` (with
  `mk_tensorUnit` and `mk_eq_trivial_iff`), and `TauCeti.SimpleFDRepClasses.finrankHom` (with
  `finrankHom_zero`, `finrankHom_biprod`, and `finrankHom_simple`).
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

/-- Bundling an irreducible finite-dimensional representation with `FDRep.of` produces a simple
object of `FDRep k G`. -/
instance FDRep.simple_of {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k G V) [ρ.IsIrreducible] : Simple (FDRep.of ρ) :=
  (FDRep.simple_iff_isIrreducible (FDRep.of ρ)).mpr ((FDRep.of_ρ' ρ).symm ▸ ‹_›)

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

/-- The one-dimensional trivial representation on `k` is a simple object of `FDRep k G`. -/
instance FDRep.simple_of_trivial :
    Simple (FDRep.of (_root_.Representation.trivial k G k)) :=
  FDRep.simple_of _

open MonoidalCategory in
/-- The monoidal unit `𝟙_ (FDRep k G)` is a simple object of `FDRep k G`. -/
instance FDRep.simple_tensorUnit : Simple (𝟙_ (FDRep k G)) :=
  FDRep.of_trivial k G ▸ FDRep.simple_of_trivial

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

variable (k G) in
/-- **Canonical identification of `SimpleFDRepClasses k G` with `SimpleClasses (FDRep k G)`.** -/
noncomputable def equivSimpleClasses : SimpleFDRepClasses k G ≃ SimpleClasses (FDRep k G) where
  toFun := lift (fun X ↦ SimpleClasses.classOf X) fun _ _ _ _ h ↦
    (SimpleClasses.classOf_eq_iff_nonempty_iso _ _).mpr h
  invFun S := mk S.repr
  left_inv c := by
    induction c using ind with
    | h X hX =>
      simp only [lift_mk]
      exact (mk_eq_mk_iff _ _).mpr ⟨SimpleClasses.classOfReprIso X⟩
  right_inv S := by
    simp only [lift_mk]
    exact SimpleClasses.classOf_repr S

/-- Evaluating `equivSimpleClasses` on the class of a simple object `X` yields
`SimpleClasses.classOf X`. -/
@[simp]
theorem equivSimpleClasses_mk (X : FDRep k G) [Simple X] :
    equivSimpleClasses k G (mk X) = SimpleClasses.classOf X := by
  dsimp [equivSimpleClasses]
  exact lift_mk X

/-- The inverse of `equivSimpleClasses` sends `S` to the class of its representative `S.repr`. -/
theorem equivSimpleClasses_symm_apply (S : SimpleClasses (FDRep k G)) :
    (equivSimpleClasses k G).symm S = mk S.repr := by
  dsimp [equivSimpleClasses]

/-- Applying the inverse of `equivSimpleClasses` to `SimpleClasses.classOf X` yields `mk X`. -/
@[simp]
theorem equivSimpleClasses_symm_classOf (X : FDRep k G) [Simple X] :
    (equivSimpleClasses k G).symm (SimpleClasses.classOf X) = mk X := by
  rw [equivSimpleClasses_symm_apply, mk_eq_mk_iff]
  exact ⟨SimpleClasses.classOfReprIso X⟩

end SimpleFDRepClasses

end Classes

section ResEquiv

variable {k : Type u} {G₁ : Type v} {G₂ : Type w} [Ring k] [Monoid G₁] [Monoid G₂]

/-- Restricting a simple object of `FDRep k G₂` along a monoid isomorphism yields a simple
object of `FDRep k G₁`. -/
instance _root_.FDRep.simple_res (φ : G₁ ≃* G₂) (X : FDRep k G₂) [Simple X] :
    Simple ((Action.res (FGModuleCat.{u} k) (φ : G₁ →* G₂)).obj X) :=
  _root_.CategoryTheory.simple_obj (Action.resEquiv (FGModuleCat.{u} k) φ).functor X

namespace SimpleFDRepClasses

variable (k) in
/-- Restricting along a monoid isomorphism `φ : G₁ ≃* G₂` induces a bijection between the simple
isomorphism classes of `FDRep k G₂` and `FDRep k G₁`. -/
noncomputable def resEquiv (φ : G₁ ≃* G₂) :
    SimpleFDRepClasses k G₂ ≃ SimpleFDRepClasses k G₁ :=
  (equivSimpleClasses k G₂).trans
    ((SimpleClasses.equiv (Action.resEquiv (FGModuleCat.{u} k) φ)).trans
      (equivSimpleClasses k G₁).symm)

/-- Evaluating `SimpleFDRepClasses.resEquiv` on the class of a simple object `X` yields the class
of its restriction along `φ`. -/
@[simp]
theorem resEquiv_mk (φ : G₁ ≃* G₂) (X : FDRep k G₂) [Simple X] :
    resEquiv k φ (mk X) = mk ((Action.res (FGModuleCat.{u} k) (φ : G₁ →* G₂)).obj X) := by
  simp only [resEquiv, Equiv.trans_apply, equivSimpleClasses_mk]
  rw [SimpleClasses.equiv_apply_classOf]
  exact equivSimpleClasses_symm_classOf ((Action.res (FGModuleCat.{u} k) (φ : G₁ →* G₂)).obj X)

/-- Applying `(SimpleFDRepClasses.resEquiv k φ).symm` equals applying `resEquiv k φ.symm`. -/
theorem resEquiv_symm_apply (φ : G₁ ≃* G₂) (c : SimpleFDRepClasses k G₁) :
    (resEquiv k φ).symm c = resEquiv k φ.symm c := by
  induction c using ind with
  | h Y hY =>
    apply (resEquiv k φ).injective
    rw [Equiv.apply_symm_apply, resEquiv_mk, resEquiv_mk, mk_eq_mk_iff]
    exact ⟨((Action.resEquiv (FGModuleCat.{u} k) φ).counitIso.app Y).symm⟩

/-- The inverse equivalence of `SimpleFDRepClasses.resEquiv k φ` is `resEquiv k φ.symm`. -/
theorem resEquiv_symm (φ : G₁ ≃* G₂) :
    (resEquiv k φ).symm = resEquiv k φ.symm :=
  Equiv.ext (resEquiv_symm_apply φ)

/-- Restricting along the identity monoid isomorphism is the identity equivalence on simple
isomorphism classes. -/
@[simp]
theorem resEquiv_refl :
    resEquiv k (MulEquiv.refl G₁) = Equiv.refl (SimpleFDRepClasses k G₁) := by
  ext c
  induction c using ind with
  | h X hX =>
    rw [resEquiv_mk, Equiv.refl_apply, mk_eq_mk_iff]
    exact ⟨eqToIso (by rw [MulEquiv.toMonoidHom_refl, MonoidHom.actionRes_id, Functor.id_obj])⟩

/-- Restricting along a composite monoid isomorphism is contravariant in the equivalence. -/
@[simp]
theorem resEquiv_trans {G₃ : Type*} [Monoid G₃] (φ : G₁ ≃* G₂) (ψ : G₂ ≃* G₃) :
    resEquiv k (φ.trans ψ) = (resEquiv k ψ).trans (resEquiv k φ) := by
  ext c
  induction c using ind with
  | h X hX =>
    rw [resEquiv_mk, Equiv.trans_apply, resEquiv_mk, resEquiv_mk, mk_eq_mk_iff]
    exact ⟨eqToIso (by rw [MulEquiv.toMonoidHom_trans, MonoidHom.actionRes_comp, Functor.comp_obj])⟩

end SimpleFDRepClasses

end ResEquiv

namespace SimpleFDRepClasses

section Field

variable {k : Type u} {G : Type v} [Field k] [Monoid G]

/-- The vector-space dimension of a simple isomorphism class in `FDRep k G`. -/
noncomputable def finrank (c : SimpleFDRepClasses k G) : ℕ :=
  c.lift (fun (X : FDRep k G) ↦ Module.finrank k X) fun _ _ _ _ ⟨iso⟩ ↦
    (FDRep.isoToLinearEquiv iso).finrank_eq

@[simp]
theorem finrank_mk (X : FDRep k G) [Simple X] : (mk X).finrank = Module.finrank k X := lift_mk X

/-- Every simple isomorphism class has positive dimension. -/
theorem finrank_pos (c : SimpleFDRepClasses k G) : 0 < c.finrank := by
  induction c using ind with
  | h X hX => rw [finrank_mk]; exact (FDRep.isIrreducible_of_simple X).finrank_pos

variable (k G) in
/-- The isomorphism class of the one-dimensional trivial representation in `FDRep k G`. -/
noncomputable def trivial : SimpleFDRepClasses k G :=
  mk (FDRep.of (_root_.Representation.trivial k G k))

theorem trivial_def : trivial k G = mk (FDRep.of (_root_.Representation.trivial k G k)) := (rfl)

open MonoidalCategory in
@[simp]
theorem mk_tensorUnit : mk (𝟙_ (FDRep k G)) = trivial k G := by
  rw [trivial_def, mk_eq_mk_iff]; exact ⟨(eqToIso (FDRep.of_trivial k G)).symm⟩

open MonoidalCategory in
@[simp]
theorem equivSimpleClasses_trivial :
    equivSimpleClasses k G (trivial k G) = SimpleClasses.classOf (𝟙_ (FDRep k G)) := by
  rw [← mk_tensorUnit, equivSimpleClasses_mk]

@[simp]
theorem finrank_trivial : (trivial k G).finrank = 1 := by
  rw [trivial_def, finrank_mk, FDRep.finrank_of, Module.finrank_self]

/-- **Characterization of the trivial class.** Over any field `k` and monoid `G`, a simple object
`X : FDRep k G` represents `SimpleFDRepClasses.trivial k G` if and only if every `g : G` acts as
`1` on `X`. -/
-- `TauCeti.RepresentationTheory.LinearCharacter.Basic` imports this file, so we prove this
-- directly via `LinearMap.toSpanSingleton` and Schur's lemma rather than `ofLinearCharacter 1`.
theorem mk_eq_trivial_iff (X : FDRep k G) [Simple X] :
    mk X = trivial k G ↔ ∀ g : G, X.ρ g = 1 := by
  rw [trivial_def, mk_eq_mk_iff, nonempty_fdRepIso_iff, FDRep.of_ρ']
  refine ⟨fun ⟨e⟩ g ↦ LinearMap.ext fun x ↦ e.injective
    (by simpa using LinearMap.congr_fun (e.isIntertwining' g) x), fun h ↦ ?_⟩
  let := FDRep.isIrreducible_of_simple X
  have := (FDRep.isIrreducible_of_simple X).nontrivial
  obtain ⟨v, hv⟩ := exists_ne (0 : X)
  let f : _root_.Representation.IntertwiningMap (_root_.Representation.trivial k G k) X.ρ :=
    (LinearMap.toSpanSingleton k X v).intertwiningMap_of_isIntertwiningMap _ _ fun g c ↦ by
      simp [h g]
  have hf : f ≠ 0 := fun h0 ↦ hv (by simpa [f] using DFunLike.congr_fun h0 1)
  exact ⟨(f.ofBijective ((_root_.Representation.IsIrreducible.bijective_or_eq_zero f).resolve_right
    hf)).symm⟩

/-- The dimension `dim_k Hom_G(X, W)` of morphisms from a simple class `c = [X]` to
`W : FDRep k G`. Under split semisimplicity (for instance over an algebraically closed field in
which `|G|` is invertible), this is the multiplicity of `c` in `W`. -/
noncomputable def finrankHom (c : SimpleFDRepClasses k G) (W : FDRep k G) : ℕ :=
  c.lift (fun X ↦ Module.finrank k (X ⟶ W)) fun _ _ _ _ ⟨iso⟩ ↦
    (Linear.homCongr k iso (Iso.refl W)).finrank_eq

@[simp]
theorem finrankHom_mk (X : FDRep k G) [Simple X] (W : FDRep k G) :
    (mk X).finrankHom W = Module.finrank k (X ⟶ W) := lift_mk X

/-- `SimpleFDRepClasses.finrankHom` is invariant under isomorphism in the target object. -/
theorem finrankHom_congr (c : SimpleFDRepClasses k G) {W₁ W₂ : FDRep k G} (iso : W₁ ≅ W₂) :
    c.finrankHom W₁ = c.finrankHom W₂ := by
  induction c using ind with
  | h X hX => simp only [finrankHom_mk]; exact (Linear.homCongr k (Iso.refl X) iso).finrank_eq

open scoped ZeroObject in
@[simp]
theorem finrankHom_zero (c : SimpleFDRepClasses k G) : c.finrankHom (0 : FDRep k G) = 0 := by
  induction c using ind with
  | h X hX =>
    have : Subsingleton (X ⟶ (0 : FDRep k G)) :=
      ⟨fun f g ↦ (Limits.isZero_zero (FDRep k G)).eq_of_tgt f g⟩
    rw [finrankHom_mk]; exact Module.finrank_zero_of_subsingleton

open Limits in
@[simp]
theorem finrankHom_biprod (c : SimpleFDRepClasses k G) (W₁ W₂ : FDRep k G) :
    c.finrankHom (W₁ ⊞ W₂) = c.finrankHom W₁ + c.finrankHom W₂ := by
  induction c using ind with
  | h X hX =>
    rw [finrankHom_mk, finrankHom_mk, finrankHom_mk,
      (TauCeti.homToBiprodLinearEquiv k X W₁ W₂).finrank_eq, Module.finrank_prod]

/-- Over an algebraically closed field, `c.finrankHom Y` at a simple object `Y` is `1` at `mk Y`
and `0` elsewhere (Schur's lemma). -/
theorem finrankHom_simple [IsAlgClosed k] [DecidableEq (SimpleFDRepClasses k G)]
    (c : SimpleFDRepClasses k G) (Y : FDRep k G) [Simple Y] :
    c.finrankHom Y = if c = mk Y then 1 else 0 := by
  induction c using ind with
  | h X hX =>
    have : Simple X := hX
    rw [finrankHom_mk, FDRep.finrank_hom_simple_simple X Y]
    exact ite_congr (propext (mk_eq_mk_iff X Y).symm) (fun _ ↦ rfl) (fun _ ↦ rfl)

end Field

section ResEquivField

variable {k : Type u} {G₁ : Type v} {G₂ : Type w} [Field k] [Monoid G₁] [Monoid G₂]

/-- Restricting along a monoid isomorphism preserves `SimpleFDRepClasses.finrank`. -/
@[simp]
theorem finrank_resEquiv (φ : G₁ ≃* G₂) (c : SimpleFDRepClasses k G₂) :
    (resEquiv k φ c).finrank = c.finrank := by
  induction c using ind with
  | h X hX =>
    rw [resEquiv_mk, finrank_mk, finrank_mk]
    exact congrArg (fun M : FGModuleCat.{u} k ↦ Module.finrank k M)
      (Action.res_obj_V (FGModuleCat.{u} k) (φ : G₁ →* G₂) X)

/-- Restricting along a monoid isomorphism maps the trivial simple class to the trivial simple
class. -/
@[simp]
theorem resEquiv_trivial (φ : G₁ ≃* G₂) :
    resEquiv k φ (trivial k G₂) = trivial k G₁ := by
  rw [← mk_tensorUnit, ← mk_tensorUnit, resEquiv_mk, mk_eq_mk_iff]
  exact ⟨FDRep.resTensorUnitIso (φ : G₁ →* G₂)⟩

/-- Restricting along a monoid isomorphism preserves `SimpleFDRepClasses.finrankHom`. -/
@[simp]
theorem finrankHom_resEquiv (φ : G₁ ≃* G₂) (c : SimpleFDRepClasses k G₂) (W : FDRep k G₂) :
    (resEquiv k φ c).finrankHom ((Action.res (FGModuleCat.{u} k) (φ : G₁ →* G₂)).obj W) =
      c.finrankHom W := by
  induction c using ind with
  | h X hX =>
    rw [resEquiv_mk, finrankHom_mk, finrankHom_mk]
    exact MonoidHom.finrank_hom_actionRes_of_surjective (φ : G₁ →* G₂) φ.surjective X W

end ResEquivField

end SimpleFDRepClasses

end TauCeti
