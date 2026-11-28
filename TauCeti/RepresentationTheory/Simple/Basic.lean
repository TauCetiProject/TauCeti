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
public import TauCeti.RepresentationTheory.Rep.Subrepresentation
import TauCeti.CategoryTheory.Action.Monoidal
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
`FDRep k G` that canonical type is `TauCeti.SimpleClasses (FDRep k G)` (defined in
`TauCeti.CategoryTheory.Simple.Classes`). This file supplies its `FDRep`-specific operations:
the dimension `SimpleClasses.finrank`, the trivial class `SimpleClasses.trivial`, the
Hom-dimension `SimpleClasses.finrankHom` over a field, and naturality of `SimpleClasses.equiv`
along `CategoryTheory.Action.resEquiv`. It lives here rather than beside its comparison with the
module-level quotient (`TauCeti.SimpleClasses.toSimpleSubmoduleClasses`, in
`TauCeti.RepresentationTheory.Simple.FDRepClasses`) so that working with `SimpleClasses (FDRep k G)`
does not drag in the semisimple isotypic-component theory that only the comparison needs.

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
* `TauCeti.SimpleClasses.equiv_actionResEquiv_symm` and friends: behaviour of
  `SimpleClasses.equiv (Action.resEquiv (FGModuleCat k) φ)` on simple classes of `FDRep`.
* `TauCeti.SimpleClasses.finrank`, `TauCeti.SimpleClasses.trivial` (with `classOf_tensorUnit` and
  `classOf_eq_trivial_iff`), and `TauCeti.SimpleClasses.finrankHom` (with `finrankHom_zero`,
  `finrankHom_biprod`, and `finrankHom_simple`).
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

section ResEquiv

variable {k : Type u} {G₁ : Type v} {G₂ : Type w} [Ring k] [Monoid G₁] [Monoid G₂]

/-- Restricting a simple object of `FDRep k G₂` along a monoid isomorphism yields a simple
object of `FDRep k G₁`. -/
instance _root_.FDRep.simple_res (φ : G₁ ≃* G₂) (X : FDRep k G₂) [Simple X] :
    Simple ((Action.res (FGModuleCat.{u} k) (φ : G₁ →* G₂)).obj X) :=
  _root_.CategoryTheory.simple_obj (Action.resEquiv (FGModuleCat.{u} k) φ).functor X

namespace SimpleClasses

/-- Applying `(SimpleClasses.equiv (Action.resEquiv (FGModuleCat.{u} k) φ)).symm` equals
applying `SimpleClasses.equiv (Action.resEquiv (FGModuleCat.{u} k) φ.symm)`. -/
theorem equiv_actionResEquiv_symm_apply (φ : G₁ ≃* G₂) (S : SimpleClasses (FDRep k G₁)) :
    (equiv (Action.resEquiv (FGModuleCat.{u} k) φ)).symm S =
      equiv (Action.resEquiv (FGModuleCat.{u} k) φ.symm) S := by
  induction S using SimpleClasses.ind with
  | h Y =>
    apply (equiv (Action.resEquiv (FGModuleCat.{u} k) φ)).injective
    simp only [Equiv.apply_symm_apply, equiv_apply_classOf]
    have : Simple ((Action.resEquiv (FGModuleCat.{u} k) φ.symm).functor.obj Y) :=
      _root_.CategoryTheory.simple_obj (Action.resEquiv (FGModuleCat.{u} k) φ.symm).functor Y
    have : Simple ((Action.resEquiv (FGModuleCat.{u} k) φ).functor.obj
        ((Action.resEquiv (FGModuleCat.{u} k) φ.symm).functor.obj Y)) :=
      _root_.CategoryTheory.simple_obj (Action.resEquiv (FGModuleCat.{u} k) φ).functor _
    exact (classOf_eq_iff_nonempty_iso _ _).mpr
      ⟨((Action.resEquiv (FGModuleCat.{u} k) φ).counitIso.app Y).symm⟩

/-- The inverse equivalence of `SimpleClasses.equiv (Action.resEquiv (FGModuleCat.{u} k) φ)` is
`SimpleClasses.equiv (Action.resEquiv (FGModuleCat.{u} k) φ.symm)`. -/
@[simp]
theorem equiv_actionResEquiv_symm (φ : G₁ ≃* G₂) :
    (equiv (Action.resEquiv (FGModuleCat.{u} k) φ)).symm =
      equiv (Action.resEquiv (FGModuleCat.{u} k) φ.symm) :=
  Equiv.ext (equiv_actionResEquiv_symm_apply φ)

/-- Restricting along the identity monoid isomorphism is the identity equivalence on simple
isomorphism classes. -/
@[simp]
theorem equiv_actionResEquiv_refl :
    equiv (Action.resEquiv (FGModuleCat.{u} k) (MulEquiv.refl G₁)) =
      Equiv.refl (SimpleClasses (FDRep k G₁)) := by
  refine Equiv.ext fun S ↦ ?_
  induction S using SimpleClasses.ind with
  | h X =>
    simp only [equiv_apply_classOf, Equiv.refl_apply]
    rw [classOf_eq_iff_nonempty_iso]
    refine ⟨eqToIso ?_⟩
    change (Action.res (FGModuleCat.{u} k) (MulEquiv.refl G₁ : G₁ →* G₁)).obj X = X
    rw [MulEquiv.toMonoidHom_refl, MonoidHom.actionRes_id, Functor.id_obj]

/-- Restricting along a composite monoid isomorphism is contravariant in the equivalence. -/
@[simp]
theorem equiv_actionResEquiv_trans {G₃ : Type*} [Monoid G₃] (φ : G₁ ≃* G₂) (ψ : G₂ ≃* G₃) :
    equiv (Action.resEquiv (FGModuleCat.{u} k) (φ.trans ψ)) =
      (equiv (Action.resEquiv (FGModuleCat.{u} k) ψ)).trans
        (equiv (Action.resEquiv (FGModuleCat.{u} k) φ)) := by
  refine Equiv.ext fun S ↦ ?_
  induction S using SimpleClasses.ind with
  | h X =>
    simp only [equiv_apply_classOf, Equiv.trans_apply]
    rw [classOf_eq_iff_nonempty_iso]
    refine ⟨eqToIso ?_⟩
    change (Action.res (FGModuleCat.{u} k) (φ.trans ψ : G₁ →* G₃)).obj X =
      (Action.res (FGModuleCat.{u} k) (φ : G₁ →* G₂)).obj
        ((Action.res (FGModuleCat.{u} k) (ψ : G₂ →* G₃)).obj X)
    rw [MulEquiv.toMonoidHom_trans, MonoidHom.actionRes_comp, Functor.comp_obj]

end SimpleClasses

end ResEquiv

namespace SimpleClasses

section Field

variable {k : Type u} {G : Type v} [Field k] [Monoid G]

/-- The vector-space dimension of a simple isomorphism class in `FDRep k G`. -/
noncomputable def finrank (S : SimpleClasses (FDRep k G)) : ℕ :=
  Module.finrank k S.repr

@[simp]
theorem finrank_classOf (X : FDRep k G) [Simple X] :
    (classOf X).finrank = Module.finrank k X :=
  (FDRep.isoToLinearEquiv (classOfReprIso X)).finrank_eq

/-- Every simple isomorphism class has positive dimension. -/
theorem finrank_pos (S : SimpleClasses (FDRep k G)) : 0 < S.finrank :=
  (FDRep.isIrreducible_of_simple S.repr).finrank_pos

section
open MonoidalCategory
variable (k G)

/-- The isomorphism class of the one-dimensional trivial representation in `FDRep k G`. -/
noncomputable def trivial : SimpleClasses (FDRep k G) :=
  classOf (𝟙_ (FDRep k G))

end

open MonoidalCategory in
theorem trivial_def : trivial k G = classOf (𝟙_ (FDRep k G)) := (rfl)

open MonoidalCategory in
@[simp]
theorem classOf_tensorUnit : classOf (𝟙_ (FDRep k G)) = trivial k G := (rfl)

@[simp]
theorem finrank_trivial : (trivial k G).finrank = 1 := by
  rw [trivial_def, finrank_classOf, ← FDRep.of_trivial k G, FDRep.finrank_of, Module.finrank_self]

/-- **Characterization of the trivial class.** Over any field `k` and monoid `G`, a simple object
`X : FDRep k G` represents `SimpleClasses.trivial k G` if and only if every `g : G` acts as `1` on
`X`. -/
-- `TauCeti.RepresentationTheory.LinearCharacter.Basic` imports this file, so we prove this
-- directly via `LinearMap.toSpanSingleton` and Schur's lemma rather than `ofLinearCharacter 1`.
theorem classOf_eq_trivial_iff (X : FDRep k G) [Simple X] :
    classOf X = trivial k G ↔ ∀ g : G, X.ρ g = 1 := by
  rw [trivial_def, classOf_eq_iff_nonempty_iso, ← FDRep.of_trivial k G, nonempty_fdRepIso_iff,
    FDRep.of_ρ']
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

/-- The dimension `dim_k Hom_G(S.repr, W)` of morphisms from a simple class `S` to
`W : FDRep k G`. Over a split semisimple category (for instance, for a finite group over an
algebraically closed field in which `|G|` is invertible), this is the multiplicity of `S` in
`W`. -/
noncomputable def finrankHom (S : SimpleClasses (FDRep k G)) (W : FDRep k G) : ℕ :=
  Module.finrank k (S.repr ⟶ W)

@[simp]
theorem finrankHom_classOf (X : FDRep k G) [Simple X] (W : FDRep k G) :
    (classOf X).finrankHom W = Module.finrank k (X ⟶ W) :=
  (Linear.homCongr k (classOfReprIso X) (Iso.refl W)).finrank_eq

/-- `SimpleClasses.finrankHom` is invariant under isomorphism in the target object. -/
theorem finrankHom_congr (S : SimpleClasses (FDRep k G)) {W₁ W₂ : FDRep k G} (iso : W₁ ≅ W₂) :
    S.finrankHom W₁ = S.finrankHom W₂ :=
  (Linear.homCongr k (Iso.refl S.repr) iso).finrank_eq

open scoped ZeroObject in
@[simp]
theorem finrankHom_zero (S : SimpleClasses (FDRep k G)) :
    S.finrankHom (0 : FDRep k G) = 0 := by
  have : Subsingleton (S.repr ⟶ (0 : FDRep k G)) :=
    ⟨fun f g ↦ (Limits.isZero_zero (FDRep k G)).eq_of_tgt f g⟩
  exact Module.finrank_zero_of_subsingleton

open Limits in
@[simp]
theorem finrankHom_biprod (S : SimpleClasses (FDRep k G)) (W₁ W₂ : FDRep k G) :
    S.finrankHom (W₁ ⊞ W₂) = S.finrankHom W₁ + S.finrankHom W₂ :=
  TauCeti.finrank_homTo_biprod k S.repr W₁ W₂

/-- Over an algebraically closed field, `S.finrankHom Y` at a simple object `Y` is `1` at
`classOf Y` and `0` elsewhere (Schur's lemma). -/
theorem finrankHom_simple [IsAlgClosed k] [DecidableEq (SimpleClasses (FDRep k G))]
    (S : SimpleClasses (FDRep k G)) (Y : FDRep k G) [Simple Y] :
    S.finrankHom Y = if S = classOf Y then 1 else 0 := by
  rw [finrankHom, FDRep.finrank_hom_simple_simple S.repr Y]
  exact ite_congr (propext ((eq_iff_nonempty_iso S (classOf Y)).trans
    ⟨fun ⟨e⟩ ↦ ⟨e.trans (classOfReprIso Y)⟩,
     fun ⟨e⟩ ↦ ⟨e.trans (classOfReprIso Y).symm⟩⟩).symm) (fun _ ↦ rfl) (fun _ ↦ rfl)

end Field

section ResEquivField

variable {k : Type u} {G₁ : Type v} {G₂ : Type w} [Field k] [Monoid G₁] [Monoid G₂]

/-- Restricting along a monoid isomorphism preserves `SimpleClasses.finrank`. -/
@[simp]
theorem finrank_equiv_actionResEquiv (φ : G₁ ≃* G₂) (S : SimpleClasses (FDRep k G₂)) :
    (equiv (Action.resEquiv (FGModuleCat.{u} k) φ) S).finrank = S.finrank := by
  induction S using SimpleClasses.ind with
  | h X =>
    simp only [equiv_apply_classOf, finrank_classOf]
    exact congrArg (fun M : FGModuleCat.{u} k ↦ Module.finrank k M)
      (Action.res_obj_V (FGModuleCat.{u} k) (φ : G₁ →* G₂) X)

/-- Restricting along a monoid isomorphism maps the trivial simple class to the trivial simple
class. -/
@[simp]
theorem equiv_actionResEquiv_trivial (φ : G₁ ≃* G₂) :
    equiv (Action.resEquiv (FGModuleCat.{u} k) φ) (trivial k G₂) = trivial k G₁ := by
  rw [← classOf_tensorUnit, ← classOf_tensorUnit, equiv_apply_classOf, classOf_eq_iff_nonempty_iso]
  exact ⟨(Functor.Monoidal.εIso (Action.res (FGModuleCat.{u} k) (φ : G₁ →* G₂))).symm⟩

/-- Restricting along a monoid isomorphism preserves `SimpleClasses.finrankHom`. -/
@[simp]
theorem finrankHom_equiv_actionResEquiv (φ : G₁ ≃* G₂) (S : SimpleClasses (FDRep k G₂))
    (W : FDRep k G₂) :
    (equiv (Action.resEquiv (FGModuleCat.{u} k) φ) S).finrankHom
        ((Action.res (FGModuleCat.{u} k) (φ : G₁ →* G₂)).obj W) =
      S.finrankHom W := by
  induction S using SimpleClasses.ind with
  | h X =>
    simp only [equiv_apply_classOf, finrankHom_classOf]
    exact MonoidHom.finrank_hom_actionRes_of_surjective (φ : G₁ →* G₂) φ.surjective X W

end ResEquivField

end SimpleClasses

end TauCeti
