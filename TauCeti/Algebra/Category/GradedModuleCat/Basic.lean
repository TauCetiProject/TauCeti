/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.GradedMulAction
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import TauCeti.Algebra.Module.GradedModule.Shift

/-!
# The category of graded modules

Let `𝒜 : ℤ → Submodule k A` be a family of `k`-submodules of a `k`-algebra `A`, typically the
pieces of a `GradedAlgebra`. A **graded `𝒜`-module** is an `A`-module `M` with an internal
`ℤ`-grading `M = ⨁ₚ Mₚ` by `k`-submodules, in the sense of `TauCeti.InternalGrading`, on which
`𝒜` acts compatibly: `𝒜ᵢ • Mₚ ⊆ M_{i+p}`. A morphism of graded modules is an `A`-linear map of
degree zero, sending `Mₚ` into `Nₚ` for every `p`.

This file makes graded `𝒜`-modules into a `k`-linear category `TauCeti.GradedModuleCat 𝒜`, with
a faithful additive forgetful functor to `ModuleCat A`, and constructs its **grading shift**
`TauCeti.GradedModuleCat.shift 𝒜`, the `k`-linear autoequivalence `M ↦ M{1}` of the category
with `(M{1})ₚ = M_{p-1}`. This is the convention under which the class of `M{1}` in a graded
Grothendieck group is `q` times the class of `M`, and it agrees with the shift of
`TauCeti.GradedVectorSpace`. Graded Grothendieck groups, graded Ext and graded Cartan maps of
graded algebras are formed in this category with this shift.

## Main definitions

* `TauCeti.GradedModuleCat 𝒜`: the category of graded `𝒜`-modules.
* `TauCeti.GradedModuleCat.ofHom`: the morphism given by an `A`-linear map of degree zero.
* `TauCeti.GradedModuleCat.isoMk`: the isomorphism given by an `A`-linear equivalence which
  preserves and reflects degrees.
* `TauCeti.GradedModuleCat.toModuleCat`: the forgetful functor to `ModuleCat A`.
* `TauCeti.GradedModuleCat.shiftFunctor`: the shift `M ↦ M{n}`, with `(M{n})ₚ = M_{p-n}`.
* `TauCeti.GradedModuleCat.shift`: the grading shift `M ↦ M{1}`, as an autoequivalence.

## Main results

* `TauCeti.GradedModuleCat.mem_shift_functor_obj_piece_iff` and
  `TauCeti.GradedModuleCat.mem_shift_inverse_obj_piece_iff`: `(M{1})ₚ = M_{p-1}` and
  `(M{-1})ₚ = M_{p+1}`.
-/

public section

namespace TauCeti

open CategoryTheory

universe v uk uA

variable {k : Type uk} {A : Type uA} [CommRing k] [Ring A] [Algebra k A]
variable (𝒜 : ℤ → Submodule k A)

/-- The category of **graded `𝒜`-modules**: `A`-modules with an internal `ℤ`-grading by
`k`-submodules on which `𝒜ᵢ` raises degrees by `i`. -/
structure GradedModuleCat where
  /-- The underlying type of the module. -/
  carrier : Type v
  [isAddCommGroup : AddCommGroup carrier]
  [isModule : Module A carrier]
  [isModuleBase : Module k carrier]
  [isScalarTower : IsScalarTower k A carrier]
  /-- The internal grading of the module. -/
  grading : InternalGrading k carrier
  [gradedSMul : SetLike.GradedSMul 𝒜 grading.piece]

namespace GradedModuleCat

attribute [instance] isAddCommGroup isModule isModuleBase isScalarTower gradedSMul

variable {𝒜}

instance : CoeSort (GradedModuleCat.{v} 𝒜) (Type v) :=
  ⟨GradedModuleCat.carrier⟩

/-- The regular graded module of a graded algebra, with its given homogeneous pieces. -/
noncomputable abbrev regular [DirectSum.Decomposition 𝒜] [SetLike.GradedMul 𝒜] :
    GradedModuleCat.{uA} 𝒜 where
  carrier := A
  grading := InternalGrading.ofDecomposition 𝒜
  gradedSMul := ⟨fun {_ _} _ _ ha hx ↦ by
    rw [InternalGrading.ofDecomposition_piece] at hx ⊢
    exact SetLike.GradedMul.mul_mem ha hx⟩

/-- A morphism of graded `𝒜`-modules: an `A`-linear map of degree zero. -/
structure Hom (M N : GradedModuleCat.{v} 𝒜) where
  /-- The underlying `A`-linear map. -/
  hom : M →ₗ[A] N
  /-- The underlying map sends `Mₚ` into `Nₚ`. -/
  isHomogeneous : LinearMap.IsHomogeneous hom M.grading.piece N.grading.piece 0

instance : Category (GradedModuleCat.{v} 𝒜) where
  Hom := Hom
  id M := ⟨LinearMap.id, LinearMap.isHomogeneous_id _⟩
  comp f g := ⟨g.hom ∘ₗ f.hom, by simpa using g.isHomogeneous.comp f.isHomogeneous⟩

section Hom

variable {M N P : GradedModuleCat.{v} 𝒜}

/-- The morphism of graded modules given by an `A`-linear map of degree zero. -/
abbrev ofHom (f : M →ₗ[A] N) (hf : LinearMap.IsHomogeneous f M.grading.piece N.grading.piece 0) :
    M ⟶ N :=
  ⟨f, hf⟩

@[simp]
theorem hom_ofHom (f : M →ₗ[A] N)
    (hf : LinearMap.IsHomogeneous f M.grading.piece N.grading.piece 0) : (ofHom f hf).hom = f :=
  rfl

@[simp]
theorem hom_id : (𝟙 M : M ⟶ M).hom = LinearMap.id :=
  rfl

@[simp]
theorem hom_comp (f : M ⟶ N) (g : N ⟶ P) : (f ≫ g).hom = g.hom ∘ₗ f.hom :=
  rfl

/-- Two morphisms of graded modules are equal when their underlying linear maps are. -/
@[ext]
theorem hom_ext {f g : M ⟶ N} (h : f.hom = g.hom) : f = g := by
  rcases f with ⟨f, _⟩
  rcases g with ⟨g, _⟩
  cases h
  rfl

theorem hom_injective : Function.Injective (fun f : M ⟶ N ↦ f.hom) :=
  fun _ _ ↦ hom_ext

/-- A morphism of graded modules sends elements of degree `p` to elements of degree `p`. -/
theorem map_mem (f : M ⟶ N) {p : ℤ} {x : M} (hx : x ∈ M.grading.piece p) :
    f.hom x ∈ N.grading.piece p := by
  simpa using f.isHomogeneous.map_mem hx

end Hom

section Linear

variable {M N P : GradedModuleCat.{v} 𝒜}

instance : Zero (M ⟶ N) :=
  ⟨⟨0, LinearMap.isHomogeneous_zero _ _ _⟩⟩

instance : Add (M ⟶ N) :=
  ⟨fun f g ↦ ⟨f.hom + g.hom, f.isHomogeneous.add g.isHomogeneous⟩⟩

instance : Neg (M ⟶ N) :=
  ⟨fun f ↦ ⟨-f.hom, f.isHomogeneous.neg⟩⟩

instance : Sub (M ⟶ N) :=
  ⟨fun f g ↦ ⟨f.hom - g.hom, f.isHomogeneous.sub g.isHomogeneous⟩⟩

instance : SMul ℕ (M ⟶ N) :=
  ⟨fun n f ↦ ⟨n • f.hom, LinearMap.isHomogeneous_def.2 fun _ _ hx ↦ by
    simpa using nsmul_mem (f.isHomogeneous.map_mem hx) n⟩⟩

instance : SMul ℤ (M ⟶ N) :=
  ⟨fun n f ↦ ⟨n • f.hom, LinearMap.isHomogeneous_def.2 fun _ _ hx ↦ by
    simpa using zsmul_mem (f.isHomogeneous.map_mem hx) n⟩⟩

instance : SMul k (M ⟶ N) :=
  ⟨fun c f ↦ ⟨c • f.hom, f.isHomogeneous.smul c⟩⟩

@[simp]
theorem hom_zero : (0 : M ⟶ N).hom = 0 :=
  rfl

@[simp]
theorem hom_add (f g : M ⟶ N) : (f + g).hom = f.hom + g.hom :=
  rfl

@[simp]
theorem hom_neg (f : M ⟶ N) : (-f).hom = -f.hom :=
  rfl

@[simp]
theorem hom_sub (f g : M ⟶ N) : (f - g).hom = f.hom - g.hom :=
  rfl

@[simp]
theorem hom_nsmul (n : ℕ) (f : M ⟶ N) : (n • f).hom = n • f.hom :=
  rfl

@[simp]
theorem hom_zsmul (n : ℤ) (f : M ⟶ N) : (n • f).hom = n • f.hom :=
  rfl

@[simp]
theorem hom_smul (c : k) (f : M ⟶ N) : (c • f).hom = c • f.hom :=
  rfl

instance : AddCommGroup (M ⟶ N) :=
  Function.Injective.addCommGroup _ hom_injective rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

instance : Module k (M ⟶ N) :=
  Function.Injective.module k ⟨⟨fun f : M ⟶ N ↦ f.hom, rfl⟩, fun _ _ ↦ rfl⟩ hom_injective
    (fun _ _ ↦ rfl)

instance : Preadditive (GradedModuleCat.{v} 𝒜) where
  add_comp _ _ _ _ _ _ := by ext; simp
  comp_add _ _ _ _ _ _ := by ext; simp

instance : Linear k (GradedModuleCat.{v} 𝒜) where
  smul_comp _ _ _ _ _ _ := by ext; simp
  comp_smul _ _ _ _ _ _ := by ext; simp

end Linear

/-- The isomorphism of graded modules given by an `A`-linear equivalence which preserves and
reflects degrees. -/
@[expose, simps]
def isoMk {M N : GradedModuleCat.{v} 𝒜} (e : M ≃ₗ[A] N)
    (he : ∀ p x, x ∈ M.grading.piece p ↔ e x ∈ N.grading.piece p) : M ≅ N where
  hom := ofHom e.toLinearMap <| LinearMap.isHomogeneous_def.2 fun p x hx ↦ by
    simpa using (he p x).1 hx
  inv := ofHom e.symm.toLinearMap <| LinearMap.isHomogeneous_def.2 fun p y hy ↦ by
    simpa using (he p (e.symm y)).2 (by simpa using hy)
  hom_inv_id := by ext; simp
  inv_hom_id := by ext; simp

section Forget

/-- The forgetful functor from graded `𝒜`-modules to `A`-modules. -/
@[expose, simps]
def toModuleCat : GradedModuleCat.{v} 𝒜 ⥤ ModuleCat.{v} A where
  obj M := ModuleCat.of A M
  map f := ModuleCat.ofHom f.hom

instance : (toModuleCat (𝒜 := 𝒜)).Faithful where
  map_injective h := hom_ext (congrArg ModuleCat.Hom.hom h)

instance : (toModuleCat (𝒜 := 𝒜)).Additive where
  map_add := rfl

end Forget

section Shift

variable (M : GradedModuleCat.{v} 𝒜)

/-- The graded module `M{n}`: the module `M` with `(M{n})ₚ = M_{p-n}`. -/
abbrev shiftObj (n : ℤ) : GradedModuleCat.{v} 𝒜 where
  carrier := M
  grading := M.grading.shift (-n)
  gradedSMul := ⟨fun {i j} _ _ ha hx ↦ by
    rw [InternalGrading.shift_piece] at hx ⊢
    simpa [add_assoc] using SetLike.GradedSMul.smul_mem (B := M.grading.piece) ha hx⟩

/-- A shift of a graded module has the same underlying `k`-module, so it is finite whenever the
module is. -/
instance [Module.Finite k M] (n : ℤ) : Module.Finite k (M.shiftObj n) :=
  inferInstanceAs (Module.Finite k M)

theorem mem_shiftObj_piece_iff (n p : ℤ) (x : M) :
    x ∈ (M.shiftObj n).grading.piece p ↔ x ∈ M.grading.piece (p - n) := by
  simp [sub_eq_add_neg]

/-- The shift `M ↦ M{n}` of graded modules, the identity on underlying linear maps. -/
@[expose]
def shiftFunctor (n : ℤ) : GradedModuleCat.{v} 𝒜 ⥤ GradedModuleCat.{v} 𝒜 where
  obj M := M.shiftObj n
  map {M N} f := ofHom (M := M.shiftObj n) (N := N.shiftObj n) f.hom <|
    LinearMap.isHomogeneous_def.2 fun p x hx ↦ by
      simp only [InternalGrading.shift_piece, add_zero] at hx ⊢
      exact map_mem f hx

@[simp]
theorem shiftFunctor_obj (n : ℤ) : (shiftFunctor n).obj M = M.shiftObj n :=
  rfl

@[simp]
theorem hom_shiftFunctor_map {M N : GradedModuleCat.{v} 𝒜} (n : ℤ) (f : M ⟶ N) :
    ((shiftFunctor n).map f).hom = f.hom :=
  rfl

variable (𝒜) in
/-- The **grading shift** `M ↦ M{1}` of graded `𝒜`-modules, with `(M{1})ₚ = M_{p-1}`, as an
autoequivalence; its inverse is `M ↦ M{-1}`. -/
@[expose]
def shift : GradedModuleCat.{v} 𝒜 ≌ GradedModuleCat.{v} 𝒜 where
  functor := shiftFunctor 1
  inverse := shiftFunctor (-1)
  unitIso := NatIso.ofComponents (fun M ↦ isoMk (LinearEquiv.refl A M) fun p x ↦ by simp; rfl)
    fun _ ↦ by ext; rfl
  counitIso := NatIso.ofComponents (fun M ↦ isoMk (LinearEquiv.refl A M) fun p x ↦ by simp; rfl)
    fun _ ↦ by ext; rfl
  functor_unitIso_comp _ := by ext; rfl

@[simp]
theorem mem_shift_functor_obj_piece_iff (p : ℤ) (x : M) :
    x ∈ ((shift 𝒜).functor.obj M).grading.piece p ↔ x ∈ M.grading.piece (p - 1) :=
  M.mem_shiftObj_piece_iff 1 p x

@[simp]
theorem mem_shift_inverse_obj_piece_iff (p : ℤ) (x : M) :
    x ∈ ((shift 𝒜).inverse.obj M).grading.piece p ↔ x ∈ M.grading.piece (p + 1) := by
  rw [← sub_neg_eq_add]
  exact M.mem_shiftObj_piece_iff (-1) p x

@[simp]
theorem hom_shift_functor_map {M N : GradedModuleCat.{v} 𝒜} (f : M ⟶ N) :
    ((shift 𝒜).functor.map f).hom = f.hom :=
  rfl

@[simp]
theorem hom_shift_inverse_map {M N : GradedModuleCat.{v} 𝒜} (f : M ⟶ N) :
    ((shift 𝒜).inverse.map f).hom = f.hom :=
  rfl

/-- Forgetting the internal grading identifies every grading shift with the identity functor
on underlying modules. -/
def shiftFunctorCompToModuleCatIso (n : ℤ) :
    shiftFunctor (𝒜 := 𝒜) n ⋙ toModuleCat ≅ toModuleCat :=
  -- `shiftObj` changes only the grading, so its carrier and module instances reduce to those
  -- of `M`; the identity linear equivalence therefore supplies each component.
  NatIso.ofComponents (fun M ↦ (LinearEquiv.refl A M).toModuleIso) fun f ↦ by
    simp only [Functor.comp_map, toModuleCat_map, hom_shiftFunctor_map,
      LinearEquiv.toModuleIso_hom, LinearEquiv.refl_toLinearMap, ModuleCat.ofHom_id]
    -- The shifted carrier has the same module instances, so both identities are on the
    -- underlying source and target of `f.hom`.
    exact (Category.comp_id (ModuleCat.ofHom f.hom)).trans
      (Category.id_comp (ModuleCat.ofHom f.hom)).symm

@[simp]
theorem shiftFunctorCompToModuleCatIso_hom_app_hom (n : ℤ) :
    ((shiftFunctorCompToModuleCatIso (𝒜 := 𝒜) n).hom.app M).hom = LinearMap.id :=
  (rfl)

@[simp]
theorem shiftFunctorCompToModuleCatIso_inv_app_hom (n : ℤ) :
    ((shiftFunctorCompToModuleCatIso (𝒜 := 𝒜) n).inv.app M).hom = LinearMap.id :=
  (rfl)

instance (n : ℤ) : (shiftFunctor (𝒜 := 𝒜) n).Additive where
  map_add := rfl

instance (n : ℤ) : (shiftFunctor (𝒜 := 𝒜) n).Linear k where
  map_smul _ _ := rfl

instance : (shift 𝒜).functor.Additive :=
  inferInstanceAs (shiftFunctor 1).Additive

instance : (shift 𝒜).functor.Linear k :=
  inferInstanceAs ((shiftFunctor 1).Linear k)

end Shift

end GradedModuleCat

end TauCeti
