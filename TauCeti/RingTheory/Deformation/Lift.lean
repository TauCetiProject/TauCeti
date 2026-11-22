/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Topology.LocallyConstant.Basic
public import TauCeti.RingTheory.Deformation.ArtinLocalAlg

/-!
# Lifts of a residual representation and their strict classes

Let `G` be a topological monoid (in practice a profinite group, such as a Galois group), `k` a
field and `ρbar : G →* GL n k` a residual representation. For an object `A` of the Artinian
coefficient category `C_Λ`, a *lift* of `ρbar` to `A` is a homomorphism `ρ : G →* GL n A` which
is continuous for the discrete topology on `A` and whose reduction along the augmentation
`A → k` is `ρbar`. Lifts are framed: they are matrices in a basis reducing to the standard basis
of `kⁿ`. Pushing a lift forward along a morphism `A ⟶ B` of `C_Λ` makes lifts a functor
`C_Λ ⥤ Type`, the *framed lifting functor* of Mazur's deformation theory.

The *strict kernel* `Γ̂ₙ(A)`, the kernel of the reduction `GL n A →* GL n k`, acts on lifts by
conjugation, and pushforward is equivariant. The orbits are the *strict classes* of lifts, which
form the unframed deformation functor `Def_ρbar : C_Λ ⥤ Type`. Strict classes are finer than
`GL n A`-conjugacy classes: two lifts that are conjugate only by a matrix not reducing to the
identity are in general different deformations.

Since an object of `C_Λ` carries no topology, continuity for the discrete topology is expressed as
`IsLocallyConstant`. A residual representation admitting a lift is itself locally constant, and
over the residue field `k` its only lift is itself; so both functors take a single value on `k`
exactly when `ρbar` is continuous for the discrete topology on `k`.

## Main definitions

* `TauCeti.Deformation.ArtinLocalAlg.strictKernel n A`: the kernel `Γ̂ₙ(A)` of the reduction
  `GL n A →* GL n k`.
* `TauCeti.Deformation.ArtinLocalAlg.strictKernelMap n f`: the homomorphism of strict kernels
  induced by a morphism `f` of `C_Λ`.
* `TauCeti.Deformation.Lift ρbar A`: the lifts of `ρbar` to `A`.
* `TauCeti.Deformation.Lift.map f`: the pushforward of lifts along a morphism `f` of `C_Λ`.
* `TauCeti.Deformation.liftFunctor Λ ρbar`: the framed lifting functor `C_Λ ⥤ Type`.
* `TauCeti.Deformation.StrictClass ρbar A`: strict classes of lifts, the orbits of the
  conjugation action of `Γ̂ₙ(A)`.
* `TauCeti.Deformation.strictClassFunctor Λ ρbar`: the deformation functor `Def_ρbar : C_Λ ⥤ Type`
  of strict classes, with the natural quotient map `TauCeti.Deformation.toStrictClass Λ ρbar`.

## Main results

* `TauCeti.Deformation.Lift.isLocallyConstant_residual`: a residual representation with a lift is
  locally constant.
* `TauCeti.Deformation.Lift.nonempty_residue_iff`: `ρbar` lifts to `k` exactly when it is locally
  constant, and the lift is then unique.
* `TauCeti.Deformation.Lift.map_smul`: pushforward of lifts is equivariant for the conjugation
  actions of the strict kernels.
* `TauCeti.Deformation.StrictClass.mk_eq_mk_iff`: two lifts have the same strict class exactly
  when they are conjugate by an element of the strict kernel.

## References

* B. Mazur, *Deforming Galois representations*, in *Galois groups over `ℚ`*, MSRI Publ. 16
  (1989), 385–437, §§1.1–1.2.
* T. Gee, *Modularity lifting theorems*, Essent. Number Theory 1 (2022), §3.1.
* M. Kisin, *Moduli of finite flat group schemes and modularity*, Ann. of Math. 170 (2009),
  §1.1 (lecture notes version: *Lectures on deformations of Galois representations*, Lecture 1).
-/

public section

open CategoryTheory Matrix

universe u v w x

namespace TauCeti.Deformation

variable {Λ : Type u} [CommRing Λ] {k : Type v} [Field k] [Algebra Λ k]
  {n : Type x} [Fintype n] [DecidableEq n]

namespace ArtinLocalAlg

/-- Reducing a matrix over `A` to `k` after pushing it forward along a morphism `f : A ⟶ B` of
`C_Λ` is reducing it to `k`. -/
@[simp]
theorem map_augmentation_map {A B : ArtinLocalAlg Λ k} (f : A ⟶ B) (a : GL n A.obj.left) :
    GeneralLinearGroup.map (B.augmentation : B.obj.left →+* k)
        (GeneralLinearGroup.map (f.hom.left.hom : A.obj.left →+* B.obj.left) a) =
      GeneralLinearGroup.map (A.augmentation : A.obj.left →+* k) a :=
  GeneralLinearGroup.ext fun i j ↦ by simp

/-- Reduction to `k` is the identity on matrices over the residue field. -/
theorem map_augmentation_residue (a : GL n (residue Λ k).obj.left) :
    GeneralLinearGroup.map ((residue Λ k).augmentation : (residue Λ k).obj.left →+* k) a = a := by
  rw [augmentation_residue]
  -- The carrier of `residue Λ k` is `k`, and `AlgHom.id Λ k` is `RingHom.id k` as a ring map.
  exact DFunLike.congr_fun GeneralLinearGroup.map_id a

variable (n) in
/-- The *strict kernel* `Γ̂ₙ(A)` of an object `A` of `C_Λ`: the kernel of the reduction
`GL n A →* GL n k` along the augmentation, the matrices reducing to the identity. -/
def strictKernel (A : ArtinLocalAlg Λ k) : Subgroup (GL n A.obj.left) :=
  (GeneralLinearGroup.map (A.augmentation : A.obj.left →+* k)).ker

theorem mem_strictKernel_iff {A : ArtinLocalAlg Λ k} {a : GL n A.obj.left} :
    a ∈ A.strictKernel n ↔ GeneralLinearGroup.map (A.augmentation : A.obj.left →+* k) a = 1 :=
  MonoidHom.mem_ker

/-- A morphism of `C_Λ` maps the strict kernel of its source into that of its target. -/
theorem map_mem_strictKernel {A B : ArtinLocalAlg Λ k} (f : A ⟶ B) {a : GL n A.obj.left}
    (ha : a ∈ A.strictKernel n) :
    GeneralLinearGroup.map (f.hom.left.hom : A.obj.left →+* B.obj.left) a ∈ B.strictKernel n := by
  rw [mem_strictKernel_iff, map_augmentation_map, ← mem_strictKernel_iff]
  exact ha

variable (n) in
/-- The homomorphism `Γ̂ₙ(A) →* Γ̂ₙ(B)` of strict kernels induced by a morphism `f : A ⟶ B` of
`C_Λ`, applying `f` to the matrix entries. -/
def strictKernelMap {A B : ArtinLocalAlg Λ k} (f : A ⟶ B) : A.strictKernel n →* B.strictKernel n :=
  ((GeneralLinearGroup.map (f.hom.left.hom : A.obj.left →+* B.obj.left)).comp
    (A.strictKernel n).subtype).codRestrict _ fun a ↦ map_mem_strictKernel f a.property

@[simp]
theorem coe_strictKernelMap_apply {A B : ArtinLocalAlg Λ k} (f : A ⟶ B) (a : A.strictKernel n) :
    (strictKernelMap n f a : GL n B.obj.left) =
      GeneralLinearGroup.map (f.hom.left.hom : A.obj.left →+* B.obj.left) a :=
  (rfl)

@[simp]
theorem strictKernelMap_id {A : ArtinLocalAlg Λ k} (a : A.strictKernel n) :
    strictKernelMap n (𝟙 A) a = a :=
  Subtype.ext <| GeneralLinearGroup.ext fun i j ↦ by simp

theorem strictKernelMap_comp {A B C : ArtinLocalAlg Λ k} (f : A ⟶ B) (g : B ⟶ C)
    (a : A.strictKernel n) :
    strictKernelMap n (f ≫ g) a = strictKernelMap n g (strictKernelMap n f a) :=
  Subtype.ext <| GeneralLinearGroup.ext fun i j ↦ by simp

/-- Over the residue field the strict kernel is trivial: reduction to `k` is the identity. -/
@[simp]
theorem strictKernel_residue : (residue Λ k).strictKernel n = ⊥ :=
  eq_bot_iff.mpr fun a ha ↦ by
    rw [Subgroup.mem_bot, ← map_augmentation_residue a]
    exact mem_strictKernel_iff.mp ha

instance : Subsingleton ((residue Λ k).strictKernel n) := by
  rw [strictKernel_residue]
  infer_instance

end ArtinLocalAlg

open ArtinLocalAlg

variable {G : Type w} [Monoid G] [TopologicalSpace G]

/-- A *lift* of the residual representation `ρbar : G →* GL n k` to an object `A` of `C_Λ`: a
homomorphism `G →* GL n A`, continuous for the discrete topology on `A`, whose reduction along
the augmentation `A → k` is `ρbar`. -/
structure Lift (ρbar : G →* GL n k) (A : ArtinLocalAlg Λ k) where
  /-- The underlying homomorphism `G →* GL n A`. -/
  toMonoidHom : G →* GL n A.obj.left
  /-- The lift is continuous for the discrete topology on `A`. -/
  isLocallyConstant' : IsLocallyConstant toMonoidHom
  /-- The lift reduces to `ρbar`. -/
  map_augmentation_comp' :
    (GeneralLinearGroup.map (A.augmentation : A.obj.left →+* k)).comp toMonoidHom = ρbar

namespace Lift

variable {ρbar : G →* GL n k} {A B C : ArtinLocalAlg Λ k}

instance : FunLike (Lift ρbar A) G (GL n A.obj.left) where
  coe ρ := ρ.toMonoidHom
  coe_injective ρ ρ' h := by
    cases ρ
    cases ρ'
    congr
    exact DFunLike.coe_injective h

instance : MonoidHomClass (Lift ρbar A) G (GL n A.obj.left) where
  map_mul ρ := ρ.toMonoidHom.map_mul
  map_one ρ := ρ.toMonoidHom.map_one

/-- Lifts are determined by their values. -/
@[ext]
theorem ext {ρ ρ' : Lift ρbar A} (h : ∀ g, ρ g = ρ' g) : ρ = ρ' :=
  DFunLike.ext _ _ h

@[simp]
theorem coe_toMonoidHom (ρ : Lift ρbar A) : ⇑ρ.toMonoidHom = ρ :=
  (rfl)

@[simp]
theorem coe_mk (ρ : G →* GL n A.obj.left) (h₁ h₂) : ⇑(⟨ρ, h₁, h₂⟩ : Lift ρbar A) = ρ :=
  (rfl)

/-- A lift is continuous for the discrete topology on `A`. -/
theorem isLocallyConstant (ρ : Lift ρbar A) : IsLocallyConstant ρ :=
  ρ.isLocallyConstant'

/-- A lift reduces to the residual representation. -/
@[simp]
theorem map_augmentation_apply (ρ : Lift ρbar A) (g : G) :
    GeneralLinearGroup.map (A.augmentation : A.obj.left →+* k) (ρ g) = ρbar g :=
  DFunLike.congr_fun ρ.map_augmentation_comp' g

/-- A residual representation admitting a lift is continuous for the discrete topology on `k`. -/
theorem isLocallyConstant_residual (ρ : Lift ρbar A) : IsLocallyConstant ρbar := by
  have h : ⇑ρbar = GeneralLinearGroup.map (A.augmentation : A.obj.left →+* k) ∘ ρ :=
    funext fun g ↦ (ρ.map_augmentation_apply g).symm
  rw [h]
  exact ρ.isLocallyConstant.comp _

section Map

/-- The pushforward `g ↦ GL n f (ρ g)` of a lift `ρ` along a morphism `f : A ⟶ B` of `C_Λ`. -/
def map (f : A ⟶ B) (ρ : Lift ρbar A) : Lift ρbar B where
  toMonoidHom :=
    (GeneralLinearGroup.map (f.hom.left.hom : A.obj.left →+* B.obj.left)).comp ρ.toMonoidHom
  isLocallyConstant' :=
    ρ.isLocallyConstant.comp (GeneralLinearGroup.map (f.hom.left.hom : A.obj.left →+* B.obj.left))
  map_augmentation_comp' := MonoidHom.ext fun g ↦ by simp

@[simp]
theorem map_apply (f : A ⟶ B) (ρ : Lift ρbar A) (g : G) :
    map f ρ g = GeneralLinearGroup.map (f.hom.left.hom : A.obj.left →+* B.obj.left) (ρ g) :=
  (rfl)

/-- Pushforward along the identity is the identity. -/
@[simp]
theorem map_id (ρ : Lift ρbar A) : map (𝟙 A) ρ = ρ :=
  ext fun g ↦ GeneralLinearGroup.ext fun i j ↦ by simp

/-- Pushforward along a composite is the composite of the pushforwards. -/
theorem map_comp (f : A ⟶ B) (f' : B ⟶ C) (ρ : Lift ρbar A) :
    map (f ≫ f') ρ = map f' (map f ρ) :=
  ext fun g ↦ GeneralLinearGroup.ext fun i j ↦ by simp

end Map

section Residue

/-- Over the residue field there is at most one lift: it is the residual representation. -/
instance : Subsingleton (Lift ρbar (residue Λ k)) where
  allEq ρ ρ' := ext fun g ↦ by
    rw [← map_augmentation_residue (ρ g), ← map_augmentation_residue (ρ' g),
      map_augmentation_apply, map_augmentation_apply]

/-- The residual representation lifts to `k` exactly when it is continuous for the discrete
topology on `k`; the lift is then unique. -/
theorem nonempty_residue_iff : Nonempty (Lift ρbar (residue Λ k)) ↔ IsLocallyConstant ρbar :=
  ⟨fun ⟨ρ⟩ ↦ ρ.isLocallyConstant_residual,
   fun h ↦ ⟨⟨ρbar, h, MonoidHom.ext fun g ↦ map_augmentation_residue (ρbar g)⟩⟩⟩

end Residue

section Conjugation

/-- The strict kernel `Γ̂ₙ(A)` acts on lifts to `A` by conjugation. -/
instance : SMul (A.strictKernel n) (Lift ρbar A) where
  smul a ρ :=
    { toMonoidHom := (MulAut.conj (a : GL n A.obj.left)).toMonoidHom.comp ρ.toMonoidHom
      isLocallyConstant' := ρ.isLocallyConstant.comp (MulAut.conj (a : GL n A.obj.left))
      map_augmentation_comp' := MonoidHom.ext fun g ↦ by simp [mem_strictKernel_iff.mp a.property] }

@[simp]
theorem smul_apply (a : A.strictKernel n) (ρ : Lift ρbar A) (g : G) :
    (a • ρ) g = a * ρ g * (a : GL n A.obj.left)⁻¹ :=
  (rfl)

instance : MulAction (A.strictKernel n) (Lift ρbar A) where
  one_smul ρ := ext fun g ↦ by simp
  mul_smul a b ρ := ext fun g ↦ by simp [mul_assoc]

/-- Pushforward along a morphism `f` of `C_Λ` intertwines conjugation by `a` with conjugation by
the image of `a`. -/
theorem map_smul (f : A ⟶ B) (a : A.strictKernel n) (ρ : Lift ρbar A) :
    map f (a • ρ) = (⟨_, map_mem_strictKernel f a.property⟩ : B.strictKernel n) • map f ρ :=
  ext fun g ↦ by simp

end Conjugation

end Lift

variable (ρbar : G →* GL n k)

variable (Λ) in
/-- The *framed lifting functor* `C_Λ ⥤ Type` of the residual representation `ρbar`, sending
`A` to the lifts of `ρbar` to `A` and a morphism to pushforward of lifts. -/
-- Exposed so that `(liftFunctor Λ ρbar).obj A` unfolds to `Lift ρbar A` in statements.
@[expose] def liftFunctor : ArtinLocalAlg Λ k ⥤ Type (max w v x) where
  obj A := Lift ρbar A
  map f := TypeCat.ofHom (Lift.map f)
  map_id A := by
    ext ρ : 3
    exact Lift.map_id ρ
  map_comp f f' := by
    ext ρ : 3
    exact Lift.map_comp f f' ρ

variable (Λ) in
@[simp]
theorem liftFunctor_obj (A : ArtinLocalAlg Λ k) : (liftFunctor Λ ρbar).obj A = Lift ρbar A :=
  (rfl)

variable (Λ) in
@[simp]
theorem liftFunctor_map_apply {A B : ArtinLocalAlg Λ k} (f : A ⟶ B) (ρ : Lift ρbar A) :
    (liftFunctor Λ ρbar).map f ρ = Lift.map f ρ :=
  (rfl)

/-- The *strict classes* of lifts of `ρbar` to `A`: lifts up to conjugation by the strict kernel
`Γ̂ₙ(A)`. These are the values of the deformation functor of `ρbar`. -/
-- Exposed as a quotient type: code generation needs its representation in other modules.
@[expose] def StrictClass (A : ArtinLocalAlg Λ k) : Type (max w v x) :=
  MulAction.orbitRel.Quotient (A.strictKernel n) (Lift ρbar A)

namespace StrictClass

variable {ρbar} {A B C : ArtinLocalAlg Λ k}

/-- The strict class of a lift. -/
def mk (ρ : Lift ρbar A) : StrictClass ρbar A :=
  Quotient.mk'' ρ

/-- Every strict class is the class of a lift. -/
theorem mk_surjective : Function.Surjective (mk : Lift ρbar A → StrictClass ρbar A) :=
  Quotient.mk''_surjective

/-- Two lifts have the same strict class exactly when they are conjugate by an element of the
strict kernel. -/
theorem mk_eq_mk_iff {ρ ρ' : Lift ρbar A} :
    mk ρ = mk ρ' ↔ ∃ a : A.strictKernel n, a • ρ = ρ' := by
  refine Quotient.eq''.trans ?_
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_symm, MulAction.mem_orbit_iff]

/-- A function on lifts that is invariant under conjugation by the strict kernel descends to strict
classes. -/
def lift {β : Sort*} (f : Lift ρbar A → β) (hf : ∀ (a : A.strictKernel n) ρ, f (a • ρ) = f ρ) :
    StrictClass ρbar A → β :=
  Quotient.lift f fun ρ ρ' h ↦ by
    obtain ⟨a, rfl⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp h)
    exact hf a ρ'

@[simp]
theorem lift_mk {β : Sort*} (f : Lift ρbar A → β) (hf : ∀ (a : A.strictKernel n) ρ, f (a • ρ) = f ρ)
    (ρ : Lift ρbar A) : lift f hf (mk ρ) = f ρ :=
  (rfl)

/-- The descent of an invariant function to strict classes is unique. -/
theorem lift_unique {β : Sort*} (f : Lift ρbar A → β)
    (hf : ∀ (a : A.strictKernel n) ρ, f (a • ρ) = f ρ) (g : StrictClass ρbar A → β)
    (hg : ∀ ρ, g (mk ρ) = f ρ) : g = lift f hf :=
  funext fun c ↦ by
    obtain ⟨ρ, rfl⟩ := mk_surjective c
    exact hg ρ

/-- The pushforward of strict classes along a morphism `f : A ⟶ B` of `C_Λ`. -/
def map (f : A ⟶ B) : StrictClass ρbar A → StrictClass ρbar B :=
  Quotient.map' (Lift.map f) fun ρ ρ' h ↦ by
    obtain ⟨a, rfl⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp h)
    exact MulAction.orbitRel_apply.mpr
      (MulAction.mem_orbit_iff.mpr ⟨_, (Lift.map_smul f a ρ').symm⟩)

@[simp]
theorem map_mk (f : A ⟶ B) (ρ : Lift ρbar A) : map f (mk ρ) = mk (Lift.map f ρ) :=
  (rfl)

/-- Pushforward of strict classes along the identity is the identity. -/
@[simp]
theorem map_id (c : StrictClass ρbar A) : map (𝟙 A) c = c := by
  obtain ⟨ρ, rfl⟩ := mk_surjective c
  simp

/-- Pushforward of strict classes along a composite is the composite of the pushforwards. -/
theorem map_comp (f : A ⟶ B) (f' : B ⟶ C) (c : StrictClass ρbar A) :
    map (f ≫ f') c = map f' (map f c) := by
  obtain ⟨ρ, rfl⟩ := mk_surjective c
  simp [Lift.map_comp]

/-- Over the residue field there is at most one strict class. -/
instance : Subsingleton (StrictClass ρbar (residue Λ k)) :=
  Quotient.instSubsingletonQuotient _

end StrictClass

variable (Λ) in
/-- The *deformation functor* `Def_ρbar : C_Λ ⥤ Type` of the residual representation `ρbar`,
sending `A` to the strict classes of lifts of `ρbar` to `A`. -/
-- Exposed so that `(strictClassFunctor Λ ρbar).obj A` unfolds to `StrictClass ρbar A` in
-- statements.
@[expose] def strictClassFunctor : ArtinLocalAlg Λ k ⥤ Type (max w v x) where
  obj A := StrictClass ρbar A
  map f := TypeCat.ofHom (StrictClass.map f)
  map_id A := by
    ext c : 3
    exact StrictClass.map_id c
  map_comp f f' := by
    ext c : 3
    exact StrictClass.map_comp f f' c

variable (Λ) in
@[simp]
theorem strictClassFunctor_obj (A : ArtinLocalAlg Λ k) :
    (strictClassFunctor Λ ρbar).obj A = StrictClass ρbar A :=
  (rfl)

variable (Λ) in
@[simp]
theorem strictClassFunctor_map_apply {A B : ArtinLocalAlg Λ k} (f : A ⟶ B)
    (c : StrictClass ρbar A) : (strictClassFunctor Λ ρbar).map f c = StrictClass.map f c :=
  (rfl)

variable (Λ) in
/-- The natural map from lifts to their strict classes. -/
def toStrictClass : liftFunctor Λ ρbar ⟶ strictClassFunctor Λ ρbar where
  app A := TypeCat.ofHom StrictClass.mk

variable (Λ) in
@[simp]
theorem toStrictClass_app_apply (A : ArtinLocalAlg Λ k) (ρ : Lift ρbar A) :
    (toStrictClass Λ ρbar).app A ρ = StrictClass.mk ρ :=
  (rfl)

end TauCeti.Deformation
