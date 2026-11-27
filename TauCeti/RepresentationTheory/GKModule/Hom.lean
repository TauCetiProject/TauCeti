/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.GKModule.Basic

/-!
# Morphisms of `(𝔤, K)`-modules

A **morphism** of `(𝔤, K)`-modules `M → N` is a `𝔤`-module morphism commuting with the actions of
`K`. As for `TauCeti.GKModule`, only the monoid structure of `K` is used.

## Main definitions

* `TauCeti.GKModule.Hom M N`: the morphisms of `(𝔤, K)`-modules, with `id` and `comp`.
* `TauCeti.GKModule.Hom.toIntertwiningMap φ`: the underlying intertwining map of the actions of
  `K`.

## Main statements

* `TauCeti.GKModule.Hom.id_comp`, `TauCeti.GKModule.Hom.comp_id`,
  `TauCeti.GKModule.Hom.comp_assoc`: the category laws.

## References

* J. Bernstein and B. Krötz, *Smooth Fréchet globalizations of Harish-Chandra modules*, Israel J.
  Math. 199 (2014), 45–111, §4.1.
-/

public section

namespace TauCeti

open Representation

variable {k 𝔤 K : Type*} [Field k] [LieRing 𝔤] [LieAlgebra k 𝔤] [Monoid K]
  {Ad : Representation k K 𝔤} [IsLieAction Ad]
  {V : Type*} [AddCommGroup V] [Module k V] [LieRingModule 𝔤 V] [LieModule k 𝔤 V]
  {W : Type*} [AddCommGroup W] [Module k W] [LieRingModule 𝔤 W] [LieModule k 𝔤 W]
  {U : Type*} [AddCommGroup U] [Module k U] [LieRingModule 𝔤 U] [LieModule k 𝔤 U]
  {X : Type*} [AddCommGroup X] [Module k X] [LieRingModule 𝔤 X] [LieModule k 𝔤 X]

namespace GKModule

/-- A **morphism of `(𝔤, K)`-modules**: a `𝔤`-module morphism commuting with the actions of
`K`. -/
structure Hom (M : GKModule Ad V) (N : GKModule Ad W) extends V →ₗ⁅k,𝔤⁆ W where
  /-- The morphism commutes with the actions of `K`. -/
  map_ρ (g : K) (v : V) : toLieModuleHom (M.ρ g v) = N.ρ g (toLieModuleHom v)

namespace Hom

variable {M : GKModule Ad V} {N : GKModule Ad W} {P : GKModule Ad U} {Q : GKModule Ad X}

/-- A morphism of `(𝔤, K)`-modules is a function through its underlying `𝔤`-module morphism. -/
instance instFunLike : FunLike (Hom M N) V W where
  coe φ := φ.toLieModuleHom
  coe_injective φ ψ h := by
    obtain ⟨φ, _⟩ := φ
    obtain ⟨ψ, _⟩ := ψ
    congr
    exact LieModuleHom.coe_injective h

/-- A morphism of `(𝔤, K)`-modules is linear. -/
instance instLinearMapClass : LinearMapClass (Hom M N) k V W where
  map_add φ := map_add φ.toLieModuleHom
  map_smulₛₗ φ := map_smul φ.toLieModuleHom

@[simp]
theorem coe_toLieModuleHom (φ : Hom M N) : ⇑φ.toLieModuleHom = φ :=
  (rfl)

@[simp]
theorem coe_mk (f : V →ₗ⁅k,𝔤⁆ W) (h : ∀ (g : K) (v : V), f (M.ρ g v) = N.ρ g (f v)) :
    ⇑(⟨f, h⟩ : Hom M N) = f :=
  (rfl)

theorem toLieModuleHom_injective :
    Function.Injective (toLieModuleHom : Hom M N → V →ₗ⁅k,𝔤⁆ W) := fun _ _ h ↦
  DFunLike.ext _ _ (LieModuleHom.congr_fun h)

@[ext]
theorem ext {φ ψ : Hom M N} (h : ∀ v, φ v = ψ v) : φ = ψ :=
  DFunLike.ext _ _ h

@[simp]
theorem map_lie (φ : Hom M N) (x : 𝔤) (v : V) : φ ⁅x, v⁆ = ⁅x, φ v⁆ :=
  φ.toLieModuleHom.map_lie x v

@[simp]
theorem map_ρ_apply (φ : Hom M N) (g : K) (v : V) : φ (M.ρ g v) = N.ρ g (φ v) :=
  φ.map_ρ g v

/-- The underlying intertwining map `M.ρ → N.ρ` of the actions of `K`. -/
def toIntertwiningMap (φ : Hom M N) : IntertwiningMap M.ρ N.ρ :=
  φ.toLieModuleHom.toLinearMap.intertwiningMap_of_isIntertwiningMap M.ρ N.ρ φ.map_ρ

@[simp]
theorem coe_toIntertwiningMap (φ : Hom M N) : ⇑φ.toIntertwiningMap = φ :=
  (rfl)

variable (M) in
/-- The identity morphism. -/
def id : Hom M M where
  toLieModuleHom := LieModuleHom.id
  map_ρ _ _ := rfl

@[simp]
theorem coe_id : ⇑(id M) = _root_.id :=
  (rfl)

theorem id_apply (v : V) : id M v = v :=
  (rfl)

/-- The composite of two morphisms. -/
def comp (ψ : Hom N P) (φ : Hom M N) : Hom M P where
  toLieModuleHom := ψ.toLieModuleHom.comp φ.toLieModuleHom
  map_ρ g v := (congrArg ψ (φ.map_ρ g v)).trans (ψ.map_ρ g (φ v))

@[simp]
theorem coe_comp (ψ : Hom N P) (φ : Hom M N) : ⇑(ψ.comp φ) = ψ ∘ φ :=
  (rfl)

@[simp]
theorem comp_apply (ψ : Hom N P) (φ : Hom M N) (v : V) : ψ.comp φ v = ψ (φ v) :=
  (rfl)

@[simp]
theorem id_comp (φ : Hom M N) : (id N).comp φ = φ :=
  ext fun _ ↦ rfl

@[simp]
theorem comp_id (φ : Hom M N) : φ.comp (id M) = φ :=
  ext fun _ ↦ rfl

theorem comp_assoc (χ : Hom P Q) (ψ : Hom N P) (φ : Hom M N) :
    (χ.comp ψ).comp φ = χ.comp (ψ.comp φ) :=
  ext fun _ ↦ rfl

end Hom

end GKModule

end TauCeti
