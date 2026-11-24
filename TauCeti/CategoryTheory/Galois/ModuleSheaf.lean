/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.RepresentationTheory.Basic
public import TauCeti.CategoryTheory.Galois.Sheaf

/-!
# Sheaves of modules on finite continuous `G`-sets from representations

Let `G` be a topological group and `ρ` a representation of `G` on a `Λ`-module `M`. On a finite
continuous `G`-set `S`, the `G`-equivariant maps from `S` to `M` form a `Λ`-module
(`ContAction.equivariantMaps ρ S`), and restriction along `G`-maps makes them a presheaf of
`Λ`-modules (`ContAction.modulePresheaf ρ`). Its underlying presheaf of sets is the presheaf of
`G`-maps into the underlying `G`-set of `ρ` (`ContAction.modulePresheafCompForgetIso`), so it is a
sheaf for the jointly surjective topology (`ContAction.isSheaf_modulePresheaf`). When `Λ` is
Noetherian and `M` is finitely generated, its values are finitely generated.

## Main definitions

* `ContAction.equivariantMaps ρ S`: the `Λ`-module of `G`-maps from `S` to `M`.
* `ContAction.modulePresheaf ρ`: the presheaf of these modules on finite continuous `G`-sets.

## Main results

* `ContAction.isSheaf_modulePresheaf`: `G`-maps into a representation form a sheaf of
  `Λ`-modules for the jointly surjective topology.
-/

public section

open CategoryTheory Limits Opposite FintypeCatDiscrete

universe u

namespace ContAction

variable {G : Type u} [Group G] [TopologicalSpace G]
  {Λ : Type u} [CommRing Λ] {M : Type u} [AddCommGroup M] [Module Λ M]
  (ρ : Representation Λ G M)

/-- The `Λ`-module of `G`-equivariant maps from the underlying set of a finite continuous `G`-set
`S` to a representation `ρ` of `G` on `M`. -/
@[expose]
def equivariantMaps (S : ContAction FintypeCat.{u} G) :
    Submodule Λ ((fiberFunctor G).obj S → M) where
  carrier := {φ | ∀ (g : G) s, φ (g • s) = ρ g (φ s)}
  add_mem' {φ ψ} hφ hψ g s := by simp [hφ g s, hψ g s]
  zero_mem' g s := by simp
  smul_mem' c φ hφ g s := by simp [hφ g s]

theorem mem_equivariantMaps {S : ContAction FintypeCat.{u} G}
    (φ : (fiberFunctor G).obj S → M) :
    φ ∈ equivariantMaps ρ S ↔ ∀ (g : G) s, φ (g • s) = ρ g (φ s) :=
  Iff.rfl

/-- The presheaf of `Λ`-modules of `G`-equivariant maps into a representation `ρ` of `G`, on
finite continuous `G`-sets; restriction is precomposition. -/
@[expose]
def modulePresheaf : (ContAction FintypeCat.{u} G)ᵒᵖ ⥤ ModuleCat.{u} Λ where
  obj S := ModuleCat.of Λ (equivariantMaps ρ S.unop)
  map f := ModuleCat.ofHom
    { toFun φ := ⟨φ.val ∘ (fiberFunctor G).map f.unop, fun g s ↦ by
        rw [Function.comp_apply, fiberFunctor_map_smul, φ.property]; rfl⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }

/-- Restriction of `G`-equivariant maps is precomposition. -/
@[simp]
theorem modulePresheaf_map_apply {S T : ContAction FintypeCat.{u} G} (f : T ⟶ S)
    (φ : (modulePresheaf ρ).obj (op S)) (t : (fiberFunctor G).obj T) :
    ((modulePresheaf ρ).map f.op φ).val t = φ.val ((fiberFunctor G).map f t) :=
  (rfl)

/-- The `G`-set underlying a representation `ρ` of `G`. -/
@[expose]
def representationAction : Action (Type u) G where
  V := M
  ρ := (TypeCat.endEquiv _).toMonoidHom.comp
    { toFun g := (ρ g : M → M)
      map_one' := funext fun _ ↦ by simp; rfl
      map_mul' _ _ := funext fun _ ↦ by simp; rfl }

/-- The underlying presheaf of sets of `modulePresheaf ρ` is the presheaf of `G`-maps into the
underlying `G`-set of `ρ`. -/
noncomputable def modulePresheafCompForgetIso :
    modulePresheaf ρ ⋙ forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u} ⋙ forget AddCommGrpCat.{u} ≅
      (homPresheaf G).obj (representationAction ρ) :=
  NatIso.ofComponents (fun S ↦ Equiv.toIso
    { toFun φ := (⟨φ.val, φ.property⟩ :
        (fiberFunctor G).obj S.unop →[G] (representationAction ρ).V)
      invFun φ :=
        let ψ : (fiberFunctor G).obj S.unop →[G] (representationAction ρ).V := φ
        ⟨ψ, ψ.map_smul'⟩
      left_inv _ := rfl
      right_inv _ := rfl }) fun _ ↦ rfl

/-- **`G`-maps into a representation form a sheaf of modules.** For a representation `ρ` of `G`
on a `Λ`-module, the `G`-equivariant maps into it form a sheaf of `Λ`-modules on finite
continuous `G`-sets for the jointly surjective topology. -/
theorem isSheaf_modulePresheaf [IsTopologicalGroup G] :
    Presheaf.IsSheaf (jointlySurjectiveTopology G) (modulePresheaf ρ) :=
  Presheaf.isSheaf_of_isSheaf_comp _ _ (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})
    (Presheaf.isSheaf_of_isSheaf_comp _ _ (forget AddCommGrpCat.{u})
      ((Presheaf.isSheaf_of_iso_iff (modulePresheafCompForgetIso ρ)).2
        (isSheaf_homPresheaf (representationAction ρ))))

/-- The `G`-equivariant maps from a finite `G`-set to a finitely generated module over a
Noetherian ring form a finitely generated module. -/
instance instModuleFiniteModulePresheafObj [IsNoetherianRing Λ] [Module.Finite Λ M]
    (S : (ContAction FintypeCat.{u} G)ᵒᵖ) : Module.Finite Λ ((modulePresheaf ρ).obj S) :=
  have : Finite ((fiberFunctor G).obj S.unop) := inferInstanceAs (Finite S.unop.obj.V)
  Module.Finite.of_injective (equivariantMaps ρ S.unop).subtype Subtype.val_injective

end ContAction
