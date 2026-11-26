/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.RepresentationTheory.Invariants
public import TauCeti.CategoryTheory.Galois.Sheaf
public import TauCeti.RepresentationTheory.ToAction

/-!
# Sheaves of modules on finite continuous `G`-sets from representations

Let `G` be a topological group and `ρ` a representation of `G` on a `Λ`-module `M`. On a finite
continuous `G`-set `S`, the `G`-equivariant maps from `S` to `M` form a `Λ`-module
(`ContAction.equivariantMaps ρ S`), and restriction along `G`-maps makes them a presheaf of
`Λ`-modules (`ContAction.modulePresheaf ρ`). Its underlying presheaf of sets is the presheaf of
`G`-maps into the underlying `G`-set `Representation.toAction ρ` of `ρ`
(`ContAction.modulePresheafCompForgetIso`), so it is a sheaf for the jointly surjective topology
(`ContAction.isSheaf_modulePresheaf`), bundled as `ContAction.moduleSheaf ρ`. When `Λ` is
Noetherian and `M` is finitely generated, its values are finitely generated. Its sections over a
point are the invariants of `ρ` (`ContAction.modulePresheafObjEquivInvariants`), and for `G` finite
discrete and `M ≠ 0` it has a nonzero section over the left regular `G`-set
(`ContAction.nontrivial_modulePresheaf_obj_leftRegular`).

## Main definitions

* `ContAction.equivariantMaps ρ S`: the `Λ`-module of `G`-maps from `S` to `M`.
* `ContAction.modulePresheaf ρ`: the presheaf of these modules on finite continuous `G`-sets, with
  sections `ContAction.modulePresheafObjEquiv`, determined by their values
  (`ContAction.modulePresheafObj_ext`).
* `ContAction.moduleSheaf ρ`: the same presheaf, as a sheaf for the jointly surjective topology.
* `ContAction.modulePresheafObjEquivInvariants`: sections over a terminal `G`-set are invariants.

## Main results

* `ContAction.isSheaf_modulePresheaf`: `G`-maps into a representation form a sheaf of
  `Λ`-modules for the jointly surjective topology.
* `ContAction.nontrivial_modulePresheaf_obj_leftRegular`: a nonzero section over the left regular
  `G`-set.
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
def equivariantMaps (S : ContAction FintypeCat.{u} G) :
    Submodule Λ ((fiberFunctor G).obj S → M) where
  carrier := {φ | ∀ (g : G) s, φ (g • s) = ρ g (φ s)}
  add_mem' {φ ψ} hφ hψ g s := by simp [hφ g s, hψ g s]
  zero_mem' g s := by simp
  smul_mem' c φ hφ g s := by simp [hφ g s]

@[simp]
theorem mem_equivariantMaps {S : ContAction FintypeCat.{u} G}
    (φ : (fiberFunctor G).obj S → M) :
    φ ∈ equivariantMaps ρ S ↔ ∀ (g : G) s, φ (g • s) = ρ g (φ s) :=
  Iff.rfl

/-- The presheaf of `Λ`-modules of `G`-equivariant maps into a representation `ρ` of `G`, on
finite continuous `G`-sets; restriction is precomposition. -/
def modulePresheaf : (ContAction FintypeCat.{u} G)ᵒᵖ ⥤ ModuleCat.{u} Λ where
  obj S := ModuleCat.of Λ (equivariantMaps ρ S.unop)
  map f := ModuleCat.ofHom
    { toFun φ := ⟨φ.val ∘ (fiberFunctor G).map f.unop, (mem_equivariantMaps ρ _).2 fun g s ↦ by
        simp only [Function.comp_apply, fiberFunctor_map_smul,
          (mem_equivariantMaps ρ _).1 φ.property]⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }

/-- The sections of `modulePresheaf ρ` over `S` are the `G`-maps from `S` into `ρ`. -/
noncomputable def modulePresheafObjEquiv (S : ContAction FintypeCat.{u} G) :
    (modulePresheaf ρ).obj (op S) ≃ₗ[Λ] equivariantMaps ρ S :=
  LinearEquiv.refl _ _

/-- Restriction of `G`-equivariant maps is precomposition. -/
theorem modulePresheafObjEquiv_map_apply {S T : ContAction FintypeCat.{u} G} (f : T ⟶ S)
    (φ : (modulePresheaf ρ).obj (op S)) (t : (fiberFunctor G).obj T) :
    (modulePresheafObjEquiv ρ T ((modulePresheaf ρ).map f.op φ)).val t =
      (modulePresheafObjEquiv ρ S φ).val ((fiberFunctor G).map f t) :=
  (rfl)

/-- Sections of `modulePresheaf ρ` are determined by their values. -/
theorem modulePresheafObj_ext {S : ContAction FintypeCat.{u} G}
    {φ ψ : (modulePresheaf ρ).obj (op S)}
    (h : ∀ s, (modulePresheafObjEquiv ρ S φ).val s = (modulePresheafObjEquiv ρ S ψ).val s) :
    φ = ψ :=
  (modulePresheafObjEquiv ρ S).injective (Subtype.ext (funext h))

/-- The underlying presheaf of sets of `modulePresheaf ρ` is the presheaf of `G`-maps into the
underlying `G`-set of `ρ`. -/
noncomputable def modulePresheafCompForgetIso :
    modulePresheaf ρ ⋙ forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u} ⋙ forget AddCommGrpCat.{u} ≅
      (homPresheaf G).obj ρ.toAction :=
  -- `ρ.toAction` is `Action.ofMulAction` for `MulAction.compHom M ρ`, so its underlying type is
  -- `M` and `g` acts on it by `ρ g`, definitionally (`Representation.toAction_V`,
  -- `Representation.toAction_ρ_apply`). Hence the defining condition of `equivariantMaps ρ` and
  -- `MulActionHom.map_smul'` for `G`-maps into `ρ.toAction.V` agree, and both directions keep the
  -- underlying function, so naturality (precomposition on both sides) is `rfl`. The `let` only
  -- states the type `→[G] ρ.toAction.V` through the `ToType` wrapper of the presheaf's values.
  NatIso.ofComponents (fun S ↦ Equiv.toIso
    { toFun φ := (⟨φ.val, φ.property⟩ : (fiberFunctor G).obj S.unop →[G] ρ.toAction.V)
      invFun φ :=
        let ψ : (fiberFunctor G).obj S.unop →[G] ρ.toAction.V := φ
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
        (isSheaf_homPresheaf ρ.toAction)))

/-- The `G`-equivariant maps into a representation `ρ`, as a sheaf of `Λ`-modules on finite
continuous `G`-sets for the jointly surjective topology. -/
noncomputable def moduleSheaf [IsTopologicalGroup G] :
    Sheaf (jointlySurjectiveTopology G) (ModuleCat.{u} Λ) :=
  ⟨modulePresheaf ρ, isSheaf_modulePresheaf ρ⟩

/-- The underlying presheaf of `moduleSheaf ρ` is `modulePresheaf ρ`. -/
@[simp]
theorem moduleSheaf_obj [IsTopologicalGroup G] : (moduleSheaf ρ).obj = modulePresheaf ρ :=
  (rfl)

/-- The `G`-equivariant maps from a finite `G`-set to a finitely generated module over a
Noetherian ring form a finitely generated module. -/
instance instModuleFiniteModulePresheafObj [IsNoetherianRing Λ] [Module.Finite Λ M]
    (S : (ContAction FintypeCat.{u} G)ᵒᵖ) : Module.Finite Λ ((modulePresheaf ρ).obj S) :=
  have : Finite ((fiberFunctor G).obj S.unop) := inferInstanceAs (Finite S.unop.obj.V)
  Module.Finite.of_injective (equivariantMaps ρ S.unop).subtype Subtype.val_injective

variable [IsTopologicalGroup G]

/-- **`G`-maps from a point are the invariants.** Over a terminal finite continuous `G`-set `S`,
whose underlying set is a point, evaluation at that point identifies the `G`-maps from `S` into
`ρ` with the invariants of `ρ`. -/
noncomputable def modulePresheafObjEquivInvariants {S : ContAction FintypeCat.{u} G}
    (hS : IsTerminal S) : (modulePresheaf ρ).obj (op S) ≃ₗ[Λ] Representation.invariants ρ :=
  letI : Unique ((fiberFunctor G).obj S) :=
    Types.isTerminalEquivUnique _ (hS.isTerminalObj (fiberFunctor G))
  { toFun φ := ⟨φ.val default, fun g ↦ by
      rw [← (mem_equivariantMaps ρ _).1 φ.property, Subsingleton.elim (g • default) default]⟩
    invFun v := ⟨fun _ ↦ v, (mem_equivariantMaps ρ _).2 fun g _ ↦ (v.property g).symm⟩
    map_add' _ _ := rfl
    map_smul' _ _ := rfl
    left_inv φ := Subtype.ext (funext fun s ↦ by rw [Subsingleton.elim s default])
    right_inv _ := rfl }

/-- Under `modulePresheafObjEquivInvariants`, a `G`-map from a point is sent to its value. -/
theorem coe_modulePresheafObjEquivInvariants_apply {S : ContAction FintypeCat.{u} G}
    (hS : IsTerminal S) (φ : (modulePresheaf ρ).obj (op S)) (s : (fiberFunctor G).obj S) :
    (modulePresheafObjEquivInvariants ρ hS φ : M) = (modulePresheafObjEquiv ρ S φ).val s := by
  let : Unique ((fiberFunctor G).obj S) :=
    Types.isTerminalEquivUnique _ (hS.isTerminalObj (fiberFunctor G))
  rw [Subsingleton.elim s default]
  rfl

/-- **`G`-maps from the left regular `G`-set.** For a finite discrete group `G` and `M ≠ 0`, there
is a nonzero `G`-map from the left regular `G`-set into `ρ`: the orbit map `g ↦ ρ g m` of a
nonzero `m`. -/
theorem nontrivial_modulePresheaf_obj_leftRegular [Finite G] [DiscreteTopology G] [Nontrivial M] :
    Nontrivial ((modulePresheaf ρ).obj (op (leftRegular G))) := by
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  let φ : equivariantMaps ρ (leftRegular G) :=
    ⟨fun x ↦ ρ (leftRegularFiberEquiv G x) m, (mem_equivariantMaps ρ _).2 fun g x ↦ by
      rw [leftRegularFiberEquiv_smul, map_mul, mul_apply_eq_comp]⟩
  refine (modulePresheafObjEquiv ρ _).nontrivial_congr.2 ⟨φ, 0, fun h ↦ hm ?_⟩
  simpa [φ] using congr(Subtype.val $h ((leftRegularFiberEquiv G).symm 1))

end ContAction
