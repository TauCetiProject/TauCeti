/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Rep.Iso
public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import TauCeti.Algebra.Category.ModuleCat.CartanMap.Basic
public import TauCeti.RepresentationTheory.GrothendieckGroup.FDRep
import TauCeti.RepresentationTheory.OfModule

/-!
# Finite-dimensional representations as group-algebra modules

For a finite group `G` over a field `k`, the usual equivalence between representations of `G`
and modules over the group algebra `k[G]` restricts to an equivalence

`FDRep k G ≌ FGModuleCat k[G]`.

The finiteness assertion in one direction uses that `k[G]` is finite-dimensional over `k`; in
the other, a finite-dimensional representation is generated over `k[G]` by any finite set of
`k`-module generators.  This restricted equivalence identifies the abelian exact structure on
finite-dimensional representations with the exact structure of finitely generated
group-algebra modules, and is the bridge between categorical representation theory and
`G₀(k[G])`.

## Main definitions

* `TauCeti.fdRepToFGModuleFunctor`: the functor taking a representation to its group-algebra
  module.
* `TauCeti.fdRepEquivalence`: the equivalence between finite-dimensional representations and
  finitely generated group-algebra modules.
* `TauCeti.isConflationExact_fdRepEquivalence_functor` and
  `TauCeti.isConflationExact_fdRepEquivalence_inverse`: the equivalence preserves the chosen exact
  structures in both directions.
-/

public section

open CategoryTheory
open CategoryTheory.Limits
open scoped MonoidAlgebra

namespace TauCeti

universe u

variable (k G : Type u) [Field k] [Group G] [Finite G]

local instance : IsNoetherianRing k[G] := IsNoetherianRing.of_finite k k[G]

/-- The group-algebra module underlying a finite-dimensional representation, as a functor to
finitely generated modules. -/
@[expose] noncomputable def fdRepToFGModuleFunctor : FDRep k G ⥤ FGModuleCat.{u} k[G] :=
  ObjectProperty.lift (ModuleCat.isFG.{u} k[G])
    ((forget₂ (FDRep k G) (Rep.{u} k G)) ⋙
      Rep.toModuleMonoidAlgebra.{u, u, u})
    fun V ↦ (ModuleCat.isFG_iff _).mpr
      (Module.Finite.of_restrictScalars_finite k k[G]
        (_root_.Representation.asModule V.ρ))

instance : (fdRepToFGModuleFunctor k G).Faithful := by
  dsimp [fdRepToFGModuleFunctor]
  infer_instance

instance : (fdRepToFGModuleFunctor k G).Full := by
  dsimp [fdRepToFGModuleFunctor]
  infer_instance

instance : (fdRepToFGModuleFunctor k G).Additive where
  map_add := by
    intros
    rfl

instance : (fdRepToFGModuleFunctor k G).EssSurj := by
  constructor
  intro M
  let := Module.restrictScalars k k[G] M.obj
  have := IsScalarTower.restrictScalars k k[G] M.obj
  have : Module.Finite k[G] M.obj := M.2
  have : Module.Finite k M.obj := Module.Finite.trans k[G] M.obj
  let ρ := _root_.Representation.ofModule' (k := k) (G := G) M.obj
  have : Module.Finite k[G] ρ.asModule :=
    Module.Finite.of_restrictScalars_finite k k[G] ρ.asModule
  let V : FDRep k G := FDRep.of ρ
  refine ⟨V, ⟨?_⟩⟩
  change FGModuleCat.of k[G]
      (_root_.Representation.ofModule' (k := k) (G := G) M.obj).asModule ≅
    FGModuleCat.of k[G] M.obj
  exact (Representation.ofModule'AsModuleEquiv M.obj).toFGModuleCatIso

/-- **Finite-dimensional representations are finitely generated group-algebra modules.** This is
the restriction of `Rep.equivalenceModuleMonoidAlgebra` to finite objects. -/
noncomputable def fdRepEquivalence : FDRep k G ≌ FGModuleCat.{u} k[G] :=
  letI : (fdRepToFGModuleFunctor k G).IsEquivalence :=
    ⟨inferInstance, inferInstance, inferInstance⟩
  (fdRepToFGModuleFunctor k G).asEquivalence

instance : (fdRepEquivalence k G).functor.Additive := by
  dsimp [fdRepEquivalence]
  infer_instance

/-- The forward functor of `fdRepEquivalence` sends a representation to its underlying
group-algebra module. -/
@[simp]
theorem fdRepEquivalence_functor_obj_obj (V : FDRep k G) :
    ((fdRepEquivalence k G).functor.obj V).obj =
      ModuleCat.of k[G] (_root_.Representation.asModule V.ρ) := by
  rw [fdRepEquivalence, Functor.asEquivalence_functor]
  rfl

/-- On finitely generated modules over the group algebra of a finite group, the exact structure
induced from all modules is the canonical abelian exact structure. -/
private theorem finiteModulesExactStructure_monoidAlgebra_eq_abelian :
    finiteModulesExactStructure k[G] = ExactStructure.abelian (FGModuleCat.{u} k[G]) := by
  apply ExactStructure.ext
  intro S
  rw [finiteModulesExactStructure_conflation_iff, ExactStructure.abelian_conflation]
  have hι : (ModuleCat.isFG.{u} k[G]).ι =
      forget₂ (FGModuleCat.{u} k[G]) (ModuleCat.{u} k[G]) := rfl
  let _ : PreservesFiniteColimits (ModuleCat.isFG.{u} k[G]).ι :=
    hι.symm ▸ (inferInstance : PreservesFiniteColimits
      (forget₂ (FGModuleCat.{u} k[G]) (ModuleCat.{u} k[G])))
  let _ : PreservesFiniteLimits (ModuleCat.isFG.{u} k[G]).ι :=
    hι.symm ▸ (inferInstance : PreservesFiniteLimits
      (forget₂ (FGModuleCat.{u} k[G]) (ModuleCat.{u} k[G])))
  exact CategoryTheory.ShortExact.shortExact_map_iff (ModuleCat.isFG.{u} k[G]).ι

/-- The forward direction of `fdRepEquivalence` carries short exact sequences of
finite-dimensional representations to conflations of finitely generated group-algebra modules. -/
theorem isConflationExact_fdRepEquivalence_functor :
    (ExactStructure.abelian (FDRep k G)).IsConflationExact
      (finiteModulesExactStructure k[G]) (fdRepEquivalence k G).functor := by
  rw [finiteModulesExactStructure_monoidAlgebra_eq_abelian]
  exact ExactStructure.isConflationExact_abelian (fdRepEquivalence k G).functor

/-- The inverse direction of `fdRepEquivalence` carries conflations of finitely generated
group-algebra modules to short exact sequences of finite-dimensional representations. -/
theorem isConflationExact_fdRepEquivalence_inverse :
    (finiteModulesExactStructure k[G]).IsConflationExact
      (ExactStructure.abelian (FDRep k G)) (fdRepEquivalence k G).inverse := by
  rw [finiteModulesExactStructure_monoidAlgebra_eq_abelian]
  exact ExactStructure.isConflationExact_abelian (fdRepEquivalence k G).inverse

end TauCeti
