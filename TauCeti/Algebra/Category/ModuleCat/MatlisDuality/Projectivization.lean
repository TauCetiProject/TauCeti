/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import TauCeti.CategoryTheory.Preadditive.AdditiveClosure.Basic
public import TauCeti.RingTheory.MatlisDuality.Basic

import TauCeti.CategoryTheory.Preadditive.Projectivization

/-!
# Projectivization and the Matlis dual

Let `M` be a module over an `R`-algebra `A`, with endomorphism ring `Γ = Module.End A M`. If the
dual `D_R A` of the right regular module lies in the additive closure `add M` in `ModuleCat A`, then
the dual `D_R M` is a finitely generated projective right `Γ`-module
(`ModuleCat.finite_projective_end_op_matlisDual_of_additiveClosure`). By projectivization
(`TauCeti.finiteProjectiveModules_preadditiveCoyonedaObj_obj`) `Hom_A(M, D_R A)` is a finitely
generated projective right `Γ`-module, and the Hom-tensor adjunction
(`TauCeti.MatlisDual.equivLinearMapDualRegular`) identifies it with `D_R M`.

## Main results

* `ModuleCat.finite_projective_end_op_matlisDual_of_additiveClosure`: if `D_R A` lies in `add M`,
  then `D_R M` is a finitely generated projective right module over `Module.End A M`.
-/

public section

namespace TauCeti

open CategoryTheory MatlisDual

universe w

attribute [local instance] RingHomInvPair.of_ringEquiv

/-- **Duals of `add M` and projectivization**: if an object `X` of `add M` has as underlying module
the dual `D_R A` of the right regular module, then the dual `D_R M` is a finitely generated
projective right module over `Γ = Module.End A M`, that is a left module over `Γᵐᵒᵖ`. -/
theorem _root_.ModuleCat.finite_projective_end_op_matlisDual_of_additiveClosure {R : Type*}
    [CommRing R] {E : Type*} [AddCommGroup E] [Module R E] {A : Type*} [Ring A] [Algebra R A]
    (M : ModuleCat.{w} A) [Module R M] [IsScalarTower R A M] {X : ModuleCat.{w} A}
    (hX : additiveClosure M X) (e : X ≃ₗ[A] MatlisDual R E A) :
    Module.Finite (Module.End A M)ᵐᵒᵖ (MatlisDual R E M) ∧
      Module.Projective (Module.End A M)ᵐᵒᵖ (MatlisDual R E M) := by
  -- By projectivization, `Hom(M, X)` is a finitely generated projective right module over `End M`.
  obtain ⟨hF, hP⟩ :=
    finiteProjectiveModules_iff.1 (finiteProjectiveModules_preadditiveCoyonedaObj_obj hX)
  have : Module.Finite (End M)ᵐᵒᵖ (M ⟶ X) := hF
  have : Module.Projective (End M)ᵐᵒᵖ (M ⟶ X) := hP
  -- Postcomposition with `e` and the Hom-tensor adjunction identify `Hom(M, X)` with `D_R M`,
  -- semilinearly along the isomorphism `(End M)ᵐᵒᵖ ≅ Γᵐᵒᵖ`.
  let σ := RingEquiv.op (ModuleCat.endRingEquiv M)
  let e' : (M ⟶ X) ≃ₛₗ[(σ : (End M)ᵐᵒᵖ →+* (Module.End A M)ᵐᵒᵖ)] MatlisDual R E M :=
    { ModuleCat.homAddEquiv.trans <|
        (LinearEquiv.arrowCongrAddEquiv (LinearEquiv.refl A M) e).trans
          equivLinearMapDualRegular.symm.toAddEquiv with
      map_smul' g f := by
        -- The right action of `Γ` on `D_R M` is dualization of endomorphisms
        -- (`end_op_smul_eq_map`), which the inverse adjunction turns into precomposition
        -- (`equivLinearMapDualRegular_symm_comp`). The `change` unfolds `homAddEquiv` and
        -- `arrowCongrAddEquiv`, writes the action of `g : (End M)ᵐᵒᵖ` on `f : M ⟶ X` as
        -- precomposition with `g.unop`, and groups the composite as `(e ∘ f) ∘ g.unop`, the form
        -- in which `equivLinearMapDualRegular_symm_comp` applies.
        change equivLinearMapDualRegular.symm
          ((e.toLinearMap ∘ₗ f.hom) ∘ₗ ModuleCat.endRingEquiv M g.unop) = _
        rw [end_op_smul_eq_map, equivLinearMapDualRegular_symm_comp]
        rfl }
  exact ⟨.of_surjective e'.toLinearMap e'.surjective, .of_equiv e'⟩

end TauCeti
