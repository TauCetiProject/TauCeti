/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.FGModuleCat.Basic
public import TauCeti.CategoryTheory.Preadditive.AdditiveClosure.Basic
public import TauCeti.RingTheory.MatlisDuality.Basic

import TauCeti.Algebra.Category.FGModuleCat.End
import TauCeti.CategoryTheory.Preadditive.Projectivization.Basic

/-!
# Projectivization and the Matlis dual in `mod A`

Let `M` be a finitely generated module over an `R`-algebra `A`, with endomorphism ring
`Γ = Module.End A M`. If the dual `D_R A` of the right regular module lies in `add M`, then the dual
`D_R M` is a finitely generated projective right `Γ`-module
(`FGModuleCat.finite_projective_end_op_matlisDual_of_additiveClosure`). By projectivization
(`TauCeti.finiteProjectiveModules_preadditiveCoyonedaObj_obj`) `Hom_A(M, D_R A)` is a finitely
generated projective right `Γ`-module, and the Hom-tensor adjunction
(`TauCeti.MatlisDual.equivLinearMapDualRegular`) identifies it with `D_R M`.

## Main results

* `FGModuleCat.finite_projective_end_op_matlisDual_of_additiveClosure`: if `D_R A` lies in
  `add M`, then `D_R M` is a finitely generated projective right module over `Module.End A M`.
-/

public section

namespace TauCeti

open CategoryTheory MatlisDual

universe w

attribute [local instance] RingHomInvPair.of_ringEquiv

/-- **Duals of `add M` and projectivization**: if an object `X` of `add M` has as underlying module
the dual `D_R A` of the right regular module, then the dual `D_R M` is a finitely generated
projective right module over `Γ = Module.End A M`, that is a left module over `Γᵐᵒᵖ`. -/
theorem _root_.FGModuleCat.finite_projective_end_op_matlisDual_of_additiveClosure {R : Type*}
    [CommRing R] {E : Type*} [AddCommGroup E] [Module R E] {A : Type*} [Ring A] [Algebra R A]
    (M : FGModuleCat.{w} A) [Module R M.obj] [IsScalarTower R A M.obj] {X : FGModuleCat.{w} A}
    (hX : additiveClosure M X) (e : X.obj ≃ₗ[A] MatlisDual R E A) :
    Module.Finite (Module.End A M.obj)ᵐᵒᵖ (MatlisDual R E M.obj) ∧
      Module.Projective (Module.End A M.obj)ᵐᵒᵖ (MatlisDual R E M.obj) := by
  -- By projectivization, `Hom(M, X)` is a finitely generated projective right module over `End M`.
  obtain ⟨hF, hP⟩ :=
    finiteProjectiveModules_iff.1 (finiteProjectiveModules_preadditiveCoyonedaObj_obj hX)
  have : Module.Finite (End M)ᵐᵒᵖ (M ⟶ X) := hF
  have : Module.Projective (End M)ᵐᵒᵖ (M ⟶ X) := hP
  -- Postcomposition with `e` and the Hom-tensor adjunction identify `Hom(M, X)` with `D_R M`,
  -- semilinearly along the isomorphism `(End M)ᵐᵒᵖ ≅ Γᵐᵒᵖ`.
  let σ := RingEquiv.op (FGModuleCat.endRingEquiv M)
  let e' : (M ⟶ X) ≃ₛₗ[(σ : (End M)ᵐᵒᵖ →+* (Module.End A M.obj)ᵐᵒᵖ)]
      MatlisDual R E M.obj :=
    { InducedCategory.homAddEquiv.trans <| ModuleCat.homAddEquiv.trans <|
        (LinearEquiv.arrowCongrAddEquiv (LinearEquiv.refl A M.obj) e).trans
          equivLinearMapDualRegular.symm.toAddEquiv with
      map_smul' g f := by
        apply (equivLinearMapDualRegular (A := A)).injective
        -- The right action of `Γ` on `D_R M` is dualization of endomorphisms
        -- (`end_op_smul_eq_map`), which the adjunction turns into precomposition.
        ext x
        simp [End.smul_left, σ] }
  exact ⟨.of_surjective e'.toLinearMap e'.surjective, .of_equiv e'⟩

end TauCeti
