/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Algebra
public import TauCeti.Algebra.Category.ModuleCat.End
public import TauCeti.CategoryTheory.Linear.HomCokernel.Basic
public import Mathlib.Algebra.Module.ULift
public import TauCeti.Algebra.Module.AuslanderReiten.DualPresentation
import TauCeti.Algebra.Category.ModuleCat.AuslanderReiten.Defect
import TauCeti.LinearAlgebra.LinearMap.RestrictScalars

/-!
# The right transpose as a Hom cokernel

The right transpose is the cokernel of precomposition into the right regular module,
with bundled module morphisms as representatives. This comparison needs no injectivity
assumption on the presenting map and precedes the Ext computations.
-/

public section

open CategoryTheory
open scoped ModuleCat.Algebra

namespace TauCeti.FiniteProjectivePresentation

universe u v w

variable {A : Type u} [Ring A] {N : ModuleCat.{max u v} Aᵐᵒᵖ}

/-- Bundle a functional as a morphism to the lifted right regular module. -/
def rightTransposeRep {P : Type max u v} [AddCommGroup P] [Module Aᵐᵒᵖ P]
    (g : P →ₗ[Aᵐᵒᵖ] A) :
    ModuleCat.of Aᵐᵒᵖ P ⟶ ModuleCat.of Aᵐᵒᵖ (ULift.{v} A) :=
  ModuleCat.ofHom (ULift.moduleEquiv.symm.toLinearMap ∘ₗ g)

/-- The bundled transpose representative lifts the values of the original functional. -/
theorem rightTransposeRep_eq {P : Type max u v} [AddCommGroup P] [Module Aᵐᵒᵖ P]
    (g : P →ₗ[Aᵐᵒᵖ] A) :
    rightTransposeRep g = ModuleCat.ofHom (ULift.moduleEquiv.symm.toLinearMap ∘ₗ g) :=
  (rfl)

/-- Bundling a transpose representative respects precomposition. -/
@[simp]
theorem rightTransposeRep_comp {P P' : Type max u v} [AddCommGroup P] [Module Aᵐᵒᵖ P]
    [AddCommGroup P'] [Module Aᵐᵒᵖ P']
    (g : P' →ₗ[Aᵐᵒᵖ] A) (f : P →ₗ[Aᵐᵒᵖ] P') :
    rightTransposeRep (g ∘ₗ f) = ModuleCat.ofHom f ≫ rightTransposeRep g :=
  ModuleCat.ofHom_comp f (ULift.moduleEquiv.symm.toLinearMap ∘ₗ g)

/-- Left multiplication on functionals becomes postcomposition on their representatives. -/
@[simp↓]
theorem rightTransposeRep_smul {P : Type max u v} [AddCommGroup P] [Module Aᵐᵒᵖ P]
    (a : A) (g : P →ₗ[Aᵐᵒᵖ] A) :
    rightTransposeRep (a • g) = rightTransposeRep g ≫ (rightRegularEnd.{u, v} a).asHom := by
  simp [rightTransposeRep, LinearMap.smul_eq_mulLeft_comp, rightRegularEnd_asHom,
    ← ModuleCat.ofHom_comp, LinearMap.comp_assoc]

variable (Q : FiniteProjectivePresentation N)
variable (k : Type w) [CommRing k] [Algebra k A]

/-- The right transpose as the cokernel of precomposition on bundled morphisms into
the right regular module. -/
noncomputable def rightTransposeHomCokernelEquiv :
    Q.rightTranspose ≃ₗ[k] HomCokernel k Q.shortComplex.f (ModuleCat.of Aᵐᵒᵖ (ULift.{v} A)) :=
  ((Q.p.lcomp A A).cokerRestrictScalarsEquiv k).symm.trans
    (ModuleCat.covariantDefectEquivHomQuotient k (B := ModuleCat.of Aᵐᵒᵖ (ULift.{v} A))
      ULift.moduleEquiv.symm Q.shortComplex.f)

/-- The Hom cokernel comparison bundles the functional representing a transpose class. -/
@[simp↓]
theorem rightTransposeHomCokernelEquiv_mk (g : Q.P₁ →ₗ[Aᵐᵒᵖ] A) :
    let _ := Linear.homModule (R := k) Q.P₀ (ModuleCat.of Aᵐᵒᵖ (ULift.{v} A))
    let _ := Linear.homModule (R := k) Q.P₁ (ModuleCat.of Aᵐᵒᵖ (ULift.{v} A))
    Q.rightTransposeHomCokernelEquiv k (Submodule.Quotient.mk g) =
      Submodule.Quotient.mk (ModuleCat.ofHom (ULift.moduleEquiv.symm.toLinearMap ∘ₗ g)) := by
  let e := ModuleCat.covariantDefectEquivHomQuotient k (B := ModuleCat.of Aᵐᵒᵖ (ULift.{v} A))
    ULift.moduleEquiv.symm Q.shortComplex.f
  have h := LinearMap.cokerRestrictScalarsEquiv_symm_mk k (Q.p.lcomp A A) g
  -- The restricted-scalar cokernel of precomposition is the covariant defect.
  have h' := ModuleCat.covariantDefectEquivHomQuotient_mk k (B := ModuleCat.of Aᵐᵒᵖ (ULift.{v} A))
    ULift.moduleEquiv.symm Q.shortComplex.f g
  exact (congrArg (fun x ↦ e x) h).trans (h'.trans (by simp))

end TauCeti.FiniteProjectivePresentation
