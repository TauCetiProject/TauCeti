/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import TauCeti.Algebra.Category.ModuleCat.AuslanderReiten.HomCokernel
public import TauCeti.Algebra.Category.ModuleCat.Ext.MatlisDualRegular
public import TauCeti.Algebra.Category.ModuleCat.MatlisDuality.ShortExact
import TauCeti.Algebra.Category.ModuleCat.MatlisDuality.HomCokernel
import TauCeti.Algebra.Homology.Ext.Copresentation
import TauCeti.Algebra.Category.ModuleCat.MatlisDuality.Injective

/-!
# Computing the right transpose by Ext¹ of the Matlis duals

Dualizing a length-one projective resolution gives an injective copresentation. When the
right regular module has finite length over `R` and the injective coefficient module `E`
satisfies `length_R Hom_R(R/𝔪, E) = 1` for every maximal ideal `𝔪`, the covariant
Hom-cokernel comparison identifies the transpose of a right module `N` with `Ext¹(D A, D N)`.
The left action comes from pullback along duals of left multiplications on the right regular
module.
-/

public section

open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra

universe u v w a

namespace TauCeti.FiniteProjectivePresentation

variable (R : Type w) [CommRing R] (E : Type v) [AddCommGroup E] [Module R E]
  [Small.{v} R] [Module.Injective R E] {A : Type a} [Ring A] [Algebra R A]
  {N : ModuleCat.{max a u v} Aᵐᵒᵖ} (Q : FiniteProjectivePresentation N)
  (hE : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Module.length R (R ⧸ 𝔪 →ₗ[R] E) = 1)

open TauCeti.Abelian

local notation "D" => ModuleCat.matlisDualOpObj R E

private theorem injective_dual_shortComplex_X₂ :
    Injective (Q.shortComplex.op.map (ModuleCat.matlisDualOp.{w, v, a, max a u v} R E)).X₂ :=
  injective_matlisDualOpObj_of_projective.{a, v, u, w} R E Q.P₀

attribute [local instance] ModuleCat.moduleOfAlgebra ModuleCat.isScalarTower_moduleOfAlgebra

variable (hB : @IsFiniteLength R _ (ModuleCat.of Aᵐᵒᵖ (ULift.{max u v} A)) _
  (ModuleCat.moduleOfAlgebra R (ModuleCat.of Aᵐᵒᵖ (ULift.{max u v} A))))

/-- The transpose of a length-one right projective resolution computes `Ext¹(D A, D N)`
via the dual injective copresentation. The coefficient module is injective over `R`,
with a length-one socle over each residue field, and the right regular module has finite
length over `R`. For a resolution of `N = D M`, this gives the Ext computation of the
inverse Auslander–Reiten translate of `M`. -/
noncomputable def rightTransposeEquivExtDual (hp : Function.Injective Q.p) :
    Q.rightTranspose ≃ₗ[R] Ext (D (ModuleCat.of Aᵐᵒᵖ (ULift.{max u v} A))) (D N) 1 := by
  have := injective_dual_shortComplex_X₂.{u, v, w, a} R E Q
  let hS := (Q.shortExact_shortComplex hp).matlisDualOp.{w, v, a, max a u} R E
  let e := ModuleCat.matlisDualOpHomCokernelEquiv.{w, v, max a u, a}
    (B := ModuleCat.of Aᵐᵒᵖ (ULift.{max u v} A)) hE hB Q.shortComplex.f
  exact (Q.rightTransposeHomCokernelEquiv.{a, max u v, w} R).trans
    (e.trans (covariantHomCokernelEquivExt R hS _))

/-- Under the dual comparison, a functional represents the pullback of the dual short exact
sequence along the dual of the functional. -/
@[simp↓]
theorem rightTransposeEquivExtDual_mk (hp : Function.Injective Q.p) (g : Q.P₁ →ₗ[Aᵐᵒᵖ] A) :
    Q.rightTransposeEquivExtDual.{u, v, w, a} R E hE hB hp (Submodule.Quotient.mk g) =
      (Ext.mk₀ (ModuleCat.matlisDualOpMap R E
        (ModuleCat.ofHom (ULift.moduleEquiv.{a, a, max u v}.symm.toLinearMap ∘ₗ g)))).comp
        ((Q.shortExact_shortComplex hp).matlisDualOp.{w, v, a, max a u} R E).extClass
        (zero_add 1) := by
  rw [rightTransposeEquivExtDual, LinearEquiv.trans_apply, rightTransposeHomCokernelEquiv_mk]
  have := injective_dual_shortComplex_X₂.{u, v, w, a} R E Q
  let hS := (Q.shortExact_shortComplex hp).matlisDualOp.{w, v, a, max a u} R E
  let g' : Q.P₁ ⟶ ModuleCat.of Aᵐᵒᵖ (ULift.{max u v} A) :=
    ModuleCat.ofHom (ULift.moduleEquiv.{a, a, max u v}.symm.toLinearMap ∘ₗ g)
  exact (congrArg (covariantHomCokernelEquivExt R hS _)
    (ModuleCat.matlisDualOpHomCokernelEquiv_mk.{w, v, max a u, a} hE hB Q.shortComplex.f g')).trans
      (covariantHomCokernelEquivExt_mk R hS _ (ModuleCat.matlisDualOpMap R E g'))

/-- The left action on the transpose corresponds to pulling back along the dual of left
multiplication on the right regular module. -/
theorem rightTransposeEquivExtDual_smul (hp : Function.Injective Q.p) (a : A)
    (x : Q.rightTranspose) :
    Q.rightTransposeEquivExtDual.{u, v, w, a} R E hE hB hp (a • x) =
      (Ext.mk₀ (ModuleCat.matlisDualOpMap R E (rightRegularEnd a).asHom)).comp
        (Q.rightTransposeEquivExtDual.{u, v, w, a} R E hE hB hp x) (zero_add 1) := by
  obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hrep := rightTransposeRep_smul.{a, max u v} a g
  simp only [rightTransposeRep_eq] at hrep
  rw [← Submodule.Quotient.mk_smul, rightTransposeEquivExtDual_mk, rightTransposeEquivExtDual_mk]
  simp only [hrep, ModuleCat.matlisDualOpMap_comp]
  exact (Ext.mk₀_comp_mk₀_assoc _ _ _).symm

/-- Precomposition on relation modules agrees, under the dual comparison, with pushforward along
the dual of the map of presented modules. -/
theorem rightTransposeEquivExtDual_naturality {N' : ModuleCat.{max a u v} Aᵐᵒᵖ}
    (P : FiniteProjectivePresentation N') (hQ : Function.Injective Q.p)
    (hP : Function.Injective P.p) (φ : Q.shortComplex ⟶ P.shortComplex)
    (x : P.rightTranspose) :
    Q.rightTransposeEquivExtDual.{u, v, w, a} R E hE hB hQ (Q.rightTransposeMap P φ x) =
      (P.rightTransposeEquivExtDual.{u, v, w, a} R E hE hB hP x).comp
        (Ext.mk₀ (ModuleCat.matlisDualOpMap R E φ.τ₃)) (add_zero 1) := by
  obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  let Df : (ModuleCat.{max a u v} Aᵐᵒᵖ)ᵒᵖ ⥤ ModuleCat.{max a u v} A :=
    ModuleCat.matlisDualOp.{w, v, a, max a u v} R E
  let ψ : P.shortComplex.op.map Df ⟶ Q.shortComplex.op.map Df :=
    Df.mapShortComplex.map (ShortComplex.opMap φ)
  -- The opposite complex swaps the endpoint maps before dualizing. State those
  -- endpoints explicitly so subsequent Ext composition does not reduce functor wrappers.
  have hclass :
      ((P.shortExact_shortComplex hP).matlisDualOp.{w, v, a, max a u} R E).extClass.comp
          (Ext.mk₀ (ModuleCat.matlisDualOpMap R E φ.τ₃)) (add_zero 1) =
        (Ext.mk₀ (ModuleCat.matlisDualOpMap R E φ.τ₁)).comp
          ((Q.shortExact_shortComplex hQ).matlisDualOp.{w, v, a, max a u} R E).extClass
          (zero_add 1) :=
    ((P.shortExact_shortComplex hP).matlisDualOp.{w, v, a, max a u} R E).extClass_naturality
      ((Q.shortExact_shortComplex hQ).matlisDualOp.{w, v, a, max a u} R E) ψ
  have hrep := rightTransposeRep_comp.{a, max u v} g φ.τ₁.hom
  simp only [rightTransposeRep_eq, ModuleCat.ofHom_hom] at hrep
  rw [rightTransposeMap_mk, rightTransposeEquivExtDual_mk, rightTransposeEquivExtDual_mk]
  simp only [hrep, ModuleCat.matlisDualOpMap_comp]
  refine (Ext.mk₀_comp_mk₀_assoc _ _ _).symm.trans ?_
  refine Eq.trans ?_ (Ext.comp_assoc_of_third_deg_zero _ _ _ _).symm
  have h := congrArg (fun α : Ext (D P.shortComplex.X₁) (D N) 1 ↦
    (Ext.mk₀ (ModuleCat.matlisDualOpMap R E (rightTransposeRep.{a, max u v} g))).comp
      α (zero_add 1)) hclass.symm
  rw [rightTransposeRep_eq] at h
  exact h

/-- The dual Ext computation as an equivalence of left `A`-modules under the same
finite-length and dualizing-coefficient hypotheses as `rightTransposeEquivExtDual`. -/
noncomputable def rightTransposeLinearEquivExtDual (hp : Function.Injective Q.p) :
    Q.rightTranspose ≃ₗ[A]
      ExtWithSourceAction (matlisDualRightRegularEnd.{u, v, w, a} R E (A := A)) (D N) 1 :=
  ExtWithSourceAction.linearEquivOfCompat (matlisDualRightRegularEnd.{u, v, w, a} R E)
    (Q.rightTransposeEquivExtDual.{u, v, w, a} R E hE hB hp).toAddEquiv (by
      intro b x
      rw [matlisDualRightRegularEnd_unop_asHom]
      exact Q.rightTransposeEquivExtDual_smul.{u, v, w, a} R E hE hB hp b x)

/-- Forgetting the left action gives the same dual Ext class as the scalar comparison. -/
@[simp↓]
theorem rightTransposeLinearEquivExtDual_toExt (hp : Function.Injective Q.p)
    (x : Q.rightTranspose) :
    ExtWithSourceAction.toExt (matlisDualRightRegularEnd.{u, v, w, a} R E)
        (Q.rightTransposeLinearEquivExtDual.{u, v, w, a} R E hE hB hp x) =
      Q.rightTransposeEquivExtDual.{u, v, w, a} R E hE hB hp x :=
  ExtWithSourceAction.toExt_linearEquivOfCompat
    (matlisDualRightRegularEnd.{u, v, w, a} R E (A := A)) _ _ x

/-- The left-linear dual Ext comparison sends transpose maps to pushforward along the dual of
the presented map. -/
theorem rightTransposeLinearEquivExtDual_naturality {N' : ModuleCat.{max a u v} Aᵐᵒᵖ}
    (P : FiniteProjectivePresentation N') (hQ : Function.Injective Q.p)
    (hP : Function.Injective P.p) (φ : Q.shortComplex ⟶ P.shortComplex)
    (x : P.rightTranspose) :
    Q.rightTransposeLinearEquivExtDual.{u, v, w, a} R E hE hB hQ (Q.rightTransposeMap P φ x) =
      ExtWithSourceAction.map (matlisDualRightRegularEnd.{u, v, w, a} R E)
        (ModuleCat.matlisDualOpMap R E φ.τ₃)
        (P.rightTransposeLinearEquivExtDual.{u, v, w, a} R E hE hB hP x) := by
  apply (ExtWithSourceAction.toExt (matlisDualRightRegularEnd.{u, v, w, a} R E (A := A))).injective
  rw [ExtWithSourceAction.toExt_map, rightTransposeLinearEquivExtDual_toExt,
    rightTransposeLinearEquivExtDual_toExt]
  exact Q.rightTransposeEquivExtDual_naturality.{u, v, w, a} R E hE hB P hQ hP φ x

end TauCeti.FiniteProjectivePresentation
