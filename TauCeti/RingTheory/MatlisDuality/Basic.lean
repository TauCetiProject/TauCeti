/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Algebra.Module.Dual.ProjectiveInjective
import TauCeti.Algebra.Module.Opposite
public import TauCeti.LinearAlgebra.Dual.RightAction
public import TauCeti.RingTheory.MatlisDuality.Semilocal

/-!
# The Matlis dual of a module over an algebra

Let `R` be a commutative ring, `E` an `R`-module and `A` an `R`-algebra. The Matlis dual
`D_R N = Hom_R(N, E)` exchanges left and right `A`-modules. This file defines it with its
contravariant action on morphisms, shows that for injective `E` it sends projective modules to
injective modules, and proves that evaluation `N → D_R (D_R N)` is an isomorphism of `A`-modules for
`N` of finite length over `R`, when `E` is an injective hull of `R ⧸ J(R)` and `R ⧸ J(R)` is
semisimple.

Right `A`-modules are modules over `Aᵐᵒᵖ`.

## Main definitions

* `TauCeti.MatlisDual R E N`: the module `Hom_R(N, E)`, a right module when `N` is a left `A`-module
  and a left module when `N` is a right `A`-module, in both cases by precomposition. It is a type
  synonym, since the module of linear maps already carries the action on the codomain.
* `TauCeti.MatlisDual.map` and `TauCeti.MatlisDual.mapOp`: the contravariant action on morphisms of
  left and of right modules, with the isomorphisms `TauCeti.MatlisDual.congr` and
  `TauCeti.MatlisDual.congrOp`.
* `TauCeti.IsInjectiveEnvelope.matlisDualEvalEquiv` and
  `TauCeti.IsInjectiveEnvelope.matlisDualEvalEquivOp`: biduality for modules of finite length, as an
  isomorphism of left and of right `A`-modules.

## Implementation notes

The actions of `A` and `Aᵐᵒᵖ` on `MatlisDual R E N` are instances of low priority, so that instance
search prefers the `R`-module structure on the values whenever `A` is `R` itself. The action of `R`
through `A` is equal to it by the `IsScalarTower` instances, not definitionally.

The suffix `Op` on a construction marks a right-module source: `MatlisDual.map` dualizes morphisms
of left modules, `MatlisDual.mapOp` those of right modules, and `matlisDualEvalEquivOp` is biduality
for right modules.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Section II.3.
-/

public section

noncomputable section

namespace TauCeti

open MulOpposite

universe u v w t

section Defs

variable (R : Type u) [CommRing R] (E : Type v) [AddCommGroup E] [Module R E]
  (N : Type w) [AddCommGroup N] [Module R N]

/-- The **Matlis dual** `D_R N = Hom_R(N, E)` of an `R`-module `N`, with values in `E`. A left
`A`-module `N` has a right `A`-module as dual, and a right `A`-module has a left `A`-module as dual.
The synonym keeps these actions apart from the action on the codomain of a linear map. -/
-- The module compiler needs the synonym exposed to compile its inherited operations.
@[expose] def MatlisDual : Type _ := N →ₗ[R] E

namespace MatlisDual

instance : AddCommGroup (MatlisDual R E N) := inferInstanceAs (AddCommGroup (N →ₗ[R] E))

instance : Module R (MatlisDual R E N) := inferInstanceAs (Module R (N →ₗ[R] E))

/-- The underlying `R`-module of `D_R N` is the module of linear maps `N → E`. -/
def equivLinearMap : MatlisDual R E N ≃ₗ[R] (N →ₗ[R] E) := LinearEquiv.refl R _

variable {R E N}

@[ext]
theorem ext {φ ψ : MatlisDual R E N}
    (h : ∀ x, equivLinearMap R E N φ x = equivLinearMap R E N ψ x) : φ = ψ :=
  (equivLinearMap R E N).injective (LinearMap.ext h)

end MatlisDual

end Defs

namespace MatlisDual

variable {R : Type u} [CommRing R] {E : Type v} [AddCommGroup E] [Module R E]
  {A : Type t} [Ring A] [Algebra R A]

section Left

variable {N : Type w} [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]

/-- The dual of a left `A`-module is a right `A`-module: `(φ · a) x = φ (a • x)`. -/
instance (priority := low) : Module Aᵐᵒᵖ (MatlisDual R E N) :=
  Module.compHom (N →ₗ[R] E) (linearMapOpAction R N E)

/-- The right action on the dual of a left module is precomposition with the left action. -/
@[simp]
theorem smul_op_apply (a : Aᵐᵒᵖ) (φ : MatlisDual R E N) (x : N) :
    equivLinearMap R E N (a • φ) x = equivLinearMap R E N φ (a.unop • x) :=
  linearMapOpAction_apply_apply R N E a (equivLinearMap R E N φ) x

instance : IsScalarTower R Aᵐᵒᵖ (MatlisDual R E N) :=
  IsScalarTower.of_algebraMap_smul fun r φ => by
    ext x
    simp [MulOpposite.algebraMap_apply]

variable {N' : Type*} [AddCommGroup N'] [Module R N'] [Module A N'] [IsScalarTower R A N']

/-- A morphism of left modules dualizes to a morphism of right modules, by precomposition. -/
def map (g : N →ₗ[A] N') : MatlisDual R E N' →ₗ[Aᵐᵒᵖ] MatlisDual R E N where
  toFun φ := (equivLinearMap R E N).symm ((equivLinearMap R E N' φ) ∘ₗ g.restrictScalars R)
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

@[simp]
theorem map_apply (g : N →ₗ[A] N') (φ : MatlisDual R E N') (x : N) :
    equivLinearMap R E N (map g φ) x = equivLinearMap R E N' φ (g x) :=
  (rfl)

@[simp]
theorem map_id : map (R := R) (E := E) (LinearMap.id : N →ₗ[A] N) = LinearMap.id := by
  ext
  simp

@[simp]
theorem map_comp {N'' : Type*} [AddCommGroup N''] [Module R N''] [Module A N'']
    [IsScalarTower R A N''] (g : N' →ₗ[A] N'') (h : N →ₗ[A] N') :
    map (R := R) (E := E) (g ∘ₗ h) = map h ∘ₗ map g := by
  ext
  simp

/-- An isomorphism of left modules dualizes to an isomorphism of right modules. The two modules may
carry any `R`-module structures compatible with the `A`-action. -/
def congr (e : N ≃ₗ[A] N') : MatlisDual R E N' ≃ₗ[Aᵐᵒᵖ] MatlisDual R E N :=
  LinearEquiv.ofLinearMap (map e.toLinearMap) (map e.symm.toLinearMap)
    (by ext; simp) (by ext; simp)

@[simp]
theorem congr_apply (e : N ≃ₗ[A] N') (φ : MatlisDual R E N') (x : N) :
    equivLinearMap R E N (congr e φ) x = equivLinearMap R E N' φ (e x) :=
  (rfl)

@[simp]
theorem congr_symm (e : N ≃ₗ[A] N') :
    (congr (R := R) (E := E) e).symm = congr e.symm :=
  (rfl)

@[simp]
theorem congr_refl :
    congr (R := R) (E := E) (LinearEquiv.refl A N) = LinearEquiv.refl Aᵐᵒᵖ _ := by
  ext
  simp

@[simp]
theorem congr_trans {N'' : Type*} [AddCommGroup N''] [Module R N''] [Module A N'']
    [IsScalarTower R A N''] (e : N ≃ₗ[A] N') (e' : N' ≃ₗ[A] N'') :
    congr (R := R) (E := E) (e.trans e') = (congr e').trans (congr e) := by
  ext
  simp

end Left

section Right

variable {N : Type w} [AddCommGroup N] [Module R N] [Module Aᵐᵒᵖ N] [IsScalarTower R Aᵐᵒᵖ N]

/-- The dual of a right `A`-module is a left `A`-module: `(a • φ) x = φ (x · a)`. -/
instance (priority := low) : Module A (MatlisDual R E N) :=
  Module.compHom (N →ₗ[R] E) (linearMapRightAction R N E)

/-- The left action on the dual of a right module is precomposition with the right action. -/
@[simp]
theorem smul_apply (a : A) (φ : MatlisDual R E N) (x : N) :
    equivLinearMap R E N (a • φ) x = equivLinearMap R E N φ (op a • x) :=
  linearMapRightAction_apply_apply R N E a (equivLinearMap R E N φ) x

instance : IsScalarTower R A (MatlisDual R E N) :=
  IsScalarTower.of_algebraMap_smul fun r φ => by
    ext x
    simp [← MulOpposite.algebraMap_apply]

variable {N' : Type*} [AddCommGroup N'] [Module R N'] [Module Aᵐᵒᵖ N'] [IsScalarTower R Aᵐᵒᵖ N']

/-- A morphism of right modules dualizes to a morphism of left modules, by precomposition. -/
def mapOp (g : N →ₗ[Aᵐᵒᵖ] N') : MatlisDual R E N' →ₗ[A] MatlisDual R E N where
  toFun φ := (equivLinearMap R E N).symm ((equivLinearMap R E N' φ) ∘ₗ g.restrictScalars R)
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

@[simp]
theorem mapOp_apply (g : N →ₗ[Aᵐᵒᵖ] N') (φ : MatlisDual R E N') (x : N) :
    equivLinearMap R E N (mapOp g φ) x = equivLinearMap R E N' φ (g x) :=
  (rfl)

@[simp]
theorem mapOp_id :
    mapOp (R := R) (A := A) (E := E) (LinearMap.id : N →ₗ[Aᵐᵒᵖ] N) = LinearMap.id := by
  ext
  simp

@[simp]
theorem mapOp_comp {N'' : Type*} [AddCommGroup N''] [Module R N''] [Module Aᵐᵒᵖ N'']
    [IsScalarTower R Aᵐᵒᵖ N''] (g : N' →ₗ[Aᵐᵒᵖ] N'') (h : N →ₗ[Aᵐᵒᵖ] N') :
    mapOp (R := R) (A := A) (E := E) (g ∘ₗ h) = mapOp h ∘ₗ mapOp g := by
  ext
  simp

/-- An isomorphism of right modules dualizes to an isomorphism of left modules. The two modules may
carry any `R`-module structures compatible with the `A`-action. -/
def congrOp (e : N ≃ₗ[Aᵐᵒᵖ] N') : MatlisDual R E N' ≃ₗ[A] MatlisDual R E N :=
  LinearEquiv.ofLinearMap (mapOp e.toLinearMap) (mapOp e.symm.toLinearMap)
    (by ext; simp) (by ext; simp)

@[simp]
theorem congrOp_apply (e : N ≃ₗ[Aᵐᵒᵖ] N') (φ : MatlisDual R E N') (x : N) :
    equivLinearMap R E N (congrOp (A := A) e φ) x = equivLinearMap R E N' φ (e x) :=
  (rfl)

@[simp]
theorem congrOp_symm (e : N ≃ₗ[Aᵐᵒᵖ] N') :
    (congrOp (R := R) (A := A) (E := E) e).symm = congrOp e.symm :=
  (rfl)

@[simp]
theorem congrOp_refl :
    congrOp (R := R) (A := A) (E := E) (LinearEquiv.refl Aᵐᵒᵖ N) = LinearEquiv.refl A _ := by
  ext
  simp

@[simp]
theorem congrOp_trans {N'' : Type*} [AddCommGroup N''] [Module R N''] [Module Aᵐᵒᵖ N'']
    [IsScalarTower R Aᵐᵒᵖ N''] (e : N ≃ₗ[Aᵐᵒᵖ] N') (e' : N' ≃ₗ[Aᵐᵒᵖ] N'') :
    congrOp (R := R) (A := A) (E := E) (e.trans e') = (congrOp e').trans (congrOp e) := by
  ext
  simp

end Right

end MatlisDual

open MatlisDual

section Instances

attribute [local instance] opOpModule isScalarTower_opOpModule RingHomInvPair.of_ringEquiv

variable {R : Type u} [CommRing R] {E : Type v} [AddCommGroup E] [Module R E] [Small.{v} R]
  [Module.Injective R E] {A : Type t} [Ring A] [Algebra R A]
  {N : Type w} [AddCommGroup N] [Module R N]

/-- The dual of a projective right module is an injective left module. -/
instance [Module Aᵐᵒᵖ N] [IsScalarTower R Aᵐᵒᵖ N] [Module.Projective Aᵐᵒᵖ N] :
    Module.Injective A (MatlisDual R E N) :=
  (equivLinearMap R E N).moduleInjective_of_dual_projective smul_apply

/-- The dual of a projective left module is an injective right module. -/
instance [Module A N] [IsScalarTower R A N] [Module.Projective A N] :
    Module.Injective Aᵐᵒᵖ (MatlisDual R E N) :=
  have : Module.Projective Aᵐᵒᵖᵐᵒᵖ N := Module.Projective.of_equiv (opOpSemilinearEquiv (A := A))
  (equivLinearMap R E N).moduleInjective_of_dual_projective (A := Aᵐᵒᵖ)
    fun a φ x => smul_op_apply a φ x

/-- `D_R A`, the dual of the right regular module with action `(a • φ) x = φ (x * a)`, is an
injective left `A`-module. -/
instance : Module.Injective A (MatlisDual R E A) :=
  (equivLinearMap R E A).moduleInjective_of_dual_regular fun a φ x =>
    (smul_apply a φ x).trans (by rw [op_smul_eq_mul])

end Instances

section Biduality

variable {R : Type u} [CommRing R] {E : Type v} [AddCommGroup E] [Module R E]

/-- Evaluation `N → D_R (D_R N)`, as a map of `R`-modules. -/
def MatlisDual.evalₗ (R : Type u) [CommRing R] (E : Type v) [AddCommGroup E] [Module R E]
    (N : Type w) [AddCommGroup N] [Module R N] :
    N →ₗ[R] MatlisDual R E (MatlisDual R E N) :=
  (equivLinearMap R E _).symm.toLinearMap ∘ₗ (equivLinearMap R E N).toLinearMap.lcomp R E ∘ₗ
    LinearMap.applyₗ

@[simp]
theorem MatlisDual.evalₗ_apply (N : Type w) [AddCommGroup N] [Module R N] (x : N)
    (φ : MatlisDual R E N) :
    equivLinearMap R E _ (evalₗ R E N x) φ = equivLinearMap R E N φ x :=
  (rfl)

variable [IsSemisimpleRing (R ⧸ Ring.jacobson R)] [Small.{v} R] {f : R ⧸ Ring.jacobson R →ₗ[R] E}
  {A : Type t} [Ring A] [Algebra R A] {N : Type w} [AddCommGroup N] [Module R N]

/-- **Matlis biduality.** Evaluation `N → D_R (D_R N)` is bijective for every `R`-module `N` of
finite length. -/
theorem IsInjectiveEnvelope.bijective_evalₗ (hf : IsInjectiveEnvelope f)
    (hN : IsFiniteLength R N) : Function.Bijective (evalₗ R E N) :=
  (equivLinearMap R E _).symm.bijective.comp
    (((equivLinearMap R E N).arrowCongr (LinearEquiv.refl R E)).bijective.comp
      (hf.bijective_applyₗ_quotient_jacobson hN))

/-- **Matlis biduality for left modules.** Evaluation `N → D_R (D_R N)` is an isomorphism of left
`A`-modules for every left `A`-module `N` of finite length over `R`. -/
def IsInjectiveEnvelope.matlisDualEvalEquiv [Module A N] [IsScalarTower R A N]
    (hf : IsInjectiveEnvelope f) (hN : IsFiniteLength R N) :
    N ≃ₗ[A] MatlisDual R E (MatlisDual R E N) :=
  LinearEquiv.ofBijective
    { evalₗ R E N with
      map_smul' := fun a x => by
        ext φ
        simp } (hf.bijective_evalₗ hN)

@[simp]
theorem IsInjectiveEnvelope.matlisDualEvalEquiv_apply [Module A N] [IsScalarTower R A N]
    (hf : IsInjectiveEnvelope f) (hN : IsFiniteLength R N) (x : N) (φ : MatlisDual R E N) :
    equivLinearMap R E _ (hf.matlisDualEvalEquiv (A := A) hN x) φ = equivLinearMap R E N φ x :=
  (rfl)

/-- **Matlis biduality for right modules.** Evaluation `N → D_R (D_R N)` is an isomorphism of right
`A`-modules for every right `A`-module `N` of finite length over `R`. -/
def IsInjectiveEnvelope.matlisDualEvalEquivOp [Module Aᵐᵒᵖ N] [IsScalarTower R Aᵐᵒᵖ N]
    (hf : IsInjectiveEnvelope f) (hN : IsFiniteLength R N) :
    N ≃ₗ[Aᵐᵒᵖ] MatlisDual R E (MatlisDual R E N) :=
  LinearEquiv.ofBijective
    { evalₗ R E N with
      map_smul' := fun a x => by
        ext φ
        simp } (hf.bijective_evalₗ hN)

@[simp]
theorem IsInjectiveEnvelope.matlisDualEvalEquivOp_apply [Module Aᵐᵒᵖ N] [IsScalarTower R Aᵐᵒᵖ N]
    (hf : IsInjectiveEnvelope f) (hN : IsFiniteLength R N) (x : N) (φ : MatlisDual R E N) :
    equivLinearMap R E _ (hf.matlisDualEvalEquivOp (A := A) hN x) φ = equivLinearMap R E N φ x :=
  (rfl)

end Biduality

end TauCeti
