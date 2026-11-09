/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Dual.ProjectiveInjective
public import TauCeti.RingTheory.MatlisDuality.Semilocal

/-!
# Matlis duality for Artin algebras

Let `R` be a commutative Artinian ring with an injective hull `E` of `R ⧸ J(R)`, and let `A` be an
Artin `R`-algebra, an `R`-algebra that is finitely generated as an `R`-module. The Matlis dual
`D_R N = Hom_R(N, E)` exchanges left and right `A`-modules. This file proves that it preserves
finite generation, that evaluation `N → D_R (D_R N)` is an isomorphism of `A`-modules, that it
exchanges finitely generated projective and injective modules, and that `D_R A` is an injective
cogenerator, so that every finitely generated `A`-module has a finitely generated injective hull.

Right `A`-modules are modules over `Aᵐᵒᵖ`.

## Main definitions

* `TauCeti.MatlisDual R E N`: the module `Hom_R(N, E)`, a right module when `N` is a left `A`-module
  and a left module when `N` is a right `A`-module, in both cases by precomposition. It is a type
  synonym, since the module of linear maps already carries the action on the codomain.
* `TauCeti.MatlisDual.mapOp` and `TauCeti.MatlisDual.map`: the contravariant action on morphisms,
  with the isomorphisms `TauCeti.MatlisDual.congrOp` and `TauCeti.MatlisDual.congr`.
* `TauCeti.IsInjectiveEnvelope.matlisDualEvalEquiv` and
  `TauCeti.IsInjectiveEnvelope.matlisDualEvalEquivOp`: biduality for modules of finite length, as an
  isomorphism of left and of right `A`-modules.

## Main results

* `TauCeti.IsInjectiveEnvelope.moduleInjective_op_matlisDual_iff_projective` and
  `TauCeti.IsInjectiveEnvelope.moduleProjective_op_matlisDual_iff_injective`, with the right-module
  forms `moduleInjective_matlisDual_iff_projective_op` and
  `moduleProjective_matlisDual_iff_injective_op`: a finitely generated module is projective exactly
  when its dual is injective, and injective exactly when its dual is projective.
* `TauCeti.IsInjectiveEnvelope.exists_injective_linearMap_pi_matlisDual`: every finitely generated
  `A`-module embeds into a finite power of the injective module `D_R A`.
* `TauCeti.exists_isInjectiveEnvelope_of_isArtinianRing`: every finitely generated `A`-module has a
  finitely generated injective hull.

## Implementation notes

The actions of `A` and `Aᵐᵒᵖ` on `MatlisDual R E N` are instances of low priority, so that instance
search prefers the `R`-module structure on the values whenever `A` is `R` itself. The action of `R`
through `A` is equal to it by the `IsScalarTower` instances, not definitionally.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Sections II.3 and
  II.4.
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
def mapOp (g : N →ₗ[A] N') : MatlisDual R E N' →ₗ[Aᵐᵒᵖ] MatlisDual R E N where
  toFun φ := (equivLinearMap R E N).symm ((equivLinearMap R E N' φ) ∘ₗ g.restrictScalars R)
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

@[simp]
theorem mapOp_apply (g : N →ₗ[A] N') (φ : MatlisDual R E N') (x : N) :
    equivLinearMap R E N (mapOp g φ) x = equivLinearMap R E N' φ (g x) :=
  (rfl)

@[simp]
theorem mapOp_id : mapOp (R := R) (E := E) (LinearMap.id : N →ₗ[A] N) = LinearMap.id := by
  ext
  simp

@[simp]
theorem mapOp_comp {N'' : Type*} [AddCommGroup N''] [Module R N''] [Module A N'']
    [IsScalarTower R A N''] (g : N' →ₗ[A] N'') (h : N →ₗ[A] N') :
    mapOp (R := R) (E := E) (g ∘ₗ h) = mapOp h ∘ₗ mapOp g := by
  ext
  simp

/-- An isomorphism of left modules dualizes to an isomorphism of right modules. The two modules may
carry any `R`-module structures compatible with the `A`-action. -/
def congrOp (e : N ≃ₗ[A] N') : MatlisDual R E N' ≃ₗ[Aᵐᵒᵖ] MatlisDual R E N :=
  LinearEquiv.ofLinearMap (mapOp e.toLinearMap) (mapOp e.symm.toLinearMap)
    (by ext; simp) (by ext; simp)

@[simp]
theorem congrOp_apply (e : N ≃ₗ[A] N') (φ : MatlisDual R E N') (x : N) :
    equivLinearMap R E N (congrOp e φ) x = equivLinearMap R E N' φ (e x) :=
  (rfl)

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
def map (g : N →ₗ[Aᵐᵒᵖ] N') : MatlisDual R E N' →ₗ[A] MatlisDual R E N where
  toFun φ := (equivLinearMap R E N).symm ((equivLinearMap R E N' φ) ∘ₗ g.restrictScalars R)
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

@[simp]
theorem map_apply (g : N →ₗ[Aᵐᵒᵖ] N') (φ : MatlisDual R E N') (x : N) :
    equivLinearMap R E N (map g φ) x = equivLinearMap R E N' φ (g x) :=
  (rfl)

@[simp]
theorem map_id : map (R := R) (A := A) (E := E) (LinearMap.id : N →ₗ[Aᵐᵒᵖ] N) = LinearMap.id := by
  ext
  simp

@[simp]
theorem map_comp {N'' : Type*} [AddCommGroup N''] [Module R N''] [Module Aᵐᵒᵖ N'']
    [IsScalarTower R Aᵐᵒᵖ N''] (g : N' →ₗ[Aᵐᵒᵖ] N'') (h : N →ₗ[Aᵐᵒᵖ] N') :
    map (R := R) (A := A) (E := E) (g ∘ₗ h) = map h ∘ₗ map g := by
  ext
  simp

/-- An isomorphism of right modules dualizes to an isomorphism of left modules. The two modules may
carry any `R`-module structures compatible with the `A`-action. -/
def congr (e : N ≃ₗ[Aᵐᵒᵖ] N') : MatlisDual R E N' ≃ₗ[A] MatlisDual R E N :=
  LinearEquiv.ofLinearMap (map e.toLinearMap) (map e.symm.toLinearMap)
    (by ext; simp) (by ext; simp)

@[simp]
theorem congr_apply (e : N ≃ₗ[Aᵐᵒᵖ] N') (φ : MatlisDual R E N') (x : N) :
    equivLinearMap R E N (congr (A := A) e φ) x = equivLinearMap R E N' φ (e x) :=
  (rfl)

end Right

end MatlisDual

open MatlisDual

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

section OpOp

/-- A left `A`-module, seen as a module over the opposite of `Aᵐᵒᵖ`. -/
private abbrev opOpModule (A : Type t) [Ring A] (N : Type w) [AddCommGroup N] [Module A N] :
    Module Aᵐᵒᵖᵐᵒᵖ N :=
  Module.compHom N (RingEquiv.opOp A).symm.toRingHom

attribute [local instance] opOpModule RingHomInvPair.of_ringEquiv

private theorem isScalarTower_opOp {R : Type u} [CommRing R] {A : Type t} [Ring A] [Algebra R A]
    {N : Type w} [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N] :
    IsScalarTower R Aᵐᵒᵖᵐᵒᵖ N :=
  IsScalarTower.of_algebraMap_smul fun r x => algebraMap_smul A r x

/-- A left `A`-module is semilinearly identified with itself over the opposite of `Aᵐᵒᵖ`. -/
private def opOpSemilinearEquiv {A : Type t} [Ring A] {N : Type w} [AddCommGroup N] [Module A N] :
    N ≃ₛₗ[RingHomClass.toRingHom (RingEquiv.opOp A)] N :=
  { Equiv.refl N with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

end OpOp

attribute [local instance] opOpModule isScalarTower_opOp RingHomInvPair.of_ringEquiv

section Instances

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

section Artin

variable {R : Type u} [CommRing R] [IsArtinianRing R] {E : Type v} [AddCommGroup E] [Module R E]
  [Small.{v} R] {f : R ⧸ Ring.jacobson R →ₗ[R] E} {A : Type t} [Ring A] [Algebra R A]
  {N : Type w} [AddCommGroup N] [Module R N]

/-- The Matlis dual of a finitely generated module over a commutative Artinian ring is finitely
generated. -/
theorem IsInjectiveEnvelope.finite_matlisDual (hf : IsInjectiveEnvelope f) (N : Type w)
    [AddCommGroup N] [Module R N] [Module.Finite R N] : Module.Finite R (MatlisDual R E N) := by
  have hN := IsArtinianRing.isFiniteLength_of_finite R N
  refine ((IsArtinianRing.tfae R _).out 1 4).mpr ?_
  rw [← Module.length_ne_top_iff, (equivLinearMap R E N).length_eq,
    hf.length_linearMap_quotient_jacobson, Module.length_ne_top_iff]
  exact hN

section Finite

variable [Module.Finite R A]

/-- The Matlis dual of a finitely generated left `A`-module is a finitely generated right
`A`-module. -/
theorem IsInjectiveEnvelope.finite_op_matlisDual [Module A N] [IsScalarTower R A N]
    [Module.Finite A N] (hf : IsInjectiveEnvelope f) :
    Module.Finite Aᵐᵒᵖ (MatlisDual R E N) :=
  have : Module.Finite R N := Module.Finite.trans A N
  have := hf.finite_matlisDual N
  Module.Finite.of_restrictScalars_finite R Aᵐᵒᵖ _

/-- The Matlis dual of a finitely generated right `A`-module is a finitely generated left
`A`-module. -/
theorem IsInjectiveEnvelope.finite_matlisDual_of_finite_op [Module Aᵐᵒᵖ N]
    [IsScalarTower R Aᵐᵒᵖ N] [Module.Finite Aᵐᵒᵖ N] (hf : IsInjectiveEnvelope f) :
    Module.Finite A (MatlisDual R E N) :=
  have : Module.Finite R N := Module.Finite.trans Aᵐᵒᵖ N
  have := hf.finite_matlisDual N
  Module.Finite.of_restrictScalars_finite R A _

variable [Small.{w} A]

/-- The dual of a finitely generated injective right `A`-module is a projective left module. -/
theorem IsInjectiveEnvelope.moduleProjective_matlisDual_of_injective_op [Module Aᵐᵒᵖ N]
    [IsScalarTower R Aᵐᵒᵖ N] [Module.Finite Aᵐᵒᵖ N] [Module.Injective Aᵐᵒᵖ N]
    (hf : IsInjectiveEnvelope f) : Module.Projective A (MatlisDual R E N) :=
  have : Module.Finite R N := Module.Finite.trans Aᵐᵒᵖ N
  have := hf.finite_matlisDual_of_finite_op (A := A) (N := N)
  have : Small.{w} Aᵐᵒᵖ := small_of_injective MulOpposite.unop_injective
  (equivLinearMap R E N).moduleProjective_of_dual_injective_of_bijective smul_apply
    (hf.bijective_applyₗ_quotient_jacobson (IsArtinianRing.isFiniteLength_of_finite R A))
    (hf.bijective_applyₗ_quotient_jacobson (IsArtinianRing.isFiniteLength_of_finite R N)).1

/-- The dual of a finitely generated injective left `A`-module is a projective right module. -/
theorem IsInjectiveEnvelope.moduleProjective_op_matlisDual_of_injective [Module A N]
    [IsScalarTower R A N] [Module.Finite A N] [Module.Injective A N]
    (hf : IsInjectiveEnvelope f) : Module.Projective Aᵐᵒᵖ (MatlisDual R E N) :=
  have : Module.Finite R N := Module.Finite.trans A N
  have := hf.finite_op_matlisDual (A := A) (N := N)
  have : Small.{w} Aᵐᵒᵖᵐᵒᵖ := small_of_surjective (RingEquiv.opOp A).surjective
  have : Module.Injective Aᵐᵒᵖᵐᵒᵖ N :=
    Module.Injective.of_ringEquiv (RingEquiv.opOp A) (opOpSemilinearEquiv (A := A))
  (equivLinearMap R E N).moduleProjective_of_dual_injective_of_bijective (A := Aᵐᵒᵖ)
    (fun a φ x => smul_op_apply a φ x)
    (hf.bijective_applyₗ_quotient_jacobson (IsArtinianRing.isFiniteLength_of_finite R _))
    (hf.bijective_applyₗ_quotient_jacobson (IsArtinianRing.isFiniteLength_of_finite R N)).1

/-- A finitely generated left `A`-module is projective exactly when its Matlis dual is an injective
right module. -/
theorem IsInjectiveEnvelope.moduleInjective_op_matlisDual_iff_projective [Module A N]
    [IsScalarTower R A N] [Module.Finite A N] (hf : IsInjectiveEnvelope f) :
    Module.Injective Aᵐᵒᵖ (MatlisDual R E N) ↔ Module.Projective A N := by
  have := hf.moduleInjective
  refine ⟨fun _ => ?_, fun _ => inferInstance⟩
  have : Module.Finite R N := Module.Finite.trans A N
  have := hf.finite_op_matlisDual (A := A) (N := N)
  have : Small.{max w v} A := small_lift A
  have := hf.moduleProjective_matlisDual_of_injective_op (A := A) (N := MatlisDual R E N)
  exact .of_equiv' (hf.matlisDualEvalEquiv (IsArtinianRing.isFiniteLength_of_finite R N)).symm

/-- A finitely generated right `A`-module is projective exactly when its Matlis dual is an injective
left module. -/
theorem IsInjectiveEnvelope.moduleInjective_matlisDual_iff_projective_op [Module Aᵐᵒᵖ N]
    [IsScalarTower R Aᵐᵒᵖ N] [Module.Finite Aᵐᵒᵖ N] (hf : IsInjectiveEnvelope f) :
    Module.Injective A (MatlisDual R E N) ↔ Module.Projective Aᵐᵒᵖ N := by
  have := hf.moduleInjective
  refine ⟨fun _ => ?_, fun _ => inferInstance⟩
  have : Module.Finite R N := Module.Finite.trans Aᵐᵒᵖ N
  have := hf.finite_matlisDual_of_finite_op (A := A) (N := N)
  have : Small.{max w v} A := small_lift A
  have := hf.moduleProjective_op_matlisDual_of_injective (A := A) (N := MatlisDual R E N)
  exact .of_equiv'
    (hf.matlisDualEvalEquivOp (A := A) (IsArtinianRing.isFiniteLength_of_finite R N)).symm

/-- A finitely generated left `A`-module is injective exactly when its Matlis dual is a projective
right module. -/
theorem IsInjectiveEnvelope.moduleProjective_op_matlisDual_iff_injective [Module A N]
    [IsScalarTower R A N] [Module.Finite A N] (hf : IsInjectiveEnvelope f) :
    Module.Projective Aᵐᵒᵖ (MatlisDual R E N) ↔ Module.Injective A N := by
  have := hf.moduleInjective
  refine ⟨fun _ => ?_, fun _ => hf.moduleProjective_op_matlisDual_of_injective⟩
  have : Module.Finite R N := Module.Finite.trans A N
  have : Small.{max w v} A := small_lift A
  have : Module.Injective A (MatlisDual R E (MatlisDual R E N)) := inferInstance
  exact ((Module.Baer.of_injective this).of_equiv
    (hf.matlisDualEvalEquiv (IsArtinianRing.isFiniteLength_of_finite R N)).symm).injective

/-- A finitely generated right `A`-module is injective exactly when its Matlis dual is a projective
left module. -/
theorem IsInjectiveEnvelope.moduleProjective_matlisDual_iff_injective_op [Module Aᵐᵒᵖ N]
    [IsScalarTower R Aᵐᵒᵖ N] [Module.Finite Aᵐᵒᵖ N] (hf : IsInjectiveEnvelope f) :
    Module.Projective A (MatlisDual R E N) ↔ Module.Injective Aᵐᵒᵖ N := by
  have := hf.moduleInjective
  refine ⟨fun _ => ?_, fun _ => hf.moduleProjective_matlisDual_of_injective_op⟩
  have : Module.Finite R N := Module.Finite.trans Aᵐᵒᵖ N
  have : Small.{max w v} Aᵐᵒᵖ :=
    have : Small.{max w v} A := small_lift A
    small_of_injective MulOpposite.unop_injective
  have : Module.Injective Aᵐᵒᵖ (MatlisDual R E (MatlisDual R E N)) := inferInstance
  refine ((Module.Baer.of_injective this).of_equiv ?_).injective
  exact (hf.matlisDualEvalEquivOp (A := A) (IsArtinianRing.isFiniteLength_of_finite R N)).symm

omit [Small.{w} A] in
/-- **`D_R A` is a cogenerator.** Every finitely generated left module over an Artin algebra `A`
embeds into a finite power of `D_R A`. -/
theorem IsInjectiveEnvelope.exists_injective_linearMap_pi_matlisDual [Module A N]
    [IsScalarTower R A N] [Module.Finite A N] (hf : IsInjectiveEnvelope f) :
    ∃ (n : ℕ) (g : N →ₗ[A] (Fin n → MatlisDual R E A)), Function.Injective g := by
  have : Module.Finite R N := Module.Finite.trans A N
  have := hf.finite_op_matlisDual (A := A) (N := N)
  obtain ⟨n, b, hb⟩ := Module.Finite.exists_fin (R := Aᵐᵒᵖ) (M := MatlisDual R E N)
  -- The coordinate `i` of `g x` is the functional `a ↦ b i (a • x)`.
  let g₀ (x : N) (i : Fin n) : MatlisDual R E A :=
    (equivLinearMap R E A).symm ((equivLinearMap R E N (b i)).comp
      ((LinearMap.toSpanSingleton A N x).restrictScalars R))
  have hg₀ (x : N) (i : Fin n) (a : A) :
      equivLinearMap R E A (g₀ x i) a = equivLinearMap R E N (b i) (a • x) := by
    simp [g₀]
  let g : N →ₗ[A] (Fin n → MatlisDual R E A) :=
    { toFun := g₀
      map_add' := fun _ _ => by ext; simp [hg₀]
      map_smul' := fun _ _ => by ext; simp [hg₀, mul_smul] }
  refine ⟨n, g, (injective_iff_map_eq_zero g).mpr fun x hx => ?_⟩
  -- Every functional on `N` is a combination of the `b i`, each of which vanishes on `A • x`.
  have key (φ : MatlisDual R E N) (hφ : φ ∈ Submodule.span Aᵐᵒᵖ (Set.range b)) (a : A) :
      equivLinearMap R E N φ (a • x) = 0 := by
    induction hφ using Submodule.span_induction generalizing a with
    | mem _ h =>
      obtain ⟨i, rfl⟩ := h
      rw [← hg₀]
      exact congr(equivLinearMap R E A ($hx i) a)
    | zero => simp
    | add _ _ _ _ h₁ h₂ => simp [h₁, h₂]
    | smul c _ _ h => simpa [mul_smul] using h (c.unop * a)
  refine (injective_iff_map_eq_zero _).mp
    (hf.bijective_evalₗ (IsArtinianRing.isFiniteLength_of_finite R N)).1 x
    (MatlisDual.ext fun φ => ?_)
  simpa using key φ (hb ▸ Submodule.mem_top) 1

end Finite

end Artin

/-- **Finitely generated injective hulls.** Every finitely generated left module over an Artin
algebra has an injective hull which is finitely generated. -/
theorem exists_isInjectiveEnvelope_of_isArtinianRing (R : Type u) [CommRing R] [IsArtinianRing R]
    {A : Type t} [Ring A] [Algebra R A] [Module.Finite R A] (N : Type w) [AddCommGroup N]
    [Module R N] [Module A N] [IsScalarTower R A N] [Module.Finite A N] :
    ∃ (Q : Type (max u t)) (_ : AddCommGroup Q) (_ : Module A Q) (_ : Module.Finite A Q)
      (i : N →ₗ[A] Q), IsInjectiveEnvelope i := by
  obtain ⟨E, _, _, f, hf, -⟩ := exists_isInjectiveEnvelope_quotient_jacobson R
  obtain ⟨n, g, hg⟩ := hf.exists_injective_linearMap_pi_matlisDual (A := A) (N := N)
  have := hf.moduleInjective
  have : Small.{max u t} A := small_max A
  have : Module.Injective A (Fin n → MatlisDual R E A) := Module.Injective.pi A _
  obtain ⟨P, _, hP⟩ := g.exists_isInjectiveEnvelope_submodule hg
  have := hf.finite_matlisDual A
  have : Module.Finite R P :=
    Module.Finite.of_injective (P.subtype.restrictScalars R) P.injective_subtype
  exact ⟨P, inferInstance, inferInstance, Module.Finite.of_restrictScalars_finite R A P, _, hP⟩

end TauCeti
