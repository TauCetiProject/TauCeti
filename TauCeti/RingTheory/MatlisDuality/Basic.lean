/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Algebra.Module.Dual.ProjectiveInjective
import TauCeti.Algebra.Module.Opposite
public import TauCeti.LinearAlgebra.Dual.RightAction
public import TauCeti.Algebra.Module.Injective.Cogenerator

/-!
# The Matlis dual of a module over an algebra

Let `R` be a commutative ring, `E` an `R`-module and `A` an `R`-algebra. The Matlis dual
`D_R N = Hom_R(N, E)` exchanges left and right `A`-modules. This file defines it with its
contravariant action on morphisms, shows that for injective `E` it sends projective modules to
injective modules, and proves that evaluation `N → D_R (D_R N)` is an isomorphism of `A`-modules for
`N` of finite length over `R`, when `E` is injective and `Hom_R(R ⧸ 𝔪, E)` has length one for every
maximal ideal `𝔪`. Hence dualizing is fully faithful on modules of finite length over `R`. The
hypothesis on `E` holds for an injective hull of `R ⧸ J(R)` when `R ⧸ J(R)` is semisimple
(`TauCeti.IsInjectiveEnvelope.length_quotient_linearMap_eq_one`), for instance for `E = R` over a
field, and also for `ℚ ⧸ ℤ` over `ℤ`.

Right `A`-modules are modules over `Aᵐᵒᵖ`.

## Main definitions

* `TauCeti.MatlisDual R E N`: the module `Hom_R(N, E)`, a right module when `N` is a left `A`-module
  and a left module when `N` is a right `A`-module, in both cases by precomposition. It is a type
  synonym, since the module of linear maps already carries the action on the codomain.
* `TauCeti.MatlisDual.map` and `TauCeti.MatlisDual.mapOp`: the contravariant action on morphisms of
  left and of right modules, with the isomorphisms `TauCeti.MatlisDual.congr` and
  `TauCeti.MatlisDual.congrOp`.
* `TauCeti.MatlisDual.dualSelfEquiv`: the isomorphism `D_R (Hom_A(A, A)) ≅ D_R A` of left
  `A`-modules.
* `TauCeti.MatlisDual.evalEquiv` and `TauCeti.MatlisDual.evalEquivOp`: biduality for modules of
  finite length over `R`, as an isomorphism of left and of right `A`-modules.

## Main results

* `TauCeti.subsingleton_matlisDual_iff`: `D_R N` is zero exactly when `N` is, for every `N`.
* `TauCeti.MatlisDual.bijective_map` and `TauCeti.MatlisDual.bijective_mapOp`: for modules of
  finite length over `R`, dualizing is a bijection on morphisms.
* `TauCeti.MatlisDual.exists_retract_of_retract`: a retract of `D_R N` dualizes to a retract of
  `N`, for `N` of finite length over `R`.

## Implementation notes

The actions of `A` and `Aᵐᵒᵖ` on `MatlisDual R E N` are instances of low priority, so that instance
search prefers the `R`-module structure on the values whenever `A` is `R` itself. The action of `R`
through `A` is equal to it by the `IsScalarTower` instances, not definitionally.

The suffix `Op` on a construction marks a right-module source: `MatlisDual.map` dualizes morphisms
of left modules, `MatlisDual.mapOp` those of right modules, and `MatlisDual.evalEquivOp` is
biduality for right modules.

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

section Regular

/-- **The dual of the endomorphisms of the regular module**: `D_R (Hom_A(A, A))` is isomorphic to
`D_R A`, the dual of the right regular module. A functional `θ` on `Hom_A(A, A)` goes to
`a ↦ θ (x ↦ x * a)`. This is the value `ν A` of the Nakayama functor on the regular module. -/
def dualSelfEquiv : MatlisDual R E (Module.Dual A A) ≃ₗ[A] MatlisDual R E A :=
  congrOp (LinearMap.ringLmapEquivSelf A Aᵐᵒᵖ A).symm

@[simp]
theorem dualSelfEquiv_apply (θ : MatlisDual R E (Module.Dual A A)) (a : A) :
    equivLinearMap R E A (dualSelfEquiv θ) a =
      equivLinearMap R E _ θ (LinearMap.toSpanSingleton A A a) := by
  simp only [dualSelfEquiv, congrOp_apply, LinearMap.ringLmapEquivSelf_symm_apply,
    Module.End.one_eq_id, LinearMap.smulRight_id]

@[simp]
theorem dualSelfEquiv_symm_apply (φ : MatlisDual R E A) (ψ : Module.Dual A A) :
    equivLinearMap R E _ (dualSelfEquiv.symm φ) ψ = equivLinearMap R E A φ (ψ 1) := by
  simp [dualSelfEquiv]

end Regular

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

variable [Module.Injective R E] [Small.{v} R] {A : Type t} [Ring A] [Algebra R A]
  {N : Type w} [AddCommGroup N] [Module R N]

/-- **Matlis duality is faithful on objects.** If `E` is injective and receives a nonzero map from
every `R ⧸ 𝔪`, in particular if each `Hom_R(R ⧸ 𝔪, E)` has length one, then `E` is a cogenerator:
evaluation `N → D_R (D_R N)` is injective for every `R`-module `N`. -/
theorem MatlisDual.injective_evalₗ
    (hE : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Module.length R (R ⧸ 𝔪 →ₗ[R] E) = 1) :
    Function.Injective (evalₗ R E N) :=
  (equivLinearMap R E _).symm.injective.comp
    (((equivLinearMap R E N).arrowCongr (LinearEquiv.refl R E)).injective.comp
      (injective_applyₗ_of_forall_isMaximal fun 𝔪 h𝔪 ↦
        Module.length_pos_iff.mp (by rw [hE 𝔪 h𝔪]; exact zero_lt_one)))

/-- **Matlis duality detects zero modules**: `D_R N` is zero exactly when `N` is, for every
`R`-module `N`, of finite length or not. -/
theorem subsingleton_matlisDual_iff
    (hE : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Module.length R (R ⧸ 𝔪 →ₗ[R] E) = 1) :
    Subsingleton (MatlisDual R E N) ↔ Subsingleton N := by
  refine ⟨fun _ ↦ ?_, fun _ ↦ (equivLinearMap R E N).toEquiv.subsingleton⟩
  have : Subsingleton (MatlisDual R E (MatlisDual R E N)) :=
    (equivLinearMap R E (MatlisDual R E N)).toEquiv.subsingleton
  exact (MatlisDual.injective_evalₗ hE).subsingleton

/-- **Matlis biduality.** If `E` is injective and each `Hom_R(R ⧸ 𝔪, E)` has length one, then
evaluation `N → D_R (D_R N)` is bijective for every `R`-module `N` of finite length. -/
theorem MatlisDual.bijective_evalₗ
    (hE : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Module.length R (R ⧸ 𝔪 →ₗ[R] E) = 1)
    (hN : IsFiniteLength R N) : Function.Bijective (evalₗ R E N) :=
  (equivLinearMap R E _).symm.bijective.comp
    (((equivLinearMap R E N).arrowCongr (LinearEquiv.refl R E)).bijective.comp
      (bijective_applyₗ_of_forall_isMaximal hE hN))

/-- **Matlis biduality for left modules.** Evaluation `N → D_R (D_R N)` is an isomorphism of left
`A`-modules for every left `A`-module `N` of finite length over `R`. -/
def MatlisDual.evalEquiv [Module A N] [IsScalarTower R A N]
    (hE : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Module.length R (R ⧸ 𝔪 →ₗ[R] E) = 1)
    (hN : IsFiniteLength R N) : N ≃ₗ[A] MatlisDual R E (MatlisDual R E N) :=
  LinearEquiv.ofBijective
    { evalₗ R E N with
      map_smul' := fun a x => by
        ext φ
        simp } (bijective_evalₗ hE hN)

@[simp]
theorem MatlisDual.evalEquiv_apply [Module A N] [IsScalarTower R A N]
    (hE : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Module.length R (R ⧸ 𝔪 →ₗ[R] E) = 1)
    (hN : IsFiniteLength R N) (x : N) (φ : MatlisDual R E N) :
    equivLinearMap R E _ (evalEquiv (A := A) hE hN x) φ = equivLinearMap R E N φ x :=
  (rfl)

/-- **Matlis biduality for right modules.** Evaluation `N → D_R (D_R N)` is an isomorphism of right
`A`-modules for every right `A`-module `N` of finite length over `R`. -/
def MatlisDual.evalEquivOp [Module Aᵐᵒᵖ N] [IsScalarTower R Aᵐᵒᵖ N]
    (hE : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Module.length R (R ⧸ 𝔪 →ₗ[R] E) = 1)
    (hN : IsFiniteLength R N) : N ≃ₗ[Aᵐᵒᵖ] MatlisDual R E (MatlisDual R E N) :=
  LinearEquiv.ofBijective
    { evalₗ R E N with
      map_smul' := fun a x => by
        ext φ
        simp } (bijective_evalₗ hE hN)

@[simp]
theorem MatlisDual.evalEquivOp_apply [Module Aᵐᵒᵖ N] [IsScalarTower R Aᵐᵒᵖ N]
    (hE : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Module.length R (R ⧸ 𝔪 →ₗ[R] E) = 1)
    (hN : IsFiniteLength R N) (x : N) (φ : MatlisDual R E N) :
    equivLinearMap R E _ (evalEquivOp (A := A) hE hN x) φ = equivLinearMap R E N φ x :=
  (rfl)

/-- **Matlis duality is fully faithful on left modules.** Dualizing is a bijection from morphisms
of left `A`-modules of finite length over `R` to morphisms of their dual right modules. -/
theorem MatlisDual.bijective_map [Module A N] [IsScalarTower R A N]
    {N' : Type*} [AddCommGroup N'] [Module R N'] [Module A N'] [IsScalarTower R A N']
    (hE : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Module.length R (R ⧸ 𝔪 →ₗ[R] E) = 1)
    (hN : IsFiniteLength R N) (hN' : IsFiniteLength R N') :
    Function.Bijective (map (R := R) (A := A) (E := E) : (N →ₗ[A] N') → _) := by
  refine ⟨fun g h hgh => ?_, fun F => ⟨(evalEquiv hE hN').symm.toLinearMap ∘ₗ
    mapOp F ∘ₗ (evalEquiv hE hN).toLinearMap, ?_⟩⟩
  · ext x
    refine (bijective_evalₗ hE hN').1 (MatlisDual.ext fun φ => ?_)
    simpa using congr(equivLinearMap R E N ($hgh φ) x)
  · ext φ x
    rw [map_apply, ← evalEquiv_apply (A := A) hE hN', LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    simp

/-- **Matlis duality is fully faithful on right modules.** Dualizing is a bijection from morphisms
of right `A`-modules of finite length over `R` to morphisms of their dual left modules. -/
theorem MatlisDual.bijective_mapOp [Module Aᵐᵒᵖ N] [IsScalarTower R Aᵐᵒᵖ N]
    {N' : Type*} [AddCommGroup N'] [Module R N'] [Module Aᵐᵒᵖ N'] [IsScalarTower R Aᵐᵒᵖ N']
    (hE : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Module.length R (R ⧸ 𝔪 →ₗ[R] E) = 1)
    (hN : IsFiniteLength R N) (hN' : IsFiniteLength R N') :
    Function.Bijective (mapOp (R := R) (A := A) (E := E) : (N →ₗ[Aᵐᵒᵖ] N') → _) := by
  refine ⟨fun g h hgh => ?_, fun F => ⟨(evalEquivOp hE hN').symm.toLinearMap ∘ₗ
    map F ∘ₗ (evalEquivOp hE hN).toLinearMap, ?_⟩⟩
  · ext x
    refine (bijective_evalₗ hE hN').1 (MatlisDual.ext fun φ => ?_)
    simpa using congr(equivLinearMap R E N ($hgh φ) x)
  · ext φ x
    rw [mapOp_apply, ← evalEquivOp_apply (A := A) hE hN', LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    simp

/-- **A retract of a Matlis dual dualizes to a retract**: if a left `A`-module `I` is a retract of
`D_R N`, for a right `A`-module `N` of finite length over `R`, then `D_R I` is a retract of `N`,
through the duals of the two maps and biduality. -/
theorem MatlisDual.exists_retract_of_retract [Module Aᵐᵒᵖ N] [IsScalarTower R Aᵐᵒᵖ N]
    (hE : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Module.length R (R ⧸ 𝔪 →ₗ[R] E) = 1)
    (hN : IsFiniteLength R N) {I : Type*} [AddCommGroup I] [Module R I] [Module A I]
    [IsScalarTower R A I] (r : MatlisDual R E N →ₗ[A] I) (s : I →ₗ[A] MatlisDual R E N)
    (hrs : r ∘ₗ s = LinearMap.id) :
    ∃ (r' : N →ₗ[Aᵐᵒᵖ] MatlisDual R E I) (s' : MatlisDual R E I →ₗ[Aᵐᵒᵖ] N),
      r' ∘ₗ s' = LinearMap.id := by
  refine ⟨map s ∘ₗ (evalEquivOp hE hN).toLinearMap,
    (evalEquivOp hE hN).symm.toLinearMap ∘ₗ map r, LinearMap.ext fun φ ↦ ?_⟩
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  rw [← LinearMap.comp_apply (map s), ← map_comp, hrs, map_id, LinearMap.id_apply]

end Biduality

end TauCeti
