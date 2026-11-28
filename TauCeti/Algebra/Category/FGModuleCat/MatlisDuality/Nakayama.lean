/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.FGModuleCat.Injective
public import TauCeti.RingTheory.MatlisDuality.Nakayama

import TauCeti.Algebra.Category.FGModuleCat.Projective

/-!
# The Nakayama equivalence for Artin algebras

For an Artin algebra `A` over a commutative Artinian ring `R`, fix an injective hull `E`
of `R ⧸ J(R)`. The Nakayama functor `ν = Hom_R(Hom_A(-, A), E)` is an `R`-linear
equivalence from the finitely generated projective left `A`-modules to the finitely
generated injective left `A`-modules. Its action on maps is precomposition through
both duals.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Theorem II.3.3 and Proposition II.4.3.
-/

public section

noncomputable section

open CategoryTheory
open scoped ModuleCat.Algebra

namespace TauCeti.IsInjectiveEnvelope

universe u v w

variable {R : Type u} [CommRing R] [IsArtinianRing R]
  {A : Type v} [Ring A] [Algebra R A] [Module.Finite R A]
  {E : Type w} [AddCommGroup E] [Module R E] [Small.{w} R]
  {i : R ⧸ Ring.jacobson R →ₗ[R] E} (hi : IsInjectiveEnvelope i)

/-- The Nakayama functor takes a finitely generated projective left module `P` to the
finitely generated injective left module `D_R (Hom_A(P, A))`. -/
def nakayamaFunctor :
    (isProjective (FGModuleCat.{max v w} A)).FullSubcategory ⥤
      (isInjective (FGModuleCat.{max v w} A)).FullSubcategory where
  obj P := by
    have : Projective P.obj := P.property
    letI := FGModuleCat.moduleProjective_of_projective P.obj
    letI := hi.moduleInjective
    letI := hi.finite_matlisDual_of_finite_op (A := A) (N := Module.Dual A P.obj)
    let M := FGModuleCat.of A (MatlisDual R E (Module.Dual A P.obj))
    exact ⟨M, FGModuleCat.injective_of_moduleInjective M⟩
  map {P Q} g := ObjectProperty.homMk (FGModuleCat.ofHom
    (MatlisDual.mapOp (R := R) (E := E) (g.hom.hom.hom.lcomp Aᵐᵒᵖ A)))
  map_id P := by
    apply ObjectProperty.hom_ext _
    apply FGModuleCat.hom_ext
    exact MatlisDual.mapOp_id
  map_comp g h := by
    apply ObjectProperty.hom_ext _
    apply FGModuleCat.hom_ext
    exact MatlisDual.mapOp_comp (R := R) (E := E)
      (g.hom.hom.hom.lcomp Aᵐᵒᵖ A) (h.hom.hom.hom.lcomp Aᵐᵒᵖ A)

/-- Identify the underlying module of a Nakayama image with the Matlis dual of the regular dual. -/
def nakayamaFunctorObjIso (P : (isProjective (FGModuleCat.{max v w} A)).FullSubcategory) :
    (hi.nakayamaFunctor.obj P).obj.obj ≅
      ModuleCat.of A (MatlisDual R E (Module.Dual A P.obj)) :=
  Iso.refl _

/-- Evaluate the image of a Nakayama morphism by precomposing a regular-dual functional. -/
@[simp]
theorem nakayamaFunctorObjIso_map_apply
    {P Q : (isProjective (FGModuleCat.{max v w} A)).FullSubcategory} (g : P ⟶ Q)
    (φ : (hi.nakayamaFunctor.obj P).obj.obj) (ψ : Module.Dual A Q.obj) :
    MatlisDual.equivLinearMap R E _
        ((hi.nakayamaFunctorObjIso Q).hom ((hi.nakayamaFunctor.map g).hom.hom φ)) ψ =
      MatlisDual.equivLinearMap R E _ ((hi.nakayamaFunctorObjIso P).hom φ)
        (ψ.comp g.hom.hom.hom) :=
  MatlisDual.mapOp_apply _ _ _

instance : (hi.nakayamaFunctor (A := A)).Additive where
  map_add {P Q} g h := by
    apply ObjectProperty.hom_ext _
    apply FGModuleCat.hom_ext
    -- Pass through the two full subcategories to compare the underlying linear maps.
    change MatlisDual.mapOp (R := R) (E := E) ((g.hom.hom.hom + h.hom.hom.hom).lcomp Aᵐᵒᵖ A) =
      MatlisDual.mapOp (g.hom.hom.hom.lcomp Aᵐᵒᵖ A) +
        MatlisDual.mapOp (h.hom.hom.hom.lcomp Aᵐᵒᵖ A)
    exact LinearMap.ext fun φ ↦ MatlisDual.ext fun ψ ↦ by
      simp [LinearMap.lcomp_apply', LinearMap.comp_add]

instance : (hi.nakayamaFunctor (A := A)).Linear R where
  map_smul {P Q} g r := by
    apply ObjectProperty.hom_ext _
    apply FGModuleCat.hom_ext
    -- The module category acts through the algebra map. On the Matlis dual this
    -- agrees with its given R-action by the scalar tower.
    suffices h : ∀ (φ : MatlisDual R E (Module.Dual A P.obj)) (ψ : Module.Dual A Q.obj),
        MatlisDual.equivLinearMap R E _
            (MatlisDual.mapOp ((r • g.hom.hom.hom).lcomp Aᵐᵒᵖ A) φ) ψ =
          MatlisDual.equivLinearMap R E _
            (algebraMap R A r • MatlisDual.mapOp (g.hom.hom.hom.lcomp Aᵐᵒᵖ A) φ) ψ by
      exact LinearMap.ext fun φ ↦ MatlisDual.ext fun ψ ↦ h φ ψ
    intro φ ψ
    rw [algebraMap_smul A]
    simp [LinearMap.lcomp_apply', LinearMap.comp_smul]

instance : (hi.nakayamaFunctor (A := A)).Faithful where
  map_injective {P Q} g h e := by
    have : Projective Q.obj := Q.property
    let : Module.Projective A Q.obj := FGModuleCat.moduleProjective_of_projective Q.obj
    apply (isProjective (FGModuleCat A)).ι.map_injective
    apply FGModuleCat.hom_ext
    apply (hi.bijective_mapOp_lcomp P.obj Q.obj).injective
    exact congrArg (fun k ↦ k.hom.hom.hom) e

instance : (hi.nakayamaFunctor (A := A)).Full where
  map_surjective {P Q} g := by
    have : Projective Q.obj := Q.property
    let : Module.Projective A Q.obj := FGModuleCat.moduleProjective_of_projective Q.obj
    obtain ⟨h, hh⟩ := (hi.bijective_mapOp_lcomp P.obj Q.obj).surjective g.hom.hom.hom
    refine ⟨ObjectProperty.homMk (FGModuleCat.ofHom h), ?_⟩
    apply (isInjective (FGModuleCat A)).ι.map_injective
    exact FGModuleCat.hom_ext hh

instance : (hi.nakayamaFunctor (A := A)).EssSurj where
  mem_essImage I := by
    have : IsArtinianRing A := IsArtinianRing.of_finite R A
    have : Injective I.obj := I.property
    let : Module.Injective A I.obj := FGModuleCat.moduleInjective_of_injective I.obj
    have := hi.finite_op_matlisDual (A := A) (N := I.obj)
    have := hi.moduleProjective_op_matlisDual_of_injective (A := A) (N := I.obj)
    let P := FGModuleCat.of A (MatlisDual R E I.obj →ₗ[Aᵐᵒᵖ] A)
    let X : (isProjective (FGModuleCat.{max v w} A)).FullSubcategory :=
      ⟨P, FGModuleCat.projective_of_moduleProjective A P⟩
    exact ⟨X, ⟨(isInjective (FGModuleCat A)).isoMk
      ((ModuleCat.isFG A).isoMk (hi.nakayamaEquiv (I := I.obj)).symm.toModuleIso)⟩⟩

instance : (hi.nakayamaFunctor (A := A)).IsEquivalence where

/-- The Nakayama equivalence from finitely generated projective to finitely generated injective
left modules over an Artin algebra. Its forward functor is `nakayamaFunctor`. -/
def nakayamaEquivalence :
    (isProjective (FGModuleCat.{max v w} A)).FullSubcategory ≌
      (isInjective (FGModuleCat.{max v w} A)).FullSubcategory :=
  hi.nakayamaFunctor.asEquivalence

@[simp]
theorem nakayamaEquivalence_functor :
    (hi.nakayamaEquivalence (A := A)).functor = hi.nakayamaFunctor := (rfl)

instance : (hi.nakayamaEquivalence (A := A)).functor.Linear R := by
  rw [nakayamaEquivalence_functor]
  infer_instance

end TauCeti.IsInjectiveEnvelope
