/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Tilde.Basic
import TauCeti.LinearAlgebra.TensorProduct.Quotient

/-!
# Affine base change of global sections

For a ring map `φ : R ⟶ S`, the canonical map
`S ⊗_R Γ(Spec R, M) ⟶ Γ(Spec S, (Spec φ)^* M)` is natural in the sheaf of modules `M`.
It is an isomorphism when `M` is quasicoherent, with no flatness or finiteness hypothesis.
The comparison sends `1 ⊗ m` to the pullback of the section `m`.

This is the affine section calculation underlying cohomology and base change. The map is
defined for arbitrary coefficient sheaves; quasicoherence is used only for its invertibility.
It also supplies the section-module comparison used to transport invariants of modules,
such as Fitting ideals, under scheme pullback.

For a surjective ring map `φ : R ⟶ S` with kernel `I`, i.e. a closed immersion
`Spec S ⟶ Spec R`, it follows that restricting global sections of a quasicoherent module `M` is
surjective with kernel `I Γ(M)` (`moduleSpecΓFunctor_map_unit_surjective`,
`ker_moduleSpecΓFunctor_map_unit`), as `S ⊗_R Γ(M) = Γ(M) ⧸ I Γ(M)`.

The construction uses `tildeFunctorCompPullbackIso`, the tilde/global-sections adjunction,
and the extension/restriction-of-scalars adjunction. The characteristic equation identifies
it with the map adjoint to pulling back global sections.

## References

* R. Hartshorne, *Algebraic Geometry*, Proposition II.5.2(e).
* The Stacks Project, [Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
  (pullback of quasicoherent sheaves on affine schemes).
-/

public section

open CategoryTheory Functor AlgebraicGeometry
open scoped ChangeOfRings
open TauCeti.AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

namespace CommRingCat.Hom

universe u

noncomputable section

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)

/-- The natural affine base-change map from scalar extension of global sections to global
sections of the pulled-back module sheaf. -/
def moduleSpecΓPullback :
    moduleSpecΓFunctor (R := R) ⋙ ModuleCat.extendScalars φ.hom ⟶
      pullback (Spec.map φ) ⋙ moduleSpecΓFunctor (R := S) :=
  whiskerLeft (moduleSpecΓFunctor (R := R))
    ((Functor.rightUnitor (ModuleCat.extendScalars φ.hom)).inv ≫
      whiskerLeft (ModuleCat.extendScalars φ.hom) (tilde.toTildeΓNatIso (R := S)).hom ≫
      (Functor.associator _ _ _).inv) ≫
    (Functor.associator _ _ _).inv ≫
    whiskerRight
      (whiskerLeft (moduleSpecΓFunctor (R := R)) (tildeFunctorCompPullbackIso φ).inv)
      (moduleSpecΓFunctor (R := S)) ≫
    whiskerRight
      ((Functor.associator _ _ _).inv ≫
        whiskerRight (tilde.adjunction (R := R)).counit (pullback (Spec.map φ)) ≫
        (Functor.leftUnitor (pullback (Spec.map φ))).hom)
      (moduleSpecΓFunctor (R := S))

/-- The affine comparison is obtained by sheafifying the extended section module and then
pulling back the tilde/global-sections counit. -/
lemma moduleSpecΓPullback_app (M : (Spec R).Modules) :
    (moduleSpecΓPullback φ).app M =
      (tilde.toTildeΓNatIso (R := S)).hom.app _ ≫
        (moduleSpecΓFunctor (R := S)).map
          ((tildeFunctorCompPullbackIso φ).inv.app (moduleSpecΓFunctor.obj M)) ≫
        (moduleSpecΓFunctor (R := S)).map
          ((pullback (Spec.map φ)).map ((tilde.adjunction (R := R)).counit.app M)) := by
  simp [moduleSpecΓPullback]

private lemma moduleSpecΓPullback_app_aux (M : (Spec R).Modules) :
    (tilde.adjunction (R := R)).unit.app (moduleSpecΓFunctor.obj M) ≫
        (moduleSpecΓFunctor (R := R)).map ((tilde.adjunction (R := R)).counit.app M) ≫
        (moduleSpecΓFunctor (R := R)).map
          ((pullbackPushforwardAdjunction (Spec.map φ)).unit.app M) ≫
        (pushforwardCompModuleSpecΓFunctorIso φ).hom.app _ =
      (ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app (moduleSpecΓFunctor.obj M) ≫
        (ModuleCat.restrictScalars φ.hom).map ((moduleSpecΓPullback φ).app M) := by
  let G := moduleSpecΓFunctor (R := S)
  let U := ModuleCat.restrictScalars φ.hom
  let P := pullback (Spec.map φ)
  let ε := (tilde.adjunction (R := R)).counit.app M
  have h := congrArg (fun a ↦ a ≫
      U.map (G.map ((tildeFunctorCompPullbackIso φ).inv.app (moduleSpecΓFunctor.obj M))) ≫
      U.map (G.map (P.map ε)))
    (unit_tildeFunctorCompPullbackIso_hom_app φ (moduleSpecΓFunctor.obj M))
  have hi := congrArg U.map (congrArg G.map
    ((tildeFunctorCompPullbackIso φ).hom_inv_id_app (moduleSpecΓFunctor.obj M)))
  have hn := (pushforwardCompModuleSpecΓFunctorIso φ).hom.naturality (P.map ε)
  have hu := (pullbackPushforwardAdjunction (Spec.map φ)).unit.naturality ε
  dsimp only [G, U, P, Functor.comp_map, Functor.id_map] at hi hn hu h
  simp only [Functor.map_comp] at hi
  simp only [Category.assoc] at h
  -- Default transparency identifies the module functor's section wrappers.
  erw [reassoc_of% hi, Category.id_comp, ← hn,
    ← Functor.map_comp_assoc, ← hu, Functor.map_comp] at h
  rw [moduleSpecΓPullback_app]
  simp only [Functor.map_comp]
  dsimp only [ε, Functor.id_obj, Functor.comp_obj] at h
  simp only [Category.assoc] at h
  exact h

/-- The affine comparison is adjoint to pulling back sections along `Spec φ`. -/
@[reassoc]
lemma unit_moduleSpecΓPullback_app (M : (Spec R).Modules) :
    (ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app (moduleSpecΓFunctor.obj M) ≫
        (ModuleCat.restrictScalars φ.hom).map ((moduleSpecΓPullback φ).app M) =
      (moduleSpecΓFunctor (R := R)).map
          ((pullbackPushforwardAdjunction (Spec.map φ)).unit.app M) ≫
        (pushforwardCompModuleSpecΓFunctorIso φ).hom.app _ := by
  have h := moduleSpecΓPullback_app_aux φ M
  rw [← Category.assoc _ _ ((moduleSpecΓFunctor (R := R)).map
      ((pullbackPushforwardAdjunction (Spec.map φ)).unit.app M) ≫
      (pushforwardCompModuleSpecΓFunctorIso φ).hom.app _),
    (tilde.adjunction (R := R)).right_triangle_components] at h
  erw [Category.id_comp] at h
  exact h.symm

/-- The affine base-change map sends `1 ⊗ m` to the pullback of the global section `m`. -/
@[simp]
lemma moduleSpecΓPullback_app_one_tmul (M : (Spec R).Modules)
    (m : moduleSpecΓFunctor.obj M) :
    dsimp% only [Functor.comp_obj]
      ((moduleSpecΓPullback φ).app M) ((1 : S) ⊗ₜ[R,φ.hom] m) =
      (moduleSpecΓFunctor (R := R)).map
        ((pullbackPushforwardAdjunction (Spec.map φ)).unit.app M) m := by
  -- The section comparison changes only the scalar action on the target group.
  erw [← ModuleCat.extendRestrictScalarsAdj_homEquiv_apply,
    Adjunction.homEquiv_unit, unit_moduleSpecΓPullback_app, ModuleCat.comp_apply]
  exact pushforwardCompModuleSpecΓFunctorIso_hom_app_apply φ _ _

/-- Affine base change of global sections is invertible for quasicoherent coefficients.
The ring map need not be flat. -/
lemma isIso_moduleSpecΓPullback_app (M : (Spec R).Modules) [M.IsQuasicoherent] :
    IsIso ((moduleSpecΓPullback φ).app M) := by
  rw [moduleSpecΓPullback_app]
  have : IsIso ((tilde.adjunction (R := R)).counit.app M) :=
    isIso_fromTildeΓ_of_isQuasicoherent M
  infer_instance

/-- Scalar extension of the global sections of a quasicoherent sheaf agrees with the global
sections of its pullback. The forward map is `moduleSpecΓPullback`. -/
def moduleSpecΓPullbackIso (M : (Spec R).Modules) [M.IsQuasicoherent] :
    (ModuleCat.extendScalars φ.hom).obj (moduleSpecΓFunctor.obj M) ≅
      moduleSpecΓFunctor.obj ((pullback (Spec.map φ)).obj M) :=
  letI := isIso_moduleSpecΓPullback_app φ M
  asIso ((moduleSpecΓPullback φ).app M)

/-- The forward affine section isomorphism is the canonical base-change map. -/
@[simp]
lemma moduleSpecΓPullbackIso_hom (M : (Spec R).Modules) [M.IsQuasicoherent] :
    (moduleSpecΓPullbackIso φ M).hom = (moduleSpecΓPullback φ).app M :=
  (rfl)

variable {φ}

/-- **Restriction of sections to a closed subscheme of an affine scheme is surjective.** For a
surjective ring map `φ : R ⟶ S`, every global section of the pullback of a quasicoherent module
`M` along the closed immersion `Spec S ⟶ Spec R` is the pullback of a global section of `M`. -/
lemma moduleSpecΓFunctor_map_unit_surjective (hφ : Function.Surjective φ.hom)
    (M : (Spec R).Modules) [M.IsQuasicoherent] :
    Function.Surjective
      (moduleSpecΓFunctor.map ((pullbackPushforwardAdjunction (Spec.map φ)).unit.app M)) := by
  let := φ.hom.toAlgebra
  have := isIso_moduleSpecΓPullback_app φ M
  intro y
  obtain ⟨z, hz⟩ := (ConcreteCategory.bijective_of_isIso ((moduleSpecΓPullback φ).app M)).2 y
  obtain ⟨m, rfl⟩ := TensorProduct.mk_surjective R (moduleSpecΓFunctor.obj M) S hφ z
  exact ⟨m, (moduleSpecΓPullback_app_one_tmul φ M m).symm.trans hz⟩

/-- **The kernel of restricting sections to a closed subscheme of an affine scheme.** For a
surjective ring map `φ : R ⟶ S` with kernel `I`, a global section of a quasicoherent module `M`
pulls back to zero along the closed immersion `Spec S ⟶ Spec R` exactly when it lies in
`I Γ(M)`. -/
lemma ker_moduleSpecΓFunctor_map_unit (hφ : Function.Surjective φ.hom)
    (M : (Spec R).Modules) [M.IsQuasicoherent] :
    LinearMap.ker
        (moduleSpecΓFunctor.map ((pullbackPushforwardAdjunction (Spec.map φ)).unit.app M)).hom =
      RingHom.ker φ.hom • ⊤ := by
  let := φ.hom.toAlgebra
  have := isIso_moduleSpecΓPullback_app φ M
  refine Eq.trans ?_ (TensorProduct.ker_mk_one_of_surjective (M := moduleSpecΓFunctor.obj M) hφ)
  ext m
  rw [LinearMap.mem_ker, LinearMap.mem_ker, ← moduleSpecΓPullback_app_one_tmul φ M m]
  exact (ConcreteCategory.bijective_of_isIso ((moduleSpecΓPullback φ).app M)).1.eq_iff' (map_zero _)

end

end CommRingCat.Hom
