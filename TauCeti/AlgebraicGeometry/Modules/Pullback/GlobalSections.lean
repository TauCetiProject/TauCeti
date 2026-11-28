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

Through the extension/restriction-of-scalars adjunction, a morphism `φ^* N ⟶ N'` of modules on
`Spec S` gives an `R`-linear map of global sections `Γ(N) ⟶ Γ(N')`
(`moduleSpecΓPullbackAdjoint`); when `N` is quasicoherent, a square of such morphisms commutes
exactly when the induced square of global sections does
(`moduleSpecΓPullbackAdjoint_naturality_iff`), also after further restriction of scalars along a
ring map into `R` (`restrictScalars_moduleSpecΓPullbackAdjoint_naturality_iff`).

The construction uses `tildeFunctorCompPullbackIso`, the tilde/global-sections adjunction,
and the extension/restriction-of-scalars adjunction. The characteristic equation identifies
it with the map adjoint to pulling back global sections.

The file also records how pullback adjunction units act on global sections of `Spec` modules
under `pullbackCongr`, `pullbackComp`, `pullbackCompIsoOfCommSq`, and `pullbackCompIsoId`,
together with naturality and square-transition compatibility
(`AlgebraicGeometry.moduleSpecΓFunctor_map_unit_naturality`,
`AlgebraicGeometry.moduleSpecΓFunctor_map_square_transition`,
`AlgebraicGeometry.moduleSpecΓFunctor_map_inv_hom_cancel`).

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

/-- A morphism `e : φ^* N ⟶ N'` of modules on `Spec S`, read on global sections as an `R`-linear
map `Γ(N) ⟶ Γ(N')`: the map adjoint to the base change `S ⊗_R Γ(N) ⟶ Γ(φ^* N)` followed by
`Γ(e)`. It sends a section to its pullback followed by `e` (`moduleSpecΓPullbackAdjoint_apply`). -/
def moduleSpecΓPullbackAdjoint {N : (Spec R).Modules} {N' : (Spec S).Modules}
    (e : (pullback (Spec.map φ)).obj N ⟶ N') :
    moduleSpecΓFunctor.obj N ⟶ (ModuleCat.restrictScalars φ.hom).obj (moduleSpecΓFunctor.obj N') :=
  (ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv _ _
    ((moduleSpecΓPullback φ).app N ≫ moduleSpecΓFunctor.map e)

/-- `moduleSpecΓPullbackAdjoint φ e` pulls a section back along `Spec φ` and then applies `e`. -/
lemma moduleSpecΓPullbackAdjoint_apply {N : (Spec R).Modules} {N' : (Spec S).Modules}
    (e : (pullback (Spec.map φ)).obj N ⟶ N') (m : moduleSpecΓFunctor.obj N) :
    moduleSpecΓPullbackAdjoint φ e m =
      moduleSpecΓFunctor.map e
        (dsimp% only [Functor.comp_obj] (moduleSpecΓFunctor (R := R)).map
          ((pullbackPushforwardAdjunction (Spec.map φ)).unit.app N) m) := by
  -- The adjoint map evaluates the base change at `1 ⊗ m`, then applies `e`.
  exact congrArg (moduleSpecΓFunctor.map e).hom (moduleSpecΓPullback_app_one_tmul φ N m)

/-- A square of module maps over `Spec φ` commutes exactly when the square of global sections it
induces through `moduleSpecΓPullbackAdjoint` commutes. -/
lemma moduleSpecΓPullbackAdjoint_naturality_iff {N₁ N₂ : (Spec R).Modules}
    {N₁' N₂' : (Spec S).Modules} [N₁.IsQuasicoherent]
    (e₁ : (pullback (Spec.map φ)).obj N₁ ⟶ N₁') (e₂ : (pullback (Spec.map φ)).obj N₂ ⟶ N₂')
    (g : N₁ ⟶ N₂) (g' : N₁' ⟶ N₂') :
    moduleSpecΓPullbackAdjoint φ e₁ ≫
          (ModuleCat.restrictScalars φ.hom).map (moduleSpecΓFunctor.map g') =
        moduleSpecΓFunctor.map g ≫ moduleSpecΓPullbackAdjoint φ e₂ ↔
      (pullback (Spec.map φ)).map g ≫ e₂ = e₁ ≫ g' := by
  have := isIso_moduleSpecΓPullback_app φ N₁
  have hP := (moduleSpecΓPullback φ).naturality g
  dsimp only [Functor.comp_map] at hP
  calc
    _ ↔ (moduleSpecΓPullback φ).app N₁ ≫ moduleSpecΓFunctor.map (e₁ ≫ g') =
        (moduleSpecΓPullback φ).app N₁ ≫ moduleSpecΓFunctor.map ((pullback _).map g ≫ e₂) := by
      -- Both squares are adjoint to squares out of `S ⊗_R Γ(N₁)`.
      rw [moduleSpecΓPullbackAdjoint, moduleSpecΓPullbackAdjoint,
        ← Adjunction.homEquiv_naturality_right, ← Adjunction.homEquiv_naturality_left,
        Equiv.apply_eq_iff_eq, reassoc_of% hP]
      simp only [Category.assoc, Functor.map_comp]
    _ ↔ moduleSpecΓFunctor.map (e₁ ≫ g') =
        moduleSpecΓFunctor.map ((pullback (Spec.map φ)).map g ≫ e₂) := cancel_epi _
    _ ↔ _ := (moduleSpecΓFunctor_map_bijective _ _).1.eq_iff.trans eq_comm

/-- `moduleSpecΓPullbackAdjoint_naturality_iff` after further restriction of scalars along
`f : A →+* R` and `f' = φ ∘ f`: the restricted square of global sections still commutes exactly
when the square of module maps does. -/
lemma restrictScalars_moduleSpecΓPullbackAdjoint_naturality_iff {A : Type u} [CommRing A]
    (f : A →+* R) (f' : A →+* S) (hf : f' = φ.hom.comp f)
    {N₁ N₂ : (Spec R).Modules} {N₁' N₂' : (Spec S).Modules} [hN₁ : N₁.IsQuasicoherent]
    (e₁ : (pullback (Spec.map φ)).obj N₁ ⟶ N₁') (e₂ : (pullback (Spec.map φ)).obj N₂ ⟶ N₂')
    (g : N₁ ⟶ N₂) (g' : N₁' ⟶ N₂') :
    ((ModuleCat.restrictScalars f).map (moduleSpecΓPullbackAdjoint φ e₁) ≫
          (ModuleCat.restrictScalarsComp'App f φ.hom f' hf _).inv) ≫
          (ModuleCat.restrictScalars f').map (moduleSpecΓFunctor.map g') =
        (ModuleCat.restrictScalars f).map (moduleSpecΓFunctor.map g) ≫
          (ModuleCat.restrictScalars f).map (moduleSpecΓPullbackAdjoint φ e₂) ≫
          (ModuleCat.restrictScalarsComp'App f φ.hom f' hf _).inv ↔
      (pullback (Spec.map φ)).map g ≫ e₂ = e₁ ≫ g' := by
  rw [Category.assoc, ← ModuleCat.restrictScalarsComp'App_inv_naturality, ← Functor.map_comp_assoc,
    ← Functor.map_comp_assoc, cancel_mono, (ModuleCat.restrictScalars f).map_injective.eq_iff,
    moduleSpecΓPullbackAdjoint_naturality_iff]

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

namespace AlgebraicGeometry

open CategoryTheory Opposite

universe u

noncomputable section

/-- Compatibility of the pullback adjunction unit on global sections with equality of scheme
morphisms. -/
lemma moduleSpecΓFunctor_map_unit_pullbackCongr
    {R₀ S₀ : CommRingCat.{u}} {f g : Spec S₀ ⟶ Spec R₀} (h : f = g)
    (M : (Spec R₀).Modules) (m : moduleSpecΓFunctor.obj M) :
    moduleSpecΓFunctor.map ((Scheme.Modules.pullbackCongr h).hom.app M)
        (moduleSpecΓFunctor.map ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M)
          m) =
      moduleSpecΓFunctor.map ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M) m := by
  subst h
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    CategoryTheory.Functor.map_id]
  rfl

/-- On global sections, the inverse composition comparison `(f ≫ g)^* ⟶ f^* g^*` sends the
unit of `f ≫ g` to the composite of the units of `g` and `f`. -/
lemma moduleSpecΓFunctor_map_pullbackComp_inv_unit
    {R₀ S₀ T₀ : CommRingCat.{u}} (f : Spec T₀ ⟶ Spec S₀) (g : Spec S₀ ⟶ Spec R₀)
    (M : (Spec R₀).Modules) (m : moduleSpecΓFunctor.obj M) :
    moduleSpecΓFunctor.map ((Scheme.Modules.pullbackComp f g).inv.app M)
        (moduleSpecΓFunctor.map ((Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).unit.app M)
          m) =
      moduleSpecΓFunctor.map ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
        ((Scheme.Modules.pullback g).obj M))
        (moduleSpecΓFunctor.map ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M)
          m) := by
  have h := congrArg (fun k ↦ (moduleSpecΓFunctor (R := R₀)).map k m)
    (Scheme.Modules.unit_comp_pushforward_map_pullbackComp_inv_app f g M)
  simp only [CategoryTheory.Functor.map_comp, ModuleCat.comp_apply] at h
  exact h

/-- On global sections, the composition comparison `f^* g^* ⟶ (f ≫ g)^*` sends the composite
of the units of `g` and `f` to the unit of `f ≫ g`. -/
lemma moduleSpecΓFunctor_map_pullbackComp_hom_unit
    {R₀ S₀ T₀ : CommRingCat.{u}} (f : Spec T₀ ⟶ Spec S₀) (g : Spec S₀ ⟶ Spec R₀)
    (M : (Spec R₀).Modules) (m : moduleSpecΓFunctor.obj M) :
    moduleSpecΓFunctor.map ((Scheme.Modules.pullbackComp f g).hom.app M)
        (moduleSpecΓFunctor.map ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
          ((Scheme.Modules.pullback g).obj M))
          (moduleSpecΓFunctor.map ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M)
            m)) =
      moduleSpecΓFunctor.map ((Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).unit.app M)
        m := by
  let z : moduleSpecΓFunctor.obj ((Scheme.Modules.pullback (f ≫ g)).obj M) :=
    moduleSpecΓFunctor.map ((Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).unit.app M) m
  have h2 := congrArg (moduleSpecΓFunctor.map ((Scheme.Modules.pullbackComp f g).hom.app M))
    (moduleSpecΓFunctor_map_pullbackComp_inv_unit f g M m).symm
  refine h2.trans ?_
  calc moduleSpecΓFunctor.map ((Scheme.Modules.pullbackComp f g).hom.app M)
        (moduleSpecΓFunctor.map ((Scheme.Modules.pullbackComp f g).inv.app M) z)
      = moduleSpecΓFunctor.map ((Scheme.Modules.pullbackComp f g).inv.app M ≫
          (Scheme.Modules.pullbackComp f g).hom.app M) z :=
        (moduleSpecΓFunctor_map_comp_apply _ _ z).symm
    _ = z := by rw [Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, ModuleCat.id_apply]

/-- Around a commutative square of spectra, `pullbackCompIsoOfCommSq` intertwines the two
composite pullback units on global sections. -/
lemma moduleSpecΓFunctor_map_pullbackCompIsoOfCommSq_unit
    {R₀ R₁ S₀ S₁ : CommRingCat.{u}}
    {t : Spec S₀ ⟶ Spec S₁} {l : Spec S₀ ⟶ Spec R₀}
    {r : Spec S₁ ⟶ Spec R₁} {b : Spec R₀ ⟶ Spec R₁}
    (sq : CommSq t l r b) (M : (Spec R₁).Modules) (m : moduleSpecΓFunctor.obj M) :
    moduleSpecΓFunctor.map ((Scheme.Modules.pullbackCompIsoOfCommSq sq).hom.app M)
        (moduleSpecΓFunctor.map ((Scheme.Modules.pullbackPushforwardAdjunction t).unit.app
          ((Scheme.Modules.pullback r).obj M))
          (moduleSpecΓFunctor.map ((Scheme.Modules.pullbackPushforwardAdjunction r).unit.app M)
            m)) =
      moduleSpecΓFunctor.map ((Scheme.Modules.pullbackPushforwardAdjunction l).unit.app
        ((Scheme.Modules.pullback b).obj M))
        (moduleSpecΓFunctor.map ((Scheme.Modules.pullbackPushforwardAdjunction b).unit.app M)
          m) := by
  rw [Scheme.Modules.pullbackCompIsoOfCommSq_hom_app]
  refine (moduleSpecΓFunctor_map_comp_apply _ _ _).trans ?_
  refine (congrArg (moduleSpecΓFunctor.map ((Scheme.Modules.pullbackComp l b).inv.app M)) ?_).trans
    (moduleSpecΓFunctor_map_pullbackComp_inv_unit l b M m)
  refine (moduleSpecΓFunctor_map_comp_apply _ _ _).trans ?_
  refine (congrArg (moduleSpecΓFunctor.map ((Scheme.Modules.pullbackCongr sq.w).hom.app M))
    (moduleSpecΓFunctor_map_pullbackComp_hom_unit t r M m)).trans ?_
  exact moduleSpecΓFunctor_map_unit_pullbackCongr sq.w M m

/-- Around a commutative square of spectra, the inverse of `pullbackCompIsoOfCommSq` intertwines
the two composite pullback units on global sections. -/
lemma moduleSpecΓFunctor_map_pullbackCompIsoOfCommSq_inv_unit
    {R₀ R₁ S₀ S₁ : CommRingCat.{u}}
    {t : Spec S₀ ⟶ Spec S₁} {l : Spec S₀ ⟶ Spec R₀}
    {r : Spec S₁ ⟶ Spec R₁} {b : Spec R₀ ⟶ Spec R₁}
    (sq : CommSq t l r b) (M : (Spec R₁).Modules) (m : moduleSpecΓFunctor.obj M) :
    moduleSpecΓFunctor.map ((Scheme.Modules.pullbackCompIsoOfCommSq sq).inv.app M)
        (moduleSpecΓFunctor.map ((Scheme.Modules.pullbackPushforwardAdjunction l).unit.app
          ((Scheme.Modules.pullback b).obj M))
          (moduleSpecΓFunctor.map ((Scheme.Modules.pullbackPushforwardAdjunction b).unit.app M)
            m)) =
      moduleSpecΓFunctor.map ((Scheme.Modules.pullbackPushforwardAdjunction t).unit.app
        ((Scheme.Modules.pullback r).obj M))
        (moduleSpecΓFunctor.map ((Scheme.Modules.pullbackPushforwardAdjunction r).unit.app M)
          m) := by
  refine (congrArg (moduleSpecΓFunctor.map ((Scheme.Modules.pullbackCompIsoOfCommSq sq).inv.app M))
    (moduleSpecΓFunctor_map_pullbackCompIsoOfCommSq_unit sq M m).symm).trans ?_
  refine (moduleSpecΓFunctor_map_comp_apply _ _ _).symm.trans ?_
  rw [Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
  rfl

/-- For a section `f ≫ g = 𝟙` of spectra, `pullbackCompIsoId` cancels the composite pullback
units on global sections. -/
lemma moduleSpecΓFunctor_map_pullbackCompIsoId_unit
    {R₀ S₀ : CommRingCat.{u}} {f : Spec R₀ ⟶ Spec S₀} {g : Spec S₀ ⟶ Spec R₀}
    (h : f ≫ g = 𝟙 (Spec R₀)) (M : (Spec R₀).Modules) (m : moduleSpecΓFunctor.obj M) :
    moduleSpecΓFunctor.map ((Scheme.Modules.pullbackCompIsoId h).hom.app M)
        (moduleSpecΓFunctor.map ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
          ((Scheme.Modules.pullback g).obj M))
          (moduleSpecΓFunctor.map ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M)
            m)) =
      m := by
  have h1 := congrArg (fun k ↦ (k.app ⊤).hom m)
    (Scheme.Modules.unit_comp_pushforwardCongr_hom_app_pushforwardId_hom_app
      (rfl : 𝟙 (Spec R₀) = 𝟙 (Spec R₀)) M)
  simp only [Scheme.Modules.Hom.comp_app,
    Scheme.Modules.pushforwardId_hom_app_app, Scheme.Modules.pushforwardCongr_hom_app_app,
    Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    eqToHom_refl, op_id, CategoryTheory.Functor.map_id, Category.comp_id] at h1
  have hid : moduleSpecΓFunctor.map ((Scheme.Modules.pullbackId (Spec R₀)).hom.app M)
      (moduleSpecΓFunctor.map
        ((Scheme.Modules.pullbackPushforwardAdjunction (𝟙 (Spec R₀))).unit.app M) m) = m := by
    refine (congrArg (((Scheme.Modules.pullbackId (Spec R₀)).hom.app M).app ⊤) h1).trans ?_
    change (((Scheme.Modules.pullbackId (Spec R₀)).inv.app M ≫
      (Scheme.Modules.pullbackId (Spec R₀)).hom.app M).app ⊤).hom m = m
    rw [Iso.inv_hom_id_app]; rfl
  rw [Scheme.Modules.pullbackCompIsoId_hom_app]
  refine (moduleSpecΓFunctor_map_comp_apply _ _ _).trans ?_
  refine (congrArg (moduleSpecΓFunctor.map ((Scheme.Modules.pullbackId (Spec R₀)).hom.app M))
    ?_).trans hid
  refine (moduleSpecΓFunctor_map_comp_apply _ _ _).trans ?_
  refine (congrArg (moduleSpecΓFunctor.map ((Scheme.Modules.pullbackCongr h).hom.app M))
    (moduleSpecΓFunctor_map_pullbackComp_hom_unit f g M m)).trans ?_
  exact moduleSpecΓFunctor_map_unit_pullbackCongr h M m

/-- Naturality of the pullback adjunction unit on global sections of `Spec` modules. -/
lemma moduleSpecΓFunctor_map_unit_naturality
    {R₀ S₀ : CommRingCat.{u}} (f : Spec S₀ ⟶ Spec R₀) {M N : (Spec R₀).Modules}
    (u : M ⟶ N) (m : moduleSpecΓFunctor.obj M) :
    moduleSpecΓFunctor.map ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N)
        (moduleSpecΓFunctor.map u m) =
      moduleSpecΓFunctor.map ((Scheme.Modules.pullback f).map u)
        (moduleSpecΓFunctor.map ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M)
          m) := by
  let m' : Γ(M, ⊤) := m
  have h := congrArg (fun k ↦ (k.app ⊤).hom m')
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality u)
  simp only [CategoryTheory.Functor.id_map, CategoryTheory.Functor.comp_map,
    Scheme.Modules.Hom.comp_app, AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply] at h
  rw [Scheme.Modules.pushforward_map_app] at h
  change (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N).app ⊤).hom
      ((u.app ⊤).hom m') =
    (((Scheme.Modules.pullback f).map u).app (f ⁻¹ᵁ ⊤)).hom
      ((((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app ⊤).hom m')
  exact h

/-- Compatibility of pullback-unit actions on global sections around a commutative square of
spectra with compatible transition and comparison morphisms. -/
lemma moduleSpecΓFunctor_map_square_transition
    {R₀ R₁ S₀ S₁ : CommRingCat.{u}}
    {t : Spec S₀ ⟶ Spec S₁} {l : Spec S₀ ⟶ Spec R₀}
    {r : Spec S₁ ⟶ Spec R₁} {b : Spec R₀ ⟶ Spec R₁}
    (sq : CommSq t l r b)
    {M₀_m : (Spec R₀).Modules} {M₀_m1 : (Spec R₁).Modules}
    {M₁_m : (Spec S₀).Modules} {M₁_m1 : (Spec S₁).Modules}
    (t₀ : (Scheme.Modules.pullback b).obj M₀_m1 ⟶ M₀_m)
    (t₁ : (Scheme.Modules.pullback t).obj M₁_m1 ⟶ M₁_m)
    (e₀ : (Scheme.Modules.pullback l).obj M₀_m ⟶ M₁_m)
    (e₁ : (Scheme.Modules.pullback r).obj M₀_m1 ⟶ M₁_m1)
    (hnat : (Scheme.Modules.pullback t).map e₁ ≫ t₁ =
      (Scheme.Modules.pullbackCompIsoOfCommSq sq).hom.app M₀_m1 ≫
        (Scheme.Modules.pullback l).map t₀ ≫ e₀)
    (x : moduleSpecΓFunctor.obj M₀_m1) :
    moduleSpecΓFunctor.map e₀
        (moduleSpecΓFunctor.map ((Scheme.Modules.pullbackPushforwardAdjunction l).unit.app M₀_m)
          (moduleSpecΓFunctor.map t₀
            (moduleSpecΓFunctor.map ((Scheme.Modules.pullbackPushforwardAdjunction b).unit.app
              M₀_m1) x))) =
      moduleSpecΓFunctor.map t₁
        (moduleSpecΓFunctor.map ((Scheme.Modules.pullbackPushforwardAdjunction t).unit.app M₁_m1)
          (moduleSpecΓFunctor.map e₁
            (moduleSpecΓFunctor.map ((Scheme.Modules.pullbackPushforwardAdjunction r).unit.app
              M₀_m1) x))) := by
  have hnat' : (Scheme.Modules.pullback l).map t₀ ≫ e₀ =
      (Scheme.Modules.pullbackCompIsoOfCommSq sq).inv.app M₀_m1 ≫
        (Scheme.Modules.pullback t).map e₁ ≫ t₁ :=
    Eq.symm <|
      (congrArg ((Scheme.Modules.pullbackCompIsoOfCommSq sq).inv.app M₀_m1 ≫ ·) hnat).trans
        (Iso.inv_hom_id_app_assoc (Scheme.Modules.pullbackCompIsoOfCommSq sq) M₀_m1 _)
  refine (congrArg (moduleSpecΓFunctor.map e₀)
    (moduleSpecΓFunctor_map_unit_naturality l t₀ _)).trans ?_
  refine (moduleSpecΓFunctor_map_comp_apply _ _ _).symm.trans ?_
  refine (congrArg (fun k ↦ (moduleSpecΓFunctor.map k) _) hnat').trans ?_
  refine (moduleSpecΓFunctor_map_comp_apply _ _ _).trans ?_
  refine (moduleSpecΓFunctor_map_comp_apply _ _ _).trans ?_
  refine (congrArg (fun z ↦ moduleSpecΓFunctor.map t₁
    (moduleSpecΓFunctor.map ((Scheme.Modules.pullback t).map e₁) z))
    (moduleSpecΓFunctor_map_pullbackCompIsoOfCommSq_inv_unit sq M₀_m1 x)).trans ?_
  exact congrArg (moduleSpecΓFunctor.map t₁)
    (moduleSpecΓFunctor_map_unit_naturality t e₁ _).symm

/-- Cancellation of one-sided inverse module morphisms on global sections along a section
`f ≫ g = 𝟙` of spectra. -/
lemma moduleSpecΓFunctor_map_inv_hom_cancel
    {R₀ S₀ : CommRingCat.{u}} {f : Spec R₀ ⟶ Spec S₀} {g : Spec S₀ ⟶ Spec R₀}
    (h : f ≫ g = 𝟙 (Spec R₀)) {M₀ : (Spec R₀).Modules} {N : (Spec S₀).Modules}
    (u : (Scheme.Modules.pullback g).obj M₀ ⟶ N)
    (v : (Scheme.Modules.pullback f).obj N ⟶ M₀)
    (huv : (Scheme.Modules.pullback f).map u ≫ v =
      (Scheme.Modules.pullbackCompIsoId h).hom.app M₀)
    (x : moduleSpecΓFunctor.obj N) (y : moduleSpecΓFunctor.obj M₀)
    (hy : moduleSpecΓFunctor.map u
        (moduleSpecΓFunctor.map ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M₀) y) =
      x) :
    y = moduleSpecΓFunctor.map v
      (moduleSpecΓFunctor.map ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N) x) := by
  have h1 := congrArg (fun z ↦ moduleSpecΓFunctor.map v
    (moduleSpecΓFunctor.map ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N) z))
    hy.symm
  refine Eq.trans ?_ h1.symm
  refine (moduleSpecΓFunctor_map_pullbackCompIsoId_unit h M₀ y).symm.trans ?_
  refine (congrArg (fun k ↦ moduleSpecΓFunctor.map k _) huv.symm).trans ?_
  refine (moduleSpecΓFunctor_map_comp_apply _ _ _).trans ?_
  exact congrArg (moduleSpecΓFunctor.map v) (moduleSpecΓFunctor_map_unit_naturality f u _).symm

end

end AlgebraicGeometry
