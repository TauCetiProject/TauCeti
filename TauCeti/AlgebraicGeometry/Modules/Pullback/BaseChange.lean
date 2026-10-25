/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Sections
public import TauCeti.AlgebraicGeometry.Modules.Pullback.GlobalSections
public import TauCeti.AlgebraicGeometry.Modules.Localization
public import TauCeti.AlgebraicGeometry.Modules.GlobalSections
public import TauCeti.AlgebraicGeometry.Modules.Sections
public import Mathlib.Topology.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import TauCeti.RingTheory.Flat.IsBaseChange
/-!
# Base change of quasicoherent sections

For a morphism of schemes, if an open and its inverse image are affine, sections of the
pullback of a quasicoherent sheaf are obtained by extending scalars along the coordinate-ring
map. The isomorphism is characterized by sending `1 ⊗ s` to the pullback of `s`.

For a cartesian square over `Spec S ⟶ Spec R`, the same section map exhibits sections on the
inverse image as the base change from `R` to `S`. This is the affine-cover input for cohomology
and base change. The module structures remain caller parameters, including at the top open.
Use `pullbackSectionsEquiv` for extension of scalars along the coordinate-ring map, and
`isBaseChange_pullbackSections` for extension along the original base-ring map `R ⟶ S`.

When `R → S` is flat, the same holds over every quasi-compact quasi-separated open `U`, which is
flat base change for the sections of a quasicoherent sheaf
(`isBaseChange_pullbackSections_of_isQuasiSeparated`). Cover `U` by finitely many affine opens
`V i`. Sections over `U` are the kernel of the differences of restrictions
`∏ Γ(V i, M) → ∏ Γ(V i ∩ V j, M)`, before and after base change, and tensoring with the flat
algebra `S` preserves this kernel. The comparison is a base change on each `V i`, and it is
injective on each quasi-compact `V i ∩ V j` (`liftBaseChange_pullbackSectionsBaseLinear_injective`),
by the same argument with only the restrictions to the cover. This follows the proof of
Mathlib's `AlgebraicGeometry.isIso_pushoutSection_of_isQuasiSeparated_of_flat_right` for the
structure sheaf.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isBaseChange_pullbackSections`: base change of sections over an
  affine open, along any base-ring map.
* `AlgebraicGeometry.Scheme.Hom.liftBaseChange_pullbackSectionsBaseLinear_injective`: for flat
  `R → S`, the comparison `S ⊗[R] Γ(U, M) → Γ(g⁻¹ U, g^* M)` is injective over a quasi-compact
  open `U`.
* `AlgebraicGeometry.Scheme.Hom.isBaseChange_pullbackSections_of_isQuasiSeparated`: for flat
  `R → S`, it is bijective over a quasi-compact quasi-separated open `U`.

## References

* R. Hartshorne, *Algebraic Geometry*, Proposition II.5.2(e) and Proposition III.9.3.
* The Stacks Project, Tag 01I9 (pullback of quasicoherent sheaves) and Tag 02KH
  (flat base change of cohomology).
-/
public section
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
open scoped ChangeOfRings TensorProduct
noncomputable section
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {X : Scheme.{u}} (M : X.Modules) {U : X.Opens} (hU : IsAffineOpen U)
private lemma chartPullback_unit (s : Γ(M, U)) :
    ((restrictFunctorIsoPullback hU.fromSpec).hom.app M).app ⊤
      (M.fromSpecSectionsEquiv hU s) =
    Scheme.Hom.pullbackSectionsLE hU.fromSpec M U ⊤ (hU.fromSpec_preimage_self.ge) s := by
  have h : (restrictAdjunction hU.fromSpec).unit.app M ≫
      (pushforward hU.fromSpec).map ((restrictFunctorIsoPullback hU.fromSpec).hom.app M) =
      (pullbackPushforwardAdjunction hU.fromSpec).unit.app M :=
    Adjunction.unit_leftAdjointUniq_hom_app (restrictAdjunction hU.fromSpec)
      (pullbackPushforwardAdjunction hU.fromSpec) M
  have he := congrArg (fun a ↦ a.app U s) h
  simp only [Hom.comp_app, pushforward_map_app, restrictAdjunction_unit_app_app] at he
  have he' : ((restrictFunctorIsoPullback hU.fromSpec).hom.app M).app
      (hU.fromSpec ⁻¹ᵁ U)
        (M.presheaf.map (homOfLE (hU.fromSpec.image_preimage_le U)).op s) =
      hU.fromSpec.pullbackSections M U s := by
    rw [Scheme.Hom.pullbackSections_apply]
    exact he
  have hn := PresheafOfModules.naturality_apply
    ((restrictFunctorIsoPullback hU.fromSpec).hom.app M).val
    (homOfLE (hU.fromSpec_preimage_self.ge)).op
    (M.presheaf.map (homOfLE (hU.fromSpec.image_preimage_le U)).op s)
  have hs : M.fromSpecSectionsEquiv hU s =
      (M.restrict hU.fromSpec).presheaf.map (homOfLE (hU.fromSpec_preimage_self.ge)).op
        (M.presheaf.map (homOfLE (hU.fromSpec.image_preimage_le U)).op s) := by
    rw [fromSpecSectionsEquiv_apply]
    apply (ConcreteCategory.bijective_of_isIso (M.restrictAppIso hU.fromSpec ⊤).hom).injective
    rw [← ConcreteCategory.comp_apply, Iso.inv_hom_id, ConcreteCategory.id_apply]
    -- Restriction along an open immersion computes on image opens.
    change M.presheaf.map _ s = M.presheaf.map _ (M.presheaf.map _ s)
    rw [← M.presheaf.map_comp_apply]
    rfl
  calc
    _ = ((restrictFunctorIsoPullback hU.fromSpec).hom.app M).app ⊤
        ((M.restrict hU.fromSpec).presheaf.map (homOfLE (hU.fromSpec_preimage_self.ge)).op
          (M.presheaf.map (homOfLE (hU.fromSpec.image_preimage_le U)).op s)) :=
      congrArg _ hs
    _ = ((pullback hU.fromSpec).obj M).presheaf.map (homOfLE (hU.fromSpec_preimage_self.ge)).op
        (((restrictFunctorIsoPullback hU.fromSpec).hom.app M).app (hU.fromSpec ⁻¹ᵁ U)
          (M.presheaf.map (homOfLE (hU.fromSpec.image_preimage_le U)).op s)) := hn
    _ = Scheme.Hom.pullbackSectionsLE hU.fromSpec M U ⊤ (hU.fromSpec_preimage_self.ge) s := by
      rw [Scheme.Hom.pullbackSectionsLE_apply]
      exact congrArg (((pullback hU.fromSpec).obj M).presheaf.map
        (homOfLE (hU.fromSpec_preimage_self.ge)).op) he'
private lemma chartPullback_unit_inv (s : Γ(M, U)) :
    ((restrictFunctorIsoPullback hU.fromSpec).inv.app M).app ⊤
      (Scheme.Hom.pullbackSectionsLE hU.fromSpec M U ⊤ (hU.fromSpec_preimage_self.ge) s) =
      M.fromSpecSectionsEquiv hU s := by
  rw [← chartPullback_unit M hU]
  exact congrArg (fun a ↦ a.app ⊤ (M.fromSpecSectionsEquiv hU s))
    ((restrictFunctorIsoPullback hU.fromSpec).app M).hom_inv_id
end AlgebraicGeometry.Scheme.Modules
namespace AlgebraicGeometry.Scheme.Modules
variable {X Y : Scheme.{u}} (g : Y ⟶ X) (M : X.Modules) {U : X.Opens}
  (hU : IsAffineOpen U) (hV : IsAffineOpen (g ⁻¹ᵁ U))
private def chartPullbackIso :
    ((pullback g).obj M).restrict hV.fromSpec ≅
      (pullback (Spec.map (g.app U))).obj (M.restrict hU.fromSpec) := by
  have hc : Spec.map (g.app U) ≫ hU.fromSpec = hV.fromSpec ≫ g := by
    simpa only [Scheme.Hom.appLE_eq_app] using
      IsAffineOpen.SpecMap_appLE_fromSpec g hU hV le_rfl
  exact (restrictFunctorIsoPullback hV.fromSpec).app _ ≪≫
    (pullbackComp hV.fromSpec g).app M ≪≫
    (pullbackCongr hc.symm).app M ≪≫
    ((pullbackComp (Spec.map (g.app U)) hU.fromSpec).app M).symm ≪≫
    (pullback (Spec.map (g.app U))).mapIso ((restrictFunctorIsoPullback hU.fromSpec).app M).symm
private lemma chartPullbackIso_unit (s : Γ(M, U)) :
    (chartPullbackIso g M hU hV).hom.app ⊤
      (((pullback g).obj M).fromSpecSectionsEquiv hV (Scheme.Hom.pullbackSections g M U s)) =
      Scheme.Hom.pullbackSectionsLE (Spec.map (g.app U)) (M.restrict hU.fromSpec)
        ⊤ ⊤ (by simp) (M.fromSpecSectionsEquiv hU s) := by
  simp only [chartPullbackIso, Iso.trans_hom, Iso.symm_hom, Hom.comp_app,
    ConcreteCategory.comp_apply, Functor.mapIso_hom, Iso.app_hom, Iso.app_inv]
  rw [chartPullback_unit]
  rw [← Scheme.Hom.pullbackSectionsLE_self g M U s]
  rw [Scheme.Hom.pullbackSectionsLE_comp_hom]
  rw [Scheme.Hom.pullbackSectionsLE_congr]
  rw [Scheme.Hom.pullbackSectionsLE_comp]
  · rw [Scheme.Hom.pullbackSectionsLE_naturality, chartPullback_unit_inv]
  · exact hU.fromSpec_preimage_self.ge
  · simp
/-- If an open and its inverse image are affine, sections of a quasicoherent pullback
are the extension of the original section module along the map of coordinate rings.
No flatness or finiteness hypothesis is required. -/
def _root_.AlgebraicGeometry.Scheme.Hom.pullbackSectionsEquiv [M.IsQuasicoherent] :
    (ModuleCat.extendScalars (g.app U).hom).obj (.of Γ(X, U) Γ(M, U)) ≃ₗ[Γ(Y, g ⁻¹ᵁ U)]
      Γ((pullback g).obj M,g ⁻¹ᵁ U) := by
  let eM := M.fromSpecSectionsEquiv hU
  let eP := ((pullback g).obj M).fromSpecSectionsEquiv hV
  let eQ := ((moduleSpecΓFunctor (R := Γ(Y, g ⁻¹ᵁ U))).mapIso
    (chartPullbackIso g M hU hV)).toLinearEquiv
  let e := (g.app U).moduleSpecΓPullbackIso (M.restrict hU.fromSpec)
  letI := (g.app U).hom.toAlgebra
  exact (eM.baseChange Γ(X, U) Γ(Y, g ⁻¹ᵁ U)).trans
    (e.toLinearEquiv.trans (eQ.symm.trans eP.symm))
end AlgebraicGeometry.Scheme.Modules
namespace AlgebraicGeometry.Scheme.Modules
variable {X Y : Scheme.{u}} (g : Y ⟶ X) (M : X.Modules) {U : X.Opens}
  (hU : IsAffineOpen U) (hV : IsAffineOpen (g ⁻¹ᵁ U)) [M.IsQuasicoherent]
-- These equations remain named rewrites: normalization of the scalar-extension carrier
-- can change the tensor presentation before simp matches, especially in the inverse equation.
/-- The affine section comparison sends `1 ⊗ s` to the pullback of `s`. -/
lemma _root_.AlgebraicGeometry.Scheme.Hom.pullbackSectionsEquiv_one_tmul (s : Γ(M, U)) :
    Scheme.Hom.pullbackSectionsEquiv g M hU hV ((1 : Γ(Y, g ⁻¹ᵁ U)) ⊗ₜ[Γ(X, U), (g.app U).hom] s) =
      Scheme.Hom.pullbackSections g M U s := by
  let := (g.app U).hom.toAlgebra
  let eM := M.fromSpecSectionsEquiv hU
  let eP := ((pullback g).obj M).fromSpecSectionsEquiv hV
  let eQ := ((moduleSpecΓFunctor (R := Γ(Y, g ⁻¹ᵁ U))).mapIso
    (chartPullbackIso g M hU hV)).toLinearEquiv
  let e := (g.app U).moduleSpecΓPullbackIso (M.restrict hU.fromSpec)
  apply eP.injective
  apply eQ.injective
  have hc : eQ (eP (Scheme.Hom.pullbackSectionsEquiv g M hU hV
        ((1 : Γ(Y, g ⁻¹ᵁ U)) ⊗ₜ[Γ(X, U), (g.app U).hom] s))) =
      e.toLinearEquiv ((1 : Γ(Y, g ⁻¹ᵁ U)) ⊗ₜ[Γ(X, U), (g.app U).hom] eM s) := by
    dsimp only [Scheme.Hom.pullbackSectionsEquiv]
    erw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
      LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
      LinearEquiv.baseChange_tmul]
    rfl
  have hu := (g.app U).moduleSpecΓPullback_app_one_tmul
    (M.restrict hU.fromSpec) (eM s)
  rw [← CommRingCat.Hom.moduleSpecΓPullbackIso_hom] at hu
  have hu' := (Iso.toLinearEquiv_apply e
    ((1 : Γ(Y, g ⁻¹ᵁ U)) ⊗ₜ[Γ(X, U), (g.app U).hom] eM s)).trans hu
  refine hc.trans (hu'.trans ?_)
  -- The section functor changes module structures but its underlying map is evaluation.
  change ((pullbackPushforwardAdjunction (Spec.map (g.app U))).unit.app
    (M.restrict hU.fromSpec)).app ⊤ (M.fromSpecSectionsEquiv hU s) =
    (chartPullbackIso g M hU hV).hom.app ⊤
      (((pullback g).obj M).fromSpecSectionsEquiv hV (Scheme.Hom.pullbackSections g M U s))
  convert! (chartPullbackIso_unit g M hU hV s).symm using 1
  erw [Scheme.Hom.pullbackSectionsLE_apply]
  simp only [Scheme.Hom.pullbackSections_apply]
  simp
  rfl
/-- The inverse affine comparison takes a pulled-back section to `1 ⊗ s`. -/
lemma _root_.AlgebraicGeometry.Scheme.Hom.pullbackSectionsEquiv_symm_pullbackSections
    (s : Γ(M, U)) :
    (g.pullbackSectionsEquiv M hU hV).symm (g.pullbackSections M U s) =
      (1 : Γ(Y, g ⁻¹ᵁ U)) ⊗ₜ[Γ(X, U), (g.app U).hom] s := by
  have h := congrArg (g.pullbackSectionsEquiv M hU hV).symm
    (g.pullbackSectionsEquiv_one_tmul M hU hV s)
  erw [LinearEquiv.symm_apply_apply] at h
  exact h.symm
end AlgebraicGeometry.Scheme.Modules
namespace AlgebraicGeometry.Scheme.Hom
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  {X Y : Scheme.{u}} [X.Over (Spec (.of R))] [Y.Over (Spec (.of S))]
  (g : Y ⟶ X) (M : X.Modules) (U : X.Opens)
/-- Pullback of sections is linear over the original base in a commuting square over
`Spec S ⟶ Spec R`. The module structures and scalar towers are caller parameters, so this
also preserves the usual actions on global sections when `U = ⊤`. -/
def pullbackSectionsBaseLinear
    (C : CommSq g (Y ↘ Spec (.of S)) (X ↘ Spec (.of R))
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))) :
    letI : Algebra R Γ(X, U) :=
      ((X.baseRingToStructurePresheaf R).app (op U)).hom.toAlgebra
    letI : Algebra S Γ(Y, g ⁻¹ᵁ U) :=
      ((Y.baseRingToStructurePresheaf S).app (op (g ⁻¹ᵁ U))).hom.toAlgebra
    ∀ [Module R Γ(M, U)] [Module S Γ((pullback g).obj M, g ⁻¹ᵁ U)]
      [Module R Γ((pullback g).obj M, g ⁻¹ᵁ U)]
      [IsScalarTower R Γ(X, U) Γ(M, U)]
      [IsScalarTower S Γ(Y, g ⁻¹ᵁ U) Γ((pullback g).obj M, g ⁻¹ᵁ U)]
      [IsScalarTower R S Γ((pullback g).obj M, g ⁻¹ᵁ U)],
      Γ(M, U) →ₗ[R] Γ((pullback g).obj M, g ⁻¹ᵁ U) := by
  let : Algebra R Γ(X, U) :=
    ((X.baseRingToStructurePresheaf R).app (op U)).hom.toAlgebra
  let : Algebra S Γ(Y, g ⁻¹ᵁ U) :=
    ((Y.baseRingToStructurePresheaf S).app (op (g ⁻¹ᵁ U))).hom.toAlgebra
  intro _ _ _ _ _ _
  let : Algebra Γ(X, U) Γ(Y, g ⁻¹ᵁ U) := (g.app U).hom.toAlgebra
  let : Algebra R Γ(Y, g ⁻¹ᵁ U) :=
    ((g.app U).hom.comp (algebraMap R Γ(X, U))).toAlgebra
  have := Scheme.Modules.isScalarTower_baseRingToStructurePresheaf_app g U C
  have := IsScalarTower.to₁₃₄ R S Γ(Y, g ⁻¹ᵁ U) Γ((pullback g).obj M, g ⁻¹ᵁ U)
  exact
    { toFun := g.pullbackSections M U
      map_add' := map_add _
      map_smul' r s := by
        rw [← IsScalarTower.algebraMap_smul Γ(X, U) r s, map_smulₛₗ]
        have hr : (g.app U).hom (algebraMap R Γ(X, U) r) =
            algebraMap R Γ(Y, g ⁻¹ᵁ U) r := rfl
        rw [hr, IsScalarTower.algebraMap_smul Γ(Y, g ⁻¹ᵁ U), RingHom.id_apply] }
/-- The base-linear pullback has the same values as the canonical semilinear section map. -/
@[simp]
lemma pullbackSectionsBaseLinear_apply
    (C : CommSq g (Y ↘ Spec (.of S)) (X ↘ Spec (.of R))
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))) :
    letI : Algebra R Γ(X, U) :=
      ((X.baseRingToStructurePresheaf R).app (op U)).hom.toAlgebra
    letI : Algebra S Γ(Y, g ⁻¹ᵁ U) :=
      ((Y.baseRingToStructurePresheaf S).app (op (g ⁻¹ᵁ U))).hom.toAlgebra
    ∀ [Module R Γ(M, U)] [Module S Γ((pullback g).obj M, g ⁻¹ᵁ U)]
      [Module R Γ((pullback g).obj M, g ⁻¹ᵁ U)]
      [IsScalarTower R Γ(X, U) Γ(M, U)]
      [IsScalarTower S Γ(Y, g ⁻¹ᵁ U) Γ((pullback g).obj M, g ⁻¹ᵁ U)]
      [IsScalarTower R S Γ((pullback g).obj M, g ⁻¹ᵁ U)],
      ∀ s : Γ(M, U), g.pullbackSectionsBaseLinear M U C s = g.pullbackSections M U s := by
  intro _ _ _ _ _ _ s
  rfl
/-- Affine base change of quasicoherent sections over the original base ring. No flatness,
finiteness, or Noetherian hypothesis is needed. Caller-supplied module structures are retained. -/
theorem isBaseChange_pullbackSections [M.IsQuasicoherent]
    (H : IsPullback g (Y ↘ Spec (.of S)) (X ↘ Spec (.of R))
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))) (hU : IsAffineOpen U) :
    letI : Algebra R Γ(X, U) :=
      ((X.baseRingToStructurePresheaf R).app (op U)).hom.toAlgebra
    letI : Algebra S Γ(Y, g ⁻¹ᵁ U) :=
      ((Y.baseRingToStructurePresheaf S).app (op (g ⁻¹ᵁ U))).hom.toAlgebra
    ∀ [Module R Γ(M, U)] [Module S Γ((pullback g).obj M, g ⁻¹ᵁ U)]
      [Module R Γ((pullback g).obj M, g ⁻¹ᵁ U)]
      [IsScalarTower R Γ(X, U) Γ(M, U)]
      [IsScalarTower S Γ(Y, g ⁻¹ᵁ U) Γ((pullback g).obj M, g ⁻¹ᵁ U)]
      [IsScalarTower R S Γ((pullback g).obj M, g ⁻¹ᵁ U)],
      IsBaseChange S (g.pullbackSectionsBaseLinear M U H.toCommSq) := by
  let : Algebra R Γ(X, U) :=
    ((X.baseRingToStructurePresheaf R).app (op U)).hom.toAlgebra
  let : Algebra S Γ(Y, g ⁻¹ᵁ U) :=
    ((Y.baseRingToStructurePresheaf S).app (op (g ⁻¹ᵁ U))).hom.toAlgebra
  intro _ _ _ _ _ _
  let : Algebra Γ(X, U) Γ(Y, g ⁻¹ᵁ U) := (g.app U).hom.toAlgebra
  let : Algebra R Γ(Y, g ⁻¹ᵁ U) :=
    ((g.app U).hom.comp (algebraMap R Γ(X, U))).toAlgebra
  have : IsScalarTower R Γ(X, U) Γ(Y, g ⁻¹ᵁ U) := .of_algebraMap_eq' rfl
  have := Scheme.Modules.isScalarTower_baseRingToStructurePresheaf_app g U H.toCommSq
  have := IsScalarTower.to₁₃₄ R S Γ(Y, g ⁻¹ᵁ U) Γ((pullback g).obj M, g ⁻¹ᵁ U)
  have : Algebra.IsPushout R S Γ(X, U) Γ(Y, g ⁻¹ᵁ U) :=
    CommRingCat.isPushout_iff_isPushout.mp
      (Scheme.isPushout_baseRingToStructurePresheaf_of_isAffineOpen H hU)
  have : IsAffineHom g := MorphismProperty.of_isPullback H.flip inferInstance
  let e : Γ(Y, g ⁻¹ᵁ U) ⊗[Γ(X, U)] Γ(M, U) ≃ₗ[Γ(Y, g ⁻¹ᵁ U)]
      Γ((pullback g).obj M, g ⁻¹ᵁ U) := g.pullbackSectionsEquiv M hU (hU.preimage g)
  refine IsBaseChange.of_equiv
    ((Algebra.IsPushout.cancelBaseChange R S Γ(X, U) Γ(Y, g ⁻¹ᵁ U) Γ(M, U)).symm.trans
      (e.restrictScalars S)) ?_
  intro s
  simp only [LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply,
    Algebra.IsPushout.cancelBaseChange_symm_tmul, map_one]
  exact g.pullbackSectionsEquiv_one_tmul M hU (hU.preimage g) s
end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme.Modules

section Restriction

variable (T : Type u) [CommRing T] {Z : Scheme.{u}} [Z.Over (Spec (.of T))] (N : Z.Modules)
  {W : Z.Opens} {ι : Type*} (V : ι → Z.Opens)

/-- The restrictions of the sections over `W` to a family of opens `V i ≤ W`, linear over the
base ring `T`, for any action of `T` on the sections over `W` through functions and for the action
through functions on the sections over each `V i`. -/
private def sectionsRestrictPiBaseLinear (hV : ∀ i, V i ≤ W) :
    letI : Algebra T Γ(Z, W) := ((Z.baseRingToStructurePresheaf T).app (op W)).hom.toAlgebra
    ∀ [Module T Γ(N, W)] [IsScalarTower T Γ(Z, W) Γ(N, W)],
      letI := fun i ↦ sectionsBaseModule T N (V i)
      Γ(N, W) →ₗ[T] ∀ i, Γ(N, V i) := by
  letI : Algebra T Γ(Z, W) := ((Z.baseRingToStructurePresheaf T).app (op W)).hom.toAlgebra
  intro _ _
  letI := fun i ↦ sectionsBaseModule T N (V i)
  exact
    { toFun s i := N.presheaf.map (homOfLE (hV i)).op s
      map_add' _ _ := funext fun _ ↦ map_add _ _ _
      map_smul' t s := funext fun i ↦ by
        rw [← IsScalarTower.algebraMap_smul Γ(Z, W) t s, RingHom.id_apply]
        exact presheaf_map_baseRingToStructurePresheaf_smul T N (homOfLE (hV i)) t s }

private lemma sectionsRestrictPiBaseLinear_apply (hV : ∀ i, V i ≤ W) :
    letI : Algebra T Γ(Z, W) := ((Z.baseRingToStructurePresheaf T).app (op W)).hom.toAlgebra
    ∀ [Module T Γ(N, W)] [IsScalarTower T Γ(Z, W) Γ(N, W)] (s : Γ(N, W)) (i : ι),
      sectionsRestrictPiBaseLinear T N V hV s i = N.presheaf.map (homOfLE (hV i)).op s := by
  intro _ _ _ _
  rfl

/-- A section over `W` is determined by its restrictions to a family of opens covering `W`. -/
private lemma sectionsRestrictPiBaseLinear_injective (hV : ∀ i, V i ≤ W) (hW : W ≤ ⨆ i, V i) :
    letI : Algebra T Γ(Z, W) := ((Z.baseRingToStructurePresheaf T).app (op W)).hom.toAlgebra
    ∀ [Module T Γ(N, W)] [IsScalarTower T Γ(Z, W) Γ(N, W)],
      Function.Injective (sectionsRestrictPiBaseLinear T N V hV) := by
  intro _ _ s t h
  exact TopCat.Sheaf.eq_of_locally_eq' (⟨N.presheaf, N.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat Z)
    V W (fun i ↦ homOfLE (hV i)) hW s t fun i ↦ congrFun h i

variable {κ : Type*} (W' : κ → Z.Opens) (a b : κ → ι) (ha : ∀ p, W' p ≤ V (a p))
  (hb : ∀ p, W' p ≤ V (b p))

/-- The differences `s (a p)|_{W' p} - s (b p)|_{W' p}` of the restrictions of a family of sections
over the `V i` to opens `W' p ≤ V (a p) ⊓ V (b p)`, linear over the base ring `T` acting through
functions. -/
private def sectionsDiffPiBaseLinear :
    letI := fun i ↦ sectionsBaseModule T N (V i)
    letI := fun p ↦ sectionsBaseModule T N (W' p)
    (∀ i, Γ(N, V i)) →ₗ[T] ∀ p, Γ(N, W' p) :=
  letI := fun i ↦ sectionsBaseModule T N (V i)
  letI := fun p ↦ sectionsBaseModule T N (W' p)
  LinearMap.pi fun p ↦
    (((sectionsBasePresheafFunctor T).obj N).map (homOfLE (ha p)).op).hom ∘ₗ
        LinearMap.proj (R := T) (φ := fun i ↦ ((sectionsBasePresheafFunctor T).obj N).obj
          (op (V i))) (a p) -
      (((sectionsBasePresheafFunctor T).obj N).map (homOfLE (hb p)).op).hom ∘ₗ
        LinearMap.proj (R := T) (φ := fun i ↦ ((sectionsBasePresheafFunctor T).obj N).obj
          (op (V i))) (b p)

private lemma sectionsDiffPiBaseLinear_apply (s : ∀ i, Γ(N, V i)) (p : κ) :
    sectionsDiffPiBaseLinear T N V W' a b ha hb s p =
      N.presheaf.map (homOfLE (ha p)).op (s (a p)) -
        N.presheaf.map (homOfLE (hb p)).op (s (b p)) :=
  rfl

/-- Families of sections over the `V i` whose restrictions agree on the opens `W' p` are exactly the
restrictions of the sections over `W`, when the `V i` cover `W` and every pairwise intersection
`V i ⊓ V j` lies in some `W' p` with `a p = i` and `b p = j`. -/
private lemma exact_sectionsRestrictPiBaseLinear (hV : ∀ i, V i ≤ W) (hW : W ≤ ⨆ i, V i)
    (hab : ∀ i j, ∃ p, a p = i ∧ b p = j ∧ V i ⊓ V j ≤ W' p) :
    letI : Algebra T Γ(Z, W) := ((Z.baseRingToStructurePresheaf T).app (op W)).hom.toAlgebra
    ∀ [Module T Γ(N, W)] [IsScalarTower T Γ(Z, W) Γ(N, W)],
      Function.Exact (sectionsRestrictPiBaseLinear T N V hV)
        (sectionsDiffPiBaseLinear T N V W' a b ha hb) := by
  intro _ _ x
  let F : TopCat.Sheaf AddCommGrpCat Z := ⟨N.presheaf, N.isSheaf⟩
  constructor
  · intro h
    have hc : TopCat.Presheaf.IsCompatible F.obj V x := fun i j ↦ by
      obtain ⟨p, rfl, rfl, hp⟩ := hab i j
      have h' := congrFun h p
      rw [sectionsDiffPiBaseLinear_apply, Pi.zero_apply, sub_eq_zero] at h'
      have := congrArg (N.presheaf.map (homOfLE hp).op) h'
      rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
        ← Functor.map_comp] at this
      -- Both sides restrict to `V (a p) ⊓ V (b p)`; morphisms between opens are unique.
      exact this
    obtain ⟨z, hz, -⟩ := F.existsUnique_gluing' V W (fun i ↦ homOfLE (hV i)) hW x hc
    exact ⟨z, funext hz⟩
  · rintro ⟨z, rfl⟩
    funext p
    rw [sectionsDiffPiBaseLinear_apply, sectionsRestrictPiBaseLinear_apply,
      sectionsRestrictPiBaseLinear_apply, Pi.zero_apply, sub_eq_zero,
      ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
      ← Functor.map_comp]
    -- Both sides restrict `z` to `W' p`; morphisms between opens are unique.
    rfl

end Restriction

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Hom

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  {X Y : Scheme.{u}} [X.Over (Spec (.of R))] [Y.Over (Spec (.of S))]
  (g : Y ⟶ X) (M : X.Modules) [M.IsQuasicoherent]
  (H : IsPullback g (Y ↘ Spec (.of S)) (X ↘ Spec (.of R))
    (Spec.map (CommRingCat.ofHom (algebraMap R S))))

/-- On a finite family of affine opens, the product of the pullbacks of sections is a base change
from `R` to `S`, for the actions of the base rings through functions. -/
private lemma isBaseChange_pi_pullbackSectionsBaseLinear {ι : Type*} [Finite ι] (V : ι → X.Opens)
    (hV : ∀ i, IsAffineOpen (V i)) :
    letI := fun i ↦ sectionsBaseModule R M (V i)
    letI := fun i ↦ sectionsBaseModule S ((pullback g).obj M) (g ⁻¹ᵁ V i)
    letI : ∀ i, Module R Γ((pullback g).obj M, g ⁻¹ᵁ V i) :=
      fun _ ↦ Module.compHom _ (algebraMap R S)
    haveI : ∀ i, IsScalarTower R S Γ((pullback g).obj M, g ⁻¹ᵁ V i) :=
      fun _ ↦ .of_algebraMap_smul fun _ _ ↦ rfl
    letI : ∀ i, Algebra R Γ(X, V i) :=
      fun i ↦ ((X.baseRingToStructurePresheaf R).app (op (V i))).hom.toAlgebra
    letI : ∀ i, Algebra S Γ(Y, g ⁻¹ᵁ V i) :=
      fun i ↦ ((Y.baseRingToStructurePresheaf S).app (op (g ⁻¹ᵁ V i))).hom.toAlgebra
    haveI : ∀ i, IsScalarTower R Γ(X, V i) Γ(M, V i) :=
      fun _ ↦ .of_algebraMap_smul fun _ _ ↦ rfl
    haveI : ∀ i, IsScalarTower S Γ(Y, g ⁻¹ᵁ V i) Γ((pullback g).obj M, g ⁻¹ᵁ V i) :=
      fun _ ↦ .of_algebraMap_smul fun _ _ ↦ rfl
    IsBaseChange S (LinearMap.pi fun i ↦
      g.pullbackSectionsBaseLinear M (V i) H.toCommSq ∘ₗ LinearMap.proj i) := by
  let := fun i ↦ sectionsBaseModule R M (V i)
  let := fun i ↦ sectionsBaseModule S ((pullback g).obj M) (g ⁻¹ᵁ V i)
  let : ∀ i, Module R Γ((pullback g).obj M, g ⁻¹ᵁ V i) :=
    fun _ ↦ Module.compHom _ (algebraMap R S)
  have : ∀ i, IsScalarTower R S Γ((pullback g).obj M, g ⁻¹ᵁ V i) :=
    fun _ ↦ .of_algebraMap_smul fun _ _ ↦ rfl
  let : ∀ i, Algebra R Γ(X, V i) :=
    fun i ↦ ((X.baseRingToStructurePresheaf R).app (op (V i))).hom.toAlgebra
  let : ∀ i, Algebra S Γ(Y, g ⁻¹ᵁ V i) :=
    fun i ↦ ((Y.baseRingToStructurePresheaf S).app (op (g ⁻¹ᵁ V i))).hom.toAlgebra
  have : ∀ i, IsScalarTower R Γ(X, V i) Γ(M, V i) :=
    fun _ ↦ .of_algebraMap_smul fun _ _ ↦ rfl
  have : ∀ i, IsScalarTower S Γ(Y, g ⁻¹ᵁ V i) Γ((pullback g).obj M, g ⁻¹ᵁ V i) :=
    fun _ ↦ .of_algebraMap_smul fun _ _ ↦ rfl
  exact IsBaseChange.pi _ fun i ↦ g.isBaseChange_pullbackSections M (V i) H (hV i)

/-- **Flat base change of sections over a quasi-compact open is injective.** Let `X` be a scheme
over `R`, let `R → S` be flat and let `Y = X ×_R S` with projection `g : Y ⟶ X`. For a
quasi-coherent sheaf `M` on `X` and a quasi-compact open `U` of `X`, the map
`S ⊗[R] Γ(U, M) → Γ(g⁻¹ U, g^* M)`, `s ⊗ m ↦ s • g^* m`, is injective. -/
theorem liftBaseChange_pullbackSectionsBaseLinear_injective [Module.Flat R S] {U : X.Opens}
    (hU : IsCompact (U : Set X)) :
    letI : Algebra R Γ(X, U) :=
      ((X.baseRingToStructurePresheaf R).app (op U)).hom.toAlgebra
    letI : Algebra S Γ(Y, g ⁻¹ᵁ U) :=
      ((Y.baseRingToStructurePresheaf S).app (op (g ⁻¹ᵁ U))).hom.toAlgebra
    ∀ [Module R Γ(M, U)] [Module S Γ((pullback g).obj M, g ⁻¹ᵁ U)]
      [Module R Γ((pullback g).obj M, g ⁻¹ᵁ U)]
      [IsScalarTower R Γ(X, U) Γ(M, U)]
      [IsScalarTower S Γ(Y, g ⁻¹ᵁ U) Γ((pullback g).obj M, g ⁻¹ᵁ U)]
      [IsScalarTower R S Γ((pullback g).obj M, g ⁻¹ᵁ U)],
      Function.Injective ((g.pullbackSectionsBaseLinear M U H.toCommSq).liftBaseChange S) := by
  let : Algebra R Γ(X, U) := ((X.baseRingToStructurePresheaf R).app (op U)).hom.toAlgebra
  let : Algebra S Γ(Y, g ⁻¹ᵁ U) :=
    ((Y.baseRingToStructurePresheaf S).app (op (g ⁻¹ᵁ U))).hom.toAlgebra
  intro _ _ _ _ _ _
  -- Cover `U` by finitely many affine opens `V i`.
  obtain ⟨s, hs, hsU⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp hU
  have := hs.to_subtype
  let V : s → X.Opens := fun i ↦ i.1
  have hVU (i : s) : V i ≤ U := hsU ▸ le_biSup (fun j : X.affineOpens ↦ (j : X.Opens)) i.2
  have hUV : U ≤ ⨆ i, V i := by rw [hsU, iSup_subtype']
  let := fun i ↦ sectionsBaseModule R M (V i)
  let := fun i ↦ sectionsBaseModule S ((pullback g).obj M) (g ⁻¹ᵁ V i)
  let : ∀ i, Module R Γ((pullback g).obj M, g ⁻¹ᵁ V i) :=
    fun _ ↦ Module.compHom _ (algebraMap R S)
  have : ∀ i, IsScalarTower R S Γ((pullback g).obj M, g ⁻¹ᵁ V i) :=
    fun _ ↦ .of_algebraMap_smul fun _ _ ↦ rfl
  -- Restriction to the cover is injective, and the pullback of sections on the cover is a base
  -- change.
  refine LinearMap.liftBaseChange_injective_of_isBaseChange S
    (f := sectionsRestrictPiBaseLinear R M V hVU)
    (f' := sectionsRestrictPiBaseLinear S ((pullback g).obj M) (fun i ↦ g ⁻¹ᵁ V i)
      fun i ↦ g.preimage_mono (hVU i)) ?_
    (isBaseChange_pi_pullbackSectionsBaseLinear g M H V fun i ↦ i.1.2)
    (sectionsRestrictPiBaseLinear_injective R M V hVU hUV)
  ext x i
  simp only [LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.coe_proj, Function.eval,
    LinearMap.restrictScalars_apply, sectionsRestrictPiBaseLinear_apply,
    pullbackSectionsBaseLinear_apply]
  exact (g.pullbackSections_restrict M U (homOfLE (hVU i)) x).symm

/-- Flat base change of sections over an open `U` covered by finitely many affine opens `V i`,
given quasi-compact opens `W' p ≤ V (a p) ⊓ V (b p)` containing all pairwise intersections. -/
private lemma isBaseChange_pullbackSectionsBaseLinear_of_cover [Module.Flat R S] {U : X.Opens}
    {ι κ : Type u} [Finite ι] [Finite κ] (V : ι → X.Opens) (hV : ∀ i, IsAffineOpen (V i))
    (hVU : ∀ i, V i ≤ U) (hUV : U ≤ ⨆ i, V i) (W' : κ → X.Opens) (a b : κ → ι)
    (ha : ∀ p, W' p ≤ V (a p)) (hb : ∀ p, W' p ≤ V (b p))
    (hab : ∀ i j, ∃ p, a p = i ∧ b p = j ∧ V i ⊓ V j ≤ W' p)
    (hW' : ∀ p, IsCompact (W' p : Set X)) :
    letI : Algebra R Γ(X, U) :=
      ((X.baseRingToStructurePresheaf R).app (op U)).hom.toAlgebra
    letI : Algebra S Γ(Y, g ⁻¹ᵁ U) :=
      ((Y.baseRingToStructurePresheaf S).app (op (g ⁻¹ᵁ U))).hom.toAlgebra
    ∀ [Module R Γ(M, U)] [Module S Γ((pullback g).obj M, g ⁻¹ᵁ U)]
      [Module R Γ((pullback g).obj M, g ⁻¹ᵁ U)]
      [IsScalarTower R Γ(X, U) Γ(M, U)]
      [IsScalarTower S Γ(Y, g ⁻¹ᵁ U) Γ((pullback g).obj M, g ⁻¹ᵁ U)]
      [IsScalarTower R S Γ((pullback g).obj M, g ⁻¹ᵁ U)],
      IsBaseChange S (g.pullbackSectionsBaseLinear M U H.toCommSq) := by
  let : Algebra R Γ(X, U) := ((X.baseRingToStructurePresheaf R).app (op U)).hom.toAlgebra
  let : Algebra S Γ(Y, g ⁻¹ᵁ U) :=
    ((Y.baseRingToStructurePresheaf S).app (op (g ⁻¹ᵁ U))).hom.toAlgebra
  intro _ _ _ _ _ _
  have hUV' : g ⁻¹ᵁ U ≤ ⨆ i, g ⁻¹ᵁ V i := by
    rw [← Scheme.Hom.preimage_iSup]
    exact g.preimage_mono hUV
  have hab' (i j : ι) : ∃ p, a p = i ∧ b p = j ∧ g ⁻¹ᵁ V i ⊓ g ⁻¹ᵁ V j ≤ g ⁻¹ᵁ W' p := by
    obtain ⟨p, hpa, hpb, hp⟩ := hab i j
    exact ⟨p, hpa, hpb, g.preimage_mono hp⟩
  let N := (pullback g).obj M
  let := fun i ↦ sectionsBaseModule R M (V i)
  let := fun i ↦ sectionsBaseModule S N (g ⁻¹ᵁ V i)
  let : ∀ i, Module R Γ(N, g ⁻¹ᵁ V i) := fun _ ↦ Module.compHom _ (algebraMap R S)
  have : ∀ i, IsScalarTower R S Γ(N, g ⁻¹ᵁ V i) := fun _ ↦ .of_algebraMap_smul fun _ _ ↦ rfl
  let := fun p ↦ sectionsBaseModule R M (W' p)
  let := fun p ↦ sectionsBaseModule S N (g ⁻¹ᵁ W' p)
  let : ∀ p, Module R Γ(N, g ⁻¹ᵁ W' p) := fun _ ↦ Module.compHom _ (algebraMap R S)
  have : ∀ p, IsScalarTower R S Γ(N, g ⁻¹ᵁ W' p) := fun _ ↦ .of_algebraMap_smul fun _ _ ↦ rfl
  let : ∀ p, Algebra R Γ(X, W' p) :=
    fun p ↦ ((X.baseRingToStructurePresheaf R).app (op (W' p))).hom.toAlgebra
  let : ∀ p, Algebra S Γ(Y, g ⁻¹ᵁ W' p) :=
    fun p ↦ ((Y.baseRingToStructurePresheaf S).app (op (g ⁻¹ᵁ W' p))).hom.toAlgebra
  have : ∀ p, IsScalarTower R Γ(X, W' p) Γ(M, W' p) := fun _ ↦ .of_algebraMap_smul fun _ _ ↦ rfl
  have : ∀ p, IsScalarTower S Γ(Y, g ⁻¹ᵁ W' p) Γ(N, g ⁻¹ᵁ W' p) :=
    fun _ ↦ .of_algebraMap_smul fun _ _ ↦ rfl
  -- Sections over `U` are the kernel of the differences of restrictions to the `W' p`, before
  -- and after base change. The comparison is a base change on the cover, and injective after
  -- base change on the `W' p`.
  refine IsBaseChange.of_left_exact_of_injective S
    (h₃ := LinearMap.pi fun p ↦ g.pullbackSectionsBaseLinear M (W' p) H.toCommSq ∘ₗ
      LinearMap.proj p)
    (f := sectionsRestrictPiBaseLinear R M V hVU) (g := sectionsDiffPiBaseLinear R M V W' a b ha hb)
    (f' := sectionsRestrictPiBaseLinear S N (fun i ↦ g ⁻¹ᵁ V i) fun i ↦ g.preimage_mono (hVU i))
    (g' := sectionsDiffPiBaseLinear S N (fun i ↦ g ⁻¹ᵁ V i) (fun p ↦ g ⁻¹ᵁ W' p) a b
      (fun p ↦ g.preimage_mono (ha p)) fun p ↦ g.preimage_mono (hb p)) ?_ ?_
    (isBaseChange_pi_pullbackSectionsBaseLinear g M H V hV)
    (LinearMap.liftBaseChange_pi_injective S _ fun p ↦
      liftBaseChange_pullbackSectionsBaseLinear_injective g M H (hW' p))
    (exact_sectionsRestrictPiBaseLinear R M V W' a b ha hb hVU hUV hab)
    (sectionsRestrictPiBaseLinear_injective R M V hVU hUV)
    (exact_sectionsRestrictPiBaseLinear S N _ _ a b _ _ _ hUV' hab')
    (sectionsRestrictPiBaseLinear_injective S N _ _ hUV')
  · ext x i
    simp only [LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.coe_proj, Function.eval,
      LinearMap.restrictScalars_apply, sectionsRestrictPiBaseLinear_apply,
      pullbackSectionsBaseLinear_apply]
    exact (g.pullbackSections_restrict M U (homOfLE (hVU i)) x).symm
  · ext x p
    simp only [LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.coe_proj, Function.eval,
      LinearMap.restrictScalars_apply, sectionsDiffPiBaseLinear_apply,
      pullbackSectionsBaseLinear_apply, map_sub]
    rw [← g.pullbackSections_restrict M (V (a p)) (homOfLE (ha p)),
      ← g.pullbackSections_restrict M (V (b p)) (homOfLE (hb p))]
    -- `(Opens.map g.base).map (homOfLE _)` is an inclusion of opens; such morphisms are unique.
    rfl

/-- **Flat base change of sections over a quasi-compact quasi-separated open.** Let `X` be a scheme
over `R`, let `R → S` be flat and let `Y = X ×_R S` with projection `g : Y ⟶ X`. For a
quasi-coherent sheaf `M` on `X` and a quasi-compact quasi-separated open `U` of `X`, pulling back
sections exhibits `Γ(g⁻¹ U, g^* M)` as the base change `S ⊗[R] Γ(U, M)`. -/
theorem isBaseChange_pullbackSections_of_isQuasiSeparated [Module.Flat R S] {U : X.Opens}
    (hU : IsCompact (U : Set X)) (hU' : IsQuasiSeparated (U : Set X)) :
    letI : Algebra R Γ(X, U) :=
      ((X.baseRingToStructurePresheaf R).app (op U)).hom.toAlgebra
    letI : Algebra S Γ(Y, g ⁻¹ᵁ U) :=
      ((Y.baseRingToStructurePresheaf S).app (op (g ⁻¹ᵁ U))).hom.toAlgebra
    ∀ [Module R Γ(M, U)] [Module S Γ((pullback g).obj M, g ⁻¹ᵁ U)]
      [Module R Γ((pullback g).obj M, g ⁻¹ᵁ U)]
      [IsScalarTower R Γ(X, U) Γ(M, U)]
      [IsScalarTower S Γ(Y, g ⁻¹ᵁ U) Γ((pullback g).obj M, g ⁻¹ᵁ U)]
      [IsScalarTower R S Γ((pullback g).obj M, g ⁻¹ᵁ U)],
      IsBaseChange S (g.pullbackSectionsBaseLinear M U H.toCommSq) := by
  intro _ _ _ _ _ _
  -- Cover `U` by finitely many affine opens; their pairwise intersections are quasi-compact.
  obtain ⟨s, hs, hsU⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp hU
  have := hs.to_subtype
  have hVU (i : s) : (i.1 : X.Opens) ≤ U :=
    hsU ▸ le_biSup (fun j : X.affineOpens ↦ (j : X.Opens)) i.2
  exact isBaseChange_pullbackSectionsBaseLinear_of_cover g M H (fun i : s ↦ i.1) (fun i ↦ i.1.2)
    hVU (by rw [hsU, iSup_subtype']) (fun p : s × s ↦ p.1.1 ⊓ p.2.1) Prod.fst Prod.snd
    (fun _ ↦ inf_le_left) (fun _ ↦ inf_le_right) (fun i j ↦ ⟨(i, j), rfl, rfl, le_rfl⟩)
    fun p ↦ hU' _ _ (hVU p.1) p.1.1.1.isOpen p.1.1.2.isCompact (hVU p.2) p.2.1.1.isOpen
      p.2.1.2.isCompact

end AlgebraicGeometry.Scheme.Hom
