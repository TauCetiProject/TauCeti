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
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
/-!
# Affine base change of quasicoherent sections
For a morphism of schemes, if an open and its inverse image are affine, sections of the
pullback of a quasicoherent sheaf are obtained by extending scalars along the coordinate-ring
map. The isomorphism is characterized by sending `1 ⊗ s` to the pullback of `s`.
For a cartesian square over `Spec S ⟶ Spec R`, the same section map exhibits sections on the
inverse image as the base change from `R` to `S`. This is the affine-cover input for cohomology
and base change. The module structures remain caller parameters, including at the top open.
The construction transports the affine-spectrum comparison to the actual open-section carriers.
It uses the pullback composition and restriction comparisons through their unit equations.
## References
* R. Hartshorne, *Algebraic Geometry*, Proposition II.5.2(e).
* The Stacks Project, Tag 01I9 (pullback of quasicoherent sheaves) and Tag 02KH
  (flat base change of cohomology).
-/
public section
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
open scoped ChangeOfRings TensorProduct
noncomputable section
universe u
namespace AlgebraicGeometry.Scheme
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  {X Y : Scheme.{u}} [X.Over (Spec (.of R))] [Y.Over (Spec (.of S))]
  {g : Y ⟶ X}
/-- In a cartesian square over affine bases, the coordinate rings of an affine open and
its inverse image form a pushout over the original base rings. -/
theorem isPushout_baseRingToStructurePresheaf_of_isAffineOpen
    (H : IsPullback g (Y ↘ Spec (.of S)) (X ↘ Spec (.of R))
      (Spec.map (CommRingCat.ofHom (algebraMap R S))))
    {U : X.Opens} (hU : IsAffineOpen U) :
    let : Algebra R Γ(X, U) := ((X.baseRingToStructurePresheaf R).app (op U)).hom.toAlgebra
    let : Algebra S Γ(Y, g ⁻¹ᵁ U) :=
      ((Y.baseRingToStructurePresheaf S).app (op (g ⁻¹ᵁ U))).hom.toAlgebra
    IsPushout (CommRingCat.ofHom (algebraMap R S))
      (CommRingCat.ofHom (algebraMap R Γ(X, U)))
      (CommRingCat.ofHom (algebraMap S Γ(Y, g ⁻¹ᵁ U))) (g.app U) := by
  have : IsAffineHom g := MorphismProperty.of_isPullback H.flip inferInstance
  let : Algebra R Γ(X, U) := ((X.baseRingToStructurePresheaf R).app (op U)).hom.toAlgebra
  let : Algebra S Γ(Y, g ⁻¹ᵁ U) :=
    ((Y.baseRingToStructurePresheaf S).app (op (g ⁻¹ᵁ U))).hom.toAlgebra
  have := isIso_pushoutSection_of_isAffineOpen H (US := ⊤) (UT := ⊤) (UX := U)
    (UY := g ⁻¹ᵁ U) le_top le_top (by simp) (isAffineOpen_top _) (isAffineOpen_top _) hU
  refine ((isIso_pushoutSection_iff ..).mp this).flip.of_iso (Scheme.ΓSpecIso (.of R))
    (Scheme.ΓSpecIso (.of S)) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · rw [← Scheme.ΓSpecIso_naturality]
    exact congrArg (· ≫ _) (Scheme.Hom.appLE_eq_app _)
  · simp only [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom,
      Scheme.baseRingToStructurePresheaf_app_eq_appLE, Iso.hom_inv_id_assoc, Iso.refl_hom,
      Category.comp_id]
  · simp only [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom,
      Scheme.baseRingToStructurePresheaf_app_eq_appLE, Iso.hom_inv_id_assoc, Iso.refl_hom,
      Category.comp_id]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp, Scheme.Hom.appLE_eq_app]
end AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.Scheme.Modules
variable {X Y : Scheme.{u}} (g : Y ⟶ X) (M : X.Modules) (U : X.Opens)
variable {Z : Scheme.{u}} (f : Z ⟶ Y)
variable (V : Y.Opens) (hV : V ≤ g ⁻¹ᵁ U)
private def pullbackSectionsLE : Γ(M, U) →ₛₗ[(g.appLE U V hV).hom] Γ((pullback g).obj M,V) where
  toFun s := ((pullback g).obj M).presheaf.map (homOfLE hV).op (Scheme.Hom.pullbackSections g M U s)
  map_add' := by simp
  map_smul' r s := by
    rw [map_smulₛₗ, map_smul]
    rfl
private lemma pullbackSectionsLE_apply (s : Γ(M, U)) :
    pullbackSectionsLE g M U V hV s =
      ((pullback g).obj M).presheaf.map (homOfLE hV).op (g.pullbackSections M U s) :=
  (rfl)
private lemma pullbackSectionsLE_self (s : Γ(M, U)) :
    pullbackSectionsLE g M U (g ⁻¹ᵁ U) le_rfl s = Scheme.Hom.pullbackSections g M U s := by
  simp [pullbackSectionsLE]
private lemma pullbackSectionsLE_naturality {N : X.Modules} (φ : M ⟶ N) (s : Γ(M, U)) :
    ((pullback g).map φ).app V (pullbackSectionsLE g M U V hV s) =
      pullbackSectionsLE g N U V hV (φ.app U s) := by
  have hn := PresheafOfModules.naturality_apply ((pullback g).map φ).val
    (homOfLE hV).op (Scheme.Hom.pullbackSections g M U s)
  have hu := Scheme.Hom.pullbackSections_naturality g M U φ s
  exact hn.trans (congrArg (((pullback g).obj N).presheaf.map (homOfLE hV).op) hu)
private lemma pullbackSectionsLE_congr {g' : Y ⟶ X} (h : g = g') (s : Γ(M, U)) :
    ((pullbackCongr h).hom.app M).app V (pullbackSectionsLE g M U V hV s) =
      pullbackSectionsLE g' M U V (by simpa [← h] using hV) s := by
  subst h
  simp [pullbackCongr]
private lemma pullbackSectionsLE_comp {W : Z.Opens} (hW : W ≤ f ⁻¹ᵁ V) (s : Γ(M, U)) :
    ((pullbackComp f g).inv.app M).app W
      (pullbackSectionsLE (f ≫ g) M U W (hW.trans (Set.preimage_mono hV)) s) =
    pullbackSectionsLE f ((pullback g).obj M) V W hW
      (pullbackSectionsLE g M U V hV s) := by
  have h := Scheme.Hom.pullbackSections_comp g M U f s
  have hn := PresheafOfModules.naturality_apply ((pullbackComp f g).inv.app M).val
    (homOfLE (show W ≤ (f ≫ g) ⁻¹ᵁ U from hW.trans
      (Set.preimage_mono (show (V : Set Y) ⊆ (g ⁻¹ᵁ U : Set Y) from hV)))).op
    (Scheme.Hom.pullbackSections (f ≫ g) M U s)
  dsimp only [pullbackSectionsLE, LinearMap.coe_mk, AddHom.coe_mk]
  -- The naturality equation uses the ModuleCat components before forgetting to groups.
  erw [hn]
  erw [h]
  have hr := Scheme.Hom.pullbackSections_restrict f ((pullback g).obj M) (g ⁻¹ᵁ U)
    (homOfLE hV) (Scheme.Hom.pullbackSections g M U s)
  rw [← hr, ← ((pullback f).obj ((pullback g).obj M)).presheaf.map_comp_apply]
  rfl
private lemma pullbackSectionsLE_comp_hom {W : Z.Opens} (hW : W ≤ f ⁻¹ᵁ V)
    (s : Γ(M, U)) :
    ((pullbackComp f g).hom.app M).app W
      (pullbackSectionsLE f ((pullback g).obj M) V W hW
        (pullbackSectionsLE g M U V hV s)) =
    pullbackSectionsLE (f ≫ g) M U W
      (hW.trans (Set.preimage_mono (show (V : Set Y) ⊆ (g ⁻¹ᵁ U : Set Y) from hV))) s := by
  rw [← pullbackSectionsLE_comp g M U f V hV hW]
  simpa only [Iso.app_hom, Iso.app_inv, Hom.comp_app, Hom.id_app, ConcreteCategory.comp_apply,
    ConcreteCategory.id_apply] using congrArg
    (fun a : (pullback (f ≫ g)).obj M ⟶ (pullback (f ≫ g)).obj M ↦ a.app W
      (pullbackSectionsLE (f ≫ g) M U W _ s)) ((pullbackComp f g).app M).inv_hom_id
end AlgebraicGeometry.Scheme.Modules
namespace AlgebraicGeometry.Scheme.Modules
variable {X : Scheme.{u}} (M : X.Modules) {U : X.Opens} (hU : IsAffineOpen U)
private lemma chartPullback_unit (s : Γ(M, U)) :
    ((restrictFunctorIsoPullback hU.fromSpec).hom.app M).app ⊤
      (M.fromSpecSectionsEquiv hU s) =
    pullbackSectionsLE hU.fromSpec M U ⊤ (hU.fromSpec_preimage_self.ge) s := by
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
    _ = pullbackSectionsLE hU.fromSpec M U ⊤ (hU.fromSpec_preimage_self.ge) s :=
      congrArg (((pullback hU.fromSpec).obj M).presheaf.map
        (homOfLE (hU.fromSpec_preimage_self.ge)).op) he'
private lemma chartPullback_unit_inv (s : Γ(M, U)) :
    ((restrictFunctorIsoPullback hU.fromSpec).inv.app M).app ⊤
      (pullbackSectionsLE hU.fromSpec M U ⊤ (hU.fromSpec_preimage_self.ge) s) =
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
      pullbackSectionsLE (Spec.map (g.app U)) (M.restrict hU.fromSpec)
        ⊤ ⊤ (by simp) (M.fromSpecSectionsEquiv hU s) := by
  simp only [chartPullbackIso, Iso.trans_hom, Iso.symm_hom, Hom.comp_app,
    ConcreteCategory.comp_apply, Functor.mapIso_hom, Iso.app_hom, Iso.app_inv]
  rw [chartPullback_unit]
  rw [← pullbackSectionsLE_self g M U s]
  rw [pullbackSectionsLE_comp_hom]
  rw [pullbackSectionsLE_congr]
  rw [pullbackSectionsLE_comp]
  · rw [pullbackSectionsLE_naturality, chartPullback_unit_inv]
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
  erw [pullbackSectionsLE_apply]
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
namespace AlgebraicGeometry.Scheme.Modules
section BaseScalars
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  {X Y : Scheme.{u}} [X.Over (Spec (.of R))] [Y.Over (Spec (.of S))]
  (g : Y ⟶ X) (U : X.Opens)
private lemma baseRingTower
    (C : CommSq g (Y ↘ Spec (.of S)) (X ↘ Spec (.of R))
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))) :
    letI : Algebra R Γ(X, U) :=
      ((X.baseRingToStructurePresheaf R).app (op U)).hom.toAlgebra
    letI : Algebra S Γ(Y, g ⁻¹ᵁ U) :=
      ((Y.baseRingToStructurePresheaf S).app (op (g ⁻¹ᵁ U))).hom.toAlgebra
    letI : Algebra R Γ(Y, g ⁻¹ᵁ U) :=
      ((g.app U).hom.comp (algebraMap R Γ(X, U))).toAlgebra
    IsScalarTower R S Γ(Y, g ⁻¹ᵁ U) := by
  let : Algebra R Γ(X, U) :=
    ((X.baseRingToStructurePresheaf R).app (op U)).hom.toAlgebra
  let : Algebra S Γ(Y, g ⁻¹ᵁ U) :=
    ((Y.baseRingToStructurePresheaf S).app (op (g ⁻¹ᵁ U))).hom.toAlgebra
  let : Algebra R Γ(Y, g ⁻¹ᵁ U) :=
    ((g.app U).hom.comp (algebraMap R Γ(X, U))).toAlgebra
  refine IsScalarTower.of_algebraMap_eq' (RingHom.ext fun r ↦ ?_)
  let : Y.Over (Spec (.of R)) :=
    ⟨(Y ↘ Spec (.of S)) ≫ Spec.map (CommRingCat.ofHom (algebraMap R S))⟩
  have : g.IsOver (Spec (.of R)) := ⟨C.w⟩
  exact (app_baseRingToStructurePresheaf R g U r).trans
    (Y.baseRingToStructurePresheaf_app_algebraMap
      (R := R) (S := S) rfl (g ⁻¹ᵁ U) r).symm
end BaseScalars
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
  have := Scheme.Modules.baseRingTower g U C
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
  have := Scheme.Modules.baseRingTower g U H.toCommSq
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
