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
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import TauCeti.AlgebraicGeometry.AffineScheme
import TauCeti.RingTheory.Flat.IsBaseChange
import TauCeti.RingTheory.TensorProduct.IsBaseChange
import TauCeti.Algebra.Category.ModuleCat.ChangeOfRings
/-!
# Base change of quasicoherent sections

For a morphism of schemes, if an open and its inverse image are affine, sections of the
pullback of a quasicoherent sheaf are obtained by extending scalars along the coordinate-ring
map. The isomorphism is characterized by sending `1 ⊗ s` to the pullback of `s`. In particular,
if a single section generates the sections over the affine open, its pullback generates the
sections of the pullback over the inverse image.

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

The same holds over affine opens of the bases of an arbitrary cartesian square
`g' ≫ f = f' ≫ g`: for affine opens `W` of `S` and `W' ⊆ g⁻¹ W` of `S'`, an open `UX ⊆ f⁻¹ W` and
`UY = g'⁻¹ UX ∩ f'⁻¹ W'`, pulling back sections exhibits `Γ(UY, g'^* M)` as
`Γ(S', W') ⊗[Γ(S, W)] Γ(UX, M)`, for affine `UX` (`isBaseChange_pullbackSectionsLEBaseLinear`)
or for quasi-compact quasi-separated `UX` and flat `g`
(`isBaseChange_pullbackSectionsLEBaseLinear_of_isQuasiSeparated`). The square
restricts to a cartesian square `UY ⟶ UX` over `W' ⟶ W ≅ Spec Γ(S, W)`
(Mathlib's `AlgebraicGeometry.Scheme.Hom.isPullback_resLE`), which reduces these to the global
statements.

## Main results

* `AlgebraicGeometry.Scheme.Hom.span_singleton_pullbackSections_eq_top`: over affine opens, the
  pullback of a generator of the sections generates the sections of the pullback.
* `AlgebraicGeometry.Scheme.Hom.isBaseChange_pullbackSections`: base change of sections over an
  affine open, along any base-ring map.
* `AlgebraicGeometry.Scheme.Hom.flat_sectionsBase_pullback`: flatness of the sections over an
  affine open survives every base change.
* `AlgebraicGeometry.Scheme.Hom.liftBaseChange_pullbackSectionsBaseLinear_injective`: for flat
  `R → S`, the comparison `S ⊗[R] Γ(U, M) → Γ(g⁻¹ U, g^* M)` is injective over a quasi-compact
  open `U`.
* `AlgebraicGeometry.Scheme.Hom.isBaseChange_pullbackSections_of_isQuasiSeparated`: for flat
  `R → S`, it is bijective over a quasi-compact quasi-separated open `U`.
* `AlgebraicGeometry.Scheme.Hom.pullbackSectionsLEBaseLinear`: in a commutative square, pullback of
  sections from an open over `W ⊆ S` to an open over `W' ⊆ g⁻¹ W`, linear over `Γ(S, W)`.
* `AlgebraicGeometry.Scheme.Hom.isBaseChange_pullbackSectionsLEBaseLinear` and
  `AlgebraicGeometry.Scheme.Hom.isBaseChange_pullbackSectionsLEBaseLinear_of_isQuasiSeparated`:
  in a cartesian square, it is a base change from `Γ(S, W)` to `Γ(S', W')` for affine `W`, `W'`,
  when the open of `X` is affine, or quasi-compact quasi-separated and `g` is flat.

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
include hU hV in
/-- If a single section `m₀` generates `Γ(U, M)` over `Γ(X, U)`, then its pullback generates
`Γ(g⁻¹ U, g^* M)` over `Γ(Y, g⁻¹ U)`, when `U` and `g⁻¹ U` are affine. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.span_singleton_pullbackSections_eq_top
    {m₀ : Γ(M, U)} (h : Submodule.span Γ(X, U) {m₀} = ⊤) :
    Submodule.span Γ(Y, g ⁻¹ᵁ U) {g.pullbackSections M U m₀} = ⊤ := by
  -- The extension of scalars of the cyclic module `Γ(U, M)` is generated by `1 ⊗ m₀`.
  refine eq_top_iff.mpr fun x _ ↦ Submodule.mem_span_singleton.mpr ?_
  obtain ⟨y, rfl⟩ := (g.pullbackSectionsEquiv M hU hV).surjective x
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp
    ((ModuleCat.ExtendScalars.span_singleton_one_tmul_eq_top (g.app U).hom
      (M := .of Γ(X, U) Γ(M, U)) h).ge (Submodule.mem_top (x := y)))
  exact ⟨b, (((g.pullbackSectionsEquiv M hU hV).map_smul b _).trans
    (congrArg (b • ·) (g.pullbackSectionsEquiv_one_tmul M hU hV m₀))).symm⟩
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
/-- **Flat sections stay flat after base change.** If the sections of a quasi-coherent sheaf `M`
over an affine open `U` of `X` form a flat `R`-module, then for every base change `Y = X ×_R S`
along a ring map `R → S`, the sections of the pullback `g^* M` over `g⁻¹ U` form a flat
`S`-module, being the base change `S ⊗_R Γ(M, U)`. -/
theorem flat_sectionsBase_pullback [M.IsQuasicoherent]
    (H : IsPullback g (Y ↘ Spec (.of S)) (X ↘ Spec (.of R))
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))) (hU : IsAffineOpen U)
    [Module.Flat R (((sectionsBasePresheafFunctor R).obj M).obj (op U))] :
    Module.Flat S (((sectionsBasePresheafFunctor S).obj ((pullback g).obj M)).obj
      (op (g ⁻¹ᵁ U))) := by
  -- The actions of `R` on sections over `U`, and of `S` and `R` on sections over `g⁻¹ U`, as in
  -- `isBaseChange_pullbackSections`.
  let : Algebra R Γ(X, U) := ((X.baseRingToStructurePresheaf R).app (op U)).hom.toAlgebra
  let : Module R Γ(M, U) := sectionsBaseModule R M U
  have : IsScalarTower R Γ(X, U) Γ(M, U) := .of_algebraMap_smul fun _ _ ↦ rfl
  let : Algebra S Γ(Y, g ⁻¹ᵁ U) :=
    ((Y.baseRingToStructurePresheaf S).app (op (g ⁻¹ᵁ U))).hom.toAlgebra
  let : Module S Γ((pullback g).obj M, g ⁻¹ᵁ U) :=
    sectionsBaseModule S ((pullback g).obj M) (g ⁻¹ᵁ U)
  have : IsScalarTower S Γ(Y, g ⁻¹ᵁ U) Γ((pullback g).obj M, g ⁻¹ᵁ U) :=
    .of_algebraMap_smul fun _ _ ↦ rfl
  let : Module R Γ((pullback g).obj M, g ⁻¹ᵁ U) := Module.compHom _ (algebraMap R S)
  have : IsScalarTower R S Γ((pullback g).obj M, g ⁻¹ᵁ U) := .of_algebraMap_smul fun _ _ ↦ rfl
  -- The object of `sectionsBasePresheafFunctor R` over `U` is `ModuleCat.of R Γ(M, U)` for the
  -- action `sectionsBaseModule R M U`, so its flatness is that of `Γ(M, U)` by definition; the
  -- same holds for the conclusion over `g⁻¹ U`.
  have : Module.Flat R Γ(M, U) :=
    ‹Module.Flat R (((sectionsBasePresheafFunctor R).obj M).obj (op U))›
  exact Module.Flat.of_linearEquiv (g.isBaseChange_pullbackSections M U H hU).equiv.symm
end AlgebraicGeometry.Scheme.Hom

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

namespace AlgebraicGeometry.Scheme.Hom

variable {X X' S S' : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S'} {g : S' ⟶ S}

/-- Pulling back sections along `g'` in a commutative square
`g' ≫ f = f' ≫ g` (with `g' : X' ⟶ X`, `f : X ⟶ S`, `f' : X' ⟶ S'`, `g : S' ⟶ S`), from an open
`UX` lying over an open `W` of `S` to an open `UY ⊆ g'⁻¹ UX` lying over an open `W' ⊆ g⁻¹ W` of
`S'`, as a map linear over `Γ(S, W)`. Here `Γ(S, W)` acts on `Γ(S', W')`, `Γ(X, UX)` and
`Γ(X', UY)` through `g.appLE`, `f.appLE` and `f'.appLE`; the module structures on the sections are
caller parameters compatible with these. -/
def pullbackSectionsLEBaseLinear (g' : X' ⟶ X) (M : X.Modules) (w : CommSq g' f' f g)
    {W : S.Opens} {W' : S'.Opens} (h : W' ≤ g ⁻¹ᵁ W) {UX : X.Opens} (eX : UX ≤ f ⁻¹ᵁ W)
    {UY : X'.Opens} (eY : UY ≤ g' ⁻¹ᵁ UX) (eY' : UY ≤ f' ⁻¹ᵁ W') :
    letI : Algebra Γ(S, W) Γ(S', W') := (g.appLE W W' h).hom.toAlgebra
    letI : Algebra Γ(S, W) Γ(X, UX) := (f.appLE W UX eX).hom.toAlgebra
    letI : Algebra Γ(S', W') Γ(X', UY) := (f'.appLE W' UY eY').hom.toAlgebra
    ∀ [Module Γ(S, W) Γ(M, UX)] [Module Γ(S', W') Γ((pullback g').obj M, UY)]
      [Module Γ(S, W) Γ((pullback g').obj M, UY)]
      [IsScalarTower Γ(S, W) Γ(X, UX) Γ(M, UX)]
      [IsScalarTower Γ(S', W') Γ(X', UY) Γ((pullback g').obj M, UY)]
      [IsScalarTower Γ(S, W) Γ(S', W') Γ((pullback g').obj M, UY)],
      Γ(M, UX) →ₗ[Γ(S, W)] Γ((pullback g').obj M, UY) := by
  letI : Algebra Γ(S, W) Γ(S', W') := (g.appLE W W' h).hom.toAlgebra
  letI : Algebra Γ(S, W) Γ(X, UX) := (f.appLE W UX eX).hom.toAlgebra
  letI : Algebra Γ(S', W') Γ(X', UY) := (f'.appLE W' UY eY').hom.toAlgebra
  intro _ _ _ _ _ _
  refine
    { toFun := g'.pullbackSectionsLE M UX UY eY
      map_add' := map_add _
      map_smul' r s := ?_ }
  -- Both ring maps `Γ(S, W) ⟶ Γ(X', UY)` are `appLE` of the common composite of the square.
  have hr : (g'.appLE UX UY eY) ((f.appLE W UX eX) r) =
      (f'.appLE W' UY eY') (g.appLE W W' h r) := by
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE,
      Scheme.Hom.appLE_comp_appLE]
    simp only [w.w]
  rw [← IsScalarTower.algebraMap_smul Γ(X, UX) r s, map_smulₛₗ, RingHom.id_apply,
    ← IsScalarTower.algebraMap_smul Γ(S', W') r (g'.pullbackSectionsLE M UX UY eY s),
    ← IsScalarTower.algebraMap_smul Γ(X', UY) (algebraMap Γ(S, W) Γ(S', W') r)]
  exact congrArg (· • g'.pullbackSectionsLE M UX UY eY s) hr

/-- The base-linear pullback of sections has the values of `Scheme.Hom.pullbackSectionsLE`. -/
@[simp]
lemma pullbackSectionsLEBaseLinear_apply (g' : X' ⟶ X) (M : X.Modules) (w : CommSq g' f' f g)
    {W : S.Opens} {W' : S'.Opens} (h : W' ≤ g ⁻¹ᵁ W) {UX : X.Opens} (eX : UX ≤ f ⁻¹ᵁ W)
    {UY : X'.Opens} (eY : UY ≤ g' ⁻¹ᵁ UX) (eY' : UY ≤ f' ⁻¹ᵁ W') :
    letI : Algebra Γ(S, W) Γ(S', W') := (g.appLE W W' h).hom.toAlgebra
    letI : Algebra Γ(S, W) Γ(X, UX) := (f.appLE W UX eX).hom.toAlgebra
    letI : Algebra Γ(S', W') Γ(X', UY) := (f'.appLE W' UY eY').hom.toAlgebra
    ∀ [Module Γ(S, W) Γ(M, UX)] [Module Γ(S', W') Γ((pullback g').obj M, UY)]
      [Module Γ(S, W) Γ((pullback g').obj M, UY)]
      [IsScalarTower Γ(S, W) Γ(X, UX) Γ(M, UX)]
      [IsScalarTower Γ(S', W') Γ(X', UY) Γ((pullback g').obj M, UY)]
      [IsScalarTower Γ(S, W) Γ(S', W') Γ((pullback g').obj M, UY)] (s : Γ(M, UX)),
      pullbackSectionsLEBaseLinear g' M w h eX eY eY' s = g'.pullbackSectionsLE M UX UY eY s := by
  intro _ _ _ _ _ _ s
  rfl

/-- Base change of sections over affine opens of the bases, either for an affine open `UX`, or for
a quasi-compact quasi-separated `UX` and flat `g`. The square restricts to a cartesian square of
open subschemes `UY ⟶ UX` over `W' ⟶ W`, that is over `Spec Γ(S', W') ⟶ Spec Γ(S, W)`, and pulling
back sections along the inclusions of `UX` and `UY` identifies the claim with the base change of
global sections there (`Scheme.Hom.isBaseChange_pullbackSections` and
`Scheme.Hom.isBaseChange_pullbackSections_of_isQuasiSeparated`). -/
private lemma isBaseChange_pullbackSectionsLEBaseLinear_aux (g' : X' ⟶ X) (M : X.Modules)
    [M.IsQuasicoherent] (H : IsPullback g' f' f g) {W : S.Opens} (hW : IsAffineOpen W)
    {W' : S'.Opens} (hW' : IsAffineOpen W') (h : W' ≤ g ⁻¹ᵁ W) {UX : X.Opens}
    (eX : UX ≤ f ⁻¹ᵁ W) (hUX : IsAffineOpen UX ∨
      (Flat g ∧ IsCompact (UX : Set X) ∧ IsQuasiSeparated (UX : Set X)))
    {UY : X'.Opens} (hUY : UY = g' ⁻¹ᵁ UX ⊓ f' ⁻¹ᵁ W') :
    letI : Algebra Γ(S, W) Γ(S', W') := (g.appLE W W' h).hom.toAlgebra
    letI : Algebra Γ(S, W) Γ(X, UX) := (f.appLE W UX eX).hom.toAlgebra
    letI : Algebra Γ(S', W') Γ(X', UY) :=
      (f'.appLE W' UY (hUY.le.trans inf_le_right)).hom.toAlgebra
    ∀ [Module Γ(S, W) Γ(M, UX)] [Module Γ(S', W') Γ((pullback g').obj M, UY)]
      [Module Γ(S, W) Γ((pullback g').obj M, UY)]
      [IsScalarTower Γ(S, W) Γ(X, UX) Γ(M, UX)]
      [IsScalarTower Γ(S', W') Γ(X', UY) Γ((pullback g').obj M, UY)]
      [IsScalarTower Γ(S, W) Γ(S', W') Γ((pullback g').obj M, UY)],
      IsBaseChange Γ(S', W') (pullbackSectionsLEBaseLinear g' M H.toCommSq h eX
        (hUY.le.trans inf_le_left) (hUY.le.trans inf_le_right)) := by
  have eY : UY ≤ g' ⁻¹ᵁ UX := hUY.le.trans inf_le_left
  have eY' : UY ≤ f' ⁻¹ᵁ W' := hUY.le.trans inf_le_right
  let : Algebra Γ(S, W) Γ(S', W') := (g.appLE W W' h).hom.toAlgebra
  let : Algebra Γ(S, W) Γ(X, UX) := (f.appLE W UX eX).hom.toAlgebra
  let : Algebra Γ(S', W') Γ(X', UY) := (f'.appLE W' UY eY').hom.toAlgebra
  intro _ _ _ _ _ _
  -- Outline: restrict the square to the open subschemes `UY ⟶ UX` over `W' ⟶ W`, a cartesian
  -- square over `Spec Γ(S', W') ⟶ Spec Γ(S, W)`; apply the global base change theorem to the
  -- pullback `M₀` of `M` to `UX`; transport it along the identifications `eM` and `eN` of
  -- sections over `UX` and `UY` with global sections of the open subschemes.
  -- The restriction of the square to `UY ⟶ UX` over `W' ⟶ W`, as a square over
  -- `Spec Γ(S', W') ⟶ Spec Γ(S, W)`.
  let g₀ : UY.toScheme ⟶ UX.toScheme := g'.resLE UX UY eY
  let : UX.toScheme.Over (Spec (.of Γ(S, W))) := ⟨f.resLE W UX eX ≫ hW.isoSpec.hom⟩
  let : UY.toScheme.Over (Spec (.of Γ(S', W'))) := ⟨f'.resLE W' UY eY' ≫ hW'.isoSpec.hom⟩
  have H₀ : IsPullback g₀ (UY.toScheme ↘ Spec (.of Γ(S', W')))
      (UX.toScheme ↘ Spec (.of Γ(S, W)))
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, W) Γ(S', W')))) :=
    (Scheme.Hom.isPullback_resLE H h eX hUY).paste_vert
      (IsPullback.of_vert_isIso ⟨(Scheme.Opens.toSpecΓ_SpecMap_appLE g W W' h).symm⟩)
  -- The pullback of `M` to `UX` and the base change of its global sections.
  let R := Γ(S, W)
  let A := Γ(S', W')
  let M₀ := (pullback UX.ι).obj M
  let T := g₀ ⁻¹ᵁ ⊤
  let : Module R Γ(M₀, ⊤) := sectionsBaseModule R M₀ ⊤
  let : Algebra R Γ(UX.toScheme, ⊤) :=
    ((UX.toScheme.baseRingToStructurePresheaf R).app (op ⊤)).hom.toAlgebra
  have : IsScalarTower R Γ(UX.toScheme, ⊤) Γ(M₀, ⊤) := .of_algebraMap_smul fun _ _ ↦ rfl
  let : Module A Γ((pullback g₀).obj M₀, T) := sectionsBaseModule A ((pullback g₀).obj M₀) T
  let : Algebra A Γ(UY.toScheme, T) :=
    ((UY.toScheme.baseRingToStructurePresheaf A).app (op T)).hom.toAlgebra
  have : IsScalarTower A Γ(UY.toScheme, T) Γ((pullback g₀).obj M₀, T) :=
    .of_algebraMap_smul fun _ _ ↦ rfl
  let : Module R Γ((pullback g₀).obj M₀, T) := Module.compHom _ (algebraMap R A)
  have : IsScalarTower R A Γ((pullback g₀).obj M₀, T) := .of_algebraMap_smul fun _ _ ↦ rfl
  have key : IsBaseChange A (g₀.pullbackSectionsBaseLinear M₀ ⊤ H₀.toCommSq) := by
    rcases hUX with hUX | ⟨_, hUX, hUX'⟩
    · have : IsAffine UX := hUX
      exact g₀.isBaseChange_pullbackSections M₀ ⊤ H₀ (isAffineOpen_top _)
    · have : Module.Flat R A :=
        HasRingHomProperty.appLE @Flat g inferInstance ⟨W, hW⟩ ⟨W', hW'⟩ h
      have : CompactSpace UX := isCompact_iff_compactSpace.mp hUX
      have : QuasiSeparatedSpace UX :=
        (isQuasiSeparated_iff_quasiSeparatedSpace _ UX.isOpen).mp hUX'
      exact g₀.isBaseChange_pullbackSections_of_isQuasiSeparated M₀ H₀
        (by simpa using isCompact_univ (X := UX.toScheme))
        (by simpa using isQuasiSeparated_univ (α := UX.toScheme))
  -- The base rings act on functions on the open subschemes through `f.appLE` and `f'.appLE`
  -- followed by restriction.
  have hbase {Z B : Scheme.{u}} (k : Z ⟶ B) {V : B.Opens} (hV : IsAffineOpen V) (U : Z.Opens)
      (e : U ≤ k ⁻¹ᵁ V) (T : U.toScheme.Opens) :
      (Scheme.ΓSpecIso Γ(B, V)).inv ≫ (k.resLE V U e ≫ hV.isoSpec.hom).appLE ⊤ T le_top =
        k.appLE V U e ≫ U.ι.appLE U T (by simp) := by
    calc (Scheme.ΓSpecIso Γ(B, V)).inv ≫ (k.resLE V U e ≫ hV.isoSpec.hom).appLE ⊤ T le_top
        _ = (Scheme.ΓSpecIso Γ(B, V)).inv ≫
            (U.toSpecΓ ≫ Spec.map (k.appLE V U e)).appLE ⊤ T (by simp) := by
          simp only [IsAffineOpen.isoSpec_hom, ← Scheme.Opens.toSpecΓ_SpecMap_appLE]
        _ = (Scheme.ΓSpecIso Γ(B, V)).inv ≫ (Spec.map (k.appLE V U e)).appTop ≫
            U.toSpecΓ.appLE ⊤ T (by simp) :=
          congrArg _ (Scheme.Hom.comp_appLE _ _ _ _ _)
        _ = k.appLE V U e ≫ U.ι.appLE U T (by simp) := by
          rw [← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc,
            Scheme.Opens.ΓSpecIso_inv_comp_toSpecΓ_appLE]
  -- Pulling sections back to the open subschemes `UX` and `UY` identifies them with global
  -- sections there, linearly over the base rings.
  let eM : Γ(M, UX) ≃ₗ[R] Γ(M₀, ⊤) := LinearEquiv.ofBijective
    { toFun := UX.ι.pullbackSectionsLE M UX ⊤ (by simp)
      map_add' := map_add _
      map_smul' r m := by
        rw [← IsScalarTower.algebraMap_smul Γ(X, UX) r m, map_smulₛₗ, RingHom.id_apply,
          ← IsScalarTower.algebraMap_smul Γ(UX.toScheme, ⊤) r, RingHom.algebraMap_toAlgebra,
          RingHom.algebraMap_toAlgebra, Scheme.baseRingToStructurePresheaf_app_eq_appLE]
        exact congrArg (· • UX.ι.pullbackSectionsLE M UX ⊤ _ m) (congrArg (fun φ ↦ φ.hom r)
          (hbase f hW UX eX ⊤)).symm }
    (Scheme.Modules.bijective_pullbackSectionsLE_ι M UX ⊤ rfl)
  have hc : UY.ι ≫ g' = g₀ ≫ UX.ι := (g'.resLE_comp_ι eY).symm
  let e₀ : Γ((pullback g').obj M, UY) →+ Γ((pullback g₀).obj M₀, T) :=
    (((pullbackComp g₀ UX.ι).inv.app M).app T).hom.comp
      ((((pullbackCongr hc).hom.app M).app T).hom.comp
        ((((pullbackComp UY.ι g').hom.app M).app T).hom.comp
          (UY.ι.pullbackSectionsLE ((pullback g').obj M) UY T (by simp)).toAddMonoidHom))
  have he₀ : Function.Bijective e₀ :=
    (ConcreteCategory.bijective_of_isIso (((pullbackComp g₀ UX.ι).inv.app M).app T)).comp
      ((ConcreteCategory.bijective_of_isIso (((pullbackCongr hc).hom.app M).app T)).comp
        ((ConcreteCategory.bijective_of_isIso (((pullbackComp UY.ι g').hom.app M).app T)).comp
          (Scheme.Modules.bijective_pullbackSectionsLE_ι ((pullback g').obj M) UY T
            (Scheme.Hom.preimage_top _))))
  let eN : Γ((pullback g').obj M, UY) ≃ₗ[A] Γ((pullback g₀).obj M₀, T) := LinearEquiv.ofBijective
    { toFun := e₀
      map_add' := map_add e₀
      map_smul' a x := by
        simp only [e₀, AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe]
        rw [← IsScalarTower.algebraMap_smul Γ(X', UY) a x, map_smulₛₗ, Hom.app_smul, Hom.app_smul,
          Hom.app_smul, RingHom.id_apply, ← IsScalarTower.algebraMap_smul Γ(UY.toScheme, T) a,
          RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra,
          Scheme.baseRingToStructurePresheaf_app_eq_appLE]
        exact congrArg (· • _) (congrArg (fun φ ↦ φ.hom a)
          (hbase f' hW' UY eY' T)).symm }
    he₀
  refine (IsBaseChange.iff_of_equiv_comm eM eN (LinearMap.ext fun s ↦ ?_)).mpr key
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.restrictScalars_apply]
  rw [pullbackSectionsBaseLinear_apply, pullbackSectionsLEBaseLinear_apply]
  simp only [eM, eN, e₀, LinearEquiv.ofBijective_apply, LinearMap.coe_mk, AddHom.coe_mk,
    AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe]
  rw [Scheme.Hom.pullbackSectionsLE_comp_hom g' M UX UY.ι UY eY,
    Scheme.Hom.pullbackSectionsLE_congr _ M UX T _ hc,
    Scheme.Hom.pullbackSectionsLE_comp UX.ι M UX g₀ ⊤ (by simp) le_rfl,
    Scheme.Hom.pullbackSectionsLE_self]

/-- **Flat base change of sections over affine opens of the bases.** Let
`g' ≫ f = f' ≫ g` be a cartesian square with `g : S' ⟶ S` flat, and `M` a quasi-coherent sheaf on
`X`. For affine opens `W` of `S` and `W' ⊆ g⁻¹ W` of `S'`, a quasi-compact quasi-separated open
`UX ⊆ f⁻¹ W` of `X` and `UY = g'⁻¹ UX ∩ f'⁻¹ W'`, pulling back sections exhibits `Γ(UY, g'^* M)` as
the base change `Γ(S', W') ⊗[Γ(S, W)] Γ(UX, M)`. -/
theorem isBaseChange_pullbackSectionsLEBaseLinear_of_isQuasiSeparated (g' : X' ⟶ X)
    (M : X.Modules) [M.IsQuasicoherent] (H : IsPullback g' f' f g) [Flat g] {W : S.Opens}
    (hW : IsAffineOpen W) {W' : S'.Opens} (hW' : IsAffineOpen W') (h : W' ≤ g ⁻¹ᵁ W)
    {UX : X.Opens} (eX : UX ≤ f ⁻¹ᵁ W) (hUX : IsCompact (UX : Set X))
    (hUX' : IsQuasiSeparated (UX : Set X))
    {UY : X'.Opens} (hUY : UY = g' ⁻¹ᵁ UX ⊓ f' ⁻¹ᵁ W') :
    letI : Algebra Γ(S, W) Γ(S', W') := (g.appLE W W' h).hom.toAlgebra
    letI : Algebra Γ(S, W) Γ(X, UX) := (f.appLE W UX eX).hom.toAlgebra
    letI : Algebra Γ(S', W') Γ(X', UY) :=
      (f'.appLE W' UY (hUY.le.trans inf_le_right)).hom.toAlgebra
    ∀ [Module Γ(S, W) Γ(M, UX)] [Module Γ(S', W') Γ((pullback g').obj M, UY)]
      [Module Γ(S, W) Γ((pullback g').obj M, UY)]
      [IsScalarTower Γ(S, W) Γ(X, UX) Γ(M, UX)]
      [IsScalarTower Γ(S', W') Γ(X', UY) Γ((pullback g').obj M, UY)]
      [IsScalarTower Γ(S, W) Γ(S', W') Γ((pullback g').obj M, UY)],
      IsBaseChange Γ(S', W') (pullbackSectionsLEBaseLinear g' M H.toCommSq h eX
        (hUY.le.trans inf_le_left) (hUY.le.trans inf_le_right)) :=
  isBaseChange_pullbackSectionsLEBaseLinear_aux g' M H hW hW' h eX
    (.inr ⟨inferInstance, hUX, hUX'⟩) hUY

/-- **Base change of sections over affine opens.** Let `g' ≫ f = f' ≫ g` be a cartesian square
and `M` a quasi-coherent sheaf on `X`. For affine opens `W` of `S`, `W' ⊆ g⁻¹ W` of `S'` and
`UX ⊆ f⁻¹ W` of `X`, and `UY = g'⁻¹ UX ∩ f'⁻¹ W'`, pulling back sections exhibits `Γ(UY, g'^* M)`
as the base change `Γ(S', W') ⊗[Γ(S, W)] Γ(UX, M)`. No flatness is needed. -/
theorem isBaseChange_pullbackSectionsLEBaseLinear (g' : X' ⟶ X) (M : X.Modules)
    [M.IsQuasicoherent] (H : IsPullback g' f' f g) {W : S.Opens} (hW : IsAffineOpen W)
    {W' : S'.Opens} (hW' : IsAffineOpen W') (h : W' ≤ g ⁻¹ᵁ W) {UX : X.Opens}
    (eX : UX ≤ f ⁻¹ᵁ W) (hUX : IsAffineOpen UX) {UY : X'.Opens}
    (hUY : UY = g' ⁻¹ᵁ UX ⊓ f' ⁻¹ᵁ W') :
    letI : Algebra Γ(S, W) Γ(S', W') := (g.appLE W W' h).hom.toAlgebra
    letI : Algebra Γ(S, W) Γ(X, UX) := (f.appLE W UX eX).hom.toAlgebra
    letI : Algebra Γ(S', W') Γ(X', UY) :=
      (f'.appLE W' UY (hUY.le.trans inf_le_right)).hom.toAlgebra
    ∀ [Module Γ(S, W) Γ(M, UX)] [Module Γ(S', W') Γ((pullback g').obj M, UY)]
      [Module Γ(S, W) Γ((pullback g').obj M, UY)]
      [IsScalarTower Γ(S, W) Γ(X, UX) Γ(M, UX)]
      [IsScalarTower Γ(S', W') Γ(X', UY) Γ((pullback g').obj M, UY)]
      [IsScalarTower Γ(S, W) Γ(S', W') Γ((pullback g').obj M, UY)],
      IsBaseChange Γ(S', W') (pullbackSectionsLEBaseLinear g' M H.toCommSq h eX
        (hUY.le.trans inf_le_left) (hUY.le.trans inf_le_right)) :=
  isBaseChange_pullbackSectionsLEBaseLinear_aux g' M H hW hW' h eX (.inl hUX) hUY

end AlgebraicGeometry.Scheme.Hom
