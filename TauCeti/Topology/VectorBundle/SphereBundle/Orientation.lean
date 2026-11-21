/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Orientation.LocalSystem
public import TauCeti.Topology.VectorBundle.SphereBundle.LocallyTrivial

/-!
# The orientation local system of a line bundle and its unit sphere bundle

Let `E → B` be a real vector bundle of rank one. A unit vector `v` orients its fibre, and `-v`
gives the opposite orientation, so the unit sphere bundle `S(E)` maps to the orientation double
cover as a map of double covers over `B`, intertwining the negation `v ↦ -v` with the deck
involution (`TauCeti.sphereBundleOrientation`). When the fibre norm is continuous on the total
space, `S(E) → B` is a double cover (`TauCeti.isCoveringMap_sphereBundleProj`), and precomposition
with this map identifies the orientation local system `o(E)`
(`TauCeti.VectorBundleOrientationCover.signLocalSystem`) with the sign local system of the
involution `v ↦ -v` of `S(E)` (`TauCeti.signLocalSystemIsoSphereBundle`).

## Main results

* `TauCeti.sphereBundleOrientation`: the orientation map `S(E) → ` orientation double cover of a
  line bundle.
* `TauCeti.signLocalSystemIsoSphereBundle`: the orientation local system of a line bundle is the
  sign local system of its unit sphere bundle.

## References

* A. Hatcher, *Algebraic Topology*, Section 3.H (local coefficients and the local system of a
  covering space).
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §12 (the orientation double cover).
-/

public section

noncomputable section

open Bundle CategoryTheory

universe u

namespace TauCeti

variable {B : Type u} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type u} [∀ b, NormedAddCommGroup (E b)] [∀ b, NormedSpace ℝ (E b)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]
  (hnorm : Continuous fun v : TotalSpace F E ↦ ‖v.snd‖) (hF : Module.finrank ℝ F = 1)

/-- In rank one a unit vector `v` orients its fibre: the map from the unit sphere bundle to the
orientation double cover sending `v` to the orientation of its fibre in which `v` is positive.
It lies over the base and carries `-v` to the opposite orientation
(`TauCeti.sphereBundleOrientation_sphereBundleNeg`). -/
def sphereBundleOrientation : C(sphereBundle F E, VectorBundleOrientationCover F E (Fin 1)) where
  toFun v := ⟨(v : TotalSpace F E).proj,
    (FiniteDimensional.basisSingleton (Fin 1) ((VectorBundle.finrank_eq ℝ F E _).trans hF)
      (v : TotalSpace F E).snd
      (snd_ne_zero_of_mem_sphereBundle v.property)).orientation⟩
  continuous_toFun :=
    VectorBundleOrientationCover.continuous_mk_basis_orientation
      ((FiberBundle.continuous_proj F E).comp continuous_subtypeVal) _ fun i ↦ by
        simp only [FiniteDimensional.basisSingleton_apply]
        exact continuous_subtypeVal

/-- The orientation map sends a unit vector `v` over `b` to the orientation of `E_b` given by the
basis `(v)`. -/
theorem sphereBundleOrientation_apply (v : sphereBundle F E) :
    sphereBundleOrientation hF v = ⟨(v : TotalSpace F E).proj,
      (FiniteDimensional.basisSingleton (Fin 1) ((VectorBundle.finrank_eq ℝ F E _).trans hF)
        (v : TotalSpace F E).snd
        (snd_ne_zero_of_mem_sphereBundle v.property)).orientation⟩ :=
  (rfl)

/-- The orientation given by a unit vector lies over the base point of the vector. -/
@[simp]
theorem proj_sphereBundleOrientation (v : sphereBundle F E) :
    (sphereBundleOrientation hF v).proj = (v : TotalSpace F E).proj :=
  (rfl)

/-- The orientation map of the unit sphere bundle lies over the base. -/
theorem proj_comp_sphereBundleOrientation :
    VectorBundleOrientationCover.proj ∘ ⇑(sphereBundleOrientation hF) = ⇑(sphereBundleProj F E) :=
  funext fun v ↦ (sphereBundleProj_apply F E v).symm

/-- The opposite unit vector gives the opposite orientation. -/
@[simp]
theorem sphereBundleOrientation_sphereBundleNeg (v : sphereBundle F E) :
    sphereBundleOrientation hF (sphereBundleNeg F E v) =
      VectorBundleOrientationCover.deck (sphereBundleOrientation hF v) := by
  obtain ⟨⟨b, x⟩, hx⟩ := v
  have hneg : sphereBundleNeg F E ⟨⟨b, x⟩, hx⟩ =
      ⟨⟨b, -x⟩, mem_sphereBundle.2 ((norm_neg x).trans (mem_sphereBundle.1 hx))⟩ :=
    Subtype.ext (coe_sphereBundleNeg_apply F E _)
  rw [hneg, VectorBundleOrientationCover.deck_apply, sphereBundleOrientation_apply,
    sphereBundleOrientation_apply]
  refine VectorBundleOrientationCover.mk_eq_mk_iff.2 ?_
  -- The basis `(-x)` is the basis `(x)` with its vector multiplied by the unit `-1`.
  convert Module.Basis.orientation_neg_single (FiniteDimensional.basisSingleton (Fin 1)
    ((VectorBundle.finrank_eq ℝ F E _).trans hF) x
    (snd_ne_zero_of_mem_sphereBundle hx)) 0 using 2
  refine Module.Basis.eq_of_apply_eq fun i ↦ ?_
  rw [Module.Basis.unitsSMul_apply, Fin.fin_one_eq_zero i, Function.update_self]
  simp [FiniteDimensional.basisSingleton_apply]

variable (R : Type u) [Ring R]

/-- **The orientation local system of a line bundle is the sign local system of its unit sphere
bundle.** For a real vector bundle of rank one whose fibre norm is continuous on the total space,
the orientation map of the unit sphere bundle `S(E)` (`TauCeti.sphereBundleOrientation`) is a map
of double covers over the base, so precomposition with it identifies the orientation local system
`o(E)` with the sign local system of the deck involution `v ↦ -v` of `S(E)`. -/
def signLocalSystemIsoSphereBundle :
    VectorBundleOrientationCover.signLocalSystem F E R ((Fintype.card_fin 1).trans hF.symm) ≅
      (isCoveringMap_sphereBundleProj F E hnorm hF).signLocalSystem
        (X := TopCat.of B) R (sphereBundleNeg F E) (sphereBundleProj_comp_sphereBundleNeg F E) :=
  haveI : Nontrivial F := Module.nontrivial_of_finrank_eq_succ hF
  eqToIso (VectorBundleOrientationCover.signLocalSystem_def _) ≪≫
    IsCoveringMap.signLocalSystemIsoOfMap (R := R) (X := TopCat.of B)
      (σ := sphereBundleNeg F E) (hσ := sphereBundleProj_comp_sphereBundleNeg F E)
      (isCoveringMap_sphereBundleProj F E hnorm hF)
      (VectorBundleOrientationCover.isCoveringMap_proj ((Fintype.card_fin 1).trans hF.symm))
      (proj_comp_sphereBundleOrientation hF) (funext (sphereBundleOrientation_sphereBundleNeg hF))
      VectorBundleOrientationCover.deck_ne_self
      (fun _ _ h ↦ eq_or_eq_sphereBundleNeg_of_sphereBundleProj_eq hF h)
      (fun _ _ h ↦
        VectorBundleOrientationCover.eq_or_eq_deck ((Fintype.card_fin 1).trans hF.symm) h)
      (sphereBundleProj_surjective F E)

/-- The identification of the orientation local system of a line bundle with the sign local system
of its unit sphere bundle is precomposition with the orientation map. -/
@[simp]
theorem signLocalSystemObjEquiv_signLocalSystemIsoSphereBundle_hom_app_apply
    (x : FundamentalGroupoid (TopCat.of B))
    (g : (VectorBundleOrientationCover.signLocalSystem F E R
      ((Fintype.card_fin 1).trans hF.symm)).obj x) (e : sphereBundleProj F E ⁻¹' {x.as}) :
    ((isCoveringMap_sphereBundleProj F E hnorm hF).signLocalSystemObjEquiv (X := TopCat.of B)
        (sphereBundleNeg F E) (sphereBundleProj_comp_sphereBundleNeg F E) x
        ((signLocalSystemIsoSphereBundle hnorm hF R).hom.app x g) :
        sphereBundleProj F E ⁻¹' {x.as} → R) e =
      (VectorBundleOrientationCover.signLocalSystemObjEquiv ((Fintype.card_fin 1).trans hF.symm)
          x g : VectorBundleOrientationCover.proj ⁻¹' {x.as} → R)
        (Function.fiberMap (sphereBundleOrientation hF) (proj_comp_sphereBundleOrientation hF) x.as
          e) := by
  have : Nontrivial F := Module.nontrivial_of_finrank_eq_succ hF
  rw [signLocalSystemIsoSphereBundle, Iso.trans_hom, NatTrans.comp_app, ModuleCat.comp_apply,
    IsCoveringMap.signLocalSystemObjEquiv_signLocalSystemIsoOfMap_hom_app_apply,
    VectorBundleOrientationCover.signLocalSystemObjEquiv_eqToIso_signLocalSystem_def_hom_app]

/-- The inverse identification of the sign local system of the unit sphere bundle with the
orientation local system takes, at the orientation given by a unit vector `e`, the value at `e`. -/
@[simp]
theorem signLocalSystemObjEquiv_signLocalSystemIsoSphereBundle_inv_app_apply_fiberMap
    (x : FundamentalGroupoid (TopCat.of B))
    (g : ((isCoveringMap_sphereBundleProj F E hnorm hF).signLocalSystem (X := TopCat.of B) R
      (sphereBundleNeg F E) (sphereBundleProj_comp_sphereBundleNeg F E)).obj x)
    (e : sphereBundleProj F E ⁻¹' {x.as}) :
    (VectorBundleOrientationCover.signLocalSystemObjEquiv ((Fintype.card_fin 1).trans hF.symm) x
        ((signLocalSystemIsoSphereBundle hnorm hF R).inv.app x g) :
        VectorBundleOrientationCover.proj ⁻¹' {x.as} → R)
        (Function.fiberMap (sphereBundleOrientation hF) (proj_comp_sphereBundleOrientation hF) x.as
          e) =
      ((isCoveringMap_sphereBundleProj F E hnorm hF).signLocalSystemObjEquiv (X := TopCat.of B)
        (sphereBundleNeg F E) (sphereBundleProj_comp_sphereBundleNeg F E) x g :
        sphereBundleProj F E ⁻¹' {x.as} → R) e := by
  have : Nontrivial F := Module.nontrivial_of_finrank_eq_succ hF
  rw [signLocalSystemIsoSphereBundle, Iso.trans_inv, NatTrans.comp_app, ModuleCat.comp_apply,
    VectorBundleOrientationCover.signLocalSystemObjEquiv_eqToIso_signLocalSystem_def_inv_app]
  exact IsCoveringMap.signLocalSystemObjEquiv_signLocalSystemIsoOfMap_inv_app_apply_fiberMap _ _ _ _
    _ _ _ _ x g e


end TauCeti
