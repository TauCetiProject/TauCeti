/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Jet.Nonlinear
public import TauCeti.Geometry.Manifold.FiberBundle.Vertical
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Topology.Algebra.Module.Equiv.Submodule

/-!
# The nonlinear first-jet bundle of a smooth fibre bundle

For a fibre bundle `π : E → B` over a manifold `B` (modelled on `IB`) with manifold fibre `F`
(modelled on `IF`), a 1-jet over `z : ManifoldTotalSpace F E` represents the first-order behaviour
at `π(z)` of local sections passing through `z`. Rather than quotienting `C^∞` local section germs
— which fixes regularity to `C^∞` and requires boundaryless base models for ordinary total
derivatives (`TauCeti.FirstJetAt`) — `TauCeti.FiberFirstJet IB IF F E z` models a 1-jet
intrinsically as a continuous linear right-inverse `j : T_{z.proj} B →L[𝕜] T_z E` of
`mfderiv proj z`. Every differentiable local section `s` with `s(x) = z` induces such a splitting
via `ds_x`. Locally, over any boundaryless fibre model `[IF.Boundaryless]` (with no boundaryless
assumption on `B` and no bump functions needed), every splitting is realized by a `C^n` local
section defined in a chart neighbourhood of `z`
(`FiberFirstJetBundle.exists_contMDiffAt_prolong_eq` in `FirstJet.Prolongation`); smooth bump
extensions would only be needed to extend such a local section globally across `B`.

Unlike a vector bundle, `J¹E → E` (`TotalSpace.proj`) has no coordinate-independent zero section:
local bundle transitions mix base and fibre coordinates, contributing an additive shear term to
local derivative coordinates (`coordChange_eq_firstJetCoordChange_snd`). Differences of two
splittings at `z`, however, have zero base differential and transform linearly through
`VerticalSpace.coordChange` (`coordChange_sub`), making `FiberFirstJet IB IF F E z` an affine
torsor over `T_{z.proj} B →L[𝕜] V_z E`.

Assembling local derivative coordinates (`coordAt`, `ofCoordAt`) via `fiberPrebundle` equips
`TauCeti.FiberFirstJetBundle IB IF F E` (`J¹E`) with a `C^n` fibre bundle and `C^n` manifold
structure for `C^(n + 1)` bundle data (`contMDiffFiberBundle`, `isManifold`). At each `p : J¹E`,
`FiberFirstJetBundle.contactFormAt p` is the pointwise Cartan contact map
`T_p(J¹E) →L[𝕜] V_{p.proj} E` projecting target differentials onto the vertical space along `p.2`.

## Main definitions and results

* `TauCeti.FiberFirstJet`: continuous linear right-inverses of `mfderiv proj z`, with
  `ContinuousLinearMapClass` instance, preferred-chart coordinates `modelEquivAt` /
  `modelHomeomorphAt`, affine torsor structure over `T_{z.proj} B →L[𝕜] V_z E`, vertical contact
  projection `contactProj` (`ker_contactProj`), and tangent splitting `splittingEquiv`.
* `TauCeti.FiberFirstJet.coordAt`, `ofCoordAt`, and `coordChange`: local derivative coordinates and
  their affine transition law (`coordChange_sub`, `coordChange_self`, `coordChange_comp`,
  `coordChange_eq_firstJetCoordChange_snd`, `contMDiffOn_coordChange`).
* `TauCeti.FiberFirstJet.fiberPrebundle` and `contMDiffFiberBundle`: topological and `C^n` fibre
  bundle structures on `TauCeti.FiberFirstJetBundle IB IF F E`.
* `TauCeti.FiberFirstJetBundle.baseProj`, `isManifold`, and `contactFormAt`: source (base)
  projection, `C^n` manifold structure on `J¹E`, and the pointwise Cartan contact map.

## References

* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer,
  1993, §12.
* D. J. Saunders, *The Geometry of Jet Bundles*, Cambridge University Press, 1989, §§4.1–4.2.
* I. M. Anderson, *The Variational Bicomplex*, Utah State University, 1992, Chapter 1, §A.
* Local nonlinear jet transition formulas build on `TauCeti.Analysis.Calculus.Jet.Nonlinear`
  (`TauCeti.firstJetCoordChange`) and `TauCeti.Geometry.Manifold.FiberBundle.Vertical`.
-/

public section
noncomputable section

open Bundle Set Filter ContinuousLinearMap
open scoped Manifold Topology ContDiff

namespace TauCeti
section ManifoldFiber

variable {𝕜 B : Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  {EF : Type*} [NormedAddCommGroup EF] [NormedSpace 𝕜 EF] {HF : Type*} [TopologicalSpace HF]
  {IF : ModelWithCorners 𝕜 EF HF} {F : Type*} [TopologicalSpace F] [ChartedSpace HF F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)]
  [FiberBundle F E]

variable (IB IF F E) in
/-- A **first jet** of `E` at `z : ManifoldTotalSpace F E`: a continuous linear right-inverse
`TangentSpace IB z.proj →L[𝕜] TangentSpace (IB.prod IF) z` of `mfderiv proj z`. -/
structure FiberFirstJet (z : ManifoldTotalSpace F E) where
  /-- The underlying continuous linear splitting `T_{z.proj} B →L[𝕜] T_z E`. -/
  toContinuousLinearMap : TangentSpace IB z.proj →L[𝕜] TangentSpace (IB.prod IF) z
  /-- A first jet splits `mfderiv proj z` on the right. -/
  mfderiv_proj_comp :
    (mfderiv (IB.prod IF) IB (ManifoldTotalSpace.proj : ManifoldTotalSpace F E → B) z).comp
      toContinuousLinearMap = ContinuousLinearMap.id 𝕜 (TangentSpace IB z.proj)

namespace FiberFirstJet
section Carrier
variable {z : ManifoldTotalSpace F E}

instance : FunLike (FiberFirstJet IB IF F E z) (TangentSpace IB z.proj)
    (TangentSpace (IB.prod IF) z) where
  coe j := j.toContinuousLinearMap
  coe_injective := by rintro ⟨_, _⟩ ⟨_, _⟩ h; congr; exact DFunLike.coe_injective h

instance : ContinuousLinearMapClass (FiberFirstJet IB IF F E z) 𝕜 (TangentSpace IB z.proj)
    (TangentSpace (IB.prod IF) z) where
  map_add j := map_add j.toContinuousLinearMap
  map_smulₛₗ j := j.toContinuousLinearMap.map_smul'
  map_continuous j := j.toContinuousLinearMap.cont

@[simp]
theorem toContinuousLinearMap_apply (j : FiberFirstJet IB IF F E z)
    (u : TangentSpace IB z.proj) : j.toContinuousLinearMap u = j u :=
  (rfl)

/-- Two first jets at `z` are equal iff they agree on every base tangent vector. -/
@[ext]
theorem ext {j₁ j₂ : FiberFirstJet IB IF F E z} (h : ∀ u, j₁ u = j₂ u) : j₁ = j₂ :=
  DFunLike.ext j₁ j₂ h

/-- Applying `mfderiv proj z` to `j u` recovers `u`. -/
@[simp]
theorem mfderiv_proj_apply (j : FiberFirstJet IB IF F E z) (u : TangentSpace IB z.proj) :
    mfderiv (IB.prod IF) IB ManifoldTotalSpace.proj z (j u) = u :=
  DFunLike.congr_fun j.mfderiv_proj_comp u

/-- Every first jet `j` at `z` is injective as a map of tangent spaces. -/
theorem injective (j : FiberFirstJet IB IF F E z) : Function.Injective j :=
  Function.LeftInverse.injective j.mfderiv_proj_apply

/-- In model coordinates at `z`, the first component of `j u` is the model coordinate of `u`. -/
@[simp]
theorem tangentSpaceCastModel_apply_fst (j : FiberFirstJet IB IF F E z)
    (u : TangentSpace IB z.proj) :
    (tangentSpaceCastModel (IB.prod IF) z (j u)).1 = tangentSpaceCastModel IB z.proj u := by
  rw [← ManifoldTotalSpace.tangentSpaceCastModel_mfderiv_proj, j.mfderiv_proj_apply]

private def ofModel (z : ManifoldTotalSpace F E) (A : EB →L[𝕜] EF) :
    FiberFirstJet IB IF F E z where
  toContinuousLinearMap := (tangentSpaceCastModel (IB.prod IF) z).symm.toContinuousLinearMap
    |>.comp (((ContinuousLinearMap.id 𝕜 EB).prod A).comp
      (tangentSpaceCastModel IB z.proj).toContinuousLinearMap)
  mfderiv_proj_comp := by
    ext u
    refine (EquivLike.apply_eq_iff_eq (tangentSpaceCastModel IB z.proj)).1 ?_
    rw [comp_apply, ManifoldTotalSpace.tangentSpaceCastModel_mfderiv_proj]
    simp

@[simp]
private theorem ofModel_apply (z : ManifoldTotalSpace F E) (A : EB →L[𝕜] EF)
    (u : TangentSpace IB z.proj) :
    ofModel (IB := IB) (IF := IF) (F := F) (E := E) z A u =
      (tangentSpaceCastModel (IB.prod IF) z).symm
        (tangentSpaceCastModel IB z.proj u, A (tangentSpaceCastModel IB z.proj u)) :=
  (rfl)

/-- Preferred-chart coordinate equivalence `FiberFirstJet IB IF F E z ≃ (EB →L[𝕜] EF)`. -/
def modelEquivAt (z : ManifoldTotalSpace F E) :
    FiberFirstJet IB IF F E z ≃ (EB →L[𝕜] EF) where
  toFun j := (ContinuousLinearMap.snd 𝕜 EB EF).comp
    ((tangentSpaceCastModel (IB.prod IF) z).toContinuousLinearMap.comp
      (j.toContinuousLinearMap.comp (tangentSpaceCastModel IB z.proj).symm.toContinuousLinearMap))
  invFun := ofModel z
  left_inv j := by
    ext u
    apply (tangentSpaceCastModel (IB.prod IF) z).injective
    dsimp only
    simp only [ofModel_apply, toContinuousLinearMap_apply, comp_apply, coe_snd',
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply,
      ContinuousLinearEquiv.symm_apply_apply]
    exact Prod.ext (j.tangentSpaceCastModel_apply_fst u).symm rfl
  right_inv A := by ext u; simp

@[simp]
theorem modelEquivAt_apply (z : ManifoldTotalSpace F E) (j : FiberFirstJet IB IF F E z)
    (u : EB) : modelEquivAt z j u =
      (tangentSpaceCastModel (IB.prod IF) z (j ((tangentSpaceCastModel IB z.proj).symm u))).2 :=
  (rfl)

/-- `(modelEquivAt z).symm A` acts in model coordinates at `z` as the graph map `u ↦ (u, A u)`. -/
@[simp]
theorem modelEquivAt_symm_apply (z : ManifoldTotalSpace F E) (A : EB →L[𝕜] EF)
    (u : TangentSpace IB z.proj) :
    (modelEquivAt (IB := IB) (IF := IF) (F := F) (E := E) z).symm A u =
      (tangentSpaceCastModel (IB.prod IF) z).symm
        (tangentSpaceCastModel IB z.proj u, A (tangentSpaceCastModel IB z.proj u)) :=
  (rfl)

/-- Every fibre `FiberFirstJet IB IF F E z` is nonempty, witnessed in preferred model coordinates
by `(modelEquivAt z).symm 0`. -/
instance : Nonempty (FiberFirstJet IB IF F E z) :=
  ⟨(modelEquivAt z).symm 0⟩

instance : TopologicalSpace (FiberFirstJet IB IF F E z) :=
  TopologicalSpace.induced FiberFirstJet.toContinuousLinearMap inferInstance

/-- Preferred-chart homeomorphism `FiberFirstJet IB IF F E z ≃ₜ (EB →L[𝕜] EF)`. -/
def modelHomeomorphAt (z : ManifoldTotalSpace F E) :
    FiberFirstJet IB IF F E z ≃ₜ (EB →L[𝕜] EF) where
  toEquiv := modelEquivAt z
  continuous_toFun :=
    (ContinuousLinearMap.postcomp EB ((ContinuousLinearMap.snd 𝕜 EB EF).comp
      (tangentSpaceCastModel (IB.prod IF) z).toContinuousLinearMap) :
      (EB →L[𝕜] TangentSpace (IB.prod IF) z) →L[𝕜] (EB →L[𝕜] EF)).continuous.comp
      ((ContinuousLinearMap.precomp (TangentSpace (IB.prod IF) z)
        (tangentSpaceCastModel IB z.proj).symm.toContinuousLinearMap :
        (TangentSpace IB z.proj →L[𝕜] TangentSpace (IB.prod IF) z) →L[𝕜]
          (EB →L[𝕜] TangentSpace (IB.prod IF) z)).continuous.comp continuous_induced_dom)
  continuous_invFun := by
    refine continuous_induced_rng.2 ?_
    have hprod : Continuous fun A : EB →L[𝕜] EF ↦ (ContinuousLinearMap.id 𝕜 EB).prod A :=
      (ContinuousLinearMap.prodₗᵢ 𝕜).continuous.comp (continuous_const.prodMk continuous_id)
    exact (ContinuousLinearMap.precomp (TangentSpace (IB.prod IF) z)
      (tangentSpaceCastModel IB z.proj).toContinuousLinearMap :
      (EB →L[𝕜] TangentSpace (IB.prod IF) z) →L[𝕜]
        (TangentSpace IB z.proj →L[𝕜] TangentSpace (IB.prod IF) z)).continuous.comp
      ((ContinuousLinearMap.postcomp EB
        (tangentSpaceCastModel (IB.prod IF) z).symm.toContinuousLinearMap :
        (EB →L[𝕜] EB × EF) →L[𝕜] (EB →L[𝕜] TangentSpace (IB.prod IF) z)).continuous.comp hprod)

@[simp]
theorem coe_modelHomeomorphAt (z : ManifoldTotalSpace F E) :
    (modelHomeomorphAt z : FiberFirstJet IB IF F E z → (EB →L[𝕜] EF)) = modelEquivAt z :=
  (rfl)

@[simp]
theorem coe_modelHomeomorphAt_symm (z : ManifoldTotalSpace F E) :
    ((modelHomeomorphAt (IB := IB) (IF := IF) (F := F) (E := E) z).symm :
      (EB →L[𝕜] EF) → FiberFirstJet IB IF F E z) = (modelEquivAt z).symm :=
  (rfl)

/-- Affine translation of a first jet `j` by a vertical-valued linear map
`φ : T_{z.proj} B →L[𝕜] V_z E`: adding a vertical vector leaves `mfderiv proj z` unchanged. -/
instance : VAdd (TangentSpace IB z.proj →L[𝕜] VerticalSpace IB IF F E z)
    (FiberFirstJet IB IF F E z) where
  vadd φ j :=
    { toContinuousLinearMap :=
        VerticalSpace.subtypeL.comp φ + j.toContinuousLinearMap
      mfderiv_proj_comp := by
        ext u
        simp [j.mfderiv_proj_apply] }

@[simp]
theorem vadd_apply (φ : TangentSpace IB z.proj →L[𝕜] VerticalSpace IB IF F E z)
    (j : FiberFirstJet IB IF F E z) (u : TangentSpace IB z.proj) :
    (φ +ᵥ j) u = (φ u : TangentSpace (IB.prod IF) z) + j u := by
  rw [← toContinuousLinearMap_apply]
  simp [HVAdd.hVAdd, VAdd.vadd, comp_apply]

/-- In preferred model coordinates at `z`, vertical translation `φ +ᵥ j` adds the vertical model
coordinate of `φ` to `modelEquivAt z j`. -/
@[simp]
theorem modelEquivAt_vadd (z : ManifoldTotalSpace F E)
    (φ : TangentSpace IB z.proj →L[𝕜] VerticalSpace IB IF F E z)
    (j : FiberFirstJet IB IF F E z) :
    modelEquivAt z (φ +ᵥ j) =
      (VerticalSpace.modelEquivAt z).toContinuousLinearMap.comp
        (φ.comp (tangentSpaceCastModel IB z.proj).symm.toContinuousLinearMap) +
        modelEquivAt z j := by
  ext u
  simp

/-- Affine difference `j₁ -ᵥ j₂ : T_{z.proj} B →L[𝕜] V_z E` of two first jets at `z`, corestricting
`j₁ - j₂` into `ker (mfderiv proj z)`. -/
instance : VSub (TangentSpace IB z.proj →L[𝕜] VerticalSpace IB IF F E z)
    (FiberFirstJet IB IF F E z) where
  vsub j₁ j₂ :=
    (VerticalSpace.equivSubmodule z).symm.toContinuousLinearMap.comp <|
      ContinuousLinearMap.codRestrict (j₁.toContinuousLinearMap - j₂.toContinuousLinearMap)
        (verticalSubmodule IB IF F E z)
        fun u ↦ mem_verticalSubmodule_iff.2 <| by
          simp [j₁.mfderiv_proj_apply, j₂.mfderiv_proj_apply]

@[simp]
theorem coe_vsub_apply (j₁ j₂ : FiberFirstJet IB IF F E z)
    (u : TangentSpace IB z.proj) :
    (((j₁ -ᵥ j₂) u : VerticalSpace IB IF F E z) : TangentSpace (IB.prod IF) z) = j₁ u - j₂ u := by
  simp [VSub.vsub, comp_apply]

/-- `FiberFirstJet IB IF F E z` is an `AddTorsor` over `T_{z.proj} B →L[𝕜] V_z E`. -/
instance : AddTorsor (TangentSpace IB z.proj →L[𝕜] VerticalSpace IB IF F E z)
    (FiberFirstJet IB IF F E z) where
  zero_vadd j := by ext u; simp
  add_vadd φ ψ j := by ext u; simp [add_assoc]
  vsub_vadd' j₁ j₂ := by ext u; simp [sub_add_cancel]
  vadd_vsub' φ j := by ext u; simp

/-- The **vertical contact projection** sending `w ∈ T_z E` to `w - j (dπ_z w) ∈ V_z E`,
implemented via `ContinuousLinearMap.projKerOfRightInverse`. -/
def contactProj (j : FiberFirstJet IB IF F E z) :
    TangentSpace (IB.prod IF) z →L[𝕜] VerticalSpace IB IF F E z :=
  (((ContinuousLinearEquiv.ofEq _ _ (verticalSubmodule_eq IB IF F E z).symm).trans
    (VerticalSpace.equivSubmodule z).symm).toContinuousLinearMap).comp
    ((mfderiv (IB.prod IF) IB (ManifoldTotalSpace.proj : ManifoldTotalSpace F E → B)
      z).projKerOfRightInverse j.toContinuousLinearMap j.mfderiv_proj_apply)

@[simp]
theorem coe_contactProj (j : FiberFirstJet IB IF F E z)
    (w : TangentSpace (IB.prod IF) z) :
    (j.contactProj w : TangentSpace (IB.prod IF) z) =
      w - j (mfderiv (IB.prod IF) IB ManifoldTotalSpace.proj z w) := by
  simp [contactProj, ContinuousLinearEquiv.ofEq]

@[simp]
theorem contactProj_coe (j : FiberFirstJet IB IF F E z)
    (v : VerticalSpace IB IF F E z) :
    j.contactProj (v : TangentSpace (IB.prod IF) z) = v := by
  apply VerticalSpace.ext
  rw [coe_contactProj, VerticalSpace.mfderiv_proj_coe, map_zero, sub_zero]

@[simp]
theorem contactProj_apply_self (j : FiberFirstJet IB IF F E z)
    (u : TangentSpace IB z.proj) : j.contactProj (j u) = 0 := by
  apply VerticalSpace.ext
  rw [coe_contactProj, j.mfderiv_proj_apply, sub_self, VerticalSpace.coe_zero]

/-- The kernel of the vertical contact projection `j.contactProj` is the horizontal subspace
`range j` spanned by the first jet `j`. -/
theorem ker_contactProj (j : FiberFirstJet IB IF F E z) :
    LinearMap.ker j.contactProj.toLinearMap =
      LinearMap.range j.toContinuousLinearMap.toLinearMap := by
  ext w
  simp only [LinearMap.mem_ker, LinearMap.mem_range, ContinuousLinearMap.coe_coe,
    toContinuousLinearMap_apply]
  refine ⟨fun hw ↦ ⟨mfderiv (IB.prod IF) IB ManifoldTotalSpace.proj z w, ?_⟩, ?_⟩
  · have h0 : (j.contactProj w : TangentSpace (IB.prod IF) z) = 0 := by
      rw [hw, VerticalSpace.coe_zero]
    rw [coe_contactProj, sub_eq_zero] at h0
    exact h0.symm
  · rintro ⟨u, rfl⟩
    exact j.contactProj_apply_self u

/-- Direct-sum splitting `T_z E ≃L[𝕜] T_{z.proj} B × V_z E` determined by a first jet `j`,
implemented via `ContinuousLinearEquiv.equivOfRightInverse`. -/
def splittingEquiv (j : FiberFirstJet IB IF F E z) :
    TangentSpace (IB.prod IF) z ≃L[𝕜] TangentSpace IB z.proj × VerticalSpace IB IF F E z :=
  (ContinuousLinearEquiv.equivOfRightInverse
    (mfderiv (IB.prod IF) IB (ManifoldTotalSpace.proj : ManifoldTotalSpace F E → B) z)
    j.toContinuousLinearMap j.mfderiv_proj_apply).trans
    ((ContinuousLinearEquiv.refl 𝕜 _).prodCongr
      ((ContinuousLinearEquiv.ofEq _ _ (verticalSubmodule_eq IB IF F E z).symm).trans
        (VerticalSpace.equivSubmodule z).symm))

@[simp]
theorem splittingEquiv_apply (j : FiberFirstJet IB IF F E z)
    (w : TangentSpace (IB.prod IF) z) : j.splittingEquiv w =
      (mfderiv (IB.prod IF) IB ManifoldTotalSpace.proj z w, j.contactProj w) := by
  ext <;> simp [splittingEquiv, ContinuousLinearEquiv.ofEq]

@[simp]
theorem splittingEquiv_symm_apply (j : FiberFirstJet IB IF F E z)
    (p : TangentSpace IB z.proj × VerticalSpace IB IF F E z) :
    j.splittingEquiv.symm p = j p.1 + (p.2 : TangentSpace (IB.prod IF) z) := by
  simp [splittingEquiv, ContinuousLinearEquiv.ofEq, ← ContinuousLinearEquiv.coe_symm_toLinearEquiv]

end Carrier

section Bundle
variable [IsManifold IB 1 B] [IsManifold IF 1 F] [ContMDiffFiberBundle 1 F E IB IF]

/-- In any preferred chart `i` containing `z`, applying `j` to an inverse base tangent coordinate
recovers `u` in the first ambient tangent coordinate. -/
theorem continuousLinearMapAt_apply_symmL_fst {i z : ManifoldTotalSpace F E}
    (hz : z ∈ (chartAt (ModelProd HB HF) i).source) (j : FiberFirstJet IB IF F E z) (u : EB) :
    ((trivializationAt (EB × EF) (TangentSpace (IB.prod IF)) i).continuousLinearMapAt 𝕜 z
      (j ((trivializationAt EB (TangentSpace IB) i.proj).symmL 𝕜 z.proj u))).1 = u := by
  rw [ManifoldTotalSpace.fst_continuousLinearMapAt_tangent hz, j.mfderiv_proj_apply,
    (trivializationAt EB (TangentSpace IB) i.proj).continuousLinearMapAt_symmL
      (ManifoldTotalSpace.proj_mem_of_mem_chartAt_source hz).2]

/-- Local derivative coordinate `EB →L[𝕜] EF` of a first jet `j` in the bundle chart at `i`. -/
def coordAt (i : ManifoldTotalSpace F E) {z : ManifoldTotalSpace F E}
    (j : FiberFirstJet IB IF F E z) : EB →L[𝕜] EF :=
  (ContinuousLinearMap.snd 𝕜 EB EF).comp
    (((trivializationAt (EB × EF) (TangentSpace (IB.prod IF)) i).continuousLinearMapAt 𝕜 z).comp
      (j.toContinuousLinearMap.comp
        ((trivializationAt EB (TangentSpace IB) i.proj).symmL 𝕜 z.proj)))

@[simp]
theorem coordAt_apply (i : ManifoldTotalSpace F E) {z : ManifoldTotalSpace F E}
    (j : FiberFirstJet IB IF F E z) (u : EB) : coordAt i j u =
      ((trivializationAt (EB × EF) (TangentSpace (IB.prod IF)) i).continuousLinearMapAt 𝕜 z
        (j ((trivializationAt EB (TangentSpace IB) i.proj).symmL 𝕜 z.proj u))).2 :=
  (rfl)

/-- Over its own base point `z`, `coordAt z` agrees with `modelEquivAt z`. -/
@[simp]
theorem coordAt_self (z : ManifoldTotalSpace F E) (j : FiberFirstJet IB IF F E z) :
    coordAt z j = modelEquivAt z j := by
  ext u
  rw [coordAt_apply, modelEquivAt_apply,
    TauCeti.Manifold.symmL_trivializationAt_self_eq_tangentSpaceCastModel_symm,
    TauCeti.Manifold.continuousLinearMapAt_trivializationAt_self_eq_tangentSpaceCastModel,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.coe_coe]

/-- Reconstruct a first jet at `z` from its derivative coordinate `A` in chart `i`. -/
def ofCoordAt {i z : ManifoldTotalSpace F E} (hz : z ∈ (chartAt (ModelProd HB HF) i).source)
    (A : EB →L[𝕜] EF) : FiberFirstJet IB IF F E z where
  toContinuousLinearMap :=
    ((trivializationAt (EB × EF) (TangentSpace (IB.prod IF)) i).symmL 𝕜 z).comp
      (((ContinuousLinearMap.id 𝕜 EB).prod A).comp
        ((trivializationAt EB (TangentSpace IB) i.proj).continuousLinearMapAt 𝕜 z.proj))
  mfderiv_proj_comp := by
    ext v
    simp only [comp_apply, id_apply, ContinuousLinearMap.prod_apply]
    rw [ManifoldTotalSpace.mfderiv_proj_symmL hz,
      (trivializationAt EB (TangentSpace IB) i.proj).symmL_continuousLinearMapAt
        (ManifoldTotalSpace.proj_mem_of_mem_chartAt_source hz).2]

@[simp]
theorem ofCoordAt_apply {i z : ManifoldTotalSpace F E}
    (hz : z ∈ (chartAt (ModelProd HB HF) i).source) (A : EB →L[𝕜] EF)
    (v : TangentSpace IB z.proj) :
    ofCoordAt hz A v = (trivializationAt (EB × EF) (TangentSpace (IB.prod IF)) i).symmL 𝕜 z
      (((ContinuousLinearMap.id 𝕜 EB).prod A)
        ((trivializationAt EB (TangentSpace IB) i.proj).continuousLinearMapAt 𝕜 z.proj v)) :=
  (rfl)

@[simp]
theorem coordAt_ofCoordAt {i z : ManifoldTotalSpace F E}
    (hz : z ∈ (chartAt (ModelProd HB HF) i).source) (A : EB →L[𝕜] EF) :
    coordAt i (ofCoordAt (IB := IB) (IF := IF) hz A) = A := by
  ext u
  rw [coordAt_apply, ofCoordAt_apply,
    (trivializationAt EB (TangentSpace IB) i.proj).continuousLinearMapAt_symmL
      (ManifoldTotalSpace.proj_mem_of_mem_chartAt_source hz).2,
    (trivializationAt (EB × EF) (TangentSpace (IB.prod IF)) i).continuousLinearMapAt_symmL hz,
    ContinuousLinearMap.prod_apply]

@[simp]
theorem ofCoordAt_coordAt {i z : ManifoldTotalSpace F E}
    (hz : z ∈ (chartAt (ModelProd HB HF) i).source) (j : FiberFirstJet IB IF F E z) :
    ofCoordAt hz (coordAt i j) = j := by
  have hbi := (ManifoldTotalSpace.proj_mem_of_mem_chartAt_source hz).2
  ext v
  rw [ofCoordAt_apply]
  set eT := trivializationAt (EB × EF) (TangentSpace (IB.prod IF)) i
  set eB := trivializationAt EB (TangentSpace IB) i.proj
  set u := eB.continuousLinearMapAt 𝕜 z.proj v
  have hv : eB.symmL 𝕜 z.proj u = v := eB.symmL_continuousLinearMapAt hbi v
  have hpair : ((ContinuousLinearMap.id 𝕜 EB).prod (coordAt i j)) u =
      eT.continuousLinearMapAt 𝕜 z (j v) :=
    Prod.ext
      (by rw [ContinuousLinearMap.prod_apply, id_apply,
        ← continuousLinearMapAt_apply_symmL_fst hz j u, hv])
      (by rw [ContinuousLinearMap.prod_apply, coordAt_apply, hv])
  rw [hpair, eT.symmL_continuousLinearMapAt hz]

/-- Nonlinear first-jet coordinate change from chart `i` to chart `k` at `z`. -/
def coordChange (i k z : ManifoldTotalSpace F E) (A : EB →L[𝕜] EF) : EB →L[𝕜] EF :=
  (ContinuousLinearMap.snd 𝕜 EB EF).comp
    ((tangentCoordChange (IB.prod IF) i k z).comp
      (((ContinuousLinearMap.id 𝕜 EB).prod A).comp (tangentCoordChange IB k.proj i.proj z.proj)))

@[simp]
theorem coordChange_apply (i k z : ManifoldTotalSpace F E) (A : EB →L[𝕜] EF) (u : EB) :
    coordChange (IB := IB) (IF := IF) (F := F) (E := E) i k z A u =
      (tangentCoordChange (IB.prod IF) i k z
        (tangentCoordChange IB k.proj i.proj z.proj u,
          A (tangentCoordChange IB k.proj i.proj z.proj u))).2 :=
  (rfl)

/-- Differences of derivative coordinates transform linearly via `VerticalSpace.coordChange` and
base `tangentCoordChange`, witnessing the affine bundle structure of `J¹E → E`. -/
theorem coordChange_sub (i k z : ManifoldTotalSpace F E) (A₁ A₂ : EB →L[𝕜] EF) :
    coordChange (IB := IB) (IF := IF) (F := F) (E := E) i k z A₁ -
        coordChange (IB := IB) (IF := IF) (F := F) (E := E) i k z A₂ =
      (VerticalSpace.coordChange (IB := IB) (IF := IF) (F := F) (E := E) i k z).comp
        ((A₁ - A₂).comp (tangentCoordChange IB k.proj i.proj z.proj)) := by
  ext u
  simp only [sub_apply, coordChange_apply, comp_apply, VerticalSpace.coordChange_apply]
  have hsub : (tangentCoordChange IB k.proj i.proj z.proj u,
        A₁ (tangentCoordChange IB k.proj i.proj z.proj u)) -
      (tangentCoordChange IB k.proj i.proj z.proj u,
        A₂ (tangentCoordChange IB k.proj i.proj z.proj u)) =
      (0, A₁ (tangentCoordChange IB k.proj i.proj z.proj u) -
        A₂ (tangentCoordChange IB k.proj i.proj z.proj u)) := by ext <;> simp
  rw [← hsub, map_sub, Prod.snd_sub]

/-- Reconstructing a first jet from `A` in chart `i` and reading its coordinate in chart `k` applies
`FiberFirstJet.coordChange i k z`. -/
theorem coordAt_ofCoordAt_eq_coordChange {i k z : ManifoldTotalSpace F E}
    (hi : z ∈ (chartAt (ModelProd HB HF) i).source)
    (hk : z ∈ (chartAt (ModelProd HB HF) k).source) (A : EB →L[𝕜] EF) :
    coordAt k (ofCoordAt (IB := IB) (IF := IF) hi A) =
      coordChange (IB := IB) (IF := IF) (F := F) (E := E) i k z A := by
  ext u
  rw [coordAt_apply, ofCoordAt_apply,
    TauCeti.Manifold.continuousLinearMapAt_symmL_coordChange
      (ManifoldTotalSpace.proj_mem_of_mem_chartAt_source hk).2
      (ManifoldTotalSpace.proj_mem_of_mem_chartAt_source hi).2,
    TauCeti.Manifold.continuousLinearMapAt_symmL_coordChange hi hk,
    ContinuousLinearMap.prod_apply, id_apply, coordChange_apply]

/-- Reading `j : FiberFirstJet IB IF F E z` in chart `i` containing `z` applies `coordChange z i z`
to the preferred model coordinate `modelEquivAt z j`. -/
theorem coordAt_eq_coordChange_modelEquivAt {i z : ManifoldTotalSpace F E}
    (hi : z ∈ (chartAt (ModelProd HB HF) i).source) (j : FiberFirstJet IB IF F E z) :
    coordAt i j = coordChange (IB := IB) (IF := IF) (F := F) (E := E) z i z (modelEquivAt z j) := by
  rw [← coordAt_self z j, ← coordAt_ofCoordAt_eq_coordChange (mem_chart_source _ z) hi,
    ofCoordAt_coordAt]

/-- On the domain of chart `i`, `FiberFirstJet.coordChange i i z` is the identity. -/
theorem coordChange_self {i z : ManifoldTotalSpace F E}
    (hz : z ∈ (chartAt (ModelProd HB HF) i).source) (A : EB →L[𝕜] EF) :
    coordChange (IB := IB) (IF := IF) (F := F) (E := E) i i z A = A := by
  rw [← coordAt_ofCoordAt_eq_coordChange hz hz, coordAt_ofCoordAt]

/-- On triple chart overlaps, `FiberFirstJet.coordChange` satisfies the cocycle law. -/
theorem coordChange_comp {i j k z : ManifoldTotalSpace F E}
    (hz : z ∈ (chartAt (ModelProd HB HF) i).source ∩
      (chartAt (ModelProd HB HF) j).source ∩
      (chartAt (ModelProd HB HF) k).source) (A : EB →L[𝕜] EF) :
    coordChange (IB := IB) (IF := IF) (F := F) (E := E) j k z
        (coordChange (IB := IB) (IF := IF) (F := F) (E := E) i j z A) =
      coordChange (IB := IB) (IF := IF) (F := F) (E := E) i k z A := by
  rcases hz with ⟨⟨hzi, hzj⟩, hzk⟩
  rw [← coordAt_ofCoordAt_eq_coordChange hzi hzj,
    ← coordAt_ofCoordAt_eq_coordChange hzj hzk, ofCoordAt_coordAt,
    coordAt_ofCoordAt_eq_coordChange hzi hzk]

/-- Over boundaryless base and fibre models, `FiberFirstJet.coordChange i k z` agrees with the
derivative component `(firstJetCoordChange h g ...).2` of the local nonlinear 1-jet transition law
from `TauCeti.Analysis.Calculus.Jet.Nonlinear`. -/
theorem coordChange_eq_firstJetCoordChange_snd [IB.Boundaryless] [IF.Boundaryless]
    {i k z : ManifoldTotalSpace F E}
    (hi : z ∈ (chartAt (ModelProd HB HF) i).source)
    (hk : z ∈ (chartAt (ModelProd HB HF) k).source) (A : EB →L[𝕜] EF) :
    let h : EB → EB := extChartAt IB i.proj ∘ (extChartAt IB k.proj).symm
    let g : EB × EF → EF := fun q ↦
      (extChartAt (IB.prod IF) k ((extChartAt (IB.prod IF) i).symm (h q.1, q.2))).2
    coordChange (IB := IB) (IF := IF) (F := F) (E := E) i k z A =
      (firstJetCoordChange h g (extChartAt IB k.proj z.proj)
        ((extChartAt (IB.prod IF) i z).2, A)).2 := by
  intro h g
  -- Stage 1: chart-source memberships and base-fibre pairing `extChartAt i z`.
  have hi' : z ∈ (extChartAt (IB.prod IF) i).source := (extChartAt_source (IB.prod IF) i).symm ▸ hi
  have hk' : z ∈ (extChartAt (IB.prod IF) k).source := (extChartAt_source (IB.prod IF) k).symm ▸ hk
  have hbi : z.proj ∈ (extChartAt IB i.proj).source :=
    ManifoldTotalSpace.proj_mem_extChartAt_source_of_mem_chartAt_source hi
  have hbk : z.proj ∈ (extChartAt IB k.proj).source :=
    ManifoldTotalSpace.proj_mem_extChartAt_source_of_mem_chartAt_source hk
  have hpair : (h (extChartAt IB k.proj z.proj), (extChartAt (IB.prod IF) i z).2) =
      extChartAt (IB.prod IF) i z := Prod.ext (by
    dsimp only [h]
    rw [Function.comp_apply, (extChartAt IB k.proj).left_inv hbk,
      ManifoldTotalSpace.extChartAt_fst_eq hi]) rfl
  -- Stage 2: total Fréchet derivatives of the base and ambient chart transitions.
  have hh_deriv : HasFDerivAt h (tangentCoordChange IB k.proj i.proj z.proj)
      (extChartAt IB k.proj z.proj) := by
    have hd := hasFDerivWithinAt_tangentCoordChange (I := IB) ⟨hbk, hbi⟩
    rwa [IB.range_eq_univ, hasFDerivWithinAt_univ] at hd
  have hT_deriv : HasFDerivAt (extChartAt (IB.prod IF) k ∘ (extChartAt (IB.prod IF) i).symm)
      (tangentCoordChange (IB.prod IF) i k z) (extChartAt (IB.prod IF) i z) := by
    have hd := hasFDerivWithinAt_tangentCoordChange (I := IB.prod IF) ⟨hi', hk'⟩
    rwa [(IB.prod IF).range_eq_univ, hasFDerivWithinAt_univ] at hd
  -- Stage 3: differentiate `g` by the chain rule and match with `firstJetCoordChange`.
  let pt : EB × EF := (extChartAt IB k.proj z.proj, (extChartAt (IB.prod IF) i z).2)
  have hinner : HasFDerivAt (fun q : EB × EF ↦ (h q.1, q.2)) _ pt :=
    (hh_deriv.comp pt (hasFDerivAt_fst (𝕜 := 𝕜) (E := EB) (F := EF))).prodMk
      (hasFDerivAt_snd (𝕜 := 𝕜) (E := EB) (F := EF))
  have hmid := (hpair.symm ▸ hT_deriv).comp pt hinner
  have hg_deriv : HasFDerivAt g _ pt := (hasFDerivAt_snd (𝕜 := 𝕜) (E := EB) (F := EF)).comp pt hmid
  ext u
  rw [coordChange_apply, firstJetCoordChange_snd_apply, hg_deriv.fderiv, hh_deriv.fderiv]
  simp only [comp_apply, ContinuousLinearMap.prod_apply, coe_fst', coe_snd']

/-- For a `C^(n + 1)` fibre bundle over `C^(n + 1)` base and fibre manifolds, the first-jet
coordinate change `(z, A) ↦ coordChange i k z A` is `C^n` on chart overlaps. -/
theorem contMDiffOn_coordChange {n : ℕ∞ω} [IsManifold IB (n + 1) B] [IsManifold IF (n + 1) F]
    [ContMDiffFiberBundle (n + 1) F E IB IF] (i k : ManifoldTotalSpace F E) :
    ContMDiffOn ((IB.prod IF).prod 𝓘(𝕜, EB →L[𝕜] EF)) 𝓘(𝕜, EB →L[𝕜] EF) n
      (fun p : ManifoldTotalSpace F E × (EB →L[𝕜] EF) ↦
        coordChange (IB := IB) (IF := IF) (F := F) (E := E) i k p.1 p.2)
      (((chartAt (ModelProd HB HF) i).source ∩ (chartAt (ModelProd HB HF) k).source) ×ˢ univ) := by
  have : IsManifold IB n B := .of_le (n := n + 1) le_self_add
  have : IsManifold IF n F := .of_le (n := n + 1) le_self_add
  have : ContMDiffFiberBundle n F E IB IF := .of_le (n := n + 1) le_self_add
  set S := ((chartAt (ModelProd HB HF) i).source ∩ (chartAt (ModelProd HB HF) k).source) ×ˢ
    (univ : Set (EB →L[𝕜] EF))
  have hfst : ContMDiffOn ((IB.prod IF).prod 𝓘(𝕜, EB →L[𝕜] EF)) (IB.prod IF) n Prod.fst S :=
    contMDiffOn_fst
  have hTE := ((tangentBundleCore.isContMDiff (I := IB.prod IF) (M := ManifoldTotalSpace F E)
    (n := n)).contMDiffOn_coordChange (achart _ i) (achart _ k)).comp hfst fun _ hp ↦ hp.1
  have hTB := ((tangentBundleCore.isContMDiff (I := IB) (M := B) (n := n)).contMDiffOn_coordChange
    (achart _ k.proj) (achart _ i.proj)).comp
    ((ManifoldTotalSpace.contMDiff_proj n F E IB IF).comp_contMDiffOn hfst)
    fun _ hp ↦ ⟨(ManifoldTotalSpace.proj_mem_of_mem_chartAt_source hp.1.2).2,
      (ManifoldTotalSpace.proj_mem_of_mem_chartAt_source hp.1.1).2⟩
  have hprod : ContMDiffOn ((IB.prod IF).prod 𝓘(𝕜, EB →L[𝕜] EF)) 𝓘(𝕜, EB →L[𝕜] EB × EF) n
      (fun p : ManifoldTotalSpace F E × (EB →L[𝕜] EF) ↦
        (ContinuousLinearMap.id 𝕜 EB).prod p.2) S :=
    (ContinuousLinearMap.prodₗᵢ 𝕜 :
      (EB →L[𝕜] EB) × (EB →L[𝕜] EF) ≃ₗᵢ[𝕜] EB →L[𝕜] EB × EF).contDiff.contMDiff.comp_contMDiffOn
      (contMDiffOn_const.prodMk_space contMDiffOn_snd)
  exact contMDiffOn_const.clm_comp (hTE.clm_comp (hprod.clm_comp hTB))

open Classical in
/-- Local pretrivialization of `FiberFirstJet IB IF F E` over the chart domain of `i`. -/
def pretrivializationAt (i : ManifoldTotalSpace F E) :
    Pretrivialization (EB →L[𝕜] EF) (π (EB →L[𝕜] EF) (FiberFirstJet IB IF F E)) where
  toFun p := (p.proj, coordAt i p.snd)
  invFun q := if hq : q.1 ∈ (chartAt (ModelProd HB HF) i).source then ⟨q.1, ofCoordAt hq q.2⟩
    else ⟨q.1, Classical.arbitrary _⟩
  source := π (EB →L[𝕜] EF) (FiberFirstJet IB IF F E) ⁻¹' (chartAt (ModelProd HB HF) i).source
  target := (chartAt (ModelProd HB HF) i).source ×ˢ univ
  map_source' _ hp := ⟨hp, mem_univ _⟩
  map_target' _ hq := by split_ifs with h; exacts [h, (h hq.1).elim]
  left_inv' := by
    rintro ⟨z, j⟩ (hz : z ∈ (chartAt (ModelProd HB HF) i).source)
    dsimp only; rw [dite_eq_left hz, ofCoordAt_coordAt]
  right_inv' := by
    rintro ⟨z, A⟩ ⟨hz : z ∈ (chartAt (ModelProd HB HF) i).source, -⟩
    dsimp only; rw [dite_eq_left hz]; simp [coordAt_ofCoordAt]
  open_target := (chartAt (ModelProd HB HF) i).open_source.prod isOpen_univ
  baseSet := (chartAt (ModelProd HB HF) i).source
  open_baseSet := (chartAt (ModelProd HB HF) i).open_source
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

@[simp]
theorem pretrivializationAt_apply (i : ManifoldTotalSpace F E)
    (p : TotalSpace (EB →L[𝕜] EF) (FiberFirstJet IB IF F E)) :
    pretrivializationAt i p = (p.proj, coordAt i p.snd) :=
  (rfl)

/-- Over the chart domain of `i`, `(pretrivializationAt i).toPartialEquiv.symm (z, A)` reconstructs
`⟨z, ofCoordAt hz A⟩`. -/
theorem pretrivializationAt_symm_eq {i z : ManifoldTotalSpace F E}
    (hz : z ∈ (chartAt (ModelProd HB HF) i).source) (A : EB →L[𝕜] EF) :
    (pretrivializationAt (IB := IB) (IF := IF) (F := F) (E := E) i).toPartialEquiv.symm (z, A) =
      ⟨z, ofCoordAt hz A⟩ :=
  dite_eq_left hz

/-- The `FiberPrebundle` assembling `FiberFirstJet IB IF F E` into a fibre bundle. -/
def fiberPrebundle : FiberPrebundle (EB →L[𝕜] EF) (FiberFirstJet IB IF F E) where
  pretrivializationAtlas := range (pretrivializationAt (IB := IB) (IF := IF) (F := F) (E := E))
  pretrivializationAt := pretrivializationAt
  mem_base_pretrivializationAt z := mem_chart_source _ z
  pretrivialization_mem_atlas z := ⟨z, rfl⟩
  continuous_trivChange := by
    rintro _ ⟨k, rfl⟩ _ ⟨i, rfl⟩
    have : IsManifold IB (0 + 1) B := (by simpa); have : IsManifold IF (0 + 1) F := by simpa
    have : ContMDiffFiberBundle (0 + 1) F E IB IF := by simpa
    refine ((continuousOn_fst.prodMk
      (contMDiffOn_coordChange (IB := IB) (IF := IF) (F := F) (E := E) (n := 0) i k).continuousOn
      ).mono ?_).congr ?_
    · rintro ⟨z, A⟩ ⟨⟨hz_i, -⟩, hz_k⟩
      rw [mem_preimage, pretrivializationAt_symm_eq hz_i] at hz_k
      exact ⟨⟨hz_i, hz_k⟩, mem_univ _⟩
    · rintro ⟨z, A⟩ ⟨⟨hz_i, -⟩, hz_k⟩
      rw [mem_preimage, pretrivializationAt_symm_eq hz_i] at hz_k
      rw [Function.comp_apply, pretrivializationAt_symm_eq hz_i, pretrivializationAt_apply,
        coordAt_ofCoordAt_eq_coordChange hz_i hz_k]
  totalSpaceMk_isInducing z := by
    have hfun : (pretrivializationAt (IB := IB) (IF := IF) (F := F) (E := E) z ∘ TotalSpace.mk z) =
        Prod.mk z ∘ modelHomeomorphAt z := by funext j; simp [pretrivializationAt_apply]
    exact hfun ▸ (isInducing_prodMkRight z).comp (modelHomeomorphAt z).isInducing

instance instTopologicalSpaceTotalSpace :
    TopologicalSpace (TotalSpace (EB →L[𝕜] EF) (FiberFirstJet IB IF F E)) :=
  (fiberPrebundle (IB := IB) (IF := IF) (F := F) (E := E)).totalSpaceTopology

instance instFiberBundle : FiberBundle (EB →L[𝕜] EF) (FiberFirstJet IB IF F E) :=
  (fiberPrebundle (IB := IB) (IF := IF) (F := F) (E := E)).toFiberBundle

@[simp]
theorem trivializationAt_baseSet (i : ManifoldTotalSpace F E) :
    (trivializationAt (EB →L[𝕜] EF) (FiberFirstJet IB IF F E) i).baseSet =
      (chartAt (ModelProd HB HF) i).source :=
  (rfl)

@[simp]
theorem trivializationAt_apply (i : ManifoldTotalSpace F E)
    (p : TotalSpace (EB →L[𝕜] EF) (FiberFirstJet IB IF F E)) :
    trivializationAt (EB →L[𝕜] EF) (FiberFirstJet IB IF F E) i p = (p.proj, coordAt i p.snd) :=
  (rfl)

/-- Over the chart domain of `i`, `(trivializationAt _ (FiberFirstJet ...) i).symm z A` reconstructs
the first jet `ofCoordAt hz A`. -/
theorem trivializationAt_symm_apply {i z : ManifoldTotalSpace F E}
    (hz : z ∈ (chartAt (ModelProd HB HF) i).source) (A : EB →L[𝕜] EF) :
    (trivializationAt (EB →L[𝕜] EF) (FiberFirstJet IB IF F E) i).symm z A = ofCoordAt hz A :=
  TotalSpace.mk_injective z (((pretrivializationAt i).mk_symm hz A).trans (dite_eq_left hz))

private theorem trivialization_coordChange_eq {i k z : ManifoldTotalSpace F E}
    (he₁ : pretrivializationAt i ∈
      (fiberPrebundle (IB := IB) (IF := IF) (F := F) (E := E)).pretrivializationAtlas)
    (he₂ : pretrivializationAt k ∈
      (fiberPrebundle (IB := IB) (IF := IF) (F := F) (E := E)).pretrivializationAtlas)
    (hz_i : z ∈ (chartAt (ModelProd HB HF) i).source)
    (hz_k : z ∈ (chartAt (ModelProd HB HF) k).source) (A : EB →L[𝕜] EF) :
    ((fiberPrebundle (IB := IB) (IF := IF) (F := F)
        (E := E)).trivializationOfMemPretrivializationAtlas he₁).coordChange
      ((fiberPrebundle (IB := IB) (IF := IF) (F := F)
        (E := E)).trivializationOfMemPretrivializationAtlas he₂) z A =
    coordChange (IB := IB) (IF := IF) (F := F) (E := E) i k z A := by
  set e₁ := (fiberPrebundle (IB := IB) (IF := IF) (F := F)
    (E := E)).trivializationOfMemPretrivializationAtlas he₁
  set e₂ := (fiberPrebundle (IB := IB) (IF := IF) (F := F)
    (E := E)).trivializationOfMemPretrivializationAtlas he₂
  let p : TotalSpace (EB →L[𝕜] EF) (FiberFirstJet IB IF F E) := ⟨z, ofCoordAt hz_i A⟩
  -- Mathlib's `FiberPrebundle.trivializationOfMemPretrivializationAtlas` extends `e` via
  -- `{ e with ... }` with no public projection lemma equating its `toPretrivialization` to `e`.
  have he₁_snd : (e₁ p).snd = A := by
    change (pretrivializationAt i p).snd = A
    rw [pretrivializationAt_apply, coordAt_ofCoordAt]
  have he₂_snd : (e₂ p).snd = coordChange (IB := IB) (IF := IF) (F := F) (E := E) i k z A := by
    change (pretrivializationAt k p).snd = _
    rw [pretrivializationAt_apply, coordAt_ofCoordAt_eq_coordChange hz_i hz_k]
  have h := e₁.coordChange_apply_snd e₂ (p := p) hz_i
  rwa [he₁_snd, he₂_snd] at h

/-- For a `C^(n + 1)` fibre bundle over `C^(n + 1)` base and fibre manifolds, `FiberFirstJet` forms
a `C^n` fibre bundle over `ManifoldTotalSpace F E`. -/
theorem contMDiffFiberBundle {n : ℕ∞ω} [IsManifold IB (n + 1) B] [IsManifold IF (n + 1) F]
    [ContMDiffFiberBundle (n + 1) F E IB IF] :
    ContMDiffFiberBundle n (EB →L[𝕜] EF) (FiberFirstJet IB IF F E)
      (IB.prod IF) 𝓘(𝕜, EB →L[𝕜] EF) := by
  refine ⟨fun e e' he he' ↦ ?_⟩
  obtain ⟨_, ⟨i, rfl⟩, rfl⟩ := he.out
  obtain ⟨_, ⟨k, rfl⟩, rfl⟩ := he'.out
  refine (contMDiffOn_coordChange (IB := IB) (IF := IF) (F := F) (E := E) (n := n) i k).congr ?_
  rintro ⟨z, A⟩ ⟨⟨hz_i, hz_k⟩, -⟩
  exact trivialization_coordChange_eq _ _ hz_i hz_k A

omit [IsManifold IB 1 B] [IsManifold IF 1 F] [ContMDiffFiberBundle 1 F E IB IF] in
instance [IsManifold IB ∞ B] [IsManifold IF ∞ F] [ContMDiffFiberBundle ∞ F E IB IF] :
    ContMDiffFiberBundle ∞ (EB →L[𝕜] EF) (FiberFirstJet IB IF F E)
      (IB.prod IF) 𝓘(𝕜, EB →L[𝕜] EF) := by
  have : IsManifold IB (∞ + 1) B := (by simpa); have : IsManifold IF (∞ + 1) F := by simpa
  have : ContMDiffFiberBundle (∞ + 1) F E IB IF := (by simpa); exact contMDiffFiberBundle

omit [IsManifold IB 1 B] [IsManifold IF 1 F] [ContMDiffFiberBundle 1 F E IB IF] in
instance [IsManifold IB ω B] [IsManifold IF ω F] [ContMDiffFiberBundle ω F E IB IF] :
    ContMDiffFiberBundle ω (EB →L[𝕜] EF) (FiberFirstJet IB IF F E)
      (IB.prod IF) 𝓘(𝕜, EB →L[𝕜] EF) := by
  have : IsManifold IB (ω + 1) B := (by simpa); have : IsManifold IF (ω + 1) F := by simpa
  have : ContMDiffFiberBundle (ω + 1) F E IB IF := (by simpa); exact contMDiffFiberBundle

end Bundle
end FiberFirstJet

variable (IB IF F E) in
/-- The **nonlinear first-jet bundle** `J¹E` of a fibre bundle `E`. -/
abbrev FiberFirstJetBundle := TotalSpace (EB →L[𝕜] EF) (FiberFirstJet IB IF F E)

namespace FiberFirstJetBundle

/-- Two points of `FiberFirstJetBundle` agree iff they have the same target point and the same
preferred-chart derivative coordinate. -/
theorem mk_eq_mk_iff_modelEquivAt {z₁ z₂ : ManifoldTotalSpace F E}
    {j₁ : FiberFirstJet IB IF F E z₁} {j₂ : FiberFirstJet IB IF F E z₂} :
    (⟨z₁, j₁⟩ : FiberFirstJetBundle IB IF F E) = ⟨z₂, j₂⟩ ↔
      z₁ = z₂ ∧ FiberFirstJet.modelEquivAt z₁ j₁ = FiberFirstJet.modelEquivAt z₂ j₂ :=
  ⟨by rintro ⟨⟩; exact ⟨rfl, rfl⟩, fun ⟨rfl, h⟩ ↦
    congrArg (TotalSpace.mk' _ z₁) ((FiberFirstJet.modelEquivAt z₁).injective h)⟩

/-- The source (base) projection `π_1 : J¹E → B` onto `B`. -/
def baseProj (p : FiberFirstJetBundle IB IF F E) : B := p.proj.proj

/-- Pointwise formula for the source projection `baseProj` via `TotalSpace.proj` and
`ManifoldTotalSpace.proj`. -/
theorem baseProj_apply (p : FiberFirstJetBundle IB IF F E) : baseProj p = p.proj.proj :=
  (rfl)

/-- `baseProj` factors as `ManifoldTotalSpace.proj ∘ TotalSpace.proj`. -/
theorem baseProj_eq_proj_comp_proj :
    (baseProj : FiberFirstJetBundle IB IF F E → B) =
      ManifoldTotalSpace.proj ∘ TotalSpace.proj :=
  (rfl)

/-- Every point `z : ManifoldTotalSpace F E` has a nonempty fibre in `FiberFirstJetBundle`, so
`TotalSpace.proj` is surjective. -/
theorem proj_surjective :
    Function.Surjective
      (TotalSpace.proj : FiberFirstJetBundle IB IF F E → ManifoldTotalSpace F E) :=
  fun z ↦ let ⟨j⟩ := (inferInstance : Nonempty (FiberFirstJet IB IF F E z)); ⟨⟨z, j⟩, rfl⟩

/-- When the model fibre `F` is nonempty, the source projection `baseProj : J¹E → B` is
surjective. -/
theorem baseProj_surjective [Nonempty F] :
    Function.Surjective (baseProj : FiberFirstJetBundle IB IF F E → B) := fun b ↦
  let ⟨x, hx⟩ := FiberBundle.surjective_proj F E b
  let ⟨j⟩ := (inferInstance :
    Nonempty (FiberFirstJet IB IF F E (ManifoldTotalSpace.homeomorph F E x)))
  ⟨⟨ManifoldTotalSpace.homeomorph F E x, j⟩,
    (baseProj_apply _).trans ((ManifoldTotalSpace.proj_homeomorph x).trans hx)⟩

section Structure
variable [IsManifold IB 1 B] [IsManifold IF 1 F] [ContMDiffFiberBundle 1 F E IB IF]

/-- In any chart `i` containing `z₁`, two points of `FiberFirstJetBundle` over `z₁` and `z₂` agree
iff `z₁ = z₂` and their `coordAt i` coordinates coincide. -/
theorem mk_eq_mk_iff_coordAt {i z₁ z₂ : ManifoldTotalSpace F E}
    (hz₁ : z₁ ∈ (chartAt (ModelProd HB HF) i).source)
    {j₁ : FiberFirstJet IB IF F E z₁} {j₂ : FiberFirstJet IB IF F E z₂} :
    (⟨z₁, j₁⟩ : FiberFirstJetBundle IB IF F E) = ⟨z₂, j₂⟩ ↔
      z₁ = z₂ ∧ FiberFirstJet.coordAt i j₁ = FiberFirstJet.coordAt i j₂ := by
  refine ⟨by rintro ⟨⟩; exact ⟨rfl, rfl⟩, ?_⟩
  rintro ⟨rfl, h⟩
  apply congrArg (TotalSpace.mk' _ z₁)
  rw [← FiberFirstJet.ofCoordAt_coordAt hz₁ j₁, ← FiberFirstJet.ofCoordAt_coordAt hz₁ j₂, h]

/-- On any `C^1` fibre bundle over `C^1` base and fibre manifolds, the source projection
`baseProj : J¹E → B` is `C^n` for every `n : ℕ∞ω`. -/
theorem contMDiff_baseProj (n : ℕ∞ω) :
    ContMDiff ((IB.prod IF).prod 𝓘(𝕜, EB →L[𝕜] EF)) IB n
      (baseProj : FiberFirstJetBundle IB IF F E → B) :=
  (ManifoldTotalSpace.contMDiff_proj n F E IB IF).comp
    (Bundle.contMDiff_proj (FiberFirstJet IB IF F E))

/-- For a `C^(n + 1)` fibre bundle over `C^(n + 1)` base and fibre manifolds, the total space
`FiberFirstJetBundle IB IF F E` is a `C^n` manifold. -/
theorem isManifold {n : ℕ∞ω} [IsManifold IB (n + 1) B] [IsManifold IF (n + 1) F]
    [ContMDiffFiberBundle (n + 1) F E IB IF] :
    IsManifold ((IB.prod IF).prod 𝓘(𝕜, EB →L[𝕜] EF)) n (FiberFirstJetBundle IB IF F E) := by
  have : IsManifold IB n B := .of_le (n := n + 1) le_self_add
  have : IsManifold IF n F := .of_le (n := n + 1) le_self_add
  have : ContMDiffFiberBundle n F E IB IF := .of_le (n := n + 1) le_self_add
  have := FiberFirstJet.contMDiffFiberBundle (IB := IB) (IF := IF) (F := F) (E := E) (n := n)
  exact isManifold_of_hasGroupoid_contMDiffGroupoid ((IB.prod IF).prod 𝓘(𝕜, EB →L[𝕜] EF)) n
    (TotalSpace (EB →L[𝕜] EF) (FiberFirstJet IB IF F E))

omit [IsManifold IB 1 B] [IsManifold IF 1 F] [ContMDiffFiberBundle 1 F E IB IF] in
instance [IsManifold IB ∞ B] [IsManifold IF ∞ F] [ContMDiffFiberBundle ∞ F E IB IF] :
    IsManifold ((IB.prod IF).prod 𝓘(𝕜, EB →L[𝕜] EF)) ∞ (FiberFirstJetBundle IB IF F E) := by
  have : IsManifold IB (∞ + 1) B := (by simpa); have : IsManifold IF (∞ + 1) F := by simpa
  have : ContMDiffFiberBundle (∞ + 1) F E IB IF := (by simpa); exact isManifold

omit [IsManifold IB 1 B] [IsManifold IF 1 F] [ContMDiffFiberBundle 1 F E IB IF] in
instance [IsManifold IB ω B] [IsManifold IF ω F] [ContMDiffFiberBundle ω F E IB IF] :
    IsManifold ((IB.prod IF).prod 𝓘(𝕜, EB →L[𝕜] EF)) ω (FiberFirstJetBundle IB IF F E) := by
  have : IsManifold IB (ω + 1) B := (by simpa); have : IsManifold IF (ω + 1) F := by simpa
  have : ContMDiffFiberBundle (ω + 1) F E IB IF := (by simpa); exact isManifold

/-- Pointwise **Cartan contact map** `θ_p : T_p(J¹E) →L[𝕜] V_{p.proj} E`, projecting the target
differential `mfderiv _ _ TotalSpace.proj p` onto the vertical space along `p.snd`. -/
def contactFormAt (p : FiberFirstJetBundle IB IF F E) :
    TangentSpace ((IB.prod IF).prod 𝓘(𝕜, EB →L[𝕜] EF)) p →L[𝕜]
      VerticalSpace IB IF F E p.proj :=
  p.snd.contactProj.comp
    (mfderiv ((IB.prod IF).prod 𝓘(𝕜, EB →L[𝕜] EF)) (IB.prod IF) TotalSpace.proj p)

/-- Applying `contactFormAt p` projects `mfderiv _ _ TotalSpace.proj p ξ` along
`p.snd.contactProj`. -/
theorem contactFormAt_apply (p : FiberFirstJetBundle IB IF F E)
    (ξ : TangentSpace ((IB.prod IF).prod 𝓘(𝕜, EB →L[𝕜] EF)) p) :
    contactFormAt p ξ =
      p.snd.contactProj
        (mfderiv ((IB.prod IF).prod 𝓘(𝕜, EB →L[𝕜] EF)) (IB.prod IF) TotalSpace.proj p ξ) :=
  (rfl)

/-- Coercing `contactFormAt p ξ` into the ambient tangent space `T_{p.proj} E` subtracts the
horizontal lift `p.snd (dπ (d(proj)_p ξ))` from `d(proj)_p ξ`. -/
@[simp]
theorem coe_contactFormAt (p : FiberFirstJetBundle IB IF F E)
    (ξ : TangentSpace ((IB.prod IF).prod 𝓘(𝕜, EB →L[𝕜] EF)) p) :
    (contactFormAt p ξ : TangentSpace (IB.prod IF) p.proj) =
      mfderiv ((IB.prod IF).prod 𝓘(𝕜, EB →L[𝕜] EF)) (IB.prod IF) TotalSpace.proj p ξ -
        p.snd (mfderiv (IB.prod IF) IB ManifoldTotalSpace.proj p.proj
          (mfderiv ((IB.prod IF).prod 𝓘(𝕜, EB →L[𝕜] EF)) (IB.prod IF) TotalSpace.proj p ξ)) :=
  p.snd.coe_contactProj _

end Structure
end FiberFirstJetBundle
end ManifoldFiber
end TauCeti
