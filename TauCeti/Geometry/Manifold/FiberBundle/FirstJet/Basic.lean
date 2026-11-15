/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Jet.Nonlinear
public import TauCeti.Geometry.Manifold.FiberBundle.Vertical
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# The nonlinear first-jet bundle of a smooth fibre bundle

For a fibre bundle `E` over `B` (modelled on `IB`) with manifold fibre `F` (modelled on `IF`),
`TauCeti.FiberFirstJet IB IF F E z` over `z : ManifoldTotalSpace F E` is the affine torsor of
continuous linear right-inverses `T_{π(z)} B →L[𝕜] T_z E` of `mfderiv proj z`, with contact
projection `contactProj` and splitting `splittingEquiv`. Local derivative coordinates (`coordAt`,
`ofCoordAt`) transform by `coordChange` (`coordChange_eq_firstJetCoordChange`, `coordChange_sub`)
and assemble into `TauCeti.FiberFirstJetBundle IB IF F E` (`J¹E`), a `C^n` fibre bundle and `C^n`
manifold for `C^(n+1)` data, with `targetProj`, `baseProj`, and Cartan contact form `contactFormAt`.

## References
* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, 1993, §12.
* D. J. Saunders, *The Geometry of Jet Bundles*, Cambridge University Press, 1989, §§4.1–4.2.
* I. M. Anderson, *The Variational Bicomplex*, Utah State University, 1992, Chapter 1, §A.
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
  /-- The underlying continuous linear splitting `T_{π(z)} B →L[𝕜] T_z E`. -/
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
@[simp] theorem toContinuousLinearMap_apply (j : FiberFirstJet IB IF F E z)
    (u : TangentSpace IB z.proj) : j.toContinuousLinearMap u = j u := (rfl)
@[simp] protected theorem map_zero (j : FiberFirstJet IB IF F E z) : j 0 = 0 :=
  j.toContinuousLinearMap.map_zero
@[simp] protected theorem map_add (j : FiberFirstJet IB IF F E z) (u v : TangentSpace IB z.proj) :
    j (u + v) = j u + j v := j.toContinuousLinearMap.map_add u v
@[ext] theorem ext {j₁ j₂ : FiberFirstJet IB IF F E z} (h : ∀ u, j₁ u = j₂ u) : j₁ = j₂ :=
  DFunLike.ext j₁ j₂ h
@[simp] theorem mfderiv_proj_apply (j : FiberFirstJet IB IF F E z) (u : TangentSpace IB z.proj) :
    mfderiv (IB.prod IF) IB ManifoldTotalSpace.proj z (j u) = u :=
  DFunLike.congr_fun j.mfderiv_proj_comp u
theorem injective (j : FiberFirstJet IB IF F E z) : Function.Injective j :=
  Function.LeftInverse.injective j.mfderiv_proj_apply
@[simp] theorem tangentSpaceCastModel_apply_fst (j : FiberFirstJet IB IF F E z)
    (u : TangentSpace IB z.proj) :
    (tangentSpaceCastModel (IB.prod IF) z (j u)).1 = tangentSpaceCastModel IB z.proj u := by
  rw [← ManifoldTotalSpace.tangentSpaceCastModel_mfderiv_proj, j.mfderiv_proj_apply]

/-- Preferred-chart coordinate equivalence `FiberFirstJet IB IF F E z ≃ (EB →L[𝕜] EF)`. -/
def modelEquivAt (z : ManifoldTotalSpace F E) :
    FiberFirstJet IB IF F E z ≃ (EB →L[𝕜] EF) where
  toFun j := (ContinuousLinearMap.snd 𝕜 EB EF).comp
    ((tangentSpaceCastModel (IB.prod IF) z).toContinuousLinearMap.comp
      (j.toContinuousLinearMap.comp (tangentSpaceCastModel IB z.proj).symm.toContinuousLinearMap))
  invFun A :=
    { toContinuousLinearMap := (tangentSpaceCastModel (IB.prod IF) z).symm.toContinuousLinearMap
        |>.comp (((ContinuousLinearMap.id 𝕜 EB).prod A).comp
          (tangentSpaceCastModel IB z.proj).toContinuousLinearMap)
      mfderiv_proj_comp := by
        ext u; apply (tangentSpaceCastModel IB z.proj).injective
        rw [comp_apply, ManifoldTotalSpace.tangentSpaceCastModel_mfderiv_proj]; simp }
  left_inv j := by
    ext u; apply (tangentSpaceCastModel (IB.prod IF) z).injective
    change tangentSpaceCastModel (IB.prod IF) z ((tangentSpaceCastModel (IB.prod IF) z).symm
        (tangentSpaceCastModel IB z.proj u, (tangentSpaceCastModel (IB.prod IF) z
          (j ((tangentSpaceCastModel IB z.proj).symm (tangentSpaceCastModel IB z.proj u)))).2)) =
      tangentSpaceCastModel (IB.prod IF) z (j u)
    rw [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.symm_apply_apply]
    exact Prod.ext (j.tangentSpaceCastModel_apply_fst u).symm rfl
  right_inv A := by ext u; simp
@[simp] theorem modelEquivAt_apply (z : ManifoldTotalSpace F E) (j : FiberFirstJet IB IF F E z)
    (u : EB) : modelEquivAt z j u =
      (tangentSpaceCastModel (IB.prod IF) z (j ((tangentSpaceCastModel IB z.proj).symm u))).2 :=
  (rfl)
instance : Inhabited (FiberFirstJet IB IF F E z) := ⟨(modelEquivAt z).symm 0⟩
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
    have heq : (fun A : EB →L[𝕜] EF ↦ (ContinuousLinearMap.id 𝕜 EB).prod A) =
        fun A ↦ ContinuousLinearMap.inl 𝕜 EB EF + (ContinuousLinearMap.inr 𝕜 EB EF).comp A :=
      funext fun _ ↦ by ext <;> simp
    have hprod : Continuous fun A : EB →L[𝕜] EF ↦ (ContinuousLinearMap.id 𝕜 EB).prod A :=
      heq ▸ continuous_const.add (ContinuousLinearMap.postcomp EB
        (ContinuousLinearMap.inr 𝕜 EB EF) : (EB →L[𝕜] EF) →L[𝕜] (EB →L[𝕜] EB × EF)).continuous
    exact (ContinuousLinearMap.precomp (TangentSpace (IB.prod IF) z)
      (tangentSpaceCastModel IB z.proj).toContinuousLinearMap :
      (EB →L[𝕜] TangentSpace (IB.prod IF) z) →L[𝕜]
        (TangentSpace IB z.proj →L[𝕜] TangentSpace (IB.prod IF) z)).continuous.comp
      ((ContinuousLinearMap.postcomp EB
        (tangentSpaceCastModel (IB.prod IF) z).symm.toContinuousLinearMap :
        (EB →L[𝕜] EB × EF) →L[𝕜] (EB →L[𝕜] TangentSpace (IB.prod IF) z)).continuous.comp hprod)
@[simp] theorem coe_modelHomeomorphAt (z : ManifoldTotalSpace F E) :
    (modelHomeomorphAt z : FiberFirstJet IB IF F E z → (EB →L[𝕜] EF)) = modelEquivAt z := (rfl)

instance : VAdd (TangentSpace IB z.proj →L[𝕜] VerticalSpace IB IF F E z)
    (FiberFirstJet IB IF F E z) where
  vadd φ j :=
    { toContinuousLinearMap := (VerticalSpace.toTangent z).comp φ + j.toContinuousLinearMap
      mfderiv_proj_comp := by
        ext u; simp [VerticalSpace.mfderiv_proj_toTangent, j.mfderiv_proj_apply] }
@[simp] theorem vadd_apply (φ : TangentSpace IB z.proj →L[𝕜] VerticalSpace IB IF F E z)
    (j : FiberFirstJet IB IF F E z) (u : TangentSpace IB z.proj) :
    (φ +ᵥ j) u = VerticalSpace.toTangent z (φ u) + j u := (rfl)
instance : VSub (TangentSpace IB z.proj →L[𝕜] VerticalSpace IB IF F E z)
    (FiberFirstJet IB IF F E z) where
  vsub j₁ j₂ := VerticalSpace.liftCLM (j₁.toContinuousLinearMap - j₂.toContinuousLinearMap)
    fun u ↦ by simp [j₁.mfderiv_proj_apply, j₂.mfderiv_proj_apply]
@[simp] theorem toTangent_vsub_apply (j₁ j₂ : FiberFirstJet IB IF F E z)
    (u : TangentSpace IB z.proj) :
    VerticalSpace.toTangent z ((j₁ -ᵥ j₂) u) = j₁ u - j₂ u := VerticalSpace.toTangent_liftCLM _ _ u
instance : AddTorsor (TangentSpace IB z.proj →L[𝕜] VerticalSpace IB IF F E z)
    (FiberFirstJet IB IF F E z) where
  zero_vadd j := by ext u; simp
  add_vadd φ ψ j := by ext u; simp [add_assoc]
  vsub_vadd' j₁ j₂ := by ext u; simp [sub_add_cancel]
  vadd_vsub' φ j := by ext u; simp

/-- The **vertical contact projection** sending `w ∈ T_z E` to `w - j (dπ_z w) ∈ V_z E`. -/
def contactProj (j : FiberFirstJet IB IF F E z) :
    TangentSpace (IB.prod IF) z →L[𝕜] VerticalSpace IB IF F E z :=
  VerticalSpace.liftCLM
    (ContinuousLinearMap.id 𝕜 (TangentSpace (IB.prod IF) z) -
      j.toContinuousLinearMap.comp (mfderiv (IB.prod IF) IB ManifoldTotalSpace.proj z))
    fun w ↦ by simp [j.mfderiv_proj_apply]
@[simp] theorem toTangent_contactProj (j : FiberFirstJet IB IF F E z)
    (w : TangentSpace (IB.prod IF) z) : VerticalSpace.toTangent z (j.contactProj w) =
      w - j (mfderiv (IB.prod IF) IB ManifoldTotalSpace.proj z w) :=
  VerticalSpace.toTangent_liftCLM _ _ w
@[simp] theorem contactProj_toTangent (j : FiberFirstJet IB IF F E z)
    (v : VerticalSpace IB IF F E z) :
    j.contactProj (VerticalSpace.toTangent z v) = v := VerticalSpace.ext (by simp)
@[simp] theorem contactProj_apply_self (j : FiberFirstJet IB IF F E z)
    (u : TangentSpace IB z.proj) : j.contactProj (j u) = 0 := VerticalSpace.ext (by simp)
theorem ker_contactProj (j : FiberFirstJet IB IF F E z) :
    LinearMap.ker j.contactProj.toLinearMap =
      LinearMap.range j.toContinuousLinearMap.toLinearMap := by
  ext w; simp only [LinearMap.mem_ker, LinearMap.mem_range, ContinuousLinearMap.coe_coe,
    toContinuousLinearMap_apply]
  refine ⟨fun hw ↦ ⟨mfderiv (IB.prod IF) IB ManifoldTotalSpace.proj z w, ?_⟩, ?_⟩
  · have h0 : VerticalSpace.toTangent z (j.contactProj w) = 0 := by rw [hw, map_zero]
    rw [toTangent_contactProj, sub_eq_zero] at h0; exact h0.symm
  · rintro ⟨u, rfl⟩; exact j.contactProj_apply_self u

/-- Direct-sum splitting `T_z E ≃L[𝕜] T_{π(z)} B × V_z E` determined by a first jet `j`. -/
def splittingEquiv (j : FiberFirstJet IB IF F E z) :
    TangentSpace (IB.prod IF) z ≃L[𝕜] TangentSpace IB z.proj × VerticalSpace IB IF F E z :=
  ContinuousLinearEquiv.equivOfInverse
    ((mfderiv (IB.prod IF) IB ManifoldTotalSpace.proj z).prod j.contactProj)
    (j.toContinuousLinearMap.comp (ContinuousLinearMap.fst 𝕜 _ _) +
      (VerticalSpace.toTangent z).comp (ContinuousLinearMap.snd 𝕜 _ _))
    (fun w ↦ by simp) (fun ⟨u, v⟩ ↦ by ext <;> simp)
@[simp] theorem splittingEquiv_apply (j : FiberFirstJet IB IF F E z)
    (w : TangentSpace (IB.prod IF) z) : j.splittingEquiv w =
      (mfderiv (IB.prod IF) IB ManifoldTotalSpace.proj z w, j.contactProj w) := (rfl)
@[simp] theorem splittingEquiv_symm_apply (j : FiberFirstJet IB IF F E z)
    (p : TangentSpace IB z.proj × VerticalSpace IB IF F E z) :
    j.splittingEquiv.symm p = j p.1 + VerticalSpace.toTangent z p.2 := (rfl)
end Carrier

section Bundle
variable [IsManifold IB 1 B] [IsManifold IF 1 F] [ContMDiffFiberBundle 1 F E IB IF]

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
@[simp] theorem coordAt_apply (i : ManifoldTotalSpace F E) {z : ManifoldTotalSpace F E}
    (j : FiberFirstJet IB IF F E z) (u : EB) : coordAt i j u =
      ((trivializationAt (EB × EF) (TangentSpace (IB.prod IF)) i).continuousLinearMapAt 𝕜 z
        (j ((trivializationAt EB (TangentSpace IB) i.proj).symmL 𝕜 z.proj u))).2 := (rfl)
@[simp] theorem coordAt_self (z : ManifoldTotalSpace F E) (j : FiberFirstJet IB IF F E z) :
    coordAt z j = modelEquivAt z j := by
  ext u; rw [coordAt_apply, modelEquivAt_apply, TauCeti.Manifold.symmL_trivializationAt_self,
    TauCeti.Manifold.continuousLinearMapAt_trivializationAt_self]; rfl

/-- Reconstruct a first jet at `z` from its derivative coordinate `A` in chart `i`. -/
def ofCoordAt {i z : ManifoldTotalSpace F E} (hz : z ∈ (chartAt (ModelProd HB HF) i).source)
    (A : EB →L[𝕜] EF) : FiberFirstJet IB IF F E z where
  toContinuousLinearMap :=
    ((trivializationAt (EB × EF) (TangentSpace (IB.prod IF)) i).symmL 𝕜 z).comp
      (((ContinuousLinearMap.id 𝕜 EB).prod A).comp
        ((trivializationAt EB (TangentSpace IB) i.proj).continuousLinearMapAt 𝕜 z.proj))
  mfderiv_proj_comp := by
    have hbi := (ManifoldTotalSpace.proj_mem_of_mem_chartAt_source hz).2
    ext v; simp only [comp_apply, id_apply]
    set u := (trivializationAt EB (TangentSpace IB) i.proj).continuousLinearMapAt 𝕜 z.proj v
    have hfst := ManifoldTotalSpace.fst_continuousLinearMapAt_tangent hz
      ((trivializationAt (EB × EF) (TangentSpace (IB.prod IF)) i).symmL 𝕜 z (u, A u))
    rw [(trivializationAt (EB × EF) (TangentSpace (IB.prod IF)) i).continuousLinearMapAt_symmL
      hz] at hfst
    have h0 := congrArg ((trivializationAt EB (TangentSpace IB) i.proj).symmL 𝕜 z.proj) hfst.symm
    rwa [(trivializationAt EB (TangentSpace IB) i.proj).symmL_continuousLinearMapAt hbi,
      (trivializationAt EB (TangentSpace IB) i.proj).symmL_continuousLinearMapAt hbi] at h0
@[simp] theorem ofCoordAt_apply {i z : ManifoldTotalSpace F E}
    (hz : z ∈ (chartAt (ModelProd HB HF) i).source) (A : EB →L[𝕜] EF)
    (v : TangentSpace IB z.proj) :
    ofCoordAt hz A v = (trivializationAt (EB × EF) (TangentSpace (IB.prod IF)) i).symmL 𝕜 z
      (((ContinuousLinearMap.id 𝕜 EB).prod A)
        ((trivializationAt EB (TangentSpace IB) i.proj).continuousLinearMapAt 𝕜 z.proj v)) := (rfl)
@[simp] theorem coordAt_ofCoordAt {i z : ManifoldTotalSpace F E}
    (hz : z ∈ (chartAt (ModelProd HB HF) i).source) (A : EB →L[𝕜] EF) :
    coordAt i (ofCoordAt (IB := IB) (IF := IF) hz A) = A := by
  ext u; rw [coordAt_apply, ofCoordAt_apply,
    (trivializationAt EB (TangentSpace IB) i.proj).continuousLinearMapAt_symmL
      (ManifoldTotalSpace.proj_mem_of_mem_chartAt_source hz).2,
    (trivializationAt (EB × EF) (TangentSpace (IB.prod IF)) i).continuousLinearMapAt_symmL hz]; rfl
@[simp] theorem ofCoordAt_coordAt {i z : ManifoldTotalSpace F E}
    (hz : z ∈ (chartAt (ModelProd HB HF) i).source) (j : FiberFirstJet IB IF F E z) :
    ofCoordAt hz (coordAt i j) = j := by
  have hbi := (ManifoldTotalSpace.proj_mem_of_mem_chartAt_source hz).2; ext v; rw [ofCoordAt_apply]
  set eT := trivializationAt (EB × EF) (TangentSpace (IB.prod IF)) i
  set eB := trivializationAt EB (TangentSpace IB) i.proj
  set u := eB.continuousLinearMapAt 𝕜 z.proj v
  have hv : eB.symmL 𝕜 z.proj u = v := eB.symmL_continuousLinearMapAt hbi v
  rw [show ((ContinuousLinearMap.id 𝕜 EB).prod (coordAt i j)) u =
        eT.continuousLinearMapAt 𝕜 z (j v) from Prod.ext
      (by rw [ContinuousLinearMap.prod_apply, id_apply,
            ← continuousLinearMapAt_apply_symmL_fst hz j u, hv])
      (by rw [ContinuousLinearMap.prod_apply, coordAt_apply, hv]),
    eT.symmL_continuousLinearMapAt hz]

/-- Nonlinear first-jet coordinate change from chart `i` to chart `k` at `z`. -/
def coordChange (i k z : ManifoldTotalSpace F E) (A : EB →L[𝕜] EF) : EB →L[𝕜] EF :=
  (ContinuousLinearMap.snd 𝕜 EB EF).comp
    ((tangentCoordChange (IB.prod IF) i k z).comp
      (((ContinuousLinearMap.id 𝕜 EB).prod A).comp (tangentCoordChange IB k.proj i.proj z.proj)))
@[simp] theorem coordChange_apply (i k z : ManifoldTotalSpace F E) (A : EB →L[𝕜] EF) (u : EB) :
    coordChange (IB := IB) (IF := IF) (F := F) (E := E) i k z A u =
      (tangentCoordChange (IB.prod IF) i k z
        (tangentCoordChange IB k.proj i.proj z.proj u,
          A (tangentCoordChange IB k.proj i.proj z.proj u))).2 := (rfl)
theorem coordChange_sub (i k z : ManifoldTotalSpace F E) (A₁ A₂ : EB →L[𝕜] EF) :
    coordChange (IB := IB) (IF := IF) (F := F) (E := E) i k z A₁ -
        coordChange (IB := IB) (IF := IF) (F := F) (E := E) i k z A₂ =
      (VerticalSpace.coordChange (IB := IB) (IF := IF) (F := F) (E := E) i k z).comp
        ((A₁ - A₂).comp (tangentCoordChange IB k.proj i.proj z.proj)) := by
  ext u; simp only [sub_apply, coordChange_apply, comp_apply, VerticalSpace.coordChange_apply]
  have hsub : (tangentCoordChange IB k.proj i.proj z.proj u,
        A₁ (tangentCoordChange IB k.proj i.proj z.proj u)) -
      (tangentCoordChange IB k.proj i.proj z.proj u,
        A₂ (tangentCoordChange IB k.proj i.proj z.proj u)) =
      (0, A₁ (tangentCoordChange IB k.proj i.proj z.proj u) -
        A₂ (tangentCoordChange IB k.proj i.proj z.proj u)) := by ext <;> simp
  rw [← hsub, map_sub, Prod.snd_sub]
theorem coordAt_ofCoordAt_eq_coordChange {i k z : ManifoldTotalSpace F E}
    (hi : z ∈ (chartAt (ModelProd HB HF) i).source)
    (hk : z ∈ (chartAt (ModelProd HB HF) k).source) (A : EB →L[𝕜] EF) :
    coordAt k (ofCoordAt (IB := IB) (IF := IF) hi A) =
      coordChange (IB := IB) (IF := IF) (F := F) (E := E) i k z A := by
  ext u; rw [coordAt_apply, ofCoordAt_apply,
    TauCeti.Manifold.continuousLinearMapAt_symmL_coordChange
      (ManifoldTotalSpace.proj_mem_of_mem_chartAt_source hk).2
      (ManifoldTotalSpace.proj_mem_of_mem_chartAt_source hi).2,
    TauCeti.Manifold.continuousLinearMapAt_symmL_coordChange hi hk]; rfl

theorem coordChange_eq_firstJetCoordChange [IB.Boundaryless] [IF.Boundaryless]
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
  have hi' : z ∈ (extChartAt (IB.prod IF) i).source := (extChartAt_source (IB.prod IF) i).symm ▸ hi
  have hk' : z ∈ (extChartAt (IB.prod IF) k).source := (extChartAt_source (IB.prod IF) k).symm ▸ hk
  have hbi : z.proj ∈ (extChartAt IB i.proj).source :=
    (extChartAt_source IB i.proj).symm ▸ (ManifoldTotalSpace.proj_mem_of_mem_chartAt_source hi).2
  have hbk : z.proj ∈ (extChartAt IB k.proj).source :=
    (extChartAt_source IB k.proj).symm ▸ (ManifoldTotalSpace.proj_mem_of_mem_chartAt_source hk).2
  have hpair : (h (extChartAt IB k.proj z.proj), (extChartAt (IB.prod IF) i z).2) =
      extChartAt (IB.prod IF) i z := Prod.ext (by
    dsimp only [h]; rw [Function.comp_apply, (extChartAt IB k.proj).left_inv hbk,
      ManifoldTotalSpace.extChartAt_fst_eq hi]) rfl
  have hh_deriv : HasFDerivAt h (tangentCoordChange IB k.proj i.proj z.proj)
      (extChartAt IB k.proj z.proj) := by
    have hd := hasFDerivWithinAt_tangentCoordChange (I := IB) ⟨hbk, hbi⟩
    rwa [IB.range_eq_univ, hasFDerivWithinAt_univ] at hd
  have hT_deriv : HasFDerivAt (extChartAt (IB.prod IF) k ∘ (extChartAt (IB.prod IF) i).symm)
      (tangentCoordChange (IB.prod IF) i k z) (extChartAt (IB.prod IF) i z) := by
    have hd := hasFDerivWithinAt_tangentCoordChange (I := IB.prod IF) ⟨hi', hk'⟩
    rwa [(IB.prod IF).range_eq_univ, hasFDerivWithinAt_univ] at hd
  let pt : EB × EF := (extChartAt IB k.proj z.proj, (extChartAt (IB.prod IF) i z).2)
  have hinner : HasFDerivAt (fun q : EB × EF ↦ (h q.1, q.2)) _ pt :=
    (hh_deriv.comp pt (hasFDerivAt_fst (𝕜 := 𝕜) (E := EB) (F := EF))).prodMk
      (hasFDerivAt_snd (𝕜 := 𝕜) (E := EB) (F := EF))
  have hmid := (hpair.symm ▸ hT_deriv).comp pt hinner
  have hg_deriv : HasFDerivAt g _ pt := (hasFDerivAt_snd (𝕜 := 𝕜) (E := EB) (F := EF)).comp pt hmid
  ext u; rw [firstJetCoordChange_snd_apply, hg_deriv.fderiv, hh_deriv.fderiv]; rfl

omit [IsManifold IB 1 B] [IsManifold IF 1 F] [ContMDiffFiberBundle 1 F E IB IF] in
theorem contMDiffOn_coordChange {n : ℕ∞ω} [IsManifold IB (n + 1) B] [IsManifold IF (n + 1) F]
    [ContMDiffFiberBundle (n + 1) F E IB IF] (i k : ManifoldTotalSpace F E) :
    haveI : IsManifold IB 1 B := .of_le (n := n + 1) le_add_self
    haveI : IsManifold IF 1 F := .of_le (n := n + 1) le_add_self
    haveI : ContMDiffFiberBundle 1 F E IB IF := .of_le (n := n + 1) le_add_self
    ContMDiffOn ((IB.prod IF).prod 𝓘(𝕜, EB →L[𝕜] EF)) 𝓘(𝕜, EB →L[𝕜] EF) n
      (fun p : ManifoldTotalSpace F E × (EB →L[𝕜] EF) ↦
        coordChange (IB := IB) (IF := IF) (F := F) (E := E) i k p.1 p.2)
      (((chartAt (ModelProd HB HF) i).source ∩ (chartAt (ModelProd HB HF) k).source) ×ˢ univ) := by
  have : IsManifold IB 1 B := .of_le (n := n + 1) le_add_self
  have : IsManifold IF 1 F := .of_le (n := n + 1) le_add_self
  have : ContMDiffFiberBundle 1 F E IB IF := .of_le (n := n + 1) le_add_self
  have : IsManifold IB n B := .of_le (n := n + 1) le_self_add
  have : IsManifold IF n F := .of_le (n := n + 1) le_self_add
  have : ContMDiffFiberBundle n F E IB IF := .of_le (n := n + 1) le_self_add
  set S := ((chartAt (ModelProd HB HF) i).source ∩ (chartAt (ModelProd HB HF) k).source) ×ˢ
    (univ : Set (EB →L[𝕜] EF))
  have hfst : ContMDiffOn ((IB.prod IF).prod 𝓘(𝕜, EB →L[𝕜] EF)) (IB.prod IF) n Prod.fst S :=
    contMDiffOn_fst
  have hTE := ((tangentBundleCore.isContMDiff (I := IB.prod IF) (M := ManifoldTotalSpace F E)
    (n := n)).1 (achart _ i) (achart _ k)).comp hfst fun _ hp ↦ hp.1
  have hproj : ContMDiff (IB.prod IF) IB n (ManifoldTotalSpace.proj : ManifoldTotalSpace F E → B) :=
    (ManifoldTotalSpace.contMDiff_proj n F E IB IF).congr fun z ↦
      (ManifoldTotalSpace.homeomorph_symm_proj z).symm
  have hTB := ((tangentBundleCore.isContMDiff (I := IB) (M := B) (n := n)).1
    (achart _ k.proj) (achart _ i.proj)).comp (hproj.comp_contMDiffOn hfst)
    fun _ hp ↦ ⟨(ManifoldTotalSpace.proj_mem_of_mem_chartAt_source hp.1.2).2,
      (ManifoldTotalSpace.proj_mem_of_mem_chartAt_source hp.1.1).2⟩
  have heq : (fun p : ManifoldTotalSpace F E × (EB →L[𝕜] EF) ↦
        (ContinuousLinearMap.id 𝕜 EB).prod p.2) =
      fun p ↦ ContinuousLinearMap.inl 𝕜 EB EF + (ContinuousLinearMap.inr 𝕜 EB EF).comp p.2 :=
    funext fun _ ↦ by ext <;> simp
  have hprod : ContMDiffOn ((IB.prod IF).prod 𝓘(𝕜, EB →L[𝕜] EF)) 𝓘(𝕜, EB →L[𝕜] EB × EF) n
      (fun p : ManifoldTotalSpace F E × (EB →L[𝕜] EF) ↦
        (ContinuousLinearMap.id 𝕜 EB).prod p.2) S :=
    heq ▸ contMDiffOn_const.add (contMDiffOn_const.clm_comp contMDiffOn_snd)
  exact contMDiffOn_const.clm_comp (hTE.clm_comp (hprod.clm_comp hTB))

open Classical in
/-- Local pretrivialization of `FiberFirstJet IB IF F E` over the chart domain of `i`. -/
def pretrivializationAt (i : ManifoldTotalSpace F E) :
    Pretrivialization (EB →L[𝕜] EF) (π (EB →L[𝕜] EF) (FiberFirstJet IB IF F E)) where
  toFun p := (p.proj, coordAt i p.2)
  invFun q := if hq : q.1 ∈ (chartAt (ModelProd HB HF) i).source then ⟨q.1, ofCoordAt hq q.2⟩
    else ⟨q.1, default⟩
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
@[simp] theorem pretrivializationAt_apply (i : ManifoldTotalSpace F E)
    (p : TotalSpace (EB →L[𝕜] EF) (FiberFirstJet IB IF F E)) :
    pretrivializationAt i p = (p.proj, coordAt i p.2) := (rfl)
theorem pretrivializationAt_symm_eq {i z : ManifoldTotalSpace F E}
    (hz : z ∈ (chartAt (ModelProd HB HF) i).source) (A : EB →L[𝕜] EF) :
    (pretrivializationAt (IB := IB) (IF := IF) (F := F) (E := E) i).toPartialEquiv.symm (z, A) =
      ⟨z, ofCoordAt hz A⟩ := dite_eq_left hz

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
      rw [mem_preimage, pretrivializationAt_symm_eq hz_i] at hz_k; exact ⟨⟨hz_i, hz_k⟩, mem_univ _⟩
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
@[simp] theorem trivializationAt_baseSet (i : ManifoldTotalSpace F E) :
    (trivializationAt (EB →L[𝕜] EF) (FiberFirstJet IB IF F E) i).baseSet =
      (chartAt (ModelProd HB HF) i).source := (rfl)
@[simp] theorem trivializationAt_apply (i : ManifoldTotalSpace F E)
    (p : TotalSpace (EB →L[𝕜] EF) (FiberFirstJet IB IF F E)) :
    trivializationAt (EB →L[𝕜] EF) (FiberFirstJet IB IF F E) i p = (p.proj, coordAt i p.2) := (rfl)

omit [IsManifold IB 1 B] [IsManifold IF 1 F] [ContMDiffFiberBundle 1 F E IB IF] in
theorem contMDiffFiberBundle {n : ℕ∞ω} [IsManifold IB (n + 1) B] [IsManifold IF (n + 1) F]
    [ContMDiffFiberBundle (n + 1) F E IB IF] :
    haveI : IsManifold IB 1 B := .of_le (n := n + 1) le_add_self
    haveI : IsManifold IF 1 F := .of_le (n := n + 1) le_add_self
    haveI : ContMDiffFiberBundle 1 F E IB IF := .of_le (n := n + 1) le_add_self
    ContMDiffFiberBundle n (EB →L[𝕜] EF) (FiberFirstJet IB IF F E)
      (IB.prod IF) 𝓘(𝕜, EB →L[𝕜] EF) := by
  have : IsManifold IB 1 B := .of_le (n := n + 1) le_add_self
  have : IsManifold IF 1 F := .of_le (n := n + 1) le_add_self
  have : ContMDiffFiberBundle 1 F E IB IF := .of_le (n := n + 1) le_add_self
  refine ⟨fun e e' he he' ↦ ?_⟩
  obtain ⟨_, ⟨i, rfl⟩, rfl⟩ := he.out; obtain ⟨_, ⟨k, rfl⟩, rfl⟩ := he'.out
  refine (contMDiffOn_coordChange (IB := IB) (IF := IF) (F := F) (E := E) (n := n) i k).congr ?_
  rintro ⟨z, A⟩ ⟨⟨hz_i, hz_k⟩, -⟩
  change (pretrivializationAt k ((pretrivializationAt i).toPartialEquiv.symm (z, A))).2 = _
  rw [pretrivializationAt_symm_eq hz_i, pretrivializationAt_apply,
    coordAt_ofCoordAt_eq_coordChange hz_i hz_k]
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
theorem mk_eq_mk_iff_modelEquivAt {z₁ z₂ : ManifoldTotalSpace F E}
    {j₁ : FiberFirstJet IB IF F E z₁} {j₂ : FiberFirstJet IB IF F E z₂} :
    (⟨z₁, j₁⟩ : FiberFirstJetBundle IB IF F E) = ⟨z₂, j₂⟩ ↔
      z₁ = z₂ ∧ FiberFirstJet.modelEquivAt z₁ j₁ = FiberFirstJet.modelEquivAt z₂ j₂ :=
  ⟨by rintro ⟨⟩; exact ⟨rfl, rfl⟩, fun ⟨rfl, h⟩ ↦
    congrArg (TotalSpace.mk' _ z₁) ((FiberFirstJet.modelEquivAt z₁).injective h)⟩

/-- The target projection `π_{1,0} : J¹E → E` onto `ManifoldTotalSpace F E`. -/
def targetProj (p : FiberFirstJetBundle IB IF F E) : ManifoldTotalSpace F E := p.proj
/-- The source (base) projection `π_1 : J¹E → B` onto `B`. -/
def baseProj (p : FiberFirstJetBundle IB IF F E) : B := p.proj.proj
@[simp] theorem targetProj_apply (p : FiberFirstJetBundle IB IF F E) : targetProj p = p.proj :=
  (rfl)
@[simp] theorem baseProj_apply (p : FiberFirstJetBundle IB IF F E) : baseProj p = p.proj.proj :=
  (rfl)
theorem targetProj_eq_proj :
    (targetProj : FiberFirstJetBundle IB IF F E → ManifoldTotalSpace F E) = TotalSpace.proj := (rfl)
theorem baseProj_eq_proj_comp_targetProj :
    (baseProj : FiberFirstJetBundle IB IF F E → B) = ManifoldTotalSpace.proj ∘ targetProj := (rfl)
theorem targetProj_surjective :
    Function.Surjective (targetProj : FiberFirstJetBundle IB IF F E → ManifoldTotalSpace F E) :=
  fun z ↦ ⟨⟨z, default⟩, rfl⟩
theorem baseProj_surjective [Nonempty F] :
    Function.Surjective (baseProj : FiberFirstJetBundle IB IF F E → B) := fun b ↦
  let ⟨x, hx⟩ := FiberBundle.surjective_proj F E b
  ⟨⟨ManifoldTotalSpace.homeomorph F E x, default⟩, (ManifoldTotalSpace.proj_homeomorph x).trans hx⟩

section Structure
variable [IsManifold IB 1 B] [IsManifold IF 1 F] [ContMDiffFiberBundle 1 F E IB IF]

theorem mk_eq_mk_iff_coordAt {i z₁ z₂ : ManifoldTotalSpace F E}
    (hz₁ : z₁ ∈ (chartAt (ModelProd HB HF) i).source)
    {j₁ : FiberFirstJet IB IF F E z₁} {j₂ : FiberFirstJet IB IF F E z₂} :
    (⟨z₁, j₁⟩ : FiberFirstJetBundle IB IF F E) = ⟨z₂, j₂⟩ ↔
      z₁ = z₂ ∧ FiberFirstJet.coordAt i j₁ = FiberFirstJet.coordAt i j₂ := by
  refine ⟨by rintro ⟨⟩; exact ⟨rfl, rfl⟩, ?_⟩; rintro ⟨rfl, h⟩; apply congrArg (TotalSpace.mk' _ z₁)
  rw [← FiberFirstJet.ofCoordAt_coordAt hz₁ j₁, ← FiberFirstJet.ofCoordAt_coordAt hz₁ j₂, h]
theorem contMDiff_targetProj (n : ℕ∞ω) :
    ContMDiff ((IB.prod IF).prod 𝓘(𝕜, EB →L[𝕜] EF)) (IB.prod IF) n
      (targetProj : FiberFirstJetBundle IB IF F E → ManifoldTotalSpace F E) :=
  Bundle.contMDiff_proj (FiberFirstJet IB IF F E)
theorem contMDiff_baseProj (n : ℕ∞ω) :
    ContMDiff ((IB.prod IF).prod 𝓘(𝕜, EB →L[𝕜] EF)) IB n
      (baseProj : FiberFirstJetBundle IB IF F E → B) :=
  ((ManifoldTotalSpace.contMDiff_proj n F E IB IF).congr fun z ↦
    (ManifoldTotalSpace.homeomorph_symm_proj z).symm).comp (contMDiff_targetProj n)

omit [IsManifold IB 1 B] [IsManifold IF 1 F] [ContMDiffFiberBundle 1 F E IB IF] in
theorem isManifold {n : ℕ∞ω} [IsManifold IB (n + 1) B] [IsManifold IF (n + 1) F]
    [ContMDiffFiberBundle (n + 1) F E IB IF] :
    haveI : IsManifold IB 1 B := .of_le (n := n + 1) le_add_self
    haveI : IsManifold IF 1 F := .of_le (n := n + 1) le_add_self
    haveI : ContMDiffFiberBundle 1 F E IB IF := .of_le (n := n + 1) le_add_self
    IsManifold ((IB.prod IF).prod 𝓘(𝕜, EB →L[𝕜] EF)) n (FiberFirstJetBundle IB IF F E) := by
  have : IsManifold IB 1 B := .of_le (n := n + 1) le_add_self
  have : IsManifold IF 1 F := .of_le (n := n + 1) le_add_self
  have : ContMDiffFiberBundle 1 F E IB IF := .of_le (n := n + 1) le_add_self
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

/-- Pointwise **Cartan contact form** `θ_p : T_p(J¹E) →L[𝕜] V_{π_{1,0}(p)} E`. -/
def contactFormAt (p : FiberFirstJetBundle IB IF F E) :
    TangentSpace ((IB.prod IF).prod 𝓘(𝕜, EB →L[𝕜] EF)) p →L[𝕜]
      VerticalSpace IB IF F E p.proj :=
  p.2.contactProj.comp
    (mfderiv ((IB.prod IF).prod 𝓘(𝕜, EB →L[𝕜] EF)) (IB.prod IF) TotalSpace.proj p)
@[simp] theorem toTangent_contactFormAt (p : FiberFirstJetBundle IB IF F E)
    (ξ : TangentSpace ((IB.prod IF).prod 𝓘(𝕜, EB →L[𝕜] EF)) p) :
    VerticalSpace.toTangent p.proj (contactFormAt p ξ) =
      mfderiv ((IB.prod IF).prod 𝓘(𝕜, EB →L[𝕜] EF)) (IB.prod IF) TotalSpace.proj p ξ -
        p.2 (mfderiv (IB.prod IF) IB ManifoldTotalSpace.proj p.proj
          (mfderiv ((IB.prod IF).prod 𝓘(𝕜, EB →L[𝕜] EF)) (IB.prod IF) TotalSpace.proj p ξ)) :=
  p.2.toTangent_contactProj _
end Structure
end FiberFirstJetBundle
end ManifoldFiber
end TauCeti
