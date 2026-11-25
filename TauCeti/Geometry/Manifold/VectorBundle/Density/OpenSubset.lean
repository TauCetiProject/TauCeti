/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Density
public import TauCeti.Geometry.Manifold.VectorBundle.Pullback

/-!
# Intrinsic densities on open subsets

The intrinsic density line of an open submanifold is smoothly identified with the pullback of
the ambient density line. The comparison uses the native tangent-frame identity. It also acts
on real bundle-dual densities with arbitrary normed model fibres.
-/

public noncomputable section

open Bundle FiberBundle Filter Set Topology TopologicalSpace
open scoped Manifold ContDiff
universe u v
namespace TauCeti.DensityBundle
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type v} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {U : Opens M}

/-- Canonical identification of intrinsic and ambient densities over an open subset. -/
def openEquiv (x : U) :
    TauCeti.DensityBundle I U x ≃L[ℝ] TauCeti.DensityBundle I M (x : M) :=
  ContinuousLinearEquiv.refl ℝ _

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
/-- The open density comparison keeps the underlying density functional. -/
@[simp]
theorem openEquiv_apply (x : U) (μ : TauCeti.DensityBundle I U x) :
    openEquiv x μ = μ := by rfl

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
/-- The inverse open density comparison keeps the underlying density functional. -/
@[simp]
theorem openEquiv_symm_apply (x : U) (μ : TauCeti.DensityBundle I M (x : M)) :
    (openEquiv x).symm μ = μ := by rfl

/-- The open density comparison preserves preferred tangent-frame evaluations locally. -/
theorem eventually_open_frame_eq (x : U) :
    ∀ᶠ y in nhds x, ∀ μ : TauCeti.DensityBundle I U y,
      (openEquiv (I := I) y μ)
        (fun i ↦ (trivializationAt E (TangentSpace I : M → Type _) (x : M)).symm
          (y : M) (Module.finBasis ℝ E i)) =
      μ (fun i ↦ (trivializationAt E (TangentSpace I : U → Type _) x).symm
        y (Module.finBasis ℝ E i)) := by
  filter_upwards [TauCeti.Manifold.eventually_tangentSpaceOpenEquiv_symmL_trivializationAt_eq
    (I := I) x,
    (trivializationAt E (TangentSpace I : U → Type _) x).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt E (TangentSpace I : U → Type _) x),
    continuousAt_subtypeVal.eventually
      ((trivializationAt E (TangentSpace I : M → Type _) (x : M)).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt E (TangentSpace I : M → Type _) (x : M)))]
      with y hy hyU hyM
  intro μ
  apply congrArg μ
  funext i
  simpa only [Trivialization.symmL_apply (trivializationAt E (TangentSpace I : U → Type _) x) hyU,
    Trivialization.symmL_apply (trivializationAt E (TangentSpace I : M → Type _) (x : M)) hyM,
    TauCeti.Manifold.tangentSpaceOpenEquiv_apply] using (hy (Module.finBasis ℝ E i)).symm

/-- Smoothness of the open density comparison over the base inclusion. -/
theorem contMDiff_openInclusion :
    ContMDiff (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ)) ∞
      (fun p : TotalSpace ℝ (TauCeti.DensityBundle I U) ↦
        TotalSpace.mk' ℝ (E := TauCeti.DensityBundle I M) (p.proj : M)
          (openEquiv p.proj p.snd)) := by
  intro p
  rw [Bundle.contMDiffAt_totalSpace_iff]
  refine ⟨contMDiff_subtypeVal.contMDiffAt.comp p
    (contMDiffAt_proj (E := TauCeti.DensityBundle I U)), ?_⟩
  have hc := (Bundle.contMDiffAt_totalSpace_iff.mp
    (contMDiffAt_id (I := I.prod 𝓘(ℝ)) (x := p) (n := ∞))).2
  refine hc.congr_of_eventuallyEq ?_
  have h := ((FiberBundle.continuous_proj ℝ (TauCeti.DensityBundle I U)).continuousAt).eventually
    (eventually_open_frame_eq (I := I) p.proj)
  filter_upwards [h] with q hq
  simpa only [Function.id_def, TauCeti.Density.trivializationAt_eq,
    Trivialization.density_apply] using hq q.snd


private abbrev pulledDensity :=
  (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ (TauCeti.DensityBundle I M)

/-- Smoothness of intrinsic-to-pullback density transport. -/
theorem contMDiff_openToPullback :
    let c : C(U, M) := ⟨Subtype.val, continuous_subtypeVal⟩
    ContMDiff (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ)) ∞
      (fun p : TotalSpace ℝ (TauCeti.DensityBundle I U) ↦
        TotalSpace.mk' ℝ (E := (c *ᵖ (TauCeti.DensityBundle I M))) p.proj
          (openEquiv p.proj p.snd)) := by
  intro c
  apply (Bundle.Pullback.contMDiff_iff c
    (show ContMDiff I I ∞ c from contMDiff_subtypeVal)).2
  exact ⟨contMDiff_proj _, contMDiff_openInclusion⟩

/-- Smoothness of pullback-to-intrinsic density transport. -/
theorem contMDiff_openFromPullback :
    let c : C(U, M) := ⟨Subtype.val, continuous_subtypeVal⟩
    ContMDiff (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ)) ∞
      (fun p : TotalSpace ℝ ((c *ᵖ (TauCeti.DensityBundle I M))) ↦
        TotalSpace.mk' ℝ (E := TauCeti.DensityBundle I U) p.proj
          ((openEquiv p.proj).symm p.snd)) := by
  intro c p
  rw [Bundle.contMDiffAt_totalSpace_iff]
  refine ⟨contMDiffAt_proj _, ?_⟩
  have hc := (Bundle.contMDiffAt_totalSpace_iff.mp
    ((Pullback.contMDiff_lift (I := I) (I' := I) (n := ∞) c
      contMDiff_subtypeVal).contMDiffAt (x := p))).2
  refine hc.congr_of_eventuallyEq ?_
  have h := (FiberBundle.continuous_proj ℝ
    (pulledDensity (I := I) (U := U))).continuousAt.eventually
    (eventually_open_frame_eq (I := I) p.proj)
  filter_upwards [h] with q hq
  simp only [TauCeti.Density.trivializationAt_eq, Trivialization.density_apply]
  -- The density trivialization evaluates on this tangent frame; pullback lift keeps its value.
  change (((openEquiv q.proj).symm q.snd)
      (fun i ↦ (trivializationAt E (TangentSpace I : U → Type _) p.proj).symm
        q.proj (Module.finBasis ℝ E i))) =
    ((Pullback.lift ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)))) q).snd
      (fun i ↦ (trivializationAt E (TangentSpace I : M → Type _) (p.proj : M)).symm
      (q.proj : M) (Module.finBasis ℝ E i))
  exact (hq ((openEquiv q.proj).symm q.snd)).symm.trans (by rfl)

/-- The intrinsic density bundle of an open subset is diffeomorphic to the ambient pullback. -/
def openDiffeomorph :
    let c : C(U, M) := ⟨Subtype.val, continuous_subtypeVal⟩
    TotalSpace ℝ (TauCeti.DensityBundle I U) ≃ₘ^∞⟮I.prod 𝓘(ℝ), I.prod 𝓘(ℝ)⟯
      TotalSpace ℝ ((c *ᵖ (TauCeti.DensityBundle I M))) := by
  intro c
  exact
    { toFun p := ⟨p.proj, openEquiv p.proj p.snd⟩
      invFun p := ⟨p.proj, (openEquiv p.proj).symm p.snd⟩
      left_inv p := by cases p; rfl
      right_inv p := by cases p; rfl
      contMDiff_toFun := contMDiff_openToPullback
      contMDiff_invFun := contMDiff_openFromPullback }

/-- The density diffeomorphism preserves the open base point. -/
@[simp]
theorem openDiffeomorph_proj (p : TotalSpace ℝ (TauCeti.DensityBundle I U)) :
    dsimp% only [ContinuousMap.coe_mk] (
    (openDiffeomorph (I := I) p).proj = p.proj) := by rfl

/-- The density diffeomorphism acts by the fibre comparison. -/
@[simp]
theorem openDiffeomorph_snd (p : TotalSpace ℝ (TauCeti.DensityBundle I U)) :
    dsimp% only [ContinuousMap.coe_mk] (
    (openDiffeomorph (I := I) p).snd = openEquiv p.proj p.snd) := by rfl

/-- The inverse density diffeomorphism preserves the open base point. -/
@[simp]
theorem openDiffeomorph_symm_proj
    (p : TotalSpace ℝ ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ
      (TauCeti.DensityBundle I M))) :
    dsimp% only [ContinuousMap.coe_mk] (
    ((openDiffeomorph (I := I)).symm p).proj = p.proj) := by rfl

/-- The inverse density diffeomorphism acts by the inverse fibre comparison. -/
@[simp]
theorem openDiffeomorph_symm_snd
    (p : TotalSpace ℝ ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ
      (TauCeti.DensityBundle I M))) :
    dsimp% only [ContinuousMap.coe_mk] (
    ((openDiffeomorph (I := I)).symm p).snd = (openEquiv p.proj).symm p.snd) := by rfl

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]

/-- Intrinsic dual-density coefficients of a bundle restricted to an open subset. -/
abbrev localCoefficients := fun x : U ↦
  ((((⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M))) *ᵖ V) x →L[ℝ] TauCeti.DensityBundle I U x)
/-- Ambient dual-density coefficients of a bundle. -/
abbrev ambientCoefficients := fun x : M ↦ V x →L[ℝ] TauCeti.DensityBundle I M x

/-- Canonical open-subset comparison of real bundle-dual densities. -/
def openHomEquiv (x : U) :
    let c : C(U, M) := ⟨Subtype.val, continuous_subtypeVal⟩
    ((c *ᵖ V) x →L[ℝ] TauCeti.DensityBundle I U x) ≃L[ℝ]
      (V (x : M) →L[ℝ] TauCeti.DensityBundle I M (x : M)) :=
  let _c : C(U, M) := ⟨Subtype.val, continuous_subtypeVal⟩
  ContinuousLinearEquiv.arrowCongr (ContinuousLinearEquiv.refl ℝ _) (openEquiv x)

omit [ContMDiffVectorBundle ∞ F V I] in
/-- The open dual-density comparison agrees in preferred Hom frames locally. -/
theorem eventually_openHom_frame_eq (x : U) :
    let c : C(U, M) := ⟨Subtype.val, continuous_subtypeVal⟩
    ∀ᶠ y in nhds x, ∀ ℓ : (fun x : U ↦ (c *ᵖ V) x →L[ℝ] TauCeti.DensityBundle I U x) y,
      (trivializationAt (F →L[ℝ] ℝ) ((fun x : M ↦ V x →L[ℝ] TauCeti.DensityBundle I M x)) (x : M)
        (TotalSpace.mk' (F →L[ℝ] ℝ) (y : M) (openHomEquiv y ℓ))).2 =
      (trivializationAt (F →L[ℝ] ℝ) ((fun x : U ↦ (c *ᵖ V) x →L[ℝ] TauCeti.DensityBundle I U x)) x
        (TotalSpace.mk' (F →L[ℝ] ℝ) y ℓ)).2 := by
  intro c
  filter_upwards [eventually_open_frame_eq (I := I) x,
    continuousAt_subtypeVal.eventually
      ((trivializationAt F V (x : M)).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt F V (x : M))),
    (trivializationAt ℝ (TauCeti.DensityBundle I U) x).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt ℝ (TauCeti.DensityBundle I U) x),
    continuousAt_subtypeVal.eventually
      ((trivializationAt ℝ (TauCeti.DensityBundle I M) (x : M)).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt ℝ (TauCeti.DensityBundle I M) (x : M)))]
      with y hframe hyV hyDU hyDM
  intro ℓ
  rw [hom_trivializationAt_apply, hom_trivializationAt_apply]
  apply ContinuousLinearMap.ext
  intro v
  have hyVU : y ∈ (trivializationAt F (c *ᵖ V) x).baseSet := hyV
  have hsymm : (trivializationAt F (c *ᵖ V) x).symmL ℝ y v =
      (trivializationAt F V (x : M)).symmL ℝ (y : M) v := by
    rw [Trivialization.symmL_apply (trivializationAt F (c *ᵖ V) x) hyVU,
      Trivialization.symmL_apply (trivializationAt F V (x : M)) hyV]
    exact Trivialization.symm_pullback (trivializationAt F V (x : M))
      c hyV v
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
    Trivialization.continuousLinearMapAt_apply, Trivialization.linearMapAt_apply,
    ite_eq_left hyDU]
  erw [ite_eq_left hyDM]
  -- Express the tensor-Hom coordinate in the density trivialization after fibre evaluation.
  change ((trivializationAt ℝ (TauCeti.DensityBundle I M) (x : M))
    ⟨(y : M), openEquiv y (ℓ ((trivializationAt F V (x : M)).symmL ℝ (y : M) v))⟩).2 =
    ((trivializationAt ℝ (TauCeti.DensityBundle I U) x)
      ⟨y, ℓ ((trivializationAt F (c *ᵖ V) x).symmL ℝ y v)⟩).2
  rw [hsymm]
  simpa only [TauCeti.Density.trivializationAt_eq, Trivialization.density_apply] using
    hframe (ℓ ((trivializationAt F V (x : M)).symmL ℝ (y : M) v))

omit [ContMDiffVectorBundle ∞ F V I] in
/-- Smoothness of the open dual-density comparison over the inclusion. -/
theorem contMDiff_openHomInclusion :
    let c : C(U, M) := ⟨Subtype.val, continuous_subtypeVal⟩
    ContMDiff (I.prod 𝓘(ℝ, F →L[ℝ] ℝ)) (I.prod 𝓘(ℝ, F →L[ℝ] ℝ)) ∞
      (fun p : TotalSpace (F →L[ℝ] ℝ) ((fun x : U ↦ (c *ᵖ V) x →L[ℝ] TauCeti.DensityBundle I U x)) ↦
        TotalSpace.mk' (F →L[ℝ] ℝ) (E := (fun x : M ↦ V x →L[ℝ] TauCeti.DensityBundle I M x))
          (p.proj : M) (openHomEquiv p.proj p.snd)) := by
  intro c p
  rw [Bundle.contMDiffAt_totalSpace_iff]
  refine ⟨contMDiff_subtypeVal.contMDiffAt.comp p
    (contMDiffAt_proj (E := localCoefficients (I := I) (V := V) (U := U))), ?_⟩
  have hc := (Bundle.contMDiffAt_totalSpace_iff.mp
    (contMDiffAt_id (I := I.prod 𝓘(ℝ, F →L[ℝ] ℝ)) (x := p) (n := ∞))).2
  refine hc.congr_of_eventuallyEq ?_
  have h := (FiberBundle.continuous_proj (F →L[ℝ] ℝ)
    (localCoefficients (I := I) (V := V) (U := U))).continuousAt.eventually
      (eventually_openHom_frame_eq (I := I) (F := F) (V := V) (U := U) p.proj)
  filter_upwards [h] with q hq
  simpa only [Function.id_def] using hq q.snd

/-- The ambient dual-density coefficients pulled back to an open subset. -/
abbrev pulledAmbientCoefficients :=
  ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M))) *ᵖ (ambientCoefficients (I := I) (V := V))

omit [ContMDiffVectorBundle ∞ F V I] in
/-- Smoothness of intrinsic-to-pullback dual-density transport. -/
theorem contMDiff_openHomToPullback :
    let c : C(U, M) := ⟨Subtype.val, continuous_subtypeVal⟩
    ContMDiff (I.prod 𝓘(ℝ, F →L[ℝ] ℝ)) (I.prod 𝓘(ℝ, F →L[ℝ] ℝ)) ∞
      (fun p : TotalSpace (F →L[ℝ] ℝ) ((fun x : U ↦ (c *ᵖ V) x →L[ℝ] TauCeti.DensityBundle I U x)) ↦
        TotalSpace.mk' (F →L[ℝ] ℝ) (E := (c *ᵖ (fun x : M ↦ V x →L[ℝ] TauCeti.DensityBundle I M x)))
          p.proj (openHomEquiv p.proj p.snd)) := by
  intro c
  apply (Bundle.Pullback.contMDiff_iff c
    (show ContMDiff I I ∞ c from contMDiff_subtypeVal)).2
  exact ⟨contMDiff_proj _, contMDiff_openHomInclusion⟩

omit [ContMDiffVectorBundle ∞ F V I] in
/-- Smoothness of pullback-to-intrinsic dual-density transport. -/
theorem contMDiff_openHomFromPullback :
    let c : C(U, M) := ⟨Subtype.val, continuous_subtypeVal⟩
    ContMDiff (I.prod 𝓘(ℝ, F →L[ℝ] ℝ)) (I.prod 𝓘(ℝ, F →L[ℝ] ℝ)) ∞
      (fun p : TotalSpace (F →L[ℝ] ℝ) ((c *ᵖ (fun x : M ↦ V x →L[ℝ] TauCeti.DensityBundle I M x))) ↦
        TotalSpace.mk' (F →L[ℝ] ℝ) (E := (fun x : U ↦ (c *ᵖ V) x →L[ℝ] TauCeti.DensityBundle I U x))
          p.proj ((openHomEquiv p.proj).symm p.snd)) := by
  intro c p
  rw [Bundle.contMDiffAt_totalSpace_iff]
  refine ⟨contMDiffAt_proj _, ?_⟩
  have hc := (Bundle.contMDiffAt_totalSpace_iff.mp
    (contMDiffAt_id (I := I.prod 𝓘(ℝ, F →L[ℝ] ℝ)) (x := p) (n := ∞))).2
  refine hc.congr_of_eventuallyEq ?_
  have h := ((FiberBundle.continuous_proj (F →L[ℝ] ℝ)
    (pulledAmbientCoefficients (I := I) (V := V) (U := U))).continuousAt).eventually
      (eventually_openHom_frame_eq (I := I) (F := F) (V := V) (U := U) p.proj)
  filter_upwards [h] with q hq
  -- The common-frame identity compares the intrinsic coefficient with this ambient lift.
  change (trivializationAt (F →L[ℝ] ℝ) (localCoefficients (I := I) (V := V) (U := U)) p.proj
      ⟨q.proj, (openHomEquiv q.proj).symm q.snd⟩).2 =
    (trivializationAt (F →L[ℝ] ℝ) (ambientCoefficients (I := I) (V := V)) (p.proj : M)
      ⟨(q.proj : M), (Pullback.lift ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M))) q).snd⟩).2
  exact (hq ((openHomEquiv q.proj).symm q.snd)).symm.trans (by rfl)

/-- Intrinsic real bundle-dual densities are diffeomorphic to the ambient pullback. -/
@[expose] def openHomDiffeomorph :
    let c : C(U, M) := ⟨Subtype.val, continuous_subtypeVal⟩
    TotalSpace (F →L[ℝ] ℝ) ((fun x : U ↦ (c *ᵖ V) x →L[ℝ] TauCeti.DensityBundle I U x))
      ≃ₘ^∞⟮I.prod 𝓘(ℝ, F →L[ℝ] ℝ), I.prod 𝓘(ℝ, F →L[ℝ] ℝ)⟯
      TotalSpace (F →L[ℝ] ℝ) ((c *ᵖ (fun x : M ↦ V x →L[ℝ] TauCeti.DensityBundle I M x))) := by
  intro c
  exact
    { toFun p := ⟨p.proj, openHomEquiv p.proj p.snd⟩
      invFun p := ⟨p.proj, (openHomEquiv p.proj).symm p.snd⟩
      left_inv p := by cases p; rfl
      right_inv p := by cases p; rfl
      contMDiff_toFun := contMDiff_openHomToPullback
      contMDiff_invFun := contMDiff_openHomFromPullback }


omit [ContMDiffVectorBundle ∞ F V I] in
/-- The dual-density diffeomorphism preserves the open base point. -/
@[simp]
theorem openHomDiffeomorph_proj
    (p : TotalSpace (F →L[ℝ] ℝ) (localCoefficients (I := I) (V := V) (U := U))) :
    dsimp% only [ContinuousMap.coe_mk] (
    (openHomDiffeomorph (I := I) (F := F) (V := V) p).proj = p.proj) := by rfl

omit [ContMDiffVectorBundle ∞ F V I] in
/-- The dual-density diffeomorphism acts by the native fibre comparison. -/
@[simp]
theorem openHomDiffeomorph_snd
    (p : TotalSpace (F →L[ℝ] ℝ) (localCoefficients (I := I) (V := V) (U := U))) :
    dsimp% only [ContinuousMap.coe_mk] (
    (openHomDiffeomorph (I := I) (F := F) (V := V) p).snd = openHomEquiv p.proj p.snd) := by
  rfl

omit [ContMDiffVectorBundle ∞ F V I] in
/-- The inverse dual-density diffeomorphism preserves the open base point. -/
@[simp]
theorem openHomDiffeomorph_symm_proj
    (p : TotalSpace (F →L[ℝ] ℝ) (pulledAmbientCoefficients (I := I) (V := V) (U := U))) :
    dsimp% only [ContinuousMap.coe_mk] (
    ((openHomDiffeomorph (I := I) (F := F) (V := V)).symm p).proj = p.proj) := by rfl

omit [ContMDiffVectorBundle ∞ F V I] in
/-- The inverse dual-density diffeomorphism acts by the inverse native fibre comparison. -/
@[simp]
theorem openHomDiffeomorph_symm_snd
    (p : TotalSpace (F →L[ℝ] ℝ) (pulledAmbientCoefficients (I := I) (V := V) (U := U))) :
    dsimp% only [ContinuousMap.coe_mk] (
    ((openHomDiffeomorph (I := I) (F := F) (V := V)).symm p).snd =
      (openHomEquiv p.proj).symm p.snd) := by
  rfl


omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [ContMDiffVectorBundle ∞ F V I]
  [FiberBundle F V] [VectorBundle ℝ F V] [TopologicalSpace (TotalSpace F V)] in
/-- The open dual-density comparison preserves the underlying fibrewise linear functional. -/
-- Coercion simplification changes the open pullback carrier first; use presimplification.
@[simp↓]
theorem openHomEquiv_apply (x : U)
    (ℓ : ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V) x →L[ℝ]
      TauCeti.DensityBundle I U x) : openHomEquiv x ℓ = ℓ := by
  rfl

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [ContMDiffVectorBundle ∞ F V I]
  [FiberBundle F V] [VectorBundle ℝ F V] [TopologicalSpace (TotalSpace F V)] in
/-- The inverse open dual-density comparison has the same underlying fibrewise functional. -/
-- Coercion simplification changes the open pullback carrier first; use presimplification.
@[simp↓]
theorem openHomEquiv_symm_apply (x : U)
    (ℓ : V (x : M) →L[ℝ] TauCeti.DensityBundle I M (x : M)) :
    (openHomEquiv x).symm ℓ = ℓ := by
  rfl

end TauCeti.DensityBundle
