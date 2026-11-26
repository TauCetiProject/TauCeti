/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Density
public import TauCeti.Geometry.Manifold.VectorBundle.Pullback
public import TauCeti.Geometry.Manifold.VectorBundle.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.Pullback.Hom
import TauCeti.Geometry.Manifold.VectorBundle.TotalSpace.Basic

/-!
# Intrinsic densities on open subsets

On an open submanifold `U` of `M`, the intrinsic density line of `U` is identified with the
ambient density line pulled back along the inclusion: `TauCeti.DensityBundle.openEquiv` fibrewise
and `TauCeti.DensityBundle.openDiffeomorph` on total spaces, with target
`TauCeti.DensityBundle.pullbackAmbientDensity`. The same comparison identifies real bundle-dual
densities `openHomBundle` with `pullbackAmbientHomBundle`, for arbitrary normed model fibres
(`TauCeti.DensityBundle.openHomEquiv`, `TauCeti.DensityBundle.openHomDiffeomorph`), obtained by
post-composing with the density comparison and applying `Bundle.Pullback.homEquiv`. These
identifications let density-valued test data, and hence native bundle distributions, be
restricted to open subsets intrinsically.
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

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
private theorem contMDiff_subtypeVal_continuousMap :
    ContMDiff I I ∞ (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) :=
  contMDiff_subtypeVal

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
private theorem eventually_openEquiv_apply_trivializationAt_symm_eq (x : U) :
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

private theorem contMDiff_openEquiv_subtypeVal :
    ContMDiff (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ)) ∞
      (fun p : TotalSpace ℝ (TauCeti.DensityBundle I U) ↦
        TotalSpace.mk' ℝ (E := TauCeti.DensityBundle I M) (p.proj : M)
          (openEquiv p.proj p.snd)) := by
  refine Bundle.contMDiff_totalSpace_of_eventuallyEq (h := id)
    (contMDiff_subtypeVal.comp (contMDiff_proj _)) contMDiff_id fun p ↦ ?_
  filter_upwards [(FiberBundle.continuous_proj ℝ
    (TauCeti.DensityBundle I U)).continuousAt.eventually
    (eventually_openEquiv_apply_trivializationAt_symm_eq (I := I) p.proj)] with q hq
  simpa only [id, TauCeti.Density.trivializationAt_eq, Trivialization.density_apply] using hq q.snd

/-- The ambient density line pulled back to an open subset. -/
abbrev pullbackAmbientDensity :=
  (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ (TauCeti.DensityBundle I M)

private theorem contMDiff_openEquiv_pullback :
    ContMDiff (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ)) ∞
      (fun p : TotalSpace ℝ (TauCeti.DensityBundle I U) ↦
        TotalSpace.mk' ℝ (E := pullbackAmbientDensity (I := I) (U := U)) p.proj
          (openEquiv p.proj p.snd)) :=
  (Bundle.Pullback.contMDiff_iff _ contMDiff_subtypeVal_continuousMap).2
    ⟨contMDiff_proj _, contMDiff_openEquiv_subtypeVal⟩

/-- The intrinsic density bundle of an open subset is diffeomorphic to the ambient pullback. -/
def openDiffeomorph :
    TotalSpace ℝ (TauCeti.DensityBundle I U) ≃ₘ^∞⟮I.prod 𝓘(ℝ), I.prod 𝓘(ℝ)⟯
      TotalSpace ℝ (pullbackAmbientDensity (I := I) (U := U)) :=
  TauCeti.bundleDiffeomorph openEquiv contMDiff_openEquiv_pullback

/-- The density diffeomorphism acts by the fibre comparison over the same base point. -/
@[simp]
theorem openDiffeomorph_apply (p : TotalSpace ℝ (TauCeti.DensityBundle I U)) :
    openDiffeomorph (I := I) p = ⟨p.proj, openEquiv p.proj p.snd⟩ :=
  TauCeti.bundleDiffeomorph_apply _ _ p

/-- The inverse density diffeomorphism acts by the inverse fibre comparison. -/
@[simp]
theorem openDiffeomorph_symm_apply
    (p : TotalSpace ℝ (pullbackAmbientDensity (I := I) (U := U))) :
    (openDiffeomorph (I := I)).symm p = ⟨p.proj, (openEquiv p.proj).symm p.snd⟩ :=
  TauCeti.bundleDiffeomorph_symm_apply _ _ p

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]

/-- Real bundle-dual densities of a bundle restricted to an open subset. -/
abbrev openHomBundle := fun x : U ↦
  ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V) x →L[ℝ] TauCeti.DensityBundle I U x

/-- Ambient real bundle-dual densities. -/
abbrev ambientHomBundle := fun x : M ↦ V x →L[ℝ] TauCeti.DensityBundle I M x

/-- Ambient real bundle-dual densities pulled back to an open subset. -/
abbrev pullbackAmbientHomBundle :=
  (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ (ambientHomBundle (I := I) (V := V))

/-- Canonical open-subset comparison of real bundle-dual densities. -/
def openHomEquiv (x : U) :
    openHomBundle (I := I) (V := V) (U := U) x ≃L[ℝ] ambientHomBundle (I := I) (V := V) (x : M) :=
  ContinuousLinearEquiv.arrowCongr (ContinuousLinearEquiv.refl ℝ _) (openEquiv x)

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M]
  [FiberBundle F V] [VectorBundle ℝ F V] [TopologicalSpace (TotalSpace F V)] in
/-- The open dual-density comparison preserves the underlying fibrewise linear functional. -/
-- Coercion simplification changes the open pullback carrier first; use presimplification.
@[simp↓]
theorem openHomEquiv_apply (x : U)
    (ℓ : ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V) x →L[ℝ]
      TauCeti.DensityBundle I U x) : openHomEquiv x ℓ = ℓ := by
  rfl

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M]
  [FiberBundle F V] [VectorBundle ℝ F V] [TopologicalSpace (TotalSpace F V)] in
/-- The inverse open dual-density comparison has the same underlying fibrewise functional. -/
-- Coercion simplification changes the open pullback carrier first; use presimplification.
@[simp↓]
theorem openHomEquiv_symm_apply (x : U)
    (ℓ : V (x : M) →L[ℝ] TauCeti.DensityBundle I M (x : M)) :
    (openHomEquiv x).symm ℓ = ℓ := by
  rfl

/-- Near each point of the open subset, the open dual-density comparison does not change
coordinates in the preferred intrinsic and ambient Hom trivializations. -/
theorem eventually_openHomEquiv_trivializationAt_eq (x : U) :
    ∀ᶠ y in 𝓝 x, ∀ ℓ : openHomBundle (I := I) (V := V) (U := U) y,
      (trivializationAt (F →L[ℝ] ℝ) (ambientHomBundle (I := I) (V := V)) (x : M)
        ⟨(y : M), openHomEquiv y ℓ⟩).2 =
      (trivializationAt (F →L[ℝ] ℝ) (openHomBundle (I := I) (V := V) (U := U)) x ⟨y, ℓ⟩).2 := by
  let c : C(U, M) := ⟨Subtype.val, continuous_subtypeVal⟩
  filter_upwards [eventually_openEquiv_apply_trivializationAt_symm_eq (I := I) x,
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
    exact Trivialization.symm_pullback (trivializationAt F V (x : M)) c hyV v
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
    Trivialization.continuousLinearMapAt_apply, Trivialization.linearMapAt_apply,
    ite_eq_left hyDU]
  -- `filter_upwards` states `hyDM` through the density pretrivialization; restate it on the
  -- trivialization's base set as it appears in the goal.
  have hyDM' : (y : M) ∈ (trivializationAt ℝ (TauCeti.DensityBundle I M) (x : M)).baseSet := hyDM
  rw [ite_eq_left hyDM']
  -- Express the Hom coordinate in the density trivialization after fibre evaluation.
  change ((trivializationAt ℝ (TauCeti.DensityBundle I M) (x : M))
    ⟨(y : M), openEquiv y (ℓ ((trivializationAt F V (x : M)).symmL ℝ (y : M) v))⟩).2 =
    ((trivializationAt ℝ (TauCeti.DensityBundle I U) x)
      ⟨y, ℓ ((trivializationAt F (c *ᵖ V) x).symmL ℝ y v)⟩).2
  rw [hsymm]
  simpa only [TauCeti.Density.trivializationAt_eq, Trivialization.density_apply] using
    hframe (ℓ ((trivializationAt F V (x : M)).symmL ℝ (y : M) v))

/-- Real bundle-dual densities of the restricted bundle valued in the pulled-back ambient
densities. -/
private abbrev openPullbackHomBundle := fun x : U ↦
  ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V) x →L[ℝ]
    pullbackAmbientDensity (I := I) (U := U) x

/-- Post-composition with the density comparison identifies intrinsic bundle-dual densities with
duals valued in the pulled-back ambient densities. -/
private def openPostcompDiffeomorph :
    TotalSpace (F →L[ℝ] ℝ) (openHomBundle (I := I) (V := V) (U := U))
      ≃ₘ^∞⟮I.prod 𝓘(ℝ, F →L[ℝ] ℝ), I.prod 𝓘(ℝ, F →L[ℝ] ℝ)⟯
      TotalSpace (F →L[ℝ] ℝ) (openPullbackHomBundle (I := I) (V := V) (U := U)) where
  toFun p := ⟨p.proj, (openEquiv (I := I) p.proj).toContinuousLinearMap.comp p.snd⟩
  invFun p := ⟨p.proj, (openEquiv (I := I) p.proj).symm.toContinuousLinearMap.comp p.snd⟩
  -- `openEquiv` is the identity on underlying densities.
  left_inv p := by cases p; rfl
  right_inv p := by cases p; rfl
  contMDiff_toFun := TauCeti.contMDiff_clm_bundle_postcomp
    (W := (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V)
    (E₂ := pullbackAmbientDensity (I := I) (U := U))
    (fun x ↦ (openEquiv (I := I) x).toContinuousLinearMap) contMDiff_openEquiv_pullback
  contMDiff_invFun := TauCeti.contMDiff_clm_bundle_postcomp
    (W := (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V)
    (E₁ := pullbackAmbientDensity (I := I) (U := U))
    (fun x ↦ (openEquiv (I := I) x).symm.toContinuousLinearMap)
    ((openDiffeomorph (I := I) (U := U)).symm.contMDiff.congr fun p ↦
      (openDiffeomorph_symm_apply p).symm)

/-- Intrinsic real bundle-dual densities are diffeomorphic to the ambient pullback: post-compose
with the density comparison, then identify the Hom bundle of pullbacks with the pullback of the
Hom bundle. -/
def openHomDiffeomorph :
    TotalSpace (F →L[ℝ] ℝ) (openHomBundle (I := I) (V := V) (U := U))
      ≃ₘ^∞⟮I.prod 𝓘(ℝ, F →L[ℝ] ℝ), I.prod 𝓘(ℝ, F →L[ℝ] ℝ)⟯
      TotalSpace (F →L[ℝ] ℝ) (pullbackAmbientHomBundle (I := I) (V := V) (U := U)) :=
  openPostcompDiffeomorph.trans (Bundle.Pullback.homDiffeomorph (E₁ := V)
    (E₂ := TauCeti.DensityBundle I M) _ contMDiff_subtypeVal_continuousMap)

/-- The dual-density diffeomorphism acts by the fibre comparison over the same base point. -/
@[simp]
theorem openHomDiffeomorph_apply
    (p : TotalSpace (F →L[ℝ] ℝ) (openHomBundle (I := I) (V := V) (U := U))) :
    openHomDiffeomorph (I := I) (F := F) (V := V) p = ⟨p.proj, openHomEquiv p.proj p.snd⟩ := by
  simp only [openHomDiffeomorph, Diffeomorph.coe_trans, Function.comp_apply,
    Bundle.Pullback.homDiffeomorph_apply, Bundle.Pullback.homEquiv_apply]
  -- `openHomEquiv` is post-composition with `openEquiv` (`arrowCongr` with the identity source).
  rfl

/-- The inverse dual-density diffeomorphism acts by the inverse fibre comparison. -/
@[simp]
theorem openHomDiffeomorph_symm_apply
    (p : TotalSpace (F →L[ℝ] ℝ) (pullbackAmbientHomBundle (I := I) (V := V) (U := U))) :
    (openHomDiffeomorph (I := I) (F := F) (V := V)).symm p =
      ⟨p.proj, (openHomEquiv p.proj).symm p.snd⟩ := by
  simp only [openHomDiffeomorph, Diffeomorph.symm_trans', Diffeomorph.coe_trans,
    Function.comp_apply, Bundle.Pullback.homDiffeomorph_symm_apply,
    Bundle.Pullback.homEquiv_symm_apply]
  -- The inverse of `openHomEquiv` is post-composition with the inverse of `openEquiv`.
  rfl

end TauCeti.DensityBundle
