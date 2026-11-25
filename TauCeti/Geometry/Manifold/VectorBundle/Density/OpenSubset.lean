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

/-!
# Intrinsic densities on open subsets

The intrinsic density line of an open submanifold is smoothly identified with the pullback of
the ambient density line (`TauCeti.DensityBundle.openDiffeomorph`, an instance of
`TauCeti.bundleDiffeomorph`). The comparison uses the native tangent-frame identity. It also acts
on real bundle-dual densities with arbitrary normed model fibres
(`TauCeti.DensityBundle.openHomDiffeomorph`).
-/

public noncomputable section

open Bundle FiberBundle Filter Set Topology TopologicalSpace
open scoped Manifold ContDiff
universe u v

namespace TauCeti.DensityBundle

section Coordinates

variable {EX HX X EB HB B₁ B₂ G : Type*} [NormedAddCommGroup EX] [NormedSpace ℝ EX]
  [TopologicalSpace HX] {IX : ModelWithCorners ℝ EX HX} [TopologicalSpace X] [ChartedSpace HX X]
  [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  [TopologicalSpace B₁] [ChartedSpace HB B₁] [TopologicalSpace B₂] [ChartedSpace HB B₂]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {E₁ : B₁ → Type*} [TopologicalSpace (TotalSpace G E₁)] [∀ x, TopologicalSpace (E₁ x)]
  [FiberBundle G E₁]
  {E₂ : B₂ → Type*} [TopologicalSpace (TotalSpace G E₂)] [∀ x, TopologicalSpace (E₂ x)]
  [FiberBundle G E₂]

/-- A map into a fibre bundle is smooth if its base map is smooth and, near each point, its
fibre coordinates agree with those of a smooth map into another bundle with the same fibre. -/
private theorem contMDiff_totalSpace_of_eventually_coordinates_eq
    (g : X → TotalSpace G E₂) (h : X → TotalSpace G E₁)
    (hg : ContMDiff IX IB ∞ fun x ↦ (g x).proj) (hh : ContMDiff IX (IB.prod 𝓘(ℝ, G)) ∞ h)
    (hco : ∀ p, ∀ᶠ q in 𝓝 p, (trivializationAt G E₂ (g p).proj (g q)).2 =
      (trivializationAt G E₁ (h p).proj (h q)).2) :
    ContMDiff IX (IB.prod 𝓘(ℝ, G)) ∞ g := by
  intro p
  rw [Bundle.contMDiffAt_totalSpace_iff]
  exact ⟨hg p, (Bundle.contMDiffAt_totalSpace_iff.mp (hh p)).2.congr_of_eventuallyEq (hco p)⟩

end Coordinates

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
  refine contMDiff_totalSpace_of_eventually_coordinates_eq _ id
    (contMDiff_subtypeVal.comp (contMDiff_proj _)) contMDiff_id fun p ↦ ?_
  filter_upwards [(FiberBundle.continuous_proj ℝ
    (TauCeti.DensityBundle I U)).continuousAt.eventually
    (eventually_openEquiv_apply_trivializationAt_symm_eq (I := I) p.proj)] with q hq
  simpa only [id, TauCeti.Density.trivializationAt_eq, Trivialization.density_apply] using hq q.snd

private theorem contMDiff_openEquiv_pullback :
    ContMDiff (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ)) ∞
      (fun p : TotalSpace ℝ (TauCeti.DensityBundle I U) ↦
        TotalSpace.mk' ℝ (E := (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ
          (TauCeti.DensityBundle I M)) p.proj (openEquiv p.proj p.snd)) :=
  (Bundle.Pullback.contMDiff_iff _ contMDiff_subtypeVal_continuousMap).2
    ⟨contMDiff_proj _, contMDiff_openEquiv_subtypeVal⟩

/-- The intrinsic density bundle of an open subset is diffeomorphic to the ambient pullback. -/
def openDiffeomorph :
    TotalSpace ℝ (TauCeti.DensityBundle I U) ≃ₘ^∞⟮I.prod 𝓘(ℝ), I.prod 𝓘(ℝ)⟯
      TotalSpace ℝ ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ
        (TauCeti.DensityBundle I M)) :=
  TauCeti.bundleDiffeomorph openEquiv contMDiff_openEquiv_pullback

/-- The density diffeomorphism acts by the fibre comparison over the same base point. This
records `TauCeti.bundleDiffeomorph_apply` for the unexposed definition. -/
@[simp]
theorem openDiffeomorph_apply (p : TotalSpace ℝ (TauCeti.DensityBundle I U)) :
    openDiffeomorph (I := I) p = ⟨p.proj, openEquiv p.proj p.snd⟩ :=
  TauCeti.bundleDiffeomorph_apply _ _ p

/-- The inverse density diffeomorphism acts by the inverse fibre comparison. -/
@[simp]
theorem openDiffeomorph_symm_apply
    (p : TotalSpace ℝ ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ
      (TauCeti.DensityBundle I M))) :
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

/-- The open dual-density comparison agrees in preferred Hom frames locally. -/
private theorem eventually_trivializationAt_openHomEquiv_eq (x : U) :
    ∀ᶠ y in nhds x, ∀ ℓ : openHomBundle (I := I) (V := V) (U := U) y,
      (trivializationAt (F →L[ℝ] ℝ) (ambientHomBundle (I := I) (V := V)) (x : M)
        (TotalSpace.mk' (F →L[ℝ] ℝ) (y : M) (openHomEquiv y ℓ))).2 =
      (trivializationAt (F →L[ℝ] ℝ) (openHomBundle (I := I) (V := V) (U := U)) x
        (TotalSpace.mk' (F →L[ℝ] ℝ) y ℓ)).2 := by
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
    exact Trivialization.symm_pullback (trivializationAt F V (x : M))
      c hyV v
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
    Trivialization.continuousLinearMapAt_apply, Trivialization.linearMapAt_apply,
    ite_eq_left hyDU]
  -- The ambient density trivialization's base-set test is stated at `(y : M)` through the open
  -- pullback carrier, which `rw` does not match syntactically.
  erw [ite_eq_left hyDM]
  -- Express the tensor-Hom coordinate in the density trivialization after fibre evaluation.
  change ((trivializationAt ℝ (TauCeti.DensityBundle I M) (x : M))
    ⟨(y : M), openEquiv y (ℓ ((trivializationAt F V (x : M)).symmL ℝ (y : M) v))⟩).2 =
    ((trivializationAt ℝ (TauCeti.DensityBundle I U) x)
      ⟨y, ℓ ((trivializationAt F (c *ᵖ V) x).symmL ℝ y v)⟩).2
  rw [hsymm]
  simpa only [TauCeti.Density.trivializationAt_eq, Trivialization.density_apply] using
    hframe (ℓ ((trivializationAt F V (x : M)).symmL ℝ (y : M) v))

private theorem contMDiff_openHomEquiv_subtypeVal :
    ContMDiff (I.prod 𝓘(ℝ, F →L[ℝ] ℝ)) (I.prod 𝓘(ℝ, F →L[ℝ] ℝ)) ∞
      (fun p : TotalSpace (F →L[ℝ] ℝ) (openHomBundle (I := I) (V := V) (U := U)) ↦
        TotalSpace.mk' (F →L[ℝ] ℝ) (E := ambientHomBundle (I := I) (V := V))
          (p.proj : M) (openHomEquiv p.proj p.snd)) := by
  refine contMDiff_totalSpace_of_eventually_coordinates_eq _ id
    (contMDiff_subtypeVal.comp (contMDiff_proj _)) contMDiff_id fun p ↦ ?_
  filter_upwards [(FiberBundle.continuous_proj (F →L[ℝ] ℝ)
    (openHomBundle (I := I) (V := V) (U := U))).continuousAt.eventually
      (eventually_trivializationAt_openHomEquiv_eq (I := I) (F := F) (V := V) p.proj)] with q hq
  exact hq q.snd

private theorem contMDiff_openHomEquiv_pullback :
    ContMDiff (I.prod 𝓘(ℝ, F →L[ℝ] ℝ)) (I.prod 𝓘(ℝ, F →L[ℝ] ℝ)) ∞
      (fun p : TotalSpace (F →L[ℝ] ℝ) (openHomBundle (I := I) (V := V) (U := U)) ↦
        TotalSpace.mk' (F →L[ℝ] ℝ) (E := pullbackAmbientHomBundle (I := I) (V := V) (U := U))
          p.proj (openHomEquiv p.proj p.snd)) :=
  (Bundle.Pullback.contMDiff_iff _ contMDiff_subtypeVal_continuousMap).2
    ⟨contMDiff_proj _, contMDiff_openHomEquiv_subtypeVal⟩

private theorem contMDiff_openHomEquiv_symm_pullback :
    ContMDiff (I.prod 𝓘(ℝ, F →L[ℝ] ℝ)) (I.prod 𝓘(ℝ, F →L[ℝ] ℝ)) ∞
      (fun p : TotalSpace (F →L[ℝ] ℝ) (pullbackAmbientHomBundle (I := I) (V := V) (U := U)) ↦
        TotalSpace.mk' (F →L[ℝ] ℝ) (E := openHomBundle (I := I) (V := V) (U := U))
          p.proj ((openHomEquiv p.proj).symm p.snd)) := by
  -- Compare with the canonical lift of the pullback total space into the ambient one.
  refine contMDiff_totalSpace_of_eventually_coordinates_eq _
    (fun q ↦ TotalSpace.mk' (F →L[ℝ] ℝ) (E := ambientHomBundle (I := I) (V := V))
      (q.proj : M) q.snd)
    (contMDiff_proj _) (Pullback.contMDiff_lift _ contMDiff_subtypeVal_continuousMap)
    fun p ↦ ?_
  filter_upwards [(FiberBundle.continuous_proj (F →L[ℝ] ℝ)
    (pullbackAmbientHomBundle (I := I) (V := V) (U := U))).continuousAt.eventually
      (eventually_trivializationAt_openHomEquiv_eq (I := I) (F := F) (V := V) p.proj)] with q hq
  -- `openHomEquiv` is the identity on underlying functionals, and the pullback fibre at `q.proj`
  -- is the ambient fibre at `(q.proj : M)`, so the comparison applies to `q.snd` itself.
  exact (hq ((openHomEquiv q.proj).symm q.snd)).symm

/-- Intrinsic real bundle-dual densities are diffeomorphic to the ambient pullback. -/
def openHomDiffeomorph :
    TotalSpace (F →L[ℝ] ℝ) (openHomBundle (I := I) (V := V) (U := U))
      ≃ₘ^∞⟮I.prod 𝓘(ℝ, F →L[ℝ] ℝ), I.prod 𝓘(ℝ, F →L[ℝ] ℝ)⟯
      TotalSpace (F →L[ℝ] ℝ) (pullbackAmbientHomBundle (I := I) (V := V) (U := U)) where
  toFun p := ⟨p.proj, openHomEquiv p.proj p.snd⟩
  invFun p := ⟨p.proj, (openHomEquiv p.proj).symm p.snd⟩
  -- The fibre comparison is the identity on underlying functionals.
  left_inv p := by cases p; rfl
  right_inv p := by cases p; rfl
  contMDiff_toFun := contMDiff_openHomEquiv_pullback
  contMDiff_invFun := contMDiff_openHomEquiv_symm_pullback

/-- The dual-density diffeomorphism acts by the fibre comparison over the same base point. -/
@[simp]
theorem openHomDiffeomorph_apply
    (p : TotalSpace (F →L[ℝ] ℝ) (openHomBundle (I := I) (V := V) (U := U))) :
    openHomDiffeomorph (I := I) (F := F) (V := V) p = ⟨p.proj, openHomEquiv p.proj p.snd⟩ :=
  (rfl)

/-- The inverse dual-density diffeomorphism acts by the inverse fibre comparison. -/
@[simp]
theorem openHomDiffeomorph_symm_apply
    (p : TotalSpace (F →L[ℝ] ℝ) (pullbackAmbientHomBundle (I := I) (V := V) (U := U))) :
    (openHomDiffeomorph (I := I) (F := F) (V := V)).symm p =
      ⟨p.proj, (openHomEquiv p.proj).symm p.snd⟩ :=
  (rfl)

end TauCeti.DensityBundle
