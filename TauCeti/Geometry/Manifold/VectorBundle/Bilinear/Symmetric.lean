/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Bilinear.Section
public import TauCeti.Topology.VectorBundle.SymmetricBilinear

/-!
# The `C^n` bundle of symmetric bilinear maps

For a `C^n` vector bundle `V` with model fibre `F` and a normed space `G`, the topological vector
bundle `fun x ↦ symmetricBilinearMaps 𝕜 (V x) G` of symmetric bilinear maps is a `C^n` vector
bundle, provided two is invertible in `𝕜`. For `G = ℝ` and the tangent bundle this is the bundle
`Sym²(T*M)` of symmetric covariant two-tensors.

Its coordinate changes are pullbacks of symmetric bilinear maps along the coordinate changes of
`V`. Their regularity is read off through the ambient space of all bilinear maps: the inclusion of
the symmetric subspace and the symmetrization `b ↦ (b + bᵀ) / 2` are continuous linear maps, and
the symmetrization is a retraction onto the symmetric subspace.

The same retraction compares the bundle with the ambient bundle of bilinear maps: a field of
symmetric bilinear maps is `C^n` as a section of the symmetric bundle if and only if it is `C^n`
as a section of the bundle of all bilinear maps. Consequently the `C^n` sections of the symmetric
bundle are identified with the symmetric `C^n` bilinear sections,
`TauCeti.Manifold.symmetricBilinearSectionEquiv`. Riemannian metrics are among the latter, as the
positive-definite symmetric sections.

The `C^n` structure follows Mathlib's `C^n` bundle of continuous alternating maps,
`Mathlib.Geometry.Manifold.VectorBundle.ContinuousAlternatingMap`, by Sébastien Gouëzel.

## Main results

* `ContMDiffVectorBundle.symmetricBilinearMaps`: the bundle of symmetric bilinear maps on a `C^n`
  vector bundle is a `C^n` vector bundle.
* `TauCeti.Manifold.contMDiffWithinAt_symmetricBilinearMaps_section_iff`: regularity of a field of
  symmetric bilinear maps agrees in the symmetric and in the ambient bilinear bundle.
* `TauCeti.Manifold.symmetricBilinearSectionEquiv`: `C^n` sections of the symmetric bundle are the
  symmetric `C^n` bilinear sections.
-/

public section

noncomputable section

open Bundle Set Filter TauCeti
open scoped ContDiff Manifold Topology

/-! ### Regularity of the symmetric pullback -/

section Pullback

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NeZero (2 : 𝕜)]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
  {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners 𝕜 EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  {F F' : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {n : ℕ∞ω}

/-- When two is invertible, symmetric pullback depends in a `C^n` way on the map it pulls back
along. -/
theorem ContMDiffOn.symmetricBilinearMapsComp {P : M → F' →L[𝕜] F} {s : Set M}
    (hP : ContMDiffOn IM 𝓘(𝕜, F' →L[𝕜] F) n P s) :
    ContMDiffOn IM 𝓘(𝕜, symmetricBilinearMaps 𝕜 F G →L[𝕜] symmetricBilinearMaps 𝕜 F' G) n
      (fun x ↦ (P x).symmetricBilinearMapsComp (G := G)) s := by
  -- Pull back in the ambient space of bilinear maps, then symmetrize.
  have hbil := ((hP.clm_precomp (F₃ := G)).clm_postcomp (F₁ := F')).clm_comp
    (hP.clm_precomp (F₃ := F →L[𝕜] G))
  -- The symmetric spaces are named explicitly: unification alone does not identify the normed
  -- and the submodule instances on them.
  have hsym := ContMDiffOn.clm_comp (F₂ := symmetricBilinearMaps 𝕜 F G)
    (f := fun _ ↦ (symmetricBilinearMaps 𝕜 F G).subtypeL) hbil contMDiffOn_const
  have h := ContMDiffOn.clm_comp (F₁ := F' →L[𝕜] F' →L[𝕜] G)
    (F₂ := symmetricBilinearMaps 𝕜 F G) (F₃ := symmetricBilinearMaps 𝕜 F' G)
    (g := fun _ ↦ ContinuousLinearMap.symmetrizeBilinear (V := F') (G := G)) contMDiffOn_const
    hsym
  refine h.congr fun x _ ↦ ?_
  -- Symmetrization fixes the symmetric pullback.
  ext1 b
  rw [ContinuousLinearMap.comp_apply,
    ← ContinuousLinearMap.symmetrizeBilinear_coe ((P x).symmetricBilinearMapsComp b)]
  congr 1
  ext v w
  simp

end Pullback

/-! ### The `C^n` vector bundle structure -/

section Bundle

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NeZero (2 : 𝕜)]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {V : B → Type*}
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle 𝕜 F V]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {n : ℕ∞ω} [ContMDiffVectorBundle n F V IB]

/-- The coordinate changes of the bundle of symmetric bilinear maps are `C^n`. -/
theorem Bundle.Pretrivialization.contMDiffOn_symmetricBilinearMapsCoordChange
    (e e' : Trivialization F (π F V)) [MemTrivializationAtlas e] [MemTrivializationAtlas e'] :
    ContMDiffOn IB
      𝓘(𝕜, TauCeti.symmetricBilinearMaps 𝕜 F G →L[𝕜] TauCeti.symmetricBilinearMaps 𝕜 F G) n
      (symmetricBilinearMapsCoordChange 𝕜 G e e') (e.baseSet ∩ e'.baseSet) := by
  rw [symmetricBilinearMapsCoordChange_def]
  exact ((contMDiffOn_coordChangeL e' e).mono (inter_comm _ _).subset).symmetricBilinearMapsComp

instance TauCeti.isContMDiff_symmetricBilinearMapsVectorPrebundle :
    (symmetricBilinearMapsVectorPrebundle 𝕜 F V G).IsContMDiff IB n where
  exists_contMDiffCoordChange := by
    intro _ h _ h'
    obtain ⟨e, he, rfl⟩ := mem_pretrivializationAtlas_symmetricBilinearMapsVectorPrebundle.1 h
    obtain ⟨e', he', rfl⟩ := mem_pretrivializationAtlas_symmetricBilinearMapsVectorPrebundle.1 h'
    simp only [Pretrivialization.baseSet_symmetricBilinearMaps]
    exact ⟨Pretrivialization.symmetricBilinearMapsCoordChange 𝕜 G e e',
      Pretrivialization.contMDiffOn_symmetricBilinearMapsCoordChange e e',
      fun _ hb ↦ Pretrivialization.symmetricBilinearMapsCoordChange_apply G hb⟩

/-- When two is invertible, the symmetric bilinear maps on the fibres of a `C^n` vector bundle
form a `C^n` vector bundle. -/
instance ContMDiffVectorBundle.symmetricBilinearMaps :
    ContMDiffVectorBundle n (symmetricBilinearMaps 𝕜 F G)
      (fun x ↦ symmetricBilinearMaps 𝕜 (V x) G) IB :=
  (symmetricBilinearMapsVectorPrebundle 𝕜 F V G).contMDiffVectorBundle IB

end Bundle

/-! ### Comparison with the bundle of all bilinear maps -/

namespace TauCeti.Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {V : B → Type*}
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle 𝕜 F V]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {n : ℕ∞ω}

/-- In the chosen trivializations, a symmetric bilinear map has the same coordinates in the
symmetric bundle and in the bundle of all bilinear maps. -/
theorem coe_trivializationAt_symmetricBilinearMaps_snd {x₀ x : B}
    (hx : x ∈ (trivializationAt F V x₀).baseSet) (b : symmetricBilinearMaps 𝕜 (V x) G) :
    ((trivializationAt (symmetricBilinearMaps 𝕜 F G)
        (fun x ↦ symmetricBilinearMaps 𝕜 (V x) G) x₀ ⟨x, b⟩).2 :
        F →L[𝕜] F →L[𝕜] G) =
      (trivializationAt (F →L[𝕜] F →L[𝕜] G) (fun x ↦ V x →L[𝕜] V x →L[𝕜] G) x₀
        ⟨x, (b : V x →L[𝕜] V x →L[𝕜] G)⟩).2 := by
  ext v w
  rw [hom_trivializationAt_apply, inCoordinates_apply_eq₂ hx hx (by simp)]
  simp [trivializationAt_symmetricBilinearMaps_apply, Trivialization.symmL_apply _ hx]

variable [NeZero (2 : 𝕜)]

/-- A field of symmetric bilinear maps is `C^n` as a section of the symmetric bundle exactly when
it is `C^n` as a section of the bundle of all bilinear maps. -/
theorem contMDiffWithinAt_symmetricBilinearMaps_section_iff
    {b : ∀ x, symmetricBilinearMaps 𝕜 (V x) G} {s : Set B} {x₀ : B} :
    ContMDiffWithinAt IB (IB.prod 𝓘(𝕜, symmetricBilinearMaps 𝕜 F G)) n
        (fun x ↦ TotalSpace.mk' (symmetricBilinearMaps 𝕜 F G) x (b x)) s x₀ ↔
      ContMDiffWithinAt IB (IB.prod 𝓘(𝕜, F →L[𝕜] F →L[𝕜] G)) n
        (fun x ↦ TotalSpace.mk' (F →L[𝕜] F →L[𝕜] G) x (b x : V x →L[𝕜] V x →L[𝕜] G)) s x₀ := by
  rw [contMDiffWithinAt_section, contMDiffWithinAt_section]
  have hx₀ := mem_baseSet_trivializationAt F V x₀
  have hev : ∀ᶠ x in 𝓝[s] x₀, x ∈ (trivializationAt F V x₀).baseSet :=
    eventually_nhdsWithin_of_eventually_nhds
      ((trivializationAt F V x₀).open_baseSet.mem_nhds hx₀)
  constructor
  · intro h
    refine ((symmetricBilinearMaps 𝕜 F G).subtypeL.contDiff.comp_contMDiffWithinAt
      h).congr_of_eventuallyEq ?_ ?_
    · filter_upwards [hev] with x hx
      exact (coe_trivializationAt_symmetricBilinearMaps_snd hx (b x)).symm
    · exact (coe_trivializationAt_symmetricBilinearMaps_snd hx₀ (b x₀)).symm
  · intro h
    refine ((ContinuousLinearMap.symmetrizeBilinear (V := F) (G := G)).contDiff
      |>.comp_contMDiffWithinAt h).congr_of_eventuallyEq ?_ ?_
    · filter_upwards [hev] with x hx
      simp [← coe_trivializationAt_symmetricBilinearMaps_snd hx (b x)]
    · simp [← coe_trivializationAt_symmetricBilinearMaps_snd hx₀ (b x₀)]

/-- A field of symmetric bilinear maps is `C^n` at a point as a section of the symmetric bundle
exactly when it is as a section of the bundle of all bilinear maps. -/
theorem contMDiffAt_symmetricBilinearMaps_section_iff
    {b : ∀ x, symmetricBilinearMaps 𝕜 (V x) G} {x₀ : B} :
    ContMDiffAt IB (IB.prod 𝓘(𝕜, symmetricBilinearMaps 𝕜 F G)) n
        (fun x ↦ TotalSpace.mk' (symmetricBilinearMaps 𝕜 F G) x (b x)) x₀ ↔
      ContMDiffAt IB (IB.prod 𝓘(𝕜, F →L[𝕜] F →L[𝕜] G)) n
        (fun x ↦ TotalSpace.mk' (F →L[𝕜] F →L[𝕜] G) x (b x : V x →L[𝕜] V x →L[𝕜] G)) x₀ :=
  contMDiffWithinAt_symmetricBilinearMaps_section_iff

/-- A field of symmetric bilinear maps is a `C^n` section of the symmetric bundle exactly when it
is a `C^n` section of the bundle of all bilinear maps. -/
theorem contMDiff_symmetricBilinearMaps_section_iff
    {b : ∀ x, symmetricBilinearMaps 𝕜 (V x) G} :
    ContMDiff IB (IB.prod 𝓘(𝕜, symmetricBilinearMaps 𝕜 F G)) n
        (fun x ↦ TotalSpace.mk' (symmetricBilinearMaps 𝕜 F G) x (b x)) ↔
      ContMDiff IB (IB.prod 𝓘(𝕜, F →L[𝕜] F →L[𝕜] G)) n
        (fun x ↦ TotalSpace.mk' (F →L[𝕜] F →L[𝕜] G) x (b x : V x →L[𝕜] V x →L[𝕜] G)) :=
  forall_congr' fun _ ↦ contMDiffAt_symmetricBilinearMaps_section_iff

variable (IB n) in
/-- The `C^n` sections of the bundle of symmetric bilinear maps are the symmetric `C^n` bilinear
sections. -/
def symmetricBilinearSectionEquiv :
    Cₛ^n⟮IB; symmetricBilinearMaps 𝕜 F G, fun x ↦ symmetricBilinearMaps 𝕜 (V x) G⟯ ≃ₗ[𝕜]
      symmetricBilinearSections (IB := IB) (F := F) (V := V) (G := G) (n := n) where
  toFun σ := ⟨⟨fun x ↦ (σ x : V x →L[𝕜] V x →L[𝕜] G),
      contMDiff_symmetricBilinearMaps_section_iff.1 σ.contMDiff⟩,
    (mem_symmetricBilinearSections _).2 fun x ↦
      (mem_symmetricBilinearMaps 𝕜 (V x) G _).1 (σ x).2⟩
  invFun β := ⟨fun x ↦ ⟨β.1 x, (mem_symmetricBilinearMaps 𝕜 (V x) G _).2
      ((mem_symmetricBilinearSections _).1 β.2 x)⟩,
    contMDiff_symmetricBilinearMaps_section_iff.2 β.1.contMDiff⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem symmetricBilinearSectionEquiv_apply
    (σ : Cₛ^n⟮IB; symmetricBilinearMaps 𝕜 F G, fun x ↦ symmetricBilinearMaps 𝕜 (V x) G⟯)
    (x : B) :
    ((symmetricBilinearSectionEquiv IB n σ : BilinearSection IB F V G n) x) =
      (σ x : V x →L[𝕜] V x →L[𝕜] G) :=
  (rfl)

@[simp]
theorem coe_symmetricBilinearSectionEquiv_symm_apply
    (β : symmetricBilinearSections (IB := IB) (F := F) (V := V) (G := G) (n := n)) (x : B) :
    (((symmetricBilinearSectionEquiv IB n).symm β x : symmetricBilinearMaps 𝕜 (V x) G) :
        V x →L[𝕜] V x →L[𝕜] G) =
      (β : BilinearSection IB F V G n) x :=
  (rfl)

end TauCeti.Manifold
