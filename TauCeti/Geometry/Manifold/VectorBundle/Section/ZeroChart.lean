/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.Linearization
public import TauCeti.Analysis.Fredholm.LevelSet.Smooth

/-!
# Local charts for regular zeros of bundle sections

A section along a map from a Banach space has, near a regular zero, a zero set parametrized
by the kernel of its coordinate derivative. The chart is on the actual zero set of the section,
not on the globally extended coordinate equation: outside a bundle trivialization's base set,
that equation can have spurious zeros. We restrict the implicit-function chart to the interior
of the preimage of the base set before taking its zero slice.

`sectionZeroChart` provides this local homeomorphism, with its source, target, coordinate
formula and normalization. Its inverse, included into the parameter space, is smooth at the
origin and has derivative the inclusion of the kernel. For a surjective Fredholm derivative,
`exists_sectionZeroChartModel` gives a chart modelled on `Fin n → 𝕜`, where `n` is the index,
and identifies its tangent image with the kernel of the intrinsic section linearization.

The atlas on regular zero sets over Banach manifolds is constructed in `Section.Chart`;
smooth compatibility is proved in `Section.Manifold`.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed.,
  Appendix A.3, for regular zeros of Fredholm sections.

The construction uses Mathlib's complemented-kernel implicit function theorem and
`OpenPartialHomeomorph.subtypeCoord`, as in `TauCeti.levelSetChart`.
-/

public section

open Bundle Filter Set
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {𝕜 X B F : Type*} {E : B → Type*}
  [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  [TopologicalSpace B] [∀ a, TopologicalSpace (E a)]
  [TopologicalSpace (TotalSpace F E)]
  [∀ a, AddCommGroup (E a)] [∀ a, Module 𝕜 (E a)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]
  {b : X → B} {s : ∀ y, E (b y)}

section Local

variable {x : X}
  {e : Trivialization F (π F E)} [MemTrivializationAtlas e]
  {T : X →L[𝕜] F}

private theorem sectionZeroChart_slice_mem
    (hf : HasStrictFDerivAt (fun y ↦ (e ⟨b y, s y⟩).2) T x)
    (hT : T.range = ⊤) (hker : T.ker.ClosedComplemented) {k : T.ker}
    (hk : (0, k) ∈ ((hf.implicitToOpenPartialHomeomorphOfComplemented _ _ hT hker).restrOpen
      (interior (b ⁻¹' e.baseSet)) isOpen_interior).target) :
    ((hf.implicitToOpenPartialHomeomorphOfComplemented _ _ hT hker).restrOpen
      (interior (b ⁻¹' e.baseSet)) isOpen_interior).symm (0, k) ∈ {y | s y = 0} := by
  let Φ := (hf.implicitToOpenPartialHomeomorphOfComplemented _ _ hT hker).restrOpen
    (interior (b ⁻¹' e.baseSet)) isOpen_interior
  have hy := Φ.map_target hk
  have hbase : b (Φ.symm (0, k)) ∈ e.baseSet :=
    interior_subset (s := b ⁻¹' e.baseSet) hy.2
  have hcoord : (e ⟨b (Φ.symm (0, k)), s (Φ.symm (0, k))⟩).2 = 0 := by
    rw [← hf.implicitToOpenPartialHomeomorphOfComplemented_fst hT hker]
    exact congrArg Prod.fst (Φ.right_inv hk)
  exact (e.continuousLinearEquivAt 𝕜 _ hbase).map_eq_zero_iff.1 hcoord

private theorem sectionZeroChart_mk_snd_eq
    (hf : HasStrictFDerivAt (fun y ↦ (e ⟨b y, s y⟩).2) T x)
    (hT : T.range = ⊤) (hker : T.ker.ClosedComplemented) {y : X}
    (hy : y ∈ ((hf.implicitToOpenPartialHomeomorphOfComplemented _ _ hT hker).restrOpen
      (interior (b ⁻¹' e.baseSet)) isOpen_interior).source) (hys : y ∈ {y | s y = 0}) :
    (0, (((hf.implicitToOpenPartialHomeomorphOfComplemented _ _ hT hker).restrOpen
      (interior (b ⁻¹' e.baseSet)) isOpen_interior) y).2) =
      ((hf.implicitToOpenPartialHomeomorphOfComplemented _ _ hT hker).restrOpen
        (interior (b ⁻¹' e.baseSet)) isOpen_interior) y := by
  have hbase : b y ∈ e.baseSet := interior_subset (s := b ⁻¹' e.baseSet) hy.2
  simp only [OpenPartialHomeomorph.coe_restrOpen]
  apply Prod.ext
  · rw [hf.implicitToOpenPartialHomeomorphOfComplemented_fst hT hker, hys]
    exact (congrArg Prod.snd (e.zeroSection 𝕜 hbase)).symm
  · rfl

/-- The implicit-function chart of a section's actual zero set, restricted to the neighbourhood
where the chosen bundle trivialization is valid. The coordinates are the projection onto the
kernel of the coordinate derivative, applied to displacement from the base point. -/
noncomputable def sectionZeroChart
    (hf : HasStrictFDerivAt (fun y ↦ (e ⟨b y, s y⟩).2) T x)
    (hT : T.range = ⊤) (hker : T.ker.ClosedComplemented) (hz : s x = 0) :
    OpenPartialHomeomorph ↥{y | s y = 0} ↥T.ker :=
  let Φ := (hf.implicitToOpenPartialHomeomorphOfComplemented _ _ hT hker).restrOpen
    (interior (b ⁻¹' e.baseSet)) isOpen_interior
  Φ.subtypeCoord {y | s y = 0} ⟨⟨x, hz⟩⟩ (fun k ↦ (0, k)) Prod.snd
    (sectionZeroChart_slice_mem hf hT hker) (sectionZeroChart_mk_snd_eq hf hT hker)
    -- Preserve the retraction type when unfolding the subtype-coordinate construction.
    (show Set.LeftInvOn Prod.snd (fun k : T.ker ↦ ((0 : F), k))
      ((fun k ↦ (0, k)) ⁻¹' Φ.target) from fun _ _ ↦ rfl)
    (continuous_const.prodMk continuous_id) continuous_snd.continuousOn

/-- The source consists of zeros in the implicit-function source and in the interior of the
preimage of the bundle trivialization's base set. -/
@[simp]
theorem sectionZeroChart_source
    (hf : HasStrictFDerivAt (fun y ↦ (e ⟨b y, s y⟩).2) T x)
    (hT : T.range = ⊤) (hker : T.ker.ClosedComplemented) (hz : s x = 0) :
    (sectionZeroChart hf hT hker hz).source = Subtype.val ⁻¹'
      ((hf.implicitToOpenPartialHomeomorphOfComplemented _ _ hT hker).source ∩
        interior (b ⁻¹' e.baseSet)) := by
  unfold sectionZeroChart
  dsimp only
  rw [OpenPartialHomeomorph.subtypeCoord_source, OpenPartialHomeomorph.restrOpen_source]

/-- The target is the zero slice of the implicit-function target, restricted to points whose
inverse remains in the trivialization's base set. -/
@[simp]
theorem sectionZeroChart_target
    (hf : HasStrictFDerivAt (fun y ↦ (e ⟨b y, s y⟩).2) T x)
    (hT : T.range = ⊤) (hker : T.ker.ClosedComplemented) (hz : s x = 0) :
    (sectionZeroChart hf hT hker hz).target = (fun k ↦ (0, k)) ⁻¹'
      ((hf.implicitToOpenPartialHomeomorphOfComplemented _ _ hT hker).restrOpen
        (interior (b ⁻¹' e.baseSet)) isOpen_interior).target := by
  unfold sectionZeroChart
  dsimp only
  rw [OpenPartialHomeomorph.subtypeCoord_target]

/-- The section-zero chart reads displacement through the chosen projection onto the kernel. -/
theorem sectionZeroChart_apply
    (hf : HasStrictFDerivAt (fun y ↦ (e ⟨b y, s y⟩).2) T x)
    (hT : T.range = ⊤) (hker : T.ker.ClosedComplemented) (hz : s x = 0)
    (y : ↥{y | s y = 0}) :
    sectionZeroChart hf hT hker hz y = Classical.choose hker (y.1 - x) := by
  unfold sectionZeroChart
  dsimp only
  rw [OpenPartialHomeomorph.subtypeCoord_apply, OpenPartialHomeomorph.coe_restrOpen,
    hf.implicitToOpenPartialHomeomorphOfComplemented_apply hT hker]

/-- On the target, the inverse chart is the ambient implicit function on the zero slice. -/
theorem coe_sectionZeroChart_symm_apply
    (hf : HasStrictFDerivAt (fun y ↦ (e ⟨b y, s y⟩).2) T x)
    (hT : T.range = ⊤) (hker : T.ker.ClosedComplemented) (hz : s x = 0)
    {k : ↥T.ker} (hk : k ∈ (sectionZeroChart hf hT hker hz).target) :
    ((sectionZeroChart hf hT hker hz).symm k : X) =
      (hf.implicitToOpenPartialHomeomorphOfComplemented _ _ hT hker).symm (0, k) := by
  rw [sectionZeroChart_target] at hk
  unfold sectionZeroChart
  dsimp only
  rw [OpenPartialHomeomorph.coe_subtypeCoord_symm_apply _ _ _ _ _ _ _ _ _ _ hk]
  rfl

/-- The chart is centred at the regular zero. -/
@[simp]
theorem sectionZeroChart_apply_self
    (hf : HasStrictFDerivAt (fun y ↦ (e ⟨b y, s y⟩).2) T x)
    (hT : T.range = ⊤) (hker : T.ker.ClosedComplemented) (hz : s x = 0) :
    sectionZeroChart hf hT hker hz ⟨x, hz⟩ = 0 := by
  rw [sectionZeroChart_apply]
  simp

/-- Continuity of the base map at the zero ensures that the zero lies in the chart source. -/
theorem mem_sectionZeroChart_source
    (hb : ContinuousAt b x) (he : b x ∈ e.baseSet)
    (hf : HasStrictFDerivAt (fun y ↦ (e ⟨b y, s y⟩).2) T x)
    (hT : T.range = ⊤) (hker : T.ker.ClosedComplemented) (hz : s x = 0) :
    (⟨x, hz⟩ : ↥{y | s y = 0}) ∈ (sectionZeroChart hf hT hker hz).source := by
  rw [sectionZeroChart_source]
  exact ⟨hf.mem_implicitToOpenPartialHomeomorphOfComplemented_source hT hker,
    mem_interior_iff_mem_nhds.2 (hb.preimage_mem_nhds (e.open_baseSet.mem_nhds he))⟩

/-- The origin belongs to the target of a section-zero chart at a zero in its base set. -/
theorem mem_sectionZeroChart_target
    (hb : ContinuousAt b x) (he : b x ∈ e.baseSet)
    (hf : HasStrictFDerivAt (fun y ↦ (e ⟨b y, s y⟩).2) T x)
    (hT : T.range = ⊤) (hker : T.ker.ClosedComplemented) (hz : s x = 0) :
    (0 : ↥T.ker) ∈ (sectionZeroChart hf hT hker hz).target :=
  sectionZeroChart_apply_self hf hT hker hz ▸
    (sectionZeroChart hf hT hker hz).map_source
      (mem_sectionZeroChart_source hb he hf hT hker hz)

/-- The inverse sends the chart origin back to the section's zero. -/
@[simp]
theorem sectionZeroChart_symm_zero
    (hb : ContinuousAt b x) (he : b x ∈ e.baseSet)
    (hf : HasStrictFDerivAt (fun y ↦ (e ⟨b y, s y⟩).2) T x)
    (hT : T.range = ⊤) (hker : T.ker.ClosedComplemented) (hz : s x = 0) :
    (sectionZeroChart hf hT hker hz).symm 0 = ⟨x, hz⟩ := by
  rw [← sectionZeroChart_apply_self hf hT hker hz]
  exact (sectionZeroChart hf hT hker hz).left_inv
    (mem_sectionZeroChart_source hb he hf hT hker hz)

private theorem coe_sectionZeroChart_symm_eventuallyEq
    (hb : ContinuousAt b x) (he : b x ∈ e.baseSet)
    (hf : HasStrictFDerivAt (fun y ↦ (e ⟨b y, s y⟩).2) T x)
    (hT : T.range = ⊤) (hker : T.ker.ClosedComplemented) (hz : s x = 0)
    (hcoord : (e ⟨b x, s x⟩).2 = 0) :
    (fun k ↦ ((sectionZeroChart hf hT hker hz).symm k : X)) =ᶠ[𝓝 0]
      fun k ↦ ((levelSetChart hf hT hker hcoord).symm k : X) := by
  filter_upwards [(sectionZeroChart hf hT hker hz).open_target.mem_nhds
    (mem_sectionZeroChart_target hb he hf hT hker hz)] with k hk
  rw [coe_sectionZeroChart_symm_apply hf hT hker hz hk]
  symm
  apply levelSetChart_symm_apply
  rw [sectionZeroChart_target, Set.mem_preimage] at hk
  rw [levelSetChart_target]
  exact hk.1

/-- The inverse chart, included in the parameter space, is as smooth at the origin as the
section's fiber coordinates are at its zero. -/
theorem contDiffAt_coe_sectionZeroChart_symm {m : ℕ∞ω}
    (hb : ContinuousAt b x) (he : b x ∈ e.baseSet)
    (hf : HasStrictFDerivAt (fun y ↦ (e ⟨b y, s y⟩).2) T x)
    (hT : T.range = ⊤) (hker : T.ker.ClosedComplemented) (hz : s x = 0)
    (hs : ContDiffAt 𝕜 m (fun y ↦ (e ⟨b y, s y⟩).2) x) :
    ContDiffAt 𝕜 m (fun k ↦ ((sectionZeroChart hf hT hker hz).symm k : X)) 0 := by
  have hcoord : (e ⟨b x, s x⟩).2 = 0 := by
    simpa only [zeroSection, hz] using congrArg Prod.snd (e.zeroSection 𝕜 he)
  exact (contDiffAt_coe_levelSetChart_symm hf hs hT hker hcoord).congr_of_eventuallyEq
    (coe_sectionZeroChart_symm_eventuallyEq hb he hf hT hker hz hcoord)

/-- The tangent parametrization at the origin is the canonical inclusion of the kernel of the
section's coordinate derivative. -/
theorem hasStrictFDerivAt_coe_sectionZeroChart_symm
    (hb : ContinuousAt b x) (he : b x ∈ e.baseSet)
    (hf : HasStrictFDerivAt (fun y ↦ (e ⟨b y, s y⟩).2) T x)
    (hT : T.range = ⊤) (hker : T.ker.ClosedComplemented) (hz : s x = 0) :
    HasStrictFDerivAt (fun k ↦ ((sectionZeroChart hf hT hker hz).symm k : X))
      T.ker.subtypeL 0 := by
  have hcoord : (e ⟨b x, s x⟩).2 = 0 := by
    simpa only [zeroSection, hz] using congrArg Prod.snd (e.zeroSection 𝕜 he)
  exact (hasStrictFDerivAt_coe_levelSetChart_symm hf hT hker hcoord).congr_of_eventuallyEq
    (coe_sectionZeroChart_symm_eventuallyEq hb he hf hT hker hz hcoord).symm

/-- Away from the origin, the inverse section-zero chart is smooth wherever its image lies
in the neighbourhood on which the implicit coordinate derivative remains invertible. -/
theorem contDiffAt_coe_sectionZeroChart_symm_of_mem {m : ℕ∞ω}
    (hf : HasStrictFDerivAt (fun y ↦ (e ⟨b y, s y⟩).2) T x)
    (hT : T.range = ⊤) (hker : T.ker.ClosedComplemented) (hz : s x = 0)
    {k : ↥T.ker} (hk : k ∈ (sectionZeroChart hf hT hker hz).target)
    (hmem : ((sectionZeroChart hf hT hker hz).symm k : X) ∈
      hf.implicitCoordSource hT hker)
    {A : X →L[𝕜] F}
    (hA : HasFDerivAt (fun y ↦ (e ⟨b y, s y⟩).2) A
      ((sectionZeroChart hf hT hker hz).symm k : X))
    (hs : ContDiffAt 𝕜 m (fun y ↦ (e ⟨b y, s y⟩).2)
      ((sectionZeroChart hf hT hker hz).symm k : X)) :
    ContDiffAt 𝕜 m (fun j ↦ ((sectionZeroChart hf hT hker hz).symm j : X)) k := by
  -- Unlike the level-set theorem, this needs no base-set hypothesis at the chart centre:
  -- the extended fiber coordinate need not vanish there, even though the section does.
  have ht := hk
  rw [sectionZeroChart_target] at ht
  have hval := coe_sectionZeroChart_symm_apply hf hT hker hz hk
  have hinverse := hf.contDiffAt_implicitToOpenPartialHomeomorphOfComplemented_symm_of_mem
    hT hker ht.1 (hval ▸ hmem) (hval ▸ hA) (hval ▸ hs)
  have hslice : ContDiffAt 𝕜 m
      (fun j : T.ker ↦ (hf.implicitToOpenPartialHomeomorphOfComplemented _ _ hT hker).symm
        (0, j)) k := by
    simpa only [Function.comp_def] using
      hinverse.comp k (contDiffAt_const.prodMk contDiffAt_id)
  apply hslice.congr_of_eventuallyEq
  filter_upwards [(sectionZeroChart hf hT hker hz).open_target.mem_nhds hk] with j hj
  exact coe_sectionZeroChart_symm_apply hf hT hker hz hj

section Fredholm

variable [CompleteSpace 𝕜]

/-- A regular zero of a Fredholm section has a local parametrization of dimension the index.
The parametrization is as smooth at its origin as the section's coordinates, and its derivative
is injective with image exactly the kernel of the intrinsic section linearization.

The base map may in particular be a manifold chart inverse, so the statement also applies to
local parameter expressions of sections over Banach manifolds. -/
theorem exists_sectionZeroChartModel {m : ℕ∞ω} {n : ℕ}
    (hb : ContinuousAt b x) (he : b x ∈ e.baseSet)
    (hf : HasStrictFDerivAt (fun y ↦ (e ⟨b y, s y⟩).2) T x)
    (hFred : ContinuousLinearMap.IsFredholm T)
    (hsurj : Function.Surjective (sectionLinearization (F := F) 𝓘(𝕜, X) b s x))
    (hindex : ContinuousLinearMap.index T = n) (hz : s x = 0)
    (hs : ContDiffAt 𝕜 m (fun y ↦ (e ⟨b y, s y⟩).2) x) :
    ∃ χ : OpenPartialHomeomorph ↥{y | s y = 0} (Fin n → 𝕜),
      (⟨x, hz⟩ : ↥{y | s y = 0}) ∈ χ.source ∧ χ ⟨x, hz⟩ = 0 ∧
      ContDiffAt 𝕜 m (fun k ↦ (χ.symm k : X)) 0 ∧
      Function.Injective (fderiv 𝕜 (fun k ↦ (χ.symm k : X)) 0) ∧
      (fderiv 𝕜 (fun k ↦ (χ.symm k : X)) 0).range =
        (sectionLinearization (F := F) 𝓘(𝕜, X) b s x).ker := by
  have hsurjT : Function.Surjective T := by
    have h := (surjective_sectionLinearization_iff hb he
      hf.hasFDerivAt.differentiableAt.mdifferentiableAt hz).1 hsurj
    rw [mvfderiv_eq_fderiv, hf.hasFDerivAt.fderiv, ContinuousLinearMap.coe_comp] at h
    exact h.of_comp
  have hT : T.range = ⊤ := LinearMap.range_eq_top.2 hsurjT
  have hn : Module.finrank 𝕜 T.ker = n :=
    (ContinuousLinearMap.finrank_ker_eq_iff_index_eq T hsurjT).2 hindex
  let K := T.kerModelEquiv hFred.finite_ker hn
  let ψ := sectionZeroChart hf hT hFred.closedComplemented_ker hz
  let χ := ψ.transHomeomorph K.toHomeomorph
  have hχ : ∀ k, (χ.symm k : X) = (ψ.symm (K.symm k) : X) := by
    intro k
    rw [OpenPartialHomeomorph.transHomeomorph_symm_apply,
      ContinuousLinearEquiv.coe_symm_toHomeomorph, Function.comp_apply]
  have hderiv : HasFDerivAt (fun k ↦ (χ.symm k : X))
      (T.ker.subtypeL.comp (K.symm : (Fin n → 𝕜) →L[𝕜] T.ker)) 0 := by
    have hd : HasFDerivAt (fun k ↦ (ψ.symm k : X)) T.ker.subtypeL (K.symm 0) := by
      simpa only [map_zero] using (hasStrictFDerivAt_coe_sectionZeroChart_symm
        hb he hf hT hFred.closedComplemented_ker hz).hasFDerivAt
    have hc := hd.comp 0 (K.symm.hasFDerivAt)
    simpa only [map_zero, Function.comp_def, ← hχ] using hc
  have hinj : Function.Injective (T.ker.subtypeL.comp
      (K.symm : (Fin n → 𝕜) →L[𝕜] T.ker)) :=
    Subtype.val_injective.comp K.symm.injective
  refine ⟨χ, ?_, ?_, ?_, ?_, ?_⟩
  · rw [OpenPartialHomeomorph.transHomeomorph_source]
    exact mem_sectionZeroChart_source hb he hf hT hFred.closedComplemented_ker hz
  · rw [OpenPartialHomeomorph.transHomeomorph_apply, Function.comp_apply,
      ContinuousLinearEquiv.coe_toHomeomorph, sectionZeroChart_apply_self]
    exact map_zero _
  · have hψ : ContDiffAt 𝕜 m (fun k ↦ (ψ.symm k : X)) (K.symm 0) := by
      simpa only [map_zero] using contDiffAt_coe_sectionZeroChart_symm
        hb he hf hT hFred.closedComplemented_ker hz hs
    have hc := hψ.comp 0 K.symm.contDiff.contDiffAt
    simpa only [map_zero, Function.comp_def, ← hχ] using hc
  · rwa [hderiv.fderiv]
  · rw [hderiv.fderiv]
    exact range_subtypeL_comp_eq_ker_sectionLinearization hb he hf.hasFDerivAt.hasMFDerivAt hz K

end Fredholm

end Local

end TauCeti
