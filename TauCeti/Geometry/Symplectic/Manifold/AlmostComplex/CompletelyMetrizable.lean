/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Topology
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Complete
public import TauCeti.Geometry.Manifold.VectorBundle.Section.CountableSeminorms
public import Mathlib.Topology.MetricSpace.Polish
public import Mathlib.Topology.Baire.CompleteMetrizable

/-!
# Complete metrizability of spaces of smooth almost complex structures

The space of smooth almost complex structures on a manifold, with the `C^∞` topology
`TauCeti.SmoothAlmostComplexStructure.frameTopology`, is a closed subspace of the complete space of
smooth sections of `End(TM)` (`ContMDiffSection.completeSpace_frameTopology`). For countably many
covering frames on sigma-compact domains that space is metrizable, so the almost complex
structures form a completely metrizable space. On a sigma-compact manifold with finite-dimensional
model this holds for every covering frame system, since the topology does not depend on the
frames.

On a compact manifold, tameness by a smooth two-form `ω` is an open condition in the `C^∞`
topology: the function `(J, v) ↦ ω(v, J v)` is jointly continuous, and it suffices to check
positivity on a compact set of nonzero tangent vectors meeting every line. Hence the spaces of
smooth `ω`-tame and of smooth `ω`-compatible almost complex structures on a closed manifold, an open
subset and the intersection of an open with a closed subset, are completely metrizable and so Baire
spaces. These are the parameter spaces of the genericity theorems of pseudoholomorphic curve
theory.

## Main declarations

* `TauCeti.SmoothTwoForm.continuous_eval₂`: evaluating a smooth two-form on tangent vectors
  depending continuously on a parameter is continuous.
* `TauCeti.SmoothAlmostComplexStructure.continuous_apply_frameTopology`: applying an almost complex
  structure to a tangent vector is jointly continuous.
* `TauCeti.SmoothAlmostComplexStructure.isCompletelyMetrizableSpace_frameTopology`: on a
  sigma-compact manifold with finite-dimensional model and no boundary, the smooth almost complex
  structures form a completely metrizable space.
* `TauCeti.SmoothTwoForm.isOpen_setOf_tames_frameTopology`: on a compact manifold, tameness is open.
* `TauCeti.SmoothTwoForm.baireSpace_tames_frameTopology`,
  `TauCeti.SmoothTwoForm.baireSpace_compatible_frameTopology`: on a closed manifold, the smooth tame
  and the smooth compatible structures form Baire spaces.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 3.2.
-/

public section

noncomputable section

open Bundle Set Filter Topology TopologicalSpace
open scoped ContDiff Manifold

namespace TauCeti

variable {E H M : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace SmoothTwoForm

/-- Evaluating a smooth two-form on two tangent vectors depending continuously on a parameter,
over the same base point, is continuous. -/
theorem continuous_eval₂ (form : SmoothTwoForm I M) {X : Type*} [TopologicalSpace X]
    {b : X → M} {v w : ∀ p, TangentSpace I (b p)}
    (hv : Continuous fun p ↦ TotalSpace.mk' E (E := TangentSpace I) (b p) (v p))
    (hw : Continuous fun p ↦ TotalSpace.mk' E (E := TangentSpace I) (b p) (w p)) :
    Continuous fun p ↦ form.eval₂ (b p) (v p) (w p) := by
  refine continuous_iff_continuousAt.2 fun p₀ ↦ ?_
  have hb : Continuous b := (FiberBundle.continuous_proj E (TangentSpace I)).comp hv
  have hω : Continuous fun x : M ↦ TotalSpace.mk' (E [⋀^Fin 2]→L[ℝ] ℝ)
      (E := fun x : M ↦ TangentSpace I x [⋀^Fin 2]→L[ℝ] ℝ) x (form.1 x) := by
    have h := (SmoothBundleForm.toContMDiffSection form).contMDiff.continuous
    simp only [SmoothBundleForm.toContMDiffSection_apply] at h
    exact h
  have h1 := ((continuousAt_continuousAlternatingMap_bundle _).1
    ((hω.comp hb).continuousAt (x := p₀))).2
  have h2 := ((FiberBundle.continuousAt_totalSpace _ _).1 (hv.continuousAt (x := p₀))).2
  have h3 := ((FiberBundle.continuousAt_totalSpace _ _).1 (hw.continuousAt (x := p₀))).2
  set e := trivializationAt E (TangentSpace I) (b p₀)
  have hvec : ContinuousAt (fun p ↦ ![(e ⟨b p, v p⟩).2, (e ⟨b p, w p⟩).2]) p₀ :=
    continuousAt_pi.2 fun i ↦ by
      fin_cases i
      · exact h2
      · exact h3
  have hev : ContinuousAt (fun p ↦ ContinuousAlternatingMap.inCoordinates E ℝ (b p₀) (b p)
      (b p₀) (b p) (form.1 (b p)) ![(e ⟨b p, v p⟩).2, (e ⟨b p, w p⟩).2]) p₀ :=
    continuous_eval.continuousAt.comp (h1.prodMk hvec)
  refine hev.congr ?_
  filter_upwards [hb.continuousAt.preimage_mem_nhds
    ((trivializationAt E (TangentSpace I) (b p₀)).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt' (b p₀)))] with p hp
  have hvec' : ⇑(e.symmL ℝ (b p)) ∘ ![(e ⟨b p, v p⟩).2, (e ⟨b p, w p⟩).2] = ![v p, w p] := by
    funext i
    fin_cases i <;> exact (e.symmL_apply hp _).trans (e.symm_apply_apply_mk hp _)
  simp only [ContinuousAlternatingMap.inCoordinates, SmoothBundleForm.eval₂_apply,
    ContinuousAlternatingMap.compContinuousLinearMap_apply]
  rw [hvec']
  change ((Bundle.Trivial.trivialization M ℝ).continuousLinearMapAt ℝ
    (b p)).compContinuousAlternatingMap (form.1 (b p)) ![v p, w p] = _
  simp

end SmoothTwoForm

variable {ι : Type*}
  (e : ι → Trivialization (E →L[ℝ] E)
    (π (E →L[ℝ] E) (fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)))
  [∀ i, MemTrivializationAtlas (e i)]
  (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)

namespace SmoothAlmostComplexStructure

/-- For a covering frame system, applying a smooth almost complex structure to a tangent vector is
jointly continuous in the structure, for the `C^∞` topology, and the tangent vector. -/
theorem continuous_apply_frameTopology [LocallyCompactSpace E] (hcover : ∀ x, ∃ i, x ∈ U i) :
    let _ := frameTopology e U hU
    Continuous fun p : SmoothAlmostComplexStructure I M × TangentBundle I M ↦
      TotalSpace.mk' E (E := TangentSpace I) p.2.proj (p.1 p.2.proj p.2.2) := by
  let _ := ContMDiffSection.frameTopology (I := I) (n := ∞) e U hU
  let _ := frameTopology e U hU
  have hϕ : Continuous fun p : SmoothAlmostComplexStructure I M × TangentBundle I M ↦
      TotalSpace.mk' (E →L[ℝ] E) (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        p.2.proj (p.1.toEndomorphism p.2.proj) :=
    (ContMDiffSection.continuous_totalSpace_eval (I := I) (n := ∞) e U hU hcover).comp
      (((isEmbedding_toEndomorphism_frameTopology e U hU).continuous.comp continuous_fst).prodMk
        ((FiberBundle.continuous_proj E (TangentSpace I)).comp continuous_snd))
  exact hϕ.clm_bundle_apply (v := fun p ↦ p.2.2) continuous_snd

end SmoothAlmostComplexStructure

namespace SmoothTwoForm

/-- On a compact manifold with finite-dimensional model, there is a compact set of nonzero tangent
vectors meeting every line through a nonzero tangent vector. -/
private theorem exists_isCompact_forall_ne_zero [FiniteDimensional ℝ E] [CompactSpace M] :
    ∃ K : Set (TangentBundle I M), IsCompact K ∧ (∀ q ∈ K, q.2 ≠ 0) ∧
      ∀ (x : M) (v : TangentSpace I x), v ≠ 0 →
        ∃ c : ℝ, c ≠ 0 ∧ (⟨x, c • v⟩ : TangentBundle I M) ∈ K := by
  have : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
  let T (x : M) := trivializationAt E (TangentSpace I) x
  have (x : M) : (T x).IsLinear ℝ :=
    inferInstanceAs ((trivializationAt E (TangentSpace I) x).IsLinear ℝ)
  have hT (x : M) : (T x).baseSet ∈ 𝓝 x :=
    (T x).open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' x)
  choose C hCx hCT hC using fun x ↦ local_compact_nhds (hT x)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_nhds_subcover C fun x _ ↦ hCx x
  let f (x : M) (p : M × E) : TangentBundle I M := ⟨p.1, (T x).symm p.1 p.2⟩
  have hf (x : M) : ContinuousOn (f x) (C x ×ˢ Metric.sphere 0 1) := by
    exact (T x).continuousOn_symm.mono fun p hp ↦ ⟨hCT x hp.1, mem_univ _⟩
  refine ⟨⋃ x ∈ t, f x '' (C x ×ˢ Metric.sphere 0 1),
    t.isCompact_biUnion fun x _ ↦ ((hC x).prod (isCompact_sphere 0 1)).image_of_continuousOn
      (hf x), ?_, fun y v hv ↦ ?_⟩
  · simp only [mem_iUnion, mem_image]
    rintro q ⟨x, -, ⟨y, a⟩, ⟨hy, ha⟩, rfl⟩ h0
    have hy' := hCT x hy
    have h := (T x).continuousLinearMapAt_symmL (R := ℝ) hy' a
    rw [(T x).symmL_apply hy'] at h
    change (T x).symm y a = 0 at h0
    rw [h0, map_zero] at h
    rw [← h] at ha
    simp at ha
  · obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.1 (ht.2 (mem_univ y))
    have hy' := hCT x hyx
    set a := (T x).continuousLinearMapAt ℝ y v
    have hva : (T x).symmL ℝ y a = v := (T x).symmL_continuousLinearMapAt hy' v
    have ha : a ≠ 0 := by
      rintro h
      rw [h, map_zero] at hva
      exact hv hva.symm
    refine ⟨‖a‖⁻¹, inv_ne_zero (norm_ne_zero_iff.2 ha), mem_iUnion₂.2 ⟨x, hx, ?_⟩⟩
    refine ⟨(y, ‖a‖⁻¹ • a), ⟨hyx, by simp [norm_smul, ha]⟩, ?_⟩
    simp only [f]
    rw [← (T x).symmL_apply (R := ℝ) hy', map_smul, hva]

variable [FiniteDimensional ℝ E]

/-- On a compact manifold, tameness by a smooth two-form is an open condition on smooth almost
complex structures in the `C^∞` topology. -/
theorem isOpen_setOf_tames_frameTopology [CompactSpace M] (hcover : ∀ x, ∃ i, x ∈ U i)
    (form : SmoothTwoForm I M) :
    let _ := SmoothAlmostComplexStructure.frameTopology e U hU
    IsOpen {J : SmoothAlmostComplexStructure I M | form.Tames J} := by
  let _ := SmoothAlmostComplexStructure.frameTopology e U hU
  obtain ⟨K, hK, hK0, hKray⟩ := exists_isCompact_forall_ne_zero (I := I) (M := M)
  have hcont : Continuous fun p : SmoothAlmostComplexStructure I M × TangentBundle I M ↦
      form.eval₂ p.2.proj p.2.2 (p.1 p.2.proj p.2.2) :=
    form.continuous_eval₂ (b := fun p : SmoothAlmostComplexStructure I M × TangentBundle I M ↦
      p.2.proj) continuous_snd
      (SmoothAlmostComplexStructure.continuous_apply_frameTopology e U hU hcover)
  have hset : {J : SmoothAlmostComplexStructure I M | form.Tames J} =
      {J | ∀ q ∈ K, 0 < form.eval₂ q.proj q.2 (J q.proj q.2)} := by
    ext J
    simp only [mem_ofPred_eq, tames_iff]
    refine ⟨fun h q hq ↦ h q.proj q.2 (hK0 q hq), fun h x v hv ↦ ?_⟩
    obtain ⟨c, hc, hcK⟩ := hKray x v hv
    have h' := h _ hcK
    simp only [map_smul, SmoothBundleForm.eval₂_smul_left, SmoothBundleForm.eval₂_smul_right,
      smul_eq_mul, ← mul_assoc] at h'
    exact (mul_pos_iff_of_pos_left (mul_self_pos.2 hc)).1 h'
  rw [hset, isOpen_iff_mem_nhds]
  intro J₀ hJ₀
  exact hK.eventually_forall_of_forall_eventually fun q hq ↦
    (hcont.tendsto (J₀, q)).eventually_const_lt (hJ₀ q hq)

end SmoothTwoForm

namespace SmoothAlmostComplexStructure

variable [FiniteDimensional ℝ E] [I.Boundaryless]

/-- For countably many covering frames on sigma-compact domains, the smooth almost complex
structures with the `C^∞` topology form a completely metrizable space: they are a closed subset
of the complete metrizable space of smooth sections of `End(TM)`. -/
theorem isCompletelyMetrizableSpace_frameTopology_of_sigmaCompactDomains [Countable ι]
    [∀ i, SigmaCompactSpace (U i)] (hcover : ∀ x, ∃ i, x ∈ U i) :
    let _ := frameTopology e U hU
    IsCompletelyMetrizableSpace (SmoothAlmostComplexStructure I M) := by
  let _ := ContMDiffSection.frameUniformSpace (I := I) (n := ∞) e U hU
  let _ := frameTopology e U hU
  have := ContMDiffSection.isUniformAddGroup_frameUniformSpace (I := I) (n := ∞) e U hU
  have := ContMDiffSection.completeSpace_frameTopology (I := I) (n := ∞) e U hU hcover
  have := ContMDiffSection.metrizableSpace_frameTopology_of_sigmaCompactDomains (I := I)
    (n := ∞) e U hU hcover
  have := IsUniformAddGroup.uniformity_countably_generated
    (α := Cₛ^∞⟮I; E →L[ℝ] E, fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x⟯)
  exact (isClosedEmbedding_toEndomorphism_frameTopology e U hU hcover).IsCompletelyMetrizableSpace

/-- On a sigma-compact manifold, the smooth almost complex structures with the `C^∞` topology of
any covering frame system form a completely metrizable space. -/
theorem isCompletelyMetrizableSpace_frameTopology [SigmaCompactSpace M]
    (hcover : ∀ x, ∃ i, x ∈ U i) :
    let _ := frameTopology e U hU
    IsCompletelyMetrizableSpace (SmoothAlmostComplexStructure I M) := by
  have : SecondCountableTopology H := I.secondCountableTopology
  have : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
  have : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  let e' (x : M) := trivializationAt (E →L[ℝ] E)
    (fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) x
  let U' (x : M) : Opens M := ⟨(e' x).baseSet, (e' x).open_baseSet⟩
  obtain ⟨T, hT, hTU⟩ := isOpen_iUnion_countable (fun x ↦ (U' x : Set M)) fun x ↦ (U' x).isOpen
  have := hT.to_subtype
  have hcover' (x : M) : ∃ i : T, x ∈ U' i := by
    have hx : x ∈ ⋃ y, (U' y : Set M) :=
      mem_iUnion.2 ⟨x, FiberBundle.mem_baseSet_trivializationAt _ _ x⟩
    rw [← hTU] at hx
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 hx
    exact ⟨⟨y, hy⟩, hxy⟩
  have (i : T) : SigmaCompactSpace (U' i) := by
    have := (U' i).isOpen.isOpenEmbedding_subtypeVal.locallyCompactSpace
    infer_instance
  have h := isCompletelyMetrizableSpace_frameTopology_of_sigmaCompactDomains
    (fun i : T ↦ e' i) (fun i ↦ U' i) (fun _ ↦ subset_rfl) hcover'
  change @IsCompletelyMetrizableSpace _ (frameTopology e U hU)
  rwa [frameTopology_eq_of_covers e U hU hcover (fun i : T ↦ e' i) (fun i ↦ U' i)
    (fun _ ↦ subset_rfl) hcover']

/-- On a sigma-compact manifold, the smooth almost complex structures with the `C^∞` topology form
a Baire space. -/
theorem baireSpace_frameTopology [SigmaCompactSpace M] (hcover : ∀ x, ∃ i, x ∈ U i) :
    let _ := frameTopology e U hU
    BaireSpace (SmoothAlmostComplexStructure I M) := by
  let _ := frameTopology e U hU
  have := isCompletelyMetrizableSpace_frameTopology e U hU hcover
  infer_instance

end SmoothAlmostComplexStructure

namespace SmoothTwoForm

variable [FiniteDimensional ℝ E] [I.Boundaryless] [CompactSpace M]

/-- On a compact manifold, the smooth almost complex structures tamed by a smooth two-form, with
the `C^∞` topology, form a completely metrizable space: an open subset of a completely metrizable
space. -/
theorem isCompletelyMetrizableSpace_tames_frameTopology (hcover : ∀ x, ∃ i, x ∈ U i)
    (form : SmoothTwoForm I M) :
    let _ := SmoothAlmostComplexStructure.frameTopology e U hU
    IsCompletelyMetrizableSpace {J : SmoothAlmostComplexStructure I M // form.Tames J} := by
  let _ := SmoothAlmostComplexStructure.frameTopology e U hU
  have := SmoothAlmostComplexStructure.isCompletelyMetrizableSpace_frameTopology e U hU hcover
  exact (isOpen_setOf_tames_frameTopology e U hU hcover form).isCompletelyMetrizableSpace

/-- On a compact manifold, the smooth almost complex structures compatible with a smooth two-form,
with the `C^∞` topology, form a completely metrizable space: the intersection of the open set of
tame structures with the closed set of invariant ones. -/
theorem isCompletelyMetrizableSpace_compatible_frameTopology (hcover : ∀ x, ∃ i, x ∈ U i)
    (form : SmoothTwoForm I M) :
    let _ := SmoothAlmostComplexStructure.frameTopology e U hU
    IsCompletelyMetrizableSpace {J : SmoothAlmostComplexStructure I M // form.Compatible J} := by
  let _ := SmoothAlmostComplexStructure.frameTopology e U hU
  have := SmoothAlmostComplexStructure.isCompletelyMetrizableSpace_frameTopology e U hU hcover
  have hset : {J : SmoothAlmostComplexStructure I M | form.Compatible J} =
      {J | form.Tames J} ∩ {J | form.Invariant J} := by
    ext J
    exact ⟨fun h ↦ ⟨h.tames, h.invariant⟩, fun h ↦ ⟨h.2, h.1⟩⟩
  have hG : IsGδ {J : SmoothAlmostComplexStructure I M | form.Compatible J} := by
    rw [hset]
    exact (isOpen_setOf_tames_frameTopology e U hU hcover form).isGδ.inter
      (isClosed_setOf_invariant_frameTopology e U hU hcover form).isGδ
  exact hG.isCompletelyMetrizableSpace

/-- On a compact manifold, the smooth almost complex structures tamed by a smooth two-form, with
the `C^∞` topology, form a Baire space. -/
theorem baireSpace_tames_frameTopology (hcover : ∀ x, ∃ i, x ∈ U i)
    (form : SmoothTwoForm I M) :
    let _ := SmoothAlmostComplexStructure.frameTopology e U hU
    BaireSpace {J : SmoothAlmostComplexStructure I M // form.Tames J} := by
  let _ := SmoothAlmostComplexStructure.frameTopology e U hU
  have := isCompletelyMetrizableSpace_tames_frameTopology e U hU hcover form
  infer_instance

/-- On a compact manifold, the smooth almost complex structures compatible with a smooth two-form,
with the `C^∞` topology, form a Baire space. -/
theorem baireSpace_compatible_frameTopology (hcover : ∀ x, ∃ i, x ∈ U i)
    (form : SmoothTwoForm I M) :
    let _ := SmoothAlmostComplexStructure.frameTopology e U hU
    BaireSpace {J : SmoothAlmostComplexStructure I M // form.Compatible J} := by
  let _ := SmoothAlmostComplexStructure.frameTopology e U hU
  have := isCompletelyMetrizableSpace_compatible_frameTopology e U hU hcover form
  infer_instance

end SmoothTwoForm

end TauCeti
