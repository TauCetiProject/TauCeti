/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.FrameCover
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm

/-!
# The `C^∞` topology on smooth almost complex structures

A smooth almost complex structure is a smooth section of the tangent endomorphism bundle
`End(TM)` squaring to `-1`. `TauCeti.SmoothAlmostComplexStructure.frameTopology` is the subspace
topology induced by `ContMDiffSection.frameTopology` on these sections: convergence of every
derivative of the frame coefficients, uniformly on compact coordinate sets. This is the `C^∞`
topology on compact sources used for spaces of almost complex structures in symplectic topology.

As for sections, the topology is supplied explicitly, since the frame domains of `End(TM)` are
parameters. For a covering frame system the topology is Hausdorff, the endomorphism section is a
closed embedding (the identity `J² = -1` is a closed condition on sections), and, for a locally
compact model space (in particular a finite-dimensional one), the topology does not depend on the
covering frames. Point evaluation is continuous.

For a smooth two-form `ω`, the spaces of `ω`-tame and of `ω`-compatible smooth almost complex
structures are the subtypes `{J // ω.Tames J}` and `{J // ω.Compatible J}` with the subspace
topology. Invariance of `ω` is a closed condition, so the compatible structures form a closed
subspace of the tame ones. Tameness is a pointwise open condition, but it is not open for this
topology on a noncompact manifold, so no openness is asserted. Nonemptiness of these spaces for a
nondegenerate form on a Hausdorff σ-compact manifold is
`TauCeti.SmoothTwoForm.IsNondegenerate.exists_compatible`.

## Main declarations

* `TauCeti.SmoothAlmostComplexStructure.frameTopology`: the `C^∞` topology on smooth almost complex
  structures in specified frames of `End(TM)`.
* `TauCeti.SmoothAlmostComplexStructure.isClosedEmbedding_toEndomorphism_frameTopology`: for a
  covering frame system, the endomorphism section is a closed embedding.
* `TauCeti.SmoothAlmostComplexStructure.frameTopology_eq_of_covers`: for a locally compact model
  space, independence of the covering frames.
* `TauCeti.SmoothTwoForm.isClosed_setOf_invariant_frameTopology`: invariance of a smooth two-form
  is a closed condition.
* `TauCeti.SmoothTwoForm.isClosed_setOf_invariant_tames_frameTopology`: compatible structures
  form a closed subspace of the tame structures.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 3.2.
* M. Hirsch, *Differential Topology*, GTM 33, Chapter 2, §1.
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
variable {ι : Type*}
  (e : ι → Trivialization (E →L[ℝ] E)
    (π (E →L[ℝ] E) (fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)))
  [∀ i, MemTrivializationAtlas (e i)]
  (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)

namespace SmoothAlmostComplexStructure

/-- The `C^∞` topology on smooth almost complex structures: the topology induced by the compact
derivative topology `ContMDiffSection.frameTopology` on sections of `End(TM)`, in the specified
frames. -/
@[instance_reducible]
def frameTopology : TopologicalSpace (SmoothAlmostComplexStructure I M) :=
  .induced toEndomorphism (ContMDiffSection.frameTopology (I := I) (n := ∞) e U hU)

/-- The endomorphism section is an embedding for the `C^∞` topology. -/
theorem isEmbedding_toEndomorphism_frameTopology :
    let _ := ContMDiffSection.frameTopology (I := I) (n := ∞) e U hU
    let _ := frameTopology e U hU
    IsEmbedding (toEndomorphism : SmoothAlmostComplexStructure I M → _) := by
  let _ := ContMDiffSection.frameTopology (I := I) (n := ∞) e U hU
  let _ := frameTopology e U hU
  exact ⟨.induced _, toEndomorphism_injective⟩

/-- A family of smooth almost complex structures is continuous exactly when its family of
endomorphism sections is continuous. -/
theorem continuous_frameTopology_iff {P : Type*} [TopologicalSpace P]
    {J : P → SmoothAlmostComplexStructure I M} :
    let _ := ContMDiffSection.frameTopology (I := I) (n := ∞) e U hU
    let _ := frameTopology e U hU
    Continuous J ↔ Continuous (fun p ↦ (J p).toEndomorphism) := by
  let _ := ContMDiffSection.frameTopology (I := I) (n := ∞) e U hU
  let _ := frameTopology e U hU
  exact (isEmbedding_toEndomorphism_frameTopology e U hU).isInducing.continuous_iff

/-- Convergence of smooth almost complex structures is convergence of their endomorphism
sections. -/
theorem tendsto_frameTopology_iff {P : Type*} {l : Filter P}
    {J : P → SmoothAlmostComplexStructure I M} {J₀ : SmoothAlmostComplexStructure I M} :
    let _ := ContMDiffSection.frameTopology (I := I) (n := ∞) e U hU
    let _ := frameTopology e U hU
    Tendsto J l (𝓝 J₀) ↔ Tendsto (fun p ↦ (J p).toEndomorphism) l (𝓝 J₀.toEndomorphism) := by
  let _ := ContMDiffSection.frameTopology (I := I) (n := ∞) e U hU
  let _ := frameTopology e U hU
  exact (isEmbedding_toEndomorphism_frameTopology e U hU).isInducing.tendsto_nhds_iff

/-- For a covering frame system, evaluating a smooth almost complex structure at a point is
continuous into the endomorphisms of that tangent space. -/
theorem continuous_toEndomorphism_apply_frameTopology (hcover : ∀ x, ∃ i, x ∈ U i) (x : M) :
    let _ := frameTopology e U hU
    Continuous (fun J : SmoothAlmostComplexStructure I M ↦ J.toEndomorphism x) := by
  let _ := ContMDiffSection.frameTopology (I := I) (n := ∞) e U hU
  let _ := frameTopology e U hU
  exact (ContMDiffSection.continuous_eval_const (I := I) (n := ∞) e U hU hcover x).comp
    (isEmbedding_toEndomorphism_frameTopology e U hU).continuous

/-- For a covering frame system, the sections of `End(TM)` squaring to `-1` form a closed set, so
the endomorphism section is a closed embedding for the `C^∞` topology. -/
theorem isClosedEmbedding_toEndomorphism_frameTopology (hcover : ∀ x, ∃ i, x ∈ U i) :
    let _ := ContMDiffSection.frameTopology (I := I) (n := ∞) e U hU
    let _ := frameTopology e U hU
    IsClosedEmbedding (toEndomorphism : SmoothAlmostComplexStructure I M → _) := by
  let _ := ContMDiffSection.frameTopology (I := I) (n := ∞) e U hU
  let _ := frameTopology e U hU
  refine ⟨isEmbedding_toEndomorphism_frameTopology e U hU, ?_⟩
  -- The fibre `TangentSpace I x →L[ℝ] TangentSpace I x` is by definition `E →L[ℝ] E`, so the
  -- fibrewise condition `J ∘ J = -1` and evaluation at `x` are stated on `E →L[ℝ] E`, whose
  -- normed structure gives continuity of composition.
  have hrange : range (toEndomorphism : SmoothAlmostComplexStructure I M → _) =
      ⋂ x : M, {s | (s x : E →L[ℝ] E).comp (s x) = -ContinuousLinearMap.id ℝ E} := by
    ext s
    simp only [mem_range, mem_iInter, mem_ofPred_eq]
    exact ⟨fun ⟨J, hJ⟩ ↦ hJ ▸ J.square_neg, fun h ↦ ⟨⟨s, h⟩, rfl⟩⟩
  rw [hrange]
  refine isClosed_iInter fun x ↦ ?_
  let ev : Cₛ^∞⟮I; E →L[ℝ] E, fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x⟯ →
      (E →L[ℝ] E) := fun s ↦ s x
  have hx : Continuous ev :=
    ContMDiffSection.continuous_eval_const (I := I) (n := ∞) e U hU hcover x
  exact isClosed_eq (f := fun s ↦ (ev s).comp (ev s))
    (isBoundedBilinearMap_comp.continuous.comp (hx.prodMk hx)) continuous_const

/-- A covering frame system gives a Hausdorff `C^∞` topology on smooth almost complex
structures. -/
theorem t2Space_frameTopology (hcover : ∀ x, ∃ i, x ∈ U i) :
    let _ := frameTopology e U hU
    T2Space (SmoothAlmostComplexStructure I M) := by
  let _ := ContMDiffSection.frameTopology (I := I) (n := ∞) e U hU
  let _ := frameTopology e U hU
  let _ := ContMDiffSection.t2Space_frameTopology (I := I) (n := ∞) e U hU hcover
  exact (isEmbedding_toEndomorphism_frameTopology e U hU).t2Space

/-- For a locally compact model space `E` (in particular a finite-dimensional one), the `C^∞`
topology on smooth almost complex structures does not depend on the covering frames of `End(TM)`. -/
theorem frameTopology_eq_of_covers [LocallyCompactSpace E] (hcover : ∀ x, ∃ i, x ∈ U i)
    {κ : Type*}
    (e' : κ → Trivialization (E →L[ℝ] E)
      (π (E →L[ℝ] E) (fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)))
    [∀ j, MemTrivializationAtlas (e' j)]
    (U' : κ → Opens M) (hU' : ∀ j, (U' j : Set M) ⊆ (e' j).baseSet)
    (hcover' : ∀ x, ∃ j, x ∈ U' j) :
    frameTopology e U hU = frameTopology e' U' hU' := by
  unfold frameTopology
  rw [ContMDiffSection.frameTopology_eq_of_covers e U hU hcover e' U' hU' hcover']

/-- Negation of smooth almost complex structures is continuous for the `C^∞` topology. -/
theorem continuous_neg_frameTopology :
    let _ := frameTopology e U hU
    Continuous (fun J : SmoothAlmostComplexStructure I M ↦ -J) := by
  let _ := ContMDiffSection.frameTopology (I := I) (n := ∞) e U hU
  let _ := frameTopology e U hU
  let _ := ContMDiffSection.isTopologicalAddGroup_frameTopology (I := I) (n := ∞) e U hU
  refine (continuous_frameTopology_iff e U hU).mpr ?_
  simp only [neg_toEndomorphism]
  exact continuous_neg.comp (isEmbedding_toEndomorphism_frameTopology e U hU).continuous

end SmoothAlmostComplexStructure

namespace SmoothTwoForm

/-- For a covering frame system, the smooth almost complex structures leaving a smooth two-form
invariant form a closed set in the `C^∞` topology. -/
theorem isClosed_setOf_invariant_frameTopology (hcover : ∀ x, ∃ i, x ∈ U i)
    (form : SmoothTwoForm I M) :
    let _ := SmoothAlmostComplexStructure.frameTopology e U hU
    IsClosed {J : SmoothAlmostComplexStructure I M | form.Invariant J} := by
  let _ := SmoothAlmostComplexStructure.frameTopology e U hU
  have hset : {J : SmoothAlmostComplexStructure I M | form.Invariant J} =
      ⋂ (x : M) (v : TangentSpace I x) (w : TangentSpace I x),
        {J | form.eval₂ x (J x v) (J x w) = form.eval₂ x v w} := by
    ext J
    simp only [invariant_iff, mem_iInter, mem_ofPred_eq]
  rw [hset]
  refine isClosed_iInter fun x ↦ isClosed_iInter fun v ↦ isClosed_iInter fun w ↦ ?_
  have hx := SmoothAlmostComplexStructure.continuous_toEndomorphism_apply_frameTopology
    e U hU hcover x
  refine isClosed_eq ?_ continuous_const
  have hv : Continuous (fun J : SmoothAlmostComplexStructure I M ↦ J x v) :=
    (continuous_eval_const v).comp hx
  have hw : Continuous (fun J : SmoothAlmostComplexStructure I M ↦ J x w) :=
    (continuous_eval_const w).comp hx
  simp only [SmoothBundleForm.eval₂_apply]
  exact (form.1 x).coe_continuous.comp (continuous_pi fun k ↦ by fin_cases k <;> simpa)

/-- For a covering frame system, the compatible structures form a closed subspace of the space of
tame smooth almost complex structures with the `C^∞` topology. -/
theorem isClosed_setOf_invariant_tames_frameTopology (hcover : ∀ x, ∃ i, x ∈ U i)
    (form : SmoothTwoForm I M) :
    let _ := SmoothAlmostComplexStructure.frameTopology e U hU
    IsClosed {J : {J : SmoothAlmostComplexStructure I M // form.Tames J} | form.Invariant J} := by
  let _ := SmoothAlmostComplexStructure.frameTopology e U hU
  exact (isClosed_setOf_invariant_frameTopology e U hU hcover form).preimage continuous_subtype_val

end SmoothTwoForm

end TauCeti
