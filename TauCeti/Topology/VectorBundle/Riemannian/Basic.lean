/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.VectorBundle.Riemannian

/-!
# Continuity and compactness in Riemannian vector bundles

In a vector bundle whose fibers carry inner products depending continuously on the base point,
the fiber norm is a continuous function on the total space.  When the model fiber is
finite-dimensional, this file proves that the vectors of norm at most `r` lying over a compact
subset of the base form a compact subset of the total space.  The compactness statement holds more
generally for fiber norms that are continuous on the total space and for which each
trivialization is locally bounded, as for the operator norm on covectors. Similarly, the pointwise
inner product of two continuous sections for a `Bundle.ContinuousRiemannianMetric`, which need not
be registered as a `RiemannianBundle` instance, is continuous.

This is the properness statement that turns a bound on the speed of a curve in the base together
with relative compactness of its image into relative compactness of its velocity lift.  The
part of the bundle lying over a compact set need not be compact on its own: the fibers of a
bundle with a positive-dimensional model fiber are noncompact, so the norm bound is what makes
the statement true.  The proof is local: near each point of the base, the fiber norm bounds the
model norm of the coordinates in the trivialization at that point (in the Riemannian case by
`eventually_norm_trivializationAt_lt`), so the coordinates of a convergent ultrafilter of bounded
vectors converge too.

Pulling a continuous metric back along a continuously evaluated family of linear maps gives a
continuous family of bilinear forms on a fixed finite-dimensional model. This does not require
continuous reference inner products on the fibres.

## Main results

* `Continuous.norm_bundle`: the fiber norm of a continuous map into the fibers of a continuous
  Riemannian bundle is continuous, with `TauCeti.continuous_norm_bundle` its tautological case.
* `Bundle.Trivialization.continuousAt_norm_symmL`: in a continuous Riemannian bundle, the fiber
  norm of `e.symmL ℝ (b x) (w x)` is continuous at `x₀` when `b` and `w` are continuous at `x₀`
  and `b x₀ ∈ e.baseSet`.
* `Bundle.Trivialization.continuousOn_innerSL_comp_symmL`: the covectors `⟪η x, ·⟫` of a
  section continuous on a subset of the base set of a trivialization, read in it, are continuous
  there.
* `IsOpen.norm_lt_bundle`: the vectors of norm less than `r` over an open set form an open subset
  of the total space.
* `IsCompact.norm_le_bundle`: the vectors of norm at most `r` over a compact set form a compact
  subset of the total space.
* `IsCompact.norm_le_bundle_of_continuous`: the same for a continuous fiber norm with locally
  bounded trivializations.
* `Bundle.RiemannianMetric.isSymm_toBilinForm_inner`: the inner product of a Riemannian metric
  on a fiber is a symmetric bilinear form.
* `Bundle.RiemannianMetric.inner_self_nonneg`: the diagonal values `g(v, v)` of a metric are
  nonnegative.
* `Bundle.ContinuousRiemannianMetric.continuous_inner`: the pointwise inner product of two
  continuous maps into the fibers is continuous, with versions `continuousWithinAt_inner`,
  `continuousAt_inner` and `continuousOn_inner`.
* `Bundle.ContinuousRiemannianMetric.hasCompactSupport_inner`: the scalar pairing is compactly
  supported when either section is compactly supported.
-/

public section

open Bundle Filter Set
open scoped Topology

variable
  {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ x, NormedAddCommGroup (E x)]

section Norm

variable [∀ x, InnerProductSpace ℝ (E x)] [FiberBundle F E] [VectorBundle ℝ F E]
  [IsContinuousRiemannianBundle F E]

variable {X : Type*} [TopologicalSpace X] {b : X → B} {v : ∀ x, E (b x)}

/-- Given a continuous map into the fibers of a continuous Riemannian bundle, its fiber norm is
a continuous function. -/
theorem Continuous.norm_bundle (hv : Continuous fun x ↦ (v x : TotalSpace F E)) :
    Continuous fun x ↦ ‖v x‖ := by
  simp only [norm_eq_sqrt_real_inner]
  exact (hv.inner_bundle hv).sqrt

namespace TauCeti

variable (F E) in
/-- In a continuous Riemannian bundle, the fiber norm is a continuous function on the total
space. -/
theorem continuous_norm_bundle : Continuous fun z : TotalSpace F E ↦ ‖z.snd‖ :=
  Continuous.norm_bundle (b := TotalSpace.proj) (v := fun z ↦ z.snd)
    (continuous_id.congr fun z ↦ (TotalSpace.eta z).symm)

end TauCeti

/-- In a continuous Riemannian bundle, the fiber norm of `e.symmL ℝ (b x) (w x)` is continuous at
`x₀` whenever `b` and `w` are continuous at `x₀` and `b x₀ ∈ e.baseSet`. -/
theorem Bundle.Trivialization.continuousAt_norm_symmL (e : Trivialization F (π F E))
    [e.IsLinear ℝ] {w : X → F} {x₀ : X} (hb : ContinuousAt b x₀) (hw : ContinuousAt w x₀)
    (hb₀ : b x₀ ∈ e.baseSet) :
    ContinuousAt (fun x ↦ ‖e.symmL ℝ (b x) (w x)‖) x₀ := by
  have hsec : ContinuousAt (fun x ↦ TotalSpace.mk' F (b x) (e.symmL ℝ (b x) (w x))) x₀ := by
    refine ((e.continuousOn_symm.continuousAt
      ((e.open_baseSet.prod isOpen_univ).mem_nhds ⟨hb₀, mem_univ _⟩)).comp
      (hb.prodMk hw)).congr_of_eventuallyEq ?_
    filter_upwards [hb.preimage_mem_nhds (e.open_baseSet.mem_nhds hb₀)] with x hx
    simp [e.symmL_apply hx]
  exact (TauCeti.continuous_norm_bundle F E).continuousAt.comp hsec

/-- **Pairing with a continuous section in a trivialization.** For a section `η` of a continuous
Riemannian bundle with finite-dimensional model fiber, continuous on a subset `s` of the base set
of a trivialization `e`, the covectors `⟪η x, ·⟫` read in `e`, `x ↦ ⟪η x, ·⟫ ∘L e.symmL ℝ x`,
depend continuously on `x ∈ s`. -/
theorem Bundle.Trivialization.continuousOn_innerSL_comp_symmL [FiniteDimensional ℝ F]
    (e : Trivialization F (π F E)) [e.IsLinear ℝ] {η : ∀ x, E x} {s : Set B}
    (hs : s ⊆ e.baseSet) (hη : ContinuousOn (fun x ↦ TotalSpace.mk' F x (η x)) s) :
    ContinuousOn (fun x ↦ innerSL ℝ (η x) ∘L e.symmL ℝ x) s := by
  refine continuousOn_clm_apply.2 fun v ↦ ?_
  -- The section `x ↦ e.symm x v` is continuous on `s`.
  have hv : ContinuousOn (fun x ↦ TotalSpace.mk' F x (e.symm x v)) s :=
    (e.continuousOn_symm.mono (prod_mono hs subset_rfl)).comp
      (continuousOn_id.prodMk continuousOn_const) fun x hx ↦ ⟨hx, mem_univ v⟩
  refine (hη.inner_bundle hv).congr fun x hx ↦ ?_
  rw [ContinuousLinearMap.comp_apply, innerSL_apply_apply, e.symmL_apply (hs hx)]

/-- In a continuous Riemannian bundle, the vectors of norm less than `r` lying over an open subset
of the base form an open subset of the total space. -/
theorem IsOpen.norm_lt_bundle {U : Set B} (hU : IsOpen U) (r : ℝ) :
    IsOpen {z : TotalSpace F E | z.proj ∈ U ∧ ‖z.snd‖ < r} :=
  (hU.preimage (FiberBundle.continuous_proj F E)).inter
    (isOpen_lt (TauCeti.continuous_norm_bundle F E) continuous_const)

end Norm

section Compact

variable [FiniteDimensional ℝ F]

section General

variable [∀ x, NormedSpace ℝ (E x)] [FiberBundle F E] [VectorBundle ℝ F E]

/-- **The norm-bounded part of a normed vector bundle over a compact set is compact.** Let the
fibers of a vector bundle with finite-dimensional model fiber carry norms, such that the fiber
norm is continuous on the total space and each trivialization is bounded in norm near its base
point. Then the vectors of norm at most `r` lying over a compact subset of the base form a compact
subset of the total space. -/
theorem IsCompact.norm_le_bundle_of_continuous
    (hnorm : Continuous fun z : TotalSpace F E ↦ ‖z.snd‖)
    (hloc : ∀ x, ∃ C, ∀ᶠ y in 𝓝 x, ∀ w : E y,
      ‖(trivializationAt F E x).continuousLinearMapAt ℝ y w‖ ≤ C * ‖w‖)
    {K : Set B} (hK : IsCompact K) (r : ℝ) :
    IsCompact {z : TotalSpace F E | z.proj ∈ K ∧ ‖z.snd‖ ≤ r} := by
  refine isCompact_iff_ultrafilter_le_nhds'.2 fun 𝒰 hS ↦ ?_
  -- The base points converge to some `x ∈ K`.
  obtain ⟨x, hxK, hx⟩ := hK.ultrafilter_le_nhds' (𝒰.map TotalSpace.proj)
    (Ultrafilter.mem_map.2 (mem_of_superset hS fun _ hz ↦ hz.1))
  replace hx : Tendsto (TotalSpace.proj : TotalSpace F E → B) 𝒰 (𝓝 x) := hx
  set e := trivializationAt F E x
  have hxe : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  obtain ⟨C, hC⟩ := hloc x
  have hU : {z : TotalSpace F E | z.proj ∈ e.baseSet ∧
      ∀ w, ‖e.continuousLinearMapAt ℝ z.proj w‖ ≤ C * ‖w‖} ∈ 𝒰 :=
    hx (inter_mem (e.open_baseSet.mem_nhds hxe) hC)
  -- The fiber coordinates in `e` are bounded, so they converge to some `v`.
  obtain ⟨v, -, hv⟩ := (isCompact_closedBall (0 : F) (|C| * r)).ultrafilter_le_nhds'
    (𝒰.map fun z ↦ (e z).2) <| Ultrafilter.mem_map.2 <| mem_of_superset (inter_mem hS hU)
      fun z ⟨⟨_, hzr⟩, hzb, hzC⟩ ↦ by
        have h := hzC z.snd
        rw [Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) e hzb] at h
        exact mem_closedBall_zero_iff.2 <| h.trans <|
          (mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg _)).trans
            (mul_le_mul_of_nonneg_left hzr (abs_nonneg C))
  -- `hv` is about the second coordinate of `e`, which is `(e z).2` by definition.
  replace hv : Tendsto (fun z ↦ (e z).2) (𝒰 : Filter (TotalSpace F E)) (𝓝 v) := hv
  -- So the vectors converge to the vector with coordinates `(x, v)`.
  have hsource : e.source ∈ 𝒰 := mem_of_superset hU fun z hz ↦ e.mem_source.2 hz.1
  have he : Tendsto e 𝒰 (𝓝 (x, v)) :=
    -- A pair is determined by its components; the second components agree by `rfl`.
    (hx.prodMk_nhds hv).congr' (mem_of_superset hsource fun z hz ↦
      show (z.proj, (e z).2) = e z from Prod.ext (e.coe_fst hz).symm rfl)
  have hlim : (𝒰 : Filter (TotalSpace F E)) ≤ 𝓝 (e.toOpenPartialHomeomorph.symm (x, v)) :=
    tendsto_id'.1 <| ((e.continuousAt_symm (e.mem_target.2 hxe)).tendsto.comp he).congr'
      (mem_of_superset hsource fun z hz ↦ e.left_inv hz)
  refine ⟨_, ⟨?_, ?_⟩, hlim⟩
  · rwa [e.proj_symm_apply' hxe]
  · exact (isClosed_le hnorm continuous_const).mem_of_tendsto hlim
      (mem_of_superset hS fun _ hz ↦ hz.2)

end General

variable [∀ x, InnerProductSpace ℝ (E x)] [FiberBundle F E] [VectorBundle ℝ F E]
  [IsContinuousRiemannianBundle F E]

/-- **The norm-bounded part of a Riemannian bundle over a compact set is compact.** In a
continuous Riemannian vector bundle with finite-dimensional model fiber, the vectors of norm at
most `r` lying over a compact subset of the base form a compact subset of the total space. -/
theorem IsCompact.norm_le_bundle {K : Set B} (hK : IsCompact K) (r : ℝ) :
    IsCompact {z : TotalSpace F E | z.proj ∈ K ∧ ‖z.snd‖ ≤ r} :=
  hK.norm_le_bundle_of_continuous (TauCeti.continuous_norm_bundle F E)
    (fun x ↦ (eventually_norm_trivializationAt_lt F E x).imp fun _ h ↦
      h.2.mono fun _ hy ↦ (ContinuousLinearMap.le_of_opNorm_le _ hy.le)) r

end Compact

namespace Bundle.RiemannianMetric

variable {B : Type*} {E : B → Type*} [∀ b, TopologicalSpace (E b)] [∀ b, AddCommGroup (E b)]
  [∀ b, Module ℝ (E b)]

/-- The inner product of a Riemannian metric on a fiber is a symmetric bilinear form. -/
theorem isSymm_toBilinForm_inner (g : RiemannianMetric E) (b : B) :
    (g.inner b).toBilinForm.IsSymm :=
  LinearMap.BilinForm.isSymm_def.mpr (g.symm b)

/-- The diagonal values of a Riemannian metric are nonnegative. -/
theorem inner_self_nonneg (g : RiemannianMetric E) (b : B) (v : E b) : 0 ≤ g.inner b v v := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  · exact (g.pos b v hv).le

end Bundle.RiemannianMetric

namespace Bundle.ContinuousRiemannianMetric

section Inner

variable {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ x, TopologicalSpace (E x)]
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)] [FiberBundle F E] [VectorBundle ℝ F E]
  {X : Type*} [TopologicalSpace X] {b : X → B} {v w : ∀ x, E (b x)} {s : Set X} {x₀ : X}

/-- The diagonal values of a continuous Riemannian metric are nonnegative. -/
theorem inner_self_nonneg (g : ContinuousRiemannianMetric F E) (b : B) (v : E b) :
    0 ≤ g.inner b v v :=
  g.toRiemannianMetric.inner_self_nonneg b v

/-- Sections have compactly supported scalar pairing if either factor is compactly supported. -/
theorem hasCompactSupport_inner (h : ContinuousRiemannianMetric F E) {ξ η : ∀ x, E x}
    (hc : IsCompact (closure {x | ξ x ≠ 0}) ∨ IsCompact (closure {x | η x ≠ 0})) :
    HasCompactSupport (fun x ↦ h.inner x (ξ x) (η x)) := by
  rcases hc with hc | hc
  · exact hc.of_isClosed_subset isClosed_closure
      (closure_mono fun x hx hξ ↦ hx (by simp [hξ]))
  · exact hc.of_isClosed_subset isClosed_closure
      (closure_mono fun x hx hη ↦ hx (by simp [hη]))

/-- The pointwise inner product, for a continuous Riemannian metric, of two maps into the same
fibers that are continuous within `s` at `x₀` is continuous within `s` at `x₀`. -/
theorem continuousWithinAt_inner (g : ContinuousRiemannianMetric F E)
    (hv : ContinuousWithinAt (fun x ↦ TotalSpace.mk' F (b x) (v x)) s x₀)
    (hw : ContinuousWithinAt (fun x ↦ TotalSpace.mk' F (b x) (w x)) s x₀) :
    ContinuousWithinAt (fun x ↦ g.inner (b x) (v x) (w x)) s x₀ :=
  continuous_snd.continuousAt.comp_continuousWithinAt <|
    (Trivial.homeomorphProd B ℝ).continuous.continuousAt.comp_continuousWithinAt <|
      ContinuousWithinAt.clm_bundle_apply₂ (F₁ := F) (F₂ := F) (E₃ := Trivial B ℝ)
        (g.continuous.continuousAt.comp_continuousWithinAt
          ((FiberBundle.continuous_proj F E).continuousAt.comp_continuousWithinAt hv)) hv hw

/-- The pointwise inner product, for a continuous Riemannian metric, of two maps into the same
fibers that are continuous at `x₀` is continuous at `x₀`. -/
theorem continuousAt_inner (g : ContinuousRiemannianMetric F E)
    (hv : ContinuousAt (fun x ↦ TotalSpace.mk' F (b x) (v x)) x₀)
    (hw : ContinuousAt (fun x ↦ TotalSpace.mk' F (b x) (w x)) x₀) :
    ContinuousAt (fun x ↦ g.inner (b x) (v x) (w x)) x₀ := by
  simp only [← continuousWithinAt_univ] at hv hw ⊢
  exact g.continuousWithinAt_inner hv hw

/-- The pointwise inner product, for a continuous Riemannian metric, of two maps into the same
fibers that are continuous on `s` is continuous on `s`. -/
theorem continuousOn_inner (g : ContinuousRiemannianMetric F E)
    (hv : ContinuousOn (fun x ↦ TotalSpace.mk' F (b x) (v x)) s)
    (hw : ContinuousOn (fun x ↦ TotalSpace.mk' F (b x) (w x)) s) :
    ContinuousOn (fun x ↦ g.inner (b x) (v x) (w x)) s :=
  fun x hx ↦ g.continuousWithinAt_inner (hv x hx) (hw x hx)

/-- The pointwise inner product, for a continuous Riemannian metric, of two continuous maps into
the same fibers is continuous. -/
theorem continuous_inner (g : ContinuousRiemannianMetric F E)
    (hv : Continuous fun x ↦ TotalSpace.mk' F (b x) (v x))
    (hw : Continuous fun x ↦ TotalSpace.mk' F (b x) (w x)) :
    Continuous fun x ↦ g.inner (b x) (v x) (w x) :=
  continuous_iff_continuousAt.2 fun _ ↦ g.continuousAt_inner hv.continuousAt hw.continuousAt

end Inner

section BilinearComp

variable [∀ x, NormedSpace ℝ (E x)] [FiberBundle F E] [VectorBundle ℝ F E]

/-- Pulling a continuous Riemannian metric back along a family of linear maps whose evaluations
are continuous gives a continuous family of bilinear forms on a fixed model. -/
theorem continuous_inner_bilinearComp (h : ContinuousRiemannianMetric F E)
    {X V : Type*} [TopologicalSpace X]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {f : X → B}
    (σ : ∀ x, V →L[ℝ] E (f x))
    (hσ : ∀ w, Continuous fun x ↦ TotalSpace.mk' F (f x) (σ x w)) :
    Continuous fun x ↦ (h.inner (f x)).bilinearComp (σ x) (σ x) :=
  continuous_clm_apply.2 fun w ↦ continuous_clm_apply.2 fun w' ↦
    h.continuous_inner (hσ w) (hσ w')

end BilinearComp

end Bundle.ContinuousRiemannianMetric
