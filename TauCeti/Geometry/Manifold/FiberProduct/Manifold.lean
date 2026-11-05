/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.FiberProduct.Local
import TauCeti.Geometry.Manifold.Gluing.Basic
import TauCeti.Geometry.Manifold.Immersion.Basic
import TauCeti.Geometry.Manifold.Immersion.LocalDiffeomorph

/-!
# Transverse fibre products of manifolds

For transverse smooth maps `f : X → N` and `g : Y → N`, the subtype
`{p : X × Y // f p.1 = g p.2}` is an embedded manifold with its inherited topology and
model dimension `dim X + dim Y - dim N`. Its tangent vectors are exactly the pairs with
equal images under the differentials of `f` and `g`.

`TauCeti.exists_transverseFiberProduct_smoothEmbedding` glues the coordinate-patch fibre
products of `PartialDiffeomorph.exists_isManifold_localFiberProduct_isSmoothEmbedding`.
The returned embedding gives the smooth universal property via
`Manifold.IsSmoothEmbedding.contMDiff_iff_comp`: a map into the fibre product is smooth
exactly when both component maps are smooth. In particular both projections are smooth.
No Hausdorff or countability assumptions are used, and the fibre product may be empty.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer (2013),
  Theorem 6.30 (transverse preimages), applied to the diagonal in `N × N`.
-/

public section

open Function Set Module Filter Topology
open scoped Manifold ContDiff

namespace TauCeti

variable {EX HX X EY HY Y EN HN N : Type*}
  [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
  [NormedAddCommGroup EY] [NormedSpace ℝ EY] [TopologicalSpace HY]
  [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
  {IX : ModelWithCorners ℝ EX HX} {IY : ModelWithCorners ℝ EY HY}
  {IN : ModelWithCorners ℝ EN HN}
  [TopologicalSpace X] [ChartedSpace HX X]
  [TopologicalSpace Y] [ChartedSpace HY Y]
  [TopologicalSpace N] [ChartedSpace HN N]
  {n : ℕ∞ω} [IsManifold IN n N] {f : X → N} {g : Y → N}

private abbrev fiberProductPatch (a : N) :=
  {p : X × Y // f p.1 = g p.2 ∧ f p.1 ∈ (extChartPartialDiffeomorph IN n a).source}

private def fiberProductPatchInclusion (a : N) :
    fiberProductPatch (IN := IN) (n := n) (f := f) (g := g) a →
      {p : X × Y // f p.1 = g p.2} :=
  fun p ↦ ⟨p.1, p.2.1⟩

private theorem isOpenEmbedding_fiberProductPatchInclusion (hf : Continuous f) (a : N) :
    IsOpenEmbedding (fiberProductPatchInclusion (IN := IN) (n := n) (f := f) (g := g) a) := by
  let U : Set {p : X × Y // f p.1 = g p.2} :=
    {p | f p.1.1 ∈ (extChartPartialDiffeomorph IN n a).source}
  have hU : IsOpen U := (extChartPartialDiffeomorph IN n a).open_source.preimage
    (hf.comp (continuous_fst.comp continuous_subtype_val))
  let e : fiberProductPatch (IN := IN) (n := n) (f := f) (g := g) a ≃ₜ U :=
    { toEquiv := (Equiv.subtypeSubtypeEquivSubtypeInter
        (fun p : X × Y ↦ f p.1 = g p.2)
        (fun p ↦ f p.1 ∈ (extChartPartialDiffeomorph IN n a).source)).symm
      continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
      continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _ }
  exact hU.isOpenEmbedding_subtypeVal.comp e.isOpenEmbedding

variable [IsManifold IX n X] [IsManifold IY n Y]
  [IX.Boundaryless] [IY.Boundaryless] [IN.Boundaryless]
  [FiniteDimensional ℝ EX] [FiniteDimensional ℝ EY] [FiniteDimensional ℝ EN]

/-- **The transverse fibre-product theorem.** The actual equal-value subtype of two transverse
`C^n` maps, `n ≥ 1`, is a `C^n` manifold of dimension `dim X + dim Y - dim N` with its
subspace topology. Its inclusion is a smooth embedding, and its tangent image consists of
pairs whose images under the two differentials agree. Empty fibre products are allowed;
no separation or countability hypotheses are needed. -/
theorem exists_transverseFiberProduct_smoothEmbedding (hn : 1 ≤ n)
    (hf : ContMDiff IX IN n f) (hg : ContMDiff IY IN n g)
    (htrans : ∀ p : X × Y, f p.1 = g p.2 →
      (mfderiv IX IN f p.1).range ⊔
        (((tangentSpaceCast IN (g p.2) (f p.1)).toContinuousLinearMap).comp
          (mfderiv IY IN g p.2)).range = ⊤) :
    ∃ cs : ChartedSpace (Fin (finrank ℝ EX + finrank ℝ EY - finrank ℝ EN) → ℝ)
        {p : X × Y // f p.1 = g p.2},
      letI := cs
      IsManifold 𝓘(ℝ, Fin (finrank ℝ EX + finrank ℝ EY - finrank ℝ EN) → ℝ) n
        {p : X × Y // f p.1 = g p.2} ∧
      Manifold.IsSmoothEmbedding
        𝓘(ℝ, Fin (finrank ℝ EX + finrank ℝ EY - finrank ℝ EN) → ℝ) (IX.prod IY) n
        (Subtype.val : {p : X × Y // f p.1 = g p.2} → X × Y) ∧
      ∀ (p : {p : X × Y // f p.1 = g p.2}) (v : TangentSpace (IX.prod IY) p.1),
        v ∈ (mfderiv
          𝓘(ℝ, Fin (finrank ℝ EX + finrank ℝ EY - finrank ℝ EN) → ℝ) (IX.prod IY)
          (Subtype.val : {p : X × Y // f p.1 = g p.2} → X × Y) p).range ↔
        mfderiv IX IN f p.1.1 v.1 =
          tangentSpaceCast IN (g p.1.2) (f p.1.1) (mfderiv IY IN g p.1.2 v.2) := by
  classical
  let d := finrank ℝ EX + finrank ℝ EY - finrank ℝ EN
  let K := 𝓘(ℝ, Fin d → ℝ)
  let P := {p : X × Y // f p.1 = g p.2}
  let U := fiberProductPatch (IN := IN) (n := n) (f := f) (g := g)
  let ι := fiberProductPatchInclusion (IN := IN) (n := n) (f := f) (g := g)
  -- Choose the embedded manifold on each target-coordinate patch.
  have localData (a : N) :=
    (extChartPartialDiffeomorph IN n a).exists_isManifold_localFiberProduct_isSmoothEmbedding
      hn hf hg (fun p hp _ ↦ htrans p hp)
  let (a : N) : ChartedSpace (Fin d → ℝ) (U a) := (localData a).choose
  have (a : N) : IsManifold K n (U a) := (localData a).choose_spec.1
  have hemb (a : N) : Manifold.IsSmoothEmbedding K (IX.prod IY) n
      (Subtype.val : U a → X × Y) := (localData a).choose_spec.2.1
  have hopen (a : N) : IsOpenEmbedding (ι a) :=
    isOpenEmbedding_fiberProductPatchInclusion hf.continuous a
  have hcover (p : P) : ∃ a q, ι a q = p := by
    refine ⟨f p.1.1, ⟨p.1, p.2, ?_⟩, rfl⟩
    exact (mem_extChartPartialDiffeomorph_source IN n _).2 BoundarylessManifold.isInteriorPoint
  -- On an overlap, the topological transition is smooth because its composite with
  -- the embedding into X × Y is the inclusion of the source patch.
  have hdeck (a b : N) (x : U a) (y : U b) (hxy : ι a x = ι b y) :
      ∃ T : U a → U b, ContMDiffAt K K n T x ∧ ι b ∘ T =ᶠ[𝓝 x] ι a := by
    have : Nonempty (U b) := ⟨y⟩
    let e := (hopen b).toOpenPartialHomeomorph (ι b)
    let T := e.symm ∘ ι a
    have hx : ι a x ∈ range (ι b) := ⟨y, hxy.symm⟩
    have hT : ContinuousAt T x :=
      (e.continuousOn_symm.continuousAt (by
        simpa only [e, IsOpenEmbedding.toOpenPartialHomeomorph_target] using
          (hopen b).isOpen_range.mem_nhds hx)).comp
        (hopen a).continuous.continuousAt
    have hEq : ι b ∘ T =ᶠ[𝓝 x] ι a := by
      filter_upwards [(hopen a).continuous.continuousAt.preimage_mem_nhds
        ((hopen b).isOpen_range.mem_nhds hx)] with z hz
      exact (hopen b).toOpenPartialHomeomorph_right_inv _ hz
    refine ⟨T, ?_, hEq⟩
    rw [ContMDiffAt.iff_comp_isImmersionAt ((hemb b).isImmersion.isImmersionAt (T x))]
    refine ⟨hT, ((hemb a).contMDiff x).congr_of_eventuallyEq ?_⟩
    exact hEq.fun_comp Subtype.val
  let := chartedSpaceOfIsOpenEmbedding (H := Fin d → ℝ) hopen hcover
  have : IsManifold K n P := isManifold_chartedSpaceOfIsOpenEmbedding hopen hcover hdeck
  have hlocal (a : N) : IsLocalDiffeomorph K K n (ι a) :=
    isLocalDiffeomorph_chartedSpaceOfIsOpenEmbedding hopen hcover hdeck a
  -- Immersions are local on the source; each patch inclusion is a local diffeomorphism.
  have hi : Manifold.IsImmersion K (IX.prod IY) n (Subtype.val : P → X × Y) := by
    apply isImmersion_iff_forall_isImmersionAt.2
    intro p
    obtain ⟨a, q, rfl⟩ := hcover p
    exact (isImmersionAt_comp_isLocalDiffeomorphAt_iff (hlocal a q)).1
      ((hemb a).isImmersion.isImmersionAt q)
  refine ⟨inferInstance, inferInstance, ⟨hi, IsEmbedding.subtypeVal⟩, ?_⟩
  -- A patch parameterization has invertible derivative, so it does not change the
  -- tangent image of the inclusion. Use the already computed local tangent image.
  intro p v
  obtain ⟨a, q, rfl⟩ := hcover p
  have hn0 : n ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hn)
  have hchain := mfderiv_comp q (hi.contMDiff _ |>.mdifferentiableAt hn0)
    ((hlocal a q).mdifferentiableAt hn0)
  have hrange : (mfderiv K (IX.prod IY) (Subtype.val : U a → X × Y) q).range =
      (mfderiv K (IX.prod IY) (Subtype.val : P → X × Y) (ι a q)).range := by
    -- The composite of the patch inclusion and the ambient inclusion is Subtype.val.
    have hinc : (Subtype.val : P → X × Y) ∘ ι a = (Subtype.val : U a → X × Y) := rfl
    rw [hinc] at hchain
    have hr := LinearMap.range_comp_of_range_eq_top
      (mfderiv K (IX.prod IY) (Subtype.val : P → X × Y) (ι a q)).toLinearMap
      (LinearMap.range_eq_top.2 ((hlocal a q).isInvertible_mfderiv hn0).surjective)
    exact (congrArg (fun L : TangentSpace K q →L[ℝ] TangentSpace (IX.prod IY) q.1 ↦
      L.range) hchain).trans hr
  rw [← hrange]
  exact (localData a).choose_spec.2.2 q v

end TauCeti
