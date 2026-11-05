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

`TauCeti.transverseFiberProductChartedSpace` glues the coordinate-patch fibre products of
`PartialDiffeomorph.exists_isManifold_localFiberProduct_isSmoothEmbedding`. It is a named,
non-instance atlas, characterized by `TauCeti.isManifold_transverseFiberProduct`,
`TauCeti.isSmoothEmbedding_coe_transverseFiberProduct`, and
`TauCeti.mem_range_mfderiv_coe_transverseFiberProduct_iff`. The existence-only form is
`TauCeti.exists_isManifold_transverseFiberProduct_isSmoothEmbedding`.
The embedding gives the smooth universal property via
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
theorem exists_isManifold_transverseFiberProduct_isSmoothEmbedding (hn : 1 ≤ n)
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
  have hdeck := exists_contMDiffAt_transition_of_isImmersion hopen
    (g := (Subtype.val : P → X × Y)) (fun a ↦ (hemb a).isImmersion)
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
  have hinc : (Subtype.val : P → X × Y) ∘ ι a = (Subtype.val : U a → X × Y) := rfl
  have hrange := (hlocal a q).range_mfderiv_comp hn0
    (hi.contMDiff _ |>.mdifferentiableAt hn0)
  rw [hinc] at hrange
  rw [← hrange]
  exact (localData a).choose_spec.2.2 q v

variable (hn : 1 ≤ n) (hf : ContMDiff IX IN n f) (hg : ContMDiff IY IN n g)
  (htrans : ∀ p : X × Y, f p.1 = g p.2 →
    (mfderiv IX IN f p.1).range ⊔
      (((tangentSpaceCast IN (g p.2) (f p.1)).toContinuousLinearMap).comp
        (mfderiv IY IN g p.2)).range = ⊤)

/-- A fixed atlas on the transverse fibre product, chosen from the construction by gluing
embedded target-coordinate patches. It uses the subspace topology and is not a global instance.
Its manifold, embedding, and tangent-image properties are given by the lemmas below. -/
@[instance_reducible]
noncomputable def transverseFiberProductChartedSpace :
    ChartedSpace (Fin (finrank ℝ EX + finrank ℝ EY - finrank ℝ EN) → ℝ)
      {p : X × Y // f p.1 = g p.2} :=
  (exists_isManifold_transverseFiberProduct_isSmoothEmbedding hn hf hg htrans).choose

/-- The transverse fibre product with its chosen atlas is a `C^n` manifold. -/
theorem isManifold_transverseFiberProduct :
    letI := transverseFiberProductChartedSpace hn hf hg htrans
    IsManifold 𝓘(ℝ, Fin (finrank ℝ EX + finrank ℝ EY - finrank ℝ EN) → ℝ) n
      {p : X × Y // f p.1 = g p.2} :=
  (exists_isManifold_transverseFiberProduct_isSmoothEmbedding hn hf hg htrans).choose_spec.1

/-- The inclusion of the transverse fibre product with its chosen atlas is a smooth embedding. -/
theorem isSmoothEmbedding_coe_transverseFiberProduct :
    letI := transverseFiberProductChartedSpace hn hf hg htrans
    Manifold.IsSmoothEmbedding
      𝓘(ℝ, Fin (finrank ℝ EX + finrank ℝ EY - finrank ℝ EN) → ℝ) (IX.prod IY) n
      (Subtype.val : {p : X × Y // f p.1 = g p.2} → X × Y) :=
  (exists_isManifold_transverseFiberProduct_isSmoothEmbedding hn hf hg htrans).choose_spec.2.1

/-- A tangent vector lies in the image of the fibre-product inclusion exactly when its two
components have equal images under the differentials of the defining maps. -/
theorem mem_range_mfderiv_coe_transverseFiberProduct_iff :
    letI := transverseFiberProductChartedSpace hn hf hg htrans
    ∀ (p : {p : X × Y // f p.1 = g p.2}) (v : TangentSpace (IX.prod IY) p.1),
      v ∈ (mfderiv
        𝓘(ℝ, Fin (finrank ℝ EX + finrank ℝ EY - finrank ℝ EN) → ℝ) (IX.prod IY)
        (Subtype.val : {p : X × Y // f p.1 = g p.2} → X × Y) p).range ↔
      mfderiv IX IN f p.1.1 v.1 =
        tangentSpaceCast IN (g p.1.2) (f p.1.1) (mfderiv IY IN g p.1.2 v.2) :=
  (exists_isManifold_transverseFiberProduct_isSmoothEmbedding hn hf hg htrans).choose_spec.2.2

end TauCeti
