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
import TauCeti.Geometry.Manifold.MFDeriv.Prod

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
`TauCeti.mem_range_mfderiv_coe_transverseFiberProduct_iff`. In terms of the two projections, a
tangent vector of the fibre product is determined by its two components
(`TauCeti.eq_zero_of_mfderiv_transverseFiberProduct`), these components `(u, w)` satisfy
`df u = dg w`
(`TauCeti.mfderiv_comp_mfderiv_fst_eq_mfderiv_comp_mfderiv_snd_transverseFiberProduct`), and
every such pair arises (`TauCeti.exists_mfderiv_eq_of_transverseFiberProduct`).
The existence-only form is
`TauCeti.exists_isManifold_transverseFiberProduct_isSmoothEmbedding`.
The embedding gives the smooth universal property via
`Manifold.IsSmoothEmbedding.contMDiff_iff_comp`: a map into the fibre product is smooth
exactly when both component maps are smooth. In particular both projections are smooth, and
compatible diffeomorphisms of the factors induce a diffeomorphism of transverse fibre products
(`TauCeti.transverseFiberProductCongr`).
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
  fun p ↦ ⟨p.val, p.property.1⟩

private theorem isOpenEmbedding_fiberProductPatchInclusion (hf : Continuous f) (a : N) :
    IsOpenEmbedding (fiberProductPatchInclusion (IN := IN) (n := n) (f := f) (g := g) a) := by
  let U : Set {p : X × Y // f p.1 = g p.2} :=
    {p | f p.val.1 ∈ (extChartPartialDiffeomorph IN n a).source}
  have hU : IsOpen U := (extChartPartialDiffeomorph IN n a).open_source.preimage
    (hf.comp (continuous_fst.comp continuous_subtypeVal))
  let e : fiberProductPatch (IN := IN) (n := n) (f := f) (g := g) a ≃ₜ U :=
    { toEquiv := (Equiv.subtypeSubtypeEquivSubtypeInter
        (fun p : X × Y ↦ f p.1 = g p.2)
        (fun p ↦ f p.1 ∈ (extChartPartialDiffeomorph IN n a).source)).symm
      continuous_toFun := (continuous_subtypeVal.subtype_mk _).subtype_mk _
      continuous_invFun := (continuous_subtypeVal.comp continuous_subtypeVal).subtype_mk _ }
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
      ∀ (p : {p : X × Y // f p.1 = g p.2}) (v : TangentSpace (IX.prod IY) p.val),
        v ∈ (mfderiv
          𝓘(ℝ, Fin (finrank ℝ EX + finrank ℝ EY - finrank ℝ EN) → ℝ) (IX.prod IY)
          (Subtype.val : {p : X × Y // f p.1 = g p.2} → X × Y) p).range ↔
        mfderiv IX IN f p.val.1 v.1 =
          tangentSpaceCast IN (g p.val.2) (f p.val.1) (mfderiv IY IN g p.val.2 v.2) := by
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
    refine ⟨f p.val.1, ⟨p.val, p.property, ?_⟩, rfl⟩
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
  have hrange := (hlocal a q).range_mfderiv_comp (K := IX.prod IY)
    (g := (Subtype.val : P → X × Y)) hn0
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
    ∀ (p : {p : X × Y // f p.1 = g p.2}) (v : TangentSpace (IX.prod IY) p.val),
      v ∈ (mfderiv
        𝓘(ℝ, Fin (finrank ℝ EX + finrank ℝ EY - finrank ℝ EN) → ℝ) (IX.prod IY)
        (Subtype.val : {p : X × Y // f p.1 = g p.2} → X × Y) p).range ↔
      mfderiv IX IN f p.val.1 v.1 =
        tangentSpaceCast IN (g p.val.2) (f p.val.1) (mfderiv IY IN g p.val.2 v.2) :=
  (exists_isManifold_transverseFiberProduct_isSmoothEmbedding hn hf hg htrans).choose_spec.2.2


/-- A pair `(u, w)` of tangent vectors with `df u = dg w` is the pair of differentials of the two
projections of the transverse fibre product at some tangent vector `ξ`. -/
theorem exists_mfderiv_eq_of_transverseFiberProduct :
    letI := transverseFiberProductChartedSpace hn hf hg htrans
    ∀ (p : {p : X × Y // f p.1 = g p.2}) (u : TangentSpace IX p.val.1)
      (w : TangentSpace IY p.val.2),
      mfderiv IX IN f p.val.1 u = tangentSpaceCast IN (g p.val.2) (f p.val.1)
          (mfderiv IY IN g p.val.2 w) →
      ∃ ξ, mfderiv 𝓘(ℝ, Fin (finrank ℝ EX + finrank ℝ EY - finrank ℝ EN) → ℝ) IX
          (fun q : {p : X × Y // f p.1 = g p.2} ↦ q.val.1) p ξ = u ∧
        mfderiv 𝓘(ℝ, Fin (finrank ℝ EX + finrank ℝ EY - finrank ℝ EN) → ℝ) IY
          (fun q : {p : X × Y // f p.1 = g p.2} ↦ q.val.2) p ξ = w := by
  let := transverseFiberProductChartedSpace hn hf hg htrans
  intro p u w h
  have hval := ((isSmoothEmbedding_coe_transverseFiberProduct hn hf hg htrans).contMDiff
    p).mdifferentiableAt (ne_of_gt (lt_of_lt_of_le zero_lt_one hn))
  obtain ⟨ξ, hξ⟩ := (mem_range_mfderiv_coe_transverseFiberProduct_iff hn hf hg htrans p
    (u, w)).2 h
  exact ⟨ξ, by rw [hval.mfderiv_fst_apply]; exact congrArg Prod.fst hξ,
    by rw [hval.mfderiv_snd_apply]; exact congrArg Prod.snd hξ⟩

/-- The differentials of the two projections of the transverse fibre product carry a tangent
vector `ξ` to a pair `(u, w)` with `df u = dg w`. -/
theorem mfderiv_comp_mfderiv_fst_eq_mfderiv_comp_mfderiv_snd_transverseFiberProduct :
    letI := transverseFiberProductChartedSpace hn hf hg htrans
    ∀ (p : {p : X × Y // f p.1 = g p.2})
      (ξ : TangentSpace 𝓘(ℝ, Fin (finrank ℝ EX + finrank ℝ EY - finrank ℝ EN) → ℝ) p),
      mfderiv IX IN f p.val.1 (mfderiv
          𝓘(ℝ, Fin (finrank ℝ EX + finrank ℝ EY - finrank ℝ EN) → ℝ) IX
          (fun q : {p : X × Y // f p.1 = g p.2} ↦ q.val.1) p ξ) =
        tangentSpaceCast IN (g p.val.2) (f p.val.1) (mfderiv IY IN g p.val.2 (mfderiv
          𝓘(ℝ, Fin (finrank ℝ EX + finrank ℝ EY - finrank ℝ EN) → ℝ) IY
          (fun q : {p : X × Y // f p.1 = g p.2} ↦ q.val.2) p ξ)) := by
  let := transverseFiberProductChartedSpace hn hf hg htrans
  intro p ξ
  have hval := ((isSmoothEmbedding_coe_transverseFiberProduct hn hf hg htrans).contMDiff
    p).mdifferentiableAt (ne_of_gt (lt_of_lt_of_le zero_lt_one hn))
  rw [hval.mfderiv_fst_apply, hval.mfderiv_snd_apply]
  exact (mem_range_mfderiv_coe_transverseFiberProduct_iff hn hf hg htrans p _).1
    (LinearMap.mem_range_self _ ξ)

/-- A tangent vector of the transverse fibre product is zero when the differentials of both
projections vanish on it. -/
theorem eq_zero_of_mfderiv_transverseFiberProduct :
    letI := transverseFiberProductChartedSpace hn hf hg htrans
    ∀ (p : {p : X × Y // f p.1 = g p.2})
      (ξ : TangentSpace 𝓘(ℝ, Fin (finrank ℝ EX + finrank ℝ EY - finrank ℝ EN) → ℝ) p),
      mfderiv 𝓘(ℝ, Fin (finrank ℝ EX + finrank ℝ EY - finrank ℝ EN) → ℝ) IX
          (fun q : {p : X × Y // f p.1 = g p.2} ↦ q.val.1) p ξ = 0 →
        mfderiv 𝓘(ℝ, Fin (finrank ℝ EX + finrank ℝ EY - finrank ℝ EN) → ℝ) IY
          (fun q : {p : X × Y // f p.1 = g p.2} ↦ q.val.2) p ξ = 0 → ξ = 0 := by
  let := transverseFiberProductChartedSpace hn hf hg htrans
  intro p ξ h₁ h₂
  have hn0 : n ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hn)
  have hi := isSmoothEmbedding_coe_transverseFiberProduct hn hf hg htrans
  have hval := (hi.contMDiff p).mdifferentiableAt hn0
  refine (injective_iff_map_eq_zero _).1 ((hi.isImmersion.isImmersionAt p).mfderiv_injective hn0)
    ξ ?_
  rw [hval.mfderiv_fst_apply] at h₁
  rw [hval.mfderiv_snd_apply] at h₂
  exact Prod.ext h₁ h₂

end TauCeti

section Congr

open Function Set Module Filter Topology
open scoped Manifold ContDiff

namespace TauCeti

/-- Compatible `C^n` diffeomorphisms `e₁ : X₁ ≃ₘ^n Z₁` and `e₂ : X₂ ≃ₘ^n Z₂` induce a `C^n`
diffeomorphism between transverse fibre products `{p : X₁ × X₂ // f₁ p.1 = f₂ p.2}` and
`{q : Z₁ × Z₂ // g₁ q.1 = g₂ q.2}`. -/
noncomputable def transverseFiberProductCongr
    {EN HN N EX₁ HX₁ X₁ EX₂ HX₂ X₂ EZ₁ HZ₁ Z₁ EZ₂ HZ₂ Z₂ : Type*}
    [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
    {IN : ModelWithCorners ℝ EN HN} [TopologicalSpace N] [ChartedSpace HN N]
    {n : ℕ∞ω} [IsManifold IN n N] [IN.Boundaryless] [FiniteDimensional ℝ EN]
    [NormedAddCommGroup EX₁] [NormedSpace ℝ EX₁] [TopologicalSpace HX₁]
    [NormedAddCommGroup EX₂] [NormedSpace ℝ EX₂] [TopologicalSpace HX₂]
    [NormedAddCommGroup EZ₁] [NormedSpace ℝ EZ₁] [TopologicalSpace HZ₁]
    [NormedAddCommGroup EZ₂] [NormedSpace ℝ EZ₂] [TopologicalSpace HZ₂]
    {IX₁ : ModelWithCorners ℝ EX₁ HX₁} {IX₂ : ModelWithCorners ℝ EX₂ HX₂}
    {IZ₁ : ModelWithCorners ℝ EZ₁ HZ₁} {IZ₂ : ModelWithCorners ℝ EZ₂ HZ₂}
    [TopologicalSpace X₁] [ChartedSpace HX₁ X₁] [IsManifold IX₁ n X₁] [IX₁.Boundaryless]
    [FiniteDimensional ℝ EX₁]
    [TopologicalSpace X₂] [ChartedSpace HX₂ X₂] [IsManifold IX₂ n X₂] [IX₂.Boundaryless]
    [FiniteDimensional ℝ EX₂]
    [TopologicalSpace Z₁] [ChartedSpace HZ₁ Z₁] [IsManifold IZ₁ n Z₁] [IZ₁.Boundaryless]
    [FiniteDimensional ℝ EZ₁]
    [TopologicalSpace Z₂] [ChartedSpace HZ₂ Z₂] [IsManifold IZ₂ n Z₂] [IZ₂.Boundaryless]
    [FiniteDimensional ℝ EZ₂]
    (hn : 1 ≤ n)
    {f₁ : X₁ → N} {f₂ : X₂ → N} {g₁ : Z₁ → N} {g₂ : Z₂ → N}
    (hf₁ : ContMDiff IX₁ IN n f₁) (hf₂ : ContMDiff IX₂ IN n f₂)
    (htrans_f : ∀ p : X₁ × X₂, f₁ p.1 = f₂ p.2 →
      (mfderiv IX₁ IN f₁ p.1).range ⊔
        (((tangentSpaceCast IN (f₂ p.2) (f₁ p.1)).toContinuousLinearMap).comp
          (mfderiv IX₂ IN f₂ p.2)).range = ⊤)
    (hg₁ : ContMDiff IZ₁ IN n g₁) (hg₂ : ContMDiff IZ₂ IN n g₂)
    (htrans_g : ∀ q : Z₁ × Z₂, g₁ q.1 = g₂ q.2 →
      (mfderiv IZ₁ IN g₁ q.1).range ⊔
        (((tangentSpaceCast IN (g₂ q.2) (g₁ q.1)).toContinuousLinearMap).comp
          (mfderiv IZ₂ IN g₂ q.2)).range = ⊤)
    (e₁ : X₁ ≃ₘ^n⟮IX₁, IZ₁⟯ Z₁) (e₂ : X₂ ≃ₘ^n⟮IX₂, IZ₂⟯ Z₂)
    (hcompat : ∀ p : X₁ × X₂, f₁ p.1 = f₂ p.2 ↔ g₁ (e₁ p.1) = g₂ (e₂ p.2)) :
    letI := transverseFiberProductChartedSpace hn hf₁ hf₂ htrans_f
    letI := transverseFiberProductChartedSpace hn hg₁ hg₂ htrans_g
    {p : X₁ × X₂ // f₁ p.1 = f₂ p.2} ≃ₘ^n⟮
      𝓘(ℝ, Fin (finrank ℝ EX₁ + finrank ℝ EX₂ - finrank ℝ EN) → ℝ),
      𝓘(ℝ, Fin (finrank ℝ EZ₁ + finrank ℝ EZ₂ - finrank ℝ EN) → ℝ)⟯
      {q : Z₁ × Z₂ // g₁ q.1 = g₂ q.2} := by
  letI := transverseFiberProductChartedSpace hn hf₁ hf₂ htrans_f
  letI := transverseFiberProductChartedSpace hn hg₁ hg₂ htrans_g
  have hemb_f := isSmoothEmbedding_coe_transverseFiberProduct hn hf₁ hf₂ htrans_f
  have hemb_g := isSmoothEmbedding_coe_transverseFiberProduct hn hg₁ hg₂ htrans_g
  exact
    { toEquiv := Equiv.subtypeEquiv (e₁.toEquiv.prodCongr e₂.toEquiv) hcompat
      contMDiff_toFun := hemb_g.contMDiff_iff_comp.2
        ((e₁.contMDiff.prodMap e₂.contMDiff).comp hemb_f.contMDiff)
      contMDiff_invFun := hemb_f.contMDiff_iff_comp.2
        ((e₁.symm.contMDiff.prodMap e₂.symm.contMDiff).comp hemb_g.contMDiff) }

/-- The forward map of `transverseFiberProductCongr` applies `e₁` and `e₂` coordinatewise. -/
@[simp]
theorem coe_transverseFiberProductCongr_apply
    {EN HN N EX₁ HX₁ X₁ EX₂ HX₂ X₂ EZ₁ HZ₁ Z₁ EZ₂ HZ₂ Z₂ : Type*}
    [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
    {IN : ModelWithCorners ℝ EN HN} [TopologicalSpace N] [ChartedSpace HN N]
    {n : ℕ∞ω} [IsManifold IN n N] [IN.Boundaryless] [FiniteDimensional ℝ EN]
    [NormedAddCommGroup EX₁] [NormedSpace ℝ EX₁] [TopologicalSpace HX₁]
    [NormedAddCommGroup EX₂] [NormedSpace ℝ EX₂] [TopologicalSpace HX₂]
    [NormedAddCommGroup EZ₁] [NormedSpace ℝ EZ₁] [TopologicalSpace HZ₁]
    [NormedAddCommGroup EZ₂] [NormedSpace ℝ EZ₂] [TopologicalSpace HZ₂]
    {IX₁ : ModelWithCorners ℝ EX₁ HX₁} {IX₂ : ModelWithCorners ℝ EX₂ HX₂}
    {IZ₁ : ModelWithCorners ℝ EZ₁ HZ₁} {IZ₂ : ModelWithCorners ℝ EZ₂ HZ₂}
    [TopologicalSpace X₁] [ChartedSpace HX₁ X₁] [IsManifold IX₁ n X₁] [IX₁.Boundaryless]
    [FiniteDimensional ℝ EX₁]
    [TopologicalSpace X₂] [ChartedSpace HX₂ X₂] [IsManifold IX₂ n X₂] [IX₂.Boundaryless]
    [FiniteDimensional ℝ EX₂]
    [TopologicalSpace Z₁] [ChartedSpace HZ₁ Z₁] [IsManifold IZ₁ n Z₁] [IZ₁.Boundaryless]
    [FiniteDimensional ℝ EZ₁]
    [TopologicalSpace Z₂] [ChartedSpace HZ₂ Z₂] [IsManifold IZ₂ n Z₂] [IZ₂.Boundaryless]
    [FiniteDimensional ℝ EZ₂]
    (hn : 1 ≤ n)
    {f₁ : X₁ → N} {f₂ : X₂ → N} {g₁ : Z₁ → N} {g₂ : Z₂ → N}
    (hf₁ : ContMDiff IX₁ IN n f₁) (hf₂ : ContMDiff IX₂ IN n f₂)
    (htrans_f : ∀ p : X₁ × X₂, f₁ p.1 = f₂ p.2 →
      (mfderiv IX₁ IN f₁ p.1).range ⊔
        (((tangentSpaceCast IN (f₂ p.2) (f₁ p.1)).toContinuousLinearMap).comp
          (mfderiv IX₂ IN f₂ p.2)).range = ⊤)
    (hg₁ : ContMDiff IZ₁ IN n g₁) (hg₂ : ContMDiff IZ₂ IN n g₂)
    (htrans_g : ∀ q : Z₁ × Z₂, g₁ q.1 = g₂ q.2 →
      (mfderiv IZ₁ IN g₁ q.1).range ⊔
        (((tangentSpaceCast IN (g₂ q.2) (g₁ q.1)).toContinuousLinearMap).comp
          (mfderiv IZ₂ IN g₂ q.2)).range = ⊤)
    (e₁ : X₁ ≃ₘ^n⟮IX₁, IZ₁⟯ Z₁) (e₂ : X₂ ≃ₘ^n⟮IX₂, IZ₂⟯ Z₂)
    (hcompat : ∀ p : X₁ × X₂, f₁ p.1 = f₂ p.2 ↔ g₁ (e₁ p.1) = g₂ (e₂ p.2))
    (p : {p : X₁ × X₂ // f₁ p.1 = f₂ p.2}) :
    letI := transverseFiberProductChartedSpace hn hf₁ hf₂ htrans_f
    letI := transverseFiberProductChartedSpace hn hg₁ hg₂ htrans_g
    ((transverseFiberProductCongr hn hf₁ hf₂ htrans_f hg₁ hg₂ htrans_g e₁ e₂ hcompat p :
        {q : Z₁ × Z₂ // g₁ q.1 = g₂ q.2}) : Z₁ × Z₂) = (e₁ p.val.1, e₂ p.val.2) :=
  (rfl)

/-- The inverse of `transverseFiberProductCongr` applies `e₁.symm` and `e₂.symm` coordinatewise. -/
@[simp]
theorem coe_transverseFiberProductCongr_symm_apply
    {EN HN N EX₁ HX₁ X₁ EX₂ HX₂ X₂ EZ₁ HZ₁ Z₁ EZ₂ HZ₂ Z₂ : Type*}
    [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
    {IN : ModelWithCorners ℝ EN HN} [TopologicalSpace N] [ChartedSpace HN N]
    {n : ℕ∞ω} [IsManifold IN n N] [IN.Boundaryless] [FiniteDimensional ℝ EN]
    [NormedAddCommGroup EX₁] [NormedSpace ℝ EX₁] [TopologicalSpace HX₁]
    [NormedAddCommGroup EX₂] [NormedSpace ℝ EX₂] [TopologicalSpace HX₂]
    [NormedAddCommGroup EZ₁] [NormedSpace ℝ EZ₁] [TopologicalSpace HZ₁]
    [NormedAddCommGroup EZ₂] [NormedSpace ℝ EZ₂] [TopologicalSpace HZ₂]
    {IX₁ : ModelWithCorners ℝ EX₁ HX₁} {IX₂ : ModelWithCorners ℝ EX₂ HX₂}
    {IZ₁ : ModelWithCorners ℝ EZ₁ HZ₁} {IZ₂ : ModelWithCorners ℝ EZ₂ HZ₂}
    [TopologicalSpace X₁] [ChartedSpace HX₁ X₁] [IsManifold IX₁ n X₁] [IX₁.Boundaryless]
    [FiniteDimensional ℝ EX₁]
    [TopologicalSpace X₂] [ChartedSpace HX₂ X₂] [IsManifold IX₂ n X₂] [IX₂.Boundaryless]
    [FiniteDimensional ℝ EX₂]
    [TopologicalSpace Z₁] [ChartedSpace HZ₁ Z₁] [IsManifold IZ₁ n Z₁] [IZ₁.Boundaryless]
    [FiniteDimensional ℝ EZ₁]
    [TopologicalSpace Z₂] [ChartedSpace HZ₂ Z₂] [IsManifold IZ₂ n Z₂] [IZ₂.Boundaryless]
    [FiniteDimensional ℝ EZ₂]
    (hn : 1 ≤ n)
    {f₁ : X₁ → N} {f₂ : X₂ → N} {g₁ : Z₁ → N} {g₂ : Z₂ → N}
    (hf₁ : ContMDiff IX₁ IN n f₁) (hf₂ : ContMDiff IX₂ IN n f₂)
    (htrans_f : ∀ p : X₁ × X₂, f₁ p.1 = f₂ p.2 →
      (mfderiv IX₁ IN f₁ p.1).range ⊔
        (((tangentSpaceCast IN (f₂ p.2) (f₁ p.1)).toContinuousLinearMap).comp
          (mfderiv IX₂ IN f₂ p.2)).range = ⊤)
    (hg₁ : ContMDiff IZ₁ IN n g₁) (hg₂ : ContMDiff IZ₂ IN n g₂)
    (htrans_g : ∀ q : Z₁ × Z₂, g₁ q.1 = g₂ q.2 →
      (mfderiv IZ₁ IN g₁ q.1).range ⊔
        (((tangentSpaceCast IN (g₂ q.2) (g₁ q.1)).toContinuousLinearMap).comp
          (mfderiv IZ₂ IN g₂ q.2)).range = ⊤)
    (e₁ : X₁ ≃ₘ^n⟮IX₁, IZ₁⟯ Z₁) (e₂ : X₂ ≃ₘ^n⟮IX₂, IZ₂⟯ Z₂)
    (hcompat : ∀ p : X₁ × X₂, f₁ p.1 = f₂ p.2 ↔ g₁ (e₁ p.1) = g₂ (e₂ p.2))
    (q : {q : Z₁ × Z₂ // g₁ q.1 = g₂ q.2}) :
    letI := transverseFiberProductChartedSpace hn hf₁ hf₂ htrans_f
    letI := transverseFiberProductChartedSpace hn hg₁ hg₂ htrans_g
    (((transverseFiberProductCongr hn hf₁ hf₂ htrans_f hg₁ hg₂ htrans_g e₁ e₂ hcompat).symm q :
        {p : X₁ × X₂ // f₁ p.1 = f₂ p.2}) : X₁ × X₂) = (e₁.symm q.val.1, e₂.symm q.val.2) :=
  (rfl)

end TauCeti

end Congr
