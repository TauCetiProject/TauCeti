/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Trivialization
import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Transition

/-!
# Intrinsic normal vector bundles in manifolds

The intrinsic normal spaces of a positive-regularity embedding between finite-dimensional
manifolds form a vector bundle. The total space retains its quotient topology from the
pulled-back ambient tangent bundle. No metric or boundarylessness assumption is needed.

Local coordinates use a fixed complement to the differential in tangent charts, identified
with any chosen model of the codimension. These are the normal bundles needed for tubular
neighbourhoods in an arbitrary ambient manifold.

The construction combines `normalSpaceEquivOfComplement` and
`normalSpaceTrivializationOfComplement`. For the tubular-neighbourhood context, see
M. Hirsch, *Differential Topology*, Chapter 4, §§5–6.
-/

public section

noncomputable section

open Set Function Topology Bundle
open scoped Manifold ContDiff

namespace TauCeti.SmoothEmbedding

variable {𝕜 E V P H G M N : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]
  [NormedAddCommGroup P] [NormedSpace 𝕜 P] [FiniteDimensional 𝕜 P]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 V G}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J 1 N]
  {n : ℕ∞ω}

private structure NormalChartData (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (x₀ : M) where
  baseSet : Set M
  isOpen_baseSet : IsOpen baseSet
  mem_baseSet : x₀ ∈ baseSet
  subset_charts : baseSet ⊆ (chartAt H x₀).source ∩ f ⁻¹' (chartAt G (f x₀)).source
  complement : P →L[𝕜] V
  invertible : ∀ x ∈ baseSet, ((inTangentCoordinates I J _root_.id (f : M → N)
    (mfderiv I J (f : M → N)) x₀ x).coprod complement).IsInvertible
  continuous_coordinate : ContinuousOn (fun x =>
    (inTangentCoordinates I J _root_.id (f : M → N)
      (mfderiv I J (f : M → N)) x₀ x).quotientRangeCoordinate complement) baseSet

private theorem nonempty_normalChartData (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E) (x₀ : M) :
    Nonempty (NormalChartData (P := P) f hn x₀) := by
  let : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  let : CompleteSpace V := FiniteDimensional.complete 𝕜 V
  let : CompleteSpace P := FiniteDimensional.complete 𝕜 P
  obtain ⟨Q, -, U, hU, hxU, hcharts, hInv, -⟩ :=
    f.exists_contMDiffOn_inTangentCoordinates_quotientRangeCoordinate
      (m := 0) (by simpa using ENat.one_le_iff_ne_zero_withTop.mpr hn) (by simp) x₀
  have hA := f.contMDiff.contMDiffAt.mfderiv_const
    (m := 0) (by simpa using ENat.one_le_iff_ne_zero_withTop.mpr hn) (x₀ := x₀)
  obtain ⟨W, hWnhds, hAW⟩ := (contMDiffAt_iff_contMDiffOn_nhds (by simp)).mp hA
  obtain ⟨W', hW'sub, hW', hxW'⟩ := mem_nhds_iff.mp hWnhds
  obtain ⟨e, -⟩ := hInv x₀ hxU
  have hQ : Module.finrank 𝕜 Q = Module.finrank 𝕜 P := by
    have heq := e.toLinearEquiv.finrank_eq
    rw [Module.finrank_prod] at heq
    omega
  let c : P ≃L[𝕜] Q := (ContinuousLinearEquiv.ofFinrankEq hQ).symm
  let B : P →L[𝕜] V := Q.subtypeL ∘L c.toContinuousLinearMap
  have hB (x : M) (hx : x ∈ U) :
      ((inTangentCoordinates I J _root_.id (f : M → N)
        (mfderiv I J (f : M → N)) x₀ x).coprod B).IsInvertible := by
    obtain ⟨eₓ, heₓ⟩ := hInv x hx
    refine ⟨(ContinuousLinearEquiv.refl 𝕜 E |>.prodCongr c).trans eₓ, ?_⟩
    apply ContinuousLinearMap.ext
    rintro ⟨u, v⟩
    simpa [ContinuousLinearEquiv.trans_apply, B] using DFunLike.congr_fun heₓ (u, c v)
  have hcoordinate : ContinuousOn (fun x =>
      (inTangentCoordinates I J _root_.id (f : M → N)
        (mfderiv I J (f : M → N)) x₀ x).quotientRangeCoordinate B) (U ∩ W') := by
    intro x hx
    exact (((hAW.mono hW'sub).continuousOn.continuousAt
      (hW'.mem_nhds hx.2)).quotientRangeCoordinate B (hB x hx.1)).continuousWithinAt
  exact ⟨⟨U ∩ W', hU.inter hW', ⟨hxU, hxW'⟩,
    (fun _ hx => hcharts hx.1), B, (fun x hx => hB x hx.1), hcoordinate⟩⟩

private def normalChartData (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E) (x₀ : M) :
    NormalChartData (P := P) f hn x₀ :=
  Classical.choice (nonempty_normalChartData f hn hdim x₀)

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 V]
  [FiniteDimensional 𝕜 P] in
private theorem NormalChartData.continuous_coordinate_apply
    (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    {x₀ : M} (d : NormalChartData (P := P) f hn x₀) :
    Continuous (fun p : d.baseSet × V =>
      (inTangentCoordinates I J _root_.id (f : M → N)
        (mfderiv I J (f : M → N)) x₀ p.1).quotientRangeCoordinate d.complement p.2) :=
  ((d.continuous_coordinate.domRestrict.comp continuous_fst).clm_apply continuous_snd)

private def NormalChartData.trivialization (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    {x₀ : M} (d : NormalChartData (P := P) f hn x₀) :
    Trivialization P (π P (fun x => f.NormalSpace x hn)) :=
  f.normalSpaceTrivializationOfComplement hn x₀ d.baseSet d.isOpen_baseSet
    d.subset_charts d.complement d.invertible
    (d.continuous_coordinate_apply f hn)

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 V]
  [FiniteDimensional 𝕜 P] in
private theorem NormalChartData.baseSet_trivialization
    (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    {x₀ : M} (d : NormalChartData (P := P) f hn x₀) :
    (d.trivialization f hn).baseSet = d.baseSet := by
  exact f.normalSpaceTrivializationOfComplement_baseSet hn x₀ d.baseSet d.isOpen_baseSet
    d.subset_charts d.complement d.invertible _

private instance NormalChartData.linear_trivialization
    (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    {x₀ : M} (d : NormalChartData (P := P) f hn x₀) :
    (d.trivialization f hn).IsLinear 𝕜 := by
  exact f.instIsLinearNormalSpaceTrivializationOfComplement hn x₀ d.baseSet d.isOpen_baseSet
    d.subset_charts d.complement d.invertible _

/-- Preferred local coordinates on the intrinsic normal bundle in an arbitrary ambient
manifold, using a fixed model of the codimension. The total space has its quotient topology. -/
def normalSpaceTrivialization (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E) (x₀ : M) :
    Trivialization P (π P (fun x => f.NormalSpace x hn)) :=
  (normalChartData f hn hdim x₀).trivialization f hn

/-- The preferred intrinsic normal coordinates contain their reference point. -/
@[simp] theorem mem_normalSpaceTrivialization_baseSet
    (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E) (x : M) :
    x ∈ (f.normalSpaceTrivialization hn hdim x).baseSet := by
  unfold normalSpaceTrivialization
  rw [NormalChartData.baseSet_trivialization]
  exact (normalChartData f hn hdim x).mem_baseSet

/-- Preferred intrinsic normal coordinates are linear on each fibre. -/
instance instIsLinearNormalSpaceTrivialization
    (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E) (x : M) :
    (f.normalSpaceTrivialization hn hdim x).IsLinear 𝕜 := by
  unfold normalSpaceTrivialization
  infer_instance

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 V]
  [FiniteDimensional 𝕜 P] in
private theorem NormalChartData.coordChangeL (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    {x₀ x₁ : M} (d₀ : NormalChartData (P := P) f hn x₀)
    (d₁ : NormalChartData (P := P) f hn x₁) {x : M}
    (hx : x ∈ d₀.baseSet ∩ d₁.baseSet) :
    ((d₀.trivialization f hn).coordChangeL 𝕜 (d₁.trivialization f hn) x : P →L[𝕜] P) =
      (inTangentCoordinates I J _root_.id (f : M → N)
        (mfderiv I J (f : M → N)) x₁ x).quotientRangeCoordinate d₁.complement ∘L
        ((trivializationAt V (TangentSpace J) (f x₀)).coordChangeL 𝕜
          (trivializationAt V (TangentSpace J) (f x₁)) (f x)).toContinuousLinearMap ∘L
            d₀.complement := by
  ext v
  have hx' : x ∈ (d₀.trivialization f hn).baseSet ∩
      (d₁.trivialization f hn).baseSet := by
    simpa only [NormalChartData.baseSet_trivialization] using hx
  rw [ContinuousLinearEquiv.coe_coe, Trivialization.coordChangeL_apply' _ _ hx']
  simp only [NormalChartData.trivialization]
  rw [f.normalSpaceTrivializationOfComplement_symm_apply hn x₀ d₀.baseSet
    d₀.isOpen_baseSet d₀.subset_charts d₀.complement d₀.invertible _ (x, v) hx.1]
  rw [f.normalSpaceTrivializationOfComplement_apply hn x₁ d₁.baseSet
    d₁.isOpen_baseSet d₁.subset_charts d₁.complement d₁.invertible _
      ⟨x, (f.normalSpaceEquivOfComplement hn
        (d₀.subset_charts hx.1).1 (d₀.subset_charts hx.1).2 d₀.complement
          (d₀.invertible x hx.1)).symm v⟩ hx.2]
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe] using
    f.normalSpaceEquivOfComplement_apply_symm_eq_quotientRangeCoordinate_coordChangeL
      hn (d₀.subset_charts hx.1).1 (d₀.subset_charts hx.1).2
      (d₁.subset_charts hx.2).1 (d₁.subset_charts hx.2).2
      d₀.complement d₁.complement (d₀.invertible x hx.1) (d₁.invertible x hx.2) v

/-- Transition operators for the preferred intrinsic normal coordinates are continuous. -/
theorem continuousOn_normalSpaceTrivialization_coordChangeL
    (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E) (x₀ x₁ : M) :
    ContinuousOn (fun x => ((f.normalSpaceTrivialization hn hdim x₀).coordChangeL 𝕜
      (f.normalSpaceTrivialization hn hdim x₁) x : P →L[𝕜] P))
      ((f.normalSpaceTrivialization hn hdim x₀).baseSet ∩
        (f.normalSpaceTrivialization hn hdim x₁).baseSet) := by
  unfold normalSpaceTrivialization
  simp only [NormalChartData.baseSet_trivialization]
  let d₀ := normalChartData f hn hdim x₀
  let d₁ := normalChartData f hn hdim x₁
  have hcoord := (continuousOn_coordChange
    (R := 𝕜) (trivializationAt V (TangentSpace J) (f x₀))
    (trivializationAt V (TangentSpace J) (f x₁))).comp
      f.contMDiff.continuous.continuousOn (s := d₀.baseSet ∩ d₁.baseSet)
      (fun x hx => ⟨(d₀.subset_charts hx.1).2, (d₁.subset_charts hx.2).2⟩)
  refine (((d₁.continuous_coordinate.mono inter_subset_right).clm_comp hcoord).clm_comp
    (continuousOn_const (c := d₀.complement))).congr ?_
  intro x hx
  exact d₀.coordChangeL f hn d₁ hx

omit [FiniteDimensional 𝕜 V] in
private theorem NormalChartData.contMDiffOn_coordChangeL {m : ℕ∞ω}
    [IsManifold I (m + 1) M] [IsManifold J (m + 1) N]
    (f : SmoothEmbedding I J n M N) (hn : n ≠ 0) (hm : m + 1 ≤ n)
    {x₀ x₁ : M} (d₀ : NormalChartData (P := P) f hn x₀)
    (d₁ : NormalChartData (P := P) f hn x₁) :
    ContMDiffOn I 𝓘(𝕜, P →L[𝕜] P) m
      (fun x => ((d₀.trivialization f hn).coordChangeL 𝕜 (d₁.trivialization f hn) x :
        P →L[𝕜] P)) (d₀.baseSet ∩ d₁.baseSet) := by
  let : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  let : CompleteSpace P := FiniteDimensional.complete 𝕜 P
  exact f.contMDiffOn_normalSpaceTrivializationOfComplement_coordChangeL
    x₀ x₁ d₀.baseSet d₁.baseSet d₀.isOpen_baseSet d₁.isOpen_baseSet
      d₀.subset_charts d₁.subset_charts d₀.complement d₁.complement hm
      d₀.invertible d₁.invertible (d₀.continuous_coordinate_apply f hn)
      (d₁.continuous_coordinate_apply f hn)

private theorem normalSpaceTrivialization_eq (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E) (x₀ : M) :
    f.normalSpaceTrivialization hn hdim x₀ = (normalChartData f hn hdim x₀).trivialization f hn :=
  rfl

omit [IsManifold I 1 M] [IsManifold J 1 N] in
/-- Transition operators for the preferred intrinsic normal coordinates are `C^m` for a
`C^n` embedding when `m + 1 ≤ n`. -/
theorem contMDiffOn_normalSpaceTrivialization_coordChangeL {m : ℕ∞ω}
    [IsManifold I (m + 1) M] [IsManifold J (m + 1) N]
    (f : SmoothEmbedding I J n M N) (hn : n ≠ 0) (hm : m + 1 ≤ n)
    (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E) (x₀ x₁ : M) :
    haveI : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
    haveI : IsManifold J 1 N := .of_le (n := m + 1) le_add_self
    ContMDiffOn I 𝓘(𝕜, P →L[𝕜] P) m
      (fun x => ((f.normalSpaceTrivialization hn hdim x₀).coordChangeL 𝕜
        (f.normalSpaceTrivialization hn hdim x₁) x : P →L[𝕜] P))
      ((f.normalSpaceTrivialization hn hdim x₀).baseSet ∩
        (f.normalSpaceTrivialization hn hdim x₁).baseSet) := by
  have : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
  have : IsManifold J 1 N := .of_le (n := m + 1) le_add_self
  simp only [normalSpaceTrivialization_eq, NormalChartData.baseSet_trivialization]
  exact NormalChartData.contMDiffOn_coordChangeL f hn hm _ _

private theorem inducing_normalBundle_mk (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E) (x : M) :
    IsInducing (@TotalSpace.mk M P (fun x => f.NormalSpace x hn) x) := by
  let d := normalChartData f hn hdim x
  let e := d.trivialization f hn
  let c := f.normalSpaceEquivOfComplement hn
    (d.subset_charts d.mem_baseSet).1 (d.subset_charts d.mem_baseSet).2
      d.complement (d.invertible x d.mem_baseSet)
  have hformula : e.toOpenPartialHomeomorph ∘
      @TotalSpace.mk M P (fun x => f.NormalSpace x hn) x =
      fun v => (x, c v) := by
    funext v
    exact normalSpaceTrivializationOfComplement_apply _ _ _ _ _ _ _ _ _ _ d.mem_baseSet
  have hind : IsInducing (fun v => (x, c v)) :=
    (isEmbedding_prodMkRight x).isInducing.comp c.toHomeomorph.isInducing
  apply isInducing_iff_nhds.mpr
  intro v
  rw [e.nhds_eq_comap_inf_principal
      (e.mem_source.mpr ((d.baseSet_trivialization f hn).symm ▸ d.mem_baseSet)),
    Filter.comap_inf, Filter.comap_principal, Filter.comap_comap, hformula]
  have hv : e.toOpenPartialHomeomorph ⟨x, v⟩ = (x, c v) := congrFun hformula v
  rw [hv, ← hind.nhds_eq_comap]
  have hpre : @TotalSpace.mk M P (fun x => f.NormalSpace x hn) x ⁻¹' e.source = univ :=
    eq_univ_of_forall fun w => e.mem_source.mpr
      ((d.baseSet_trivialization f hn).symm ▸ d.mem_baseSet)
  rw [hpre, Filter.principal_univ, inf_top_eq]

/-- The intrinsic normal fibre bundle in an arbitrary finite-dimensional ambient manifold.
Install it locally to select the complementary-coordinate atlas. Its topology is the
existing quotient topology on intrinsic normal classes. -/
@[instance_reducible]
def normalSpaceFiberBundle (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E) :
    FiberBundle P (fun x => f.NormalSpace x hn) where
  totalSpaceMk_isInducing' := inducing_normalBundle_mk f hn hdim
  trivializationAtlas' := range (f.normalSpaceTrivialization hn hdim)
  trivializationAt' := f.normalSpaceTrivialization hn hdim
  mem_baseSet_trivializationAt' := mem_normalSpaceTrivialization_baseSet f hn hdim
  trivialization_mem_atlas' := fun x => mem_range_self x

/-- The preferred bundle chart is the chosen complementary normal chart. -/
@[simp] theorem normalSpaceFiberBundle_trivializationAt
    (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E) (x : M) :
    letI := f.normalSpaceFiberBundle hn hdim
    trivializationAt P (fun x => f.NormalSpace x hn) x =
      f.normalSpaceTrivialization hn hdim x := (rfl)

/-- The intrinsic normal atlas consists exactly of the chosen complementary charts. -/
@[simp] theorem mem_normalSpaceFiberBundle_trivializationAtlas_iff
    (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E)
    (e : Trivialization P (π P (fun x => f.NormalSpace x hn))) :
    letI := f.normalSpaceFiberBundle hn hdim
    e ∈ trivializationAtlas P (fun x => f.NormalSpace x hn) ↔
      ∃ x, f.normalSpaceTrivialization hn hdim x = e := Iff.rfl

/-- The intrinsic normal fibres form a vector bundle with their quotient topology. -/
theorem normalSpaceVectorBundle (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E) :
    letI := f.normalSpaceFiberBundle hn hdim
    VectorBundle 𝕜 P (fun x => f.NormalSpace x hn) := by
  let := f.normalSpaceFiberBundle hn hdim
  refine { trivialization_linear' := ?_, continuousOn_coordChange' := ?_ }
  · rintro e ⟨x, rfl⟩
    infer_instance
  · rintro e e' ⟨x, rfl⟩ ⟨x', rfl⟩
    exact continuousOn_normalSpaceTrivialization_coordChangeL f hn hdim x x'

omit [IsManifold I 1 M] [IsManifold J 1 N] in
/-- The intrinsic normal spaces of a `C^n` embedding form a `C^m` vector bundle when
`m + 1 ≤ n`, retaining their quotient total-space topology. -/
theorem normalSpaceContMDiffVectorBundle {m : ℕ∞ω}
    [IsManifold I (m + 1) M] [IsManifold J (m + 1) N]
    (f : SmoothEmbedding I J n M N) (hn : n ≠ 0) (hm : m + 1 ≤ n)
    (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 V - Module.finrank 𝕜 E) :
    haveI : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
    haveI : IsManifold J 1 N := .of_le (n := m + 1) le_add_self
    letI := f.normalSpaceFiberBundle hn hdim
    letI := f.normalSpaceVectorBundle hn hdim
    ContMDiffVectorBundle m P (fun x => f.NormalSpace x hn) I := by
  have : IsManifold I 1 M := .of_le (n := m + 1) le_add_self
  have : IsManifold J 1 N := .of_le (n := m + 1) le_add_self
  let := f.normalSpaceFiberBundle hn hdim
  let := f.normalSpaceVectorBundle hn hdim
  constructor
  rintro e e' ⟨x, rfl⟩ ⟨x', rfl⟩
  exact contMDiffOn_normalSpaceTrivialization_coordChangeL f hn hm hdim x x'

end TauCeti.SmoothEmbedding
