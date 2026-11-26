/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Pullback
public import Mathlib.Geometry.Manifold.PartitionOfUnity
import TauCeti.Geometry.Manifold.PartitionOfUnity.Basic
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# Comparing a finite-rank core with its pullback along a map fixing a closed set

Let `C` be a finite-rank core over a real manifold `M`, with scalars in a normed field `𝕜` which is
a normed `ℝ`-algebra (such as `ℝ` or `ℂ`), whose transitions are real `C^n`. Let `f : M → M` be
continuous, `C^n` on an open set `U`, and the identity on a closed set `A ⊆ U`. Near `A` the map
`f` stays close to the identity, so a fibre of `C` at `x` and the fibre at `f x` lie in common
charts, and reading coordinates of one chart at `f x` as coordinates of the same chart at `x`
compares them. Averaging these chart identities over a smooth partition of unity gives a morphism
`C.pullback f ⟶ C` with `C^n` chart operators, equal to the identity over `A`, hence invertible on
a neighbourhood of `A` (`TauCeti.FiniteRankBundleCore.exists_pullbackComparison`).

This is the smooth counterpart, near the fixed set, of homotopy invariance of pullbacks: no
homotopy, flow or connection is used, only that `f` fixes `A`. For a collar projection `ρ` of a
surface with boundary `A` it compares a bundle pair with one constant along the fibres of `ρ`, the
form in which `TauCeti.SchottkyDouble.contMDiffOn_coordChange_doubledBundleCore` makes the doubled
bundle smooth.

## Main definitions and results

* `TauCeti.FiniteRankBundleCore.chartAverage`: the average over a partition of unity `χ` of the
  chart identities, as an operator from the chart `i` at `f x` to the chart `j` at `x`.
* `TauCeti.FiniteRankBundleCore.pullbackChartAverage`: these operators form a morphism
  `C.pullback f ⟶ C`.
* `TauCeti.FiniteRankBundleCore.contMDiffOn_inChartCoordinates_pullbackChartAverage`: its chart
  operators are real `C^n` when the transitions of `C` are and `f` is `C^n` on the supports of `χ`.
* `TauCeti.FiniteRankBundleCore.fiberMap_pullbackChartAverage_of_eq`: it is the identity at the
  fixed points of `f` where `χ` sums to one, and
  `TauCeti.FiniteRankBundleCore.exists_isOpen_isInvertible_fiberMap_pullbackChartAverage`: if `f`
  fixes every point of the set `s` on which `χ` sums to one, it is invertible on an open
  neighbourhood of `s`.
* `TauCeti.FiniteRankBundleCore.exists_pullbackComparison`: a `C^n` comparison `C.pullback f ⟶ C`
  which is the identity over `A` and invertible on an open neighbourhood of `A`.
-/

public section

open Bundle CategoryTheory Set Topology
open scoped Manifold ContDiff

namespace TauCeti.FiniteRankBundleCore

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]
  {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

section ChartAverage

variable (C : FiniteRankBundleCore 𝕜 M) (f : M → M) {s : Set M}
  (χ : SmoothPartitionOfUnity M I M s)

/-- The average over the partition of unity `χ` of the chart identities: the operator from the
chart `i` at `f x` to the chart `j` at `x` which, weighted by `χ k x`, passes from the chart `i` to
the chart `k` at `f x`, reads the result as coordinates in the chart `k` at `x`, and passes to the
chart `j` at `x`. -/
noncomputable def chartAverage (i j x : M) : (Fin C.rank → 𝕜) →L[𝕜] (Fin C.rank → 𝕜) :=
  ∑ᶠ k, χ k x • (C.core.coordChange k j x).comp (C.core.coordChange i k (f x))

/-- The chart average is a finite sum over the points where the partition of unity is nonzero. -/
theorem chartAverage_eq_sum (i j x : M) :
    chartAverage C f χ i j x = ∑ k ∈ χ.finsupport x,
      χ k x • (C.core.coordChange k j x).comp (C.core.coordChange i k (f x)) :=
  (χ.sum_finsupport_smul_eq_finsum x
    (fun k y ↦ (C.core.coordChange k j y).comp (C.core.coordChange i k (f y)))).symm

omit [NormedAlgebra ℝ 𝕜] in
/-- A fixed point `a` of `f` lies in the chart `a` of `C` at `f a`. -/
private theorem mem_baseSet_apply_of_eq {a : M} (ha : f a = a) : f a ∈ C.core.baseSet a := by
  rw [ha]
  exact C.mem_baseSet_self a

variable {C f χ}

/-- The chart averages intertwine the transitions of `C` at `f x` with those at `x`. -/
theorem coordChange_comp_chartAverage
    (hχ : χ.IsSubordinate fun k ↦ C.core.baseSet k ∩ f ⁻¹' C.core.baseSet k) {i i' j j' x : M}
    (hi : f x ∈ C.core.baseSet i) (hi' : f x ∈ C.core.baseSet i') (hj : x ∈ C.core.baseSet j)
    (hj' : x ∈ C.core.baseSet j') :
    (C.core.coordChange j j' x).comp (chartAverage C f χ i j x) =
      (chartAverage C f χ i' j' x).comp (C.core.coordChange i i' (f x)) := by
  rw [chartAverage_eq_sum, chartAverage_eq_sum, ContinuousLinearMap.comp_finsetSum,
    ContinuousLinearMap.finsetSum_comp]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  obtain ⟨hxk, hfxk⟩ := hχ.mem_of_mem_finsupport hk
  rw [ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp,
    ← ContinuousLinearMap.comp_assoc, C.core.coordChange_linear_comp k j j' x ⟨⟨hxk, hj⟩, hj'⟩,
    ContinuousLinearMap.comp_assoc,
    C.core.coordChange_linear_comp i i' k (f x) ⟨⟨hi, hi'⟩, hfxk⟩]

/-- At a fixed point of `f` where `χ` sums to one, the chart average is the transition of `C`. -/
theorem chartAverage_of_eq
    (hχ : χ.IsSubordinate fun k ↦ C.core.baseSet k ∩ f ⁻¹' C.core.baseSet k) {i j x : M}
    (hfx : f x = x) (hxs : x ∈ s) (hi : x ∈ C.core.baseSet i) (hj : x ∈ C.core.baseSet j) :
    chartAverage C f χ i j x = C.core.coordChange i j x := by
  rw [chartAverage_eq_sum, hfx]
  exact χ.sum_finsupport_smul_eq_of_forall_eq hxs fun k hk ↦
    C.core.coordChange_linear_comp i k j x ⟨⟨hi, (hχ.mem_of_mem_finsupport hk).1⟩, hj⟩

/-- The chart averages are real `C^n` near every point of the chart `j` whose image under `f` lies
in the chart `i`, when the transitions of `C` are real `C^n` and `f` is `C^n` on the supports of
the partition of unity. -/
theorem contMDiffAt_chartAverage {n : ℕ∞}
    (hχ : χ.IsSubordinate fun k ↦ C.core.baseSet k ∩ f ⁻¹' C.core.baseSet k)
    (hg : ∀ i j, ContMDiffOn I 𝓘(ℝ, (Fin C.rank → 𝕜) →L[𝕜] (Fin C.rank → 𝕜)) n
      (C.core.coordChange i j) (C.core.baseSet i ∩ C.core.baseSet j))
    (hf : ∀ k, ∀ x ∈ tsupport (χ k), ContMDiffAt I I n f x) {i j x : M}
    (hi : f x ∈ C.core.baseSet i) (hj : x ∈ C.core.baseSet j) :
    ContMDiffAt I 𝓘(ℝ, (Fin C.rank → 𝕜) →L[𝕜] (Fin C.rank → 𝕜)) n
      (chartAverage C f χ i j) x := by
  have hopen (a b : M) : IsOpen (C.core.baseSet a ∩ C.core.baseSet b) :=
    (C.core.isOpen_baseSet a).inter (C.core.isOpen_baseSet b)
  -- Composition of `𝕜`-linear operators is real bilinear, hence real smooth.
  have hcomp : ContDiff ℝ n fun p : ((Fin C.rank → 𝕜) →L[𝕜] (Fin C.rank → 𝕜)) ×
      ((Fin C.rank → 𝕜) →L[𝕜] (Fin C.rank → 𝕜)) ↦ p.1.comp p.2 :=
    isBoundedBilinearMap_comp.contDiff.restrict_scalars ℝ
  refine χ.contMDiffAt_finsum fun k hk ↦ ?_
  obtain ⟨hxk, hfxk⟩ := hχ k hk
  exact hcomp.comp_contMDiffAt <|
    ((hg k j).contMDiffAt ((hopen k j).mem_nhds ⟨hxk, hj⟩)).prodMk_space
    (((hg i k).contMDiffAt ((hopen i k).mem_nhds ⟨hi, hfxk⟩)).comp x (hf k x hk))

end ChartAverage

section Morphism

variable {s : Set M} (C : FiniteRankBundleCore 𝕜 M) (f : C(M, M))
  (χ : SmoothPartitionOfUnity M I M s)
  (hχ : χ.IsSubordinate fun k ↦ C.core.baseSet k ∩ f ⁻¹' C.core.baseSet k)

include hχ in
/-- The chart averages are continuous on the overlap of the chart `i` at `f x` and the chart `j`
at `x`. -/
theorem continuousOn_chartAverage (i j : M) :
    ContinuousOn (chartAverage C f χ i j) (f ⁻¹' C.core.baseSet i ∩ C.core.baseSet j) :=
  fun _ hx ↦ (contMDiffAt_chartAverage (n := 0) hχ
    (fun i j ↦ contMDiffOn_zero_iff.2 (C.core.continuousOn_coordChange i j))
    (fun _ _ _ ↦ (contMDiff_zero_iff.2 f.continuous).contMDiffAt) hx.1 hx.2).continuousAt
    |>.continuousWithinAt

include hχ in
/-- On the overlap of the chart `i` of the pullback and the chart `j` of `C`, the chart average from
the chart `f i` is continuous. -/
theorem continuous_chartAverage_pullback (i j : M) :
    Continuous fun x : ↥((C.pullback f).core.baseSet i ∩ C.core.baseSet j) ↦
      chartAverage C f χ (f i) j x.val :=
  continuousOn_iff_continuous_domRestrict.1 <| (continuousOn_chartAverage C f χ hχ (f i) j).mono
    fun _ (hx : _ ∈ (C.pullback f).core.baseSet i ∩ C.core.baseSet j) ↦
      ⟨mem_baseSet_pullback.1 hx.1, hx.2⟩

/-- The comparison of `C.pullback f` with `C` obtained by averaging the chart identities over a
partition of unity `χ` subordinate to the charts and their preimages under `f`. Its operator from
the chart `i` of the pullback to the chart `j` of `C` is the chart average from the chart `f i`. -/
noncomputable def pullbackChartAverage : C.pullback f ⟶ C where
  operator i j := ⟨fun x ↦ chartAverage C f χ (f i) j x.val,
    continuous_chartAverage_pullback C f χ hχ i j⟩
  compatible _ _ _ _ _ hi hi' hj hj' v :=
    congrArg (fun T ↦ T v) (coordChange_comp_chartAverage hχ (mem_baseSet_pullback.1 hi)
      (mem_baseSet_pullback.1 hi') hj hj')

/-- The operator of the comparison from the chart `i` of the pullback to the chart `j` of `C` is the
chart average from the chart `f i`. -/
@[simp] theorem operator_pullbackChartAverage (i j : M) :
    (pullbackChartAverage C f χ hχ).operator i j =
      ⟨fun x ↦ chartAverage C f χ (f i) j x.val, continuous_chartAverage_pullback C f χ hχ i j⟩ :=
  (rfl)

/-- Pointwise form of `operator_pullbackChartAverage`. -/
theorem operator_pullbackChartAverage_apply (i j : M)
    (x : ↥((C.pullback f).core.baseSet i ∩ C.core.baseSet j)) :
    (pullbackChartAverage C f χ hχ).operator i j x = chartAverage C f χ (f i) j x.val := (rfl)

/-- In the charts `i` of the pullback and `j` of `C`, the comparison is the chart average from the
chart `f i`. -/
theorem inChartCoordinates_pullbackChartAverage {i j x : M}
    (hx : x ∈ (C.pullback f).core.baseSet i ∩ C.core.baseSet j) :
    (C.pullback f).core.inChartCoordinates C.core i j x
        ((pullbackChartAverage C f χ hχ).fiberMap x) =
      chartAverage C f χ (f i) j x :=
  ((pullbackChartAverage C f χ hχ).operator_eq i j ⟨x, hx⟩).symm

/-- The chart operators of the comparison are real `C^n` when the transitions of `C` are, and `f`
is `C^n` on the supports of the partition of unity. -/
theorem contMDiffOn_inChartCoordinates_pullbackChartAverage {n : ℕ∞}
    (hg : ∀ i j, ContMDiffOn I 𝓘(ℝ, (Fin C.rank → 𝕜) →L[𝕜] (Fin C.rank → 𝕜)) n
      (C.core.coordChange i j) (C.core.baseSet i ∩ C.core.baseSet j))
    (hf : ∀ k, ∀ x ∈ tsupport (χ k), ContMDiffAt I I n f x) (i j : M) :
    ContMDiffOn I 𝓘(ℝ, (Fin (C.pullback f).rank → 𝕜) →L[𝕜] (Fin C.rank → 𝕜)) n
      (fun x ↦ (C.pullback f).core.inChartCoordinates C.core i j x
        ((pullbackChartAverage C f χ hχ).fiberMap x))
      ((C.pullback f).core.baseSet i ∩ C.core.baseSet j) := fun _ hx ↦
  ((contMDiffAt_chartAverage hχ hg hf (mem_baseSet_pullback.1 hx.1) hx.2).congr_of_eventuallyEq
    (Filter.eventually_of_mem (((C.pullback f).core.isOpen_baseSet i).inter
      (C.core.isOpen_baseSet j) |>.mem_nhds hx) fun _ hy ↦
        inChartCoordinates_pullbackChartAverage C f χ hχ hy)).contMDiffWithinAt

/-- The fibre map of the comparison at `x` is the chart average from the chart `f x` at `f x` to the
chart `x` at `x`. -/
@[simp] theorem fiberMap_pullbackChartAverage (x : M) :
    (pullbackChartAverage C f χ hχ).fiberMap x = chartAverage C f χ (f x) x x := by
  rw [← operator_self, operator_pullbackChartAverage_apply]

/-- At a fixed point of `f` where the partition of unity sums to one, the comparison is the
identity: the fibre of the pullback there is the fibre of `C`. -/
theorem fiberMap_pullbackChartAverage_of_eq {x : M} (hfx : f x = x) (hxs : x ∈ s) :
    (pullbackChartAverage C f χ hχ).fiberMap x = ContinuousLinearMap.id 𝕜 (Fin C.rank → 𝕜) := by
  have hx : x ∈ C.core.baseSet (f x) := by
    rw [hfx]
    exact C.mem_baseSet_self x
  rw [fiberMap_pullbackChartAverage, chartAverage_of_eq hχ hfx hxs hx (C.mem_baseSet_self x), hfx,
    coordChange_self]

include hχ in
/-- If `f` fixes every point of `s`, the comparison is invertible on an open neighbourhood of
`s`. -/
theorem exists_isOpen_isInvertible_fiberMap_pullbackChartAverage [CompleteSpace 𝕜]
    (hfs : ∀ a ∈ s, f a = a) :
    ∃ V, IsOpen V ∧ s ⊆ V ∧ ∀ x ∈ V, ((pullbackChartAverage C f χ hχ).fiberMap x).IsInvertible := by
  refine ⟨⋃ a ∈ s, (f ⁻¹' C.core.baseSet a ∩ C.core.baseSet a) ∩
      chartAverage C f χ a a ⁻¹' {T | T.IsInvertible},
    isOpen_biUnion fun a _ ↦ (continuousOn_chartAverage C f χ hχ a a).isOpen_inter_preimage
      (((C.core.isOpen_baseSet a).preimage f.continuous).inter (C.core.isOpen_baseSet a))
      ContinuousLinearMap.isOpen_setOfPred_isInvertible,
    fun a ha ↦ mem_biUnion ha ⟨⟨mem_baseSet_apply_of_eq C f (hfs a ha), C.mem_baseSet_self a⟩, ?_⟩,
    fun x hx ↦ ?_⟩
  · rw [mem_preimage, chartAverage_of_eq hχ (hfs a ha) ha (C.mem_baseSet_self a)
      (C.mem_baseSet_self a), coordChange_self]
    exact ⟨ContinuousLinearEquiv.refl 𝕜 _, rfl⟩
  · obtain ⟨a, ha, ⟨hfxa, hxa⟩, hinv⟩ := mem_iUnion₂.1 hx
    -- At a fixed point `a` the chart `a` of the pullback is the chart `f a = a` of `C`.
    have hxa' : x ∈ (C.pullback f).core.baseSet a := mem_baseSet_pullback.2 (by rwa [hfs a ha])
    refine ((pullbackChartAverage C f χ hχ).operator_isInvertible_iff hxa' hxa).1 ?_
    rwa [operator_pullbackChartAverage_apply, hfs a ha]

end Morphism

/-- **Comparing a core with its pullback near a fixed set.** Let `C` be a finite-rank core over a
Hausdorff, `σ`-compact, finite-dimensional real manifold `M` whose transitions are real `C^n`, and
let `f : M → M` be continuous, `C^n` on an open set `U`, and the identity on a closed set `A ⊆ U`.
Then there is a morphism `C.pullback f ⟶ C` whose chart operators are real `C^n`, which is the
identity over `A`, and which is invertible on an open neighbourhood of `A` inside `U`. -/
theorem exists_pullbackComparison [CompleteSpace 𝕜] [FiniteDimensional ℝ E] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M] (C : FiniteRankBundleCore 𝕜 M) {n : ℕ∞}
    (hg : ∀ i j, ContMDiffOn I 𝓘(ℝ, (Fin C.rank → 𝕜) →L[𝕜] (Fin C.rank → 𝕜)) n
      (C.core.coordChange i j) (C.core.baseSet i ∩ C.core.baseSet j))
    (f : C(M, M)) {U A : Set M} (hU : IsOpen U) (hA : IsClosed A) (hAU : A ⊆ U)
    (hf : ContMDiffOn I I n f U) (hfA : ∀ a ∈ A, f a = a) :
    ∃ Φ : C.pullback f ⟶ C,
      (∀ i j, ContMDiffOn I 𝓘(ℝ, (Fin (C.pullback f).rank → 𝕜) →L[𝕜] (Fin C.rank → 𝕜)) n
        (fun x ↦ (C.pullback f).core.inChartCoordinates C.core i j x (Φ.fiberMap x))
        ((C.pullback f).core.baseSet i ∩ C.core.baseSet j)) ∧
      (∀ a ∈ A, Φ.fiberMap a = ContinuousLinearMap.id 𝕜 (Fin C.rank → 𝕜)) ∧
      ∃ V, IsOpen V ∧ A ⊆ V ∧ V ⊆ U ∧ ∀ x ∈ V, (Φ.fiberMap x).IsInvertible := by
  -- Average over a partition of unity on `A` subordinate to the parts of the charts in `U` whose
  -- image under `f` stays in the chart.
  set O : M → Set M := fun k ↦ U ∩ (C.core.baseSet k ∩ f ⁻¹' C.core.baseSet k)
  have hO (k : M) : IsOpen (O k) := hU.inter
    ((C.core.isOpen_baseSet k).inter ((C.core.isOpen_baseSet k).preimage f.continuous))
  obtain ⟨χ, hχO⟩ := SmoothPartitionOfUnity.exists_isSubordinate I hA O hO fun a ha ↦
    mem_iUnion.2 ⟨a, hAU ha, C.mem_baseSet_self a, mem_baseSet_apply_of_eq C f (hfA a ha)⟩
  have hχ : χ.IsSubordinate fun k ↦ C.core.baseSet k ∩ f ⁻¹' C.core.baseSet k :=
    fun k ↦ (hχO k).trans inter_subset_right
  obtain ⟨V, hV, hAV, hinv⟩ :=
    exists_isOpen_isInvertible_fiberMap_pullbackChartAverage C f χ hχ hfA
  exact ⟨pullbackChartAverage C f χ hχ,
    contMDiffOn_inChartCoordinates_pullbackChartAverage C f χ hχ hg
      fun k x hx ↦ hf.contMDiffAt (hU.mem_nhds (hχO k hx).1),
    fun a ha ↦ fiberMap_pullbackChartAverage_of_eq C f χ hχ (hfA a ha) ha,
    V ∩ U, hV.inter hU, subset_inter hAV hAU, inter_subset_right, fun x hx ↦ hinv x hx.1⟩

end TauCeti.FiniteRankBundleCore
