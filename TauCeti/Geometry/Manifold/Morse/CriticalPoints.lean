/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Card
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Topology.Maps.Proper.Basic
public import TauCeti.Geometry.Manifold.Morse.Index
public import TauCeti.Geometry.Manifold.RegularValue
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import TauCeti.Geometry.Manifold.MFDeriv.Chart

/-!
# The critical set of a real function on a manifold

The critical set `TauCeti.criticalPoints I f` of a function `f : M → ℝ` is the zero locus of its
vector-valued manifold derivative `mvfderiv I f`, equivalently of `mfderiv I 𝓘(ℝ) f`. On a
boundaryless manifold it is also the set of points `x` at which the coordinate expression of `f`
in the preferred extended chart at `x` has zero Fréchet derivative. That is the criticality test
built into `TauCeti.IsMorseOn`, so a Morse function is exactly a smooth function all of whose
critical points are nondegenerate.

Local extrema are critical points, so a continuous function on a nonempty compact manifold has a
critical point, and so does each nonempty compact sublevel of a continuous function. The critical
set of a `C¹` function is closed, and a nondegenerate critical point is isolated in it, so a Morse
function has finitely many critical points in every compact set; for a proper function bounded
below, this applies to every sublevel set.

Critical points are counted, in total and by Morse index, with values in `ℕ∞`: an infinite
critical set has count `⊤`, never a junk natural number. The counts of a Morse function on a
compact manifold are finite, the counts by index add up to the total count, and replacing `f` by
`-f` exchanges the indices `j` and `dim M - j`. These counts are the coefficients of the Morse
polynomial in the Morse inequalities.

## Main declarations

* `TauCeti.criticalPoints`: the critical set, with `TauCeti.mem_criticalPoints_iff_mfderiv_eq_zero`
  and, on boundaryless manifolds,
  `TauCeti.mem_criticalPoints_iff_fderiv_comp_extChartAt_symm_eq_zero`.
* `TauCeti.isMorseOn_iff_criticalPoints`: Morse functions in terms of the critical set.
* `IsLocalExtr.mem_criticalPoints`, `TauCeti.criticalPoints_nonempty` and
  `TauCeti.exists_mem_criticalPoints_of_isCompact_sublevel`: Fermat's theorem on a manifold and the
  existence of critical points on compact manifolds and in compact sublevels.
* `TauCeti.isClosed_criticalPoints` and
  `TauCeti.IsManifoldNondegenerateCriticalPoint.eventually_notMem_criticalPoints`: the critical
  set of a `C¹` function is closed, and nondegenerate critical points are isolated in it.
* `TauCeti.IsMorse.finite_criticalPoints_inter` and
  `TauCeti.IsMorse.finite_criticalPoints_inter_preimage_Iic`: finiteness on compact sets and on
  sublevel sets of proper functions bounded below.
* `TauCeti.criticalCount` and `TauCeti.totalCriticalCount`: the extended counts of critical
  points, with `TauCeti.sum_criticalCount_eq_totalCriticalCount`,
  `TauCeti.IsMorse.totalCriticalCount_ne_top` and `TauCeti.IsMorse.criticalCount_neg`.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §2.
-/

public section

open Function Set Filter Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {f : M → ℝ} {s : Set M} {x : M}

variable (I) in
/-- The **critical set** of a real-valued function on a manifold: the points where its manifold
derivative vanishes. No regularity is assumed; at a point where `f` is not differentiable the
manifold derivative is zero by convention, so such a point is critical. -/
def criticalPoints (f : M → ℝ) : Set M :=
  {x | mvfderiv I f x = 0}

/-- A point is critical when the vector-valued manifold derivative vanishes there. -/
@[simp]
theorem mem_criticalPoints : x ∈ criticalPoints I f ↔ mvfderiv I f x = 0 :=
  Iff.rfl

/-- A point is critical exactly when the manifold derivative `mfderiv I 𝓘(ℝ) f` vanishes there. -/
theorem mem_criticalPoints_iff_mfderiv_eq_zero :
    x ∈ criticalPoints I f ↔ mfderiv I 𝓘(ℝ) f x = 0 := by
  rw [mem_criticalPoints, mvfderiv]
  -- `mvfderiv` postcomposes `mfderiv` with the identification `NormedSpace.fromTangentSpace`.
  refine ⟨fun h ↦ ContinuousLinearMap.ext fun v ↦ ?_,
    fun h ↦ by rw [h, ContinuousLinearMap.comp_zero]⟩
  have hv := DFunLike.congr_fun h v
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe] at hv
  exact (NormedSpace.fromTangentSpace (f x)).map_eq_zero_iff.1 hv

/-- The critical set is the zero locus of the manifold derivative `mfderiv I 𝓘(ℝ) f`. -/
theorem criticalPoints_eq_setOf_mfderiv_eq_zero :
    criticalPoints I f = {x | mfderiv I 𝓘(ℝ) f x = 0} :=
  Set.ext fun _ ↦ mem_criticalPoints_iff_mfderiv_eq_zero

/-- A point is regular for a real-valued function exactly when it is not critical. -/
theorem isRegularPoint_iff_notMem_criticalPoints :
    IsRegularPoint I 𝓘(ℝ) f x ↔ x ∉ criticalPoints I f := by
  rw [isRegularPoint_iff_mvfderiv_ne_zero, mem_criticalPoints]

/-- A scalar value is regular exactly when it is not the value of a critical point. -/
theorem isRegularValue_iff_notMem_image_criticalPoints {c : ℝ} :
    IsRegularValue I 𝓘(ℝ) f c ↔ c ∉ f '' criticalPoints I f := by
  simp only [isRegularValue_iff, isRegularPoint_iff_notMem_criticalPoints, mem_image,
    not_exists, not_and]
  tauto

/-- A function and its negation have the same critical points. -/
@[simp]
theorem criticalPoints_neg : criticalPoints I (-f) = criticalPoints I f := by
  ext x
  rw [mem_criticalPoints, mem_criticalPoints, mvfderiv_neg, neg_eq_zero]

/-! ### Critical points read in the preferred chart -/

section Chart

variable [IsManifold I 1 M]

/-- In the source of the preferred extended chart at `x`, critical points of `f` are the points
whose chart images are critical points of the coordinate expression of `f`, wherever that
coordinate expression is differentiable. -/
private theorem mem_criticalPoints_iff_of_mem_extChartAt_source {y : M}
    (hy : y ∈ (extChartAt I x).source)
    (hg : DifferentiableAt ℝ (f ∘ (extChartAt I x).symm) (extChartAt I x y)) :
    y ∈ criticalPoints I f ↔ fderiv ℝ (f ∘ (extChartAt I x).symm) (extChartAt I x y) = 0 :=
  mem_criticalPoints_iff_mfderiv_eq_zero.trans
    (mfderiv_eq_zero_iff_fderiv_comp_extChartAt_symm_eq_zero hy hg)

/-- **A nondegenerate critical point is isolated** among the critical points of `f`. -/
theorem IsManifoldNondegenerateCriticalPoint.eventually_notMem_criticalPoints
    (h : IsManifoldNondegenerateCriticalPoint I f x) :
    ∀ᶠ y in 𝓝[≠] x, y ∉ criticalPoints I f := by
  set ψ := extChartAt I x
  have h' := (isManifoldNondegenerateCriticalPoint_iff I).1 h
  -- The chart is injective near `x`, so it sends punctured neighbourhoods of `x` into punctured
  -- neighbourhoods of `ψ x`, where the coordinate expression has nonzero derivative.
  have hsource : ψ.source ∈ 𝓝[≠] x := nhdsWithin_le_nhds (extChartAt_source_mem_nhds x)
  have htend : Tendsto ψ (𝓝[≠] x) (𝓝[≠] (ψ x)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      ((continuousAt_extChartAt x).tendsto.mono_left nhdsWithin_le_nhds) ?_
    filter_upwards [hsource, self_mem_nhdsWithin] with y hy hyx
    exact mem_compl_singleton_iff.2 fun hψ ↦ hyx (ψ.injOn hy (mem_extChartAt_source x) hψ)
  have hdiff : ∀ᶠ v in 𝓝[≠] (ψ x), DifferentiableAt ℝ (f ∘ ψ.symm) v :=
    nhdsWithin_le_nhds ((h'.contDiffAt.eventually (by simp)).mono fun v hv ↦
      hv.differentiableAt (by simp))
  filter_upwards [htend.eventually h'.eventually_fderiv_ne_zero, htend.eventually hdiff,
    hsource] with y hy0 hyd hy
  rwa [mem_criticalPoints_iff_of_mem_extChartAt_source hy hyd]

end Chart

section Boundaryless

variable [I.Boundaryless]

/-- On a boundaryless manifold, `x` is a critical point of `f` exactly when the coordinate
expression of `f` in the preferred extended chart at `x` has zero Fréchet derivative there. No
regularity of `f` is needed: where `f` is not differentiable, neither derivative is. -/
theorem mem_criticalPoints_iff_fderiv_comp_extChartAt_symm_eq_zero :
    x ∈ criticalPoints I f ↔
      fderiv ℝ (f ∘ (extChartAt I x).symm) (extChartAt I x x) = 0 := by
  by_cases hf : MDifferentiableAt I 𝓘(ℝ) f x
  · rw [mem_criticalPoints, hf.mvfderiv_eq_fderiv_comp_extChartAt_symm]
    -- The two sides differ only in reading the zero map on the tangent space or on `E`.
    exact Iff.rfl
  · rw [mem_criticalPoints_iff_mfderiv_eq_zero, mfderiv_zero_of_not_mdifferentiableAt hf,
      fderiv_zero_of_not_differentiableAt
        (mt mdifferentiableAt_iff_differentiableAt_comp_extChartAt_symm.2 hf)]
    simp only

/-- A nondegenerate critical point is a critical point. -/
theorem IsManifoldNondegenerateCriticalPoint.mem_criticalPoints
    (h : IsManifoldNondegenerateCriticalPoint I f x) : x ∈ criticalPoints I f :=
  mem_criticalPoints_iff_fderiv_comp_extChartAt_symm_eq_zero.2
    ((isManifoldNondegenerateCriticalPoint_iff I).1 h).fderiv_eq_zero

/-- A function is Morse on `s` exactly when it is smooth on `s` and each of its critical points in
`s` is nondegenerate. -/
theorem isMorseOn_iff_criticalPoints :
    IsMorseOn I f s ↔
      ContMDiffOn I 𝓘(ℝ) ∞ f s ∧
        ∀ x ∈ s, x ∈ criticalPoints I f → IsManifoldNondegenerateCriticalPoint I f x := by
  simp only [isMorseOn_iff, mem_criticalPoints_iff_fderiv_comp_extChartAt_symm_eq_zero]

/-- Every critical point in `s` of a function which is Morse on `s` is nondegenerate. -/
theorem IsMorseOn.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints
    (h : IsMorseOn I f s) (hs : x ∈ s) (hx : x ∈ criticalPoints I f) :
    IsManifoldNondegenerateCriticalPoint I f x :=
  (isMorseOn_iff_criticalPoints.1 h).2 x hs hx

/-- Every critical point of a Morse function is nondegenerate. -/
theorem IsMorse.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints (h : IsMorse I f)
    (hx : x ∈ criticalPoints I f) : IsManifoldNondegenerateCriticalPoint I f x :=
  (isMorseOn_univ.2 h).isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints (mem_univ x) hx

/-- **Fermat's theorem on a manifold.** A local extremum is a critical point. -/
theorem _root_.IsLocalExtr.mem_criticalPoints (h : IsLocalExtr f x) : x ∈ criticalPoints I f := by
  rw [mem_criticalPoints_iff_fderiv_comp_extChartAt_symm_eq_zero]
  refine IsLocalExtr.fderiv_eq_zero
    (IsLocalExtr.comp_continuous ?_ (continuousAt_extChartAt_symm x))
  rwa [extChartAt_to_inv]

/-- A local minimum is a critical point. -/
theorem _root_.IsLocalMin.mem_criticalPoints (h : IsLocalMin f x) : x ∈ criticalPoints I f :=
  IsLocalExtr.mem_criticalPoints (IsMinFilter.isExtrFilter h)

/-- A local maximum is a critical point. -/
theorem _root_.IsLocalMax.mem_criticalPoints (h : IsLocalMax f x) : x ∈ criticalPoints I f :=
  IsLocalExtr.mem_criticalPoints (IsMaxFilter.isExtrFilter h)

/-- A continuous function on a nonempty compact boundaryless manifold has a critical point, for
instance a point where it attains its minimum. -/
theorem criticalPoints_nonempty [CompactSpace M] [Nonempty M] (hf : Continuous f) :
    (criticalPoints I f).Nonempty := by
  obtain ⟨x, -, hx⟩ := isCompact_univ.exists_isMinOn univ_nonempty hf.continuousOn
  exact ⟨x, (hx.isLocalMin univ_mem).mem_criticalPoints⟩

/-- A continuous function on a boundaryless manifold has a critical point in each nonempty compact
sublevel `{f ≤ t}`, for instance a point where it attains its minimum. -/
theorem exists_mem_criticalPoints_of_isCompact_sublevel (hf : Continuous f) {t : ℝ}
    (hK : IsCompact {x | f x ≤ t}) (hne : {x | f x ≤ t}.Nonempty) :
    ∃ x ∈ criticalPoints I f, f x ≤ t := by
  obtain ⟨x, hx, hmin⟩ := hK.exists_isMinOn hne hf.continuousOn
  -- Points outside the sublevel have values above `t ≥ f x`, so `x` is a global minimum.
  have hglobal : IsMinOn f univ x := fun y _ ↦
    (le_or_gt (f y) t).elim (fun hy ↦ hmin hy) fun hy ↦ (hx.trans hy.le : f x ≤ f y)
  exact ⟨x, (hglobal.isLocalMin univ_mem).mem_criticalPoints, hx⟩

/-! ### Closedness, isolation and finiteness -/

section IsManifold

variable [IsManifold I 1 M]

/-- The critical set of a `C¹` function on a boundaryless manifold is closed. -/
theorem isClosed_criticalPoints (hf : ContMDiff I 𝓘(ℝ) 1 f) : IsClosed (criticalPoints I f) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  set ψ := extChartAt I x
  -- In the chart at `x` the derivative of the coordinate expression is continuous, so its
  -- nonvanishing locus pulls back to an open neighbourhood of `x` free of critical points.
  have hg : ContDiffOn ℝ 1 (f ∘ ψ.symm) ψ.target :=
    (hf.comp_contMDiffOn (contMDiffOn_extChartAt_symm x)).contDiffOn
  have ht : IsOpen ψ.target := isOpen_extChartAt_target x
  have hcrit : ∀ y ∈ ψ.source, y ∈ criticalPoints I f ↔ fderiv ℝ (f ∘ ψ.symm) (ψ y) = 0 :=
    fun y hy ↦ mem_criticalPoints_iff_of_mem_extChartAt_source hy
      ((hg.contDiffAt (ht.mem_nhds (ψ.map_source hy))).differentiableAt one_ne_zero)
  refine ⟨ψ.source ∩ ψ ⁻¹' (ψ.target ∩ fderiv ℝ (f ∘ ψ.symm) ⁻¹' {0}ᶜ), ?_, ?_, ?_⟩
  · rintro y ⟨hy, -, hy0⟩ hyc
    exact hy0 ((hcrit y hy).1 hyc)
  · exact (continuousOn_extChartAt x).isOpen_inter_preimage (isOpen_extChartAt_source x)
      ((hg.continuousOn_fderiv_of_isOpen ht le_rfl).isOpen_inter_preimage ht
        isOpen_compl_singleton)
  · exact ⟨mem_extChartAt_source x, mem_extChartAt_target x,
      fun h0 ↦ hx ((hcrit x (mem_extChartAt_source x)).2 h0)⟩

/-- **A Morse function has finitely many critical points in each compact set.** -/
theorem IsMorse.finite_criticalPoints_inter (hf : IsMorse I f) {K : Set M} (hK : IsCompact K) :
    (criticalPoints I f ∩ K).Finite := by
  refine (hK.inter_left (isClosed_criticalPoints (hf.contMDiff.of_le (by simp)))).finite ?_
  rw [isDiscrete_iff_nhdsNE]
  rintro x ⟨hx, -⟩
  rw [inf_principal_eq_bot]
  filter_upwards [(hf.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints
    hx).eventually_notMem_criticalPoints] with y hy using fun h ↦ hy h.1

/-- A Morse function on a compact manifold has finitely many critical points. -/
theorem IsMorse.finite_criticalPoints [CompactSpace M] (hf : IsMorse I f) :
    (criticalPoints I f).Finite := by
  simpa using hf.finite_criticalPoints_inter isCompact_univ

/-- A proper Morse function bounded below has finitely many critical points in each sublevel
set. -/
theorem IsMorse.finite_criticalPoints_inter_preimage_Iic (hf : IsMorse I f) (hp : IsProperMap f)
    (hbdd : BddBelow (range f)) (b : ℝ) : (criticalPoints I f ∩ f ⁻¹' Iic b).Finite := by
  obtain ⟨a, ha⟩ := hbdd
  have hsub : f ⁻¹' Iic b = f ⁻¹' Icc a b := by
    ext y
    simp [ha (mem_range_self y)]
  rw [hsub]
  exact hf.finite_criticalPoints_inter (hp.isCompact_preimage isCompact_Icc)

end IsManifold

end Boundaryless

/-! ### Counting critical points -/

variable (I) in
/-- The number of critical points of `f`, in `ℕ∞`; it is `⊤` when there are infinitely many. -/
noncomputable def totalCriticalCount (f : M → ℝ) : ℕ∞ :=
  (criticalPoints I f).encard

variable (I) in
/-- The number of critical points of `f` of Morse index `j`, in `ℕ∞`; it is `⊤` when there are
infinitely many. -/
noncomputable def criticalCount (f : M → ℝ) (j : ℕ) : ℕ∞ :=
  {x ∈ criticalPoints I f | manifoldMorseIndex I f x = j}.encard

/-- The total critical count is the extended cardinality of the critical set. -/
theorem totalCriticalCount_def : totalCriticalCount I f = (criticalPoints I f).encard :=
  (rfl)

/-- The critical count in index `j` is the extended cardinality of the critical points of index
`j`. -/
theorem criticalCount_def (j : ℕ) :
    criticalCount I f j = {x ∈ criticalPoints I f | manifoldMorseIndex I f x = j}.encard :=
  (rfl)

/-- The number of critical points of a given index is at most the number of critical points. -/
theorem criticalCount_le_totalCriticalCount (j : ℕ) :
    criticalCount I f j ≤ totalCriticalCount I f :=
  encard_le_encard (sep_subset _ _)

/-- A function and its negation have the same number of critical points. -/
@[simp]
theorem totalCriticalCount_neg : totalCriticalCount I (-f) = totalCriticalCount I f := by
  rw [totalCriticalCount_def, totalCriticalCount_def, criticalPoints_neg]

section FiniteDimensional

variable [FiniteDimensional ℝ E]

/-- There are no critical points of index larger than the dimension. -/
theorem criticalCount_eq_zero_of_finrank_lt {j : ℕ} (hj : Module.finrank ℝ E < j) :
    criticalCount I f j = 0 := by
  rw [criticalCount_def, encard_eq_zero, eq_empty_iff_forall_notMem]
  rintro x ⟨-, rfl⟩
  exact (manifoldMorseIndex_le_finrank.trans_lt hj).false

/-- The numbers of critical points of the indices `0, …, dim M` add up to the number of critical
points. -/
theorem sum_criticalCount_eq_totalCriticalCount :
    ∑ j ∈ Finset.range (Module.finrank ℝ E + 1), criticalCount I f j = totalCriticalCount I f := by
  have hU : criticalPoints I f = ⋃ j : Fin (Module.finrank ℝ E + 1),
      {x ∈ criticalPoints I f | manifoldMorseIndex I f x = j} := by
    ext x
    simp only [mem_iUnion]
    refine ⟨fun hx ↦ ⟨⟨manifoldMorseIndex I f x,
      Nat.lt_succ_of_le manifoldMorseIndex_le_finrank⟩, hx, rfl⟩, fun ⟨_, hx, _⟩ ↦ hx⟩
  have hdisj : Pairwise (Disjoint on fun j : Fin (Module.finrank ℝ E + 1) ↦
      {x ∈ criticalPoints I f | manifoldMorseIndex I f x = j}) := fun i j hij ↦
    disjoint_left.2 fun x hi hj ↦ hij (Fin.ext (hi.2.symm.trans hj.2))
  rw [totalCriticalCount_def, hU, encard_iUnion_of_finite hdisj, finsum_eq_sum_of_fintype,
    ← Fin.sum_univ_eq_sum_range]
  rfl

variable [I.Boundaryless]

/-- **Duality of critical counts.** Replacing a Morse function by its negation exchanges the
numbers of critical points of index `j` and `dim M - j`. -/
theorem IsMorse.criticalCount_neg (hf : IsMorse I f) {j : ℕ} (hj : j ≤ Module.finrank ℝ E) :
    criticalCount I (-f) j = criticalCount I f (Module.finrank ℝ E - j) := by
  rw [criticalCount_def, criticalCount_def, criticalPoints_neg]
  congr 1
  refine sep_ext_iff.2 fun x hx ↦ ?_
  have := (hf.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints
    hx).manifoldMorseIndex_neg_add_manifoldMorseIndex_eq_finrank
  omega

end FiniteDimensional

section Compact

variable [I.Boundaryless] [IsManifold I 1 M] [CompactSpace M]

/-- A Morse function on a compact manifold has finitely many critical points. -/
theorem IsMorse.totalCriticalCount_ne_top (hf : IsMorse I f) : totalCriticalCount I f ≠ ⊤ :=
  encard_ne_top_iff.2 hf.finite_criticalPoints

/-- A Morse function on a compact manifold has finitely many critical points of each index. -/
theorem IsMorse.criticalCount_ne_top (hf : IsMorse I f) (j : ℕ) : criticalCount I f j ≠ ⊤ :=
  ne_top_of_le_ne_top hf.totalCriticalCount_ne_top (criticalCount_le_totalCriticalCount j)

end Compact

end TauCeti
