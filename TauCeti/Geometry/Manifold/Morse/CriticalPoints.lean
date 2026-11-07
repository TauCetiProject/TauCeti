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
public import TauCeti.Topology.ConnectedComponents
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Opens

/-!
# The critical set of a real function on a manifold

The critical set `TauCeti.criticalPoints I f` of a function `f : M → ℝ` is the zero locus of its
vector-valued manifold derivative `mvfderiv I f`, equivalently of `mfderiv I 𝓘(ℝ) f`. On a
boundaryless manifold it is also the set of points `x` at which the coordinate expression of `f`
in the preferred extended chart at `x` has zero Fréchet derivative. That is the criticality test
built into `TauCeti.IsMorseOn`, so a Morse function is exactly a smooth function all of whose
critical points are nondegenerate.

Local extrema are critical points, so a continuous function on a nonempty compact manifold has a
critical point, and so does each nonempty compact sublevel of a continuous function. On a compact
manifold with at least two points it has at least two critical points, a maximum and a minimum.
The critical set of a `C¹` function is closed, and a nondegenerate critical point is isolated in
it, so a Morse function has finitely many critical points in every compact set; for a proper
function bounded below, this applies to every sublevel set. A compact band between regular
values therefore holds finitely many critical levels, along which properties of the band can be
proved one level at a time. Above a regular value, the critical points in a compact band stay a
positive distance away in value, so the band begins with a collar free of critical points.

Restricting `f` to an open subset `U` keeps exactly the critical points lying in `U`, so the total
critical count is additive over a finite partition of `M` into open sets, such as its connected
components. In dimension zero every point is critical.

Critical points are counted, in total and by Morse index, with values in `ℕ∞`: an infinite
critical set has count `⊤`, never a junk natural number. The counts of a Morse function on a
compact manifold are finite, the counts by index add up to the total count, and replacing `f` by
`-f` exchanges the indices `j` and `dim M - j`. These counts are the coefficients of the Morse
polynomial in the Morse inequalities.

## Main declarations

* `TauCeti.criticalPoints`: the critical set, with `TauCeti.mem_criticalPoints_iff_mfderiv_eq_zero`,
  on boundaryless manifolds `TauCeti.mem_criticalPoints_iff_fderiv_comp_extChartAt_symm_eq_zero`,
  and on a normed space `TauCeti.mem_criticalPoints_iff_fderiv_eq_zero`.
* `TauCeti.isMorseOn_iff_criticalPoints`: Morse functions in terms of the critical set.
* `TauCeti.criticalPoints_comp_subtypeVal` and `TauCeti.totalCriticalCount_comp_subtypeVal`: the
  critical points of the restriction of `f` to an open submanifold `U` are those of `f` in `U`.
* `TauCeti.criticalPoints_comp_subtypeVal`: the critical set of a restriction to an open subset.
* `IsLocalExtr.mem_criticalPoints`, `TauCeti.criticalPoints_nonempty` and
  `TauCeti.exists_mem_criticalPoints_of_isCompact_sublevel`: Fermat's theorem on a manifold and the
  existence of critical points on compact manifolds and in compact sublevels.
* `TauCeti.isClosed_criticalPoints` and
  `TauCeti.IsManifoldNondegenerateCriticalPoint.eventually_notMem_criticalPoints`: the critical
  set of a `C¹` function is closed, and nondegenerate critical points are isolated in it.
* `TauCeti.exists_mem_Ioc_forall_notMem_criticalPoints`: a compact band starting at a regular
  value begins with a collar free of critical points.
* `TauCeti.IsMorse.eventually_eq_of_mem_criticalPoints`: the critical points of a Morse function
  are isolated.
* `TauCeti.finite_criticalPoints_inter_of_forall_isManifoldNondegenerateCriticalPoint`: a `C¹`
  function has finitely many critical points in a compact set where they are all nondegenerate.
* `TauCeti.IsMorse.finite_criticalPoints_inter` and
  `TauCeti.IsMorse.finite_criticalPoints_inter_preimage_Iic`: finiteness on compact sets and on
  sublevel sets of proper functions bounded below.
* `TauCeti.IsMorse.exists_criticalPoints_inter_preimage_Icc_subset`: in a compact band around
  `c`, a Morse function has no critical values close to `c` other than `c` itself.
* `TauCeti.IsMorse.band_induction`: a property of compact bands between regular values follows
  from its validity across bands without critical points, across single critical levels, and
  along triples of levels.
* `TauCeti.criticalCount` and `TauCeti.totalCriticalCount`: the extended counts of critical
  points, with `TauCeti.sum_criticalCount_eq_totalCriticalCount`,
  `TauCeti.IsMorse.totalCriticalCount_ne_top`, `TauCeti.two_le_totalCriticalCount` and
  `TauCeti.IsMorse.criticalCount_neg`.
* `TauCeti.exists_isMinOn_isMaxOn_of_totalCriticalCount_eq_two`, with
  `IsMinOn.eq_of_le_of_two_criticalPoints` and `IsMaxOn.eq_of_le_of_two_criticalPoints`: a function
  with exactly two critical points is constant or has them as its unique minimum and maximum.
* `TauCeti.totalCriticalCount_eq_finsum_connectedComponents`: the total count is the sum of the
  counts in the connected components, when there are finitely many.
* `TauCeti.totalCriticalCount_eq_sum` and `TauCeti.totalCriticalCount_eq_sum_connectedComponents`:
  additivity of the total count over finite open partitions and over connected components.
* `TauCeti.sum_range_neg_one_pow_mul_toNat_criticalCount_eq_sum`,
  `TauCeti.toNat_totalCriticalCount_modEq_sum_range_neg_one_pow_mul_toNat_criticalCount` and
  `TauCeti.IsMorse.sum_range_neg_one_pow_mul_toNat_criticalCount_neg`: the signed count
  `∑ᵢ (-1)ⁱ cᵢ` is the sum of `(-1)^λ` over the critical points, it has the parity of the number
  of critical points, and the signed counts of `f` and `-f` differ by the factor `(-1)ᵐ`.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §2.
-/

public section

open Function Set Filter Topology
open TopologicalSpace (Opens)
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

/-- On a normed space with its trivial model, a point is critical exactly when the Fréchet
derivative vanishes there. -/
theorem mem_criticalPoints_iff_fderiv_eq_zero {f : E → ℝ} {x : E} :
    x ∈ criticalPoints 𝓘(ℝ, E) f ↔ fderiv ℝ f x = 0 := by
  rw [mem_criticalPoints, mvfderiv_eq_fderiv]
  -- `NormedSpace.fromTangentSpace x` is the identity of `E`, read on the tangent space.
  exact Iff.rfl

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

/-- On a manifold modelled on a zero-dimensional space every point is critical. -/
@[simp]
theorem criticalPoints_eq_univ_of_subsingleton [Subsingleton E] : criticalPoints I f = univ :=
  -- The derivative at `x` is a linear form on the tangent space, which is the zero space `E`.
  eq_univ_of_forall fun _ ↦ Subsingleton.elim (α := E →L[ℝ] ℝ) _ _

/-- A function and its negation have the same critical points. -/
@[simp]
theorem criticalPoints_neg : criticalPoints I (-f) = criticalPoints I f := by
  ext x
  rw [mem_criticalPoints, mem_criticalPoints, mvfderiv_neg, neg_eq_zero]

/-! ### Restriction to an open submanifold -/

/-- A point of an open submanifold `U` is a critical point of the restriction of `f` to `U` exactly
when it is a critical point of `f`. -/
theorem mem_criticalPoints_comp_subtypeVal {U : Opens M} {x : U} :
    x ∈ criticalPoints I (f ∘ Subtype.val : U → ℝ) ↔ (x : M) ∈ criticalPoints I f := by
  by_cases hf : MDifferentiableAt I 𝓘(ℝ) f x
  swap
  · -- On the open set `U`, `f` and its restriction are differentiable at the same points, and
    -- both manifold derivatives vanish by convention where they are not.
    have hfU : ¬MDifferentiableAt I 𝓘(ℝ) (f ∘ Subtype.val : U → ℝ) x :=
      (differentiableWithinAt_localInvariantProp.liftPropAt_iff_comp_subtype_val f x).not.1 hf
    simp only [mem_criticalPoints_iff_mfderiv_eq_zero, mfderiv_zero_of_not_mdifferentiableAt hf,
      mfderiv_zero_of_not_mdifferentiableAt hfU]
  rw [mem_criticalPoints_iff_mfderiv_eq_zero, mem_criticalPoints_iff_mfderiv_eq_zero,
    mfderiv_comp x hf (contMDiff_subtype_val.mdifferentiableAt one_ne_zero),
    Manifold.mfderiv_subtype_val]
  refine ⟨fun h ↦ ContinuousLinearMap.ext fun v ↦ ?_,
    fun h ↦ by rw [h, ContinuousLinearMap.zero_comp]⟩
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply, zero_apply] using
    DFunLike.congr_fun h ((Manifold.tangentSpaceOpenEquiv (I := I) x).symm v)

/-- The critical points of the restriction of `f` to an open submanifold `U` are the critical
points of `f` lying in `U`. -/
@[simp]
theorem criticalPoints_comp_subtypeVal {U : Opens M} :
    criticalPoints I (f ∘ Subtype.val : U → ℝ) = Subtype.val ⁻¹' criticalPoints I f :=
  Set.ext fun _ ↦ mem_criticalPoints_comp_subtypeVal

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

/-- Where the coordinate expression of `f` in the preferred extended chart at `x` is differentiable,
`x` is a critical point exactly when that expression has zero Fréchet derivative. No boundary
hypothesis is needed: `range I` is uniquely differentiable, so the derivative within it is the
Fréchet derivative. -/
theorem mem_criticalPoints_iff_fderiv_comp_extChartAt_symm_eq_zero_of_differentiableAt
    (hg : DifferentiableAt ℝ (f ∘ (extChartAt I x).symm) (extChartAt I x x)) :
    x ∈ criticalPoints I f ↔
      fderiv ℝ (f ∘ (extChartAt I x).symm) (extChartAt I x x) = 0 := by
  have hf : MDifferentiableAt I 𝓘(ℝ) f x := by
    rw [mdifferentiableAt_iff]
    refine ⟨(hg.continuousAt.comp (continuousAt_extChartAt x)).congr
      (comp_extChartAt_symm_comp_extChartAt_eventuallyEq f x), ?_⟩
    simpa only [writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
      Function.id_comp] using hg.differentiableWithinAt
  have hu : UniqueDiffWithinAt ℝ (range I) (extChartAt I x x) :=
    I.uniqueDiffOn _ (extChartAt_target_subset_range x (mem_extChartAt_target x))
  rw [mem_criticalPoints, hf.mvfderiv]
  simp only [writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
    Function.id_comp]
  rw [hg.fderivWithin hu]
  -- The two sides differ only in reading the zero map on the tangent space or on `E`.
  exact Iff.rfl

/-- At a critical point, the coordinate expression of `f` in the preferred extended chart has zero
Fréchet derivative. No boundary hypothesis is needed: where the expression is not differentiable
the Fréchet derivative is zero by convention. -/
theorem fderiv_comp_extChartAt_symm_eq_zero_of_mem_criticalPoints (hx : x ∈ criticalPoints I f) :
    fderiv ℝ (f ∘ (extChartAt I x).symm) (extChartAt I x x) = 0 := by
  by_cases hg : DifferentiableAt ℝ (f ∘ (extChartAt I x).symm) (extChartAt I x x)
  · exact (mem_criticalPoints_iff_fderiv_comp_extChartAt_symm_eq_zero_of_differentiableAt hg).1 hx
  · exact fderiv_zero_of_not_differentiableAt hg

/-- A nondegenerate critical point is a critical point. -/
theorem IsManifoldNondegenerateCriticalPoint.mem_criticalPoints
    (h : IsManifoldNondegenerateCriticalPoint I f x) : x ∈ criticalPoints I f :=
  let h' := (isManifoldNondegenerateCriticalPoint_iff I).1 h
  (mem_criticalPoints_iff_fderiv_comp_extChartAt_symm_eq_zero_of_differentiableAt
    (h'.contDiffAt.differentiableAt (by simp))).2 h'.fderiv_eq_zero

/-- Every critical point in `s` of a function which is Morse on `s` is nondegenerate. -/
theorem IsMorseOn.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints
    (h : IsMorseOn I f s) (hs : x ∈ s) (hx : x ∈ criticalPoints I f) :
    IsManifoldNondegenerateCriticalPoint I f x :=
  (isMorseOn_iff.1 h).2 x hs (fderiv_comp_extChartAt_symm_eq_zero_of_mem_criticalPoints hx)

/-- Every critical point of a Morse function is nondegenerate. -/
theorem IsMorse.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints (h : IsMorse I f)
    (hx : x ∈ criticalPoints I f) : IsManifoldNondegenerateCriticalPoint I f x :=
  (isMorseOn_univ.2 h).isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints (mem_univ x) hx

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

/-- A function is Morse on `s` exactly when it is smooth on `s` and each of its critical points in
`s` is nondegenerate. -/
theorem isMorseOn_iff_criticalPoints :
    IsMorseOn I f s ↔
      ContMDiffOn I 𝓘(ℝ) ∞ f s ∧
        ∀ x ∈ s, x ∈ criticalPoints I f → IsManifoldNondegenerateCriticalPoint I f x := by
  simp only [isMorseOn_iff, mem_criticalPoints_iff_fderiv_comp_extChartAt_symm_eq_zero]

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

/-- If the only critical points of `f` are a global minimum `x₀` and a point `x₁` with a larger
value, then `x₀` is the only point at which `f` attains its minimum: any other such point would be
a third critical point. -/
theorem _root_.IsMinOn.eq_of_le_of_two_criticalPoints {x₀ x₁ y : M} (hx₀ : IsMinOn f univ x₀)
    (hlt : f x₀ < f x₁) (hcrit : ∀ x ∈ criticalPoints I f, x = x₀ ∨ x = x₁)
    (hy : f y ≤ f x₀) : y = x₀ := by
  have hy' : IsMinOn f univ y := isMinOn_univ_iff.2 fun z ↦ hy.trans (hx₀ (mem_univ z))
  refine (hcrit y (hy'.isLocalMin univ_mem).mem_criticalPoints).resolve_right ?_
  rintro rfl
  exact hy.not_gt hlt

/-- If the only critical points of `f` are a global maximum `x₁` and a point `x₀` with a smaller
value, then `x₁` is the only point at which `f` attains its maximum: any other such point would be
a third critical point. -/
theorem _root_.IsMaxOn.eq_of_le_of_two_criticalPoints {x₀ x₁ y : M} (hx₁ : IsMaxOn f univ x₁)
    (hlt : f x₀ < f x₁) (hcrit : ∀ x ∈ criticalPoints I f, x = x₀ ∨ x = x₁)
    (hy : f x₁ ≤ f y) : y = x₁ := by
  have hy' : IsMaxOn f univ y := isMaxOn_univ_iff.2 fun z ↦ (hx₁ (mem_univ z)).trans hy
  refine (hcrit y (hy'.isLocalMax univ_mem).mem_criticalPoints).resolve_left ?_
  rintro rfl
  exact hy.not_gt hlt

/-- A continuous function on a nonempty compact boundaryless manifold has a critical point, for
instance a point where it attains its minimum. -/
theorem criticalPoints_nonempty [CompactSpace M] [Nonempty M] (hf : Continuous f) :
    (criticalPoints I f).Nonempty := by
  obtain ⟨x, -, hx⟩ := isCompact_univ.exists_isMinOn univ_nonempty hf.continuousOn
  exact ⟨x, (hx.isLocalMin univ_mem).mem_criticalPoints⟩

/-- A function on a boundaryless manifold has a critical point in each nonempty compact sublevel
`{f ≤ t}` on which it is continuous, for instance a point where it attains its minimum. -/
theorem exists_mem_criticalPoints_of_isCompact_sublevel {t : ℝ}
    (hf : ContinuousOn f {x | f x ≤ t}) (hK : IsCompact {x | f x ≤ t})
    (hne : {x | f x ≤ t}.Nonempty) : ∃ x ∈ criticalPoints I f, f x ≤ t := by
  obtain ⟨x, hx, hmin⟩ := hK.exists_isMinOn hne hf
  -- Points outside the sublevel have values above `t ≥ f x`, so `x` is a global minimum.
  have hglobal : IsMinOn f univ x := fun y _ ↦
    (le_or_gt (f y) t).elim (fun hy ↦ hmin hy) fun hy ↦ (hx.trans hy.le : f x ≤ f y)
  exact ⟨x, (hglobal.isLocalMin univ_mem).mem_criticalPoints, hx⟩

end Boundaryless

/-! ### Closedness, isolation and finiteness -/

section IsManifold

variable [IsManifold I 1 M]

/-- The critical set of a `C¹` function is closed. -/
theorem isClosed_criticalPoints (hf : ContMDiff I 𝓘(ℝ) 1 f) : IsClosed (criticalPoints I f) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  set ψ := extChartAt I x
  -- In the chart at `x` the derivative of the coordinate expression is continuous on the chart
  -- target, so its nonvanishing locus pulls back to an open neighbourhood of `x` free of critical
  -- points.
  have hg : ContDiffOn ℝ 1 (f ∘ ψ.symm) ψ.target :=
    (hf.comp_contMDiffOn (contMDiffOn_extChartAt_symm x)).contDiffOn
  have hcrit : ∀ y ∈ ψ.source,
      y ∈ criticalPoints I f ↔ fderivWithin ℝ (f ∘ ψ.symm) ψ.target (ψ y) = 0 := by
    intro y hy
    have hyt : ψ y ∈ ψ.target := ψ.map_source hy
    rw [mem_criticalPoints_iff_mfderiv_eq_zero,
      ← fderivWithin_of_mem_nhdsWithin (extChartAt_target_mem_nhdsWithin_of_mem hyt)
        (I.uniqueDiffOn _ (extChartAt_target_subset_range x hyt))
        ((hg _ hyt).differentiableWithinAt one_ne_zero),
      (hf.mdifferentiableAt one_ne_zero).fderivWithin_comp_extChartAt_symm x hy]
    -- The change of tangent coordinates is invertible, so it can be cancelled.
    have hsurj : ∀ w, tangentCoordChange I x y y (tangentCoordChange I y x y w) = w := fun w ↦ by
      rw [tangentCoordChange_comp (w := y) ⟨⟨mem_extChartAt_source y, hy⟩,
        mem_extChartAt_source y⟩, tangentCoordChange_self (mem_extChartAt_source y)]
    refine ⟨fun h ↦ ContinuousLinearMap.ext fun w ↦ ?_, fun h ↦ ContinuousLinearMap.ext fun w ↦ ?_⟩
    · exact congr($h (tangentCoordChange I x y y w))
    have := congr($h (tangentCoordChange I y x y w))
    exact ((congrArg (mfderiv I 𝓘(ℝ) f y) (hsurj w).symm).trans this).trans rfl
  refine ⟨ψ.source ∩ (fun y ↦ fderivWithin ℝ (f ∘ ψ.symm) ψ.target (ψ y)) ⁻¹' {0}ᶜ, ?_, ?_, ?_⟩
  · rintro y ⟨hy, hy0⟩ hyc
    exact hy0 ((hcrit y hy).1 hyc)
  · exact ((hg.continuousOn_fderivWithin (uniqueDiffOn_extChartAt_target x) le_rfl).comp
      (continuousOn_extChartAt x) fun y hy ↦ ψ.map_source hy).isOpen_inter_preimage
      (isOpen_extChartAt_source x) isOpen_compl_singleton
  · exact ⟨mem_extChartAt_source x, fun h0 ↦ hx ((hcrit x (mem_extChartAt_source x)).2 h0)⟩

/-- **A regular value has a collar without critical points above it.** If `f` is `C¹`, `a < b`,
the band `f⁻¹[a, b]` is compact and `a` is a regular value of `f`, then for some `a' ∈ (a, b]` the
band `f⁻¹[a, a']` contains no critical point of `f`. -/
theorem exists_mem_Ioc_forall_notMem_criticalPoints (hf : ContMDiff I 𝓘(ℝ) 1 f) {a b : ℝ}
    (hab : a < b) (hcompact : IsCompact (f ⁻¹' Icc a b)) (ha : IsRegularValue I 𝓘(ℝ) f a) :
    ∃ a' ∈ Ioc a b, ∀ x ∈ criticalPoints I f, f x ∉ Icc a a' := by
  rw [isRegularValue_iff_notMem_image_criticalPoints] at ha
  have hS : IsCompact (criticalPoints I f ∩ f ⁻¹' Icc a b) :=
    hcompact.inter_left (isClosed_criticalPoints hf)
  rcases (criticalPoints I f ∩ f ⁻¹' Icc a b).eq_empty_or_nonempty with hS₀ | hSne
  · exact ⟨b, ⟨hab, le_rfl⟩, fun x hx hxab ↦ hS₀.subset ⟨hx, hxab⟩⟩
  -- Stop halfway to the lowest critical value of the band, which lies strictly above `a`.
  obtain ⟨p, ⟨hp, hpab⟩, hpmin⟩ := hS.exists_isMinOn hSne hf.continuous.continuousOn
  have hap : a < f p := hpab.1.lt_of_ne fun h ↦ ha ⟨p, hp, h.symm⟩
  refine ⟨(a + f p) / 2, ⟨by linarith, by linarith [hpab.2]⟩, fun x hx hxa ↦ ?_⟩
  have hpx := isMinOn_iff.1 hpmin x ⟨hx, hxa.1, by linarith [hxa.2, hpab.2]⟩
  linarith [hxa.2]

/-- **Nondegenerate critical points in a compact set are finite in number.** If every critical
point of a `C¹` function `f` in a compact set `K` is nondegenerate, then `K` contains only finitely
many critical points of `f`. Nothing is assumed about the critical points outside `K`. -/
theorem finite_criticalPoints_inter_of_forall_isManifoldNondegenerateCriticalPoint
    (hf : ContMDiff I 𝓘(ℝ) 1 f) {K : Set M} (hK : IsCompact K)
    (hnd : ∀ x ∈ criticalPoints I f ∩ K, IsManifoldNondegenerateCriticalPoint I f x) :
    (criticalPoints I f ∩ K).Finite := by
  refine (hK.inter_left (isClosed_criticalPoints hf)).finite ?_
  rw [isDiscrete_iff_nhdsNE]
  intro x hx
  rw [inf_principal_eq_bot]
  filter_upwards [(hnd x hx).eventually_notMem_criticalPoints] with y hy using fun h ↦ hy h.1

/-- **A Morse function has finitely many critical points in each compact set.** -/
theorem IsMorse.finite_criticalPoints_inter (hf : IsMorse I f) {K : Set M} (hK : IsCompact K) :
    (criticalPoints I f ∩ K).Finite :=
  finite_criticalPoints_inter_of_forall_isManifoldNondegenerateCriticalPoint
    (hf.contMDiff.of_le (by simp)) hK
    fun _ hx ↦ hf.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints hx.1

/-- **The critical points of a Morse function are isolated.** Near any point `x` there is no
critical point of a Morse function other than `x` itself. -/
theorem IsMorse.eventually_eq_of_mem_criticalPoints (hf : IsMorse I f) (x : M) :
    ∀ᶠ z in 𝓝 x, z ∈ criticalPoints I f → z = x := by
  by_cases hx : x ∈ criticalPoints I f
  · have hiso := (hf.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints
      hx).eventually_notMem_criticalPoints
    filter_upwards [eventually_nhdsWithin_iff.1 hiso] with z hz hzc
    by_contra hzx
    exact hz hzx hzc
  · filter_upwards [(isClosed_criticalPoints (hf.contMDiff.of_le (by simp))).isOpen_compl.mem_nhds
      hx] with z hz hzc
    exact absurd hzc hz

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

/-- **Critical values are isolated in a compact band.** If the band `f⁻¹[c - δ, c + δ]` of a Morse
function is compact, then for some `0 < ε ≤ δ` the only critical points in the band
`f⁻¹[c - ε, c + ε]` are those on the level `f⁻¹(c)`. -/
theorem IsMorse.exists_criticalPoints_inter_preimage_Icc_subset (hf : IsMorse I f) {c δ : ℝ}
    (hδ : 0 < δ) (hcompact : IsCompact (f ⁻¹' Icc (c - δ) (c + δ))) :
    ∃ ε, 0 < ε ∧ ε ≤ δ ∧ criticalPoints I f ∩ f ⁻¹' Icc (c - ε) (c + ε) ⊆ f ⁻¹' {c} := by
  -- The band holds finitely many critical values; avoid those different from `c`.
  set T := f '' (criticalPoints I f ∩ f ⁻¹' Icc (c - δ) (c + δ)) \ {c}
  have hT : IsClosed T := (((hf.finite_criticalPoints_inter hcompact).image f).sdiff).isClosed
  have hcT : Tᶜ ∈ 𝓝 c := hT.isOpen_compl.mem_nhds fun hc ↦ hc.2 rfl
  obtain ⟨ε₀, hε₀, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.1 hcT
  refine ⟨min ε₀ δ, lt_min hε₀ hδ, min_le_right _ _, fun y ⟨hy, hyε⟩ ↦ ?_⟩
  have h₀ := min_le_left ε₀ δ
  have h₁ := min_le_right ε₀ δ
  have hyδ : f y ∈ Icc (c - δ) (c + δ) := Icc_subset_Icc (by linarith) (by linarith) hyε
  have hyball : f y ∈ Metric.closedBall c ε₀ := by
    rw [Real.closedBall_eq_Icc]
    exact Icc_subset_Icc (by linarith) (by linarith) hyε
  by_contra hyc
  exact hball hyball ⟨⟨y, ⟨hy, hyδ⟩, rfl⟩, hyc⟩

/-- **Induction over the critical levels of a compact band.** Let `f` be a Morse function and
`a ≤ b` regular values of `f` with compact band `f⁻¹[a, b]`. A property `P s t` of intervals holds
for `[a, b]` if it holds across every compact band `f⁻¹[s, t]` without critical points, across
some `[c - ε, c + ε]` inside any compact band `f⁻¹[c - δ, c + δ]` around a critical value
`c ∈ (a, b)`, and passes from `[s, m]` and `[m, t]` to `[s, t]` when `f⁻¹[s, t]` is compact.

The proof cuts the band just above its lowest critical value and inducts on the number of critical
points in it. This is the induction along which Milnor's cell attachments across single critical
levels assemble into statements about a whole band. -/
theorem IsMorse.band_induction (hf : IsMorse I f) {P : ∀ s t : ℝ, s ≤ t → Prop} {a b : ℝ}
    (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b)) (ha : IsRegularValue I 𝓘(ℝ) f a)
    (hb : IsRegularValue I 𝓘(ℝ) f b)
    (hregular : ∀ s t (hst : s ≤ t), IsCompact (f ⁻¹' Icc s t) →
      (∀ x ∈ criticalPoints I f, f x ∉ Icc s t) → P s t hst)
    (hlevel : ∀ p ∈ criticalPoints I f, a < f p → f p < b → ∀ δ, 0 < δ →
      IsCompact (f ⁻¹' Icc (f p - δ) (f p + δ)) →
        ∃ ε, ∃ hε : 0 < ε, ε ≤ δ ∧ P (f p - ε) (f p + ε) (by linarith))
    (htrans : ∀ s m t (hsm : s ≤ m) (hmt : m ≤ t), IsCompact (f ⁻¹' Icc s t) → P s m hsm →
      P m t hmt → P s t (hsm.trans hmt)) :
    P a b hab := by
  have hfc : Continuous f := hf.contMDiff.continuous
  rw [isRegularValue_iff_notMem_image_criticalPoints] at ha hb
  -- Induct on the lower end `a' ≥ a` of the band, which shrinks at each cut.
  replace hlevel (p) (hp : p ∈ criticalPoints I f) {a' : ℝ} (haa' : a ≤ a') (hac : a' < f p) :=
    hlevel p hp (haa'.trans_lt hac)
  suffices ∀ N : ℕ, ∀ a', a ≤ a' → ∀ hab : a' ≤ b,
      (criticalPoints I f ∩ f ⁻¹' Icc a' b).ncard = N → IsCompact (f ⁻¹' Icc a' b) →
        a' ∉ f '' criticalPoints I f → P a' b hab
    from this _ a le_rfl hab rfl hcompact ha
  clear ha hcompact hab
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro a' haa' hab hN hcompact ha
  have hS := hf.finite_criticalPoints_inter hcompact
  rcases (criticalPoints I f ∩ f ⁻¹' Icc a' b).eq_empty_or_nonempty with hS₀ | hSne
  · exact hregular a' b hab hcompact fun x hx hxab ↦ hS₀.subset ⟨hx, hxab⟩
  -- Cut the band just above the lowest critical value `c` in it.
  obtain ⟨p, ⟨hp, hpab⟩, hpmin⟩ := hS.isCompact.exists_isMinOn hSne hfc.continuousOn
  have hac : a' < f p := hpab.1.lt_of_ne fun h ↦ ha ⟨p, hp, h.symm⟩
  have hcb : f p < b := hpab.2.lt_of_ne fun h ↦ hb ⟨p, hp, h⟩
  have hcompact' {s t : ℝ} (hs : a' ≤ s) (ht : t ≤ b) : IsCompact (f ⁻¹' Icc s t) :=
    hcompact.of_isClosed_subset (isClosed_Icc.preimage hfc)
      (preimage_mono (Icc_subset_Icc hs ht))
  -- Some `[c - δ, c + δ]` lies in `(a', b)` and contains no critical value other than `c`.
  obtain ⟨δ, hδ, hδa, hδb⟩ : ∃ δ, 0 < δ ∧ a' < f p - δ ∧ f p + δ < b :=
    ⟨min (f p - a') (b - f p) / 2, half_pos (lt_min (sub_pos.2 hac) (sub_pos.2 hcb)),
      by linarith [min_le_left (f p - a') (b - f p)],
      by linarith [min_le_right (f p - a') (b - f p)]⟩
  obtain ⟨δ', hδ', hδ'δ, hsub⟩ :=
    hf.exists_criticalPoints_inter_preimage_Icc_subset hδ (hcompact' hδa.le hδb.le)
  obtain ⟨ε, hε, hεδ', hmid⟩ :=
    hlevel p hp haa' hac hcb δ' hδ' (hcompact' (by linarith) (by linarith))
  -- Below `c - ε` the band holds no critical point, since `c` is the lowest critical value.
  have hlow : P a' (f p - ε) (by linarith) :=
    hregular _ _ _ (hcompact' le_rfl (by linarith)) fun x hx hxI ↦ by
      have : f p ≤ f x := hpmin ⟨hx, hxI.1, by linarith [hxI.2]⟩
      linarith [hxI.2]
  -- Above `c + ε` the band holds fewer critical points, missing `p`.
  have hlt : (criticalPoints I f ∩ f ⁻¹' Icc (f p + ε) b).ncard < N := by
    rw [← hN]
    refine ncard_lt_ncard ⟨fun x hx ↦ ⟨hx.1, by linarith [hx.2.1], hx.2.2⟩,
      fun h ↦ ?_⟩ hS
    have := (h ⟨hp, hpab⟩).2.1
    linarith
  have hup : P (f p + ε) b (by linarith) :=
    ih _ hlt _ (by linarith) _ rfl (hcompact' (by linarith) le_rfl) fun ⟨x, hx, hxc⟩ ↦ by
      have := hsub ⟨hx, by rw [hxc]; linarith, by rw [hxc]; linarith⟩
      rw [mem_preimage, mem_singleton_iff, hxc] at this
      linarith
  exact htrans _ _ _ _ _ hcompact
    (htrans _ _ _ _ _ (hcompact' le_rfl (by linarith)) hlow hmid) hup

end IsManifold

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

/-- The number of critical points of the restriction of `f` to an open submanifold `U` is the
number of critical points of `f` in `U`. -/
@[simp]
theorem totalCriticalCount_comp_subtypeVal {U : Opens M} :
    totalCriticalCount I (f ∘ Subtype.val : U → ℝ) = (criticalPoints I f ∩ U).encard := by
  rw [totalCriticalCount_def, criticalPoints_comp_subtypeVal,
    ← Subtype.val_injective.encard_image, image_preimage_eq_inter_range, Subtype.range_val]

/-- **The critical count is additive over components.** If `M` has finitely many connected
components, the number of critical points of `f` is the sum over the components of the numbers of
critical points of `f` in each. -/
theorem totalCriticalCount_eq_finsum_connectedComponents [Finite (ConnectedComponents M)] :
    totalCriticalCount I f = ∑ᶠ C : ConnectedComponents M,
      (criticalPoints I f ∩ ConnectedComponents.mk ⁻¹' {C}).encard := by
  have hd : Pairwise (Disjoint on fun C : ConnectedComponents M ↦
      criticalPoints I f ∩ ConnectedComponents.mk ⁻¹' {C}) := fun _ _ h ↦
    ((disjoint_singleton.2 h).preimage _).mono inter_subset_right inter_subset_right
  rw [totalCriticalCount_def, ← encard_iUnion_of_finite hd, ← inter_iUnion, ← preimage_iUnion,
    iUnion_of_singleton, preimage_univ, inter_univ]

/-- **Additivity of the critical count.** If finitely many pairwise disjoint open subsets `U i`
cover `M`, for instance the connected components of a compact manifold, then the number of
critical points of `f` is the sum of the numbers of critical points of its restrictions to the
`U i`. -/
theorem totalCriticalCount_eq_sum {ι : Type*} [Fintype ι] (U : ι → Opens M)
    (hd : Pairwise (Disjoint on U)) (hU : ⨆ i, U i = ⊤) :
    totalCriticalCount I f = ∑ i, totalCriticalCount I (f ∘ (Subtype.val : U i → M)) := by
  have hd' : Pairwise (Disjoint on fun i ↦ criticalPoints I f ∩ U i) := fun i j hij ↦
    (Opens.coe_disjoint.mpr (hd hij)).inter_left' _ |>.inter_right' _
  simp_rw [totalCriticalCount_comp_subtypeVal, ← finsum_eq_sum_of_fintype,
    ← encard_iUnion_of_finite hd', ← inter_iUnion, ← Opens.coe_iSup, hU, Opens.coe_top,
    inter_univ, totalCriticalCount_def]

/-- **The component sum formula for critical points.** If `M` is locally connected with finitely
many connected components, for instance compact and boundaryless, then the number of critical
points of `f` is the sum over the components `C` of the numbers of critical points of the
restrictions of `f` to `C`, each component carrying its structure as an open submanifold. -/
theorem totalCriticalCount_eq_sum_connectedComponents [LocallyConnectedSpace M]
    [Fintype (ConnectedComponents M)] :
    totalCriticalCount I f =
      ∑ C : ConnectedComponents M, totalCriticalCount I (f ∘ (Subtype.val : C.opens → M)) :=
  totalCriticalCount_eq_sum _ ConnectedComponents.pairwise_disjoint_opens
    ConnectedComponents.iSup_opens

/-- A continuous function on a compact boundaryless manifold with at least two points has at least
two critical points: a point of maximum and a point of minimum, which can coincide only for a
constant function, all of whose points are critical. -/
theorem two_le_totalCriticalCount [I.Boundaryless] [CompactSpace M] [Nontrivial M]
    (hf : Continuous f) : 2 ≤ totalCriticalCount I f := by
  obtain ⟨p, -, hp⟩ := isCompact_univ.exists_isMaxOn univ_nonempty hf.continuousOn
  obtain ⟨q, -, hq⟩ := isCompact_univ.exists_isMinOn univ_nonempty hf.continuousOn
  rw [isMaxOn_univ_iff] at hp
  rw [isMinOn_univ_iff] at hq
  have hpair {x y : M} (hxy : x ≠ y) (hx : x ∈ criticalPoints I f)
      (hy : y ∈ criticalPoints I f) : 2 ≤ (criticalPoints I f).encard :=
    (encard_pair hxy).symm.le.trans (encard_le_encard (pair_subset hx hy))
  rw [totalCriticalCount_def]
  obtain hpq | rfl := ne_or_eq p q
  · exact hpair hpq (IsLocalMax.mem_criticalPoints (.of_forall hp))
      (IsLocalMin.mem_criticalPoints (.of_forall hq))
  · -- The maximum and the minimum are attained at the same point, so `f` is constant and every
    -- point is a local maximum.
    have hcrit (x : M) : x ∈ criticalPoints I f :=
      IsLocalMax.mem_criticalPoints (.of_forall fun y ↦ (hp y).trans (hq x))
    obtain ⟨x, y, hxy⟩ := exists_pair_ne M
    exact hpair hxy (hcrit x) (hcrit y)

/-- A continuous function on a compact boundaryless manifold with exactly two critical points
attains its minimum at one of them, `x₀`, and its maximum at the other, `x₁`. Either
`f x₀ < f x₁`, or `f` is constant, every point is critical, and `M` consists of `x₀` and `x₁`. -/
theorem exists_isMinOn_isMaxOn_of_totalCriticalCount_eq_two [I.Boundaryless] [CompactSpace M]
    (hf : Continuous f) (h2 : totalCriticalCount I f = 2) :
    ∃ x₀ x₁ : M, IsMinOn f univ x₀ ∧ IsMaxOn f univ x₁ ∧ x₀ ≠ x₁ ∧
      criticalPoints I f = {x₀, x₁} ∧
      (f x₀ < f x₁ ∨ (∀ x, f x = f x₀) ∧ criticalPoints I f = univ) := by
  obtain ⟨p, q, hpq, hpq'⟩ := encard_eq_two.1 ((totalCriticalCount_def (I := I)).symm.trans h2)
  obtain ⟨x₀, -, hx₀⟩ := isCompact_univ.exists_isMinOn ⟨p, mem_univ p⟩ hf.continuousOn
  obtain ⟨x₁, -, hx₁⟩ := isCompact_univ.exists_isMaxOn ⟨p, mem_univ p⟩ hf.continuousOn
  rcases (hx₀ (mem_univ x₁)).lt_or_eq with hlt | hconst
  · -- The minimum and the maximum are two distinct critical points, so they are all of them.
    have h₀ := (hx₀.isLocalMin univ_mem).mem_criticalPoints (I := I)
    have h₁ := (hx₁.isLocalMax univ_mem).mem_criticalPoints (I := I)
    have hne : x₀ ≠ x₁ := fun h ↦ hlt.ne (congrArg f h)
    refine ⟨x₀, x₁, hx₀, hx₁, hne, ?_, .inl hlt⟩
    rw [hpq', mem_insert_iff, mem_singleton_iff] at h₀ h₁
    rw [hpq']
    ext x
    simp only [mem_insert_iff, mem_singleton_iff]
    grind
  -- A constant function: every point is a minimum and a maximum, and every point is critical.
  have hall (x : M) : f x = f x₀ := le_antisymm (hconst ▸ hx₁ (mem_univ x)) (hx₀ (mem_univ x))
  have hmin (x : M) : IsMinOn f univ x := isMinOn_univ_iff.2 fun y ↦ by rw [hall x, hall y]
  have hmax (x : M) : IsMaxOn f univ x := isMaxOn_univ_iff.2 fun y ↦ by rw [hall x, hall y]
  have hcrit : criticalPoints I f = univ :=
    eq_univ_of_forall fun x ↦ ((hmin x).isLocalMin univ_mem).mem_criticalPoints
  exact ⟨p, q, hmin p, hmax q, hpq, hpq', .inr ⟨fun x ↦ by rw [hall x, hall p], hcrit⟩⟩

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

/-- The signed count `∑ᵢ (-1)ⁱ cᵢ` of the critical points of `f`, by index, is the sum of `(-1)^λ`
over the critical points, `λ` being the Morse index, when the critical set is a finite set `s`.
Here `n` is any bound for the dimension of `M`. -/
theorem sum_range_neg_one_pow_mul_toNat_criticalCount_eq_sum (s : Finset M)
    (hs : (s : Set M) = criticalPoints I f) {n : ℕ} (hn : Module.finrank ℝ E ≤ n) :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * (criticalCount I f i).toNat =
      ∑ x ∈ s, (-1 : ℤ) ^ manifoldMorseIndex I f x := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := manifoldMorseIndex I f)
    (t := Finset.range (n + 1)) fun x _ ↦
      Finset.mem_range.2 (Nat.lt_succ_of_le (manifoldMorseIndex_le_finrank.trans hn))]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hi : {x ∈ criticalPoints I f | manifoldMorseIndex I f x = i} =
      ↑({x ∈ s | manifoldMorseIndex I f x = i} : Finset M) := by
    ext x
    simp [← hs]
  rw [Finset.sum_congr rfl fun x hx ↦ by rw [(Finset.mem_filter.1 hx).2], criticalCount_def, hi,
    encard_coe_eq_coe_finsetCard]
  simp [mul_comm]

/-- Terms of index above the dimension of `M` do not contribute to a signed count
`∑ᵢ (-1)ⁱ cᵢ` of critical points, so it may be truncated at `dim M`. -/
theorem sum_range_neg_one_pow_mul_toNat_criticalCount_of_finrank_le {n : ℕ}
    (hn : Module.finrank ℝ E ≤ n) :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * (criticalCount I f i).toNat =
      ∑ i ∈ Finset.range (Module.finrank ℝ E + 1), (-1 : ℤ) ^ i * (criticalCount I f i).toNat := by
  refine (Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun i hi hi' ↦ ?_).symm
  rw [criticalCount_eq_zero_of_finrank_lt (by simp_all), ENat.toNat_zero, Nat.cast_zero, mul_zero]

/-- **Parity of the critical count.** If `f` has finitely many critical points, their number is
congruent modulo `2` to the signed count `∑ᵢ (-1)ⁱ cᵢ`, for any bound `n` of the dimension of
`M`. -/
theorem toNat_totalCriticalCount_modEq_sum_range_neg_one_pow_mul_toNat_criticalCount
    (h : (criticalPoints I f).Finite) {n : ℕ} (hn : Module.finrank ℝ E ≤ n) :
    ((totalCriticalCount I f).toNat : ℤ) ≡
      ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * (criticalCount I f i).toNat [ZMOD 2] := by
  rw [sum_range_neg_one_pow_mul_toNat_criticalCount_eq_sum h.toFinset h.coe_toFinset hn,
    totalCriticalCount_def, h.encard_eq_coe_toFinset_card, ENat.toNat_natCast,
    Finset.card_eq_sum_ones]
  push_cast
  refine Int.ModEq.sum fun x _ ↦ ?_
  exact (by simpa using ((show (-1 : ℤ) ≡ 1 [ZMOD 2] by decide).pow (manifoldMorseIndex I f x)) :
    (-1 : ℤ) ^ manifoldMorseIndex I f x ≡ 1 [ZMOD 2]).symm

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

/-- **Signed counts of `f` and `-f`.** For a Morse function `f` on a manifold of dimension `m`, the
signed counts `∑ᵢ (-1)ⁱ cᵢ` of the critical points of `-f` and of `f` differ by the factor `(-1)ᵐ`,
since the critical points of index `i` of `-f` are those of index `m - i` of `f`. -/
theorem IsMorse.sum_range_neg_one_pow_mul_toNat_criticalCount_neg (hf : IsMorse I f) {n : ℕ}
    (hn : Module.finrank ℝ E ≤ n) :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * (criticalCount I (-f) i).toNat =
      (-1) ^ Module.finrank ℝ E *
        ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * (criticalCount I f i).toNat := by
  rw [sum_range_neg_one_pow_mul_toNat_criticalCount_of_finrank_le hn,
    sum_range_neg_one_pow_mul_toNat_criticalCount_of_finrank_le hn, Finset.mul_sum,
    ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi : i ≤ Module.finrank ℝ E := Nat.le_of_lt_succ (Finset.mem_range.1 hi)
  rw [add_tsub_cancel_right, hf.criticalCount_neg (Nat.sub_le _ _), Nat.sub_sub_self hi]
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le' hi
  simp [hd, pow_add, mul_assoc, ← mul_assoc ((-1 : ℤ) ^ i), ← mul_pow]

end FiniteDimensional

section Compact

variable [IsManifold I 1 M] [CompactSpace M]

/-- A Morse function on a compact manifold has finitely many critical points. -/
theorem IsMorse.totalCriticalCount_ne_top (hf : IsMorse I f) : totalCriticalCount I f ≠ ⊤ :=
  encard_ne_top_iff.2 hf.finite_criticalPoints

/-- A Morse function on a compact manifold has finitely many critical points of each index. -/
theorem IsMorse.criticalCount_ne_top (hf : IsMorse I f) (j : ℕ) : criticalCount I f j ≠ ⊤ :=
  ne_top_of_le_ne_top hf.totalCriticalCount_ne_top (criticalCount_le_totalCriticalCount j)

end Compact

end TauCeti
