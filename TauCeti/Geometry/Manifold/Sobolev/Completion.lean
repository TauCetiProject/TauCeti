/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Analysis.Normed.Operator.Extend
public import TauCeti.Analysis.Sobolev.BesselPotential.Inclusion
public import TauCeti.Analysis.Sobolev.BesselPotential.Multiplication
public import TauCeti.Geometry.Manifold.DifferentialOperator.ChartCompression.Schwartz
import TauCeti.Analysis.Distribution.SchwartzSpace.Cutoff
import TauCeti.Analysis.Distribution.TemperedDistribution.SmulLeft
import TauCeti.Analysis.Normed.Lp.PiLp.Basic
import TauCeti.Analysis.Sobolev.BesselPotential.Rellich
import TauCeti.Geometry.Manifold.Sobolev.ChartReading

/-!
# Sobolev spaces of a compact manifold as completions of smooth functions

Let `M` be a manifold modelled on `ℝⁿ`, and let `ψᵢ` be finitely many cutoffs in charts `eᵢ` of the
maximal atlas. A complex-valued smooth function `u` on `M` is read in the `i`-th chart as the
Schwartz function `ψᵢ · (u ∘ eᵢ⁻¹)` (`OpenPartialHomeomorph.cutoffPushforwardSchwartz`). For a real
order `s`, the **chart readings** of `u` are the tuple of these readings in the Hilbert sum
`⨁ᵢ H^s(ℝⁿ)` (`TauCeti.chartReading`), whose norm is `(∑ᵢ ‖ψᵢ · (u ∘ eᵢ⁻¹)‖²_{H^s})^{1/2}`.

The **Sobolev space** `H^s(M)` of the family is the closure of the chart readings of all smooth
functions (`TauCeti.chartSobolevSpace`): a closed subspace of `⨁ᵢ H^s(ℝⁿ)`, hence a Hilbert space,
in which the smooth functions are dense (`TauCeti.denseRange_toChartSobolevSpace`). For a chart
partition of a compact manifold it is the completion of the smooth functions in the norm through
which Taylor defines the Sobolev spaces of a compact manifold. A continuous linear map out of it is
determined by its values on smooth functions (`TauCeti.chartSobolevSpace_ext`). This is the space on
which operators defined on smooth functions, such as pseudodifferential operators, act once they
satisfy an a priori estimate in the chart-reading norms (`TauCeti.chartSobolevExtension`); the
extension is unique, and extensions compose.

* For `r ≤ s`, the inclusions `H^s(ℝⁿ) ⊆ H^r(ℝⁿ)` give the inclusion `H^s(M) ⊆ H^r(M)`
  (`TauCeti.chartSobolevInclusion`), which restricts to the identity on smooth functions. It is
  injective (`TauCeti.chartSobolevInclusion_injective`) with dense range
  (`TauCeti.denseRange_chartSobolevInclusion`), and it commutes with the extensions of operators
  (`TauCeti.chartSobolevInclusion_comp_chartSobolevExtension`,
  `TauCeti.chartSobolevExtension_comp_chartSobolevInclusion`).
* **Independence of the charts.** If the readings `ψᵢ ∘ eᵢ` of the cutoffs on `M`, extended by `0`,
  add up to `1`, then the chart readings of `u` in any other finite family of charts and cutoffs are
  bounded in `H^s` by those in the `eᵢ` (`TauCeti.exists_norm_chartReading_le`), because changing
  the chart of a reading costs a constant
  (`TauCeti.exists_norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_mulLeft_le`). So two
  such families define the same space up to a continuous linear isomorphism that is the identity on
  smooth functions (`TauCeti.chartSobolevSpaceCongr`), and these isomorphisms transport the
  extension of an operator between the spaces of one pair of families to its extension between
  those of another (`TauCeti.chartSobolevExtension_eq_chartSobolevSpaceCongr_comp`).
* **Rellich's theorem.** For `r < s` the inclusion `H^s(M) ⊆ H^r(M)` is compact
  (`TauCeti.isCompactOperator_chartSobolevInclusion`). Every component of an element of `H^s(M)` is
  fixed by a Schwartz function equal to `1` on the support of its cutoff
  (`TauCeti.smulLeftCLM_chartSobolevSpace_apply_of_eqOn_one`), so componentwise the inclusion is
  multiplication by that function, compact by the Euclidean Rellich theorem for a common compact
  support in a finite Hilbert sum (`BesselPotentialSpace.isCompactOperator_piLp_of_smulLeftCLM_eq`).

Such families of cutoffs exist on every compact manifold
(`IsCompact.exists_sum_cutoffPullback_eq_one`).

## Main definitions

* `TauCeti.chartReading`: the chart readings of a smooth function, in `⨁ᵢ H^s(ℝⁿ)`.
* `TauCeti.chartSobolevSpace`: the closure of the chart readings of smooth functions.
* `TauCeti.toChartSobolevSpace`: a smooth function as an element of `H^s(M)`.
* `TauCeti.chartSobolevInclusion`: the inclusion `H^s(M) ⊆ H^r(M)` for `r ≤ s`.
* `TauCeti.chartSobolevExtension`: the continuous extension `H^s(M) → H^t(M)` of an operator on
  smooth functions satisfying an a priori estimate.
* `TauCeti.chartSobolevSpaceCongr`: the isomorphism between the spaces of two chart partitions.

## Main results

* `TauCeti.denseRange_toChartSobolevSpace`: smooth functions are dense in `H^s(M)`.
* `TauCeti.chartSobolevExtension_toChartSobolevSpace`, `TauCeti.chartSobolevExtension_eq`: the
  extension of an operator satisfying an a priori estimate agrees with it on smooth functions, and
  is the only continuous map that does; `TauCeti.chartSobolevExtension_comp`: extensions compose.
* `TauCeti.isCompactOperator_chartSobolevInclusion`: the Rellich theorem, `H^s(M) ⊆ H^r(M)` is
  compact for `r < s`.
* `TauCeti.chartSobolevInclusion_injective`, `TauCeti.denseRange_chartSobolevInclusion`: the
  inclusion `H^s(M) ⊆ H^r(M)` is injective with dense range.
* `TauCeti.exists_norm_chartReading_le`: chart readings in any family of charts are bounded by
  those in a chart partition.

## References

* M. E. Taylor, *Partial Differential Equations I*, 2nd ed., Springer, 2011, Chapter 4, §3
  (Sobolev spaces on compact manifolds, defined through a partition of unity and charts).
-/

public section

noncomputable section

open Set TauCeti OpenPartialHomeomorph
open scoped ContDiff Manifold Distributions SchwartzMap BesselPotentialSpace

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  {ι : Type*} {e : ι → OpenPartialHomeomorph M (CoordinateSpace n)}
  (he : ∀ i, e i ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
  (ψ : ∀ i, 𝓓(⟨(e i).target, (e i).open_target⟩, ℝ))

/-- The **chart readings** of a smooth function `u` on `M` of order `s`: the tuple of its readings
`ψᵢ · (u ∘ eᵢ⁻¹)` in the charts `eᵢ`, in the Hilbert sum `⨁ᵢ H^s(ℝⁿ)`. -/
def chartReading (s : ℝ) :
    C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
      PiLp 2 fun _ : ι ↦ H^{s}(CoordinateSpace n) where
  toFun u := WithLp.toLp 2 fun i ↦
    SchwartzMap.toBesselPotentialSpaceCLM s 2 ((e i).cutoffPushforwardSchwartz (he i) (ψ i) u)
  map_add' u v := by
    ext1 i
    simp
  map_smul' c u := by
    ext1 i
    simp

@[simp]
theorem chartReading_apply (s : ℝ) (u : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) (i : ι) :
    chartReading he ψ s u i =
      SchwartzMap.toBesselPotentialSpaceCLM s 2 ((e i).cutoffPushforwardSchwartz (he i) (ψ i) u) :=
  (rfl)

variable [Fintype ι]

/-- The **Sobolev space** `H^s(M)` of the charts `eᵢ` and cutoffs `ψᵢ`: the closure in the Hilbert
sum `⨁ᵢ H^s(ℝⁿ)` of the chart readings of the smooth functions on `M`. It is closed, hence a
Hilbert space. -/
def chartSobolevSpace (s : ℝ) : Submodule ℂ (PiLp 2 fun _ : ι ↦ H^{s}(CoordinateSpace n)) :=
  (LinearMap.range (chartReading he ψ s)).topologicalClosure

instance (s : ℝ) : CompleteSpace (chartSobolevSpace he ψ s) :=
  inferInstanceAs (CompleteSpace (LinearMap.range (chartReading he ψ s)).topologicalClosure)

theorem isClosed_chartSobolevSpace (s : ℝ) :
    IsClosed (chartSobolevSpace he ψ s : Set (PiLp 2 fun _ : ι ↦ H^{s}(CoordinateSpace n))) :=
  Submodule.isClosed_topologicalClosure _

/-- The elements of `H^s(M)` are the limits in `⨁ᵢ H^s(ℝⁿ)` of chart readings of smooth
functions. -/
theorem mem_chartSobolevSpace_iff {s : ℝ} {x : PiLp 2 fun _ : ι ↦ H^{s}(CoordinateSpace n)} :
    x ∈ chartSobolevSpace he ψ s ↔ x ∈ closure (range (chartReading he ψ s)) := by
  rw [← SetLike.mem_coe, chartSobolevSpace, Submodule.topologicalClosure_coe, LinearMap.coe_range]

/-- `H^s(M)` is the smallest closed subspace of `⨁ᵢ H^s(ℝⁿ)` containing the chart readings of all
smooth functions. -/
theorem chartSobolevSpace_le_of_isClosed {s : ℝ}
    {S : Submodule ℂ (PiLp 2 fun _ : ι ↦ H^{s}(CoordinateSpace n))}
    (hS : IsClosed (S : Set (PiLp 2 fun _ : ι ↦ H^{s}(CoordinateSpace n))))
    (h : ∀ u, chartReading he ψ s u ∈ S) : chartSobolevSpace he ψ s ≤ S :=
  Submodule.topologicalClosure_minimal _ (LinearMap.range_le_iff_comap.2
    (eq_top_iff.2 fun u _ ↦ h u)) hS

theorem chartReading_mem_chartSobolevSpace (s : ℝ)
    (u : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) :
    chartReading he ψ s u ∈ chartSobolevSpace he ψ s :=
  Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ u)

/-- A smooth function `u` on `M` as an element of the Sobolev space `H^s(M)`: its chart
readings. -/
def toChartSobolevSpace (s : ℝ) :
    C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ] chartSobolevSpace he ψ s :=
  (chartReading he ψ s).codRestrict _ (chartReading_mem_chartSobolevSpace he ψ s)

@[simp]
theorem coe_toChartSobolevSpace (s : ℝ) (u : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) :
    (toChartSobolevSpace he ψ s u : PiLp 2 fun _ : ι ↦ H^{s}(CoordinateSpace n)) =
      chartReading he ψ s u :=
  (rfl)

theorem norm_toChartSobolevSpace (s : ℝ) (u : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) :
    ‖toChartSobolevSpace he ψ s u‖ = ‖chartReading he ψ s u‖ :=
  (rfl)

/-- **Smooth functions are dense** in the Sobolev space `H^s(M)`. -/
theorem denseRange_toChartSobolevSpace (s : ℝ) : DenseRange (toChartSobolevSpace he ψ s) := by
  rw [DenseRange, Subtype.dense_iff, ← range_comp]
  exact (Submodule.topologicalClosure_coe _).le

/-- A continuous linear map out of the Sobolev space `H^s(M)` is determined by its values on
smooth functions. -/
theorem chartSobolevSpace_ext {F : Type*} [TopologicalSpace F] [AddCommMonoid F] [Module ℂ F]
    [T2Space F] {s : ℝ} {f g : chartSobolevSpace he ψ s →L[ℂ] F}
    (h : ∀ u, f (toChartSobolevSpace he ψ s u) = g (toChartSobolevSpace he ψ s u)) : f = g :=
  ContinuousLinearMap.ext fun x ↦ (denseRange_toChartSobolevSpace he ψ s).induction
    (fun _ ⟨u, hu⟩ ↦ hu ▸ h u) (isClosed_eq f.continuous g.continuous) x

/-! ### The inclusions between the Sobolev spaces -/

variable {r s : ℝ}

/-- The componentwise inclusion `⨁ᵢ H^s(ℝⁿ) ⊆ ⨁ᵢ H^r(ℝⁿ)` maps `H^s(M)` into `H^r(M)`: it sends
the chart readings of order `s` to those of order `r`, hence their closure into the closure. -/
private theorem piMap_inclusion_mem_chartSobolevSpace (h : r ≤ s) (x : chartSobolevSpace he ψ s) :
    PiLp.piMap 2 (fun _ ↦ BesselPotentialSpace.inclusion h)
      (x : PiLp 2 fun _ : ι ↦ H^{s}(CoordinateSpace n)) ∈ chartSobolevSpace he ψ r := by
  refine Submodule.topologicalClosure_mono ?_
    (Submodule.topologicalClosure_map _ _ (Submodule.mem_map_of_mem x.property))
  rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩
  refine ⟨u, ?_⟩
  ext1 i
  simp

/-- The inclusion `H^s(M) ⊆ H^r(M)` for `r ≤ s`: the inclusion `H^s(ℝⁿ) ⊆ H^r(ℝⁿ)`
(`BesselPotentialSpace.inclusion`) in every component, which sends the chart readings of order `s`
of a smooth function to those of order `r` (`TauCeti.chartSobolevInclusion_toChartSobolevSpace`). -/
def chartSobolevInclusion (h : r ≤ s) : chartSobolevSpace he ψ s →L[ℂ] chartSobolevSpace he ψ r :=
  ((PiLp.piMap 2 fun _ ↦ BesselPotentialSpace.inclusion h) ∘L
    (chartSobolevSpace he ψ s).subtypeL).codRestrict _
    (piMap_inclusion_mem_chartSobolevSpace he ψ h)

@[simp]
theorem coe_chartSobolevInclusion_apply (h : r ≤ s) (x : chartSobolevSpace he ψ s) (i : ι) :
    (chartSobolevInclusion he ψ h x : PiLp 2 fun _ : ι ↦ H^{r}(CoordinateSpace n)) i =
      BesselPotentialSpace.inclusion h ((x : PiLp 2 fun _ : ι ↦ H^{s}(CoordinateSpace n)) i) :=
  PiLp.piMap_apply ..

@[simp]
theorem chartSobolevInclusion_toChartSobolevSpace (h : r ≤ s)
    (u : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) :
    chartSobolevInclusion he ψ h (toChartSobolevSpace he ψ s u) = toChartSobolevSpace he ψ r u := by
  ext1
  ext1 i
  simp

/-- The inclusion `H^s(M) ⊆ H^r(M)` does not increase norms. -/
theorem norm_chartSobolevInclusion_apply_le (h : r ≤ s) (x : chartSobolevSpace he ψ s) :
    ‖chartSobolevInclusion he ψ h x‖ ≤ ‖x‖ := by
  rw [← Submodule.norm_coe, ← Submodule.norm_coe x]
  refine PiLp.norm_mono fun i ↦ ?_
  rw [coe_chartSobolevInclusion_apply]
  exact BesselPotentialSpace.norm_inclusion_apply_le h _

/-- The inclusion `H^s(M) ⊆ H^s(M)` is the identity. -/
@[simp]
theorem chartSobolevInclusion_self : chartSobolevInclusion he ψ (le_refl s) = 1 :=
  chartSobolevSpace_ext he ψ fun u ↦ by simp

/-- The inclusions `H^s(M) ⊆ H^r(M) ⊆ H^t(M)` compose to the inclusion `H^s(M) ⊆ H^t(M)`. -/
@[simp]
theorem chartSobolevInclusion_comp_chartSobolevInclusion {t : ℝ} (h₁ : r ≤ s) (h₂ : t ≤ r) :
    chartSobolevInclusion he ψ h₂ ∘L chartSobolevInclusion he ψ h₁ =
      chartSobolevInclusion he ψ (h₂.trans h₁) :=
  chartSobolevSpace_ext he ψ fun u ↦ by simp

/-- The inclusion `H^s(M) ⊆ H^r(M)` is injective. -/
theorem chartSobolevInclusion_injective (h : r ≤ s) :
    Function.Injective (chartSobolevInclusion he ψ h) := fun x y hxy ↦ by
  ext1
  ext1 i
  refine BesselPotentialSpace.inclusion_injective h ?_
  simpa using congrArg (fun z : chartSobolevSpace he ψ r ↦
    (z : PiLp 2 fun _ : ι ↦ H^{r}(CoordinateSpace n)) i) hxy

/-- The inclusion `H^s(M) ⊆ H^r(M)` has dense range: its range contains the smooth functions. -/
theorem denseRange_chartSobolevInclusion (h : r ≤ s) :
    DenseRange (chartSobolevInclusion he ψ h) :=
  .of_comp (g := toChartSobolevSpace he ψ s) <| by
    convert denseRange_toChartSobolevSpace he ψ r using 1
    ext1 u
    exact chartSobolevInclusion_toChartSobolevSpace he ψ h u

/-! ### The Rellich theorem -/

/-- **Elements of `H^s(M)` are fixed by cutoffs equal to one on the chart supports.** If a Schwartz
function `θ` equals `1` on the support of `ψᵢ`, then multiplication by `θ` fixes the `i`-th
component of every element of `H^s(M)`: it fixes the reading `ψᵢ · (u ∘ eᵢ⁻¹)` of every smooth
`u`, and these are dense. -/
theorem smulLeftCLM_chartSobolevSpace_apply_of_eqOn_one {θ : 𝓢(CoordinateSpace n, ℂ)} {i : ι}
    (hθ : EqOn θ 1 (tsupport (ψ i))) (x : chartSobolevSpace he ψ s) :
    BesselPotentialSpace.smulLeftCLM s θ ((x : PiLp 2 fun _ : ι ↦ H^{s}(CoordinateSpace n)) i) =
      (x : PiLp 2 fun _ : ι ↦ H^{s}(CoordinateSpace n)) i := by
  have hclosed : IsClosed {y : PiLp 2 fun _ : ι ↦ H^{s}(CoordinateSpace n) |
      BesselPotentialSpace.smulLeftCLM s θ (y i) = y i} :=
    isClosed_eq (by fun_prop) (by fun_prop)
  refine closure_minimal ?_ hclosed ((mem_chartSobolevSpace_iff he ψ).1 x.property)
  rintro _ ⟨u, rfl⟩
  refine BesselPotentialSpace.ext ?_
  rw [BesselPotentialSpace.toDistr_smulLeftCLM, chartReading_apply,
    SchwartzMap.toDistr_toBesselPotentialSpaceCLM,
    TemperedDistribution.smulLeftCLM_toTemperedDistributionCLM_eq]
  congr 1
  ext y
  rw [SchwartzMap.smulLeftCLM_apply_apply θ.hasTemperateGrowth, cutoffPushforwardSchwartz_apply]
  by_cases hy : ψ i y = 0
  · simp [hy]
  · rw [hθ (subset_tsupport _ hy), Pi.one_apply, one_smul]

/-- **The Rellich theorem.** For real orders `r < s`, the inclusion `H^s(M) ⊆ H^r(M)` is a compact
operator. -/
theorem isCompactOperator_chartSobolevInclusion (h : r < s) :
    IsCompactOperator (chartSobolevInclusion he ψ h.le) := by
  -- A Schwartz function `θ` equal to `1` on the finitely many compact supports of the `ψᵢ`.
  obtain ⟨θ, -, -, hθ1⟩ := (isCompact_iUnion fun i ↦
    (ψ i).hasCompactSupport.isCompact).exists_schwartzMap_cutoff isOpen_univ (subset_univ _)
  exact BesselPotentialSpace.isCompactOperator_piLp_of_smulLeftCLM_eq θ h
    (i := Subtype.val) continuous_subtypeVal rfl
    (isClosed_chartSobolevSpace he ψ r).isClosedEmbedding_subtypeVal
    (fun x i ↦ smulLeftCLM_chartSobolevSpace_apply_of_eqOn_one he ψ
      (fun y hy ↦ hθ1.self_of_nhdsSet y (mem_iUnion_of_mem i hy)) x)
    (coe_chartSobolevInclusion_apply he ψ h.le)

/-! ### Extending operators by continuity -/

variable {κ : Type*} [Fintype κ] {e' : κ → OpenPartialHomeomorph M (CoordinateSpace n)}
  (he' : ∀ j, e' j ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
  (φ : ∀ j, 𝓓(⟨(e' j).target, (e' j).open_target⟩, ℝ))

/-- The **extension of an operator** `P` on smooth functions to a continuous linear map
`H^s(M) → H^t(M)`, from the Sobolev space of the cutoffs `ψᵢ` in the charts `eᵢ` to that of the
cutoffs `φⱼ` in the charts `e'ⱼ`, by continuity from the dense smooth functions
(`LinearMap.extendOfNorm`). It extends `P` exactly when `P` satisfies an a priori estimate
`‖P u‖_{H^t} ≤ C ‖u‖_{H^s}` in the chart-reading norms
(`TauCeti.chartSobolevExtension_toChartSobolevSpace`), and it is then the unique continuous
extension (`TauCeti.chartSobolevExtension_eq`). -/
def chartSobolevExtension (P : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
      C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) (s t : ℝ) :
    chartSobolevSpace he ψ s →L[ℂ] chartSobolevSpace he' φ t :=
  (toChartSobolevSpace he' φ t ∘ₗ P).extendOfNorm (toChartSobolevSpace he ψ s)

variable {he ψ he' φ} {P : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
  C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯} {s t : ℝ}

/-- An operator satisfying an a priori estimate `‖P u‖_{H^t} ≤ C ‖u‖_{H^s}` in the chart-reading
norms is extended by `TauCeti.chartSobolevExtension`. -/
theorem chartSobolevExtension_toChartSobolevSpace
    (hP : ∃ C, ∀ u, ‖chartReading he' φ t (P u)‖ ≤ C * ‖chartReading he ψ s u‖)
    (u : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) :
    chartSobolevExtension he ψ he' φ P s t (toChartSobolevSpace he ψ s u) =
      toChartSobolevSpace he' φ t (P u) :=
  LinearMap.extendOfNorm_eq (denseRange_toChartSobolevSpace he ψ s) (by simpa using hP) u

/-- The a priori estimate `‖P u‖_{H^t} ≤ C ‖u‖_{H^s}` on smooth functions persists for the
extension of `P` to `H^s(M)`. -/
theorem norm_chartSobolevExtension_apply_le {C : ℝ}
    (hP : ∀ u, ‖chartReading he' φ t (P u)‖ ≤ C * ‖chartReading he ψ s u‖)
    (x : chartSobolevSpace he ψ s) : ‖chartSobolevExtension he ψ he' φ P s t x‖ ≤ C * ‖x‖ :=
  LinearMap.norm_extendOfNorm_apply_le (denseRange_toChartSobolevSpace he ψ s) C (by simpa using hP)
    x

/-- **Uniqueness of the extension.** A continuous linear map `H^s(M) → H^t(M)` that agrees with
`P` on smooth functions is the extension of `P`. No estimate is assumed: the continuity of `L`
provides it. -/
theorem chartSobolevExtension_eq (L : chartSobolevSpace he ψ s →L[ℂ] chartSobolevSpace he' φ t)
    (hL : ∀ u, L (toChartSobolevSpace he ψ s u) = toChartSobolevSpace he' φ t (P u)) :
    chartSobolevExtension he ψ he' φ P s t = L :=
  LinearMap.extendOfNorm_unique (denseRange_toChartSobolevSpace he ψ s) ‖L‖
    (fun u ↦ by simpa only [LinearMap.comp_apply, ← hL] using L.le_opNorm _) L (LinearMap.ext hL)

/-- The extension of the identity is the inclusion `H^s(M) ⊆ H^r(M)`. -/
theorem chartSobolevExtension_id {r : ℝ} (h : r ≤ s) :
    chartSobolevExtension he ψ he ψ LinearMap.id s r = chartSobolevInclusion he ψ h :=
  chartSobolevExtension_eq _ fun u ↦ chartSobolevInclusion_toChartSobolevSpace he ψ h u

/-- The extension of the identity from `H^s(M)` to itself is the identity. -/
@[simp]
theorem chartSobolevExtension_id_self :
    chartSobolevExtension he ψ he ψ LinearMap.id s s = 1 :=
  chartSobolevExtension_eq _ fun _ ↦ rfl

/-- Following the extension of `P` to `H^s(M) → H^t(M)` by the inclusion `H^t(M) ⊆ H^r(M)` gives
the extension of `P` to `H^s(M) → H^r(M)`. -/
theorem chartSobolevInclusion_comp_chartSobolevExtension {r : ℝ} (h : r ≤ t)
    (hP : ∃ C, ∀ u, ‖chartReading he' φ t (P u)‖ ≤ C * ‖chartReading he ψ s u‖) :
    chartSobolevInclusion he' φ h ∘L chartSobolevExtension he ψ he' φ P s t =
      chartSobolevExtension he ψ he' φ P s r :=
  (chartSobolevExtension_eq _ fun u ↦ by
    rw [ContinuousLinearMap.comp_apply, chartSobolevExtension_toChartSobolevSpace hP,
      chartSobolevInclusion_toChartSobolevSpace]).symm

/-- Precomposing the extension of `P` to `H^s(M) → H^t(M)` with the inclusion `H^r(M) ⊆ H^s(M)`
gives the extension of `P` to `H^r(M) → H^t(M)`. -/
theorem chartSobolevExtension_comp_chartSobolevInclusion {r : ℝ} (h : s ≤ r)
    (hP : ∃ C, ∀ u, ‖chartReading he' φ t (P u)‖ ≤ C * ‖chartReading he ψ s u‖) :
    chartSobolevExtension he ψ he' φ P s t ∘L chartSobolevInclusion he ψ h =
      chartSobolevExtension he ψ he' φ P r t :=
  (chartSobolevExtension_eq _ fun u ↦ by
    rw [ContinuousLinearMap.comp_apply, chartSobolevInclusion_toChartSobolevSpace,
      chartSobolevExtension_toChartSobolevSpace hP]).symm

/-- The extension of a sum of operators satisfying a priori estimates is the sum of their
extensions. -/
theorem chartSobolevExtension_add {Q : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
      C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯}
    (hP : ∃ C, ∀ u, ‖chartReading he' φ t (P u)‖ ≤ C * ‖chartReading he ψ s u‖)
    (hQ : ∃ C, ∀ u, ‖chartReading he' φ t (Q u)‖ ≤ C * ‖chartReading he ψ s u‖) :
    chartSobolevExtension he ψ he' φ (P + Q) s t =
      chartSobolevExtension he ψ he' φ P s t + chartSobolevExtension he ψ he' φ Q s t :=
  chartSobolevExtension_eq _ fun u ↦ by
    simp [chartSobolevExtension_toChartSobolevSpace hP,
      chartSobolevExtension_toChartSobolevSpace hQ]

/-- The extension of a difference of operators satisfying a priori estimates is the difference of
their extensions. -/
theorem chartSobolevExtension_sub {Q : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
      C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯}
    (hP : ∃ C, ∀ u, ‖chartReading he' φ t (P u)‖ ≤ C * ‖chartReading he ψ s u‖)
    (hQ : ∃ C, ∀ u, ‖chartReading he' φ t (Q u)‖ ≤ C * ‖chartReading he ψ s u‖) :
    chartSobolevExtension he ψ he' φ (P - Q) s t =
      chartSobolevExtension he ψ he' φ P s t - chartSobolevExtension he ψ he' φ Q s t :=
  chartSobolevExtension_eq _ fun u ↦ by
    simp [chartSobolevExtension_toChartSobolevSpace hP,
      chartSobolevExtension_toChartSobolevSpace hQ]

/-- The extension of a scalar multiple of an operator satisfying an a priori estimate is the
scalar multiple of its extension. -/
theorem chartSobolevExtension_smul (a : ℂ)
    (hP : ∃ C, ∀ u, ‖chartReading he' φ t (P u)‖ ≤ C * ‖chartReading he ψ s u‖) :
    chartSobolevExtension he ψ he' φ (a • P) s t = a • chartSobolevExtension he ψ he' φ P s t :=
  chartSobolevExtension_eq _ fun u ↦ by simp [chartSobolevExtension_toChartSobolevSpace hP]

/-- **The extension of a composition** is the composition of the extensions, when both operators
satisfy a priori estimates. -/
theorem chartSobolevExtension_comp {ν : Type*} [Fintype ν]
    {e'' : ν → OpenPartialHomeomorph M (CoordinateSpace n)}
    {he'' : ∀ k, e'' k ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M}
    {χ : ∀ k, 𝓓(⟨(e'' k).target, (e'' k).open_target⟩, ℝ)}
    {Q : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
      C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯} {r : ℝ}
    (hP : ∃ C, ∀ u, ‖chartReading he'' χ r (P u)‖ ≤ C * ‖chartReading he' φ t u‖)
    (hQ : ∃ C, ∀ u, ‖chartReading he' φ t (Q u)‖ ≤ C * ‖chartReading he ψ s u‖) :
    chartSobolevExtension he' φ he'' χ P t r ∘L chartSobolevExtension he ψ he' φ Q s t =
      chartSobolevExtension he ψ he'' χ (P ∘ₗ Q) s r :=
  (chartSobolevExtension_eq _ fun u ↦ by
    rw [ContinuousLinearMap.comp_apply, chartSobolevExtension_toChartSobolevSpace hQ,
      chartSobolevExtension_toChartSobolevSpace hP, LinearMap.comp_apply]).symm

/-! ### Changing the charts -/

variable (he ψ he' φ) [T2Space M]

/-- **Chart readings are controlled by those in a chart partition.** If the readings `ψᵢ ∘ eᵢ` of
the cutoffs `ψᵢ` on `M`, extended by `0`, add up to `1`, then for any finitely many cutoffs `φⱼ` in
charts `e'ⱼ` there is a constant `C` such that every smooth `u` on `M` satisfies

`‖(φⱼ · (u ∘ e'ⱼ⁻¹))ⱼ‖_{⨁ H^s} ≤ C ‖(ψᵢ · (u ∘ eᵢ⁻¹))ᵢ‖_{⨁ H^s}`. -/
theorem exists_norm_chartReading_le
    (hψ : ∀ x, ∑ i, (e i).cutoffPullback (he i) (ψ i) 1 x = 1) (s : ℝ) :
    ∃ C, ∀ u, ‖chartReading he' φ s u‖ ≤ C * ‖chartReading he ψ s u‖ := by
  choose C hC using fun j i ↦
    exists_norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_mulLeft_le (he' j) (he i)
      (φ j) (ψ i) ENNReal.one_lt_two ENNReal.ofNat_ne_top s
  refine ⟨∑ j, ∑ i, |C j i|, fun u ↦ ?_⟩
  -- `u = ∑ᵢ Ψᵢ u`, and each piece is read again in every chart `e'ⱼ`.
  have hu : u = ∑ i, LinearMap.mulLeft ℂ (ContMDiffMap.ofReal ((e i).cutoffPullback (he i) (ψ i) 1))
      u := ContMDiffMap.eq_sum_mulLeft_ofReal _ _ (subset_univ _) fun x _ ↦ hψ x
  have hj (j : κ) : ‖chartReading he' φ s u j‖ ≤ (∑ i, |C j i|) * ‖chartReading he ψ s u‖ := by
    rw [chartReading_apply]
    conv_lhs => rw [hu, map_sum, map_sum]
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ (hC j i u).trans ?_)
    exact mul_le_mul (le_abs_self _) (PiLp.norm_apply_le (chartReading he ψ s u) i)
      (norm_nonneg _) (abs_nonneg _)
  calc ‖chartReading he' φ s u‖
      ≤ ∑ j, ‖chartReading he' φ s u j‖ := PiLp.norm_le_sum_norm _
    _ ≤ ∑ j, (∑ i, |C j i|) * ‖chartReading he ψ s u‖ := Finset.sum_le_sum fun j _ ↦ hj j
    _ = (∑ j, ∑ i, |C j i|) * ‖chartReading he ψ s u‖ := (Finset.sum_mul ..).symm

/-- **Independence of the charts.** The Sobolev spaces `H^s(M)` of two chart partitions, whose
cutoffs read on `M` add up to `1`, are isomorphic Banach spaces, through the isomorphism that is
the identity on smooth functions (`TauCeti.chartSobolevSpaceCongr_toChartSobolevSpace`). -/
def chartSobolevSpaceCongr
    (hψ : ∀ x, ∑ i, (e i).cutoffPullback (he i) (ψ i) 1 x = 1)
    (hφ : ∀ x, ∑ j, (e' j).cutoffPullback (he' j) (φ j) 1 x = 1) (s : ℝ) :
    chartSobolevSpace he ψ s ≃L[ℂ] chartSobolevSpace he' φ s :=
  (LinearEquiv.refl ℂ C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯).extend
    (toChartSobolevSpace he ψ s) (toChartSobolevSpace he' φ s)
    (denseRange_toChartSobolevSpace he ψ s)
    (by simpa using exists_norm_chartReading_le he ψ he' φ hψ s)
    (denseRange_toChartSobolevSpace he' φ s)
    (by simpa using exists_norm_chartReading_le he' φ he ψ hφ s)

@[simp]
theorem chartSobolevSpaceCongr_toChartSobolevSpace
    (hψ : ∀ x, ∑ i, (e i).cutoffPullback (he i) (ψ i) 1 x = 1)
    (hφ : ∀ x, ∑ j, (e' j).cutoffPullback (he' j) (φ j) 1 x = 1) (s : ℝ)
    (u : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) :
    chartSobolevSpaceCongr he ψ he' φ hψ hφ s (toChartSobolevSpace he ψ s u) =
      toChartSobolevSpace he' φ s u := by
  rw [chartSobolevSpaceCongr, LinearEquiv.extend_eq, LinearEquiv.refl_apply]

@[simp]
theorem chartSobolevSpaceCongr_symm_toChartSobolevSpace
    (hψ : ∀ x, ∑ i, (e i).cutoffPullback (he i) (ψ i) 1 x = 1)
    (hφ : ∀ x, ∑ j, (e' j).cutoffPullback (he' j) (φ j) 1 x = 1) (s : ℝ)
    (u : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) :
    (chartSobolevSpaceCongr he ψ he' φ hψ hφ s).symm (toChartSobolevSpace he' φ s u) =
      toChartSobolevSpace he ψ s u := by
  rw [chartSobolevSpaceCongr, LinearEquiv.extend_symm_eq, LinearEquiv.refl_symm,
    LinearEquiv.refl_apply]

variable {he ψ he' φ} in
/-- **The extension of an operator does not depend on the chart partitions.** Let `P` satisfy an a
priori estimate `‖P u‖_{H^t} ≤ C ‖u‖_{H^s}` in the chart readings of the partitions `ψ` and `φ`.
Its extension between the spaces of two other chart partitions `ψ₂` and `φ₂` is its extension
between those of `ψ` and `φ`, transported along the isomorphisms `TauCeti.chartSobolevSpaceCongr`.
-/
theorem chartSobolevExtension_eq_chartSobolevSpaceCongr_comp {ι₂ κ₂ : Type*} [Fintype ι₂]
    [Fintype κ₂] {e₂ : ι₂ → OpenPartialHomeomorph M (CoordinateSpace n)}
    {he₂ : ∀ i, e₂ i ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M}
    {ψ₂ : ∀ i, 𝓓(⟨(e₂ i).target, (e₂ i).open_target⟩, ℝ)}
    {e₂' : κ₂ → OpenPartialHomeomorph M (CoordinateSpace n)}
    {he₂' : ∀ j, e₂' j ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M}
    {φ₂ : ∀ j, 𝓓(⟨(e₂' j).target, (e₂' j).open_target⟩, ℝ)}
    (hψ : ∀ x, ∑ i, (e i).cutoffPullback (he i) (ψ i) 1 x = 1)
    (hψ₂ : ∀ x, ∑ i, (e₂ i).cutoffPullback (he₂ i) (ψ₂ i) 1 x = 1)
    (hφ : ∀ x, ∑ j, (e' j).cutoffPullback (he' j) (φ j) 1 x = 1)
    (hφ₂ : ∀ x, ∑ j, (e₂' j).cutoffPullback (he₂' j) (φ₂ j) 1 x = 1)
    {P : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
      C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯} {s t : ℝ}
    (hP : ∃ C, ∀ u, ‖chartReading he' φ t (P u)‖ ≤ C * ‖chartReading he ψ s u‖) :
    chartSobolevExtension he₂ ψ₂ he₂' φ₂ P s t =
      (chartSobolevSpaceCongr he' φ he₂' φ₂ hφ hφ₂ t : _ →L[ℂ] _) ∘L
        chartSobolevExtension he ψ he' φ P s t ∘L
          ((chartSobolevSpaceCongr he ψ he₂ ψ₂ hψ hψ₂ s).symm : _ →L[ℂ] _) :=
  chartSobolevExtension_eq _ fun u ↦ by
    simp [chartSobolevExtension_toChartSobolevSpace hP]

end TauCeti
