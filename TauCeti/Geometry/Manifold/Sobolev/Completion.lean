/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import TauCeti.Analysis.Normed.Lp.PiLp.Basic
public import TauCeti.Analysis.Normed.Operator.RangeClosure
public import TauCeti.Analysis.Sobolev.BesselPotential.Inclusion
public import TauCeti.Geometry.Manifold.DifferentialOperator.ChartCompression.Schwartz
import TauCeti.Analysis.Distribution.SchwartzSpace.Cutoff
import TauCeti.Analysis.Distribution.TemperedDistribution.SmulLeft
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.Sobolev.BesselPotential.Rellich.Basic
import TauCeti.Geometry.Manifold.Sobolev.ChartReading

/-!
# Sobolev spaces of a compact manifold as completions of smooth functions

Let `M` be a manifold modelled on `ℝⁿ`, and let `ψᵢ` be finitely many cutoffs in charts `eᵢ` of the
maximal atlas. A complex-valued smooth function `u` on `M` is read in the `i`-th chart as the
Schwartz function `ψᵢ · (u ∘ eᵢ⁻¹)` (`OpenPartialHomeomorph.cutoffPushforwardSchwartz`). For a real
order `s`, the **chart readings** of `u` are the tuple of these readings in the Hilbert sum
`⨁ᵢ H^s(ℝⁿ)` (`TauCeti.chartReading`), whose norm is `(∑ᵢ ‖ψᵢ · (u ∘ eᵢ⁻¹)‖²_{H^s})^{1/2}`.

The **Sobolev space** `H^s(M)` of the family is the closure of the chart readings of all smooth
functions (`TauCeti.chartSobolevSpace`), an instance of the closure of the range of a linear map
(`LinearMap.rangeClosure`): a closed subspace of `⨁ᵢ H^s(ℝⁿ)`, hence a Hilbert space, in which the
smooth functions are dense (`LinearMap.denseRange_toRangeClosure`). For a chart partition of a
compact manifold it is the completion of the smooth functions in the norm through which Taylor
defines the Sobolev spaces of a compact manifold. A continuous linear map out of it is determined
by its values on smooth functions (`LinearMap.rangeClosure_ext`). This is the space on which
operators defined on smooth functions, such as pseudodifferential operators, act once they satisfy
an a priori estimate in the chart-reading norms (`TauCeti.chartSobolevExtension`, an instance of
`LinearMap.rangeClosureExtension`); the extension is unique, and extensions compose.

* For `r ≤ s`, the inclusions `H^s(ℝⁿ) ⊆ H^r(ℝⁿ)` give the inclusion `H^s(M) ⊆ H^r(M)`
  (`TauCeti.chartSobolevInclusion`), which restricts to the identity on smooth functions. It is
  injective (`TauCeti.chartSobolevInclusion_injective`) with dense range
  (`LinearMap.denseRange_rangeClosureMap`), and it commutes with the extensions of operators
  (`LinearMap.rangeClosureMap_comp_rangeClosureExtension`,
  `LinearMap.rangeClosureExtension_comp_rangeClosureMap`).
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
  (`TauCeti.isCompactOperator_chartSobolevInclusion`). Every chart reading `ψᵢ · (u ∘ eᵢ⁻¹)` is
  fixed by a Schwartz function equal to `1` on the support of its cutoff
  (`TauCeti.smulLeftCLM_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz`), so componentwise
  the inclusion is multiplication by that function, compact by the Euclidean Rellich theorem for a
  common compact support in a finite Hilbert sum
  (`BesselPotentialSpace.isCompactOperator_rangeClosureMap_piMap_inclusion`).
* **Charts.** A single chart `c` with a cutoff `χ` localizes in both directions: the reading
  `u ↦ χ · (u ∘ c⁻¹)` extends to `H^s(M) → H^s(ℝⁿ)` for a chart partition
  (`TauCeti.chartSobolevReading`), and the pullback `u ↦ (χ u) ∘ c` of Schwartz functions extends
  to `H^s(ℝⁿ) → H^s(M)` (`TauCeti.chartSobolevPullback`). Through them an operator on `H^s(M)` is
  compared with its chart compressions on `ℝⁿ`.

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
* `TauCeti.chartSobolevReading`: the reading `H^s(M) → H^s(ℝⁿ)` in a chart through a cutoff.
* `TauCeti.chartSobolevPullback`: the pullback `H^s(ℝⁿ) → H^s(M)` through a cutoff in a chart.

## Main results

* `TauCeti.toChartSobolevSpace_injective`: for a chart partition, a smooth function is determined
  by its element of `H^s(M)`.
* `TauCeti.isCompactOperator_chartSobolevInclusion`: the Rellich theorem, `H^s(M) ⊆ H^r(M)` is
  compact for `r < s`.
* `TauCeti.chartSobolevInclusion_injective`: the inclusion `H^s(M) ⊆ H^r(M)` is injective.
* `TauCeti.chartSobolevExtension_eq_chartSobolevSpaceCongr_comp`: the extension of an operator does
  not depend on the chart partitions.
* `TauCeti.exists_norm_chartReading_le`: chart readings in any family of charts are bounded by
  those in a chart partition.
* `TauCeti.exists_norm_chartReading_complexCutoffPullback_le`: the chart readings of `(χ u) ∘ c`
  are bounded by the `H^s` norm of the Schwartz function `u`.

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

/-- The componentwise inclusion `⨁ᵢ H^s(ℝⁿ) ⊆ ⨁ᵢ H^r(ℝⁿ)` sends the chart readings of order `s`
to those of order `r`. -/
theorem piMap_inclusion_chartReading {r s : ℝ} (h : r ≤ s)
    (u : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) :
    PiLp.piMap 2 (fun _ ↦ BesselPotentialSpace.inclusion h) (chartReading he ψ s u) =
      chartReading he ψ r u := by
  ext1 i
  simp

variable [Fintype ι]

/-- The **Sobolev space** `H^s(M)` of the charts `eᵢ` and cutoffs `ψᵢ`: the closure in the Hilbert
sum `⨁ᵢ H^s(ℝⁿ)` of the chart readings of the smooth functions on `M` (`LinearMap.rangeClosure`).
It is closed, hence a Hilbert space. -/
abbrev chartSobolevSpace (s : ℝ) : Submodule ℂ (PiLp 2 fun _ : ι ↦ H^{s}(CoordinateSpace n)) :=
  (chartReading he ψ s).rangeClosure

/-- A smooth function `u` on `M` as an element of the Sobolev space `H^s(M)`: its chart
readings. Smooth functions are dense in `H^s(M)` (`LinearMap.denseRange_toRangeClosure`). -/
abbrev toChartSobolevSpace (s : ℝ) :
    C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ] chartSobolevSpace he ψ s :=
  (chartReading he ψ s).toRangeClosure

/-! ### The inclusions between the Sobolev spaces -/

variable {r s : ℝ}

/-- The inclusion `H^s(M) ⊆ H^r(M)` for `r ≤ s`: the inclusion `H^s(ℝⁿ) ⊆ H^r(ℝⁿ)`
(`BesselPotentialSpace.inclusion`) in every component, which sends the chart readings of order `s`
of a smooth function to those of order `r` (`TauCeti.piMap_inclusion_chartReading`). -/
abbrev chartSobolevInclusion (h : r ≤ s) :
    chartSobolevSpace he ψ s →L[ℂ] chartSobolevSpace he ψ r :=
  (chartReading he ψ s).rangeClosureMap (chartReading he ψ r)
    (PiLp.piMap 2 fun _ ↦ BesselPotentialSpace.inclusion h) (piMap_inclusion_chartReading he ψ h)

/-- The inclusion `H^s(M) ⊆ H^r(M)` does not increase norms. -/
theorem norm_chartSobolevInclusion_apply_le (h : r ≤ s) (x : chartSobolevSpace he ψ s) :
    ‖chartSobolevInclusion he ψ h x‖ ≤ ‖x‖ := by
  simpa only [one_mul] using (chartSobolevInclusion he ψ h).le_of_opNorm_le
    ((LinearMap.norm_rangeClosureMap_le _).trans
      (PiLp.norm_piMap_le zero_le_one fun _ ↦ BesselPotentialSpace.norm_inclusion_le h)) x

/-- The inclusion `H^s(M) ⊆ H^s(M)` is the identity. -/
@[simp]
theorem chartSobolevInclusion_self : chartSobolevInclusion he ψ (le_refl s) = 1 :=
  LinearMap.rangeClosure_ext _ fun u ↦ by simp

/-- The inclusions `H^s(M) ⊆ H^r(M) ⊆ H^t(M)` compose to the inclusion `H^s(M) ⊆ H^t(M)`. -/
@[simp]
theorem chartSobolevInclusion_comp_chartSobolevInclusion {t : ℝ} (h₁ : r ≤ s) (h₂ : t ≤ r) :
    chartSobolevInclusion he ψ h₂ ∘L chartSobolevInclusion he ψ h₁ =
      chartSobolevInclusion he ψ (h₂.trans h₁) :=
  LinearMap.rangeClosure_ext _ fun u ↦ by simp

/-- The inclusion `H^s(M) ⊆ H^r(M)` is injective. -/
theorem chartSobolevInclusion_injective (h : r ≤ s) :
    Function.Injective (chartSobolevInclusion he ψ h) :=
  LinearMap.rangeClosureMap_injective _
    (PiLp.piMap_injective 2 fun _ ↦ BesselPotentialSpace.inclusion_injective h)

/-! ### The Rellich theorem -/

/-- **The Rellich theorem.** For real orders `r < s`, the inclusion `H^s(M) ⊆ H^r(M)` is a compact
operator. -/
theorem isCompactOperator_chartSobolevInclusion (h : r < s) :
    IsCompactOperator (chartSobolevInclusion he ψ h.le) := by
  -- A Schwartz function `θ` equal to `1` on the finitely many compact supports of the `ψᵢ`.
  obtain ⟨θ, -, -, hθ1⟩ := (isCompact_iUnion fun i ↦
    (ψ i).hasCompactSupport.isCompact).exists_schwartzMap_cutoff isOpen_univ (subset_univ _)
  exact BesselPotentialSpace.isCompactOperator_rangeClosureMap_piMap_inclusion θ h
    (fun u i ↦ smulLeftCLM_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz (he i)
      (fun y hy ↦ hθ1.self_of_nhdsSet y (mem_iUnion_of_mem i hy)) s u)
    (piMap_inclusion_chartReading he ψ h.le)

/-! ### Extending operators by continuity -/

variable {κ : Type*} [Fintype κ] {e' : κ → OpenPartialHomeomorph M (CoordinateSpace n)}
  (he' : ∀ j, e' j ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
  (φ : ∀ j, 𝓓(⟨(e' j).target, (e' j).open_target⟩, ℝ))

/-- The **extension of an operator** `P` on smooth functions to a continuous linear map
`H^s(M) → H^t(M)`, from the Sobolev space of the cutoffs `ψᵢ` in the charts `eᵢ` to that of the
cutoffs `φⱼ` in the charts `e'ⱼ`, by continuity from the dense smooth functions
(`LinearMap.rangeClosureExtension`). It extends `P` exactly when `P` satisfies an a priori
estimate `‖P u‖_{H^t} ≤ C ‖u‖_{H^s}` in the chart-reading norms
(`LinearMap.rangeClosureExtension_toRangeClosure`), and it is then the unique continuous extension
(`LinearMap.rangeClosureExtension_eq`); extensions add and compose. -/
abbrev chartSobolevExtension (P : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
      C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) (s t : ℝ) :
    chartSobolevSpace he ψ s →L[ℂ] chartSobolevSpace he' φ t :=
  (chartReading he ψ s).rangeClosureExtension (chartReading he' φ t) P

/-! ### Changing the charts -/

variable [T2Space M]

/-- **A smooth function is determined by its element of `H^s(M)`** when the readings `ψᵢ ∘ eᵢ` of
the cutoffs on `M`, extended by `0`, add up to `1`: its readings `ψᵢ · (u ∘ eᵢ⁻¹)` are then its
components, and they determine `u`. -/
theorem toChartSobolevSpace_injective
    (hψ : ∀ x, ∑ i, (e i).cutoffPullback (he i) (ψ i) 1 x = 1) (s : ℝ) :
    Function.Injective (toChartSobolevSpace he ψ s) := by
  refine (injective_iff_map_eq_zero _).2 fun u hu ↦
    eq_zero_of_forall_cutoffPushforwardSchwartz_eq_zero he ψ hψ fun i ↦ ?_
  refine SchwartzMap.toBesselPotentialSpaceCLM_injective s 2 ?_
  rw [map_zero, ← chartReading_apply, ← LinearMap.coe_toRangeClosure, hu, ZeroMemClass.coe_zero,
    PiLp.zero_apply]

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
the identity on smooth functions (`LinearMap.rangeClosureCongr_toRangeClosure`). -/
abbrev chartSobolevSpaceCongr
    (hψ : ∀ x, ∑ i, (e i).cutoffPullback (he i) (ψ i) 1 x = 1)
    (hφ : ∀ x, ∑ j, (e' j).cutoffPullback (he' j) (φ j) 1 x = 1) (s : ℝ) :
    chartSobolevSpace he ψ s ≃L[ℂ] chartSobolevSpace he' φ s :=
  (chartReading he ψ s).rangeClosureCongr (chartReading he' φ s)
    (exists_norm_chartReading_le he ψ he' φ hψ s) (exists_norm_chartReading_le he' φ he ψ hφ s)

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
  LinearMap.rangeClosureExtension_eq _ fun u ↦ by
    simp [LinearMap.rangeClosureExtension_toRangeClosure hP]

/-! ### Reading in a chart and pulling back from a chart -/

section Chart

variable {c : OpenPartialHomeomorph M (CoordinateSpace n)}
  (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
  (χ : 𝓓(⟨c.target, c.open_target⟩, ℝ))

/-- **Reading an element of `H^s(M)` in a chart.** The continuous linear map
`H^s(M) → H^s(ℝⁿ)` extending the reading `u ↦ χ · (u ∘ c⁻¹)` of smooth functions in a chart `c`
through a cutoff `χ`. It extends the reading when the readings `ψᵢ ∘ eᵢ` of the cutoffs defining
`H^s(M)` add up to `1` (`TauCeti.chartSobolevReading_toChartSobolevSpace`). -/
def chartSobolevReading (s : ℝ) : chartSobolevSpace he ψ s →L[ℂ] H^{s}(CoordinateSpace n) :=
  ((SchwartzMap.toBesselPotentialSpaceCLM s 2).toLinearMap ∘ₗ
    c.cutoffPushforwardSchwartz hc χ).extendOfNorm (toChartSobolevSpace he ψ s)

/-- For a chart partition, the reading of `H^s(M)` in the chart `c` through the cutoff `χ` sends a
smooth function `u` to its reading `χ · (u ∘ c⁻¹)`. -/
@[simp]
theorem chartSobolevReading_toChartSobolevSpace
    (hψ : ∀ x, ∑ i, (e i).cutoffPullback (he i) (ψ i) 1 x = 1) (s : ℝ)
    (u : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) :
    chartSobolevReading he ψ hc χ s (toChartSobolevSpace he ψ s u) =
      SchwartzMap.toBesselPotentialSpaceCLM s 2 (c.cutoffPushforwardSchwartz hc χ u) := by
  obtain ⟨C, hC⟩ := exists_norm_chartReading_le he ψ (fun _ : Unit ↦ hc) (fun _ ↦ χ) hψ s
  have hle (v : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) :
      ‖SchwartzMap.toBesselPotentialSpaceCLM s 2 (c.cutoffPushforwardSchwartz hc χ v)‖ ≤
        C * ‖toChartSobolevSpace he ψ s v‖ := by
    rw [LinearMap.norm_toRangeClosure, ← chartReading_apply (fun _ : Unit ↦ hc) (fun _ ↦ χ) s v ()]
    exact (PiLp.norm_apply_le _ ()).trans (hC v)
  exact LinearMap.extendOfNorm_eq (e := toChartSobolevSpace he ψ s)
    (f := (SchwartzMap.toBesselPotentialSpaceCLM s 2).toLinearMap ∘ₗ
      c.cutoffPushforwardSchwartz hc χ)
    (LinearMap.denseRange_toRangeClosure _) ⟨C, hle⟩ u

/-- **The readings of a function pulled back from a chart.** For a cutoff `χ` in a chart `c` and
every real `s` there is a constant `C` such that for every Schwartz function `u`, the smooth
function `(χ u) ∘ c` on `M`, extended by `0`, has chart readings

`‖(ψᵢ · (((χ u) ∘ c) ∘ eᵢ⁻¹))ᵢ‖_{⨁ H^s} ≤ C ‖u‖_{H^s}`. -/
theorem exists_norm_chartReading_complexCutoffPullback_le (s : ℝ) :
    ∃ C, ∀ u : 𝓢(CoordinateSpace n, ℂ),
      ‖chartReading he ψ s
          (c.complexCutoffPullback hc χ (ContMDiffMap.ofContDiff u (u.smooth ⊤)))‖ ≤
        C * ‖SchwartzMap.toBesselPotentialSpaceCLM s 2 u‖ := by
  -- A cutoff `χ₁` equal to `1` near the support of `χ`, so that `(χ u) ∘ c` is `χ ∘ c` times
  -- `(χ₁ u) ∘ c`, whose reading in `c` through `χ` is `χ u`.
  obtain ⟨χ₁, hχ₁, -⟩ := TestFunction.exists_eventually_eq_one (Ω := ⟨c.target, c.open_target⟩)
    (n := ⊤) χ.hasCompactSupport.isCompact χ.tsupport_subset
  obtain ⟨θ, hθ⟩ : ∃ θ : 𝓢(CoordinateSpace n, ℂ), ∀ y, θ y = χ y :=
    ⟨(χ.hasCompactSupport.comp_left Complex.ofReal_zero).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp χ.contDiff), HasCompactSupport.toSchwartzMap_toFun _ _⟩
  choose C hC using fun i ↦
    exists_norm_toBesselPotentialSpaceCLM_cutoffPushforwardSchwartz_mulLeft_le (he i) hc (ψ i) χ
      ENNReal.one_lt_two ENNReal.ofNat_ne_top s
  refine ⟨(∑ i, |C i|) * ‖BesselPotentialSpace.smulLeftCLM (F := ℂ) s θ‖, fun u ↦ ?_⟩
  set U := ContMDiffMap.ofContDiff u (u.smooth ⊤)
  have h1 : ∀ y ∈ tsupport χ, χ₁ y = 1 := fun y hy ↦ hχ₁.self_of_nhdsSet y hy
  have hread : SchwartzMap.toBesselPotentialSpaceCLM s 2
      (c.cutoffPushforwardSchwartz hc χ (c.complexCutoffPullback hc χ₁ U)) =
        BesselPotentialSpace.smulLeftCLM s θ (SchwartzMap.toBesselPotentialSpaceCLM s 2 u) := by
    refine BesselPotentialSpace.ext ?_
    rw [BesselPotentialSpace.toDistr_smulLeftCLM, SchwartzMap.toDistr_toBesselPotentialSpaceCLM,
      SchwartzMap.toDistr_toBesselPotentialSpaceCLM,
      TemperedDistribution.smulLeftCLM_toTemperedDistributionCLM_eq]
    congr 1
    ext y
    rw [SchwartzMap.smulLeftCLM_apply_apply θ.hasTemperateGrowth, cutoffPushforwardSchwartz_apply,
      hθ]
    by_cases hy : χ y = 0
    · simp [hy]
    · have hyt : y ∈ c.target := χ.tsupport_subset (subset_tsupport _ hy)
      rw [complexCutoffPullback_apply_of_mem hc _ _ (c.map_target hyt), c.right_inv hyt,
        h1 _ (subset_tsupport _ hy), one_smul, ContMDiffMap.coe_ofContDiff, Complex.coe_smul]
  have hi (i : ι) : ‖chartReading he ψ s (c.complexCutoffPullback hc χ U) i‖ ≤
      |C i| * (‖BesselPotentialSpace.smulLeftCLM (F := ℂ) s θ‖ *
        ‖SchwartzMap.toBesselPotentialSpaceCLM s 2 u‖) := by
    rw [chartReading_apply,
      ← mulLeft_ofReal_cutoffPullback_one_complexCutoffPullback_eq_complexCutoffPullback hc h1]
    refine (hC i _).trans ?_
    rw [hread]
    exact mul_le_mul (le_abs_self _) (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      (abs_nonneg _)
  calc ‖chartReading he ψ s (c.complexCutoffPullback hc χ U)‖
      ≤ ∑ i, ‖chartReading he ψ s (c.complexCutoffPullback hc χ U) i‖ := PiLp.norm_le_sum_norm _
    _ ≤ ∑ i, |C i| * (‖BesselPotentialSpace.smulLeftCLM (F := ℂ) s θ‖ *
          ‖SchwartzMap.toBesselPotentialSpaceCLM s 2 u‖) := Finset.sum_le_sum fun i _ ↦ hi i
    _ = (∑ i, |C i|) * ‖BesselPotentialSpace.smulLeftCLM (F := ℂ) s θ‖ *
          ‖SchwartzMap.toBesselPotentialSpaceCLM s 2 u‖ := by
      rw [← Finset.sum_mul, mul_assoc]

/-- **Pulling back from a chart into `H^s(M)`.** The continuous linear map `H^s(ℝⁿ) → H^s(M)`
extending the map that sends a Schwartz function `u` to the smooth function `(χ u) ∘ c` on `M`,
extended by `0` outside the chart source (`OpenPartialHomeomorph.complexCutoffPullback`), for a
cutoff `χ` in a chart `c` (`TauCeti.chartSobolevPullback_toBesselPotentialSpaceCLM`). -/
def chartSobolevPullback (s : ℝ) : H^{s}(CoordinateSpace n) →L[ℂ] chartSobolevSpace he ψ s :=
  (toChartSobolevSpace he ψ s ∘ₗ c.complexCutoffPullback hc χ ∘ₗ
    ({ toFun u := ContMDiffMap.ofContDiff u (u.smooth ⊤)
       map_add' u v := by
         ext
         simp
       map_smul' a u := by
         ext
         simp } :
      𝓢(CoordinateSpace n, ℂ) →ₗ[ℂ]
        C^∞⟮𝓘(ℝ, CoordinateSpace n), CoordinateSpace n; 𝓘(ℝ, ℂ), ℂ⟯)).extendOfNorm
    (SchwartzMap.toBesselPotentialSpaceCLM s 2).toLinearMap

/-- The pullback `H^s(ℝⁿ) → H^s(M)` through the cutoff `χ` in the chart `c` sends a Schwartz
function `u` to the smooth function `(χ u) ∘ c` on `M`, extended by `0`. -/
@[simp]
theorem chartSobolevPullback_toBesselPotentialSpaceCLM (s : ℝ) (u : 𝓢(CoordinateSpace n, ℂ)) :
    chartSobolevPullback he ψ hc χ s (SchwartzMap.toBesselPotentialSpaceCLM s 2 u) =
      toChartSobolevSpace he ψ s
        (c.complexCutoffPullback hc χ (ContMDiffMap.ofContDiff u (u.smooth ⊤))) := by
  obtain ⟨C, hC⟩ := exists_norm_chartReading_complexCutoffPullback_le he ψ hc χ s
  refine LinearMap.extendOfNorm_eq
    (SchwartzMap.denseRange_toBesselPotentialSpaceCLM (p := 2) s ENNReal.ofNat_ne_top)
    ⟨C, fun v ↦ ?_⟩ u
  rw [LinearMap.comp_apply, LinearMap.norm_toRangeClosure]
  exact hC v

end Chart

end TauCeti
