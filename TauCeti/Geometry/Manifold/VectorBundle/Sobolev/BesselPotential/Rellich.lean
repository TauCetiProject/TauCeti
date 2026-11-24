/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import TauCeti.Analysis.Sobolev.BesselPotential.Inclusion
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.BesselPotential
import TauCeti.Analysis.Distribution.SchwartzSpace.Cutoff
import TauCeti.Analysis.Normed.Operator.Compact.Ehrling
import TauCeti.Analysis.Sobolev.BesselPotential.Rellich

/-!
# The Rellich theorem for Sobolev spaces of bundle distributions

Let `A` be a square chart partition of a bundle `V → M` (`TauCeti.SquareChartPartition`): finitely
many charts `cᵢ` and frames, and cutoffs `χᵢ` with compact supports inside the chart sources such
that `∑ᵢ χᵢ² = 1`. Its Sobolev spaces `H^s` (`TauCeti.SquareChartPartition.sobolevSpace`) are the
tuples `(χᵢ Tᵢⱼ)` of localizations of real functionals `T` on the bundle tests of `V`, in the
Hilbert sum `⨁ᵢⱼ H^s(E, ℂ)` of Euclidean Bessel-potential spaces. This file proves:

* **The inclusion.** For `r ≤ s` the inclusion `H^s ⊆ H^r`
  (`TauCeti.SquareChartPartition.sobolevInclusion`) is a continuous linear map of norm at most `1`,
  which represents the same functional
  (`TauCeti.SquareChartPartition.toDistribution_sobolevInclusion`) and is injective.
* **Rellich's theorem.** For `r < s` the inclusion `H^s ⊆ H^r` is a compact operator
  (`TauCeti.SquareChartPartition.isCompactOperator_sobolevInclusion`). No compactness of `M` is
  assumed: the partition is finite, and every localization `χᵢ Tᵢⱼ` is supported in the compact
  image of the support of `χᵢ` in the chart.
* **Ehrling's inequality.** For `t ≤ r < s` and `ε > 0` there is `C` with
  `‖u‖_{H^r} ≤ ε ‖u‖_{H^s} + C ‖u‖_{H^t}` for all `u ∈ H^s`
  (`TauCeti.SquareChartPartition.exists_norm_sobolevInclusion_le`).

## The argument

The chart supports of `A` are finitely many compact subsets of the model space `E`, so a single
compactly supported smooth function `φ`, a Schwartz function, equals `1` on all of them. Every
localization `χᵢ Tᵢⱼ` is a distribution cut off by `χᵢ` read in the chart, so it is fixed by
multiplication by `φ` (`Distribution.smulLeftCLM_cutoffTempered_of_eq_one`). On each component the
inclusion `H^s(E, ℂ) ⊆ H^r(E, ℂ)` therefore agrees with `u ↦ φ u` followed by the inclusion, which
is compact by the Euclidean Rellich theorem
(`BesselPotentialSpace.isCompactOperator_inclusion_comp_smulLeftCLM`). The image of the unit ball
of `H^s` thus lies in the tuples with every component in one fixed compact set; these form a
compact subset of `H^r`, since `H^r` is closed in the Hilbert sum.

## Main declarations

* `TauCeti.SquareChartPartition.sobolevInclusion`: the inclusion `H^s ⊆ H^r` for `r ≤ s`.
* `TauCeti.SquareChartPartition.norm_sobolevInclusion_le`: its norm is at most `1`.
* `TauCeti.SquareChartPartition.isCompactOperator_sobolevInclusion`: Rellich's theorem.
* `TauCeti.SquareChartPartition.exists_norm_sobolevInclusion_le`: Ehrling's inequality.

## References

* M. E. Taylor, *Partial Differential Equations I*, 2nd ed., Springer, 2011, Chapter 4,
  Proposition 3.4 (Rellich's theorem on a compact manifold).
* J.-P. Demailly, *Complex Analytic and Differential Geometry*, Chapter VI, (2.2) (Rellich's
  theorem on a compact manifold).
-/

public section

noncomputable section

open Bundle Set Metric
open scoped Manifold ContDiff SchwartzMap CompactConvergenceCLM BesselPotentialSpace

namespace TauCeti

namespace SquareChartPartition

variable {ι : Type*} [Fintype ι]
  {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I]

variable (A : SquareChartPartition ι I F V) {r s t : ℝ}

/-! ### The inclusion -/

/-- The **inclusion `H^s ⊆ H^r`**, for `r ≤ s`, of the Sobolev spaces of the square chart partition
`A`: each localization in `H^s(E, ℂ)` is viewed in `H^r(E, ℂ)`. It represents the same functional
on bundle tests (`TauCeti.SquareChartPartition.toDistribution_sobolevInclusion`), and its norm is
at most `1` (`TauCeti.SquareChartPartition.norm_sobolevInclusion_le`). -/
def sobolevInclusion (h : r ≤ s) : A.sobolevSpace s →L[ℝ] A.sobolevSpace r :=
  LinearMap.mkContinuous
    { toFun u := ⟨WithLp.toLp 2 fun k ↦ BesselPotentialSpace.inclusion h (u.val k),
        (A.mem_sobolevSpace_iff_exists_localization r).2 ⟨A.toDistribution s u, fun k ↦ by
          rw [localization_toDistribution, BesselPotentialSpace.toDistr_inclusion]⟩⟩
      map_add' u v := Subtype.ext <| PiLp.ext fun k ↦ by simp
      map_smul' a u := Subtype.ext <| PiLp.ext fun k ↦ by
        simp only [Submodule.coe_smul, PiLp.smul_apply, RingHom.id_apply, ← Complex.coe_smul]
        exact map_smul _ _ _ }
    1 fun u ↦ by
      rw [one_mul, ← Submodule.norm_coe, ← Submodule.norm_coe, PiLp.norm_eq_of_L2,
        PiLp.norm_eq_of_L2]
      gcongr with k
      exact BesselPotentialSpace.norm_inclusion_apply_le h _

theorem coe_sobolevInclusion_apply (h : r ≤ s) (u : A.sobolevSpace s) :
    (A.sobolevInclusion h u : PiLp 2 fun _ : ι × Fin (Module.finrank ℝ F) ↦ H^{r}(E, ℂ)) =
      WithLp.toLp 2 fun k ↦ BesselPotentialSpace.inclusion h (u.val k) :=
  (rfl)

@[simp]
theorem sobolevInclusion_apply_apply (h : r ≤ s) (u : A.sobolevSpace s)
    (k : ι × Fin (Module.finrank ℝ F)) :
    (A.sobolevInclusion h u).val k = BesselPotentialSpace.inclusion h (u.val k) :=
  (rfl)

/-- The inclusion `H^s ⊆ H^r` does not change the functional on bundle tests represented by an
element of `H^s`. -/
@[simp]
theorem toDistribution_sobolevInclusion (h : r ≤ s) (u : A.sobolevSpace s) :
    A.toDistribution r (A.sobolevInclusion h u) = A.toDistribution s u := by
  simp [toDistribution_apply, BesselPotentialSpace.toDistr_inclusion]

@[simp]
theorem sobolevInclusion_ofMemSobolev (h : r ≤ s) {T : BundleTest I F V →L_c[ℝ] ℝ}
    (hT : A.MemSobolev s T) :
    A.sobolevInclusion h (A.ofMemSobolev s hT) = A.ofMemSobolev r (hT.mono h) :=
  A.toDistribution_injective r (by simp)

theorem sobolevInclusion_injective (h : r ≤ s) : Function.Injective (A.sobolevInclusion h) :=
  fun u v huv ↦ A.toDistribution_injective s <| by
    rw [← A.toDistribution_sobolevInclusion h u, ← A.toDistribution_sobolevInclusion h v, huv]

@[simp]
theorem sobolevInclusion_self (u : A.sobolevSpace s) : A.sobolevInclusion le_rfl u = u :=
  A.toDistribution_injective s (A.toDistribution_sobolevInclusion le_rfl u)

@[simp]
theorem sobolevInclusion_sobolevInclusion (h₁ : r ≤ s) (h₂ : t ≤ r) (u : A.sobolevSpace s) :
    A.sobolevInclusion h₂ (A.sobolevInclusion h₁ u) = A.sobolevInclusion (h₂.trans h₁) u :=
  A.toDistribution_injective t (by simp)

theorem norm_sobolevInclusion_apply_le (h : r ≤ s) (u : A.sobolevSpace s) :
    ‖A.sobolevInclusion h u‖ ≤ ‖u‖ := by
  simpa using (A.sobolevInclusion h).le_of_opNorm_le
    (LinearMap.mkContinuous_norm_le _ zero_le_one _) u

/-- The inclusion `H^s ⊆ H^r` has norm at most `1`. -/
theorem norm_sobolevInclusion_le (h : r ≤ s) : ‖A.sobolevInclusion h‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-! ### Rellich's theorem -/

/-- **Rellich's theorem for the Sobolev spaces of a square chart partition.** For `r < s` the
inclusion `H^s ⊆ H^r` is a compact operator. -/
theorem isCompactOperator_sobolevInclusion (h : r < s) :
    IsCompactOperator (A.sobolevInclusion h.le) := by
  -- A Schwartz function `φ` equal to `1` on the supports of all the cutoffs read in the charts.
  obtain ⟨φ, -, -, hφ1⟩ := (isCompact_iUnion fun i ↦ (A.chartSupport i).isCompact)
    |>.exists_schwartzMap_cutoff isOpen_univ (subset_univ _)
  have hφ (i : ι) (x : E) (hx : x ∈ tsupport (A.chartCutoff i)) : φ x = 1 :=
    hφ1.self_of_nhdsSet x (mem_iUnion.2 ⟨i, A.tsupport_chartCutoff_subset i hx⟩)
  -- Every component of an element of `H^s` is fixed by multiplication by `φ`.
  have hfix (u : A.sobolevSpace s) (k : ι × Fin (Module.finrank ℝ F)) :
      BesselPotentialSpace.smulLeftCLM s φ (u.val k) = u.val k := by
    refine BesselPotentialSpace.ext ?_
    rw [BesselPotentialSpace.toDistr_smulLeftCLM, ← A.localization_toDistribution s u k,
      localization_apply]
    exact Distribution.smulLeftCLM_cutoffTempered_of_eq_one _ φ.hasTemperateGrowth (hφ k.1)
  -- The components of the images of the unit ball lie in one compact set `K`.
  let S₀ : Set H^{s}(E, ℂ) := ⋃ k, (fun u : A.sobolevSpace s ↦ u.val k) '' closedBall 0 1
  have hS₀ : Bornology.IsBounded S₀ := by
    refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨1, ?_⟩
    rintro _ ⟨_, ⟨k, rfl⟩, u, hu, rfl⟩
    rw [mem_closedBall_zero_iff] at hu ⊢
    exact (PiLp.norm_apply_le u.val k).trans hu
  let K : Set H^{r}(E, ℂ) := closure (BesselPotentialSpace.inclusion h.le '' S₀)
  have hK : IsCompact K :=
    BesselPotentialSpace.isCompact_closure_image_inclusion_of_smulLeftCLM_eq h hS₀ <| by
      rintro _ ⟨_, ⟨k, rfl⟩, u, -, rfl⟩
      exact hfix u k
  let S : Set (A.sobolevSpace r) := Subtype.val ⁻¹' (WithLp.toLp 2 '' univ.pi fun _ ↦ K)
  have hS : IsCompact S :=
    (A.isClosed_sobolevSpace r).isClosedEmbedding_subtypeVal.isCompact_preimage
      ((isCompact_univ_pi fun _ ↦ hK).image (PiLp.continuous_toLp 2 _))
  rw [← ContinuousLinearMap.coe_coe,
    isCompactOperator_iff_isCompact_closure_image_closedBall _ one_pos]
  refine hS.of_isClosed_subset isClosed_closure (closure_minimal ?_ hS.isClosed)
  rintro _ ⟨u, hu, rfl⟩
  exact ⟨_, fun k _ ↦ subset_closure ⟨u.val k, mem_iUnion.2 ⟨k, u, hu, rfl⟩, rfl⟩,
    (A.coe_sobolevInclusion_apply h.le u).symm⟩

/-- **Ehrling's inequality for the Sobolev spaces of a square chart partition.** For `t ≤ r < s`
and `ε > 0` there is `C ≥ 0` with `‖u‖_{H^r} ≤ ε ‖u‖_{H^s} + C ‖u‖_{H^t}` for every `u ∈ H^s`. -/
theorem exists_norm_sobolevInclusion_le (htr : t ≤ r) (hrs : r < s) {ε : ℝ} (hε : 0 < ε) :
    ∃ C, 0 ≤ C ∧ ∀ u : A.sobolevSpace s,
      ‖A.sobolevInclusion hrs.le u‖ ≤
        ε * ‖u‖ + C * ‖A.sobolevInclusion (htr.trans hrs.le) u‖ := by
  obtain ⟨C, hC, hle⟩ := (A.isCompactOperator_sobolevInclusion hrs)
    |>.exists_norm_le_mul_norm_add_mul_norm (A.sobolevInclusion_injective htr) hε
  exact ⟨C, hC, fun u ↦ by simpa using hle u⟩

end SquareChartPartition

end TauCeti
