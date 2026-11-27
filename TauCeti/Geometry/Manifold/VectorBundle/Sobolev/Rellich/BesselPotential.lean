/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.BesselPotential.Multiplication
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.BesselPotential
import TauCeti.Analysis.Distribution.SchwartzSpace.Cutoff
import TauCeti.Analysis.Normed.Operator.Compact.Ehrling
import TauCeti.Analysis.Sobolev.BesselPotential.Rellich

/-!
# The Rellich theorem for the Sobolev spaces of a square chart partition

Let `A` be a square chart partition of a smooth real vector bundle `V → M`
(`TauCeti.SquareChartPartition`), with its Sobolev spaces `H^s`, `s ∈ ℝ`, of real functionals on
the bundle tests of `V` (`TauCeti.SquareChartPartition.sobolevSpace`); for instance `A` exists on
every compact boundaryless manifold (`TauCeti.exists_squareChartPartition`), and the functionals
include the distributional sections of a bundle whose dual density bundle is `V`. This file proves
that for real orders `r < s` the inclusion `H^s ⊆ H^r`
(`TauCeti.SquareChartPartition.inclusion`) is a **compact operator**
(`TauCeti.SquareChartPartition.isCompactOperator_inclusion`).

An element of `H^s` is the tuple of the localizations `χᵢ Tᵢⱼ` of a functional `T`, and the
localization in the `i`-th chart is supported in the compact set `A.chartSupport i`. A Schwartz
function `φ` equal to `1` on all of these finitely many compact sets therefore fixes every
component (`TauCeti.SquareChartPartition.smulLeftCLM_apply_of_eqOn_one`), so in each component the
inclusion is the operator `u ↦ φ u` from `H^s(E, ℂ)` to `H^r(E, ℂ)`, which is compact by the
Rellich theorem for a common compact support
(`BesselPotentialSpace.isCompactOperator_inclusion_comp_smulLeftCLM`). A map into the finite
Hilbert sum `⨁ᵢⱼ H^r(E, ℂ)` with compact components is compact, and so is its corestriction to
the closed subspace `H^r` (`BesselPotentialSpace.isCompactOperator_piLp_of_smulLeftCLM_eq`).

With Ehrling's lemma this gives **Ehrling's inequality**: for `t ≤ r < s` and every `ε > 0` there
is `C` with `‖u‖_{H^r} ≤ ε ‖u‖_{H^s} + C ‖u‖_{H^t}` for all `u ∈ H^s`
(`TauCeti.SquareChartPartition.exists_norm_inclusion_le_mul_norm_add_mul_norm`).

Compactness of `H^s ⊆ H^r` is what turns a parametrix of an elliptic operator on a compact
manifold, inverting it modulo operators of negative order, into the Fredholm property of the
operator between these Sobolev spaces.

## Main results

* `TauCeti.SquareChartPartition.isCompactOperator_inclusion`: the Rellich theorem.
* `TauCeti.SquareChartPartition.exists_norm_inclusion_le_mul_norm_add_mul_norm`: Ehrling's
  inequality.

## References

* M. E. Taylor, *Partial Differential Equations I*, 2nd ed., Springer, 2011, Chapter 4, §3
  (Sobolev spaces on compact manifolds and Rellich's theorem).
* J.-P. Demailly, *Complex Analytic and Differential Geometry*, Chapter VI, (2.1)–(2.2) (the
  Sobolev and Rellich lemmas on a compact manifold, in integer order).
-/

public section

noncomputable section

open Bundle Set
open scoped Manifold ContDiff Distributions SchwartzMap CompactConvergenceCLM BesselPotentialSpace

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

variable (A : SquareChartPartition ι I F V)

/-- **Localizations are fixed by cutoffs equal to one on the chart supports.** If a Schwartz
function `φ` equals `1` on the compact set `A.chartSupport i`, then multiplication by `φ` fixes
every component, in the `i`-th chart, of an element of the Sobolev space `H^s` of `A`. -/
theorem smulLeftCLM_apply_of_eqOn_one {s : ℝ} {φ : 𝓢(E, ℂ)} {i : ι}
    (hφ : EqOn φ 1 (A.chartSupport i)) (u : A.sobolevSpace s) (j : Fin (Module.finrank ℝ F)) :
    BesselPotentialSpace.smulLeftCLM s φ (u.val (i, j)) = u.val (i, j) :=
  BesselPotentialSpace.ext <| by
    rw [BesselPotentialSpace.toDistr_smulLeftCLM, ← A.localization_toDistribution s u (i, j),
      localization_apply]
    exact Distribution.smulLeftCLM_cutoffTempered_of_eqOn_one _ _ φ.hasTemperateGrowth
      (hφ.mono (A.tsupport_chartCutoff_subset i))

/-- **The Rellich theorem.** For real orders `r < s`, the inclusion `H^s ⊆ H^r` of the Sobolev
spaces of a square chart partition is a compact operator. -/
theorem isCompactOperator_inclusion {r s : ℝ} (h : r < s) :
    IsCompactOperator (A.inclusion h.le) := by
  -- A Schwartz function `φ` equal to `1` on the finitely many compact chart supports.
  obtain ⟨φ, -, -, hφ1⟩ :=
    (isCompact_iUnion fun i ↦ (A.chartSupport i).isCompact).exists_schwartzMap_cutoff isOpen_univ
      (subset_univ _)
  have hφ (i : ι) : EqOn φ 1 (A.chartSupport i) := fun y hy ↦
    hφ1.self_of_nhdsSet y (mem_iUnion_of_mem i hy)
  exact BesselPotentialSpace.isCompactOperator_piLp_of_smulLeftCLM_eq φ h
    (i := Subtype.val) continuous_subtypeVal rfl
    (A.isClosed_sobolevSpace r).isClosedEmbedding_subtypeVal
    (fun u k ↦ A.smulLeftCLM_apply_of_eqOn_one (hφ k.1) u k.2) (A.inclusion_apply h.le)

/-- **Ehrling's inequality.** For real orders `t ≤ r < s` and `ε > 0` there is `C ≥ 0` with
`‖u‖_{H^r} ≤ ε ‖u‖_{H^s} + C ‖u‖_{H^t}` for every `u` in the Sobolev space `H^s` of a square chart
partition. -/
theorem exists_norm_inclusion_le_mul_norm_add_mul_norm {r s t : ℝ} (htr : t ≤ r) (hrs : r < s)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C, 0 ≤ C ∧ ∀ u : A.sobolevSpace s,
      ‖A.inclusion hrs.le u‖ ≤ ε * ‖u‖ + C * ‖A.inclusion (htr.trans hrs.le) u‖ := by
  obtain ⟨C, hC, hCu⟩ := (A.isCompactOperator_inclusion hrs).exists_norm_le_mul_norm_add_mul_norm
    (i := (A.inclusion hrs.le : A.sobolevSpace s →ₗ[ℝ] A.sobolevSpace r))
    (A.inclusion_injective htr) hε
  exact ⟨C, hC, fun u ↦ by simpa using hCu u⟩

end SquareChartPartition

end TauCeti
