/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.UniformSpace.CompactConvergence
import TauCeti.Topology.Compactness.SigmaCompact

/-!
# Completeness, Cauchy criteria, and restriction for compact convergence on `C(X, Y)`

For a uniform target `Y`, the compact-convergence uniformity on `C(X, Y)` satisfies:

* `CompactExhaustion.completeSpace_continuousMap`: when `X` admits a `CompactExhaustion` and `Y`
  is complete, `C(X, Y)` is complete;
* `ContinuousMap.cauchy_map_iff_forall_isCompact_uniformCauchySeqOn` and
  `ContinuousMap.cauchySeq_iff_forall_isCompact_uniformCauchySeqOn`: Cauchy filters and directed
  Cauchy nets in `C(X, Y)` are characterized by `UniformCauchySeqOn` on every compact subset of
  `X`;
* `ContinuousMap.uniformContinuous_restrict`: restriction `C(X, Y) → C(s, Y)` to any subset `s` of
  `X` is uniformly continuous.
-/

public section

open Filter Set

/-- If `X` admits a `CompactExhaustion` and the uniform space `Y` is complete, then `C(X, Y)` is
complete for compact convergence. -/
theorem CompactExhaustion.completeSpace_continuousMap {X Y : Type*} [TopologicalSpace X]
    [UniformSpace Y] [CompleteSpace Y] (K : CompactExhaustion X) : CompleteSpace C(X, Y) := by
  have : WeaklyLocallyCompactSpace X := K.weaklyLocallyCompactSpace
  infer_instance

namespace ContinuousMap

variable {X Y : Type*} [TopologicalSpace X] [UniformSpace Y]

/-- Filter-level Cauchy equivalence on `C(X, Y)` with `UniformCauchySeqOn` on every compact subset
of `X`. -/
theorem cauchy_map_iff_forall_isCompact_uniformCauchySeqOn {ι : Type*} {p : Filter ι}
    {F : ι → C(X, Y)} :
    Cauchy (map F p) ↔ p.NeBot ∧ ∀ s, IsCompact s → UniformCauchySeqOn (fun i x ↦ F i x) p s := by
  rw [cauchy_map_iff, ContinuousMap.hasBasis_compactConvergenceUniformity.tendsto_right_iff]
  refine and_congr_right fun _ ↦ ?_
  simp only [Prod.forall, and_imp, UniformCauchySeqOn]
  exact ⟨fun h s hs u hu ↦ h s u hs hu, fun h s u hs hu ↦ h s hs u hu⟩

/-- Directed-net `CauchySeq` in `C(X, Y)` is equivalent to `UniformCauchySeqOn` on every compact
subset of `X`. -/
theorem cauchySeq_iff_forall_isCompact_uniformCauchySeqOn {ι : Type*} [Nonempty ι]
    [SemilatticeSup ι] {u : ι → C(X, Y)} :
    CauchySeq u ↔ ∀ s, IsCompact s → UniformCauchySeqOn (fun n x ↦ u n x) atTop s := by
  rw [CauchySeq, cauchy_map_iff_forall_isCompact_uniformCauchySeqOn,
    and_iff_right (atTop_neBot (α := ι))]

/-- Restriction to any subset `s` of `X` is uniformly continuous from `C(X, Y)` to `C(s, Y)` for
the compact-convergence uniform structure (and in particular into the supremum pseudometric when
`s` is compact and `Y` is a pseudometric space). -/
theorem uniformContinuous_restrict (s : Set X) :
    UniformContinuous (ContinuousMap.restrict s : C(X, Y) → C(s, Y)) :=
  ContinuousMap.uniformContinuous_comp_left (ContinuousMap.subtypeVal s)

end ContinuousMap
