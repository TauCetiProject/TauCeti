/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.PiTopology
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import TauCeti.NumberTheory.Padics.Coleman.Norm

import Mathlib.Topology.Algebra.Constructions
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Instances.Matrix
import TauCeti.RingTheory.PowerSeries.PiTopology
import TauCeti.RingTheory.PowerSeries.Substitution

/-!
# Continuity of Coleman operators

This file proves continuity of Frobenius substitution `frobeniusHom` (for any topological ring `O`
and `O⟦X⟧` in the coefficientwise topology `PowerSeries.WithPiTopology`) and, for a prime `p`
and `(p)`-adically complete ring `O` equipped with its `(p)`-adic topology, continuity of the
Coleman coordinates `coord`, trace `trace`, norm `norm`, and unit norm `normUnits` in the
coefficientwise topology on `O⟦X⟧`.

## Main results

* `TauCeti.Coleman.continuous_frobeniusHom`: Frobenius substitution `Φ` is continuous for the
  coefficientwise topology on `O⟦X⟧`.
* `TauCeti.Coleman.continuous_coord`: each `coord p O i` is continuous for the coefficientwise
  topology on `O⟦X⟧` when `O` has its `(p)`-adic topology.
* `TauCeti.Coleman.continuous_trace`: `trace p O` is continuous for the coefficientwise topology
  on `O⟦X⟧` when `O` has its `(p)`-adic topology.
* `TauCeti.Coleman.continuous_norm`: `norm p O` is continuous for the coefficientwise topology on
  `O⟦X⟧` when `O` has its `(p)`-adic topology.
* `TauCeti.Coleman.continuous_normUnits`: `normUnits p O` is continuous for the coefficientwise
  topology on `O⟦X⟧` when `O` has its `(p)`-adic topology.

## References

* R. F. Coleman, *Division Values in Local Fields*, Invent. Math. 53 (1979), §§II, IV.
* R. Sharifi, *Iwasawa Theory*, §5.4.
* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions* (2025), Ch. 10.
-/

public section

open PowerSeries
open scoped PowerSeries.WithPiTopology Topology

namespace TauCeti.Coleman

variable {p : ℕ} {O : Type*} [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]

/-- Frobenius substitution `Φ` is continuous for the coefficientwise topology on `O⟦X⟧`. -/
theorem continuous_frobeniusHom : Continuous (frobeniusHom p O) :=
  (funext frobeniusHom_apply : (frobeniusHom p O : O⟦X⟧ → O⟦X⟧) = _).symm ▸
    Continuous.powerSeries_subst continuous_id continuous_const (fun _ ↦ by simp)

variable [Fact p.Prime] [IsAdicComplete (Ideal.span {(p : O)}) O]

/-- Each Coleman coordinate `coord p O i` is continuous for the coefficientwise topology on
`O⟦X⟧` when `O` has its `(p)`-adic topology. -/
theorem continuous_coord (hAdic : IsAdic (Ideal.span {(p : O)})) (i : Fin p) :
    Continuous (coord p O i) := by
  refine continuous_of_continuousAt_zero (coord p O i).toAddMonoidHom ?_
  rw [ContinuousAt, map_zero, PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
  intro n
  simp only [map_zero, hAdic.hasBasis_nhds_zero.tendsto_right_iff]
  refine fun k _ ↦ Filter.mem_of_superset
    (x := ⋂ s ∈ Finset.range (p ^ k * (n + 1)), {f : O⟦X⟧ | coeff s f ∈ Ideal.span {(p : O)} ^ k})
    ((Filter.biInter_finset_mem _).mpr fun s _ ↦
      (PowerSeries.WithPiTopology.continuous_coeff O s).continuousAt (x := 0) <| by
        rw [map_zero]; exact hAdic.hasBasis_nhds_zero.mem_of_mem (i := k) trivial)
    fun f hf ↦ coeff_coord_mem_span_pow_of_coeff_mem_span_pow k
      (by simpa only [Set.mem_iInter, Set.mem_ofPred_eq, Finset.mem_range] using hf) i

/-- Coleman's trace operator is continuous for the coefficientwise topology on `O⟦X⟧` when `O` has
its `(p)`-adic topology. -/
theorem continuous_trace (hAdic : IsAdic (Ideal.span {(p : O)})) : Continuous (trace p O) :=
  (funext trace_eq_p_mul_coord_zero : (trace p O : O⟦X⟧ → O⟦X⟧) = _).symm ▸
    continuous_const.mul (continuous_coord hAdic _)

/-- Coleman's norm operator is continuous for the coefficientwise topology on `O⟦X⟧` when `O` has
its `(p)`-adic topology. -/
theorem continuous_norm (hAdic : IsAdic (Ideal.span {(p : O)})) : Continuous (norm p O) := by
  have hmat : Continuous (leftMulMatrix p O) := continuous_matrix fun i j ↦ by
    simp_rw [leftMulMatrix_apply]
    split_ifs
    · exact continuous_coord hAdic _
    · exact (continuous_coord hAdic _).mul continuous_const
  exact hmat.matrix_det.congr fun f ↦ (norm_eq_det_leftMulMatrix f).symm

/-- Coleman's norm on units is continuous for the coefficientwise topology on `O⟦X⟧` when `O` has
its `(p)`-adic topology. -/
theorem continuous_normUnits (hAdic : IsAdic (Ideal.span {(p : O)})) :
    Continuous (normUnits p O) :=
  normUnits_eq_unitsMap_norm p O ▸ Units.continuous_map (continuous_norm hAdic)

end TauCeti.Coleman
