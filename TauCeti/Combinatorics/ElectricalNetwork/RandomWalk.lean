/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.ElectricalNetwork.Basic
public import TauCeti.Data.ENNReal.Weights
public import TauCeti.Probability.Kernel.Invariance
public import TauCeti.Probability.Kernel.Reachability

/-!
# The random walk of an electrical network

The random walk of a finite electrical network steps from `x` to `y` with probability
`c x y / c x`, where `c x = ∑ y, c x y` is the weight of `x`. A vertex of weight zero carries no
edge and no loop, and the walk stays there forever. The walk is not made lazy: it stays at `x`
only through a loop, with probability `c x x / c x`.

The walk is reversible with respect to the measure `π {x} = c x / c_G`, where `c_G` is the total
weight: the flow `π {x} * P(x, y) = c x y / c_G` from `x` to `y` is symmetric in `x` and `y`.
Hence `π` is invariant, and it is a probability measure as soon as `c_G > 0`. On a connected
network the walk is irreducible, every vertex reaching every other along the edges of the graph of
the network. Conversely, every Markov kernel that is reversible with respect to a probability
measure charging every point is the walk of the network with conductances
`c x y = π {x} * κ x {y}`, whose invariant measure is `π`. Every such reversible Markov chain on a
finite state space is thus the walk of an electrical network, which is what lets voltages and
effective resistances describe hitting probabilities and hitting times of reversible chains.

## Main definitions

* `TauCeti.ElectricalNetwork.walkPMF`: the transition law of the walk from a vertex.
* `TauCeti.ElectricalNetwork.walk`: the random walk, a Markov kernel.
* `TauCeti.ElectricalNetwork.stationaryMeasure`: the measure `π {x} = c x / c_G`.
* `TauCeti.ElectricalNetwork.ofIsReversible`: the network of a kernel reversible with respect to a
  measure.

## Main results

* `TauCeti.ElectricalNetwork.walk_apply_singleton`: `P(x, y) = c x y / c x` when `c x > 0`.
* `TauCeti.ElectricalNetwork.isReversible_walk`: the walk is reversible with respect to
  `stationaryMeasure`, so (`TauCeti.ElectricalNetwork.invariant_walk`) this measure is invariant.
* `TauCeti.ElectricalNetwork.isIrreducible_walk`: on a connected network the walk is irreducible.
* `TauCeti.ElectricalNetwork.walk_ofIsReversible` and
  `TauCeti.ElectricalNetwork.stationaryMeasure_ofIsReversible`: a Markov kernel reversible with
  respect to a probability measure charging every point is the walk of a network, with that
  measure as its stationary measure.

## References

* D. A. Levin and Y. Peres, *Markov chains and mixing times*, second edition, American
  Mathematical Society, 2017, §9.1.
* R. Lyons and Y. Peres, *Probability on trees and networks*, Cambridge University Press, 2016,
  §2.1.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace TauCeti

namespace ElectricalNetwork

variable {V : Type*} [Fintype V] (N : ElectricalNetwork V)

/-- The transition law of the random walk from `x`: it moves to `y` with probability `c x y / c x`
when `c x > 0`, and stays at `x` when `x` has weight zero. -/
noncomputable def walkPMF (x : V) : PMF V :=
  if hx : 0 < N.weight x then
    PMF.ofFintype (fun y => ENNReal.ofReal (N.cond x y / N.weight x))
      (ENNReal.sum_ofReal_div_eq_one (fun y _ => N.nonneg x y) (N.weight_def x).symm hx)
  else PMF.pure x

/-- From a vertex of positive weight the walk moves to `y` with probability `c x y / c x`. -/
theorem walkPMF_apply {x : V} (hx : 0 < N.weight x) (y : V) :
    N.walkPMF x y = ENNReal.ofReal (N.cond x y / N.weight x) := by
  simp only [walkPMF, hx, ↓reduceDIte, PMF.ofFintype_apply]

/-- From a vertex of weight zero the walk does not move. -/
theorem walkPMF_of_weight_eq_zero {x : V} (hx : N.weight x = 0) : N.walkPMF x = PMF.pure x := by
  simp [walkPMF, hx]

variable [MeasurableSpace V] [MeasurableSingletonClass V]

/-- The random walk of a network, the Markov kernel whose row at `x` is `walkPMF x`. -/
noncomputable def walk : Kernel V V :=
  Kernel.ofPMF N.walkPMF

/-- The row of the walk at `x` is the measure of its transition law. -/
theorem walk_apply (x : V) : N.walk x = (N.walkPMF x).toMeasure :=
  Kernel.ofPMF_apply N.walkPMF x

instance : IsMarkovKernel N.walk :=
  inferInstanceAs (IsMarkovKernel (Kernel.ofPMF N.walkPMF))

/-- The walk steps from a vertex `x` of positive weight to `y` with probability `c x y / c x`. -/
theorem walk_apply_singleton {x : V} (hx : 0 < N.weight x) (y : V) :
    N.walk x {y} = ENNReal.ofReal (N.cond x y / N.weight x) := by
  rw [walk, Kernel.ofPMF_apply_singleton, N.walkPMF_apply hx]

/-- The real transition probability from a vertex `x` of positive weight to `y` is
`c x y / c x`. -/
theorem toReal_walk_apply_singleton {x : V} (hx : 0 < N.weight x) (y : V) :
    (N.walk x {y}).toReal = N.cond x y / N.weight x := by
  rw [N.walk_apply_singleton hx, ENNReal.toReal_ofReal (div_nonneg (N.nonneg x y) hx.le)]

/-- The walk stays forever at a vertex of weight zero. -/
theorem walk_apply_of_weight_eq_zero {x : V} (hx : N.weight x = 0) :
    N.walk x = Measure.dirac x := by
  rw [walk_apply, N.walkPMF_of_weight_eq_zero hx, PMF.toMeasure_pure]

/-- The walk steps from `x` to `y` with positive probability when `c x y > 0`. -/
theorem walk_apply_singleton_pos {x y : V} (hxy : 0 < N.cond x y) : 0 < N.walk x {y} := by
  have hx : 0 < N.weight x := N.weight_pos_iff.2 ⟨y, hxy⟩
  rw [N.walk_apply_singleton hx, ENNReal.ofReal_pos]
  exact div_pos hxy hx

/-- A vertex reaches, for the walk, every vertex joined to it by a walk in the graph of the
network. -/
theorem reaches_walk_of_reachable {x y : V} (h : N.graph.Reachable x y) : N.walk.Reaches x y := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact Kernel.Reaches.refl x
  | tail _ hyz ih =>
    exact ih.trans (Kernel.reaches_of_pos (N.walk_apply_singleton_pos (N.cond_pos_of_adj hyz)))

/-- **Irreducibility of the walk**: on a preconnected network, in particular on a connected one,
the walk is irreducible with respect to the counting measure, that is, every vertex reaches every
vertex. -/
theorem isIrreducible_walk (hN : N.graph.Preconnected) :
    Kernel.IsIrreducible Measure.count N.walk :=
  Kernel.isIrreducible_count_iff_forall_reaches.2 fun x y => N.reaches_walk_of_reachable (hN x y)

/-- The stationary measure of the walk, `π {x} = c x / c_G`. It is a probability measure when the
total weight is positive (`TauCeti.ElectricalNetwork.isProbabilityMeasure_stationaryMeasure`),
and the zero measure when the total weight vanishes. -/
noncomputable def stationaryMeasure : Measure V :=
  ∑ x, ENNReal.ofReal (N.weight x / N.totalWeight) • Measure.dirac x

/-- The stationary measure gives the vertex `x` the mass `c x / c_G`. -/
@[simp]
theorem stationaryMeasure_singleton (x : V) :
    N.stationaryMeasure {x} = ENNReal.ofReal (N.weight x / N.totalWeight) := by
  classical
  simp [stationaryMeasure, Set.indicator_apply]

/-- On a network of positive total weight the stationary measure is a probability measure. -/
theorem isProbabilityMeasure_stationaryMeasure (h : 0 < N.totalWeight) :
    IsProbabilityMeasure N.stationaryMeasure := by
  refine ⟨?_⟩
  rw [← Finset.coe_univ, ← sum_measure_singleton]
  simp_rw [stationaryMeasure_singleton]
  exact ENNReal.sum_ofReal_div_eq_one (fun x _ => N.weight_nonneg x) N.totalWeight_def.symm h

/-- **Detailed balance**: under the stationary measure the flow `π {x} * P(x, y)` from `x` to `y`
is `c x y / c_G`. -/
theorem stationaryMeasure_singleton_mul_walk_apply_singleton (x y : V) :
    N.stationaryMeasure {x} * N.walk x {y} = ENNReal.ofReal (N.cond x y / N.totalWeight) := by
  rcases (N.weight_nonneg x).lt_or_eq with hx | hx
  · rw [stationaryMeasure_singleton, N.walk_apply_singleton hx,
      ← ENNReal.ofReal_mul (div_nonneg (N.weight_nonneg x) N.totalWeight_nonneg)]
    congr 1
    field_simp
  · simp [← hx, N.weight_eq_zero_iff.1 hx.symm]

/-- **Reversibility of the walk**: the walk of a network is reversible with respect to its
stationary measure `π {x} = c x / c_G`. -/
theorem isReversible_walk : N.walk.IsReversible N.stationaryMeasure :=
  Kernel.isReversible_iff_singleton.2 fun x y => by
    rw [stationaryMeasure_singleton_mul_walk_apply_singleton,
      stationaryMeasure_singleton_mul_walk_apply_singleton, N.symm]

/-- The stationary measure `π {x} = c x / c_G` is invariant under the walk. -/
theorem invariant_walk : N.walk.Invariant N.stationaryMeasure :=
  N.isReversible_walk.invariant

section OfIsReversible

variable {κ : Kernel V V} {π : Measure V}

/-- The network of a kernel `κ` reversible with respect to a measure `π`: the conductance between
`x` and `y` is the flow `π {x} * κ x {y}`, symmetric by detailed balance. When `κ` is Markov and
`π` is a finite measure charging every point, its walk is `κ`
(`TauCeti.ElectricalNetwork.walk_ofIsReversible`). -/
noncomputable def ofIsReversible (κ : Kernel V V) (π : Measure V) (hκ : κ.IsReversible π) :
    ElectricalNetwork V where
  cond x y := (π {x} * κ x {y}).toReal
  symm x y := by rw [Kernel.isReversible_iff_singleton.1 hκ x y]
  nonneg _ _ := ENNReal.toReal_nonneg

/-- The conductance between `x` and `y` in the network of a reversible kernel is the flow
`π {x} * κ x {y}`. -/
@[simp]
theorem ofIsReversible_cond (hκ : κ.IsReversible π) (x y : V) :
    (ofIsReversible κ π hκ).cond x y = (π {x} * κ x {y}).toReal := (rfl)

/-- In the network of a Markov kernel reversible with respect to a measure `π`, the weight of a
vertex is the real part of its mass under `π` (which is `0` for an infinite mass). -/
@[simp]
theorem weight_ofIsReversible [IsMarkovKernel κ] (hκ : κ.IsReversible π) (x : V) :
    (ofIsReversible κ π hκ).weight x = (π {x}).toReal := by
  simp [weight_def, ENNReal.toReal_mul, ← Finset.mul_sum, ← measureReal_def]

/-- The network of a Markov kernel reversible with respect to a probability measure has total
weight `1`. -/
@[simp]
theorem totalWeight_ofIsReversible [IsMarkovKernel κ] [IsProbabilityMeasure π]
    (hκ : κ.IsReversible π) : (ofIsReversible κ π hκ).totalWeight = 1 := by
  simp [totalWeight_def, ← measureReal_def]

/-- **Reversible kernels are walks of networks**: a Markov kernel reversible with respect to a
finite measure `π` charging every point is the walk of the network with conductances
`c x y = π {x} * κ x {y}`. -/
theorem walk_ofIsReversible [IsMarkovKernel κ] [IsFiniteMeasure π] (hκ : κ.IsReversible π)
    (hπ : ∀ x, π {x} ≠ 0) : (ofIsReversible κ π hκ).walk = κ := by
  refine Kernel.ext fun x => Measure.ext_of_singleton fun y => ?_
  have hx : 0 < (π {x}).toReal := ENNReal.toReal_pos (hπ x) (measure_ne_top π {x})
  rw [walk_apply_singleton _ (by rwa [weight_ofIsReversible])]
  simp [ENNReal.toReal_mul, hx.ne', measure_ne_top]

/-- The stationary measure of the network of a Markov kernel reversible with respect to a
probability measure `π` is `π`. -/
@[simp]
theorem stationaryMeasure_ofIsReversible [IsMarkovKernel κ] [IsProbabilityMeasure π]
    (hκ : κ.IsReversible π) : (ofIsReversible κ π hκ).stationaryMeasure = π := by
  refine Measure.ext_of_singleton fun x => ?_
  rw [stationaryMeasure_singleton, totalWeight_ofIsReversible, div_one, weight_ofIsReversible,
    ENNReal.ofReal_toReal (measure_ne_top π {x})]

end OfIsReversible

end ElectricalNetwork

end TauCeti
