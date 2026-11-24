/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
public import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Energy filtrations of topological groups

An *energy filtration* of a topological additive group `M` is a decreasing family of subgroups
`F c`, indexed by real cutoffs `c`, which exhausts `M` and whose members form a basis of
neighbourhoods of `0` (`TauCeti.IsEnergyFiltration`). An element of `F c` has *energy at least
`c`*, so that `x ∈ F c` reads `ν(x) ≥ c` for the valuation `ν` of the filtration; small elements
are those of large energy. The motivating example is the ring of Novikov series with its period
filtration, and the completed modules and Hom spaces built over it; in Floer theory `c` is
symplectic area.

Every member of an energy filtration is an open, hence closed, subgroup, and the topology is
nonarchimedean. On a complete group this gives the convergence criterion used throughout filtered
`A∞` algebra: a family whose energies tend to infinity is unconditionally summable
(`TauCeti.IsEnergyFiltration.summable_of_mem`), and its sum has energy at least any common lower
bound of the energies of its terms (`TauCeti.IsEnergyFiltration.tsum_mem`).

## Main definitions

* `TauCeti.IsEnergyFiltration`: a decreasing, exhaustive real filtration by subgroups that is a
  basis of neighbourhoods of `0`.

## Main results

* `TauCeti.IsEnergyFiltration.isOpen` and `TauCeti.IsEnergyFiltration.isClosed`: the members of
  the filtration are open and closed.
* `TauCeti.IsEnergyFiltration.nonarchimedeanAddGroup`: the topology is nonarchimedean.
* `TauCeti.IsEnergyFiltration.tendsto_nhds_zero_iff`: a family tends to `0` exactly when it
  eventually has energy at least `c`, for every `c`.
* `TauCeti.IsEnergyFiltration.summable_of_mem`: on a complete group, a family whose energies
  tend to infinity is summable.
* `TauCeti.IsEnergyFiltration.tsum_mem`: an infinite sum of elements of energy at least `c` has
  energy at least `c`.

## References

* K. Fukaya, Y.-G. Oh, H. Ohta and K. Ono, *Lagrangian intersection Floer theory: anomaly and
  obstruction, Part I*, AMS/IP Studies in Advanced Mathematics 46.1, 2009, Chapter 3.
-/

public section

open Filter Topology

namespace TauCeti

variable {M : Type*} [AddCommGroup M]

section TopologicalSpace

variable [TopologicalSpace M]

/-- An **energy filtration** of a topological additive group `M`: a decreasing family of subgroups
`F c`, `c : ℝ`, which exhausts `M` and whose members form a basis of neighbourhoods of `0`.
An element of `F c` has energy at least `c`. -/
structure IsEnergyFiltration (F : ℝ → AddSubgroup M) : Prop where
  /-- Raising the cutoff shrinks the subgroup. -/
  antitone : Antitone F
  /-- Every element has some finite energy. -/
  exists_mem (x : M) : ∃ c, x ∈ F c
  /-- The subgroups `F c` form a basis of neighbourhoods of `0`. -/
  hasBasis_nhds_zero : (𝓝 (0 : M)).HasBasis (fun _ : ℝ ↦ True) fun c ↦ (F c : Set M)

namespace IsEnergyFiltration

variable {F : ℝ → AddSubgroup M} (hF : IsEnergyFiltration F)
include hF

/-- Each member of an energy filtration is a neighbourhood of `0`. -/
theorem mem_nhds_zero (c : ℝ) : (F c : Set M) ∈ 𝓝 (0 : M) :=
  hF.hasBasis_nhds_zero.mem_of_mem trivial

/-- A family tends to `0` exactly when, for every cutoff `c`, it eventually has energy at
least `c`. -/
theorem tendsto_nhds_zero_iff {ι : Type*} {l : Filter ι} {f : ι → M} :
    Tendsto f l (𝓝 0) ↔ ∀ c, ∀ᶠ i in l, f i ∈ F c := by
  simp [hF.hasBasis_nhds_zero.tendsto_right_iff]

/-- A family whose energies tend to infinity tends to `0`. -/
theorem tendsto_nhds_zero_of_mem {ι : Type*} {l : Filter ι} {f : ι → M} {e : ι → ℝ}
    (hf : ∀ i, f i ∈ F (e i)) (he : Tendsto e l atTop) : Tendsto f l (𝓝 0) :=
  hF.tendsto_nhds_zero_iff.2 fun c ↦
    (he.eventually_ge_atTop c).mono fun i hi ↦ hF.antitone hi (hf i)

variable [IsTopologicalAddGroup M]

/-- Each member of an energy filtration is open. -/
theorem isOpen (c : ℝ) : IsOpen (F c : Set M) :=
  AddSubgroup.isOpen_of_mem_nhds _ (hF.mem_nhds_zero c)

/-- Each member of an energy filtration is closed. -/
theorem isClosed (c : ℝ) : IsClosed (F c : Set M) :=
  AddSubgroup.isClosed_of_isOpen _ (hF.isOpen c)

/-- A topological group with an energy filtration is nonarchimedean: the open subgroups `F c`
form a basis of neighbourhoods of `0`. -/
theorem nonarchimedeanAddGroup : NonarchimedeanAddGroup M where
  is_nonarchimedean U hU := by
    obtain ⟨c, -, hc⟩ := hF.hasBasis_nhds_zero.mem_iff.1 hU
    exact ⟨⟨F c, hF.isOpen c⟩, hc⟩

/-- **Infinite sums do not lower energy.** An infinite sum of elements of energy at least `c` has
energy at least `c`, since `F c` is closed. -/
theorem tsum_mem {ι : Type*} {f : ι → M} {c : ℝ} (hf : ∀ i, f i ∈ F c) : ∑' i, f i ∈ F c :=
  _root_.tsum_mem (hF.isClosed c) hf

end IsEnergyFiltration

end TopologicalSpace

namespace IsEnergyFiltration

variable [UniformSpace M] [IsUniformAddGroup M] [CompleteSpace M] {F : ℝ → AddSubgroup M}

/-- **Convergence by energy.** On a complete group with an energy filtration, a family whose
energies tend to infinity along the cofinite filter is unconditionally summable. -/
theorem summable_of_mem (hF : IsEnergyFiltration F) {ι : Type*} {f : ι → M} {e : ι → ℝ}
    (hf : ∀ i, f i ∈ F (e i)) (he : Tendsto e cofinite atTop) : Summable f :=
  have := hF.nonarchimedeanAddGroup
  NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero (hF.tendsto_nhds_zero_of_mem hf he)

end IsEnergyFiltration

end TauCeti
