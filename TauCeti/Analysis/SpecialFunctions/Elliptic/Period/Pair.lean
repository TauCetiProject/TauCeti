/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.Tactic.FinCases
import Mathlib.Topology.Algebra.Module.Cardinality

/-!
# Removable singularities along a period lattice

Every full lattice in `ℂ` is the lattice of a period pair
(`PeriodPair.exists_lattice_eq_of_isZLattice`).

Elementary analytic facts about functions that are only controlled off the lattice `L.lattice` of
a period pair `L`:

* `PeriodPair.countable_lattice`, `PeriodPair.eventually_notMem_lattice`: the lattice is countable
  and avoided by a punctured neighbourhood of every point;
* `PeriodPair.differentiable_of_periodic`: a lattice-periodic function that is differentiable at
  `0` and off the lattice is entire.
-/

public section

open Filter
open scoped Topology

namespace PeriodPair

/-- Every full lattice in `ℂ` is the lattice of a period pair: a `ℤ`-basis of the lattice is an
`ℝ`-basis of `ℂ`. -/
theorem exists_lattice_eq_of_isZLattice (Λ : Submodule ℤ ℂ) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] : ∃ L : PeriodPair, L.lattice = Λ := by
  let b := Module.finBasisOfFinrankEq ℤ Λ
    (by rw [ZLattice.rank ℝ Λ, Complex.finrank_real_complex] : Module.finrank ℤ Λ = 2)
  let b' := b.ofZLatticeBasis ℝ Λ
  refine ⟨⟨b' 0, b' 1, ?_⟩, ?_⟩
  · convert b'.linearIndependent using 1
    ext i
    fin_cases i <;> rfl
  · rw [PeriodPair.lattice, ← b.ofZLatticeBasis_span ℝ]
    congr 1
    ext z
    simp [b', Fin.exists_fin_two, eq_comm]

variable (L : PeriodPair)

/-- The lattice of a period pair is countable. -/
lemma countable_lattice : (L.lattice : Set ℂ).Countable :=
  countable_of_Lindelof_of_discrete (X := L.lattice)

/-- Every point has a punctured neighbourhood avoiding the lattice. -/
lemma eventually_notMem_lattice (l₀ : ℂ) : ∀ᶠ u in 𝓝[≠] l₀, u ∉ L.lattice := by
  filter_upwards [nhdsWithin_le_nhds (L.compl_lattice_sdiff_singleton_mem_nhds l₀),
    self_mem_nhdsWithin] with u hu hne using fun h ↦ hu ⟨h, hne⟩

/-- A function that is periodic under every lattice vector, differentiable at `0` and
differentiable off the lattice is differentiable everywhere. -/
lemma differentiable_of_periodic {H : ℂ → ℂ} (hper : ∀ w ∈ L.lattice, Function.Periodic H w)
    (h₀ : DifferentiableAt ℂ H 0) (hoff : ∀ x ∉ L.lattice, DifferentiableAt ℂ H x) :
    Differentiable ℂ H := by
  intro x
  by_cases hx : x ∈ L.lattice
  · have hcomp : H = fun y ↦ H (y - x) := funext fun y ↦ by
      rw [← hper x hx (y - x), sub_add_cancel]
    rw [hcomp]
    exact differentiableAt_comp_sub_const.mpr (by simpa using h₀)
  · exact hoff x hx

end PeriodPair
