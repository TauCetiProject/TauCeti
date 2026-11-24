/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Topology.Defs.Basic
import TauCeti.Data.Fin.Basic

/-!
# Defining systems of degree-one Massey products with trivial coefficients

Let `Γ` be a topological group and `R` a topological ring on which `Γ` acts trivially. The
continuous inhomogeneous `1`-cochains are the continuous maps `Γ → R`; with trivial coefficients
the differential of a `1`-cochain is `(d a)(g, h) = a h - a (g * h) + a g` and the cup product of
two `1`-cochains is `(a ∪ b)(g, h) = a g * b h`.

For `1`-cochains `χ 0, …, χ (n - 1)`, a defining system of the `n`-fold Massey product
`⟨χ 0, …, χ (n - 1)⟩` is a family of continuous `1`-cochains `a i j`, `0 ≤ i < j ≤ n`,
`(i, j) ≠ (0, n)`, with adjacent entries `a i (i + 1) = χ i` and Kraines' defining equations
`d a i j = - ∑_{i < m < j} a i m ∪ a m j`. Written out, these say

`a i j (g * h) = a i j g + a i j h + ∑_{i < m < j} a i m g * a m j h`,

which is how the entries of a product of upper-unitriangular matrices are computed. Its value is
the `2`-cocycle `- ∑_{0 < m < n} a 0 m ∪ a m n`. The Massey product is *defined* when a defining
system exists, and *contains zero* when some value is the coboundary of a continuous `1`-cochain.

This file defines the structure `TauCeti.ContCohomology.DefiningSystem`, its value, and the two
predicates `TauCeti.ContCohomology.MasseyDefined` and `TauCeti.ContCohomology.MasseyContainsZero`.
Dwyer's criteria, which translate both predicates into lifting problems for unitriangular matrix
groups, are in `TauCeti.RepresentationTheory.Homological.ContCohomology.Massey.Dwyer`.

## Main declarations

* `TauCeti.ContCohomology.DefiningSystem`: a defining system of the Massey product of `χ`.
* `TauCeti.ContCohomology.DefiningSystem.value`: its value, a `2`-cochain.
* `TauCeti.ContCohomology.DefiningSystem.continuous_adjacent`,
  `TauCeti.ContCohomology.DefiningSystem.adjacent_mul`: when a defining system exists, the inputs
  are continuous and, for `n ≥ 2`, additive.
* `TauCeti.ContCohomology.MasseyDefined`, `TauCeti.ContCohomology.MasseyContainsZero`: the
  Massey product is defined, respectively contains zero.

## References

* Y. Harpaz and O. Wittenberg, *The Massey vanishing conjecture for number fields*, Duke Math. J.
  172 (2023), Introduction.
* D. Kraines, *Massey higher products*, Trans. Amer. Math. Soc. 124 (1966).
-/

public section

namespace TauCeti.ContCohomology

/-- A **defining system** for the `n`-fold Massey product of the `1`-cochains
`χ 0, …, χ (n - 1)`, with coefficients in a topological ring `R` on which `Γ` acts trivially.

The entries `entry i j : Γ → R` are continuous `1`-cochains. The adjacent entries are the given
cochains, and for `i < j` with `(i, j) ≠ (0, n)` the entry satisfies Kraines' defining equation
`d a i j = - ∑_{i < m < j} a i m ∪ a m j`: the entries multiply like the entries of an
upper-unitriangular matrix (`entry_mul`). The entries with `j ≤ i`, and the corner entry `(0, n)`
when `n ≥ 2`, are zero (`entry_eq_zero`), so that a defining system is determined by its permitted
entries; for `n = 1` the corner is the adjacent entry `χ 0`. -/
@[ext]
structure DefiningSystem (Γ : Type*) [Mul Γ] [TopologicalSpace Γ] (R : Type*) [Ring R]
    [TopologicalSpace R] (n : ℕ) (χ : Fin n → Γ → R) where
  /-- The `(i, j)` entry, a `1`-cochain. -/
  entry : Fin (n + 1) → Fin (n + 1) → Γ → R
  /-- Every entry is continuous. -/
  continuous_entry : ∀ i j, Continuous (entry i j)
  /-- The adjacent entries are the given cochains. -/
  entry_castSucc_succ : ∀ i : Fin n, entry i.castSucc i.succ = χ i
  /-- The defining equation `d a i j = - ∑_{i < m < j} a i m ∪ a m j` away from the corner. -/
  entry_mul : ∀ i j : Fin (n + 1), i < j → ¬ (i = 0 ∧ j = Fin.last n) → ∀ g h : Γ,
    entry i j (g * h) =
      entry i j g + entry i j h + ∑ m ∈ Finset.Ioo i j, entry i m g * entry m j h
  /-- The entries that are not permitted vanish: those on or below the diagonal, and the corner
  `(0, n)` when it is not adjacent. -/
  entry_eq_zero : ∀ i j : Fin (n + 1), (j ≤ i ∨ (i = 0 ∧ j = Fin.last n ∧ 2 ≤ n)) →
    entry i j = 0

namespace DefiningSystem

attribute [simp] entry_castSucc_succ

variable {Γ : Type*} [Mul Γ] [TopologicalSpace Γ] {R : Type*} [Ring R] [TopologicalSpace R]
  {n : ℕ} {χ : Fin n → Γ → R}

/-- The **value** of a defining system: the `2`-cochain `- ∑_{0 < m < n} a 0 m ∪ a m n`, that is
`(g, h) ↦ - ∑_{0 < m < n} a 0 m g * a m n h`. -/
def value (D : DefiningSystem Γ R n χ) (x : Γ × Γ) : R :=
  -∑ m ∈ Finset.Ioo (0 : Fin (n + 1)) (Fin.last n), D.entry 0 m x.1 * D.entry m (Fin.last n) x.2

@[simp]
theorem value_apply (D : DefiningSystem Γ R n χ) (g h : Γ) :
    D.value (g, h) =
      -∑ m ∈ Finset.Ioo (0 : Fin (n + 1)) (Fin.last n), D.entry 0 m g * D.entry m (Fin.last n) h :=
  (rfl)

/-- The inputs of a Massey product that has a defining system are continuous. -/
theorem continuous_adjacent (D : DefiningSystem Γ R n χ) (i : Fin n) : Continuous (χ i) :=
  D.entry_castSucc_succ i ▸ D.continuous_entry _ _

/-- The inputs of an `n`-fold Massey product with `n ≥ 2` that has a defining system are additive,
that is, `1`-cocycles: the defining equation of an adjacent entry has no correction term. For
`n = 1` the only input is the corner entry, on which no equation is imposed. -/
theorem adjacent_mul (D : DefiningSystem Γ R n χ) (hn : 2 ≤ n) (i : Fin n) (g h : Γ) :
    χ i (g * h) = χ i g + χ i h := by
  have hIoo : Finset.Ioo i.castSucc i.succ = ∅ := by
    refine Finset.eq_empty_of_forall_notMem fun m hm ↦ ?_
    rw [Finset.mem_Ioo, Fin.lt_def, Fin.lt_def, Fin.val_castSucc, Fin.val_succ] at hm
    omega
  have := D.entry_mul _ _ (Fin.castSucc_lt_succ (i := i))
    (Fin.not_castSucc_eq_zero_and_succ_eq_last hn i) g h
  rwa [hIoo, Finset.sum_empty, add_zero, D.entry_castSucc_succ] at this

end DefiningSystem

variable {Γ : Type*} [Mul Γ] [TopologicalSpace Γ] {R : Type*} [Ring R] [TopologicalSpace R]
  {n : ℕ}

/-- The `n`-fold Massey product of `χ` is **defined**: it has a defining system. -/
def MasseyDefined (χ : Fin n → Γ → R) : Prop :=
  Nonempty (DefiningSystem Γ R n χ)

/-- The `n`-fold Massey product of `χ` **contains zero**: some defining system has value the
coboundary `(g, h) ↦ f h - f (g * h) + f g` of a continuous `1`-cochain `f`. -/
def MasseyContainsZero (χ : Fin n → Γ → R) : Prop :=
  ∃ D : DefiningSystem Γ R n χ, ∃ f : Γ → R, Continuous f ∧
    ∀ g h : Γ, D.value (g, h) = f h - f (g * h) + f g

theorem masseyDefined_iff (χ : Fin n → Γ → R) :
    MasseyDefined χ ↔ Nonempty (DefiningSystem Γ R n χ) :=
  Iff.rfl

theorem masseyContainsZero_iff (χ : Fin n → Γ → R) :
    MasseyContainsZero χ ↔ ∃ D : DefiningSystem Γ R n χ, ∃ f : Γ → R, Continuous f ∧
      ∀ g h : Γ, D.value (g, h) = f h - f (g * h) + f g :=
  Iff.rfl

/-- A Massey product that contains zero is defined. -/
theorem MasseyContainsZero.masseyDefined {χ : Fin n → Γ → R} (h : MasseyContainsZero χ) :
    MasseyDefined χ :=
  let ⟨D, _⟩ := h
  ⟨D⟩

end TauCeti.ContCohomology
