/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Topology.FilledIn
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Runge compact pairs in the complex plane

A **Runge compact pair** `TauCeti.IsRungeCompactPair Ω K` consists of an open set `Ω ⊆ ℂ` and a
compact subset `K ⊆ Ω` that is filled in `Ω` (`TauCeti.IsFilledIn K Ω`, meaning no connected
component of `Ω \ K` is relatively compact in `Ω`).

Separating the predicate and its elementary projection/empty-set API from
`TauCeti.Analysis.Complex.Runge.Operator` avoids pulling in the Cauchy–Pompeiu and rational Runge
approximation stack when only the topological definition is needed.

## Main declarations

* `TauCeti.IsRungeCompactPair`: predicate asserting `IsOpen Ω`, `IsCompact K`, `K ⊆ Ω`, and
  `TauCeti.IsFilledIn K Ω`, with projection eliminators and `@[simp]` empty-set normal forms.

## References

* A. Rainer, *Advanced Complex Analysis*, Theorems 10.3 and 11.1.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed.,
  Theorem 1.3.9.
-/

public section

open Set

namespace TauCeti

/-- A **Runge compact pair**: an open set `Ω ⊆ ℂ` and a compact subset `K ⊆ Ω` that is filled in
`Ω` (no connected component of `Ω \ K` has compact closure contained in `Ω`). -/
def IsRungeCompactPair (Ω K : Set ℂ) : Prop :=
  IsOpen Ω ∧ IsCompact K ∧ K ⊆ Ω ∧ IsFilledIn K Ω

/-- Unfolding `TauCeti.IsRungeCompactPair`. -/
theorem isRungeCompactPair_iff {Ω K : Set ℂ} :
    IsRungeCompactPair Ω K ↔ IsOpen Ω ∧ IsCompact K ∧ K ⊆ Ω ∧ IsFilledIn K Ω :=
  (Iff.rfl)

/-- The ambient set of a Runge compact pair is open. -/
protected theorem IsRungeCompactPair.isOpen {Ω K : Set ℂ} (h : IsRungeCompactPair Ω K) :
    IsOpen Ω :=
  h.1

/-- The compact member of a Runge compact pair is compact. -/
protected theorem IsRungeCompactPair.isCompact {Ω K : Set ℂ} (h : IsRungeCompactPair Ω K) :
    IsCompact K :=
  h.2.1

/-- The compact member of a Runge compact pair is contained in the ambient set. -/
protected theorem IsRungeCompactPair.subset {Ω K : Set ℂ} (h : IsRungeCompactPair Ω K) :
    K ⊆ Ω :=
  h.2.2.1

/-- The compact member of a Runge compact pair is filled in the ambient set. -/
protected theorem IsRungeCompactPair.isFilledIn {Ω K : Set ℂ} (h : IsRungeCompactPair Ω K) :
    IsFilledIn K Ω :=
  h.2.2.2

/-- The empty set forms a Runge compact pair with `Ω` if and only if `Ω` is open. -/
@[simp]
theorem isRungeCompactPair_empty_right {Ω : Set ℂ} :
    IsRungeCompactPair Ω ∅ ↔ IsOpen Ω := by
  refine ⟨fun h => h.isOpen, fun hΩ => ⟨hΩ, isCompact_empty, empty_subset Ω, ?_⟩⟩
  rw [isFilledIn_iff_forall_mem_filledHull_sdiff_not_connectedComponentIn_subset
    isClosed_empty hΩ (empty_subset Ω),
    filledHull_eq_self (by simpa using isPreconnected_univ)
      (by simpa using NormedSpace.unbounded_univ ℂ ℂ)]
  simp

/-- A set `K` forms a Runge compact pair with `∅` if and only if `K = ∅`. -/
@[simp]
theorem isRungeCompactPair_empty_left {K : Set ℂ} :
    IsRungeCompactPair ∅ K ↔ K = ∅ :=
  ⟨fun h => subset_empty_iff.mp h.subset,
    fun h => h ▸ isRungeCompactPair_empty_right.mpr isOpen_empty⟩

end TauCeti
