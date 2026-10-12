/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Compactification.Fiber

/-!
# Unramified interior fibres of Fuchsian quotient maps

When the stabilizer acts trivially on the subgroup cosets, the fibre of an induced map of
compactified quotients has exactly the subgroup index many points. In particular, this holds
at points with trivial stabilizer in the larger group. Such fibres give the unramified count
used in the global degree formula. For an infinite index, both sides of the cardinality theorem
are zero by Mathlib's `Nat.card` and subgroup-index conventions. The group-theoretic coset
equivalence is in
`TauCeti.GroupTheory.DoubleCoset.Fiber`.
-/

public noncomputable section

open MulAction UpperHalfPlane
open scoped MatrixGroups

namespace Subgroup

variable {Δ Γ : Subgroup PSL(2, ℝ)}

/-- Over an interior orbit, the compactified fibre has cardinality `[Γ : Δ]` when
the stabilizer acts trivially on the cosets of `Δ` in `Γ`. -/
theorem card_fiber_compactifiedQuotientMap_of_stabilizer_le_normalCore (h : Δ ≤ Γ)
    (z : ℍ) (hz : stabilizer Γ z ≤ (Δ.subgroupOf Γ).normalCore) :
    Nat.card {y : Δ.CompactifiedQuotient //
      compactifiedQuotientMap h y = .ofQuotient (Quotient.mk'' z)} =
      (Δ.subgroupOf Γ).index := by
  rw [← Nat.card_congr (orbitFiberEquivCompactifiedFiber h (Quotient.mk'' z))]
  exact TauCeti.card_fiber_orbitRel_map_of_stabilizer_le_normalCore h z hz

/-- The fibre of the compactified quotient map over a free interior point has cardinality
`[Γ : Δ]`. -/
theorem card_fiber_compactifiedQuotientMap_of_stabilizer_eq_bot (h : Δ ≤ Γ)
    (z : ℍ) (hz : stabilizer Γ z = ⊥) :
    Nat.card {y : Δ.CompactifiedQuotient //
      compactifiedQuotientMap h y = .ofQuotient (Quotient.mk'' z)} =
      (Δ.subgroupOf Γ).index := by
  apply card_fiber_compactifiedQuotientMap_of_stabilizer_le_normalCore h z
  simpa only [hz] using (bot_le : (⊥ : Subgroup Γ) ≤ (Δ.subgroupOf Γ).normalCore)

end Subgroup
