/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PermutationTriple.Basic
public import TauCeti.GroupTheory.Perm.OrbitCount

/-!
# Cycle data of permutation triples

The cycle data of a permutation triple records, in the ordered branch-point convention
`0, 1, ∞`, the full cycle partition of each component. These are the parts of Mathlib's
`Equiv.Perm.partition`, rather than `Equiv.Perm.cycleType`: fixed points therefore appear as
parts equal to one.

`TauCeti.PermutationTriple.cycleData` packages the three partitions and
`TauCeti.PermutationTriple.cycleCounts` packages their numbers of parts. The latter is expressed
using `TauCeti.orbitCount`, and `cycleCounts_eq_card_cycleData` identifies the two descriptions.
The remaining results record that every partition sums to the degree and that both invariants are
unchanged by simultaneous relabeling, transport of the sheet type, inversion of the convention,
and isomorphism of triples.

## References

* S. K. Lando, A. K. Zvonkin, *Graphs on Surfaces and Their Applications*, Encyclopaedia of
  Mathematical Sciences 141, Springer 2004, §1.1 and §1.5.
-/

public section

namespace TauCeti

open Equiv Equiv.Perm

namespace PermutationTriple

variable {n m : ℕ}

/-- The ordered full cycle partitions of the three components of a permutation triple. Fixed
points occur as parts equal to one. -/
noncomputable def cycleData (t : PermutationTriple n) :
    Multiset ℕ × Multiset ℕ × Multiset ℕ :=
  (t.σ0.partition.parts, t.σ1.partition.parts, t.σinf.partition.parts)

@[simp]
theorem cycleData_σ0 (t : PermutationTriple n) :
    t.cycleData.1 = t.σ0.partition.parts := (rfl)

@[simp]
theorem cycleData_σ1 (t : PermutationTriple n) :
    t.cycleData.2.1 = t.σ1.partition.parts := (rfl)

@[simp]
theorem cycleData_σinf (t : PermutationTriple n) :
    t.cycleData.2.2 = t.σinf.partition.parts := (rfl)

/-- The ordered numbers of cycles of the three components, with fixed points included. -/
noncomputable def cycleCounts (t : PermutationTriple n) : ℕ × ℕ × ℕ :=
  (orbitCount t.σ0, orbitCount t.σ1, orbitCount t.σinf)

@[simp]
theorem cycleCounts_σ0 (t : PermutationTriple n) : t.cycleCounts.1 = orbitCount t.σ0 := (rfl)

@[simp]
theorem cycleCounts_σ1 (t : PermutationTriple n) : t.cycleCounts.2.1 = orbitCount t.σ1 := (rfl)

@[simp]
theorem cycleCounts_σinf (t : PermutationTriple n) :
    t.cycleCounts.2.2 = orbitCount t.σinf := (rfl)

/-- The cycle counts of a triple are the cardinalities of its three full cycle partitions. -/
theorem cycleCounts_eq_card_cycleData (t : PermutationTriple n) :
    t.cycleCounts = (t.cycleData.1.card, t.cycleData.2.1.card, t.cycleData.2.2.card) := by
  simp only [cycleCounts, cycleData, orbitCount_eq_card_parts_partition]

/-- Each full cycle partition of a degree-`n` triple sums to `n`. -/
theorem cycleData_sums (t : PermutationTriple n) :
    (t.cycleData.1.sum, t.cycleData.2.1.sum, t.cycleData.2.2.sum) = (n, n, n) := by
  simp only [cycleData]
  rw [t.σ0.partition.parts_sum, t.σ1.partition.parts_sum, t.σinf.partition.parts_sum]
  simp

/-- Simultaneous relabeling leaves the ordered cycle data unchanged. -/
@[simp]
theorem cycleData_smul (τ : Perm (Fin n)) (t : PermutationTriple n) :
    cycleData (τ • t) = cycleData t := by
  simp [cycleData]

/-- Simultaneous relabeling leaves all three cycle counts unchanged. -/
@[simp]
theorem cycleCounts_smul (τ : Perm (Fin n)) (t : PermutationTriple n) :
    cycleCounts (τ • t) = cycleCounts t := by
  simp [cycleCounts]

/-- Transporting the labels of the sheets leaves the ordered cycle data unchanged. -/
@[simp]
theorem cycleData_transport (e : Fin n ≃ Fin m) (t : PermutationTriple n) :
    cycleData (transport e t) = cycleData t := by
  simp [cycleData]

/-- Transporting the labels of the sheets leaves all three cycle counts unchanged. -/
@[simp]
theorem cycleCounts_transport (e : Fin n ≃ Fin m) (t : PermutationTriple n) :
    cycleCounts (transport e t) = cycleCounts t := by
  simp [cycleCounts]

/-- Inverting all three components, as in the passage to the opposite composition convention,
leaves the ordered cycle data unchanged. -/
theorem cycleData_inv_components (t : PermutationTriple n) :
    (t.σ0⁻¹.partition.parts, t.σ1⁻¹.partition.parts, t.σinf⁻¹.partition.parts) =
      cycleData t := by
  simp [cycleData]

/-- Inverting all three components leaves their ordered numbers of cycles unchanged. -/
theorem cycleCounts_inv_components (t : PermutationTriple n) :
    (orbitCount t.σ0⁻¹, orbitCount t.σ1⁻¹, orbitCount t.σinf⁻¹) = cycleCounts t := by
  simp [cycleCounts]

/-- Isomorphic permutation triples have the same ordered cycle data. -/
theorem cycleData_eq_of_equivalent {t t' : PermutationTriple n} (h : Equivalent t t') :
    cycleData t = cycleData t' := by
  obtain ⟨τ, rfl⟩ := equivalent_iff_exists_smul_eq.mp h
  exact (cycleData_smul τ t).symm

/-- Isomorphic permutation triples have the same ordered numbers of cycles. -/
theorem cycleCounts_eq_of_equivalent {t t' : PermutationTriple n} (h : Equivalent t t') :
    cycleCounts t = cycleCounts t' := by
  obtain ⟨τ, rfl⟩ := equivalent_iff_exists_smul_eq.mp h
  exact (cycleCounts_smul τ t).symm

end PermutationTriple

end TauCeti
