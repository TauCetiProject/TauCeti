/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PermutationTriple.EulerCharacteristic
public import TauCeti.Combinatorics.PermutationTriple.GeometryType
import TauCeti.Combinatorics.PermutationTriple.Examples
import TauCeti.Combinatorics.PermutationTriple.Decidable

/-!
# Executable invariants of permutation triples

The cycle counts, component orders, Euler characteristic, genus, and triangle-group geometry of
a finite permutation triple can all be computed from its executable full cycle data
`TauCeti.PermutationTriple.cycleData`. This file derives executable versions of those five
invariants and identifies each with its canonical mathematical definition.
Fixed points are included in the decomposition, and the empty multiset has least common multiple
one, so the order computation also applies in degree zero.

The genus computation preserves the canonical truncation on disconnected triples. Its geometric
interpretation still requires connectedness; in particular the empty triple has computed genus
one. All the definitions are executable with `#eval`. The numerical definitions are exposed so
ordinary importing modules can also reduce them with kernel `decide`; geometry is characterized
by its agreement theorem and the canonical reciprocal-sum API.

## References

* S. K. Lando and A. K. Zvonkin, *Graphs on Surfaces and Their Applications*, §1.5.
-/

public section

namespace TauCeti.PermutationTriple

variable {n : ℕ}

/-- The ordered numbers of cycles, including fixed points, computed from the full cycle data. -/
@[expose] def computedCycleCounts (t : PermutationTriple n) : ℕ × ℕ × ℕ :=
  (t.cycleData.1.card, t.cycleData.2.1.card, t.cycleData.2.2.card)

/-- The executable cycle counts agree with the canonical cycle counts. -/
@[simp] theorem computedCycleCounts_eq_cycleCounts (t : PermutationTriple n) :
    t.computedCycleCounts = t.cycleCounts := by
  rw [computedCycleCounts, cycleCounts_eq_card_cycleData]

/-- The ordered component orders, computed as least common multiples of their cycle lengths. -/
@[expose] def computedOrderTriple (t : PermutationTriple n) : ℕ × ℕ × ℕ :=
  (t.cycleData.1.lcm, t.cycleData.2.1.lcm, t.cycleData.2.2.lcm)

/-- The executable component orders agree with the canonical order triple. -/
@[simp] theorem computedOrderTriple_eq_orderTriple (t : PermutationTriple n) :
    t.computedOrderTriple = t.orderTriple := by
  rw [computedOrderTriple, orderTriple_eq_lcm_cycleData]

/-- The Euler characteristic, computed as the total number of cycles less the degree. -/
@[expose] def computedEulerChar (t : PermutationTriple n) : ℤ :=
  (t.computedCycleCounts.1 : ℤ) + t.computedCycleCounts.2.1 + t.computedCycleCounts.2.2 - n

/-- The executable Euler characteristic agrees with the canonical Euler characteristic. -/
@[simp] theorem computedEulerChar_eq_eulerChar (t : PermutationTriple n) :
    t.computedEulerChar = t.eulerChar := by
  rw [computedEulerChar, computedCycleCounts_eq_cycleCounts, eulerChar_eq_cycleCounts]

/-- The genus computed from the Euler characteristic, with the same truncation as the canonical
definition on disconnected triples. -/
@[expose] def computedGenus (t : PermutationTriple n) : ℕ :=
  ((2 - t.computedEulerChar) / 2).toNat

/-- The executable genus agrees with the canonical genus, including on disconnected triples. -/
@[simp] theorem computedGenus_eq_genus (t : PermutationTriple n) :
    t.computedGenus = t.genus := by
  rw [computedGenus, computedEulerChar_eq_eulerChar, genus_def]

/-- The triangle-group geometry computed by exact rational arithmetic from the component orders. -/
def computedGeometryType (t : PermutationTriple n) : GeometryType :=
  GeometryType.ofOrders
    ((⟨t.computedOrderTriple.1, by
        simpa only [computedOrderTriple_eq_orderTriple, orderTriple_σ0] using
          orderOf_pos t.σ0⟩ : ℕ+),
      (⟨t.computedOrderTriple.2.1, by
        simpa only [computedOrderTriple_eq_orderTriple, orderTriple_σ1] using
          orderOf_pos t.σ1⟩ : ℕ+),
      (⟨t.computedOrderTriple.2.2, by
        simpa only [computedOrderTriple_eq_orderTriple, orderTriple_σinf] using
          orderOf_pos t.σinf⟩ : ℕ+))

/-- The executable triangle-group geometry agrees with the canonical geometry type. -/
@[simp] theorem computedGeometryType_eq_geometryType (t : PermutationTriple n) :
    t.computedGeometryType = t.geometryType := by
  cases h : t.geometryType <;>
    simpa [computedGeometryType, computedOrderTriple_eq_orderTriple] using h

/-! ### Small computations

The examples include an empty triple and a disconnected triple, whose computed genus records
the canonical truncation, and connected Euclidean and hyperbolic triples.
-/

open Equiv

example : (cyclicTriple 0).cycleData = (0, 0, 0) ∧
    (cyclicTriple 0).computedCycleCounts = (0, 0, 0) ∧
    (cyclicTriple 0).computedOrderTriple = (1, 1, 1) ∧
    (cyclicTriple 0).computedEulerChar = 0 ∧ (cyclicTriple 0).computedGenus = 1 := by
  decide +kernel

example : (cyclicTriple 1).cycleData = ({1}, {1}, {1}) ∧
    (cyclicTriple 1).computedCycleCounts = (1, 1, 1) ∧
    (cyclicTriple 1).computedOrderTriple = (1, 1, 1) ∧
    (cyclicTriple 1).computedEulerChar = 2 ∧ (cyclicTriple 1).computedGenus = 0 := by
  decide +kernel

example : (1 : PermutationTriple 2).cycleData = ({1, 1}, {1, 1}, {1, 1}) ∧
    (1 : PermutationTriple 2).computedCycleCounts = (2, 2, 2) ∧
    (1 : PermutationTriple 2).computedOrderTriple = (1, 1, 1) ∧
    (1 : PermutationTriple 2).computedEulerChar = 4 ∧
    (1 : PermutationTriple 2).computedGenus = 0 := by
  decide +kernel

example : torusTriple.cycleData = ({4}, {4}, {2, 2}) ∧
    torusTriple.computedCycleCounts = (1, 1, 2) ∧
    torusTriple.computedOrderTriple = (4, 4, 2) ∧
    torusTriple.computedEulerChar = 0 ∧ torusTriple.computedGenus = 1 := by
  decide +kernel

-- A connected degree-four triple of orders `(3, 4, 4)`, whose reciprocal sum is `5/6`.
private def hyperbolicExample : PermutationTriple 4 :=
  ofTwo (Equiv.swap 0 1 * Equiv.swap 1 2) (finRotate 4)

example : hyperbolicExample.cycleData = ({3, 1}, {4}, {4}) ∧
    hyperbolicExample.computedCycleCounts = (2, 1, 1) ∧
    hyperbolicExample.computedOrderTriple = (3, 4, 4) ∧
    hyperbolicExample.computedEulerChar = 0 ∧ hyperbolicExample.computedGenus = 1 := by
  decide +kernel

example : hyperbolicExample.IsConnected := by decide +kernel

example : torusTriple.computedGeometryType = .euclidean := by simp [geometryType_torusTriple]

example : hyperbolicExample.computedGeometryType = .hyperbolic := by
  rw [computedGeometryType_eq_geometryType, geometryType_eq_hyperbolic_iff]
  have h : hyperbolicExample.computedOrderTriple = (3, 4, 4) := by decide +kernel
  simp only [computedOrderTriple_eq_orderTriple, Prod.ext_iff, orderTriple_σ0, orderTriple_σ1,
    orderTriple_σinf] at h
  norm_num [h.1, h.2.1, h.2.2]

end TauCeti.PermutationTriple
