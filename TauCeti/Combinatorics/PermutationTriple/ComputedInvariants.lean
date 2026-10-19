/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PermutationTriple.EulerCharacteristic
public import TauCeti.Combinatorics.PermutationTriple.GeometryType
public import TauCeti.GroupTheory.Perm.ComputedCycleType
import TauCeti.Combinatorics.PermutationTriple.Examples
import TauCeti.Combinatorics.PermutationTriple.Decidable

/-!
# Executable invariants of permutation triples

The canonical cycle data of a permutation triple is executable using
`Equiv.Perm.computedCycleType`, whose finite search lists one length at the least element of each
cycle. This file gives executable cycle counts, Euler characteristic, genus, order triple, and
geometry type, each identified with its canonical mathematical counterpart. Fixed points are
included, and the empty multiset has least common multiple one, so the order computation also
applies in degree zero.

The genus computation preserves the canonical truncation on disconnected triples. Its geometric
interpretation still requires connectedness; in particular the empty triple has computed genus
one. The definitions are exposed so ordinary importing modules can reduce them with kernel
`decide`, as well as evaluating them with `#eval`.

Computations can use the definitions in this file, while mathematical statements continue to use
`PermutationTriple.cycleCounts`, `PermutationTriple.eulerChar`, `PermutationTriple.genus`,
`PermutationTriple.orderTriple`, and `PermutationTriple.geometryType`.

## Main declarations

* `TauCeti.PermutationTriple.computedCycleCounts`: the cardinalities of the three full cycle
  decompositions.
* `TauCeti.PermutationTriple.computedEulerChar`: the Euler characteristic computed from the
  cardinalities of the three executable cycle decompositions.
* `TauCeti.PermutationTriple.computedGenus`: the genus computed from `computedEulerChar`.
* `TauCeti.PermutationTriple.computedOrderTriple`: the least common multiples of the three
  executable cycle decompositions.
* `TauCeti.PermutationTriple.computedGeometryType`: the exact rational trichotomy computed from
  `computedOrderTriple`.

## References

* S. K. Lando and A. K. Zvonkin, *Graphs on Surfaces and Their Applications*, §1.5.
-/

public section

namespace TauCeti

namespace PermutationTriple

variable {n : ℕ}

/-- The ordered numbers of cycles, including fixed points, computed from the full cycle data. -/
@[expose] def computedCycleCounts (t : PermutationTriple n) : ℕ × ℕ × ℕ :=
  (t.cycleData.1.card, t.cycleData.2.1.card, t.cycleData.2.2.card)

/-- The executable cycle counts agree with the canonical cycle counts. -/
@[simp]
theorem computedCycleCounts_eq (t : PermutationTriple n) :
    t.computedCycleCounts = t.cycleCounts := by
  rw [computedCycleCounts, cycleCounts_eq_card_cycleData]

/-- The Euler characteristic of a permutation triple, computed from its executable cycle
decompositions. -/
@[expose] def computedEulerChar (t : PermutationTriple n) : ℤ :=
  ((t.σ0.computedCycleType.card + t.σ1.computedCycleType.card +
    t.σinf.computedCycleType.card : ℕ) : ℤ) - n

/-- The executable Euler characteristic agrees with the canonical Euler characteristic. -/
@[simp]
theorem computedEulerChar_eq (t : PermutationTriple n) :
    t.computedEulerChar = t.eulerChar := by
  rw [computedEulerChar, eulerChar_def]
  simp only [Equiv.Perm.computedCycleType_eq_fullCycleType, Equiv.Perm.fullCycleType_def,
    ← Equiv.Perm.orbitCount_eq_card_parts_partition]
  push_cast
  rfl

/-- The genus of a permutation triple, computed from its executable Euler characteristic. As for
`PermutationTriple.genus`, this has its geometric meaning when the triple is connected. -/
@[expose] def computedGenus (t : PermutationTriple n) : ℕ :=
  ((2 - t.computedEulerChar) / 2).toNat

/-- The executable genus agrees with the canonical genus. -/
@[simp]
theorem computedGenus_eq (t : PermutationTriple n) : t.computedGenus = t.genus := by
  rw [computedGenus, genus_def, computedEulerChar_eq]

/-- The ordered triple of component orders, computed as the least common multiples of the three
executable cycle decompositions. -/
@[expose] def computedOrderTriple (t : PermutationTriple n) : ℕ × ℕ × ℕ :=
  (t.σ0.computedCycleType.lcm, t.σ1.computedCycleType.lcm,
    t.σinf.computedCycleType.lcm)

/-- The executable order triple agrees with the canonical order triple. -/
@[simp]
theorem computedOrderTriple_eq (t : PermutationTriple n) :
    t.computedOrderTriple = t.orderTriple := by
  rw [computedOrderTriple, orderTriple_eq_lcm_cycleData]
  simp only [Equiv.Perm.computedCycleType_eq_fullCycleType, Equiv.Perm.fullCycleType_def,
    cycleData_σ0, cycleData_σ1, cycleData_σinf]

/-- The spherical, Euclidean, or hyperbolic geometry type computed from the executable order
triple by exact comparison in `ℚ`. -/
@[expose] def computedGeometryType (t : PermutationTriple n) : GeometryType :=
  let o := t.computedOrderTriple
  let s : ℚ := (o.1 : ℚ)⁻¹ + (o.2.1 : ℚ)⁻¹ + (o.2.2 : ℚ)⁻¹
  if 1 < s then .spherical else if s = 1 then .euclidean else .hyperbolic

/-- The executable geometry type agrees with the canonical geometry type. -/
@[simp]
theorem computedGeometryType_eq (t : PermutationTriple n) :
    t.computedGeometryType = t.geometryType := by
  rw [computedGeometryType, computedOrderTriple_eq]
  simp only [orderTriple_σ0, orderTriple_σ1, orderTriple_σinf]
  cases hgeom : t.geometryType
  · have hlt := (geometryType_eq_spherical_iff t).mp hgeom
    simp [hlt]
  · have heq := (geometryType_eq_euclidean_iff t).mp hgeom
    simp [heq]
  · have hlt := (geometryType_eq_hyperbolic_iff t).mp hgeom
    simp [hlt.not_gt, hlt.ne]

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
  rw [computedGeometryType_eq, geometryType_eq_hyperbolic_iff]
  have h : hyperbolicExample.computedOrderTriple = (3, 4, 4) := by decide +kernel
  simp only [computedOrderTriple_eq, Prod.ext_iff, orderTriple_σ0, orderTriple_σ1,
    orderTriple_σinf] at h
  norm_num [h.1, h.2.1, h.2.2]

end PermutationTriple

end TauCeti
