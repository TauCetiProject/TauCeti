/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PermutationTriple.EulerCharacteristic
public import TauCeti.Combinatorics.PermutationTriple.GeometryType
public import TauCeti.GroupTheory.Perm.ComputedCycleType

/-!
# Executable invariants of permutation triples

The canonical cycle data, Euler characteristic, genus, order triple, and geometry type of a
permutation triple are phrased using Mathlib's abstract permutation invariants.  This file gives
executable versions of the four derived numerical invariants.  They read the cycle lengths from
`Equiv.Perm.computedCycleType`, whose finite search lists one length at the least element of each
cycle.

Each computed invariant is identified with its canonical counterpart.  Computations can therefore
use the definitions in this file, while mathematical statements continue to use
`PermutationTriple.eulerChar`, `PermutationTriple.genus`, `PermutationTriple.orderTriple`, and
`PermutationTriple.geometryType`.

## Main declarations

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

end PermutationTriple

end TauCeti
