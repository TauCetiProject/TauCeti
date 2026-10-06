/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Nat.Prime.Basic
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.BaseChange
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Closed
public import TauCeti.Topology.Algebra.QuadraticForm.OrthogonalGroup.Closed
public import Mathlib.NumberTheory.Padics.ProperSpace

/-!
# Compatible compact-open subgroups for orthogonal and Spin groups

A restricted product of the local orthogonal, special orthogonal, and Spin groups needs compatible
reference subgroups at every prime. The independent data are a compact-open subgroup of the local
orthogonal group and one of the local Spin group. The special orthogonal subgroup is derived by
intersecting the orthogonal subgroup with `SO`, and compatibility asks that the local Spin
projection land in this intersection.

This file packages the independent families, their compactness and openness, the almost-everywhere
integrality of rational points, and the compatibility condition. It derives the special orthogonal
family, its membership criterion, its openness, the restricted Spin projection, and
almost-everywhere integrality for rational special orthogonal points. In particular, no separately
chosen special orthogonal family can drift away from the orthogonal family.

The topology on every group is the canonical one inherited from the ambient finite-dimensional
algebra; the package stores no topology of its own.

## Main definitions

* `TauCeti.QuadraticMap.OrthogonalCompactOpens`: compatible orthogonal and Spin compact-open
  reference families for a rational quadratic space.
* `TauCeti.QuadraticMap.OrthogonalCompactOpens.specialOrthogonal`: the derived local special
  orthogonal family.
* `TauCeti.QuadraticMap.OrthogonalCompactOpens.spinToSpecialOrthogonal`: the local Spin projection
  restricted to the reference subgroups.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms* (1963), §101.
-/

public section

namespace TauCeti
namespace QuadraticMap

open Filter
open _root_.QuadraticMap
open scoped TensorProduct Topology

noncomputable section

/-- The canonical invertibility witness for two over the rationals. -/
local instance compactOpenInvertibleTwoRat : Invertible (2 : ℚ) :=
  invertibleOfNonzero two_ne_zero

variable {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]

/-- Compatible compact-open reference subgroups for the local orthogonal and Spin groups of a
rational quadratic space.

The special orthogonal reference subgroup is deliberately not a field: it is recovered as the
preimage of `orthogonal p` under `SO(Q_p) → O(Q_p)`. The compatibility field is phrased using
the Spin-to-special-orthogonal projection, so it supplies the restricted map needed by adelic
special orthogonal points rather than merely a map into the full orthogonal group. -/
@[ext]
structure OrthogonalCompactOpens (Q : QuadraticForm ℚ V) where
  /-- The compact-open reference subgroup of the local orthogonal group. -/
  orthogonal (p : Nat.Primes) : Subgroup (orthogonalGroup (Q.baseChange ℚ_[p]))
  /-- The compact-open reference subgroup of the local Spin group. -/
  spin (p : Nat.Primes) : Subgroup (spinGroup (Q.baseChange ℚ_[p]))
  /-- The local orthogonal reference subgroup is open. -/
  isOpen_orthogonal (p : Nat.Primes) :
    IsOpen (orthogonal p : Set (orthogonalGroup (Q.baseChange ℚ_[p])))
  /-- The local orthogonal reference subgroup is compact. -/
  isCompact_orthogonal (p : Nat.Primes) :
    IsCompact (orthogonal p : Set (orthogonalGroup (Q.baseChange ℚ_[p])))
  /-- The local Spin reference subgroup is open. -/
  isOpen_spin (p : Nat.Primes) :
    IsOpen (spin p : Set (spinGroup (Q.baseChange ℚ_[p])))
  /-- The local Spin reference subgroup is compact. -/
  isCompact_spin (p : Nat.Primes) :
    IsCompact (spin p : Set (spinGroup (Q.baseChange ℚ_[p])))
  /-- Local Spin reference points map into the special orthogonal subgroup cut out by the
  orthogonal reference subgroup. -/
  spin_maps (p : Nat.Primes) :
    Set.MapsTo (CliffordAlgebra.spinToSpecialOrthogonal (Q.baseChange ℚ_[p])) (spin p)
      ((orthogonal p).comap (specialOrthogonalToOrthogonal (Q.baseChange ℚ_[p])))
  /-- Every rational orthogonal point belongs to the reference subgroup at almost every prime. -/
  eventually_orthogonal (g : orthogonalGroup Q) :
    ∀ᶠ p : Nat.Primes in cofinite,
      orthogonalGroupBaseChange (A := ℚ_[p]) Q g ∈ orthogonal p
  /-- Every rational Spin point belongs to the reference subgroup at almost every prime. -/
  eventually_spin (x : spinGroup Q) :
    ∀ᶠ p : Nat.Primes in cofinite,
      CliffordAlgebra.spinGroupBaseChange (A := ℚ_[p]) Q x ∈ spin p

namespace OrthogonalCompactOpens

variable {Q : QuadraticForm ℚ V} (U : OrthogonalCompactOpens Q)

/-- The special orthogonal reference subgroup derived from the orthogonal one. -/
def specialOrthogonal (p : Nat.Primes) :
    Subgroup (specialOrthogonalGroup (Q.baseChange ℚ_[p])) :=
  (U.orthogonal p).comap (specialOrthogonalToOrthogonal (Q.baseChange ℚ_[p]))

omit [FiniteDimensional ℚ V] in
/-- A local special orthogonal point belongs to the derived reference subgroup exactly when its
image in the orthogonal group belongs to the orthogonal reference subgroup. -/
@[simp]
theorem mem_specialOrthogonal_iff (p : Nat.Primes)
    (g : specialOrthogonalGroup (Q.baseChange ℚ_[p])) :
    g ∈ U.specialOrthogonal p ↔
      specialOrthogonalToOrthogonal (Q.baseChange ℚ_[p]) g ∈ U.orthogonal p :=
  Iff.rfl

omit [FiniteDimensional ℚ V] in
/-- The derived special orthogonal reference subgroup is open, being the preimage of an open
subgroup under the continuous inclusion `SO(Q_p) → O(Q_p)`. -/
theorem isOpen_specialOrthogonal (p : Nat.Primes) :
    IsOpen (U.specialOrthogonal p : Set (specialOrthogonalGroup (Q.baseChange ℚ_[p]))) :=
  (U.isOpen_orthogonal p).preimage
    (_root_.QuadraticMap.continuous_specialOrthogonalToOrthogonal (Q.baseChange ℚ_[p]))

omit [FiniteDimensional ℚ V] in
/-- The local Spin projection carries the Spin reference subgroup into the derived special
orthogonal reference subgroup. -/
theorem mapsTo_specialOrthogonal (p : Nat.Primes) :
    Set.MapsTo (CliffordAlgebra.spinToSpecialOrthogonal (Q.baseChange ℚ_[p]))
      (U.spin p) (U.specialOrthogonal p) := by
  simpa only [specialOrthogonal] using U.spin_maps p

/-- The Spin-to-special-orthogonal projection restricted to the compatible local reference
subgroups. -/
def spinToSpecialOrthogonal (p : Nat.Primes) :
    U.spin p →* U.specialOrthogonal p :=
  ((CliffordAlgebra.spinToSpecialOrthogonal (Q.baseChange ℚ_[p])).comp
      (U.spin p).subtype).codRestrict (U.specialOrthogonal p)
    (fun x ↦ U.mapsTo_specialOrthogonal p x.2)

omit [FiniteDimensional ℚ V] in
/-- The restricted local Spin projection has the same value as the ambient projection. -/
@[simp]
theorem coe_spinToSpecialOrthogonal_apply (p : Nat.Primes) (x : U.spin p) :
    (U.spinToSpecialOrthogonal p x :
      specialOrthogonalGroup (Q.baseChange ℚ_[p])) =
      CliffordAlgebra.spinToSpecialOrthogonal (Q.baseChange ℚ_[p]) x := by
  simp only [spinToSpecialOrthogonal, MonoidHom.codRestrict_apply, MonoidHom.comp_apply]
  rw [Subgroup.subtype_apply]

/-- Every rational special orthogonal point belongs to the derived reference subgroup at almost
every prime. This is a consequence of orthogonal integrality, not additional data. -/
theorem eventually_specialOrthogonal (g : specialOrthogonalGroup Q) :
    ∀ᶠ p : Nat.Primes in cofinite,
      specialOrthogonalGroupBaseChange (A := ℚ_[p]) Q g ∈ U.specialOrthogonal p := by
  filter_upwards [U.eventually_orthogonal
    (_root_.QuadraticMap.specialOrthogonalToOrthogonal Q g)] with p hp
  rw [mem_specialOrthogonal_iff, specialOrthogonalToOrthogonal_specialOrthogonalGroupBaseChange]
  exact hp

end OrthogonalCompactOpens

end

end QuadraticMap
end TauCeti
