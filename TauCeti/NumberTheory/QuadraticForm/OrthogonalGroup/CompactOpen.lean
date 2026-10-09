/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Nat.Prime.Basic
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.BaseChange
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Closed
public import TauCeti.Topology.Algebra.QuadraticForm.OrthogonalGroup.SpecialOrthogonal
public import Mathlib.NumberTheory.Padics.ProperSpace
import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Projection

/-!
# Compatible compact-open subgroups for orthogonal and Spin groups

A restricted product of the local orthogonal, special orthogonal, and Spin groups needs compatible
reference subgroups at every prime. The independent data are a compact-open subgroup of the local
orthogonal group and one of the local Spin group. The special orthogonal subgroup is derived by
intersecting the orthogonal subgroup with `SO`, and compatibility asks that the local Spin
projection land in this intersection.

This file packages the independent families, their compactness and openness, the almost-everywhere
integrality of rational points, and the compatibility condition. It derives the special orthogonal
family, its membership criterion, its openness and compactness, the restricted Spin projection,
and almost-everywhere integrality for rational special orthogonal points. In particular, no
separately chosen special orthogonal family can drift away from the orthogonal family.

New tuples are obtained from old ones by shrinking: intersecting the orthogonal reference
subgroups with open subgroups `W p` that contain them at almost every prime, and the Spin ones
with the preimages of the `W p`, gives a compatible tuple agreeing with the original at almost
every prime. This is how tuples differing at finitely many primes, such as level structures at a
single prime, arise.

The topology on every group is the canonical one inherited from the ambient finite-dimensional
algebra; the package stores no topology of its own.

## Main definitions

* `TauCeti.QuadraticMap.OrthogonalCompactOpens`: compatible orthogonal and Spin compact-open
  reference families for a rational quadratic space.
* `TauCeti.QuadraticMap.OrthogonalCompactOpens.specialOrthogonal`: the derived local special
  orthogonal family.
* `TauCeti.QuadraticMap.OrthogonalCompactOpens.spinToSpecialOrthogonal`: the local Spin projection
  restricted to the reference subgroups.
* `TauCeti.QuadraticMap.OrthogonalCompactOpens.infOpenSubgroup`: the shrinking of a tuple by a
  family of open subgroups of the local orthogonal groups.

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
/-- The derived special orthogonal reference subgroup is compact, being the preimage of a compact
subgroup under the closed embedding `SO(Q_p) → O(Q_p)`. -/
theorem isCompact_specialOrthogonal (p : Nat.Primes) :
    IsCompact (U.specialOrthogonal p : Set (specialOrthogonalGroup (Q.baseChange ℚ_[p]))) :=
  (_root_.QuadraticMap.isClosedEmbedding_specialOrthogonalToOrthogonal
    (Q.baseChange ℚ_[p])).isCompact_preimage (U.isCompact_orthogonal p)

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

omit [FiniteDimensional ℚ V] in
/-- A Spin reference point acts through an orthogonal reference point. -/
theorem spinToOrthogonal_mem_orthogonal (p : Nat.Primes) {x : spinGroup (Q.baseChange ℚ_[p])}
    (hx : x ∈ U.spin p) :
    CliffordAlgebra.spinToOrthogonal (Q.baseChange ℚ_[p]) x ∈ U.orthogonal p := by
  rw [← CliffordAlgebra.specialOrthogonalToOrthogonal_spinToSpecialOrthogonal]
  exact U.spin_maps p hx

omit [FiniteDimensional ℚ V] in
/-- Shrinking the orthogonal reference subgroups shrinks the derived special orthogonal ones. -/
theorem specialOrthogonal_mono {U U' : OrthogonalCompactOpens Q}
    (h : ∀ p, U.orthogonal p ≤ U'.orthogonal p) (p : Nat.Primes) :
    U.specialOrthogonal p ≤ U'.specialOrthogonal p :=
  Subgroup.comap_mono (h p)

omit [FiniteDimensional ℚ V] in
/-- Orthogonal reference families agreeing at almost every prime have derived special orthogonal
families agreeing at almost every prime. -/
theorem eventually_specialOrthogonal_eq {U U' : OrthogonalCompactOpens Q}
    (h : ∀ᶠ p in cofinite, U.orthogonal p = U'.orthogonal p) :
    ∀ᶠ p in cofinite, U.specialOrthogonal p = U'.specialOrthogonal p :=
  h.mono fun p hp ↦ by rw [specialOrthogonal, specialOrthogonal, hp]

/-! ### Shrinking a compatible tuple at finitely many primes -/

/-- Intersect the orthogonal reference subgroups of `U` with open subgroups `W p` of the local
orthogonal groups, and the Spin reference subgroups with the preimages of the `W p`. When
`U.orthogonal p ≤ W p` at almost every prime, as for a family `W` that is `⊤` away from finitely
many primes, the result is again a compatible compact-open tuple. It agrees with `U` at almost
every prime and is contained in `U` at every prime. -/
def infOpenSubgroup (W : ∀ p : Nat.Primes, OpenSubgroup (orthogonalGroup (Q.baseChange ℚ_[p])))
    (hW : ∀ᶠ p in cofinite, U.orthogonal p ≤ W p) : OrthogonalCompactOpens Q where
  orthogonal p := U.orthogonal p ⊓ W p
  spin p := U.spin p ⊓
    (W p : Subgroup (orthogonalGroup (Q.baseChange ℚ_[p]))).comap
      (CliffordAlgebra.spinToOrthogonal (Q.baseChange ℚ_[p]))
  isOpen_orthogonal p := (U.isOpen_orthogonal p).inter (W p).isOpen
  isCompact_orthogonal p := (U.isCompact_orthogonal p).inter_right (W p).isClosed
  isOpen_spin p := (U.isOpen_spin p).inter
    ((W p).isOpen.preimage (CliffordAlgebra.continuous_spinToOrthogonal _))
  isCompact_spin p := (U.isCompact_spin p).inter_right
    ((W p).isClosed.preimage (CliffordAlgebra.continuous_spinToOrthogonal _))
  spin_maps p x hx := by
    refine ⟨U.spin_maps p hx.1, ?_⟩
    rw [SetLike.mem_coe, CliffordAlgebra.specialOrthogonalToOrthogonal_spinToSpecialOrthogonal]
    exact hx.2
  eventually_orthogonal g := by
    filter_upwards [U.eventually_orthogonal g, hW] with p hp hpW
    exact ⟨hp, hpW hp⟩
  eventually_spin x := by
    filter_upwards [U.eventually_spin x, hW] with p hp hpW
    exact ⟨hp, hpW (U.spinToOrthogonal_mem_orthogonal p hp)⟩

variable (W : ∀ p : Nat.Primes, OpenSubgroup (orthogonalGroup (Q.baseChange ℚ_[p])))
  (hW : ∀ᶠ p in cofinite, U.orthogonal p ≤ W p)

/-- The orthogonal reference subgroups of the shrunken tuple are the intersections with `W`. -/
@[simp]
theorem infOpenSubgroup_orthogonal (p : Nat.Primes) :
    (U.infOpenSubgroup W hW).orthogonal p = U.orthogonal p ⊓ W p :=
  (rfl)

/-- The Spin reference subgroups of the shrunken tuple are cut out by the preimages of `W`. -/
@[simp]
theorem infOpenSubgroup_spin (p : Nat.Primes) :
    (U.infOpenSubgroup W hW).spin p =
      U.spin p ⊓ (W p : Subgroup (orthogonalGroup (Q.baseChange ℚ_[p]))).comap
        (CliffordAlgebra.spinToOrthogonal (Q.baseChange ℚ_[p])) :=
  (rfl)

/-- The shrunken orthogonal reference subgroups are contained in those of `U`. -/
theorem infOpenSubgroup_orthogonal_le (p : Nat.Primes) :
    (U.infOpenSubgroup W hW).orthogonal p ≤ U.orthogonal p :=
  inf_le_left

/-- The shrunken Spin reference subgroups are contained in those of `U`. -/
theorem infOpenSubgroup_spin_le (p : Nat.Primes) :
    (U.infOpenSubgroup W hW).spin p ≤ U.spin p :=
  inf_le_left

/-- The shrunken tuple has the orthogonal reference subgroups of `U` at almost every prime. -/
theorem eventually_infOpenSubgroup_orthogonal_eq :
    ∀ᶠ p in cofinite, (U.infOpenSubgroup W hW).orthogonal p = U.orthogonal p :=
  hW.mono fun _ hp ↦ inf_eq_left.mpr hp

/-- The shrunken tuple has the Spin reference subgroups of `U` at almost every prime. -/
theorem eventually_infOpenSubgroup_spin_eq :
    ∀ᶠ p in cofinite, (U.infOpenSubgroup W hW).spin p = U.spin p := by
  filter_upwards [hW] with p hp
  exact inf_eq_left.mpr fun x hx ↦ hp (U.spinToOrthogonal_mem_orthogonal p hx)

end OrthogonalCompactOpens

end

end QuadraticMap
end TauCeti
