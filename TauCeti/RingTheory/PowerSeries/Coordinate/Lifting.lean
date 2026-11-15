/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.Coordinate.Basic
public import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Lifting formal coordinates

A coordinate can be lifted along a surjective coefficient map as soon as its linear
coefficient can be lifted to a unit. The higher coefficients lift independently. In
particular, strict coordinates lift along every surjection, whereas arbitrary coordinates
lift precisely when both coefficients and units lift. Surjective local homomorphisms
satisfy this criterion.

The prescribed-linear-coefficient version allows a coordinate on a special fibre to be
lifted without imposing strictness on the lift. This is needed when replacing a marked
formal group deformation by a law with its special fibre fixed in a specified coordinate.
-/

public section

namespace TauCeti.FormalCoordinate

open PowerSeries

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Lift a coordinate with a prescribed unit linear coefficient. No unit-lifting hypothesis
is needed for the other coefficients. -/
theorem exists_map_eq_and_linearCoeff_eq (f : R →+* S) (hf : Function.Surjective f)
    (ψ : FormalCoordinate S) (u : Rˣ) (hu : Units.map f.toMonoidHom u = linearCoeff ψ) :
    ∃ φ : FormalCoordinate R, map f φ = ψ ∧ linearCoeff φ = u := by
  classical
  choose a ha using fun n ↦ hf (coeff n ψ.toPowerSeries)
  let φ : FormalCoordinate R :=
    { toPowerSeries := PowerSeries.mk fun n ↦
        if n = 0 then 0 else if n = 1 then (u : R) else a n
      constantCoeff_toPowerSeries := by simp
      isUnit_coeff_one := by simp }
  refine ⟨φ, FormalCoordinate.ext (PowerSeries.ext fun n ↦ ?_), Units.ext ?_⟩
  · simp only [toPowerSeries_map, coeff_map]
    rcases n with _ | _ | n
    · simp [φ]
    · simpa [φ] using congrArg Units.val hu
    · simpa [φ] using ha (n + 2)
  · simp [φ, val_linearCoeff]

/-- Strict coordinates lift along every surjection, with a strict lift. -/
theorem exists_strict_map_eq (f : R →+* S) (hf : Function.Surjective f)
    (ψ : FormalCoordinate S) (hψ : linearCoeff ψ = 1) :
    ∃ φ : FormalCoordinate R, map f φ = ψ ∧ linearCoeff φ = 1 :=
  exists_map_eq_and_linearCoeff_eq f hf ψ 1 (by simp [hψ])

/-- Base change is surjective on formal coordinates exactly when it is surjective on
coefficients and on units. The unit condition cannot be dropped for general ring maps. -/
theorem map_surjective_iff (f : R →+* S) :
    Function.Surjective (map f) ↔
      Function.Surjective f ∧ Function.Surjective (Units.map f.toMonoidHom) := by
  constructor
  · intro h
    constructor
    · intro s
      obtain ⟨φ, hφ⟩ := h (ofStrictCoeffs fun _ ↦ s)
      refine ⟨coeff 2 φ.toPowerSeries, ?_⟩
      have hc := congrArg (fun ψ ↦ coeff 2 ψ.toPowerSeries) hφ
      simpa only [toPowerSeries_map, coeff_map] using
        hc.trans (coeff_succ_ofStrictCoeffs (fun _ ↦ s) 1)
    · intro u
      obtain ⟨φ, hφ⟩ := h (homothety u)
      refine ⟨linearCoeff φ, Units.ext ?_⟩
      have hc := congrArg (fun ψ ↦ coeff 1 ψ.toPowerSeries) hφ
      simpa [val_linearCoeff] using hc
  · rintro ⟨hf, hu⟩ ψ
    obtain ⟨u, hu⟩ := hu (linearCoeff ψ)
    obtain ⟨φ, hφ, -⟩ := exists_map_eq_and_linearCoeff_eq f hf ψ u hu
    exact ⟨φ, hφ⟩

/-- Every coordinate lifts along a surjective local homomorphism. This applies in particular
to reduction from a local ring to its residue field. -/
theorem map_surjective_of_isLocalHom (f : R →+* S) [IsLocalHom f]
    (hf : Function.Surjective f) : Function.Surjective (map f) :=
  (map_surjective_iff f).2
    ⟨hf, IsLocalRing.surjective_units_map_of_local_ringHom f hf inferInstance⟩

end TauCeti.FormalCoordinate
