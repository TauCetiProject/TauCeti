/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.UnitLocus
public import TauCeti.NumberTheory.Padics.Measure.Clopen.Basic
public import TauCeti.NumberTheory.Padics.Measure.PhiPsi

/-!
# Measures on the p-adic unit group

Restriction to the clopen unit locus, transported along `PadicInt.unitsHomeomorphIsUnit`, gives
`restrictUnits : D(ℤ_p, R) →ₗ[R] D(ℤ_pˣ, R)`. It is a left inverse of pushforward along the value
map. In the other order their composite is the ambient unit projector `unitRestriction`.
Consequently the measures on the unit group identify with the kernel of `psiMeasure` on ambient
measures. This lets intrinsic unit-group tests and ambient Amice calculations describe the same
measure. The comparison is linear: additive convolution on `ℤ_p` and multiplicative convolution
on `ℤ_pˣ` are different operations.

The construction uses the existing clopen restriction and pushforward APIs. Coefficients may be
any normed commutative ring, including the zero ring; no completeness or ultrametricity is needed.

## References

* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*, §3.5.3,
  Remark 3.31, Corollary 3.32 and Remark 3.33.
-/

public noncomputable section

open ContinuousMap

namespace AbstractMeasure

variable {p : ℕ} [Fact p.Prime] {R : Type*} [NormedCommRing R]

/-- Restrict an ambient measure to the intrinsic p-adic unit group. -/
def restrictUnits : D(ℤ_[p], R) →ₗ[R] D(ℤ_[p]ˣ, R) :=
  (arrowCongrLeft (PadicInt.unitsHomeomorphIsUnit p).symm).toLinearMap ∘ₗ
    restrictClopen (PadicInt.unitsClopen p)

/-- Unit restriction is clopen restriction followed by transport to the unit group. -/
theorem restrictUnits_eq_transport (μ : D(ℤ_[p], R)) :
    restrictUnits μ = arrowCongrLeft (PadicInt.unitsHomeomorphIsUnit p).symm
      (restrictClopen (PadicInt.unitsClopen p) μ) := (rfl)

/-- Restriction integrates a unit-group test by extending it by zero to the nonunits. -/
@[simp]
theorem restrictUnits_apply (μ : D(ℤ_[p], R)) (f : C(ℤ_[p]ˣ, R)) :
    restrictUnits μ f = μ (zeroExtendClopen R (PadicInt.unitsClopen p)
      (f.comp (PadicInt.unitsHomeomorphIsUnit p).symm)) := by
  rw [restrictUnits_eq_transport, arrowCongrLeft_apply, restrictClopen_apply]

/-- Restricting the pushforward of a unit-group measure recovers that measure. -/
@[simp]
theorem restrictUnits_map_val (ν : D(ℤ_[p]ˣ, R)) :
    restrictUnits (map ⟨Units.val, Units.continuous_val⟩ ν) = ν := by
  ext f
  rw [restrictUnits_apply, map_apply]
  congr 1
  ext u
  simp only [comp_apply, coe_mk]
  rw [zeroExtendClopen_apply_mem _ _ ((PadicInt.mem_unitsClopen p).mpr u.isUnit),
    comp_apply, ← PadicInt.unitsHomeomorphIsUnit_apply]
  exact congrArg f ((PadicInt.unitsHomeomorphIsUnit p).symm_apply_apply u)

/-- Including an intrinsic restriction is the ambient unit projector. -/
@[simp]
theorem map_val_restrictUnits (μ : D(ℤ_[p], R)) :
    map ⟨Units.val, Units.continuous_val⟩ (restrictUnits μ) = unitRestriction μ := by
  ext f
  rw [map_apply, restrictUnits_apply, unitRestriction_apply]
  congr 1
  ext x
  by_cases hx : IsUnit x
  · have hp : ¬(p : ℤ_[p]) ∣ x := by rwa [← PadicInt.not_isUnit_iff_dvd, not_not]
    rw [zeroExtendClopen_apply_mem _ _ ((PadicInt.mem_unitsClopen p).mpr hx)]
    simp [hp]
  · have hp : (p : ℤ_[p]) ∣ x := PadicInt.not_isUnit_iff_dvd.mp hx
    rw [zeroExtendClopen_apply_not_mem _ _ (by simpa using hx)]
    simp [hp]

/-- Inclusion of unit-group measures in ambient measures is injective. -/
theorem map_unitsVal_injective :
    Function.Injective (map ⟨Units.val, Units.continuous_val⟩ : D(ℤ_[p]ˣ, R) → D(ℤ_[p], R)) :=
  Function.LeftInverse.injective restrictUnits_map_val

/-- Restriction keeps a Dirac measure at a unit, with its intrinsic unit-group location. -/
@[simp]
theorem restrictUnits_dirac (u : ℤ_[p]ˣ) :
    restrictUnits (dirac R (u : ℤ_[p])) = dirac R u := by
  simpa only [map_dirac, coe_mk] using restrictUnits_map_val (dirac R u)

/-- Restriction kills a Dirac measure at a nonunit. -/
@[simp]
theorem restrictUnits_dirac_nonunit {x : ℤ_[p]} (hx : ¬IsUnit x) :
    restrictUnits (dirac R x) = 0 := by
  rw [restrictUnits_eq_transport, restrictClopen_dirac_not_mem _ (by simpa using hx), map_zero]

/-- Pushforward from the unit group has exactly the kernel of psi as its range. -/
theorem range_map_unitsVal :
    LinearMap.range (map ⟨Units.val, Units.continuous_val⟩ :
      D(ℤ_[p]ˣ, R) →ₗ[R] D(ℤ_[p], R)) = LinearMap.ker psiMeasure := by
  ext μ
  rw [LinearMap.mem_range, LinearMap.mem_ker,
    ← unitRestriction_eq_self_iff_psi_eq_zero]
  constructor
  · rintro ⟨ν, rfl⟩
    rw [← map_val_restrictUnits, restrictUnits_map_val]
  · intro h
    exact ⟨restrictUnits μ, (map_val_restrictUnits μ).trans h⟩

/-- Measures on the unit group are precisely the ambient measures killed by psi.
The forward map is pushforward along `Units.val`, and the inverse is intrinsic restriction. -/
def unitsMeasureEquivKerPsi : D(ℤ_[p]ˣ, R) ≃ₗ[R]
    LinearMap.ker (psiMeasure : D(ℤ_[p], R) →ₗ[R] D(ℤ_[p], R)) :=
  (LinearEquiv.ofInjective (map ⟨Units.val, Units.continuous_val⟩)
    map_unitsVal_injective).trans (LinearEquiv.ofEq _ _ range_map_unitsVal)

/-- The unit-measure equivalence includes the intrinsic measure into the ambient space. -/
@[simp]
theorem unitsMeasureEquivKerPsi_apply (ν : D(ℤ_[p]ˣ, R)) :
    (unitsMeasureEquivKerPsi ν : D(ℤ_[p], R)) = map ⟨Units.val, Units.continuous_val⟩ ν := (rfl)

/-- The inverse unit-measure equivalence restricts the ambient measure to the units. -/
@[simp]
theorem unitsMeasureEquivKerPsi_symm_apply
    (μ : LinearMap.ker (psiMeasure : D(ℤ_[p], R) →ₗ[R] D(ℤ_[p], R))) :
    unitsMeasureEquivKerPsi.symm μ = restrictUnits (μ : D(ℤ_[p], R)) := by
  have h := congrArg (restrictUnits (R := R))
    (congrArg Subtype.val (unitsMeasureEquivKerPsi.apply_symm_apply μ))
  simpa only [unitsMeasureEquivKerPsi_apply, restrictUnits_map_val] using h

-- Restriction discards the nonunit atom even though its location is nonzero.
example : restrictUnits (dirac ℤ (1 : ℤ_[3]) + 2 • dirac ℤ (3 : ℤ_[3])) =
    dirac ℤ (1 : ℤ_[3]ˣ) := by
  have h3 : ¬IsUnit (3 : ℤ_[3]) := PadicInt.p_nonunit
  rw [map_add, map_nsmul, restrictUnits_dirac_nonunit h3, smul_zero, add_zero]
  simpa only [Units.val_one] using restrictUnits_dirac (R := ℤ) (1 : ℤ_[3]ˣ)

example : restrictUnits (dirac ℤ (0 : ℤ_[2])) = 0 := by simp

example : (unitsMeasureEquivKerPsi (R := ℤ_[2]) (dirac ℤ_[2] (-1 : ℤ_[2]ˣ)) :
    D(ℤ_[2], ℤ_[2])) = dirac ℤ_[2] (-1 : ℤ_[2]) := by simp

end AbstractMeasure
