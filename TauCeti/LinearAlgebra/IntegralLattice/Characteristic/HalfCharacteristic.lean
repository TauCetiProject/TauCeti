/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Wentao Li
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Characteristic.Basic
public import TauCeti.LinearAlgebra.IntegralLattice.Characteristic.EvenSublattice
public import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Quadratic
public import TauCeti.LinearAlgebra.IntegralLattice.Overlattice.Basic

/-!
# Half-characteristic and lattice-vector classes in `A_(L_even)`

For an integral lattice `L` with even sublattice `L_even = L.evenSublattice`:

* Every lattice vector `x : L` lies in `(L_even)ᵛ` and defines a two-torsion class
  `L.latticeVectorClass x` in the discriminant group `A_(L_even)`, vanishing precisely when `x`
  has even integral norm.
* For any characteristic vector `w : L`, its half `(1 / 2) • w` lies in `(L_even)ᵛ` and defines
  the class `L.halfCharacteristicClass hw` in `A_(L_even)`.
* The discriminant quadratic form `q` of `L_even` evaluates `[w / 2]` and every translate
  `[e] + [w / 2]` (`e ∈ L`) to `w² / 8` modulo `1`.

This lightweight module provides the shared discriminant-class definitions needed by both
`TauCeti.LinearAlgebra.IntegralLattice.Characteristic.VanDerBlij` (which requires `Milgram`) and
`TauCeti.LinearAlgebra.IntegralLattice.Characteristic.ParityKernel` (which builds on
`VanDerBlij` for the characteristic-norm parity mod `2`).

## Main definitions

* `TauCeti.IntegralLattice.halfCharacteristicDual`,
  `TauCeti.IntegralLattice.halfCharacteristicClass`: `(1 / 2) • w` in `(L_even)ᵛ` and its class
  in `A_(L_even)`.
* `TauCeti.IntegralLattice.latticeVectorDual`,
  `TauCeti.IntegralLattice.latticeVectorClass`: a lattice vector `x : L` in `(L_even)ᵛ` and its
  class in `A_(L_even)`.

## Main results

* `TauCeti.IntegralLattice.halfCharacteristicClass_add_two_smul`: shifting `w` by `2 • e` shifts
  `[w / 2]` by `[e]`.
* `TauCeti.IntegralLattice.discriminantQuadraticMap_halfCharacteristicClass`:
  `q([w / 2]) = w² / 8 (mod 1)`.
* `TauCeti.IntegralLattice.discriminantQuadraticMap_halfCharacteristicClass_add`: `q` is constant
  on the coset `[w / 2] + L / L_even`.

## References

* J.-P. Serre, *A Course in Arithmetic*, Chapter V, §1.4.
* J. Milnor and D. Husemoller, *Symmetric Bilinear Forms*, Appendix 4.
-/

public section

namespace TauCeti.IntegralLattice

universe u
variable {V : Type u} [AddCommGroup V] [Module ℚ V] (L : IntegralLattice V)

/-- Half of a characteristic vector lies in the dual carrier of the even sublattice. -/
theorem half_characteristic_mem_evenSublattice_dualCarrier {w : L}
    (hw : L.IsCharacteristicVector w) : (1 / 2 : ℚ) • (w : V) ∈ L.evenSublattice.dualCarrier := by
  rw [LinearMap.BilinForm.mem_dualSubmodule]; intro y hy
  let yL : L := ⟨y, L.evenSublattice_carrier_le hy⟩
  have hy2 := even_iff_two_dvd.mp ((L.mem_evenSublattice_carrier_iff yL).mp hy)
  obtain ⟨k, hk⟩ := Int.modEq_zero_iff_dvd.mp (((L.isCharacteristicVector_iff w).mp hw yL).trans
    (Int.modEq_zero_iff_dvd.mpr hy2))
  refine Submodule.mem_one.mpr ⟨k, ?_⟩
  rw [eq_intCast, L.evenSublattice_form, map_smul, LinearMap.smul_apply, smul_eq_mul,
    ← L.integralForm_cast w yL, hk]; push_cast; ring

/-- Half of a characteristic vector, packaged in the dual carrier of `L.evenSublattice`. -/
noncomputable def halfCharacteristicDual {w : L} (hw : L.IsCharacteristicVector w) :
    L.evenSublattice.dualCarrier :=
  ⟨(1 / 2 : ℚ) • (w : V), L.half_characteristic_mem_evenSublattice_dualCarrier hw⟩

/-- Ambient coercion of `halfCharacteristicDual`. -/
@[simp] theorem coe_halfCharacteristicDual {w : L} (hw : L.IsCharacteristicVector w) :
    (L.halfCharacteristicDual hw : V) = (1 / 2 : ℚ) • (w : V) := (rfl)

/-- The discriminant class of `(1 / 2) • w` in `A_(L_even)`. -/
noncomputable def halfCharacteristicClass {w : L} (hw : L.IsCharacteristicVector w) :
    L.evenSublattice.DiscriminantGroup := Submodule.Quotient.mk (L.halfCharacteristicDual hw)

/-- `halfCharacteristicClass` unfolded as the quotient class of `halfCharacteristicDual`. -/
theorem halfCharacteristicClass_def {w : L} (hw : L.IsCharacteristicVector w) :
    L.halfCharacteristicClass hw = Submodule.Quotient.mk (L.halfCharacteristicDual hw) := (rfl)

/-- Any vector of `L` lies in the dual carrier of `L.evenSublattice`. -/
theorem coe_mem_evenSublattice_dualCarrier (x : L) : (x : V) ∈ L.evenSublattice.dualCarrier := by
  rw [LinearMap.BilinForm.mem_dualSubmodule, L.evenSublattice_form]
  exact fun y hy ↦ L.form_mem_one x ⟨y, L.evenSublattice_carrier_le hy⟩

/-- A vector of `L`, packaged in the dual carrier of `L.evenSublattice`. -/
noncomputable def latticeVectorDual (x : L) : L.evenSublattice.dualCarrier :=
  ⟨x, L.coe_mem_evenSublattice_dualCarrier x⟩

/-- Ambient coercion of `latticeVectorDual`. -/
@[simp] theorem coe_latticeVectorDual (x : L) : (L.latticeVectorDual x : V) = (x : V) := (rfl)

/-- The discriminant class in `A_(L_even)` of a lattice vector `x ∈ L`. -/
noncomputable def latticeVectorClass (x : L) : L.evenSublattice.DiscriminantGroup :=
  Submodule.Quotient.mk (L.latticeVectorDual x)

/-- `latticeVectorClass` unfolded as the quotient class of `latticeVectorDual`. -/
theorem latticeVectorClass_def (x : L) :
    L.latticeVectorClass x = Submodule.Quotient.mk (L.latticeVectorDual x) := (rfl)

/-- Shifting a characteristic vector `w` by `2 • e` shifts its half-characteristic class
in `A_(L_even)` by `L.latticeVectorClass e`. -/
theorem halfCharacteristicClass_add_two_smul {w : L} (hw : L.IsCharacteristicVector w)
    (e : L) : L.halfCharacteristicClass (hw.add_two_smul e) =
      L.latticeVectorClass e + L.halfCharacteristicClass hw := by
  simp only [halfCharacteristicClass_def, latticeVectorClass_def, ← Submodule.Quotient.mk_add]
  refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
  simp only [Submodule.coe_add, coe_halfCharacteristicDual, coe_latticeVectorDual,
    Submodule.coe_smul_of_tower, ← Int.cast_smul_eq_zsmul ℚ, smul_add, smul_smul]; norm_num; abel

/-- The class of a lattice vector in `A_(L_even)` vanishes precisely when its norm is even. -/
@[simp] theorem latticeVectorClass_eq_zero_iff (x : L) :
    L.latticeVectorClass x = 0 ↔ Even (L.integralNorm x) := by
  rw [latticeVectorClass_def, L.evenSublattice.discriminantGroup_mk_eq_zero_iff,
    coe_latticeVectorDual, L.mem_evenSublattice_carrier_iff]

/-- Every lattice vector defines a two-torsion class in `A_(L_even)`. -/
@[simp] theorem two_nsmul_latticeVectorClass (x : L) : 2 • L.latticeVectorClass x = 0 := by
  rw [latticeVectorClass_def, ← Nat.cast_smul_eq_nsmul ℤ, ← Submodule.Quotient.mk_smul,
    L.evenSublattice.discriminantGroup_mk_eq_zero_iff, Submodule.coe_smul_of_tower,
    coe_latticeVectorDual, Nat.cast_ofNat, ← Submodule.coe_smul_of_tower,
    L.mem_evenSublattice_carrier_iff]
  exact (L.mem_evenSubmodule_iff _).mp (L.two_smul_mem_evenSubmodule x)

/-- Integer scalar multiplication by `2` annihilates every `latticeVectorClass`. -/
@[simp] theorem two_zsmul_latticeVectorClass (x : L) : (2 : ℤ) • L.latticeVectorClass x = 0 := by
  rw [two_zsmul, ← two_nsmul, L.two_nsmul_latticeVectorClass]

/-- `2 • [w / 2] = 0` in `A_(L_even)` iff `L.integralNorm w` is even. -/
theorem two_nsmul_halfCharacteristicClass_eq_zero_iff_even_integralNorm {w : L}
    (hw : L.IsCharacteristicVector w) :
    2 • L.halfCharacteristicClass hw = 0 ↔ Even (L.integralNorm w) := by
  have h2w : (2 : ℚ) • ((1 / 2 : ℚ) • (w : V)) = (w : V) := by rw [smul_smul]; norm_num
  rw [halfCharacteristicClass_def, ← Nat.cast_smul_eq_nsmul ℤ, ← Submodule.Quotient.mk_smul,
    L.evenSublattice.discriminantGroup_mk_eq_zero_iff, Submodule.coe_smul_of_tower,
    coe_halfCharacteristicDual, ← Int.cast_smul_eq_zsmul ℚ, Int.cast_natCast, Nat.cast_ofNat,
    h2w, L.mem_evenSublattice_carrier_iff]

/-- The discriminant quadratic map evaluates `[w / 2]` to `w² / 8` modulo `1`. -/
theorem discriminantQuadraticMap_halfCharacteristicClass {w : L} (hw : L.IsCharacteristicVector w) :
    L.evenSublattice.discriminantQuadraticMap L.isEven_evenSublattice
        (L.halfCharacteristicClass hw) = ZMod.toRatAddCircle 8 (L.integralNorm w : ZMod 8) := by
  rw [halfCharacteristicClass_def, discriminantQuadraticMap_mk, L.evenSublattice_form,
    ZMod.toRatAddCircle_intCast, L.integralNorm_cast, L.norm_apply]
  simp only [coe_halfCharacteristicDual, map_smul, LinearMap.smul_apply, smul_eq_mul]; congr 1; ring

/-- For any `e ∈ L`, `[e] + [w / 2]` has discriminant quadratic value `w² / 8` modulo `1`. -/
theorem discriminantQuadraticMap_latticeVectorClass_add_halfCharacteristicClass {w : L}
    (hw : L.IsCharacteristicVector w) (e : L) :
    L.evenSublattice.discriminantQuadraticMap L.isEven_evenSublattice
        (L.latticeVectorClass e + L.halfCharacteristicClass hw) =
      ZMod.toRatAddCircle 8 (L.integralNorm w : ZMod 8) := by
  rw [← L.halfCharacteristicClass_add_two_smul hw e,
    L.discriminantQuadraticMap_halfCharacteristicClass,
    (ZMod.intCast_eq_intCast_iff _ _ 8).mpr (hw.integralNorm_add_two_smul_modEq e)]

/-- Translating `[w / 2]` by any class from `L / L_even` leaves its quadratic value unchanged. -/
theorem discriminantQuadraticMap_halfCharacteristicClass_add {w : L}
    (hw : L.IsCharacteristicVector w)
    (h : L.evenSublattice.discriminantSubgroup
      (L.toIntermediateCarrier L.evenSublattice_form.symm L.evenSublattice_carrier_le)) :
    L.evenSublattice.discriminantQuadraticMap L.isEven_evenSublattice
        (L.halfCharacteristicClass hw + h) =
      L.evenSublattice.discriminantQuadraticMap L.isEven_evenSublattice
        (L.halfCharacteristicClass hw) := by
  obtain ⟨x, hx⟩ := h
  rw [AddSubgroup.coe_mk]
  induction x using Submodule.Quotient.induction_on with | _ y =>
  have hy : (y : V) ∈ L.carrier := by
    simpa [coe_toIntermediateCarrier] using
      (L.evenSublattice.mk_mem_discriminantSubgroup_iff _ y).mp hx
  have hy_eq : (Submodule.Quotient.mk y : L.evenSublattice.DiscriminantGroup) =
      L.latticeVectorClass ⟨y, hy⟩ := by
    rw [L.latticeVectorClass_def ⟨y, hy⟩]
    exact congrArg Submodule.Quotient.mk (Subtype.ext (L.coe_latticeVectorDual ⟨y, hy⟩).symm)
  rw [hy_eq, add_comm,
    L.discriminantQuadraticMap_latticeVectorClass_add_halfCharacteristicClass hw,
    L.discriminantQuadraticMap_halfCharacteristicClass hw]

end TauCeti.IntegralLattice
