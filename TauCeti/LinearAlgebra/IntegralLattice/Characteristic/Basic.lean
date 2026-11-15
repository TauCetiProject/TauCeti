/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Int.ModEq
public import TauCeti.LinearAlgebra.BilinearForm.Characteristic
public import TauCeti.LinearAlgebra.IntegralLattice.Orthogonal.Sum
public import TauCeti.LinearAlgebra.IntegralLattice.Norm

/-!
# Characteristic vectors of integral lattices

A lattice vector is characteristic when pairing it with any lattice vector agrees modulo two
with the latter's norm. This parity condition is the input to the characteristic-norm congruence
for unimodular lattices. The results here give its behavior under evenness, isometries,
translation by twice a vector, and orthogonal sums.

The congruences are in `ℤ`, using the integral restriction of the rational bilinear form, so the
characteristic vectors of a lattice are those of that integral form in the sense of
`LinearMap.BilinForm.IsCharacteristic`.

## References

* J. Milnor and D. Husemoller, *Symmetric Bilinear Forms*, Appendix 4.
-/

public section

namespace TauCeti

universe u v

variable {V : Type u} [AddCommGroup V] [Module ℚ V]
variable {W : Type v} [AddCommGroup W] [Module ℚ W]

namespace IntegralLattice

/-- A vector is characteristic when its pairing with every lattice vector is congruent
modulo two to that vector's norm. -/
def IsCharacteristicVector (L : IntegralLattice V) (w : L) : Prop :=
  ∀ x : L, L.integralForm w x ≡ L.integralNorm x [ZMOD 2]

/-- The defining parity test for a characteristic vector. -/
@[grind =]
theorem isCharacteristicVector_iff (L : IntegralLattice V) (w : L) :
    L.IsCharacteristicVector w ↔
      ∀ x : L, L.integralForm w x ≡ L.integralNorm x [ZMOD 2] :=
  Iff.rfl

/-- The characteristic condition says that pairing with the vector represents norm parity. -/
@[grind =]
theorem isCharacteristicVector_iff_forall_integralForm_eq_normParity
    (L : IntegralLattice V) (w : L) :
    L.IsCharacteristicVector w ↔
      ∀ x : L, (L.integralForm w x : ZMod 2) = L.normParity x := by
  constructor
  · intro hw x
    simpa only [L.normParity_apply] using
      (ZMod.intCast_eq_intCast_iff _ _ 2).mpr (hw x)
  · intro hw x
    apply (ZMod.intCast_eq_intCast_iff _ _ 2).mp
    simpa only [L.normParity_apply] using hw x

/-- The characteristic vectors of `L` are the characteristic vectors of its integral bilinear
form. -/
theorem isCharacteristicVector_iff_isCharacteristic (L : IntegralLattice V) (w : L) :
    L.IsCharacteristicVector w ↔ L.integralForm.IsCharacteristic w := by
  rw [isCharacteristicVector_iff, LinearMap.BilinForm.isCharacteristic_iff]
  refine forall_congr' fun x ↦ ?_
  rw [Int.modEq_iff_dvd, L.integralNorm_apply, ← dvd_neg, neg_sub]

/-- Zero is characteristic precisely when the lattice is even. -/
@[simp ←]
theorem isEven_iff_isCharacteristicVector_zero (L : IntegralLattice V) :
    L.IsEven ↔ L.IsCharacteristicVector 0 := by
  rw [L.isEven_iff_forall_norm]
  constructor
  · intro h x
    simp only [map_zero, LinearMap.zero_apply]
    apply Int.modEq_iff_dvd.mpr
    simpa only [sub_zero] using
      (even_iff_two_dvd.mp ((L.even_integralNorm_iff x).mpr (h x)))
  · intro h x
    have hx := h x
    simp only [map_zero, LinearMap.zero_apply] at hx
    exact (L.even_integralNorm_iff x).mp
      (even_iff_two_dvd.mpr (by simpa only [Int.modEq_iff_dvd, sub_zero] using hx))

/-- Adding twice a lattice vector preserves the characteristic parity condition. -/
theorem IsCharacteristicVector.add_two_smul {L : IntegralLattice V} {w : L}
    (hw : L.IsCharacteristicVector w) (v : L) :
    L.IsCharacteristicVector (w + (2 : ℤ) • v) :=
  (L.isCharacteristicVector_iff_isCharacteristic _).2
    (((L.isCharacteristicVector_iff_isCharacteristic w).1 hw).add_two_smul v)

/-- Translation by twice a lattice vector preserves and reflects the characteristic condition. -/
@[simp]
theorem isCharacteristicVector_add_two_smul_iff (L : IntegralLattice V)
    (w v : L) :
    L.IsCharacteristicVector (w + (2 : ℤ) • v) ↔ L.IsCharacteristicVector w := by
  simp only [isCharacteristicVector_iff_isCharacteristic,
    LinearMap.BilinForm.isCharacteristic_add_two_smul_iff]

/-- A characteristic vector remains characteristic after changing its sign. -/
theorem IsCharacteristicVector.neg {L : IntegralLattice V} {w : L}
    (hw : L.IsCharacteristicVector w) : L.IsCharacteristicVector (-w) :=
  (L.isCharacteristicVector_iff_isCharacteristic _).2
    (LinearMap.BilinForm.isCharacteristic_neg_iff.2
      ((L.isCharacteristicVector_iff_isCharacteristic w).1 hw))

/-- Negation preserves and reflects the characteristic condition. -/
@[simp]
theorem isCharacteristicVector_neg_iff (L : IntegralLattice V) (w : L) :
    L.IsCharacteristicVector (-w) ↔ L.IsCharacteristicVector w := by
  simp only [isCharacteristicVector_iff_isCharacteristic,
    LinearMap.BilinForm.isCharacteristic_neg_iff]

/-- The pairing of the difference of two characteristic vectors with every lattice vector
is even. -/
theorem IsCharacteristicVector.even_integralForm_sub {L : IntegralLattice V}
    {w₁ w₂ : L} (h₁ : L.IsCharacteristicVector w₁)
    (h₂ : L.IsCharacteristicVector w₂) (x : L) :
    Even (L.integralForm (w₁ - w₂) x) :=
  even_iff_two_dvd.2 <| ((L.isCharacteristicVector_iff_isCharacteristic w₁).1 h₁).two_dvd_apply_sub
    ((L.isCharacteristicVector_iff_isCharacteristic w₂).1 h₂) x

/-- Isometries preserve and reflect characteristic vectors. -/
@[simp]
theorem Isometry.isCharacteristicVector_iff {L : IntegralLattice V}
    {M : IntegralLattice W} (e : Isometry L M) (w : L) :
    M.IsCharacteristicVector (e.carrierEquiv w) ↔ L.IsCharacteristicVector w := by
  let f : L.integralForm.IsometryEquiv M.integralForm :=
    { e.carrierEquiv with map_app' := e.carrierEquiv_map_integralForm }
  rw [isCharacteristicVector_iff_isCharacteristic, isCharacteristicVector_iff_isCharacteristic]
  exact f.isCharacteristic_apply_iff

/-- A vector of an orthogonal sum is characteristic precisely when its two components are. -/
@[simp]
theorem isCharacteristicVector_orthogonalSum_iff (L : IntegralLattice V)
    (M : IntegralLattice W) (w : L.orthogonalSum M) :
    (L.orthogonalSum M).IsCharacteristicVector w ↔
      L.IsCharacteristicVector (orthogonalSumFst L M w) ∧
        M.IsCharacteristicVector (orthogonalSumSnd L M w) := by
  constructor
  · intro h
    constructor
    · intro x
      have hx := h (orthogonalSumInl L M x)
      simpa only [integralForm_orthogonalSum, integralNorm_orthogonalSum,
        orthogonalSumFst_inl, orthogonalSumSnd_inl, map_zero, LinearMap.zero_apply,
        integralNorm_zero, add_zero] using hx
    · intro x
      have hx := h (orthogonalSumInr L M x)
      simpa only [integralForm_orthogonalSum, integralNorm_orthogonalSum,
        orthogonalSumFst_inr, orthogonalSumSnd_inr, map_zero, LinearMap.zero_apply,
        integralNorm_zero, zero_add] using hx
  · rintro ⟨hL, hM⟩ x
    rw [integralForm_orthogonalSum, integralNorm_orthogonalSum]
    exact (hL _).add (hM _)

/-- Translating a characteristic vector by twice a lattice vector changes its norm by a
multiple of eight. -/
theorem IsCharacteristicVector.integralNorm_add_two_smul_modEq {L : IntegralLattice V}
    {w : L} (hw : L.IsCharacteristicVector w) (v : L) :
    L.integralNorm (w + (2 : ℤ) • v) ≡ L.integralNorm w [ZMOD 8] := by
  refine (Int.modEq_iff_dvd.2 ?_).symm
  rw [L.integralNorm_apply, L.integralNorm_apply]
  exact L.isSymm_integralForm.eight_dvd_apply_add_two_smul_sub
    ((L.isCharacteristicVector_iff_isCharacteristic w).1 hw) v

end IntegralLattice

end TauCeti
