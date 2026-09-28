/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Int.ModEq
public import TauCeti.LinearAlgebra.IntegralLattice.OrthogonalSum

/-!
# Characteristic vectors of integral lattices

A lattice vector is characteristic when pairing it with any lattice vector agrees modulo two
with the latter's norm. This parity condition is the input to the characteristic-norm congruence
for unimodular lattices. The results here give its behavior under evenness, isometries,
translation by twice a vector, and orthogonal sums.

The congruences are in `ℤ`, using the integral restriction of the rational bilinear form.

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
    L.IsCharacteristicVector (w + (2 : ℤ) • v) := by
  intro x
  rw [Int.modEq_iff_dvd, map_add, map_smul]
  obtain ⟨k, hk⟩ := Int.modEq_iff_dvd.mp (hw x)
  refine ⟨k - L.integralForm v x, ?_⟩
  simp only [two_zsmul, LinearMap.add_apply] at hk ⊢
  omega

/-- Translation by twice a lattice vector preserves and reflects the characteristic condition. -/
@[simp]
theorem isCharacteristicVector_add_two_smul_iff (L : IntegralLattice V)
    (w v : L) :
    L.IsCharacteristicVector (w + (2 : ℤ) • v) ↔ L.IsCharacteristicVector w := by
  constructor
  · intro h
    have h' := h.add_two_smul (-v)
    simpa [smul_neg, add_assoc] using h'
  · intro h
    exact h.add_two_smul v

/-- A characteristic vector remains characteristic after changing its sign. -/
theorem IsCharacteristicVector.neg {L : IntegralLattice V} {w : L}
    (hw : L.IsCharacteristicVector w) : L.IsCharacteristicVector (-w) := by
  have h : w + (2 : ℤ) • (-w) = -w := by abel
  simpa only [h] using hw.add_two_smul (-w)

/-- Negation preserves and reflects the characteristic condition. -/
@[simp]
theorem isCharacteristicVector_neg_iff (L : IntegralLattice V) (w : L) :
    L.IsCharacteristicVector (-w) ↔ L.IsCharacteristicVector w := by
  constructor
  · intro h
    simpa only [neg_neg] using h.neg
  · exact IsCharacteristicVector.neg

/-- The pairing of the difference of two characteristic vectors with every lattice vector
is even. -/
theorem IsCharacteristicVector.even_integralForm_sub {L : IntegralLattice V}
    {w₁ w₂ : L} (h₁ : L.IsCharacteristicVector w₁)
    (h₂ : L.IsCharacteristicVector w₂) (x : L) :
    Even (L.integralForm (w₁ - w₂) x) := by
  rw [map_sub, LinearMap.sub_apply, even_iff_two_dvd, ← Int.modEq_zero_iff_dvd]
  simpa only [sub_self] using (h₁ x).sub (h₂ x)

/-- Isometries preserve and reflect characteristic vectors. -/
@[simp]
theorem Isometry.isCharacteristicVector_iff {L : IntegralLattice V}
    {M : IntegralLattice W} (e : Isometry L M) (w : L) :
    M.IsCharacteristicVector (e.carrierEquiv w) ↔ L.IsCharacteristicVector w := by
  constructor
  · intro h x
    have hx := h (e.carrierEquiv x)
    rwa [e.carrierEquiv_map_integralForm, e.integralNorm_carrierEquiv] at hx
  · intro h y
    have hx := h (e.carrierEquiv.symm y)
    simpa only [LinearEquiv.apply_symm_apply, ← e.carrierEquiv_map_integralForm,
      ← e.integralNorm_carrierEquiv] using hx

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
  rw [Int.modEq_iff_dvd]
  obtain ⟨k, hk⟩ := Int.modEq_iff_dvd.mp (hw v)
  rw [L.integralNorm_add, L.integralNorm_zsmul, map_smul]
  simp only [Int.zsmul_eq_mul]
  use k - L.integralNorm v
  nlinarith

end IntegralLattice

end TauCeti
