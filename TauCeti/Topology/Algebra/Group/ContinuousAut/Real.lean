/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.RealVectorSpace
public import TauCeti.Topology.Algebra.Group.ContinuousAut.Basic

/-!
# Continuous automorphisms of the real line

The continuous automorphisms of the additive group of `ℝ`, written multiplicatively as
`Multiplicative ℝ`, are the multiplications `x ↦ c x` by nonzero reals `c`: a continuous additive
map `ℝ → ℝ` is `ℝ`-linear (Mathlib's `map_real_smul`), so it is multiplication by its value
`TauCeti.ContinuousAut.realScale φ` at `1`. This gives

`TauCeti.Real.continuousAutEquivUnits : ContinuousAut (Multiplicative ℝ) ≃* ℝˣ`,

with inverse `TauCeti.Real.continuousAutOfUnit`, and, the group being commutative,
`TauCeti.Real.continuousOutEquivUnits : ContinuousOut (Multiplicative ℝ) ≃* ℝˣ`.
-/

public section

noncomputable section

namespace TauCeti.ContinuousAut

/-- The scaling factor of a continuous automorphism of `Multiplicative ℝ`: its value at `1`,
read in `ℝ`. -/
def realScale (φ : ContinuousAut (Multiplicative ℝ)) : ℝ :=
  (φ (Multiplicative.ofAdd 1)).toAdd

/-- A continuous automorphism of `Multiplicative ℝ` is multiplication by its scaling factor. -/
@[simp]
theorem apply_eq_realScale_mul (φ : ContinuousAut (Multiplicative ℝ)) (x : Multiplicative ℝ) :
    (φ x).toAdd = realScale φ * x.toAdd := by
  let f : ℝ →+ ℝ := (φ.toMulEquiv.toMonoidHom).toAdditive
  -- `f` is `φ` read in the additive presentation.
  have hf_apply : ∀ y, f y = (φ (Multiplicative.ofAdd y)).toAdd := fun _ => rfl
  have hf : Continuous f := by
    rw [show (f : ℝ → ℝ) = fun y => (φ (Multiplicative.ofAdd y)).toAdd from funext hf_apply]
    exact continuous_toAdd.comp (φ.continuous.comp continuous_ofAdd)
  have := map_real_smul f hf x.toAdd 1
  rw [hf_apply, hf_apply, smul_eq_mul, smul_eq_mul, mul_one, ofAdd_toAdd] at this
  rw [this, realScale, mul_comm]

/-- The scaling factor of a continuous automorphism is nonzero. -/
theorem realScale_ne_zero (φ : ContinuousAut (Multiplicative ℝ)) : realScale φ ≠ 0 := by
  intro h
  rw [realScale, ← toAdd_one, Multiplicative.toAdd.injective.eq_iff, ← map_one φ] at h
  exact one_ne_zero (ofAdd_eq_one.mp (φ.injective h))

/-- The scaling factor of a composite is the product of the scaling factors. -/
@[simp]
theorem realScale_mul (φ ψ : ContinuousAut (Multiplicative ℝ)) :
    realScale (φ * ψ) = realScale φ * realScale ψ := by
  conv_lhs => rw [realScale, mul_apply]
  rw [apply_eq_realScale_mul, apply_eq_realScale_mul, toAdd_ofAdd, mul_one]

/-- The scaling factor of the identity is `1`. -/
@[simp]
theorem realScale_one : realScale 1 = 1 := by
  rw [realScale, one_apply, toAdd_ofAdd]

/-- The scaling factor of the inverse is the inverse of the scaling factor. -/
@[simp]
theorem realScale_inv (φ : ContinuousAut (Multiplicative ℝ)) :
    realScale φ⁻¹ = (realScale φ)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← realScale_mul, inv_mul_cancel, realScale_one])

end TauCeti.ContinuousAut

namespace TauCeti.Real

open ContinuousAut

/-- Multiplication by a nonzero real, as a continuous automorphism of `Multiplicative ℝ`. -/
def continuousAutOfUnit (c : ℝˣ) : ContinuousAut (Multiplicative ℝ) where
  toFun x := Multiplicative.ofAdd ((c : ℝ) * x.toAdd)
  invFun x := Multiplicative.ofAdd (((c⁻¹ : ℝˣ) : ℝ) * x.toAdd)
  left_inv x := by simp
  right_inv x := by simp
  map_mul' x y := by simp [mul_add]
  continuous_toFun := continuous_ofAdd.comp (continuous_const.mul continuous_toAdd)
  continuous_invFun := continuous_ofAdd.comp (continuous_const.mul continuous_toAdd)

/-- `continuousAutOfUnit c` is `x ↦ c x`. -/
@[simp]
theorem continuousAutOfUnit_apply (c : ℝˣ) (x : Multiplicative ℝ) :
    continuousAutOfUnit c x = Multiplicative.ofAdd ((c : ℝ) * x.toAdd) :=
  (rfl)

/-- The inverse of `continuousAutOfUnit c` is `x ↦ c⁻¹ x`. -/
@[simp]
theorem continuousAutOfUnit_symm_apply (c : ℝˣ) (x : Multiplicative ℝ) :
    (continuousAutOfUnit c).symm x = Multiplicative.ofAdd (((c⁻¹ : ℝˣ) : ℝ) * x.toAdd) :=
  (rfl)

/-- The scaling factor of `continuousAutOfUnit c` is `c`. -/
@[simp]
theorem realScale_continuousAutOfUnit (c : ℝˣ) : realScale (continuousAutOfUnit c) = c := by
  rw [realScale, continuousAutOfUnit_apply, toAdd_ofAdd, toAdd_ofAdd, mul_one]

/-- **The continuous automorphisms of `ℝ` are the multiplications by nonzero reals.** The
isomorphism sends a continuous automorphism to its scaling factor. -/
def continuousAutEquivUnits : ContinuousAut (Multiplicative ℝ) ≃* ℝˣ where
  toFun φ := Units.mk0 (realScale φ) (realScale_ne_zero φ)
  invFun := continuousAutOfUnit
  left_inv φ := by
    ext x
    rw [continuousAutOfUnit_apply, Units.val_mk0, ← apply_eq_realScale_mul, ofAdd_toAdd]
  right_inv c := Units.ext (by rw [Units.val_mk0, realScale_continuousAutOfUnit])
  map_mul' φ ψ := Units.ext (by rw [Units.val_mk0, Units.val_mul, Units.val_mk0,
    Units.val_mk0, realScale_mul])

/-- `continuousAutEquivUnits` sends a continuous automorphism to its scaling factor. -/
@[simp]
theorem coe_continuousAutEquivUnits_apply (φ : ContinuousAut (Multiplicative ℝ)) :
    (continuousAutEquivUnits φ : ℝ) = realScale φ :=
  (rfl)

/-- The inverse of `continuousAutEquivUnits` is multiplication. -/
@[simp]
theorem continuousAutEquivUnits_symm_apply (c : ℝˣ) :
    continuousAutEquivUnits.symm c = continuousAutOfUnit c :=
  (rfl)

/-- **The continuous outer automorphism group of `ℝ` is `ℝˣ`**: the group is commutative, so
its continuous outer automorphisms are its continuous automorphisms, the multiplications by
nonzero reals. -/
def continuousOutEquivUnits : ContinuousOut (Multiplicative ℝ) ≃* ℝˣ :=
  ContinuousOut.mulEquivOfIsMulCommutative.trans continuousAutEquivUnits

/-- `continuousOutEquivUnits` sends the class of a continuous automorphism to its scaling
factor. -/
@[simp]
theorem coe_continuousOutEquivUnits_mk (φ : ContinuousAut (Multiplicative ℝ)) :
    (continuousOutEquivUnits (φ : ContinuousOut (Multiplicative ℝ)) : ℝ) = realScale φ := by
  rw [continuousOutEquivUnits, MulEquiv.trans_apply,
    ContinuousOut.mulEquivOfIsMulCommutative_mk, coe_continuousAutEquivUnits_apply]

/-- The inverse of `continuousOutEquivUnits` sends `c` to the class of multiplication by `c`. -/
@[simp]
theorem continuousOutEquivUnits_symm_apply (c : ℝˣ) :
    continuousOutEquivUnits.symm c =
      (continuousAutOfUnit c : ContinuousOut (Multiplicative ℝ)) := by
  rw [continuousOutEquivUnits, MulEquiv.symm_trans_apply, continuousAutEquivUnits_symm_apply,
    ContinuousOut.mulEquivOfIsMulCommutative_symm_apply]

end TauCeti.Real
