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

`TauCeti.ContinuousAut.realMulEquivUnits : ContinuousAut (Multiplicative ℝ) ≃* ℝˣ`,

and, the group being commutative, `TauCeti.ContinuousOut.realMulEquivUnits :
ContinuousOut (Multiplicative ℝ) ≃* ℝˣ`. This is the TeichmullerGeometry §4.2 Check "for
`G = Multiplicative ℝ`, the reals under addition with their usual topology, the continuous
automorphisms are the maps `x ↦ c x`, `c ≠ 0`, so `TauCeti.ContinuousOut G ≅ ℝˣ`".
-/

public section

noncomputable section

namespace TauCeti.ContinuousAut

/-- The scaling factor of a continuous automorphism of `Multiplicative ℝ`: its value at `1`,
read in `ℝ`. -/
def realScale (φ : ContinuousAut (Multiplicative ℝ)) : ℝ :=
  (φ (Multiplicative.ofAdd 1)).toAdd

/-- A continuous automorphism of `Multiplicative ℝ` is multiplication by its scaling factor. -/
theorem apply_eq_realScale_mul (φ : ContinuousAut (Multiplicative ℝ)) (x : ℝ) :
    (φ (Multiplicative.ofAdd x)).toAdd = realScale φ * x := by
  let f : ℝ →+ ℝ := (φ.toMulEquiv.toMonoidHom).toAdditive
  have hf : Continuous f := continuous_toAdd.comp (φ.continuous.comp continuous_ofAdd)
  have := map_real_smul f hf x 1
  simp only [smul_eq_mul, mul_one] at this
  rw [realScale, mul_comm]
  exact this

/-- The scaling factor of a continuous automorphism is nonzero. -/
theorem realScale_ne_zero (φ : ContinuousAut (Multiplicative ℝ)) : realScale φ ≠ 0 := by
  intro h
  have h1 : φ (Multiplicative.ofAdd 1) = φ 1 :=
    (Multiplicative.toAdd.injective h).trans (map_one φ).symm
  simpa using congrArg Multiplicative.toAdd (φ.injective h1)

/-- Multiplication by a nonzero real, as a continuous automorphism of `Multiplicative ℝ`. -/
def ofRealUnit (c : ℝˣ) : ContinuousAut (Multiplicative ℝ) where
  toFun x := Multiplicative.ofAdd ((c : ℝ) * x.toAdd)
  invFun x := Multiplicative.ofAdd (((c⁻¹ : ℝˣ) : ℝ) * x.toAdd)
  left_inv x := by simp
  right_inv x := by simp
  map_mul' x y := by simp [mul_add]
  continuous_toFun := continuous_ofAdd.comp (continuous_const.mul continuous_toAdd)
  continuous_invFun := continuous_ofAdd.comp (continuous_const.mul continuous_toAdd)

/-- `ofRealUnit c` is `x ↦ c x`. -/
@[simp]
theorem ofRealUnit_apply (c : ℝˣ) (x : Multiplicative ℝ) :
    ofRealUnit c x = Multiplicative.ofAdd ((c : ℝ) * x.toAdd) :=
  (rfl)

/-- **The continuous automorphisms of `ℝ` are the multiplications by nonzero reals.** The
isomorphism sends a continuous automorphism to its scaling factor. -/
def realMulEquivUnits : ContinuousAut (Multiplicative ℝ) ≃* ℝˣ where
  toFun φ := Units.mk0 (realScale φ) (realScale_ne_zero φ)
  invFun := ofRealUnit
  left_inv φ := by
    ext x
    change Multiplicative.ofAdd (realScale φ * x.toAdd) = φ x
    rw [← apply_eq_realScale_mul, ofAdd_toAdd]
    rfl
  right_inv c := Units.ext (by simp [realScale])
  map_mul' φ ψ := Units.ext <| by
    simp only [Units.val_mk0, Units.val_mul, realScale, mul_apply]
    rw [← ofAdd_toAdd (ψ (Multiplicative.ofAdd 1)), apply_eq_realScale_mul, realScale,
      toAdd_ofAdd]

/-- `realMulEquivUnits` sends a continuous automorphism to its scaling factor. -/
@[simp]
theorem coe_realMulEquivUnits_apply (φ : ContinuousAut (Multiplicative ℝ)) :
    (realMulEquivUnits φ : ℝ) = realScale φ :=
  (rfl)

/-- The inverse of `realMulEquivUnits` is multiplication. -/
@[simp]
theorem realMulEquivUnits_symm_apply (c : ℝˣ) : realMulEquivUnits.symm c = ofRealUnit c :=
  (rfl)

end TauCeti.ContinuousAut

namespace TauCeti.ContinuousOut

/-- **The continuous outer automorphism group of `ℝ` is `ℝˣ`**: the group is commutative, so
its continuous outer automorphisms are its continuous automorphisms, the multiplications by
nonzero reals. -/
def realMulEquivUnits : ContinuousOut (Multiplicative ℝ) ≃* ℝˣ :=
  mulEquivOfIsMulCommutative.trans ContinuousAut.realMulEquivUnits

/-- `ContinuousOut.realMulEquivUnits` sends the class of a continuous automorphism to its scaling
factor. -/
@[simp]
theorem coe_realMulEquivUnits_mk (φ : ContinuousAut (Multiplicative ℝ)) :
    (realMulEquivUnits (φ : ContinuousOut (Multiplicative ℝ)) : ℝ) = ContinuousAut.realScale φ := by
  rw [realMulEquivUnits, MulEquiv.trans_apply, mulEquivOfIsMulCommutative_mk,
    ContinuousAut.coe_realMulEquivUnits_apply]

end TauCeti.ContinuousOut
