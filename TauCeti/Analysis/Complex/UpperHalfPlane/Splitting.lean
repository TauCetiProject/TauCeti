/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.ProperAction
public import TauCeti.Topology.Algebra.ProperAction.Orbit

/-!
# The splitting `ℍ × K ≃ₜ SL(2, ℝ)`

The group `SL(2, ℝ)` acts transitively on the upper half-plane `ℍ`, and the stabilizer `K` of `i`
is compact, since the action is proper. Mathlib's continuous section `UpperHalfPlane.toSL2R` of the
orbit map `g ↦ g • i` splits `SL(2, ℝ)` as `ℍ × K`: every `g` is uniquely `toSL2R z * k` with
`z = g • i` and `k ∈ K`, and both coordinates depend continuously on `g`.

## Main definitions

* `UpperHalfPlane.toSL2RMulHomeomorph`: the splitting `ℍ × K ≃ₜ SL(2, ℝ)`,
  `(z, k) ↦ toSL2R z * k`, with `K` the stabilizer of `i`.

## Main results

* `UpperHalfPlane.instCompactSpaceStabilizerI`: the stabilizer of `i` in `SL(2, ℝ)` is compact.
* `UpperHalfPlane.toSL2RMulHomeomorph_symm_apply_fst`,
  `UpperHalfPlane.toSL2RMulHomeomorph_symm_apply_snd_coe`: the coordinates of `g` are `g • i` and
  `(toSL2R (g • i))⁻¹ * g`.
-/

public section

noncomputable section

open scoped MatrixGroups

namespace UpperHalfPlane

/-- The stabilizer of `i` in `SL(2, ℝ)` is a compact space, as a stabilizer of the proper action
of `SL(2, ℝ)` on `ℍ`. -/
instance instCompactSpaceStabilizerI : CompactSpace (MulAction.stabilizer SL(2, ℝ) I) :=
  isCompact_iff_compactSpace.mp (ProperSMul.isCompact_stabilizer I)

/-- `(toSL2R z)⁻¹ * g` fixes `i` when `g • i = z`. -/
theorem toSL2R_inv_mul_mem_stabilizer (g : SL(2, ℝ)) :
    (toSL2R (g • I))⁻¹ * g ∈ MulAction.stabilizer SL(2, ℝ) I := by
  rw [MulAction.mem_stabilizer_iff, mul_smul, inv_smul_eq_iff, toSL2R_smul_I]

/-- Right multiplication by an element of the stabilizer of `i` does not move `toSL2R z • i = z`. -/
@[simp]
theorem toSL2R_mul_smul_I (z : ℍ) (k : MulAction.stabilizer SL(2, ℝ) I) :
    (toSL2R z * k) • I = z := by
  rw [mul_smul, MulAction.mem_stabilizer_iff.mp k.property, toSL2R_smul_I]

/-- If `a * b = (toSL2R w)⁻¹`, then `a⁻¹` and `b` carry `i` and `w` to the same point. -/
theorem inv_smul_I_eq_smul_of_mul_eq_toSL2R_inv {a b : SL(2, ℝ)} {w : ℍ}
    (h : a * b = (toSL2R w)⁻¹) : a⁻¹ • I = b • w := by
  rw [← toSL2R_smul_I w, ← inv_inv (toSL2R w), ← h, mul_inv_rev, mul_smul, smul_inv_smul]

/-- **The splitting `ℍ × K ≃ₜ SL(2, ℝ)`**, `(z, k) ↦ toSL2R z * k`. Every `g ∈ SL(2, ℝ)` is
uniquely `toSL2R z * k`, with `z = g • i` and `k` in the stabilizer `K` of `i`. -/
def toSL2RMulHomeomorph : ℍ × MulAction.stabilizer SL(2, ℝ) I ≃ₜ SL(2, ℝ) where
  toFun p := toSL2R p.1 * p.2
  invFun g := (g • I, ⟨(toSL2R (g • I))⁻¹ * g, toSL2R_inv_mul_mem_stabilizer g⟩)
  left_inv p := by ext <;> simp
  right_inv g := by simp
  continuous_toFun :=
    (continuous_toSL2R.comp continuous_fst).mul (continuous_subtypeVal.comp continuous_snd)
  continuous_invFun := by
    refine (continuous_id.smul continuous_const).prodMk (Continuous.subtype_mk ?_ _)
    exact ((continuous_toSL2R.comp (continuous_id.smul continuous_const)).inv).mul continuous_id

@[simp]
theorem toSL2RMulHomeomorph_apply (p : ℍ × MulAction.stabilizer SL(2, ℝ) I) :
    toSL2RMulHomeomorph p = toSL2R p.1 * p.2 :=
  by rfl

/-- The `ℍ`-coordinate of `g` in the splitting `ℍ × K ≃ₜ SL(2, ℝ)` is `g • i`. -/
@[simp]
theorem toSL2RMulHomeomorph_symm_apply_fst (g : SL(2, ℝ)) :
    (toSL2RMulHomeomorph.symm g).1 = g • I :=
  by rfl

/-- The `K`-coordinate of `g` in the splitting `ℍ × K ≃ₜ SL(2, ℝ)` is `(toSL2R (g • i))⁻¹ * g`. -/
@[simp]
theorem toSL2RMulHomeomorph_symm_apply_snd_coe (g : SL(2, ℝ)) :
    ((toSL2RMulHomeomorph.symm g).2 : SL(2, ℝ)) = (toSL2R (g • I))⁻¹ * g :=
  by rfl

end UpperHalfPlane
