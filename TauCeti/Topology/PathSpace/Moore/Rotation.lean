/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.PathSpace.Moore.Comparison.FreeLoop
public import TauCeti.Topology.PathSpace.Moore.Truncate

/-!
# Rotating free Moore loops

A free Moore loop `γ` of length `L` can be started at any of its points. The **rotation** of `γ`
by a time `s ≤ L` (`TauCeti.MooreFreeLoopSpace.rotate`) is the free loop that starts at `γ s`,
runs along `γ` to its end point, which is its starting point, and then along `γ` from its start
back to `γ s`. It is the concatenation of the piece `γ.drop s` after time `s` with the truncation
`γ.truncate s` before time `s`, so it has the same length `L`, and it depends continuously on the
loop and the time (`TauCeti.MooreFreeLoopSpace.continuous_rotate`). The rotations by `0` and by
every time `s ≥ L` are `γ` itself.

So, as `s` runs from `0` to `L`, the rotations of `γ` form a loop of free loops based at `γ`, the
**rotation loop** `TauCeti.MooreFreeLoopSpace.rotationLoop γ` of duration `L`: the loop of loops
whose adjoint is `(s, t) ↦ γ(s + t mod L)` for `s, t ≤ L`, which rotates `γ` once around itself
(`TauCeti.MooreFreeLoopSpace.rotate_apply_of_le`,
`TauCeti.MooreFreeLoopSpace.rotate_apply_length_sub_add`). Read as a circle map, the rotation of
`γ` by the fraction `s` of its length is `γ` precomposed with the rotation of the circle by
`exp (2πis)` (`TauCeti.MooreFreeLoopSpace.toCircleMap_rotate`). The base points of the rotation
loop trace `γ`: evaluating the rotation loop at the base point gives back `γ`, read as a based loop
at its base point (`TauCeti.MooreFreeLoopSpace.map_basepointMap_rotationLoop`). Local systems on
the free loop space are tested against this loop: a local system pulled back along evaluation at
the base point has, along the rotation loop of `γ`, the monodromy of `γ` itself.

## Main definitions

* `TauCeti.MooreFreeLoopSpace.rotate γ s`: the rotation of a free Moore loop by the time `s`.
* `TauCeti.MooreFreeLoopSpace.rotationLoop γ`: the loop of rotations of `γ`, a Moore loop in the
  free loop space based at `γ`.

## Main results

* `TauCeti.MooreFreeLoopSpace.continuous_rotate`: rotation is jointly continuous.
* `TauCeti.MooreFreeLoopSpace.length_rotate`, `TauCeti.MooreFreeLoopSpace.basepoint_rotate`: the
  rotation by `s` has the same length and starts at `γ s`.
* `TauCeti.MooreFreeLoopSpace.rotate_apply_of_le`,
  `TauCeti.MooreFreeLoopSpace.rotate_apply_length_sub_add`: the values of the rotation by `s`,
  before and after the end of `γ`.
* `TauCeti.MooreFreeLoopSpace.toCircleMap_rotate`: read as a circle map, the rotation is
  precomposition with a rotation of the circle.
* `TauCeti.MooreFreeLoopSpace.map_basepointMap_rotationLoop`: the base points of the rotation loop
  of `γ` trace `γ`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §4.1 (the loop of loops rotating a loop
  around itself).
-/

public noncomputable section

open unitInterval
open scoped NNReal

namespace TauCeti

namespace MooreFreeLoopSpace

variable {X : Type*} [TopologicalSpace X]

/-- The **rotation** of a free Moore loop `γ` by the time `s`: the piece of `γ` after time `s`,
followed by the piece before time `s`. It starts and ends at `γ s`, and for `s ≥ γ.length` it is
`γ` itself. -/
def rotate (γ : MooreFreeLoopSpace X) (s : ℝ≥0) : MooreFreeLoopSpace X :=
  ⟨(γ.toMoorePath.drop s).trans (γ.toMoorePath.truncate s) (by
      rw [MoorePath.target_drop, MoorePath.source_truncate, target_toMoorePath,
        source_toMoorePath]),
    by rw [MoorePath.target_trans, MoorePath.source_trans, MoorePath.target_truncate,
      MoorePath.source_drop]⟩

theorem toMoorePath_rotate (γ : MooreFreeLoopSpace X) (s : ℝ≥0) :
    (γ.rotate s).toMoorePath = (γ.toMoorePath.drop s).trans (γ.toMoorePath.truncate s) (by
      rw [MoorePath.target_drop, MoorePath.source_truncate, target_toMoorePath,
        source_toMoorePath]) :=
  (rfl)

/-- The rotation of `γ` by `s` starts at `γ s`. -/
@[simp]
theorem basepoint_rotate (γ : MooreFreeLoopSpace X) (s : ℝ≥0) :
    (γ.rotate s).basepoint = γ.toMoorePath s := by
  rw [← source_toMoorePath, toMoorePath_rotate, MoorePath.source_trans, MoorePath.source_drop]

/-- Until `γ` ends, its rotation by `s` runs along `γ` from time `s`. -/
theorem rotate_apply_of_le (γ : MooreFreeLoopSpace X) {s t : ℝ≥0} (ht : t ≤ γ.length - s) :
    (γ.rotate s).toMoorePath t = γ.toMoorePath (s + t) := by
  rw [← length_toMoorePath, ← MoorePath.length_drop] at ht
  rw [toMoorePath_rotate, MoorePath.trans_apply_of_le _ _ _ ht, MoorePath.drop_apply]

/-- Once `γ` has ended, its rotation by `s` runs along `γ` from its start, up to time `s`. -/
theorem rotate_apply_length_sub_add (γ : MooreFreeLoopSpace X) (s t : ℝ≥0) :
    (γ.rotate s).toMoorePath (γ.length - s + t) = γ.toMoorePath (min t s) := by
  rw [toMoorePath_rotate, ← length_toMoorePath, ← MoorePath.length_drop,
    MoorePath.trans_apply_length_add, MoorePath.truncate_apply]

/-- Rotation does not change the length. -/
@[simp]
theorem length_rotate (γ : MooreFreeLoopSpace X) (s : ℝ≥0) : (γ.rotate s).length = γ.length := by
  rw [← length_toMoorePath, toMoorePath_rotate, MoorePath.length_trans, MoorePath.length_drop,
    MoorePath.length_truncate, length_toMoorePath]
  rcases le_total s γ.length with hs | hs
  · rw [min_eq_left hs, tsub_add_cancel_of_le hs]
  · rw [min_eq_right hs, tsub_eq_zero_of_le hs, zero_add]

/-- The rotation by `0` is the identity. -/
@[simp]
theorem rotate_zero (γ : MooreFreeLoopSpace X) : γ.rotate 0 = γ :=
  ext <| by simp only [toMoorePath_rotate, MoorePath.drop_zero, MoorePath.truncate_zero,
    source_toMoorePath, MoorePath.trans_refl]

/-- The rotation by a time after the end of the loop is the identity. -/
theorem rotate_of_length_le (γ : MooreFreeLoopSpace X) {s : ℝ≥0} (hs : γ.length ≤ s) :
    γ.rotate s = γ := by
  rw [← length_toMoorePath] at hs
  exact ext <| by simp only [toMoorePath_rotate, MoorePath.drop_of_length_le _ hs,
    MoorePath.truncate_of_length_le _ hs, MoorePath.refl_trans]

/-- The rotation by the length of the loop is the identity. -/
@[simp]
theorem rotate_length (γ : MooreFreeLoopSpace X) : γ.rotate γ.length = γ :=
  γ.rotate_of_length_le le_rfl

/-- **Rotation is continuous** in the loop and the time. -/
@[fun_prop]
theorem continuous_rotate :
    Continuous fun p : MooreFreeLoopSpace X × ℝ≥0 ↦ p.1.rotate p.2 :=
  isEmbedding_toMoorePath.continuous_iff.2 <| by
    simp only [Function.comp_def, toMoorePath_rotate]
    fun_prop

/-- Rotations of a continuous family of loops by a continuous family of times form a continuous
family. -/
@[fun_prop]
protected theorem _root_.Continuous.mooreFreeLoopSpace_rotate {Y : Type*} [TopologicalSpace Y]
    {f : Y → MooreFreeLoopSpace X} {g : Y → ℝ≥0} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun y ↦ (f y).rotate (g y) :=
  continuous_rotate.comp (hf.prodMk hg)

/-! ### Rotations as circle maps -/

/-- **The rotation of a free Moore loop is a rotation of the circle**: read as a circle map, the
rotation of `γ` by the fraction `s` of its length is `γ` precomposed with multiplication by
`exp (2πis)`. -/
theorem toCircleMap_rotate (γ : MooreFreeLoopSpace X) (s : I) (z : Circle) :
    toCircleMap (γ.rotate (γ.length * toNNReal s)) z = toCircleMap γ (unitToCircle s * z) := by
  obtain ⟨u, rfl⟩ := unitToCircle_surjective z
  rw [toCircleMap_unitToCircle, MoorePath.toUnitPath_apply, length_toMoorePath, length_rotate]
  have hs : γ.length * toNNReal s ≤ γ.length :=
    mul_le_of_le_one_right (by positivity) (toNNReal_le_one s)
  rcases le_total ((s : ℝ) + u) 1 with h | h
  · -- Before the end of `γ`, the rotation runs along `γ` from the time `γ.length * s`.
    obtain ⟨w, hw⟩ : ∃ w : I, (w : ℝ) = s + u :=
      ⟨⟨_, add_nonneg (unitInterval.nonneg s) (unitInterval.nonneg u), h⟩, rfl⟩
    have hle : γ.length * toNNReal u ≤ γ.length - γ.length * toNNReal s := by
      refine le_tsub_of_add_le_right ?_
      rw [← NNReal.coe_le_coe]
      push_cast [coe_toNNReal]
      rw [← mul_add]
      exact mul_le_of_le_one_right γ.length.coe_nonneg (by linarith)
    rw [rotate_apply_of_le _ hle, unitToCircle_mul_unitToCircle_of_coe_eq_add hw,
      toCircleMap_unitToCircle, MoorePath.toUnitPath_apply, length_toMoorePath]
    congr 1
    ext
    push_cast [coe_toNNReal, hw]
    ring
  · -- After the end of `γ`, the rotation runs along `γ` from its start.
    obtain ⟨w, hw⟩ : ∃ w : I, (w : ℝ) = s + u - 1 :=
      ⟨⟨_, by linarith, by linarith [unitInterval.le_one s, unitInterval.le_one u]⟩, rfl⟩
    have hws : toNNReal w ≤ toNNReal s := by
      rw [← NNReal.coe_le_coe, coe_toNNReal, coe_toNNReal, hw]
      linarith [unitInterval.le_one u]
    have heq : γ.length * toNNReal u =
        γ.length - γ.length * toNNReal s + γ.length * toNNReal w := by
      ext
      rw [NNReal.coe_add, NNReal.coe_sub hs]
      push_cast [coe_toNNReal, hw]
      ring
    rw [heq, rotate_apply_length_sub_add,
      min_eq_left (mul_le_mul_of_nonneg_left hws (by positivity)),
      unitToCircle_mul_unitToCircle_of_coe_eq_add_sub_one hw, toCircleMap_unitToCircle,
      MoorePath.toUnitPath_apply, length_toMoorePath]

/-! ### The rotation loop -/

/-- The **rotation loop** of a free Moore loop `γ`: the loop of free loops `s ↦ γ.rotate s`, of
duration `γ.length`, based at `γ`. It rotates `γ` once around itself. -/
def rotationLoop (γ : MooreFreeLoopSpace X) : MooreLoopSpace (MooreFreeLoopSpace X) γ where
  toMoorePath :=
    { toFun := γ.rotate
      continuous_toFun := by fun_prop
      length := γ.length
      apply_of_length_le' _ ht := by
        rw [γ.rotate_of_length_le ht, γ.rotate_of_length_le le_rfl] }
  source_eq := (MoorePath.source_def _).trans γ.rotate_zero
  target_eq := (MoorePath.target_def _).trans γ.rotate_length

/-- The rotation loop of `γ` is the rotation of `γ` by the time `s` at the time `s`. -/
@[simp]
theorem rotationLoop_apply (γ : MooreFreeLoopSpace X) (s : ℝ≥0) :
    γ.rotationLoop.toMoorePath s = γ.rotate s :=
  (rfl)

/-- The rotation loop of `γ` lasts as long as `γ`. -/
@[simp]
theorem length_rotationLoop (γ : MooreFreeLoopSpace X) : γ.rotationLoop.length = γ.length := by
  rw [← MooreLoopSpace.length_toMoorePath]
  rfl

/-- **The base points of the rotation loop trace the loop**: evaluating the rotation loop of `γ` at
the base point gives `γ`, read as a based loop at its base point. -/
@[simp]
theorem map_basepointMap_rotationLoop (γ : MooreFreeLoopSpace X) :
    MooreLoopSpace.map (basepointMap X) (basepointMap_apply γ) γ.rotationLoop = γ.toMooreLoop :=
  MooreLoopSpace.ext <| MoorePath.ext (by simp) fun s ↦ by
    simp [MoorePath.map_apply]

end MooreFreeLoopSpace

end TauCeti
