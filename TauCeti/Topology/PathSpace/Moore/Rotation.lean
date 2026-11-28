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
`TauCeti.MooreFreeLoopSpace.rotate_apply_length_sub_add`). Its base points trace
`γ`: evaluating the rotation loop at the base point gives back `γ`, read as a based loop at its
base point (`TauCeti.MooreFreeLoopSpace.map_basepointMap_rotationLoop`). Local systems on the free
loop space are tested against this loop: a local system pulled back along evaluation at the base
point has, along the rotation loop of `γ`, the monodromy of `γ` itself.

Reparametrized to circle maps (`TauCeti.MooreFreeLoopSpace.toCircleMap`), the rotation of `γ` by
the fraction `s` of its length is `γ` precomposed with multiplication by `exp (2πis)`
(`TauCeti.MooreFreeLoopSpace.toCircleMap_rotate`). So the torus swept out by the rotation loop
factors through the circle.

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
* `TauCeti.MooreFreeLoopSpace.map_basepointMap_rotationLoop`: the base points of the rotation loop
  of `γ` trace `γ`.
* `TauCeti.MooreFreeLoopSpace.toCircleMap_rotate`: as a circle map, the rotation by a fraction `s`
  of the length is precomposition with multiplication by `exp (2πis)`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §4.1 (the loop of loops rotating a loop
  around itself).
-/

public noncomputable section

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

/-! ### The rotation as a circle map -/

/-- **Rotation is multiplication on the circle**: reparametrized to the circle, the rotation of a
free Moore loop `γ` by the fraction `s` of its length is `γ` precomposed with multiplication by
`exp (2πis)`. -/
theorem toCircleMap_rotate_unitToCircle (γ : MooreFreeLoopSpace X) (s u : unitInterval) :
    toCircleMap (γ.rotate (γ.length * unitInterval.toNNReal s)) (unitToCircle u) =
      toCircleMap γ (unitToCircle u * unitToCircle s) := by
  have hs := unitInterval.toNNReal_le_one s
  rw [toCircleMap_unitToCircle, MoorePath.toUnitPath_apply, length_toMoorePath, length_rotate,
    unitToCircle_apply, unitToCircle_apply, ← Circle.exp_add]
  rcases le_or_gt ((u : ℝ) + s) 1 with hus | hus
  · -- Before `γ` ends, the rotation runs along `γ` from time `L s`.
    have hI : (u : ℝ) + s ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨add_nonneg (unitInterval.nonneg u) (unitInterval.nonneg s), hus⟩
    have hle : γ.length * unitInterval.toNNReal u ≤
        γ.length - γ.length * unitInterval.toNNReal s := by
      rw [le_tsub_iff_right (mul_le_of_le_one_right' hs), ← mul_add]
      exact mul_le_of_le_one_right' (by rw [← NNReal.coe_le_coe]; simpa using hus)
    have harg : 2 * Real.pi * u + 2 * Real.pi * s =
        2 * Real.pi * ((⟨(u : ℝ) + s, hI⟩ : unitInterval) : ℝ) := by
      simp only
      ring
    rw [rotate_apply_of_le _ hle, harg, ← unitToCircle_apply, toCircleMap_unitToCircle,
      MoorePath.toUnitPath_apply, length_toMoorePath]
    congr 1
    ext
    simp only [NNReal.coe_add, NNReal.coe_mul, unitInterval.coe_toNNReal]
    ring
  · -- After `γ` ends, the rotation runs along `γ` from its start, and `exp` has period `2π`.
    have hI : (u : ℝ) + s - 1 ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨by linarith, by linarith [unitInterval.le_one u, unitInterval.le_one s]⟩
    have hv : (u : ℝ) + s - 1 ≤ s := by linarith [unitInterval.le_one u]
    have hlen : γ.length * unitInterval.toNNReal u = γ.length -
        γ.length * unitInterval.toNNReal s + γ.length * NNReal.mk _ hI.1 := by
      have hsub : ((γ.length - γ.length * unitInterval.toNNReal s : ℝ≥0) : ℝ) =
          γ.length - γ.length * s := by
        rw [NNReal.coe_sub (mul_le_of_le_one_right' hs), NNReal.coe_mul,
          unitInterval.coe_toNNReal]
      ext
      rw [NNReal.coe_add, hsub, NNReal.coe_mul, NNReal.coe_mul, unitInterval.coe_toNNReal,
        NNReal.coe_mk]
      ring
    have harg : 2 * Real.pi * u + 2 * Real.pi * s =
        2 * Real.pi * ((⟨(u : ℝ) + s - 1, hI⟩ : unitInterval) : ℝ) + 2 * Real.pi := by
      simp only
      ring
    rw [hlen, rotate_apply_length_sub_add,
      min_eq_left (by gcongr; rw [← NNReal.coe_le_coe]; simpa using hv), harg,
      Circle.exp_add_two_pi, ← unitToCircle_apply, toCircleMap_unitToCircle,
      MoorePath.toUnitPath_apply, length_toMoorePath, unitInterval.toNNReal_mk]

/-- **Rotation is multiplication on the circle**: as a circle map, the rotation of `γ` by the
fraction `s` of its length is `γ` precomposed with multiplication by `exp (2πis)`. -/
theorem toCircleMap_rotate (γ : MooreFreeLoopSpace X) (s : unitInterval) :
    toCircleMap (γ.rotate (γ.length * unitInterval.toNNReal s)) =
      (toCircleMap γ).comp (ContinuousMap.mulRight (unitToCircle s)) :=
  ContinuousMap.ext_unitToCircle fun u ↦ toCircleMap_rotate_unitToCircle γ s u

end MooreFreeLoopSpace

end TauCeti
