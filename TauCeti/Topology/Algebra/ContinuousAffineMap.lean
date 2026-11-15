/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Topology.Algebra.ContinuousAffineMap

/-!
# Homogenization of continuous affine maps

`ContinuousAffineMap.homogenize` extends an affine map `g : V →ᴬ[R] W` to the continuous
linear map on `V × R` sending `(x, t)` to `g.contLinear x + t • g 0`. Its height-one slice
recovers `g`; over a division ring, a nonzero-height value is `t • g (t⁻¹ • x)`.
This construction supplies the linear functionals used to homogenize affine inequalities
and the linear pieces used to extend piecewise-affine maps to geometric cones.

Adapted from `Mei/Geometry/Convex/Homogenization/Inequalities.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`3d2e9c869ee44c41ae9c7b5c6e2042898430d0ca`, licensed under Apache 2.0.
-/

public section

namespace ContinuousAffineMap

section Ring

variable {R V W : Type*} [Ring R] [TopologicalSpace R]
  [AddCommGroup V] [Module R V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [AddCommGroup W] [Module R W] [TopologicalSpace W] [IsTopologicalAddGroup W]
  [ContinuousSMul R W]

/-- The linear map on `V × R` homogenizing an affine map `g`: it sends `(x, t)` to
`g.contLinear x + t • g 0`. -/
def homogenize (g : V →ᴬ[R] W) : (V × R) →L[R] W :=
  g.contLinear.comp (ContinuousLinearMap.fst R V R) +
    (ContinuousLinearMap.snd R V R).smulRight (g 0)

/-- Homogenization is the sum of the linear part and the height times the offset. -/
theorem homogenize_def (g : V →ᴬ[R] W) :
    g.homogenize = g.contLinear.comp (ContinuousLinearMap.fst R V R) +
      (ContinuousLinearMap.snd R V R).smulRight (g 0) := (rfl)

/-- At height `t`, homogenization adds `t` times the value of the affine map at zero. -/
@[simp]
theorem homogenize_apply (g : V →ᴬ[R] W) (x : V) (t : R) :
    g.homogenize (x, t) = g.contLinear x + t • g 0 := (rfl)

/-- At height one, the homogenized map recovers the affine map. -/
@[simp high] -- Apply before `homogenize_apply` expands the value into linear part and offset.
theorem homogenize_apply_one (g : V →ᴬ[R] W) (x : V) : g.homogenize (x, (1 : R)) = g x := by
  have h := g.map_vadd (0 : V) x
  simpa [homogenize_apply] using h.symm

@[simp]
theorem homogenize_zero : (0 : V →ᴬ[R] W).homogenize = 0 := by
  apply ContinuousLinearMap.ext
  rintro ⟨x, t⟩
  simp [homogenize_apply]

@[simp]
theorem homogenize_add (g h : V →ᴬ[R] W) :
    (g + h).homogenize = g.homogenize + h.homogenize := by
  apply ContinuousLinearMap.ext
  rintro ⟨x, t⟩
  simp [homogenize_apply, smul_add, add_add_add_comm]

@[simp]
theorem homogenize_neg (g : V →ᴬ[R] W) : (-g).homogenize = -g.homogenize := by
  apply ContinuousLinearMap.ext
  rintro ⟨x, t⟩
  simp [homogenize_apply, add_comm]

@[simp]
theorem homogenize_sub (g h : V →ᴬ[R] W) :
    (g - h).homogenize = g.homogenize - h.homogenize := by
  simp [sub_eq_add_neg]

@[simp]
theorem homogenize_smul {S : Type*} [Monoid S] [DistribMulAction S W]
    [SMulCommClass R S W] [ContinuousConstSMul S W] (c : S) (g : V →ᴬ[R] W) :
    (c • g).homogenize = c • g.homogenize := by
  apply ContinuousLinearMap.ext
  rintro ⟨x, t⟩
  simp [homogenize_apply, smul_add, smul_comm t c]

@[simp]
theorem homogenize_const (w : W) :
    (const R V w).homogenize = (ContinuousLinearMap.snd R V R).smulRight w := by
  apply ContinuousLinearMap.ext
  rintro ⟨x, t⟩
  simp

@[simp]
theorem _root_.ContinuousLinearMap.homogenize_toContinuousAffineMap (g : V →L[R] W) :
    g.toContinuousAffineMap.homogenize = g.comp (ContinuousLinearMap.fst R V R) := by
  apply ContinuousLinearMap.ext
  rintro ⟨x, t⟩
  simp [homogenize_apply]

end Ring

/-- At a nonzero height `t`, the homogenized map is `t` times the affine map at
`t⁻¹ • x`. -/
theorem homogenize_apply_of_ne_zero
    {R V W : Type*} [DivisionRing R] [TopologicalSpace R]
    [AddCommGroup V] [Module R V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [AddCommGroup W] [Module R W] [TopologicalSpace W] [IsTopologicalAddGroup W]
    [ContinuousSMul R W] (g : V →ᴬ[R] W) (x : V) {t : R} (ht : t ≠ 0) :
    g.homogenize (x, t) = t • g (t⁻¹ • x) := by
  have heval : g (t⁻¹ • x) = t⁻¹ • g.contLinear x + g 0 := by
    simpa only [vadd_eq_add, add_zero, map_smul,
      ContinuousAffineMap.coe_contLinear] using g.map_vadd 0 (t⁻¹ • x)
  rw [heval, homogenize_apply, smul_add, smul_inv_smul₀ ht]

end ContinuousAffineMap
