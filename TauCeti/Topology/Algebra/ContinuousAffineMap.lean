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

open scoped Topology in
/-- The nonvanishing set of a nonzero continuous affine map over a division ring with `0` not
isolated is dense. -/
theorem dense_setOf_ne_zero {𝕜 E F : Type*} [DivisionRing 𝕜] [TopologicalSpace 𝕜]
    [Filter.NeBot (𝓝[≠] (0 : 𝕜))] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
    [ContinuousAdd E] [ContinuousSMul 𝕜 E] [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
    {g : E →ᴬ[𝕜] F} (hg : g ≠ 0) : Dense {x : E | g x ≠ 0} := by
  have hex : ∃ y : E, g y ≠ 0 := by
    by_contra! h
    exact hg (ContinuousAffineMap.ext h)
  obtain ⟨y, hy⟩ := hex
  rw [dense_iff_closure_eq]
  refine Set.eq_univ_of_forall fun x => ?_
  by_cases hx : g x ≠ 0
  · exact subset_closure hx
  · rw [not_not] at hx
    let γ : 𝕜 → E := fun t => t • (y - x) + x
    have hγ_cont : Continuous γ := by fun_prop
    have hγ0 : γ 0 = x := by simp [γ]
    have hmem : ∀ᶠ t in 𝓝[≠] (0 : 𝕜), γ t ∈ {z : E | g z ≠ 0} := by
      filter_upwards [self_mem_nhdsWithin] with t (ht : t ≠ 0)
      have hval : g (γ t) = t • g y := by
        have hlin : g.toAffineMap.linear (y - x) = g y := by
          have := g.toAffineMap.map_vadd x (y - x)
          simpa [vadd_eq_add, sub_add_cancel, hx] using this.symm
        have := g.toAffineMap.map_vadd x (t • (y - x))
        simpa [γ, vadd_eq_add, hx, hlin] using this
      rw [hval]
      intro h0
      exact hy (by simpa [ht] using congrArg (t⁻¹ • ·) h0)
    have htend : Filter.Tendsto γ (𝓝[≠] (0 : 𝕜)) (𝓝 x) := by
      rw [← hγ0]
      exact hγ_cont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    exact mem_closure_of_tendsto htend hmem

end ContinuousAffineMap
