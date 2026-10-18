/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Convex.Extrema

/-!
# Local supporting hyperplanes of convex functions are global

A local minimum of a convex function on a convex set is a global minimum
(`IsMinOn.of_isLocalMinOn_of_convexOn`). Applied to `u - ℓ` for a linear functional `ℓ`, this
says that an affine function `x' ↦ u x + ℓ (x' - x)` lying below a convex function `u` near `x`
lies below it on the whole domain. In particular a subgradient of `u` relative to an open
neighbourhood of `x` in the domain is a subgradient relative to the whole domain.

The same holds when the function touching `u` from below at `x` is only differentiable there
rather than affine: if `u - g` has a local minimum at `x` relative to `s` and `g` has derivative
`ℓ` at `x` within `s`, then `x' ↦ u x + ℓ (x' - x)` lies below `u` on all of `s`
(`ConvexOn.add_le_of_isLocalMinOn_sub`). No differentiability of `u` is needed. This is the
first-order condition used for transport costs `h (x - y)` with `h` convex but not
differentiable, as in Gangbo and McCann.

## References

* W. Gangbo and R. J. McCann, *The geometry of optimal transportation*, Acta Math. 177 (1996),
  113--161.
-/

public section

open Filter

open scoped Topology

variable {E : Type*} [AddCommGroup E] [TopologicalSpace E] [Module ℝ E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] {s : Set E} {u : E → ℝ} {x : E}

/-- **Local supporting hyperplanes of a convex function are global.** If `u` is convex on `s`,
`x ∈ s`, and the affine function `x' ↦ u x + ℓ (x' - x)` lies below `u` at the points of `s`
near `x`, then it lies below `u` on all of `s`. -/
theorem ConvexOn.add_le_of_eventually_add_le (hu : ConvexOn ℝ s u) (hx : x ∈ s)
    (ℓ : E →ₗ[ℝ] ℝ) (h : ∀ᶠ x' in 𝓝[s] x, u x + ℓ (x' - x) ≤ u x') :
    ∀ x' ∈ s, u x + ℓ (x' - x) ≤ u x' := by
  have hmin : IsMinOn (fun y => u y - ℓ y) s x :=
    IsMinOn.of_isLocalMinOn_of_convexOn hx
      (h.mono fun x' hx' => by simp only [map_sub] at hx'; linarith)
      (hu.sub (ℓ.concaveOn hu.1))
  intro x' hx'
  have := isMinOn_iff.1 hmin x' hx'
  simp only [map_sub]
  linarith

section Normed

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {s : Set F} {u g : F → ℝ} {x : F}

/-- **A differentiable function touching a convex function from below supports it.** If `u` is
convex on `s`, `x ∈ s`, `u - g` has a local minimum at `x` relative to `s`, and `g` has
derivative `ℓ` at `x` within `s`, then the affine function `x' ↦ u x + ℓ (x' - x)` lies below `u`
on all of `s`. No differentiability of `u` is assumed. -/
theorem ConvexOn.add_le_of_isLocalMinOn_sub (hu : ConvexOn ℝ s u) (hx : x ∈ s)
    {ℓ : F →L[ℝ] ℝ} (hg : HasFDerivWithinAt g ℓ s x)
    (hmin : IsLocalMinOn (fun y => u y - g y) s x) :
    ∀ x' ∈ s, u x + ℓ (x' - x) ≤ u x' := by
  intro x' hx'
  -- Along the segment `t ↦ x + t • (x' - x)`, the difference quotients of `g` at `0⁺` are
  -- bounded by those of `u`, which by convexity are at most the full slope `u x' - u x`.
  have hpt (t : ℝ) : (1 - t) • x + t • x' = x + t • (x' - x) := by
    rw [sub_smul, one_smul, smul_sub]
    abel
  have hseg : ∀ t ∈ Set.Ioo (0 : ℝ) 1, x + t • (x' - x) ∈ s := fun t ht =>
    hpt t ▸ hu.1 hx hx' (sub_nonneg.2 ht.2.le) ht.1.le (sub_add_cancel 1 t)
  have hpath : Tendsto (fun t : ℝ => x + t • (x' - x)) (𝓝[>] 0) (𝓝[s] x) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · exact (Continuous.tendsto' (by fun_prop) 0 x (by simp)).mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsGT one_pos] with t ht using hseg t ht
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), t⁻¹ • (g (x + t • (x' - x)) - g x) ≤ u x' - u x := by
    filter_upwards [hpath.eventually hmin, Ioo_mem_nhdsGT one_pos] with t hmin_t ht
    have hconv := hu.2 hx hx' (sub_nonneg.2 ht.2.le) ht.1.le (sub_add_cancel 1 t)
    rw [hpt, smul_eq_mul, smul_eq_mul] at hconv
    rw [smul_eq_mul, inv_mul_le_iff₀ ht.1]
    linarith
  have hslope : Tendsto (fun t : ℝ => t⁻¹ • (g (x + t • (x' - x)) - g x)) (𝓝[>] 0)
      (𝓝 (ℓ (x' - x))) := by
    refine hg.lim ?_ ?_ ?_
    · exact (Continuous.tendsto' (by fun_prop) 0 0 (by simp)).mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsGT one_pos] with t ht using hseg t ht
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
      rw [inv_smul_smul₀ ht.ne']
  have := le_of_tendsto hslope hev
  linarith

end Normed
