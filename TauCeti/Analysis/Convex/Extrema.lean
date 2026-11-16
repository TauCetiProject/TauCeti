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
(`IsMinOn.of_isLocalMinOn_of_convexOn`). Applied to `u - ℓ` for a linear map `ℓ`, this
says that an affine function `x' ↦ u x + ℓ (x' - x)` lying below a convex function `u` near `x`
lies below it on the whole domain. In particular a subgradient of `u` relative to an open
neighbourhood of `x` in the domain is a subgradient relative to the whole domain.

The same holds when the function touching `u` from below at `x` is only differentiable there
rather than affine: if `u - g` has a local minimum at `x` relative to `s` and `g` has derivative
`ℓ` at `x` within `s`, then `x' ↦ u x + ℓ (x' - x)` lies below `u` on all of `s`
(`ConvexOn.add_le_of_isLocalMinOn_sub`). No differentiability of `u` is needed. This is the
first-order condition used for transport costs `h (x - y)` with `h` convex but not
differentiable, as in Gangbo and McCann.

Both results hold for functions on a real topological vector space with values in an ordered real
vector space (carrying an order-closed vector space topology for the second); the case of
real-valued functions is the one of interest.

## References

* W. Gangbo and R. J. McCann, *The geometry of optimal transportation*, Acta Math. 177 (1996),
  113--161.
-/

public section

open Filter

open scoped Topology

variable {E β : Type*} [AddCommGroup E] [TopologicalSpace E] [Module ℝ E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [AddCommGroup β] [PartialOrder β] [IsOrderedAddMonoid β]
  [Module ℝ β] [IsOrderedModule ℝ β] [PosSMulReflectLE ℝ β] {s : Set E} {u g : E → β} {x : E}

/-- **Local supporting hyperplanes of a convex function are global.** If `u` is convex on `s`,
`x ∈ s`, and the affine function `x' ↦ u x + ℓ (x' - x)` lies below `u` at the points of `s`
near `x`, then it lies below `u` on all of `s`. -/
theorem ConvexOn.add_le_of_eventually_add_le (hu : ConvexOn ℝ s u) (hx : x ∈ s)
    (ℓ : E →ₗ[ℝ] β) (h : ∀ᶠ x' in 𝓝[s] x, u x + ℓ (x' - x) ≤ u x') :
    ∀ x' ∈ s, u x + ℓ (x' - x) ≤ u x' := by
  have key (x' : E) : u x + ℓ (x' - x) ≤ u x' ↔ (u - ⇑ℓ) x ≤ (u - ⇑ℓ) x' := by
    rw [map_sub, Pi.sub_apply, Pi.sub_apply, sub_le_sub_iff, ← add_sub_assoc, sub_le_iff_le_add]
  simp_rw [key] at h ⊢
  exact IsMinOn.of_isLocalMinOn_of_convexOn hx h (hu.sub (ℓ.concaveOn hu.1))

variable [TopologicalSpace β] [ContinuousAdd β] [ContinuousSMul ℝ β] [OrderClosedTopology β]

/-- **A differentiable function touching a convex function from below supports it.** If `u` is
convex on `s`, `x ∈ s`, `u - g` has a local minimum at `x` relative to `s`, and `g` has
derivative `ℓ` at `x` within `s`, then the affine function `x' ↦ u x + ℓ (x' - x)` lies below `u`
on all of `s`. No differentiability of `u` is assumed. -/
theorem ConvexOn.add_le_of_isLocalMinOn_sub (hu : ConvexOn ℝ s u) (hx : x ∈ s)
    {ℓ : E →L[ℝ] β} (hg : HasFDerivWithinAt g ℓ s x)
    (hmin : IsLocalMinOn (fun y => u y - g y) s x) :
    ∀ x' ∈ s, u x + ℓ (x' - x) ≤ u x' := by
  intro x' hx'
  -- Along the segment `t ↦ x + t • (x' - x)`, the difference quotients of `g` at `0⁺` are
  -- bounded by those of `u`, which by convexity are at most the full slope `u x' - u x`.
  have hpt (t : ℝ) : (1 - t) • x + t • x' = x + t • (x' - x) := by module
  have hd : Tendsto (fun t : ℝ => t • (x' - x)) (𝓝[>] 0) (𝓝 0) :=
    (Continuous.tendsto' (by fun_prop) 0 0 (by simp)).mono_left nhdsWithin_le_nhds
  have hseg : ∀ᶠ t : ℝ in 𝓝[>] 0, x + t • (x' - x) ∈ s := by
    filter_upwards [Ioo_mem_nhdsGT one_pos] with t ht
    exact hu.1.add_smul_sub_mem hx hx' ⟨ht.1.le, ht.2.le⟩
  have hpath : Tendsto (fun t : ℝ => x + t • (x' - x)) (𝓝[>] 0) (𝓝[s] x) :=
    tendsto_nhdsWithin_iff.2 ⟨by simpa using hd.const_add x, hseg⟩
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), t⁻¹ • (g (x + t • (x' - x)) - g x) ≤ u x' - u x := by
    filter_upwards [hpath.eventually hmin, Ioo_mem_nhdsGT one_pos] with t hmin_t ht
    have hconv := hu.2 hx hx' (sub_nonneg.2 ht.2.le) ht.1.le (sub_add_cancel 1 t)
    rw [hpt, sub_smul, one_smul] at hconv
    rw [inv_smul_le_iff_of_pos ht.1]
    calc g (x + t • (x' - x)) - g x ≤ u (x + t • (x' - x)) - u x :=
        sub_le_sub_iff.2 ((add_comm _ _).trans_le (sub_le_sub_iff.1 hmin_t))
      _ ≤ t • (u x' - u x) := sub_le_iff_le_add.2 (hconv.trans_eq (by rw [smul_sub]; abel))
  have hslope : Tendsto (fun t : ℝ => t⁻¹ • (g (x + t • (x' - x)) - g x)) (𝓝[>] 0)
      (𝓝 (ℓ (x' - x))) := by
    refine hg.lim hd hseg (tendsto_const_nhds.congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    rw [inv_smul_smul₀ ht.ne']
  rw [← le_sub_iff_add_le']
  exact le_of_tendsto hslope hev
