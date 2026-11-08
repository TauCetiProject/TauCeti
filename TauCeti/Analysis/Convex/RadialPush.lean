/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Gauge
public import Mathlib.Topology.Homotopy.Basic

/-!
# Pushing a convex body onto its frontier away from an interior point

Let `s` be a closed, von Neumann bounded convex set in a real topological vector space, let `p` be
an interior point of `s` and let `U` be a neighbourhood of `p`. Moving every point `y` along the ray
from `p` through `y`, scaled by the gauge of `s` centred at `p`, gives a homotopy of the identity,
relative to the frontier of `s`, which keeps `s` inside itself and ends at a map sending every point
outside `U` to the frontier of `s` (`Convex.exists_homotopyRel_frontier`). The points of `s`
near `p` are spread over the whole of `s` at the end, so the homotopy is defined and continuous on
the whole space.

This is the deformation which, read through the characteristic map of a cell of a CW complex,
pushes a map missing a neighbourhood of a point of an open cell off the whole cell. It generalises
`TauCeti.radialPush`, which pushes the closed unit ball away from its centre.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.1, proof of Theorem 4.8, the deformation retraction of `Dᵏ ∖ {p}` onto `∂Dᵏ`.
-/

public section

open Set Metric unitInterval Topology

namespace Convex

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] {s : Set E} {p : E}

/-- **Pushing a convex body onto its frontier away from an interior point.** Let `s` be a closed
von Neumann bounded convex set and `p` an interior point of `s`. For every neighbourhood `U` of `p`
there is a homotopy `H` of the identity, relative to the frontier of `s`, which keeps `s` inside
itself, and whose endpoint sends every point outside `U` to the frontier of `s`. -/
theorem exists_homotopyRel_frontier (hs : Convex ℝ s) (hsc : IsClosed s)
    (hsb : Bornology.IsVonNBounded ℝ s) (hp : p ∈ interior s) {U : Set E} (hU : U ∈ 𝓝 p) :
    ∃ (g : C(E, E)) (H : (ContinuousMap.id E).HomotopyRel g (frontier s)),
      (∀ t, ∀ y ∈ s, H (t, y) ∈ s) ∧ ∀ y ∉ U, g y ∈ frontier s := by
  -- `gauge K` is the gauge of `s` centred at `p`: `y ∈ s ↔ gauge K (y - p) ≤ 1` and
  -- `y ∈ frontier s ↔ gauge K (y - p) = 1`.
  set K : Set E := (p + ·) ⁻¹' s
  have hK : Convex ℝ K := hs.translate_preimage_right p
  have hK₀ : K ∈ 𝓝 (0 : E) := (continuous_const_add p).continuousAt.preimage_mem_nhds
    (by simpa using mem_interior_iff_mem_nhds.1 hp)
  have hKb : Bornology.IsVonNBounded ℝ K := by
    simpa [← image_vadd, image_add_left] using hsb.vadd (-p)
  have hγ : Continuous (gauge K) := continuous_gauge hK hK₀
  have hmem (y : E) : y ∈ s ↔ gauge K (y - p) ≤ 1 := by
    rw [gauge_le_one_iff_mem_closure hK hK₀, (hsc.preimage (continuous_const_add p)).closure_eq]
    simp
  have hfr (y : E) : y ∈ frontier s ↔ gauge K (y - p) = 1 := by
    have hKfr : frontier K = (p + ·) ⁻¹' frontier s :=
      ((Homeomorph.addLeft p).preimage_frontier s).symm
    rw [gauge_eq_one_iff_mem_frontier hK hK₀, hKfr]
    simp
  -- Points outside `U` have a large gauge, since `K` is bounded.
  obtain ⟨c₀, hc₀, hc₀U⟩ : ∃ c₀ > 0, gauge K ⁻¹' ball 0 c₀ ⊆ (p + ·) ⁻¹' U :=
    (nhds_basis_ball.comap (gauge K)).mem_iff.1 <| by
      rw [comap_gauge_nhds_zero hKb hK₀]
      exact (continuous_const_add p).continuousAt.preimage_mem_nhds (by simpa using hU)
  set c : ℝ := min c₀ 1
  have hc : 0 < c := lt_min hc₀ one_pos
  have hfar (y : E) (hy : y ∉ U) : c ≤ gauge K (y - p) := by
    by_contra! h
    have hball : gauge K (y - p) ∈ ball 0 c₀ := by
      rw [mem_ball, Real.dist_0_eq_abs, abs_of_nonneg (gauge_nonneg _)]
      exact h.trans_le (min_le_left _ _)
    exact hy (by simpa using hc₀U hball)
  -- The point `y` moves to `p + a t y • (y - p)` at time `t`.
  set a : I → E → ℝ := fun t y ↦ (1 - (t : ℝ)) + (t : ℝ) * (max (gauge K (y - p)) c)⁻¹
  have hmax (y : E) : 0 < max (gauge K (y - p)) c := lt_max_of_lt_right hc
  have ha_nonneg (t : I) (y : E) : 0 ≤ a t y :=
    add_nonneg (sub_nonneg.2 t.2.2) (mul_nonneg t.2.1 (inv_nonneg.2 (hmax y).le))
  have hgauge (t : I) (y : E) : gauge K (a t y • (y - p)) =
      (1 - (t : ℝ)) * gauge K (y - p) + (t : ℝ) * (gauge K (y - p) / max (gauge K (y - p)) c) := by
    rw [gauge_smul_of_nonneg (ha_nonneg t y), smul_eq_mul]
    ring
  have hcont : Continuous fun q : I × E ↦ p + a q.1 q.2 • (q.2 - p) := by
    fun_prop (disch := exact fun q ↦ (hmax _).ne')
  have hzero (y : E) : p + a 0 y • (y - p) = y := by simp [a]
  have hfix (t : I) (y : E) (hy : y ∈ frontier s) : p + a t y • (y - p) = y := by
    have h1 : gauge K (y - p) = 1 := (hfr y).1 hy
    have hc1 : max (1 : ℝ) c = 1 := max_eq_left (min_le_right _ _)
    simp [a, h1, hc1]
  let g : C(E, E) :=
    ⟨fun y ↦ p + a 1 y • (y - p), hcont.comp (continuous_const.prodMk continuous_id)⟩
  have hg (y : E) : g y = p + a 1 y • (y - p) := rfl
  refine ⟨g,
    { toFun := fun q ↦ p + a q.1 q.2 • (q.2 - p)
      continuous_toFun := hcont
      map_zero_left := hzero
      map_one_left := fun _ ↦ rfl
      prop' := hfix },
    fun t y hy ↦ ?_, fun y hyU ↦ ?_⟩
  · -- The gauge of the moved point is a convex combination of `gauge K (y - p) ≤ 1` and
    -- `gauge K (y - p) / max (gauge K (y - p)) c ≤ 1`.
    -- The homotopy is `fun q ↦ p + a q.1 q.2 • (q.2 - p)` by construction.
    change p + a t y • (y - p) ∈ s
    rw [hmem, add_sub_cancel_left, hgauge]
    have h1 := (hmem y).1 hy
    have h2 : gauge K (y - p) / max (gauge K (y - p)) c ≤ 1 :=
      (div_le_one (hmax y)).2 (le_max_left _ _)
    nlinarith [t.2.1, t.2.2]
  · -- Outside `U`, the cut-off `c` is inactive, so the endpoint has gauge one.
    have hγc := hfar y hyU
    rw [hfr, hg, add_sub_cancel_left, hgauge, max_eq_left hγc]
    simp [div_self (hc.trans_le hγc).ne']

end Convex
