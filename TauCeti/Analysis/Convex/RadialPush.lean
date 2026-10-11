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

Let `s` be a closed bounded convex set in a real normed space, let `p` be an interior point of `s`
and let `ε > 0`. Moving every point `y` along the ray from `p` through `y`, scaled by the gauge of
`s` centred at `p`, gives a homotopy of the identity, relative to the frontier of `s`, which keeps
`s` inside itself and ends at a map sending every point of `s` at distance at least `ε` from `p`
onto the frontier of `s` (`Convex.exists_homotopyRel_frontier`). The points of `s` near `p` are
spread over the whole of `s` at the end, so the homotopy is defined and continuous on the whole
space.

This is the deformation which, read through the characteristic map of a cell of a CW complex,
pushes a map missing a neighbourhood of a point of an open cell off the whole cell. It generalises
`TauCeti.radialPush`, which pushes the closed unit ball away from its centre.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.1, proof of Theorem 4.8, the deformation retraction of `Dᵏ ∖ {p}` onto `∂Dᵏ`.
-/

public section

open Set Metric unitInterval

namespace Convex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E} {p : E}

/-- **Pushing a convex body onto its frontier away from an interior point.** Let `s` be a closed
bounded convex set and `p` an interior point of `s`. For every `ε > 0` there is a homotopy `H` of
the identity, relative to the frontier of `s`, which keeps `s` inside itself, and whose endpoint
sends every point of `s` at distance at least `ε` from `p` to the frontier of `s`. -/
theorem exists_homotopyRel_frontier (hs : Convex ℝ s) (hsc : IsClosed s)
    (hsb : Bornology.IsBounded s) (hp : p ∈ interior s) {ε : ℝ} (hε : 0 < ε) :
    ∃ (g : C(E, E)) (H : (ContinuousMap.id E).HomotopyRel g (frontier s)),
      (∀ t, ∀ y ∈ s, H (t, y) ∈ s) ∧ ∀ y ∈ s, ε ≤ dist y p → g y ∈ frontier s := by
  -- `gauge K` is the gauge of `s` centred at `p`: `y ∈ s ↔ gauge K (y - p) ≤ 1` and
  -- `y ∈ frontier s ↔ gauge K (y - p) = 1`.
  set K : Set E := (p + ·) ⁻¹' s
  have hK : Convex ℝ K := hs.translate_preimage_right p
  have hK₀ : K ∈ nhds (0 : E) := (continuous_const_add p).continuousAt.preimage_mem_nhds
    (by simpa using mem_interior_iff_mem_nhds.1 hp)
  have hγ : Continuous (gauge K) := continuous_gauge hK hK₀
  have hmem (y : E) : y ∈ s ↔ gauge K (y - p) ≤ 1 := by
    rw [gauge_le_one_iff_mem_closure hK hK₀, (hsc.preimage (continuous_const_add p)).closure_eq]
    simp
  have hfr (y : E) : y ∈ frontier s ↔ gauge K (y - p) = 1 := by
    have hKfr : frontier K = (p + ·) ⁻¹' frontier s :=
      ((Homeomorph.addLeft p).preimage_frontier s).symm
    rw [gauge_eq_one_iff_mem_frontier hK hK₀, hKfr]
    simp
  -- Points far from `p` have a large gauge, since `s` lies in a ball around `p`.
  obtain ⟨R, hR⟩ := hsb.subset_closedBall p
  set c : ℝ := min (ε / (max R 1)) 1
  have hR₁ : 0 < max R 1 := lt_max_of_lt_right one_pos
  have hc : 0 < c := lt_min (div_pos hε hR₁) one_pos
  have hfar (y : E) (hy : ε ≤ dist y p) : c ≤ gauge K (y - p) := by
    refine (min_le_left _ _).trans ((div_le_div_of_nonneg_right (by rwa [← dist_eq_norm])
      hR₁.le).trans (le_gauge_of_subset_closedBall (absorbent_nhds_zero hK₀) hR₁.le ?_))
    intro v hv
    simpa [dist_eq_norm] using closedBall_subset_closedBall (le_max_left R 1) (hR hv)
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
    refine continuous_const.add (Continuous.smul ?_ (continuous_snd.sub continuous_const))
    refine (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).add
      ((continuous_subtype_val.comp continuous_fst).mul (Continuous.inv₀ ?_ fun q ↦ (hmax _).ne'))
    exact (hγ.comp (continuous_snd.sub continuous_const)).max continuous_const
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
      prop' := fun t y hy ↦ hfix t y hy },
    fun t y hy ↦ ?_, fun y hy hyp ↦ ?_⟩
  · -- The gauge of the moved point is a convex combination of `gauge K (y - p) ≤ 1` and
    -- `gauge K (y - p) / max (gauge K (y - p)) c ≤ 1`.
    -- The homotopy is `fun q ↦ p + a q.1 q.2 • (q.2 - p)` by construction.
    change p + a t y • (y - p) ∈ s
    rw [hmem, add_sub_cancel_left, hgauge]
    have h1 := (hmem y).1 hy
    have h2 : gauge K (y - p) / max (gauge K (y - p)) c ≤ 1 :=
      (div_le_one (hmax y)).2 (le_max_left _ _)
    nlinarith [t.2.1, t.2.2]
  · -- Far from `p`, the cut-off `c` is inactive, so the endpoint has gauge one.
    have hγc := hfar y hyp
    rw [hfr]
    rw [hg, add_sub_cancel_left, hgauge, max_eq_left hγc]
    simp [div_self (hc.trans_le hγc).ne']

end Convex
