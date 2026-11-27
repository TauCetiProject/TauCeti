/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.EMetricSpace.Lipschitz
public import TauCeti.Analysis.Convex.Gauge.Translate

/-!
# Radial projection onto the frontier of a convex body

Let `K` be a convex subset of a real normed space `E` and `p` an interior point of `K`. The
**radial projection** of `K` from `p` sends a point `x ≠ p` to the point where the ray from `p`
through `x` leaves `K`:

`ψ x = p + (g (x - p))⁻¹ • (x - p)`,

where `g` is the gauge of `K` centred at `p`, `g v = gauge {v | p + v ∈ K} v`
(`TauCeti.frontierRadialProjection`). When `K` is bounded, `ψ` maps `E ∖ {p}` to the frontier
of `K` (`TauCeti.frontierRadialProjection_mem_frontier`). When `K` is moreover convex, `ψ` fixes
that frontier pointwise (`TauCeti.frontierRadialProjection_eq_self_of_mem_frontier`), and it is
continuous away from `p`.

The Lipschitz constant of the projection blows up only at its centre, at the rate `1 / ‖x - p‖`.
Suppose that `ball p ρ ⊆ K ⊆ closedBall p R` with `ρ > 0`. The gauge is then `ρ⁻¹`-Lipschitz,
and every value `ψ x` lies in `closedBall p R`. Writing `ψ x - ψ y` as
`a (u - v) + a (g v - g u) (b v)` with `u = x - p`, `v = y - p`, `a = (g u)⁻¹`, `b = (g v)⁻¹`
gives the bound

`‖ψ x - ψ y‖ ≤ R / r * (1 + R / ρ) * ‖x - y‖`

for `x, y` outside `ball p r` (`TauCeti.lipschitzOnWith_frontierRadialProjection`). Hence near a
point `x` the projection is Lipschitz with constant `2 R (1 + R / ρ) / ‖x - p‖`
(`TauCeti.lipschitzOnWith_frontierRadialProjection_ball`).

In the deformation theorem of Federer and Fleming, a current is pushed from each cube of a grid to
the boundary of the cube by a radial projection from a randomly shifted centre. The local
Lipschitz constant above is what enters the mass of the pushed current, through an integral of
`‖x - p‖ ^ (-k)` against the mass measure of a `k`-current. In dimension `n > k` that kernel is
integrable in the centre `p`, and the average over the centre is controlled by
`TauCeti.lintegral_setLIntegral_enorm_sub_rpow_le`.

## Main declarations

* `TauCeti.frontierRadialProjection K p`: the radial projection of `K` from `p`.
* `TauCeti.frontierRadialProjection_sub`, `TauCeti.gauge_frontierRadialProjection_sub`: the
  displacement `ψ x - p` from the centre, and its gauge, which is one off the centre.
* `TauCeti.frontierRadialProjection_mem_frontier`,
  `TauCeti.frontierRadialProjection_eq_self_of_mem_frontier`: it is a retraction of `E ∖ {p}`
  onto the frontier of a bounded convex neighbourhood of `p`.
* `TauCeti.frontierRadialProjection_frontierRadialProjection`: it is idempotent.
* `TauCeti.norm_frontierRadialProjection_sub_le`: its values lie in `closedBall p R` when `K`
  does.
* `TauCeti.continuousOn_frontierRadialProjection`: it is continuous away from `p`.
* `TauCeti.lipschitzOnWith_frontierRadialProjection`,
  `TauCeti.lipschitzOnWith_frontierRadialProjection_ball`: the Lipschitz bounds away from `p`,
  and `TauCeti.locallyLipschitzOn_frontierRadialProjection`: it is locally Lipschitz away from
  `p`.

## References

* H. Federer, *Geometric Measure Theory*, §4.2.7 (radial projection of a cube from a point and
  the averaging of its Lipschitz constant).
* L. Simon, *Introduction to Geometric Measure Theory*, Chapter 6, §4 (proof of the deformation
  theorem).
-/

public section

open Metric Set Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Set E} {p x : E}
  {ρ R r : ℝ}

/-- The **radial projection** of `K` from `p`: the point `p + (g (x - p))⁻¹ • (x - p)`, where `g`
is the gauge of `K` centred at `p`. For a bounded convex neighbourhood `K` of `p` and `x ≠ p` it is
the point where the ray from `p` through `x` leaves `K`
(`TauCeti.frontierRadialProjection_mem_frontier`). It sends `p` to itself. -/
noncomputable def frontierRadialProjection (K : Set E) (p x : E) : E :=
  p + (gauge ((p + ·) ⁻¹' K) (x - p))⁻¹ • (x - p)

theorem frontierRadialProjection_def (K : Set E) (p x : E) :
    frontierRadialProjection K p x = p + (gauge ((p + ·) ⁻¹' K) (x - p))⁻¹ • (x - p) :=
  (rfl)

@[simp]
theorem frontierRadialProjection_self (K : Set E) (p : E) :
    frontierRadialProjection K p p = p := by
  simp [frontierRadialProjection]

/-- The displacement of the radial projection of `K` from `p` from its centre. -/
theorem frontierRadialProjection_sub (K : Set E) (p x : E) :
    frontierRadialProjection K p x - p = (gauge ((p + ·) ⁻¹' K) (x - p))⁻¹ • (x - p) :=
  add_sub_cancel_left _ _

/-- The gauge of a bounded neighbourhood `K` of `p`, centred at `p`, is positive off `p`. -/
private theorem gauge_sub_pos (hp : K ∈ 𝓝 p) (hb : Bornology.IsBounded K) (hx : x ≠ p) :
    0 < gauge ((p + ·) ⁻¹' K) (x - p) :=
  (gauge_preimage_add_sub_pos_iff hp ((NormedSpace.isVonNBounded_iff ℝ).2 hb)).2 hx

/-- For a bounded neighbourhood `K` of `p`, the radial projection of `K` from `p` has gauge one,
centred at `p`, at every `x ≠ p`. -/
theorem gauge_frontierRadialProjection_sub (hp : K ∈ 𝓝 p) (hb : Bornology.IsBounded K)
    (hx : x ≠ p) : gauge ((p + ·) ⁻¹' K) (frontierRadialProjection K p x - p) = 1 := by
  have hg := gauge_sub_pos hp hb hx
  rw [frontierRadialProjection_sub, gauge_smul_of_nonneg (inv_nonneg.2 hg.le), smul_eq_mul,
    inv_mul_cancel₀ hg.ne']

/-! ### Retraction onto the frontier -/

/-- For a bounded neighbourhood `K` of `p`, the radial projection sends every `x ≠ p` to the
frontier of `K`. No convexity is needed. -/
theorem frontierRadialProjection_mem_frontier (hp : K ∈ 𝓝 p) (hb : Bornology.IsBounded K)
    (hx : x ≠ p) : frontierRadialProjection K p x ∈ frontier K := by
  -- The point `p + (g (x - p))⁻¹ • (x - p)` is a limit of points of `K` on the ray, and it is not
  -- interior since its gauge is one.
  set s := (p + ·) ⁻¹' K
  have hs : Absorbent ℝ s := absorbent_nhds_zero (preimage_add_mem_nhds_zero hp)
  have hg : 0 < gauge s (x - p) := gauge_sub_pos hp hb hx
  suffices h : frontierRadialProjection K p x - p ∈ frontier s by
    rwa [frontier_preimage_add, mem_preimage, add_sub_cancel] at h
  rw [frontierRadialProjection_sub]
  refine ⟨?_, fun hint ↦ ?_⟩
  · -- The points `t⁻¹ • (x - p)` with `x - p ∈ t • s` and `t` decreasing to the gauge lie in `s`.
    refine mem_closure_of_frequently_of_tendsto (b := 𝓝[≥] (gauge s (x - p)))
      (f := fun t ↦ t⁻¹ • (x - p)) ?_
      (((continuousAt_inv₀ hg.ne').smul continuousAt_const).tendsto.mono_left nhdsWithin_le_nhds)
    rw [(nhdsGE_basis _).frequently_iff]
    intro u hu
    obtain ⟨t, ht, htu, hmem⟩ := exists_lt_of_gauge_lt hs hu
    exact ⟨t, ⟨gauge_le_of_mem ht.le hmem, htu⟩,
      (mem_smul_set_iff_inv_smul_mem₀ ht.ne' _ _).1 hmem⟩
  · -- An interior point has gauge less than one.
    have h := interior_subset_gauge_lt_one s hint
    rw [mem_ofPred_eq, ← frontierRadialProjection_sub,
      gauge_frontierRadialProjection_sub hp hb hx] at h
    exact lt_irrefl _ h

/-- The radial projection fixes the frontier of a convex neighbourhood of its centre. -/
theorem frontierRadialProjection_eq_self_of_mem_frontier (hK : Convex ℝ K) (hp : K ∈ 𝓝 p)
    (hx : x ∈ frontier K) : frontierRadialProjection K p x = x := by
  rw [frontierRadialProjection, (gauge_preimage_add_sub_eq_one_iff_mem_frontier hK hp).2 hx,
    inv_one, one_smul, add_sub_cancel]

/-- The radial projection is idempotent. -/
@[simp]
theorem frontierRadialProjection_frontierRadialProjection (hK : Convex ℝ K) (hp : K ∈ 𝓝 p)
    (hb : Bornology.IsBounded K) (x : E) :
    frontierRadialProjection K p (frontierRadialProjection K p x) =
      frontierRadialProjection K p x := by
  rcases eq_or_ne x p with rfl | hx
  · simp
  · exact frontierRadialProjection_eq_self_of_mem_frontier hK hp
      (frontierRadialProjection_mem_frontier hp hb hx)

/-- If `K ⊆ closedBall p R`, the radial projection of `K` from an interior point `p` takes values
in `closedBall p R`. -/
theorem norm_frontierRadialProjection_sub_le (hp : K ∈ 𝓝 p)
    (hR : K ⊆ closedBall p R) (x : E) : ‖frontierRadialProjection K p x - p‖ ≤ R := by
  rw [← dist_eq_norm, ← mem_closedBall]
  rcases eq_or_ne x p with rfl | hx
  · simpa using hR (mem_of_mem_nhds hp)
  · exact closure_minimal hR isClosed_closedBall <| frontier_subset_closure <|
      frontierRadialProjection_mem_frontier hp (isBounded_closedBall.subset hR) hx

/-- The radial projection of a bounded convex neighbourhood of `p` is continuous away from
`p`. -/
theorem continuousOn_frontierRadialProjection (hK : Convex ℝ K) (hp : K ∈ 𝓝 p)
    (hb : Bornology.IsBounded K) : ContinuousOn (frontierRadialProjection K p) {p}ᶜ := by
  have hg : Continuous (gauge ((p + ·) ⁻¹' K)) :=
    continuous_gauge (hK.translate_preimage_right p) (preimage_add_mem_nhds_zero hp)
  refine continuousOn_const.add (ContinuousOn.smul ?_ (by fun_prop))
  exact ((hg.comp (by fun_prop)).continuousOn).inv₀ fun x hx ↦ (gauge_sub_pos hp hb hx).ne'

/-! ### Lipschitz bounds away from the centre -/

/-- **The Lipschitz bound of the radial projection.** If `ball p ρ ⊆ K ⊆ closedBall p R` for a
convex `K` and `ρ > 0`, the radial projection of `K` from `p` is
`R / r * (1 + R / ρ)`-Lipschitz outside `ball p r`, for every `r > 0`. -/
theorem lipschitzOnWith_frontierRadialProjection (hK : Convex ℝ K) (hρ : 0 < ρ)
    (hball : ball p ρ ⊆ K) (hR : K ⊆ closedBall p R) (hr : 0 < r) :
    LipschitzOnWith (Real.toNNReal (R / r * (1 + R / ρ))) (frontierRadialProjection K p)
      (ball p r)ᶜ := by
  have hp : K ∈ 𝓝 p := Filter.mem_of_superset (ball_mem_nhds p hρ) hball
  have hb : Bornology.IsBounded K := isBounded_closedBall.subset hR
  have hR0 : 0 ≤ R := by simpa using hR (mem_of_mem_nhds hp)
  set g := gauge ((p + ·) ⁻¹' K)
  -- Points outside `ball p r` are at distance at least `r` from `p`.
  have hfar : ∀ y ∈ (ball p r)ᶜ, r ≤ ‖y - p‖ := fun y hy ↦ by
    simpa [dist_eq_norm] using hy
  have hgpos : ∀ y ∈ (ball p r)ᶜ, 0 < g (y - p) := fun y hy ↦
    gauge_sub_pos hp hb (sub_ne_zero.1 (norm_pos_iff.1 (hr.trans_le (hfar y hy))))
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ ?_
  have hgx := hgpos x hx
  have hgy := hgpos y hy
  set a := (g (x - p))⁻¹
  set b := (g (y - p))⁻¹
  have ha : 0 ≤ a := inv_nonneg.2 hgx.le
  -- `ψ x - ψ y = a (u - v) + a (g v - g u) (b v)` with `u = x - p`, `v = y - p`.
  have hsplit : frontierRadialProjection K p x - frontierRadialProjection K p y =
      a • (x - y) + (a * (g (y - p) - g (x - p))) • (b • (y - p)) := by
    have hab : a * (g (y - p) - g (x - p)) * b = a - b := by
      simp only [a, b]
      field_simp
    rw [frontierRadialProjection, frontierRadialProjection, smul_smul, hab]
    simp only [sub_smul, smul_sub]
    abel
  rw [dist_eq_norm, hsplit, Real.coe_toNNReal _ (by positivity), dist_eq_norm]
  have hdiff : |g (y - p) - g (x - p)| ≤ ‖x - y‖ / ρ := by
    simpa [Real.dist_eq, dist_eq_norm, div_eq_inv_mul, norm_sub_rev x y, hρ.le] using
      (hK.lipschitzWith_gauge_preimage_add (Real.toNNReal_pos.2 hρ)
        (by simpa [hρ.le] using hball)).dist_le_mul (y - p) (x - p)
  calc ‖a • (x - y) + (a * (g (y - p) - g (x - p))) • (b • (y - p))‖
      ≤ a * ‖x - y‖ + a * |g (y - p) - g (x - p)| * R := by
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [norm_smul, Real.norm_of_nonneg ha]
        · rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg ha,
            ← frontierRadialProjection_sub]
          gcongr
          exact norm_frontierRadialProjection_sub_le hp hR y
    _ ≤ a * ‖x - y‖ + a * (‖x - y‖ / ρ) * R := by gcongr
    _ = a * (1 + R / ρ) * ‖x - y‖ := by ring
    _ ≤ R / r * (1 + R / ρ) * ‖x - y‖ := by
        gcongr
        -- `a = (g (x - p))⁻¹ ≤ R / ‖x - p‖ ≤ R / r`, where `R > 0` as `ψ x ≠ p`.
        have hRpos : 0 < R := (norm_frontierRadialProjection_sub_le hp hR x).trans_lt' <| by
          rw [frontierRadialProjection_sub, norm_smul]
          exact mul_pos (norm_pos_iff.2 (inv_ne_zero hgx.ne')) (hr.trans_le (hfar x hx))
        rw [inv_le_comm₀ hgx (by positivity), inv_div]
        exact (div_le_div_of_nonneg_right (hfar x hx) hR0).trans
          (le_gauge_preimage_add_of_subset_closedBall hp hR)

/-- **The local Lipschitz bound of the radial projection.** If `ball p ρ ⊆ K ⊆ closedBall p R` for
a convex `K` and `ρ > 0`, then near every `x ≠ p`, on `ball x (‖x - p‖ / 2)`, the radial projection
of `K` from `p` is Lipschitz with constant `2 R (1 + R / ρ) / ‖x - p‖`. -/
theorem lipschitzOnWith_frontierRadialProjection_ball (hK : Convex ℝ K) (hρ : 0 < ρ)
    (hball : ball p ρ ⊆ K) (hR : K ⊆ closedBall p R) (hx : x ≠ p) :
    LipschitzOnWith (Real.toNNReal (2 * R * (1 + R / ρ) / ‖x - p‖)) (frontierRadialProjection K p)
      (ball x (‖x - p‖ / 2)) := by
  have hd : 0 < ‖x - p‖ := norm_pos_iff.2 (sub_ne_zero.2 hx)
  have hsub : ball x (‖x - p‖ / 2) ⊆ (ball p (‖x - p‖ / 2))ᶜ := fun y hy ↦ by
    rw [mem_ball, dist_comm, dist_eq_norm] at hy
    rw [mem_compl_iff, mem_ball, not_lt, dist_eq_norm]
    linarith [norm_sub_le_norm_sub_add_norm_sub x y p]
  have h := (lipschitzOnWith_frontierRadialProjection hK hρ hball hR (half_pos hd)).mono hsub
  convert h using 3
  field_simp

/-- The radial projection of a bounded convex neighbourhood of `p` is locally Lipschitz away from
`p`. -/
theorem locallyLipschitzOn_frontierRadialProjection (hK : Convex ℝ K) (hp : K ∈ 𝓝 p)
    (hb : Bornology.IsBounded K) : LocallyLipschitzOn {p}ᶜ (frontierRadialProjection K p) := by
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.1 hp
  obtain ⟨R, hR⟩ := hb.subset_closedBall p
  intro x hx
  have hd : 0 < ‖x - p‖ := norm_pos_iff.2 (sub_ne_zero.2 hx)
  exact ⟨_, ball x (‖x - p‖ / 2), mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x (half_pos hd)),
    lipschitzOnWith_frontierRadialProjection_ball hK hρ hball hR hx⟩

end TauCeti
