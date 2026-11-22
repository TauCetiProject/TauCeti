/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Gauge
public import Mathlib.Topology.EMetricSpace.Lipschitz

/-!
# Radial projection onto the frontier of a convex body

Let `K` be a convex subset of a real normed space `E` and `p` an interior point of `K`. The
**radial projection** of `K` from `p` sends a point `x ≠ p` to the point where the ray from `p`
through `x` leaves `K`:

`ψ x = p + (g (x - p))⁻¹ • (x - p)`,

where `g` is the gauge of `K` centred at `p`, `g v = gauge {v | p + v ∈ K} v`
(`TauCeti.radialProjection`). When `K` is bounded, `ψ` maps `E ∖ {p}` to the frontier of `K`
(`TauCeti.radialProjection_mem_frontier`). When `K` is moreover convex, `ψ` fixes that frontier
pointwise (`TauCeti.radialProjection_eq_self_of_mem_frontier`), and it is continuous away from
`p`.

The projection blows up only at its centre, at the rate `1 / ‖x - p‖`. Suppose that
`ball p ρ ⊆ K ⊆ closedBall p R` with `ρ > 0`. The gauge is then `ρ⁻¹`-Lipschitz, and every value
`ψ x` lies in `closedBall p R`. Writing `ψ x - ψ y` as `a (u - v) + a (g v - g u) (b v)` with
`u = x - p`, `v = y - p`, `a = (g u)⁻¹`, `b = (g v)⁻¹` gives the bound

`‖ψ x - ψ y‖ ≤ R / r * (1 + R / ρ) * ‖x - y‖`

for `x, y` outside `ball p r` (`TauCeti.lipschitzOnWith_radialProjection`). Hence near a point `x`
the projection is Lipschitz with constant `2 R (1 + R / ρ) / ‖x - p‖`
(`TauCeti.lipschitzOnWith_radialProjection_ball`).

In the deformation theorem of Federer and Fleming, a current is pushed from each cube of a grid to
the boundary of the cube by a radial projection from a randomly shifted centre. The local
Lipschitz constant above is what enters the mass of the pushed current, through an integral of
`‖x - p‖ ^ (-k)` against the mass measure of a `k`-current. In dimension `n > k` that kernel is
integrable in the centre `p`, and the average over the centre is controlled by
`TauCeti.lintegral_setLIntegral_enorm_sub_rpow_le`.

## Main declarations

* `TauCeti.radialProjection K p`: the radial projection of `K` from `p`.
* `TauCeti.radialProjection_mem_frontier`, `TauCeti.radialProjection_eq_self_of_mem_frontier`:
  it is a retraction of `E ∖ {p}` onto the frontier of a bounded convex neighbourhood of `p`.
* `TauCeti.radialProjection_radialProjection`: it is idempotent.
* `TauCeti.norm_radialProjection_sub_le`: its values lie in `closedBall p R` when `K` does.
* `TauCeti.continuousOn_radialProjection`: it is continuous away from `p`.
* `TauCeti.lipschitzOnWith_radialProjection`,
  `TauCeti.lipschitzOnWith_radialProjection_ball`: the Lipschitz bounds away from `p`, and
  `TauCeti.locallyLipschitzOn_radialProjection`: it is locally Lipschitz away from `p`.

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
(`TauCeti.radialProjection_mem_frontier`). It sends `p` to itself. -/
noncomputable def radialProjection (K : Set E) (p x : E) : E :=
  p + (gauge ((p + ·) ⁻¹' K) (x - p))⁻¹ • (x - p)

theorem radialProjection_def (K : Set E) (p x : E) :
    radialProjection K p x = p + (gauge ((p + ·) ⁻¹' K) (x - p))⁻¹ • (x - p) :=
  (rfl)

@[simp]
theorem radialProjection_self (K : Set E) (p : E) : radialProjection K p p = p := by
  simp [radialProjection]

/-! ### The gauge centred at an interior point -/

omit [NormedSpace ℝ E] in
/-- The translate of a neighbourhood of `p` is a neighbourhood of `0`. -/
private theorem preimage_add_mem_nhds_zero (hp : K ∈ 𝓝 p) : (p + ·) ⁻¹' K ∈ 𝓝 (0 : E) :=
  (continuous_const_add p).continuousAt.preimage_mem_nhds (by simpa using hp)

/-- The translate of a bounded set is von Neumann bounded. -/
private theorem isVonNBounded_preimage_add (hb : Bornology.IsBounded K) :
    Bornology.IsVonNBounded ℝ ((p + ·) ⁻¹' K) :=
  (NormedSpace.isVonNBounded_iff ℝ).2 <| by
    simpa [← image_vadd, image_add_left] using hb.vadd (-p)

/-- The gauge of `K` centred at an interior point `p` is positive off `p`. -/
private theorem gauge_sub_pos (hp : K ∈ 𝓝 p) (hb : Bornology.IsBounded K) (hx : x ≠ p) :
    0 < gauge ((p + ·) ⁻¹' K) (x - p) :=
  (gauge_pos (absorbent_nhds_zero (preimage_add_mem_nhds_zero hp))
    (isVonNBounded_preimage_add hb)).2 (sub_ne_zero.2 hx)

/-- A point lies on the frontier of a convex neighbourhood `K` of `p` exactly when the gauge of `K`
centred at `p` takes the value one there. -/
private theorem gauge_sub_eq_one_iff (hK : Convex ℝ K) (hp : K ∈ 𝓝 p) :
    gauge ((p + ·) ⁻¹' K) (x - p) = 1 ↔ x ∈ frontier K := by
  have hfr : frontier ((p + ·) ⁻¹' K) = (p + ·) ⁻¹' frontier K :=
    ((Homeomorph.addLeft p).preimage_frontier K).symm
  rw [gauge_eq_one_iff_mem_frontier (hK.translate_preimage_right p)
    (preimage_add_mem_nhds_zero hp), hfr]
  simp

/-! ### Retraction onto the frontier -/

/-- For a bounded neighbourhood `K` of `p`, the radial projection sends every `x ≠ p` to the
frontier of `K`. No convexity is needed: the point `p + (g (x - p))⁻¹ • (x - p)` is a limit of
points of `K` on the ray, and it is not interior since its gauge is one. -/
theorem radialProjection_mem_frontier (hp : K ∈ 𝓝 p) (hb : Bornology.IsBounded K) (hx : x ≠ p) :
    radialProjection K p x ∈ frontier K := by
  set s := (p + ·) ⁻¹' K
  have hs : Absorbent ℝ s := absorbent_nhds_zero (preimage_add_mem_nhds_zero hp)
  have hg : 0 < gauge s (x - p) := gauge_sub_pos hp hb hx
  have hfr : frontier s = (p + ·) ⁻¹' frontier K :=
    ((Homeomorph.addLeft p).preimage_frontier K).symm
  suffices h : (gauge s (x - p))⁻¹ • (x - p) ∈ frontier s by
    rw [hfr] at h
    exact h
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
    rw [mem_ofPred_eq, gauge_smul_of_nonneg (inv_nonneg.2 hg.le), smul_eq_mul,
      inv_mul_cancel₀ hg.ne'] at h
    exact lt_irrefl _ h

/-- The radial projection fixes the frontier of a convex neighbourhood of its centre. -/
theorem radialProjection_eq_self_of_mem_frontier (hK : Convex ℝ K) (hp : K ∈ 𝓝 p)
    (hx : x ∈ frontier K) : radialProjection K p x = x := by
  rw [radialProjection, (gauge_sub_eq_one_iff hK hp).2 hx, inv_one, one_smul,
    add_sub_cancel]

/-- The radial projection is idempotent. -/
@[simp]
theorem radialProjection_radialProjection (hK : Convex ℝ K) (hp : K ∈ 𝓝 p)
    (hb : Bornology.IsBounded K) (x : E) :
    radialProjection K p (radialProjection K p x) = radialProjection K p x := by
  rcases eq_or_ne x p with rfl | hx
  · simp
  · exact radialProjection_eq_self_of_mem_frontier hK hp (radialProjection_mem_frontier hp hb hx)

/-- If `K ⊆ closedBall p R`, the radial projection of `K` from an interior point `p` takes values
in `closedBall p R`. -/
theorem norm_radialProjection_sub_le (hp : K ∈ 𝓝 p)
    (hR : K ⊆ closedBall p R) (x : E) : ‖radialProjection K p x - p‖ ≤ R := by
  rw [← dist_eq_norm, ← mem_closedBall]
  rcases eq_or_ne x p with rfl | hx
  · simpa using hR (mem_of_mem_nhds hp)
  · exact closure_minimal hR isClosed_closedBall <| frontier_subset_closure <|
      radialProjection_mem_frontier hp (isBounded_closedBall.subset hR) hx

/-- The radial projection of a bounded convex neighbourhood of `p` is continuous away from
`p`. -/
theorem continuousOn_radialProjection (hK : Convex ℝ K) (hp : K ∈ 𝓝 p)
    (hb : Bornology.IsBounded K) : ContinuousOn (radialProjection K p) {p}ᶜ := by
  have hg : Continuous (gauge ((p + ·) ⁻¹' K)) :=
    continuous_gauge (hK.translate_preimage_right p) (preimage_add_mem_nhds_zero hp)
  refine continuousOn_const.add (ContinuousOn.smul ?_ (by fun_prop))
  exact ((hg.comp (by fun_prop)).continuousOn).inv₀ fun x hx ↦ (gauge_sub_pos hp hb hx).ne'

/-! ### Lipschitz bounds away from the centre -/

/-- If `ball p ρ ⊆ K` for a convex `K`, the gauge of `K` centred at `p` is `ρ⁻¹`-Lipschitz. -/
private theorem abs_gauge_sub_le (hK : Convex ℝ K) (hρ : 0 < ρ) (hball : ball p ρ ⊆ K)
    (u v : E) : |gauge ((p + ·) ⁻¹' K) u - gauge ((p + ·) ⁻¹' K) v| ≤ ‖u - v‖ / ρ := by
  have := ((hK.translate_preimage_right p).lipschitzWith_gauge (r := ρ.toNNReal)
    (Real.toNNReal_pos.2 hρ) fun w hw ↦ hball (by
      rw [mem_ball_zero_iff, Real.coe_toNNReal _ hρ.le] at hw
      simpa [mem_ball, dist_eq_norm] using hw)).dist_le_mul u v
  rw [Real.dist_eq, dist_eq_norm, NNReal.coe_inv, Real.coe_toNNReal _ hρ.le] at this
  rwa [div_eq_inv_mul]

/-- If `K ⊆ closedBall p R`, the inverse of the gauge of `K` centred at an interior point `p` is
at most `R / r` at distance at least `r > 0` from `p`. -/
private theorem inv_gauge_sub_le {y : E} (hp : K ∈ 𝓝 p) (hR : K ⊆ closedBall p R) (hr : 0 < r)
    (hy : r ≤ ‖y - p‖) : (gauge ((p + ·) ⁻¹' K) (y - p))⁻¹ ≤ R / r := by
  have hpos := gauge_sub_pos hp (isBounded_closedBall.subset hR) (x := y)
    (by rintro rfl; simp at hy; linarith)
  rw [inv_eq_one_div, div_le_div_iff₀ hpos hr, one_mul]
  calc r ≤ ‖y - p‖ := hy
    _ = ‖radialProjection K p y - p‖ * gauge ((p + ·) ⁻¹' K) (y - p) := by
        rw [radialProjection, add_sub_cancel_left, norm_smul,
          Real.norm_of_nonneg (inv_nonneg.2 hpos.le)]
        field_simp
    _ ≤ R * gauge ((p + ·) ⁻¹' K) (y - p) := by gcongr; exact norm_radialProjection_sub_le hp hR y

/-- **The Lipschitz bound of the radial projection.** If `ball p ρ ⊆ K ⊆ closedBall p R` for a
convex `K` and `ρ > 0`, the radial projection of `K` from `p` is
`R / r * (1 + R / ρ)`-Lipschitz outside `ball p r`, for every `r > 0`. -/
theorem lipschitzOnWith_radialProjection (hK : Convex ℝ K) (hρ : 0 < ρ)
    (hball : ball p ρ ⊆ K) (hR : K ⊆ closedBall p R) (hr : 0 < r) :
    LipschitzOnWith (Real.toNNReal (R / r * (1 + R / ρ))) (radialProjection K p)
      (ball p r)ᶜ := by
  have hp : K ∈ 𝓝 p := Filter.mem_of_superset (ball_mem_nhds p hρ) hball
  have hb : Bornology.IsBounded K := isBounded_closedBall.subset hR
  have hR0 : 0 ≤ R := by simpa using hR (mem_of_mem_nhds hp)
  set g := gauge ((p + ·) ⁻¹' K)
  -- The values of the projection lie in `closedBall p R`.
  have hval : ∀ y, ‖(g (y - p))⁻¹ • (y - p)‖ ≤ R := fun y ↦ by
    simpa [radialProjection] using norm_radialProjection_sub_le hp hR y
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ ?_
  have hgx : 0 < g (x - p) := gauge_sub_pos hp hb (x := x) (by rintro rfl; simp at hx; linarith)
  have hgy : 0 < g (y - p) := gauge_sub_pos hp hb (x := y) (by rintro rfl; simp at hy; linarith)
  set a := (g (x - p))⁻¹
  set b := (g (y - p))⁻¹
  have ha : 0 ≤ a := inv_nonneg.2 hgx.le
  -- `ψ x - ψ y = a (u - v) + a (g v - g u) (b v)` with `u = x - p`, `v = y - p`.
  have hsplit : radialProjection K p x - radialProjection K p y =
      a • (x - y) + (a * (g (y - p) - g (x - p))) • (b • (y - p)) := by
    have hab : a * (g (y - p) - g (x - p)) * b = a - b := by
      simp only [a, b]
      field_simp
    rw [radialProjection, radialProjection, smul_smul, hab]
    simp only [sub_smul, smul_sub]
    abel
  rw [dist_eq_norm, hsplit, Real.coe_toNNReal _ (by positivity), dist_eq_norm]
  have hdiff : |g (y - p) - g (x - p)| ≤ ‖x - y‖ / ρ := by
    simpa [abs_sub_comm, sub_sub_sub_cancel_right] using
      abs_gauge_sub_le hK hρ hball (x - p) (y - p)
  calc ‖a • (x - y) + (a * (g (y - p) - g (x - p))) • (b • (y - p))‖
      ≤ a * ‖x - y‖ + a * |g (y - p) - g (x - p)| * R := by
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [norm_smul, Real.norm_of_nonneg ha]
        · rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg ha]
          gcongr
          exact hval y
    _ ≤ a * ‖x - y‖ + a * (‖x - y‖ / ρ) * R := by gcongr
    _ = a * (1 + R / ρ) * ‖x - y‖ := by ring
    _ ≤ R / r * (1 + R / ρ) * ‖x - y‖ := by
        gcongr
        exact inv_gauge_sub_le hp hR hr (by simpa [dist_eq_norm] using hx)

/-- **The local Lipschitz bound of the radial projection.** If `ball p ρ ⊆ K ⊆ closedBall p R` for
a convex `K` and `ρ > 0`, then near every `x ≠ p`, on `ball x (‖x - p‖ / 2)`, the radial projection
of `K` from `p` is Lipschitz with constant `2 R (1 + R / ρ) / ‖x - p‖`. -/
theorem lipschitzOnWith_radialProjection_ball (hK : Convex ℝ K) (hρ : 0 < ρ)
    (hball : ball p ρ ⊆ K) (hR : K ⊆ closedBall p R) (hx : x ≠ p) :
    LipschitzOnWith (Real.toNNReal (2 * R * (1 + R / ρ) / ‖x - p‖)) (radialProjection K p)
      (ball x (‖x - p‖ / 2)) := by
  have hd : 0 < ‖x - p‖ := norm_pos_iff.2 (sub_ne_zero.2 hx)
  have hsub : ball x (‖x - p‖ / 2) ⊆ (ball p (‖x - p‖ / 2))ᶜ := fun y hy ↦ by
    rw [mem_ball, dist_comm, dist_eq_norm] at hy
    rw [mem_compl_iff, mem_ball, not_lt, dist_eq_norm]
    linarith [norm_sub_le_norm_sub_add_norm_sub x y p]
  have h := (lipschitzOnWith_radialProjection hK hρ hball hR (half_pos hd)).mono hsub
  convert h using 3
  field_simp

/-- The radial projection of a bounded convex neighbourhood of `p` is locally Lipschitz away from
`p`. -/
theorem locallyLipschitzOn_radialProjection (hK : Convex ℝ K) (hp : K ∈ 𝓝 p)
    (hb : Bornology.IsBounded K) : LocallyLipschitzOn {p}ᶜ (radialProjection K p) := by
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.1 hp
  obtain ⟨R, hR⟩ := hb.subset_closedBall p
  intro x hx
  have hd : 0 < ‖x - p‖ := norm_pos_iff.2 (sub_ne_zero.2 hx)
  exact ⟨_, ball x (‖x - p‖ / 2), mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x (half_pos hd)),
    lipschitzOnWith_radialProjection_ball hK hρ hball hR hx⟩

end TauCeti
