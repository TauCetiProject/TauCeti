/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
public import Mathlib.Analysis.ODE.Gronwall
public import TauCeti.Analysis.Calculus.TangentCone.Basic
public import TauCeti.Analysis.Calculus.TangentCone.InnerProductSpace
public import TauCeti.Analysis.ODE.UniformTime

/-!
# Invariance of closed convex sets under ODEs: Nagumo's criterion

Let `K` be a complete convex subset of a real inner product space and `v` a possibly
time-dependent vector field which is Lipschitz in space near each point of a solution, with one
constant for all times just after the given one. If `v t y` lies in the positive tangent cone
`posTangentConeAt K y` for every `y ∈ K`, then every solution of `x' = v(t, x)` starting in `K`
stays in `K`. For an autonomous locally Lipschitz field and a closed convex set in a complete
space this condition is also necessary, which gives Nagumo's criterion: every solution starting
in `K` stays in `K` exactly when `v y ∈ posTangentConeAt K y` for every `y ∈ K`.

Sufficiency is proved through the supporting half-spaces of `K`. If `p` is a nearest point of
`K` to `x`, then `x - p` is an outward normal of `K` at `p`: `⟪x - p, k - p⟫ ≤ 0` for all `k ∈ K`.
The hypothesis is that `v t p` pairs nonpositively with every outward normal of `K` at `p`; this
holds when `v t p` is a positive tangent vector of `K` at `p`. The squared distance
`d(t) = infDist (x t) K ^ 2` then has upper right Dini derivative at most
`2 ⟪x - p, v t x - v t p⟫ ≤ 2 L d(t)`, so Grönwall's inequality and `d(a) = 0` force `d = 0`.
A Lipschitz constant is only needed near the trajectory, uniformly for nearby later times, and a
continuity argument on the time interval assembles these local bounds.

Necessity holds for any curve: a right derivative of a curve which stays in `K` is a positive
tangent vector of `K`. Together with the Picard–Lindelöf theorem this gives the criterion for an
autonomous locally Lipschitz field on a complete space.

These are the finite-dimensional invariance statements behind Hamilton's maximum principle for
systems: invariance of a closed convex set of curvature operators under the reaction ODE
`R' = Q(R)` is checked by the tangency of `Q` along that set.

## Main results

* `Convex.mapsTo_Icc_of_inner_le_zero`: a solution of a time-dependent locally Lipschitz ODE
  whose field satisfies the supporting half-space inequalities of a complete convex set `K` and
  which starts in `K` stays in `K`.
* `Convex.mapsTo_Icc_of_mem_posTangentConeAt`: the same conclusion when the field is tangent to
  `K` in the positive sense.
* `Convex.forall_mem_posTangentConeAt_iff_forall_mapsTo_Icc`: Nagumo's criterion for an
  autonomous locally Lipschitz field and a closed convex set in a complete space.

## References

* M. Nagumo, *Über die Lage der Integralkurven gewöhnlicher Differentialgleichungen*,
  Proc. Phys.-Math. Soc. Japan 24 (1942), 551–559.
* H. Brezis, *On a characterization of flow-invariant sets*, Comm. Pure Appl. Math. 23 (1970),
  261–263.
* R. S. Hamilton, *Four-manifolds with positive curvature operator*, J. Differential Geom. 24
  (1986), 153–179.
-/

public section

open Filter Metric Set
open scoped NNReal Topology RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace TauCeti

variable {K : Set E} {v : ℝ → E → E} {x : ℝ → E} {a b : ℝ}

/-- The invariance argument with a single Lipschitz constant on a set `U` containing, at each
time, the closed ball around `x t` whose radius is the distance from `x t` to `K`. -/
private theorem mapsTo_Icc_of_lipschitzOnWith (hKc : Convex ℝ K) (hK : IsComplete K) {U : Set E}
    {L : ℝ≥0} (hx : ContinuousOn x (Icc a b))
    (hx' : ∀ t ∈ Ico a b, HasDerivWithinAt x (v t (x t)) (Ici t) t)
    (hv : ∀ t ∈ Ico a b, LipschitzOnWith L (v t) U)
    (hU : ∀ t ∈ Ico a b, closedBall (x t) (infDist (x t) K) ⊆ U)
    (hvK : ∀ t ∈ Ico a b, ∀ y ∈ K, ∀ n, (∀ k ∈ K, ⟪n, k - y⟫ ≤ 0) → ⟪n, v t y⟫ ≤ 0)
    (ha : x a ∈ K) : MapsTo x (Icc a b) K := by
  have hKne : K.Nonempty := ⟨_, ha⟩
  have hmem (z : E) : z ∈ K ↔ infDist z K = 0 := hK.isClosed.mem_iff_infDist_zero hKne
  -- The squared distance `d t = infDist (x t) K ^ 2` has upper right Dini derivative `≤ 2 L d t`.
  have hslope (t : ℝ) (ht : t ∈ Ico a b) (r : ℝ) (hr : 2 * L * infDist (x t) K ^ 2 < r) :
      ∃ᶠ τ in 𝓝[>] t, (τ - t)⁻¹ * (infDist (x τ) K ^ 2 - infDist (x t) K ^ 2) < r := by
    obtain ⟨p, hpK, hp⟩ := exists_norm_eq_iInf_of_complete_convex hKne hK hKc (x t)
    have hpd : ‖x t - p‖ = infDist (x t) K := by
      simp only [hp, infDist_eq_iInf, dist_eq_norm]
    have hnormal := (norm_eq_iInf_iff_real_inner_le_zero hKc hpK).1 hp
    have hxU : x t ∈ U := hU t ht (mem_closedBall_self infDist_nonneg)
    have hpU : p ∈ U := hU t ht (by rw [mem_closedBall, dist_comm, dist_eq_norm, hpd])
    have hbound : 2 * ⟪x t - p, v t (x t)⟫ ≤ 2 * L * infDist (x t) K ^ 2 := by
      have h₁ : ⟪x t - p, v t p⟫ ≤ 0 := hvK t ht p hpK _ hnormal
      have h₂ : ⟪x t - p, v t (x t) - v t p⟫ ≤ ‖x t - p‖ * (L * ‖x t - p‖) :=
        (real_inner_le_norm _ _).trans <|
          mul_le_mul_of_nonneg_left ((hv t ht).norm_sub_le hxU hpU) (norm_nonneg _)
      rw [inner_sub_right] at h₂
      rw [← hpd]
      nlinarith
    refine ((((hx' t ht).sub_const p).norm_sq.liminf_right_slope_le
      (hbound.trans_lt hr)).and_eventually self_mem_nhdsWithin).mono fun τ ⟨hτ, hτt⟩ ↦ ?_
    have hτt : t < τ := mem_Ioi.1 hτt
    rw [slope_def_field] at hτ
    have hle : infDist (x τ) K ^ 2 ≤ ‖x τ - p‖ ^ 2 := by
      gcongr
      · exact infDist_nonneg
      · rw [← dist_eq_norm]
        exact infDist_le_dist_of_mem hpK
    calc (τ - t)⁻¹ * (infDist (x τ) K ^ 2 - infDist (x t) K ^ 2)
        ≤ (τ - t)⁻¹ * (‖x τ - p‖ ^ 2 - ‖x t - p‖ ^ 2) := by
          rw [hpd]
          gcongr
      _ = (‖x τ - p‖ ^ 2 - ‖x t - p‖ ^ 2) / (τ - t) := by rw [div_eq_inv_mul]
      _ < r := hτ
  have hcont : ContinuousOn (fun t ↦ infDist (x t) K ^ 2) (Icc a b) :=
    ((continuous_infDist_pt K).comp_continuousOn hx).pow 2
  have hgron := le_gronwallBound_of_liminf_deriv_right_le
    (f' := fun t ↦ 2 * L * infDist (x t) K ^ 2) (δ := 0) (K := 2 * L) (ε := 0) hcont hslope
    (by simp [(hmem _).1 ha]) (fun t _ ↦ by rw [add_zero])
  intro t ht
  have h := hgron t ht
  rw [gronwallBound_ε0_δ0] at h
  exact (hmem _).2 (pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm h (sq_nonneg _)))

end TauCeti

open TauCeti in
/-- **Invariance of a convex set under an ODE.** Let `K` be a complete convex set and let `x`
solve `x' = v(t, x)` on `[a, b]`, with right derivatives on `[a, b)`. Suppose that, along `K`,
`v t y` pairs nonpositively with every outward normal of `K` at `y`, and that near each `x t` the
field is Lipschitz in space with one constant for all times in a right neighbourhood of `t`. If
`x a ∈ K`, then `x t ∈ K` for all `t ∈ [a, b]`. -/
theorem Convex.mapsTo_Icc_of_inner_le_zero {K : Set E} (hKc : Convex ℝ K) (hK : IsComplete K)
    {v : ℝ → E → E} {x : ℝ → E} {a b : ℝ} (hx : ContinuousOn x (Icc a b))
    (hx' : ∀ t ∈ Ico a b, HasDerivWithinAt x (v t (x t)) (Ici t) t)
    (hv : ∀ t ∈ Ico a b, ∃ L, ∃ U ∈ 𝓝 (x t), ∀ᶠ τ in 𝓝[≥] t, LipschitzOnWith L (v τ) U)
    (hvK : ∀ t ∈ Ico a b, ∀ y ∈ K, ∀ n, (∀ k ∈ K, ⟪n, k - y⟫ ≤ 0) → ⟪n, v t y⟫ ≤ 0)
    (ha : x a ∈ K) : MapsTo x (Icc a b) K := by
  have hclosed : IsClosed (x ⁻¹' K ∩ Icc a b) := by
    rw [inter_comm]
    exact hx.preimage_isClosed_of_isClosed isClosed_Icc hK.isClosed
  refine fun t ht ↦ hclosed.Icc_subset_of_forall_mem_nhdsWithin ha (fun t₀ ⟨ht₀K, ht₀⟩ ↦ ?_) ht
  -- Near `t₀`, the field has one Lipschitz constant on a ball `B(x t₀, r)`, and `x` stays within
  -- `r / 2` of `x t₀`, so the nearest points of `K` to `x τ` stay in the ball as well.
  obtain ⟨L, U, hU, hLip⟩ := hv t₀ ht₀
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.1 hU
  have hcont : ContinuousWithinAt x (Ici t₀) t₀ :=
    (hx t₀ (Ico_subset_Icc_self ht₀)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht₀)
  obtain ⟨c, hc, hcsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.1
    (hLip.and ((hcont.eventually (ball_mem_nhds _ (half_pos hr))).and
      (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds ht₀.2))))
  have hc' : t₀ < (t₀ + c) / 2 := by linarith [mem_Ioi.1 hc]
  have hsub : Icc t₀ ((t₀ + c) / 2) ⊆ Ico t₀ c := fun τ hτ ↦
    ⟨hτ.1, hτ.2.trans_lt (by linarith [mem_Ioi.1 hc])⟩
  have hmem {τ : ℝ} (hτ : τ ∈ Ico t₀ ((t₀ + c) / 2)) : τ ∈ Ico a b :=
    ⟨ht₀.1.trans hτ.1, (hcsub (hsub (Ico_subset_Icc_self hτ))).2.2⟩
  have hinv : MapsTo x (Icc t₀ ((t₀ + c) / 2)) K := by
    refine mapsTo_Icc_of_lipschitzOnWith hKc hK
      (hx.mono fun τ hτ ↦ ⟨ht₀.1.trans hτ.1, (hcsub (hsub hτ)).2.2.le⟩)
      (fun τ hτ ↦ hx' τ (hmem hτ)) (fun τ hτ ↦ (hcsub (hsub (Ico_subset_Icc_self hτ))).1)
      (fun τ hτ y hy ↦ hrU ?_) (fun τ hτ ↦ hvK τ (hmem hτ)) ht₀K
    have hτ' : dist (x τ) (x t₀) < r / 2 := (hcsub (hsub (Ico_subset_Icc_self hτ))).2.1
    have hd : infDist (x τ) K ≤ dist (x τ) (x t₀) := infDist_le_dist_of_mem ht₀K
    rw [mem_ball]
    linarith [dist_triangle y (x τ) (x t₀), mem_closedBall.1 hy]
  filter_upwards [Ioo_mem_nhdsGT hc'] with τ hτ using hinv (Ioo_subset_Icc_self hτ)

open TauCeti in
/-- **Invariance of a convex set under an ODE, tangent cone form.** A solution of `x' = v(t, x)`
on `[a, b]` which starts in a complete convex set `K` stays in `K`, provided `v t y` is a positive
tangent vector of `K` at every `y ∈ K` and the field is Lipschitz in space near the trajectory,
locally uniformly in later times. -/
theorem Convex.mapsTo_Icc_of_mem_posTangentConeAt {K : Set E} (hKc : Convex ℝ K)
    (hK : IsComplete K) {v : ℝ → E → E} {x : ℝ → E} {a b : ℝ} (hx : ContinuousOn x (Icc a b))
    (hx' : ∀ t ∈ Ico a b, HasDerivWithinAt x (v t (x t)) (Ici t) t)
    (hv : ∀ t ∈ Ico a b, ∃ L, ∃ U ∈ 𝓝 (x t), ∀ᶠ τ in 𝓝[≥] t, LipschitzOnWith L (v τ) U)
    (hvK : ∀ t ∈ Ico a b, ∀ y ∈ K, v t y ∈ posTangentConeAt K y)
    (ha : x a ∈ K) : MapsTo x (Icc a b) K :=
  hKc.mapsTo_Icc_of_inner_le_zero hK hx hx' hv
    (fun t ht y hy _ hn ↦ real_inner_le_zero_of_mem_posTangentConeAt hn (hvK t ht y hy)) ha

open TauCeti in
/-- **Nagumo's criterion.** For a closed convex set `K` in a real Hilbert space and an autonomous
locally Lipschitz field `v`, every solution of `x' = v(x)` which starts in `K` stays in `K` if and
only if `v y` is a positive tangent vector of `K` at every `y ∈ K`. -/
theorem Convex.forall_mem_posTangentConeAt_iff_forall_mapsTo_Icc [CompleteSpace E] {K : Set E}
    (hKc : Convex ℝ K) (hK : IsClosed K) {v : E → E} (hv : LocallyLipschitz v) :
    (∀ y ∈ K, v y ∈ posTangentConeAt K y) ↔
      ∀ (x : ℝ → E) (a b : ℝ), ContinuousOn x (Icc a b) →
        (∀ t ∈ Ico a b, HasDerivWithinAt x (v (x t)) (Ici t) t) → x a ∈ K →
          MapsTo x (Icc a b) K := by
  refine ⟨fun hvK x a b hx hx' ha ↦ hKc.mapsTo_Icc_of_mem_posTangentConeAt (v := fun _ ↦ v)
    hK.isComplete hx hx' (fun t _ ↦ ?_) (fun _ _ ↦ hvK) ha, fun hinv y hy ↦ ?_⟩
  · obtain ⟨L, U, hU, h⟩ := hv (x t)
    exact ⟨L, U, hU, .of_forall fun _ ↦ h⟩
  obtain ⟨ε, hε, hsol⟩ := hv.exists_eq_forall_mem_Icc_hasDerivWithinAt y
  obtain ⟨α, hα0, hα⟩ := hsol 0
  have hsub : Icc 0 ε ⊆ Icc (0 - ε) (0 + ε) := Icc_subset_Icc (by linarith) (by linarith)
  have hα' (t : ℝ) (ht : t ∈ Ico 0 ε) : HasDerivWithinAt α (v (α t)) (Ici t) t :=
    (hα t (hsub (Ico_subset_Icc_self ht))).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  have hK' := hinv α 0 ε (fun t ht ↦ ((hα t (hsub ht)).continuousWithinAt).mono hsub) hα'
    (hα0 ▸ hy)
  have hfreq : ∃ᶠ τ in 𝓝[>] (0 : ℝ), α τ ∈ K :=
    (eventually_of_mem (Ioo_mem_nhdsGT hε) fun τ hτ ↦ hK' (Ioo_subset_Icc_self hτ)).frequently
  simpa [hα0] using (hα' 0 ⟨le_rfl, hε⟩).mem_posTangentConeAt hfreq
