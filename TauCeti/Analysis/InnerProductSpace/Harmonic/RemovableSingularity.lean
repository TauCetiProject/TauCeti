/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Harmonic.Subharmonic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import TauCeti.Analysis.InnerProductSpace.Harmonic.LogNorm
import TauCeti.Analysis.InnerProductSpace.NormPow
import TauCeti.Analysis.PDE.PoissonIntegral.Ball

/-!
# Removable singularities of harmonic functions

Let `E` be a finite-dimensional real inner product space of dimension `n ≥ 2`. A single point is
too small to carry boundary values for harmonic functions: a subharmonic function on a punctured
ball that is bounded above near the centre obeys the comparison principle as if the centre were
not there. If it lies below a harmonic function `h` on the outer sphere, it lies below `h` on
the whole punctured ball (`TauCeti.SubharmonicOn.le_of_le_sphere_of_isBoundedUnder`). As a
consequence, a harmonic function on a punctured neighbourhood of `c` that is bounded near `c` has
a limit at `c`, and extends to a function harmonic at `c`
(`TauCeti.harmonicOnNhd_update_limUnder_of_isBoundedUnder`,
`TauCeti.tendsto_limUnder_of_harmonicAt_of_isBoundedUnder`): **bounded isolated singularities of
harmonic functions are removable**. In particular a function harmonic on a punctured
neighbourhood of `c` is harmonic at `c` exactly when it is continuous there
(`TauCeti.harmonicOnNhd_sdiff_singleton_and_continuousAt_iff`). These are the harmonic
counterparts of Mathlib's `Complex.differentiableOn_update_limUnder_of_bddAbove` and
`Complex.differentiableOn_compl_singleton_and_continuousAt_iff` for holomorphic functions.

The dimension hypothesis is necessary. On the real line, `x ↦ |x|` is harmonic on `ℝ ∖ {0}` and
bounded near `0`, but no function harmonic near `0` agrees with it there, since harmonic functions
on an interval are affine. Likewise `u x = -|x|` lies below the constant `-1` at `±1` but not
between them, so the comparison principle fails on the punctured interval `(-1, 1) ∖ {0}`.

## The argument

Let `G` be the fundamental solution with pole at `c`, normalized to vanish on the outer sphere
`sphere c r`: `G x = log r - log ‖x - c‖` if `n = 2` and `G x = ‖x - c‖ ^ (2 - n) - r ^ (2 - n)`
if `n ≥ 3`. It is harmonic away from `c` and tends to `+∞` at `c`. For `ε > 0` the harmonic
function `h + ε G` dominates `u` on the outer sphere, and also on every small sphere about `c`,
because `u - h` is bounded above near `c` while `ε G` is large there. The comparison principle on
the annulus between the two spheres (`TauCeti.SubharmonicOn.le_of_le_sphere_union_sphere`) gives
`u ≤ h + ε G` on it. Letting the inner radius and then `ε` tend to `0` gives `u ≤ h`.

For the removable singularity, compare a bounded harmonic `u` with the Poisson integral `h` of its
values on a small sphere about `c`
(`TauCeti.exists_harmonicOnNhd_ball_continuousOn_closedBall_eqOn_sphere`).
Applied to `u` and to `-u`, the comparison principle gives `u = h` on the punctured ball, so `u`
tends to `h c` at `c` and setting `u c = h c` makes `u` harmonic at `c`.

## Main declarations

* `TauCeti.SubharmonicOn.le_of_le_sphere_of_isBoundedUnder`: the comparison principle on a
  punctured ball, for subharmonic functions bounded above near the centre.
* `TauCeti.harmonicOnNhd_update_limUnder_of_isBoundedUnder`,
  `TauCeti.harmonicOnNhd_update_limUnder_of_bddAbove`: the removable singularity theorem.
* `TauCeti.tendsto_limUnder_of_harmonicAt_of_isBoundedUnder`: a bounded harmonic function on a
  punctured neighbourhood of `c` has a limit at `c`.
* `TauCeti.harmonicOnNhd_sdiff_singleton_and_continuousAt_iff`: a function harmonic on a
  punctured neighbourhood of `c` is harmonic at `c` exactly when it is continuous at `c`.

## References

* S. Axler, P. Bourdon, W. Ramey, *Harmonic Function Theory*, 2nd ed., Graduate Texts in
  Mathematics **137**, Springer, 2001, Chapter 2 (isolated singularities of bounded harmonic
  functions).
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 2.8, for the comparison principle on bounded open sets used on the annuli.
-/

public section

namespace TauCeti

open InnerProductSpace Metric Set Filter Topology Function

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {u h : E → ℝ} {s : Set E} {c : E} {r : ℝ}

/-- The fundamental solution with pole at `c`, normalized to vanish on `sphere c r`: a function
harmonic away from `c`, zero on `sphere c r` and tending to `+∞` at `c`. -/
private lemma exists_harmonicOnNhd_eqOn_sphere_tendsto_atTop (hE : 2 ≤ Module.finrank ℝ E)
    (c : E) (r : ℝ) :
    ∃ G : E → ℝ, HarmonicOnNhd G {c}ᶜ ∧ (∀ x ∈ sphere c r, G x = 0) ∧
      Tendsto G (𝓝[≠] c) atTop := by
  have hnorm := tendsto_norm_sub_self_nhdsNE c
  rcases hE.eq_or_lt with hE2 | hE3
  · -- In the plane, `G x = log r - log ‖x - c‖`.
    refine ⟨fun x ↦ Real.log r - Real.log ‖x - c‖,
      (harmonicOnNhd_const _).sub (harmonicOnNhd_log_norm_sub_of_finrank_eq_two hE2.symm c),
      fun x hx ↦ by simp only [mem_sphere_iff_norm.1 hx, sub_self], ?_⟩
    exact (tendsto_atTop_add_const_left _ (Real.log r)
      (tendsto_neg_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp hnorm))).congr
      fun x ↦ (sub_eq_add_neg _ _).symm
  · -- In higher dimensions, `G x = ‖x - c‖ ^ (2 - n) - r ^ (2 - n)`.
    have hp : (2 - Module.finrank ℝ E : ℝ) < 0 := by
      rw [sub_neg]
      exact_mod_cast hE3
    refine ⟨fun x ↦ ‖x - c‖ ^ (2 - Module.finrank ℝ E : ℝ) - r ^ (2 - Module.finrank ℝ E : ℝ),
      fun x hx ↦ ?_, fun x hx ↦ by simp only [mem_sphere_iff_norm.1 hx, sub_self],
      tendsto_atTop_add_const_right _ _ ((tendsto_rpow_neg_nhdsGT_zero hp).comp hnorm)⟩
    exact (harmonicAt_norm_sub_rpow_two_sub_finrank hx).sub (harmonicAt_const _)

variable [MeasurableSpace E] [BorelSpace E] in
/-- **The comparison principle on a punctured ball.** In dimension at least two, let `u` be
subharmonic on the punctured ball `ball c r \ {c}`, continuous on `closedBall c r \ {c}` and bounded
above near `c`, and let `h` be harmonic on `ball c r` and continuous on `closedBall c r`. If
`u ≤ h` on `sphere c r`, then `u ≤ h` on `closedBall c r \ {c}`: the centre, where nothing is known
about `u`, does not count as a boundary point. In dimension one this fails, for `u x = -|x|` and
`h = -1` with `c = 0` and `r = 1`. -/
theorem SubharmonicOn.le_of_le_sphere_of_isBoundedUnder (hE : 2 ≤ Module.finrank ℝ E)
    (hu : SubharmonicOn u (ball c r \ {c})) (huc : ContinuousOn u (closedBall c r \ {c}))
    (hub : IsBoundedUnder (· ≤ ·) (𝓝[≠] c) u) (hh : HarmonicOnNhd h (ball c r))
    (hhc : ContinuousOn h (closedBall c r)) (hle : ∀ x ∈ sphere c r, u x ≤ h x) :
    ∀ x ∈ closedBall c r \ {c}, u x ≤ h x := by
  rintro x ⟨hxr, hxc⟩
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (two_pos.trans_le hE)
  rcases (mem_closedBall.1 hxr).eq_or_lt with hxr | hxr
  · exact hle x (mem_sphere.2 hxr)
  have hr : 0 < r := (dist_pos.2 hxc).trans hxr
  obtain ⟨G, hG, hGr, hGc⟩ := exists_harmonicOnNhd_eqOn_sphere_tendsto_atTop hE c r
  obtain ⟨M, hM⟩ := hub
  rw [eventually_map] at hM
  -- Near `c`, `u - h` is bounded above by `K`.
  set K := M - h c + 1
  have hhK : ∀ᶠ y in 𝓝[≠] c, h c - 1 < h y :=
    nhdsWithin_le_nhds ((hh.continuousOn.continuousAt (ball_mem_nhds c hr)).eventually
      (lt_mem_nhds (sub_one_lt (h c))))
  -- It suffices to show `u x ≤ h x + ε G x` for all `ε > 0`.
  refine le_of_forall_pos_le_add fun η hη ↦ ?_
  set ε := η / (|G x| + 1)
  have hε : 0 < ε := div_pos hη (by positivity)
  have hεG : ε * G x ≤ η := by
    calc ε * G x ≤ ε * (|G x| + 1) :=
          mul_le_mul_of_nonneg_left ((le_abs_self _).trans (le_add_of_nonneg_right zero_le_one))
            hε.le
      _ = η := div_mul_cancel₀ η (by positivity)
  -- Near `c`, `u ≤ h + ε G`.
  have hnear : ∀ᶠ y in 𝓝[≠] c, u y ≤ h y + ε * G y := by
    filter_upwards [hM, hhK, hGc.eventually_ge_atTop (K / ε)] with y hyM hyh hyG
    have : K ≤ ε * G y := by rwa [div_le_iff₀' hε] at hyG
    simp only [K] at this
    linarith
  obtain ⟨δ₀, hδ₀, hδ₀near⟩ := Metric.mem_nhdsWithin_iff.1 hnear
  -- Compare on the annulus `ball c r \ closedBall c δ` with `δ` below `δ₀` and `dist x c`.
  set δ := min (δ₀ / 2) (dist x c / 2)
  have hδ : 0 < δ := lt_min (half_pos hδ₀) (half_pos (dist_pos.2 hxc))
  have hδx : δ < dist x c := (min_le_right _ _).trans_lt (half_lt_self (dist_pos.2 hxc))
  have hcl : closedBall c r \ ball c δ ⊆ closedBall c r \ {c} :=
    sdiff_subset_sdiff_right (singleton_subset_iff.2 (mem_ball_self hδ))
  have hUc : ball c r \ closedBall c δ ⊆ {c}ᶜ := fun y hy hyc ↦
    hy.2 (mem_singleton_iff.1 hyc ▸ mem_closedBall_self hδ.le)
  refine hu.mono (sdiff_subset_sdiff_right (singleton_subset_iff.2 (mem_closedBall_self hδ.le)))
    |>.le_of_le_sphere_union_sphere (huc.mono hcl)
      ((hh.mono sdiff_subset).add ((hG.mono hUc).const_smul (c := ε)))
      ((hhc.mono (hcl.trans sdiff_subset)).add
        (continuousOn_const.mul (hG.continuousOn.mono fun y hy ↦ (hcl hy).2)))
      (fun y hy ↦ ?_) x ⟨mem_ball.2 hxr, by simpa using hδx⟩ |>.trans (add_le_add_right hεG _)
  -- On the boundary of the annulus, `y` lies on the outer or on the inner sphere.
  change u y ≤ h y + ε * G y
  rcases hy with hy | hy
  · rw [hGr y hy, mul_zero, add_zero]
    exact hle y hy
  · exact hδ₀near ⟨sphere_subset_ball ((min_le_left _ _).trans_lt (half_lt_self hδ₀)) hy,
      ne_of_mem_sphere hy hδ.ne'⟩

/-- **Removable singularity theorem for harmonic functions.** In dimension at least two, if `s`
is a neighbourhood of `c` and `u` is harmonic on `s \ {c}` and bounded near `c`, then `u`
redefined to be `limUnder (𝓝[≠] c) u` at `c` is harmonic on `s`. -/
theorem harmonicOnNhd_update_limUnder_of_isBoundedUnder [DecidableEq E]
    (hE : 2 ≤ Module.finrank ℝ E) (hs : s ∈ 𝓝 c) (hu : HarmonicOnNhd u (s \ {c}))
    (hb : IsBoundedUnder (· ≤ ·) (𝓝[≠] c) fun x ↦ |u x|) :
    HarmonicOnNhd (update u c (limUnder (𝓝[≠] c) u)) s := by
  borelize E
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (two_pos.trans_le hE)
  obtain ⟨r, hr, hrs⟩ := nhds_basis_closedBall.mem_iff.1 hs
  have hpunct : closedBall c r \ {c} ⊆ s \ {c} := sdiff_subset_sdiff_left hrs
  -- Let `H` be the harmonic function on `ball c r` with the boundary values of `u`.
  have huc : ContinuousOn u (closedBall c r \ {c}) := (hu.mono hpunct).continuousOn
  obtain ⟨H, hH, hHc, hHu⟩ := exists_harmonicOnNhd_ball_continuousOn_closedBall_eqOn_sphere
    (huc.mono fun x hx ↦ ⟨sphere_subset_closedBall hx, ne_of_mem_sphere hx hr.ne'⟩)
  -- Both `u` and `-u` are bounded above near `c`.
  obtain ⟨M, hM⟩ := hb
  have hbdd : ∀ᶠ x in 𝓝[≠] c, |u x| ≤ M := eventually_map.1 hM
  have hball := hu.mono (sdiff_subset_sdiff_left (ball_subset_closedBall.trans hrs))
  have hle := hball.subharmonicOn.le_of_le_sphere_of_isBoundedUnder hE huc
    ⟨M, eventually_map.2 (hbdd.mono fun _ hx ↦ (le_abs_self _).trans hx)⟩ hH hHc
    fun x hx ↦ (hHu hx).ge
  have hge := hball.neg.subharmonicOn.le_of_le_sphere_of_isBoundedUnder hE huc.neg
    ⟨M, eventually_map.2 (hbdd.mono fun _ hx ↦ (neg_le_abs _).trans hx)⟩ hH.neg hHc.neg
    fun x hx ↦ by simp [hHu hx]
  -- So `u = H` on the punctured closed ball, and `u` tends to `H c` at `c`.
  have heq : EqOn u H (closedBall c r \ {c}) := fun x hx ↦
    le_antisymm (hle x hx) (by simpa using hge x hx)
  have hlim : limUnder (𝓝[≠] c) u = H c := by
    refine Tendsto.limUnder_eq ?_
    refine ((hH.continuousOn.continuousAt (ball_mem_nhds c hr)).tendsto.mono_left
      nhdsWithin_le_nhds).congr' ?_
    filter_upwards [sdiff_mem_nhdsWithin_compl (ball_mem_nhds c hr) {c}] with x hx
    exact (heq ⟨ball_subset_closedBall hx.1, hx.2⟩).symm
  intro x hx
  rcases eq_or_ne x c with rfl | hxc
  · -- At `c` the updated function agrees with `H` near `c`.
    refine (harmonicAt_congr_nhds ?_).2 (hH x (mem_ball_self hr))
    filter_upwards [ball_mem_nhds x hr] with y hy
    rcases eq_or_ne y x with rfl | hyx
    · rw [update_self, hlim]
    · rw [update_of_ne hyx]
      exact heq ⟨ball_subset_closedBall hy, hyx⟩
  · -- Away from `c` it agrees with `u` near `x`.
    refine (harmonicAt_congr_nhds ?_).2 (hu x ⟨hx, hxc⟩)
    filter_upwards [isOpen_compl_singleton.mem_nhds hxc] with y hy
    exact update_of_ne hy _ _

/-- **Removable singularity theorem for harmonic functions.** In dimension at least two, if `s`
is a neighbourhood of `c` and `u` is harmonic and bounded on `s \ {c}`, then `u` redefined to be
`limUnder (𝓝[≠] c) u` at `c` is harmonic on `s`. -/
theorem harmonicOnNhd_update_limUnder_of_bddAbove [DecidableEq E] (hE : 2 ≤ Module.finrank ℝ E)
    (hs : s ∈ 𝓝 c) (hu : HarmonicOnNhd u (s \ {c})) (hb : BddAbove ((fun x ↦ |u x|) '' (s \ {c}))) :
    HarmonicOnNhd (update u c (limUnder (𝓝[≠] c) u)) s := by
  obtain ⟨M, hM⟩ := hb
  exact harmonicOnNhd_update_limUnder_of_isBoundedUnder hE hs hu ⟨M, eventually_map.2 <|
    mem_nhdsWithin_iff_exists_mem_nhds_inter.2 ⟨s, hs, fun x hx ↦ hM ⟨x, hx, rfl⟩⟩⟩

/-- In dimension at least two, a function harmonic on a punctured neighbourhood of `c` and bounded
near `c` has a limit at `c`. -/
theorem tendsto_limUnder_of_harmonicAt_of_isBoundedUnder (hE : 2 ≤ Module.finrank ℝ E)
    (hu : ∀ᶠ x in 𝓝[≠] c, HarmonicAt u x) (hb : IsBoundedUnder (· ≤ ·) (𝓝[≠] c) fun x ↦ |u x|) :
    Tendsto u (𝓝[≠] c) (𝓝 (limUnder (𝓝[≠] c) u)) := by
  classical
  obtain ⟨s, hs, hsu⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hu
  exact continuousAt_update_same.1
    ((harmonicOnNhd_update_limUnder_of_isBoundedUnder hE hs (fun _ hx ↦ hsu hx) hb) c
      (mem_of_mem_nhds hs)).1.continuousAt

/-- In dimension at least two, a function harmonic on a punctured neighbourhood `s \ {c}` of `c`
is harmonic on `s` exactly when it is continuous at `c`. -/
theorem harmonicOnNhd_sdiff_singleton_and_continuousAt_iff (hE : 2 ≤ Module.finrank ℝ E)
    (hs : s ∈ 𝓝 c) : HarmonicOnNhd u (s \ {c}) ∧ ContinuousAt u c ↔ HarmonicOnNhd u s := by
  classical
  refine ⟨fun ⟨hu, hc⟩ ↦ ?_, fun hu ↦
    ⟨hu.mono sdiff_subset, (hu c (mem_of_mem_nhds hs)).1.continuousAt⟩⟩
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (two_pos.trans_le hE)
  have htend : Tendsto u (𝓝[≠] c) (𝓝 (u c)) := hc.tendsto.mono_left nhdsWithin_le_nhds
  simpa [htend.limUnder_eq] using
    harmonicOnNhd_update_limUnder_of_isBoundedUnder hE hs hu htend.abs.isBoundedUnder_le

end TauCeti
