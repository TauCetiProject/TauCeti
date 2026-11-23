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
# Isolated singularities of harmonic functions

Let `E` be a finite-dimensional real inner product space of dimension `n ≥ 2`. A single point is
invisible to the maximum principle there, and so is an isolated singularity of a bounded harmonic
function.

* **The maximum principle with an exceptional point.** Let `U` be a bounded open set, `a` a point
  of `E`, `u` subharmonic and `w` superharmonic on `U \ {a}`, both continuous on
  `closure U \ {a}`. If `u - w` is bounded above on `closure U` near `a` and `u ≤ w` on
  `frontier U` away from `a`, then `u ≤ w` on `closure U \ {a}`
  (`TauCeti.SubharmonicOn.le_of_le_frontier_of_isBoundedUnder`). The point `a`
  may lie in `U` or on its frontier: no boundary condition is imposed at `a`.
* **Removable singularities.** A harmonic function on a punctured neighbourhood of `a` that is
  bounded near `a` has a limit at `a`, and extends to a harmonic function on the whole
  neighbourhood (`TauCeti.harmonicOnNhd_update_limUnder_of_isBoundedUnder`,
  `TauCeti.tendsto_limUnder_of_harmonicAt_of_isBoundedUnder`). It suffices that `u` is bounded on
  the punctured neighbourhood (`TauCeti.harmonicOnNhd_update_limUnder_of_bddAbove`), and a
  function harmonic on a punctured neighbourhood of `a` is harmonic at `a` exactly when it is
  continuous there (`TauCeti.harmonicOnNhd_sdiff_singleton_and_continuousAt_iff`).

Both fail in dimension one. On `(-1, 1) \ {0}` the function `1 - |x|` is harmonic, vanishes at
`±1` and is positive, and the function equal to `0` on `(-1, 0)` and to `1` on `(0, 1)` is
harmonic and bounded, with no limit at `0`. In potential-theoretic terms, points are polar in
dimension `n ≥ 2`; this is why an isolated point of the boundary of a domain is an irregular
point for the Dirichlet problem.

## The argument

Let `Φ` be the radial harmonic function with a pole at `a`, `‖x - a‖ ^ (2 - n)` for `n ≥ 3` and
`-log ‖x - a‖` for `n = 2`, which tends to `+∞` at `a`, and let `closure U ⊆ closedBall a R`. On
the annulus `U \ closedBall a δ`, the comparison principle between subharmonic and superharmonic
functions (`TauCeti.SubharmonicOn.le_of_le_frontier_of_subharmonicOn_neg`) puts `u` below
`w + ε (Φ - Φ_R)`, where `Φ_R` is the value of `Φ` at radius `R`, for every `ε > 0` once `δ` is
small, since `u - w` is bounded above near `a`. Letting `ε → 0` gives `u ≤ w`. For the removable
singularity, compare `u` from both sides with the Poisson integral of its values on a small sphere
about `a` (`TauCeti.exists_harmonicOnNhd_ball_continuousOn_closedBall_eqOn_sphere`).

## References

* S. Axler, P. Bourdon, W. Ramey, *Harmonic Function Theory*, 2nd ed., Springer GTM 137,
  Chapter 2 (bounded isolated singularities of harmonic functions are removable).
-/

public section

namespace TauCeti

open InnerProductSpace Metric Set Filter Topology Function

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {u w : E → ℝ} {U s : Set E} {a : E}

omit [MeasurableSpace E] [BorelSpace E] in
/-- In dimension at least two there is a radial function with a pole at `a`: `ψ ‖x - a‖` is
harmonic away from `a`, the profile `ψ` is antitone on `(0, ∞)`, and `ψ t → +∞` as `t → 0⁺`. -/
private theorem exists_harmonicOnNhd_comp_norm_sub (hE : 2 ≤ Module.finrank ℝ E) (a : E) :
    ∃ ψ : ℝ → ℝ, AntitoneOn ψ (Ioi 0) ∧ Tendsto ψ (𝓝[>] 0) atTop ∧
      HarmonicOnNhd (fun x ↦ ψ ‖x - a‖) {a}ᶜ := by
  rcases hE.eq_or_lt with hE2 | hE3
  · -- In dimension two, `-log ‖x - a‖`.
    exact ⟨fun t ↦ -Real.log t, fun s hs t _ hst ↦ neg_le_neg (Real.log_le_log hs hst),
      tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero,
      (harmonicOnNhd_log_norm_sub_of_finrank_eq_two hE2.symm a).neg⟩
  · -- In dimension `n ≥ 3`, `‖x - a‖ ^ (2 - n)`.
    have hp : (2 - Module.finrank ℝ E : ℝ) < 0 := by
      have : (3 : ℝ) ≤ Module.finrank ℝ E := by exact_mod_cast hE3
      linarith
    exact ⟨fun t ↦ t ^ (2 - Module.finrank ℝ E : ℝ),
      Real.antitoneOn_rpow_Ioi_of_exponent_nonpos hp.le, tendsto_rpow_neg_nhdsGT_zero hp,
      harmonicOnNhd_norm_sub_rpow_two_sub_finrank a⟩

/-- The comparison step on an annulus: with `ψ ‖x - a‖` the pole of
`exists_harmonicOnNhd_comp_norm_sub` and `closure U ⊆ closedBall a R`, let `u` be subharmonic
and `w` superharmonic on `U \ {a}`, with `u ≤ w` on `frontier U` away from `a` and `u - w ≤ M`
on `closure U` near `a`. Then `u ≤ w + ε (ψ ‖x - a‖ - ψ R)` for every `ε > 0`. -/
private theorem le_add_mul_sub_of_le_frontier {ψ : ℝ → ℝ} {R M δ₀ ε : ℝ}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hu : SubharmonicOn u (U \ {a}))
    (huc : ContinuousOn u (closure U \ {a})) (hw : SubharmonicOn (-w) (U \ {a}))
    (hwc : ContinuousOn w (closure U \ {a})) (hψa : AntitoneOn ψ (Ioi 0))
    (hψt : Tendsto ψ (𝓝[>] 0) atTop) (hψh : HarmonicOnNhd (fun x ↦ ψ ‖x - a‖) {a}ᶜ)
    (hR : closure U ⊆ closedBall a R) (hδ₀ : 0 < δ₀)
    (hM : ∀ y ∈ closure U, y ≠ a → dist y a < δ₀ → u y - w y ≤ M)
    (hle : ∀ y ∈ frontier U, y ≠ a → u y ≤ w y)
    (hε : 0 < ε) {x : E} (hxU : x ∈ closure U) (hxa : x ≠ a) :
    u x ≤ w x + ε * (ψ ‖x - a‖ - ψ R) := by
  have : Nontrivial E := ⟨⟨x, a, hxa⟩⟩
  -- `ψ` exceeds `ψ R + M / ε` near `0`; choose a radius `δ` below `δ₀` and `‖x - a‖` there.
  have hxa' : 0 < ‖x - a‖ := norm_pos_iff.2 (sub_ne_zero.2 hxa)
  obtain ⟨δ, hδψ, hδ⟩ := ((hψt.eventually (eventually_ge_atTop (ψ R + M / ε))).and
    (Ioo_mem_nhdsGT (lt_min hδ₀ hxa'))).exists
  have hδ0 : 0 < δ := hδ.1
  -- The profile at the radius of a point of `closure U` is at least `ψ R`.
  have hψR : ∀ y ∈ closure U, y ≠ a → ψ R ≤ ψ ‖y - a‖ := fun y hy hya ↦ by
    have hy0 : 0 < ‖y - a‖ := norm_pos_iff.2 (sub_ne_zero.2 hya)
    have hyR : ‖y - a‖ ≤ R := by simpa [dist_eq_norm] using hR hy
    exact hψa (mem_Ioi.2 hy0) (mem_Ioi.2 (hy0.trans_le hyR)) hyR
  set V := U \ closedBall a δ
  have hVa : closure V ⊆ closure U \ {a} := fun y hy ↦ by
    have hy' := closure_inter_subset_inter_closure U (closedBall a δ)ᶜ hy
    rw [closure_compl, interior_closedBall' a δ] at hy'
    exact ⟨hy'.1, fun h ↦ hy'.2 (h ▸ mem_ball_self hδ0)⟩
  set g : E → ℝ := ε • ((fun y ↦ ψ ‖y - a‖) - fun _ ↦ ψ R)
  have hg : HarmonicOnNhd g {a}ᶜ := (hψh.sub (harmonicOnNhd_const _)).const_smul
  have hgV : closure V ⊆ {a}ᶜ := fun y hy ↦ (hVa hy).2
  -- On `frontier V`, either `y ∈ frontier U` where `u ≤ w` and `0 ≤ g`, or `‖y - a‖ = δ` where
  -- `u - w ≤ M ≤ g`.
  have hfr : ∀ y ∈ frontier V, u y ≤ (w + g) y := by
    intro y hy
    simp only [g, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rcases frontier_inter_subset U (closedBall a δ)ᶜ hy with ⟨hyU, hyδ⟩ | ⟨-, hyδ⟩
    · rw [closure_compl, interior_closedBall' a δ] at hyδ
      have hya : y ≠ a := fun h ↦ hyδ (h ▸ mem_ball_self hδ0)
      have := hle y hyU hya
      have := mul_nonneg hε.le (sub_nonneg.2 (hψR y (frontier_subset_closure hyU) hya))
      linarith
    · rw [frontier_compl, frontier_closedBall' a δ] at hyδ
      obtain ⟨hyU, hya⟩ := hVa (frontier_subset_closure hy)
      have := hM y hyU hya (by rw [mem_sphere.1 hyδ]; exact hδ.2.trans_le (min_le_left _ _))
      have : M ≤ ε * (ψ δ - ψ R) := by rw [← div_le_iff₀' hε]; linarith
      rw [mem_sphere_iff_norm.1 hyδ]
      linarith
  have hxV : x ∈ closure V := by
    have hxδ : x ∈ (closedBall a δ)ᶜ := fun h ↦ by
      linarith [hδ.2.trans_le (min_le_right _ _), mem_closedBall_iff_norm.1 h]
    have := isClosed_closedBall.isOpen_compl.inter_closure ⟨hxδ, hxU⟩
    rwa [← sdiff_eq_compl_inter] at this
  -- Compare `u` with the superharmonic `w + g` on `V`.
  have hVU : V ⊆ U \ {a} :=
    sdiff_subset_sdiff_right (singleton_subset_iff.2 (mem_closedBall_self hδ0.le))
  have hVo : IsOpen V := hU.sdiff isClosed_closedBall
  have hwg : SubharmonicOn (-(w + g)) V :=
    neg_add' w g ▸ (hw.mono hVU).sub_harmonicOnNhd (hg.mono (subset_closure.trans hgV)) hVo
  have := (hu.mono hVU).le_of_le_frontier_of_subharmonicOn_neg hVo (hUb.subset sdiff_subset)
    (huc.mono hVa) hwg ((hwc.mono hVa).add (hg.continuousOn.mono hgV)) hfr x hxV
  simpa [g] using this

/-- **The maximum principle with an exceptional point.** In dimension at least two, let `U` be a
bounded open set and `a` a point, in `U`, on its frontier, or elsewhere. Let `u` be subharmonic and
`w` superharmonic (that is, `-w` is subharmonic) on `U \ {a}`, both continuous on
`closure U \ {a}`, with `u - w` bounded above on `closure U` near `a`. If `u ≤ w` at every point
of `frontier U` other than `a`, then `u ≤ w` on `closure U \ {a}`. No condition at `a` itself is
needed: in dimension at least two a single point does not affect the maximum principle. -/
theorem SubharmonicOn.le_of_le_frontier_of_isBoundedUnder (hE : 2 ≤ Module.finrank ℝ E)
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hu : SubharmonicOn u (U \ {a}))
    (huc : ContinuousOn u (closure U \ {a})) (hw : SubharmonicOn (-w) (U \ {a}))
    (hwc : ContinuousOn w (closure U \ {a}))
    (hb : IsBoundedUnder (· ≤ ·) (𝓝[closure U \ {a}] a) (u - w))
    (hle : ∀ x ∈ frontier U, x ≠ a → u x ≤ w x) : ∀ x ∈ closure U \ {a}, u x ≤ w x := by
  rintro x ⟨hxU, hxa⟩
  obtain ⟨ψ, hψa, hψt, hψh⟩ := exists_harmonicOnNhd_comp_norm_sub hE a
  obtain ⟨R, hR⟩ := (isBounded_iff_subset_closedBall a).1 hUb.closure
  obtain ⟨M, hM⟩ := hb
  obtain ⟨δ₀, hδ₀, hM⟩ := Metric.mem_nhdsWithin_iff.1 (eventually_map.1 hM)
  -- For every `ε > 0`, `u x ≤ w x + ε (ψ ‖x - a‖ - ψ R)`; let `ε → 0`.
  have hlim : Tendsto (fun ε : ℝ ↦ w x + ε * (ψ ‖x - a‖ - ψ R)) (𝓝[>] 0) (𝓝 (w x)) := by
    have hc : Continuous fun ε : ℝ ↦ w x + ε * (ψ ‖x - a‖ - ψ R) := by fun_prop
    simpa using (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun ε hε ↦
    le_add_mul_sub_of_le_frontier hU hUb hu huc hw hwc hψa hψt hψh hR hδ₀
      (fun y hyU hya hy ↦ hM ⟨mem_ball.2 hy, hyU, hya⟩) hle (mem_Ioi.1 hε) hxU hxa)

omit [MeasurableSpace E] [BorelSpace E] in
/-- A harmonic function on a punctured neighbourhood of `a`, bounded near `a`, agrees on a punctured
ball about `a` with a function harmonic on the whole ball: the Poisson integral of its values on
the boundary sphere. -/
private theorem exists_harmonicOnNhd_ball_eqOn_sdiff (hE : 2 ≤ Module.finrank ℝ E)
    (hs : s ∈ 𝓝 a) (hu : HarmonicOnNhd u (s \ {a}))
    (hb : IsBoundedUnder (· ≤ ·) (𝓝[≠] a) fun x ↦ |u x|) :
    ∃ r > 0, ∃ P, HarmonicOnNhd P (ball a r) ∧ EqOn u P (ball a r \ {a}) := by
  borelize E
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  obtain ⟨r, hr, hrs⟩ := nhds_basis_closedBall.mem_iff.1 hs
  have hcl : closedBall a r \ {a} ⊆ s \ {a} := sdiff_subset_sdiff_left hrs
  have hsph : sphere a r ⊆ closedBall a r \ {a} := fun y hy ↦
    ⟨sphere_subset_closedBall hy, ne_of_mem_sphere hy hr.ne'⟩
  -- The Poisson integral `P` of the values of `u` on `sphere a r`.
  obtain ⟨P, hP, hPc, hPu⟩ := exists_harmonicOnNhd_ball_continuousOn_closedBall_eqOn_sphere
    (hu.continuousOn.mono (hsph.trans hcl))
  have hPa : Tendsto P (𝓝[≠] a) (𝓝 (P a)) :=
    (hP a (mem_ball_self hr)).1.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  -- Compare `u` and `P` from both sides on the punctured ball.
  have hball : ball a r \ {a} ⊆ s \ {a} :=
    (sdiff_subset_sdiff_left ball_subset_closedBall).trans hcl
  have hclb : closure (ball a r) \ {a} ⊆ closedBall a r \ {a} := by rw [closure_ball a hr.ne']
  have hfr : frontier (ball a r) = sphere a r := frontier_ball a hr.ne'
  have huP : IsBoundedUnder (· ≤ ·) (𝓝[≠] a) (u - P) := by
    simpa only [sub_eq_add_neg, Pi.neg_def] using
      isBoundedUnder_le_add (isBoundedUnder_le_abs.1 hb).1
        (isBoundedUnder_le_neg.2 hPa.isBoundedUnder_ge)
  have hPu' : IsBoundedUnder (· ≤ ·) (𝓝[≠] a) (P - u) := by
    simpa only [sub_eq_add_neg, Pi.neg_def] using
      isBoundedUnder_le_add hPa.isBoundedUnder_le
        (isBoundedUnder_le_neg.2 (isBoundedUnder_le_abs.1 hb).2)
  have hle := SubharmonicOn.le_of_le_frontier_of_isBoundedUnder hE isOpen_ball isBounded_ball
    ((hu.mono hball).subharmonicOn) (hu.continuousOn.mono (hclb.trans hcl))
    ((hP.neg.mono sdiff_subset).subharmonicOn) (hPc.mono (hclb.trans sdiff_subset))
    (huP.mono (nhdsWithin_mono a fun _ hx ↦ hx.2))
    (fun x hx _ ↦ (hPu (hfr ▸ hx)).ge)
  have hge := SubharmonicOn.le_of_le_frontier_of_isBoundedUnder hE isOpen_ball isBounded_ball
    ((hP.mono sdiff_subset).subharmonicOn) (hPc.mono (hclb.trans sdiff_subset))
    ((hu.neg.mono hball).subharmonicOn) (hu.continuousOn.mono (hclb.trans hcl))
    (hPu'.mono (nhdsWithin_mono a fun _ hx ↦ hx.2))
    (fun x hx _ ↦ (hPu (hfr ▸ hx)).le)
  refine ⟨r, hr, P, hP, fun x hx ↦ ?_⟩
  have hx' : x ∈ closure (ball a r) \ {a} := ⟨subset_closure hx.1, hx.2⟩
  exact le_antisymm (hle x hx') (hge x hx')

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Removable singularity theorem for harmonic functions.** In dimension at least two, let `s`
be a neighbourhood of `a` and let `u` be harmonic on `s \ {a}` and bounded near `a`. Then `u`
redefined to be `limUnder (𝓝[≠] a) u` at `a` is harmonic on `s`. -/
theorem harmonicOnNhd_update_limUnder_of_isBoundedUnder [DecidableEq E]
    (hE : 2 ≤ Module.finrank ℝ E) (hs : s ∈ 𝓝 a) (hu : HarmonicOnNhd u (s \ {a}))
    (hb : IsBoundedUnder (· ≤ ·) (𝓝[≠] a) fun x ↦ |u x|) :
    HarmonicOnNhd (update u a (limUnder (𝓝[≠] a) u)) s := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  obtain ⟨r, hr, P, hP, heq⟩ := exists_harmonicOnNhd_ball_eqOn_sdiff hE hs hu hb
  have hPa : ContinuousAt P a := (hP a (mem_ball_self hr)).1.continuousAt
  -- So `u → P a` at `a`, and the updated function agrees with `P` near `a`.
  have hlim : limUnder (𝓝[≠] a) u = P a :=
    (hPa.tendsto.mono_left nhdsWithin_le_nhds |>.congr' (mem_nhdsWithin.2
      ⟨ball a r, isOpen_ball, mem_ball_self hr, fun x hx ↦ (heq ⟨hx.1, hx.2⟩).symm⟩)).limUnder_eq
  intro x hxs
  rcases eq_or_ne x a with rfl | hxa
  · refine (harmonicAt_congr_nhds ?_).2 (hP x (mem_ball_self hr))
    filter_upwards [ball_mem_nhds x hr] with y hy
    rcases eq_or_ne y x with rfl | hyx
    · simp [hlim]
    · rw [update_of_ne hyx]
      exact heq ⟨hy, hyx⟩
  · refine (harmonicAt_congr_nhds ?_).2 (hu x ⟨hxs, hxa⟩)
    filter_upwards [eventually_ne_nhds hxa] with y hy
    exact update_of_ne hy _ _

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Removable singularity theorem for harmonic functions.** In dimension at least two, a
function harmonic on a punctured neighbourhood of `a` and bounded near `a` has a limit at `a`. -/
theorem tendsto_limUnder_of_harmonicAt_of_isBoundedUnder (hE : 2 ≤ Module.finrank ℝ E)
    (hu : ∀ᶠ x in 𝓝[≠] a, HarmonicAt u x)
    (hb : IsBoundedUnder (· ≤ ·) (𝓝[≠] a) fun x ↦ |u x|) :
    Tendsto u (𝓝[≠] a) (𝓝 (limUnder (𝓝[≠] a) u)) := by
  classical
  rw [eventually_nhdsWithin_iff] at hu
  have H := harmonicOnNhd_update_limUnder_of_isBoundedUnder hE hu (fun x hx ↦ hx.1 hx.2) hb
  exact continuousAt_update_same.1 (H a (mem_of_mem_nhds hu)).1.continuousAt

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Removable singularity theorem for harmonic functions.** In dimension at least two, let `s`
be a neighbourhood of `a` and let `u` be harmonic and bounded on `s \ {a}`. Then `u` redefined to
be `limUnder (𝓝[≠] a) u` at `a` is harmonic on `s`. -/
theorem harmonicOnNhd_update_limUnder_of_bddAbove [DecidableEq E] (hE : 2 ≤ Module.finrank ℝ E)
    (hs : s ∈ 𝓝 a) (hu : HarmonicOnNhd u (s \ {a}))
    (hb : BddAbove ((fun x ↦ |u x|) '' (s \ {a}))) :
    HarmonicOnNhd (update u a (limUnder (𝓝[≠] a) u)) s := by
  obtain ⟨M, hM⟩ := hb
  exact harmonicOnNhd_update_limUnder_of_isBoundedUnder hE hs hu ⟨M, eventually_map.2 <|
    mem_nhdsWithin_iff_exists_mem_nhds_inter.2 ⟨s, hs, fun x hx ↦ hM ⟨x, hx, rfl⟩⟩⟩

omit [MeasurableSpace E] [BorelSpace E] in
/-- In dimension at least two, a function harmonic on a punctured neighbourhood `s \ {a}` of `a`
is harmonic on `s` exactly when it is continuous at `a`. -/
theorem harmonicOnNhd_sdiff_singleton_and_continuousAt_iff (hE : 2 ≤ Module.finrank ℝ E)
    (hs : s ∈ 𝓝 a) : HarmonicOnNhd u (s \ {a}) ∧ ContinuousAt u a ↔ HarmonicOnNhd u s := by
  classical
  refine ⟨fun ⟨hu, hc⟩ ↦ ?_, fun hu ↦
    ⟨hu.mono sdiff_subset, (hu a (mem_of_mem_nhds hs)).1.continuousAt⟩⟩
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  have htend : Tendsto u (𝓝[≠] a) (𝓝 (u a)) := hc.tendsto.mono_left nhdsWithin_le_nhds
  simpa [htend.limUnder_eq] using
    harmonicOnNhd_update_limUnder_of_isBoundedUnder hE hs hu htend.abs.isBoundedUnder_le

end TauCeti
