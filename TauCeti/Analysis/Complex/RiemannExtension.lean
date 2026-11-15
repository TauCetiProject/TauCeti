/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Topology.DiscreteSubset
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Normed.Module.Connected
import TauCeti.Analysis.Complex.CauchyIntegralPolydisc

/-!
# The Riemann extension theorem

A holomorphic function which is locally bounded near the common zero set `A` of a family of
holomorphic functions on an open subset `U` of a finite-dimensional complex normed space extends
holomorphically across `A`. This is the Riemann extension theorem of several complex variables;
in dimension one, `z ↦ z⁻¹` on `{0}ᶜ` shows that the boundedness assumption is needed
(`TauCeti.not_exists_differentiable_and_eqOn_inv_compl_zero`).

No assumption on the size of `A` is needed. Near a point where some function of the family does not
vanish identically, `A` lies in a hypersurface. Near any other point, the identity theorem makes
every function of the family vanish on a ball, so the ball lies in `A` and there is nothing to
extend.

The local statement covers any set `A` contained in the zero set of one holomorphic function `h`
that does not vanish identically near the point `x₀`. Choose a direction `v` along which
`t ↦ h (x₀ + t • v)` does not vanish identically, and a circle `‖t‖ = r` on which it has no zero.
Then `h (z + t • v)` has no zero on that circle for all `z` near `x₀`, and the extension is the
Cauchy integral
`z ↦ (2πi)⁻¹ • ∮ ζ in C(0, r), ζ⁻¹ • f (z + ζ • v)`,
which is analytic in `z` because `f` is analytic near the compact set swept out by the circle.
It agrees with `f` off `A` because each slice `t ↦ f (z + t • v)` extends across the discrete
zero set of `t ↦ h (z + t • v)` by the one-variable removable singularity theorem.

## Main results

* `TauCeti.exists_differentiableOn_eqOn_sdiff_of_bddAbove`: in one variable, a function
  holomorphic off a discrete set and locally bounded near it extends holomorphically.
* `TauCeti.exists_analyticAt_and_eventuallyEq_nhdsWithin_of_bddAbove`: the local Riemann extension
  theorem across a subset of a hypersurface.
* `TauCeti.exists_analyticOnNhd_eqOn_sdiff_setOf_forall_eq_zero`: **the Riemann extension
  theorem** across the common zero set of a family of holomorphic functions.

## References

* J.-P. Demailly, *Complex Analytic and Differential Geometry*, Chapter II, (4.2).
* R. C. Gunning, H. Rossi, *Analytic Functions of Several Complex Variables*, Chapter I, §C,
  Theorem 3.
-/

public section

open Complex Filter Function Metric Real Set Topology

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- **Removable singularities across a discrete set.** Let `s ⊆ ℂ` be open and let `S` have no
accumulation point in `s`. A function complex differentiable on `s \ S` and bounded off `S` near
every point of `s` agrees on `s \ S` with a function complex differentiable on `s`. -/
theorem exists_differentiableOn_eqOn_sdiff_of_bddAbove {f : ℂ → F} {s S : Set ℂ} (hs : IsOpen s)
    (hS : Sᶜ ∈ codiscreteWithin s) (hf : DifferentiableOn ℂ f (s \ S))
    (hb : ∀ z ∈ s, ∃ t ∈ 𝓝 z, BddAbove (norm ∘ f '' (t \ S))) :
    ∃ g : ℂ → F, DifferentiableOn ℂ g s ∧ EqOn g f (s \ S) := by
  classical
  -- Near each point of `s`, all other points lie in `s \ S`.
  have hpunct (z : ℂ) (hz : z ∈ s) : ∀ᶠ y in 𝓝 z, y ≠ z → y ∈ s \ S := by
    have h := disjoint_principal_right.1 (mem_codiscreteWithin.1 hS z hz)
    have h' : ∀ᶠ y in 𝓝[≠] z, y ∈ s \ S := by
      filter_upwards [h, nhdsWithin_le_nhds (hs.mem_nhds hz)] with y hy hys
      exact ⟨hys, fun hyS ↦ hy ⟨hys, fun h ↦ h hyS⟩⟩
    exact eventually_nhdsWithin_iff.1 h'
  set g : ℂ → F := fun z ↦ if z ∈ S then limUnder (𝓝[≠] z) f else f z
  have hgf : EqOn g f (s \ S) := fun z hz ↦ by simp [g, hz.2]
  refine ⟨g, fun z hz ↦ DifferentiableAt.differentiableWithinAt ?_, hgf⟩
  by_cases hzS : z ∈ S
  · -- At a point of `S`, `g` is `f` updated by its limit there.
    obtain ⟨t, ht, htb⟩ := hb z hz
    set N := {y | y ≠ z → y ∈ s \ S} ∩ t
    have hmem : N ∈ 𝓝 z := inter_mem (hpunct z hz) ht
    have hsub : N \ {z} ⊆ s \ S := fun y hy ↦ hy.1.1 hy.2
    have hd := differentiableOn_update_limUnder_of_bddAbove hmem (hf.mono hsub)
      (htb.mono (image_mono (show N \ {z} ⊆ t \ S from fun y hy ↦ ⟨hy.1.2, (hsub hy).2⟩)))
    refine (hd.differentiableAt hmem).congr_of_eventuallyEq ?_
    filter_upwards [hpunct z hz] with y hy
    rcases eq_or_ne y z with rfl | hyz
    · simp [g, hzS]
    · simp [g, (hy hyz).2, hyz]
  · -- Off `S`, `g` is `f` near `z`.
    have hmem : s \ S ∈ 𝓝 z := by
      filter_upwards [hpunct z hz] with y hy
      rcases eq_or_ne y z with rfl | hyz
      exacts [⟨hz, hzS⟩, hy hyz]
    exact (hf.differentiableAt hmem).congr_of_eventuallyEq
      (eventually_of_mem hmem fun y hy ↦ hgf hy)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Near a point `x₀` of `U` near which `h` does not vanish identically, there are a direction `v`
and a radius `r > 0` such that, for every `z` near `x₀`, the disc `z + ball 0 (2 * r) • v` lies in
`U` and `h` has no zero on the circle `z + sphere 0 r • v`. -/
private theorem exists_line_sphere_ne_zero {h : E → ℂ} {U : Set E} {x₀ : E} (hU : IsOpen U)
    (hh : AnalyticOnNhd ℂ h U) (hx₀ : x₀ ∈ U) (hne : ∃ᶠ z in 𝓝 x₀, h z ≠ 0) :
    ∃ v : E, ∃ r > 0, ∀ᶠ z in 𝓝 x₀, (∀ t ∈ ball (0 : ℂ) (2 * r), z + t • v ∈ U) ∧
      ∀ ζ ∈ sphere (0 : ℂ) r, h (z + ζ • v) ≠ 0 := by
  -- A direction `v` along which `h` does not vanish identically, short enough that the
  -- relevant segments stay in `U`.
  obtain ⟨δ, hδ, hδU⟩ := isOpen_iff.1 hU x₀ hx₀
  have hball : ∀ᶠ z in 𝓝 x₀, z ∈ ball x₀ (δ / 2) := ball_mem_nhds x₀ (half_pos hδ)
  obtain ⟨y, hy, hhy⟩ := (hball.and_frequently hne).exists
  set v := y - x₀
  have hv : ‖v‖ < δ / 2 := by rwa [mem_ball, dist_eq_norm] at hy
  have hmem (z : E) (t : ℂ) (hzt : dist z x₀ + ‖t‖ * ‖v‖ < δ) : z + t • v ∈ U := by
    refine hδU (lt_of_le_of_lt ?_ hzt)
    calc dist (z + t • v) x₀ ≤ dist z x₀ + ‖t • v‖ := by
          rw [dist_eq_norm, dist_eq_norm, add_sub_right_comm]; exact norm_add_le _ _
      _ = dist z x₀ + ‖t‖ * ‖v‖ := by rw [norm_smul]
  -- Along the line, `t ↦ h (x₀ + t • v)` has no zero on a small punctured disc.
  have hψ : AnalyticOnNhd ℂ (fun t : ℂ ↦ h (x₀ + t • v)) (ball 0 2) := fun t ht ↦ by
    refine (hh _ (hmem x₀ t ?_)).comp_of_eq
      (analyticAt_const.add (analyticAt_id.smul analyticAt_const)) rfl
    rw [mem_ball_zero_iff] at ht
    nlinarith [dist_self x₀, norm_nonneg v]
  have hψ0 : ∀ᶠ t in 𝓝[≠] (0 : ℂ), h (x₀ + t • v) ≠ 0 := by
    have hcd := (mem_codiscreteWithin.1 (hψ.preimage_zero_mem_codiscreteWithin (x := 1)
      (by simpa [v] using hhy) (by simp) (isConnected_ball two_pos))) 0 (by simp)
    filter_upwards [disjoint_principal_right.1 hcd,
      nhdsWithin_le_nhds (ball_mem_nhds (0 : ℂ) two_pos)] with t ht ht2
    exact fun h0 ↦ ht ⟨ht2, by simpa using h0⟩
  obtain ⟨ε, hε, hεψ⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hψ0)
  set r := min ε 1 / 2 with hr_def
  have hr : 0 < r := half_pos (lt_min hε one_pos)
  have hrε : r < ε := (half_lt_self (lt_min hε one_pos)).trans_le (min_le_left _ _)
  have hr1 : 2 * r ≤ 1 := by linarith [min_le_right ε 1, hr_def]
  refine ⟨v, r, hr, ?_⟩
  -- For `z` near `x₀`, `h` has no zero on the circle `z + sphere 0 r • v`, by compactness.
  refine (hball.mono fun z hz t ht ↦ hmem z t ?_).and
    ((isCompact_sphere 0 r).eventually_forall_of_forall_eventually fun ζ hζ ↦ ?_)
  · rw [mem_ball_zero_iff] at ht
    rw [mem_ball] at hz
    nlinarith [norm_nonneg v, norm_nonneg t]
  rw [mem_sphere_zero_iff_norm] at hζ
  have hζU : x₀ + ζ • v ∈ U := hmem x₀ ζ (by nlinarith [dist_self x₀, norm_nonneg v])
  have hc : ContinuousAt (fun p : E × ℂ ↦ h (p.1 + p.2 • v)) (x₀, ζ) :=
    (hh _ hζU).continuousAt.comp_of_eq
      (by fun_prop : ContinuousAt (fun p : E × ℂ ↦ p.1 + p.2 • v) (x₀, ζ)) rfl
  exact hc.eventually_ne (hεψ (by simpa [hζ] using hrε) (by simpa [← norm_eq_zero, hζ] using
    hr.ne'))

/-- Off `A`, the Cauchy integral along the circle `z + sphere 0 r • v` reproduces `f z`: the slice
`t ↦ f (z + t • v)` extends across the discrete zero set of `t ↦ h (z + t • v)` in the disc. -/
private theorem two_pi_I_inv_smul_circleIntegral_inv_smul_eq {f : E → F} {h : E → ℂ}
    {U A : Set E} {z v : E} {r : ℝ} (hr : 0 < r) (hh : AnalyticOnNhd ℂ h U)
    (hAh : ∀ z ∈ U ∩ A, h z = 0) (hfa : AnalyticOnNhd ℂ f (U \ A))
    (hb : ∀ x ∈ U, ∃ V ∈ 𝓝 x, BddAbove (norm ∘ f '' (V \ A)))
    (hzs : ∀ t ∈ ball (0 : ℂ) (2 * r), z + t • v ∈ U)
    (hzS : ∀ ζ ∈ sphere (0 : ℂ) r, h (z + ζ • v) ≠ 0) (hzA : z ∉ A) :
    (2 * π * I)⁻¹ • ∮ ζ in C(0, r), ζ⁻¹ • f (z + ζ • v) = f z := by
  have hline (t : ℂ) : AnalyticAt ℂ (fun t : ℂ ↦ z + t • v) t :=
    analyticAt_const.add (analyticAt_id.smul analyticAt_const)
  have h2r : r < 2 * r := by linarith
  -- The points of the slice in `A` are zeros of `t ↦ h (z + t • v)`, nonzero on the circle.
  have hcd : {t : ℂ | z + t • v ∈ A}ᶜ ∈ codiscreteWithin (ball (0 : ℂ) (2 * r)) := by
    have hψz : AnalyticOnNhd ℂ (fun t : ℂ ↦ h (z + t • v)) (ball 0 (2 * r)) := fun t ht ↦
      (hh _ (hzs t ht)).comp_of_eq (hline t) rfl
    refine mem_of_superset (inter_mem (hψz.preimage_zero_mem_codiscreteWithin (x := r)
      (hzS r (by simp [hr.le])) (by simp [abs_of_pos hr, h2r]) (isConnected_ball (by linarith)))
      (self_mem_codiscreteWithin _)) fun t ht hA ↦ ht.1 (hAh _ ⟨hzs t ht.2, hA⟩)
  obtain ⟨Φ, hΦ, hΦf⟩ := exists_differentiableOn_eqOn_sdiff_of_bddAbove isOpen_ball hcd
    (fun t ht ↦ ((hfa _ ⟨hzs t ht.1, ht.2⟩).differentiableAt.comp t
      (hline t).differentiableAt).differentiableWithinAt)
    (fun t ht ↦ by
      obtain ⟨V, hV, hVb⟩ := hb _ (hzs t ht)
      exact ⟨_, (hline t).continuousAt.preimage_mem_nhds hV,
        hVb.mono (by rintro _ ⟨t', ⟨ht'V, ht'A⟩, rfl⟩; exact ⟨_, ⟨ht'V, ht'A⟩, rfl⟩)⟩)
  have hcirc : EqOn (fun ζ : ℂ ↦ ζ⁻¹ • f (z + ζ • v)) (fun ζ ↦ (ζ - 0)⁻¹ • Φ ζ)
      (sphere 0 r) := fun ζ hζ ↦ by
    have hζs : ζ ∈ ball (0 : ℂ) (2 * r) := sphere_subset_ball h2r hζ
    simp only [sub_zero]
    rw [hΦf ⟨hζs, fun hA ↦ hzS ζ hζ (hAh _ ⟨hzs ζ hζs, hA⟩)⟩, comp_apply]
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) (2 * r) \ {t | z + t • v ∈ A} :=
    ⟨mem_ball_self (by linarith), by simpa using hzA⟩
  rw [circleIntegral.integral_congr hr.le hcirc,
    (hΦ.mono (closedBall_subset_ball h2r)).circleIntegral_sub_inv_smul (mem_ball_self hr),
    inv_smul_smul₀ two_pi_I_ne_zero, hΦf h0]
  simp

/-- By the identity theorem, a point `x` of `U` either lies in the interior of the common zero
set of a family of functions analytic on `U`, or some member of the family vanishes identically
near none of the points close to `x`. -/
private theorem mem_interior_or_exists_eventually_frequently_ne_zero {ι : Type*}
    {g : ι → E → ℂ} {U : Set E} (hU : IsOpen U) (hg : ∀ i, AnalyticOnNhd ℂ (g i) U) {x : E}
    (hx : x ∈ U) :
    x ∈ interior {z | ∀ i, g i z = 0} ∨ ∃ i, ∀ᶠ y in 𝓝 x, ∃ᶠ z in 𝓝 y, g i z ≠ 0 := by
  obtain ⟨δ, hδ, hδU⟩ := isOpen_iff.1 hU x hx
  -- On the ball `ball x δ`, each `g i` vanishes as soon as it vanishes near one of its points.
  have hδ0 (i : ι) (y : E) (hy : y ∈ ball x δ) (hy0 : ∀ᶠ z in 𝓝 y, g i z = 0) :
      ∀ z ∈ ball x δ, g i z = 0 :=
    AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (fun w hw ↦ hg i w (hδU hw)) (convex_ball x δ).isPreconnected hy hy0
  by_cases hex : ∃ i, ∃ᶠ z in 𝓝 x, g i z ≠ 0
  · obtain ⟨i, hi⟩ := hex
    refine Or.inr ⟨i, ?_⟩
    filter_upwards [ball_mem_nhds x hδ] with y hy
    refine not_eventually.1 fun hy0 ↦ not_eventually.2 hi ?_
    filter_upwards [ball_mem_nhds x hδ] with z hz using hδ0 i y hy hy0 z hz
  · refine Or.inl (mem_interior_iff_mem_nhds.2 (mem_of_superset (ball_mem_nhds x hδ)
      fun z hz i ↦ hδ0 i x (mem_ball_self hδ) ?_ z hz))
    exact by_contra fun h ↦ hex ⟨i, not_eventually.1 h⟩

variable [FiniteDimensional ℂ E]

/-- **The local Riemann extension theorem across a hypersurface.** Let `U` be open in a
finite-dimensional complex normed space, `h` analytic on `U`, and `A` a set whose points in `U`
are zeros of `h`, with `U \ A` open. If `f` is complex differentiable on `U \ A` and bounded off
`A` near every point of `U`, then at every `x₀ ∈ U` near which `h` does not vanish identically,
`f` agrees off `A` with a function analytic at `x₀`. -/
theorem exists_analyticAt_and_eventuallyEq_nhdsWithin_of_bddAbove {f : E → F} {h : E → ℂ}
    {U A : Set E} {x₀ : E} (hU : IsOpen U) (hUA : IsOpen (U \ A)) (hh : AnalyticOnNhd ℂ h U)
    (hAh : ∀ z ∈ U ∩ A, h z = 0) (hf : DifferentiableOn ℂ f (U \ A))
    (hb : ∀ x ∈ U, ∃ V ∈ 𝓝 x, BddAbove (norm ∘ f '' (V \ A))) (hx₀ : x₀ ∈ U)
    (hne : ∃ᶠ z in 𝓝 x₀, h z ≠ 0) :
    ∃ G : E → F, AnalyticAt ℂ G x₀ ∧ G =ᶠ[𝓝[Aᶜ] x₀] f := by
  have hfa : AnalyticOnNhd ℂ f (U \ A) := hf.analyticOnNhd_of_finiteDimensional hUA
  obtain ⟨v, r, hr, hW⟩ := exists_line_sphere_ne_zero hU hh hx₀ hne
  refine ⟨fun z ↦ (2 * π * I)⁻¹ • ∮ ζ in C(0, r), ζ⁻¹ • f (z + ζ • v), ?_, ?_⟩
  · -- The Cauchy integral is analytic at `x₀`, since `f` is analytic along the circle.
    refine (analyticAt_circleIntegral
      (f := fun p : E × ℂ ↦ p.2⁻¹ • f (p.1 + p.2 • v)) fun ζ hζ ↦ ?_).const_smul
    rw [abs_of_pos hr] at hζ
    have hζU : x₀ + ζ • v ∈ U := hW.self_of_nhds.1 ζ (sphere_subset_ball (by linarith) hζ)
    have hζA : x₀ + ζ • v ∈ U \ A := ⟨hζU, fun hA ↦ hW.self_of_nhds.2 ζ hζ (hAh _ ⟨hζU, hA⟩)⟩
    exact (analyticAt_snd.inv (ne_of_mem_sphere hζ hr.ne')).smul
      ((hfa _ hζA).comp_of_eq (analyticAt_fst.add (analyticAt_snd.smul analyticAt_const)) rfl)
  · rw [EventuallyEq, eventually_nhdsWithin_iff]
    filter_upwards [hW] with z ⟨hzs, hzS⟩ hzA
    exact two_pi_I_inv_smul_circleIntegral_inv_smul_eq hr hh hAh hfa hb hzs hzS hzA

/-- **The Riemann extension theorem.** Let `U` be an open subset of a finite-dimensional complex
normed space and `A = {z | ∀ i, g i z = 0}` the common zero set of a family of functions analytic
on `U`. Every map into a complete complex normed space that is complex differentiable on `U \ A`
and bounded off `A` near every point of `U` agrees on `U \ A` with a function analytic on `U`.

When `A` has empty interior, `U \ A` is dense in `U` and the extension is unique on `U` by
`Set.EqOn.of_subset_closure`. -/
theorem exists_analyticOnNhd_eqOn_sdiff_setOf_forall_eq_zero {ι : Type*} {g : ι → E → ℂ}
    {U : Set E} (hU : IsOpen U) (hg : ∀ i, AnalyticOnNhd ℂ (g i) U) {f : E → F}
    (hf : DifferentiableOn ℂ f (U \ {z | ∀ i, g i z = 0}))
    (hb : ∀ x ∈ U, ∃ V ∈ 𝓝 x, BddAbove (norm ∘ f '' (V \ {z | ∀ i, g i z = 0}))) :
    ∃ G : E → F, AnalyticOnNhd ℂ G U ∧ EqOn G f (U \ {z | ∀ i, g i z = 0}) := by
  classical
  set A := {z | ∀ i, g i z = 0}
  have hUA : IsOpen (U \ A) := by
    refine isOpen_iff_mem_nhds.2 fun y ⟨hyU, hyA⟩ ↦ ?_
    obtain ⟨i, hi⟩ := not_forall.1 hyA
    filter_upwards [hU.mem_nhds hyU, (hg i y hyU).continuousAt.eventually_ne hi] with z hzU hz
    exact ⟨hzU, fun hzA ↦ hz (hzA i)⟩
  have hcl (y : E) (i : ι) (hi : ∃ᶠ z in 𝓝 y, g i z ≠ 0) : y ∈ closure Aᶜ :=
    mem_closure_iff_frequently.2 <| hi.mono fun z hz hzA ↦ hz (hzA i)
  set G : E → F := fun y ↦ if y ∈ interior A then 0 else limUnder (𝓝[Aᶜ] y) f
  refine ⟨G, fun x hx ↦ ?_, fun y ⟨hyU, hyA⟩ ↦ ?_⟩
  · obtain hxA | ⟨i, hi⟩ := mem_interior_or_exists_eventually_frequently_ne_zero hU hg hx
    · -- On the interior of `A`, `G` vanishes.
      refine (analyticAt_const (v := (0 : F))).congr ?_
      filter_upwards [isOpen_interior.mem_nhds hxA] with y hy
      simp [G, show y ∈ interior A from hy]
    -- Otherwise some `g i` does not vanish identically near `x`, and `G` agrees near `x` with
    -- the local extension.
    obtain ⟨H, hH, hHf⟩ := exists_analyticAt_and_eventuallyEq_nhdsWithin_of_bddAbove hU hUA
      (hg i) (fun z hz ↦ hz.2 i) hf hb hx hi.self_of_nhds
    rw [EventuallyEq, eventually_nhdsWithin_iff] at hHf
    refine hH.congr ?_
    filter_upwards [hi, hH.eventually_analyticAt, hHf.eventually_nhds] with y hy hHy hHfy
    have := mem_closure_iff_nhdsWithin_neBot.1 (hcl y i hy)
    have hyA : y ∉ interior A := by simpa [closure_compl] using hcl y i hy
    have hlim : Tendsto f (𝓝[Aᶜ] y) (𝓝 (H y)) :=
      (hHy.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
        (eventually_nhdsWithin_iff.2 hHfy)
    simp [G, hyA, hlim.limUnder_eq]
  · -- Off `A`, `G` is the limit of the continuous function `f`.
    have hyA' : y ∉ interior A := fun h ↦ hyA (interior_subset h)
    have := mem_closure_iff_nhdsWithin_neBot.1 (subset_closure (show y ∈ Aᶜ from hyA))
    have hlim : Tendsto f (𝓝[Aᶜ] y) (𝓝 (f y)) :=
      ((hf.differentiableAt (hUA.mem_nhds ⟨hyU, hyA⟩)).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds)
    simp [G, hyA', hlim.limUnder_eq]

end TauCeti
