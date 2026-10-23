/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import TauCeti.Geometry.Manifold.IntegralCurve.Flow
public import TauCeti.Geometry.Manifold.Morse.CriticalPoints
public import TauCeti.Geometry.Manifold.Riemannian.Energy
public import TauCeti.Geometry.Manifold.Riemannian.Gradient.Basic
import TauCeti.Geometry.Manifold.IntegralCurve.Regularity
import TauCeti.Geometry.Manifold.MFDeriv.Curve
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Topology.OmegaLimit
import TauCeti.Topology.Order.MonotoneConvergence

/-!
# Convergence of negative gradient trajectories trapped in a compact set

Let `f` be a `C²` function on a boundaryless finite-dimensional manifold `M` carrying a `C¹`
Riemannian metric, and let `γ` be the maximal integral curve of the negative gradient `-grad f`
through a point `x`. Neither `M` nor the sublevels of `f` need be compact, and the metric need not
be complete. Along `γ` the function `f` decreases with derivative `-‖grad f‖²`
(`TauCeti.hasDerivAt_comp_maximalIntegralCurve_neg_mgradient`); this is the energy dissipation
identity, whose integrated form identifies the total energy `∫ ‖grad f (γ t)‖² dt` with the drop
of `f` (`TauCeti.integral_Ioi_norm_mgradient_sq_maximalIntegralCurve`).

Suppose that the forward trajectory of `x` stays in a compact set `K`. Then it exists for all
positive time, every cluster point of `γ t` as `t → ∞` is a critical point of `f`, and if `K`
contains only finitely many critical points the trajectory converges to one of them
(`TauCeti.exists_tendsto_maximalIntegralCurve_neg_mgradient`). This is the manifold counterpart,
for an arbitrary Riemannian metric, of the vector-space theorem
`TauCeti.IsIntegralCurveOn.exists_tendsto_atTop`. The ω-limit set of the trajectory is nonempty,
connected and invariant under the local flow, and `f` is constant on it, so the gradient vanishes
there.

A proper Morse function bounded below traps each forward trajectory in its initial compact
sublevel, so every forward negative gradient trajectory of such a function converges to a critical
point (`TauCeti.IsMorse.exists_tendsto_maximalIntegralCurve_neg_mgradient`). The metric is
arbitrary: it need not be adapted to the Morse charts of `f`.

## Main declarations

* `TauCeti.contMDiffOn_maximalIntegralCurve_neg_mgradient`: a negative gradient trajectory is
  `C¹` on its interval of definition.
* `TauCeti.hasDerivAt_comp_maximalIntegralCurve_neg_mgradient` and
  `TauCeti.antitoneOn_comp_maximalIntegralCurve_neg_mgradient`: energy dissipation and
  monotonicity along a negative gradient trajectory.
* `TauCeti.energy_maximalIntegralCurve_neg_mgradient`: over a bounded time interval the energy
  `½ ∫ ‖γ'‖²` of a negative gradient trajectory is half the drop of `f`.
* `TauCeti.integrableOn_Ioi_norm_mgradient_sq_maximalIntegralCurve` and
  `TauCeti.integral_Ioi_norm_mgradient_sq_maximalIntegralCurve`: the energy of a forward
  trajectory along which `f` has a limit is finite, and equals the drop of `f`.
* `TauCeti.Ici_subset_maximalIntegralCurveInterval_neg_mgradient`: a trapped forward trajectory
  exists for all positive time.
* `TauCeti.mem_criticalPoints_of_mapClusterPt_maximalIntegralCurve_neg_mgradient`: the ω-limit
  points of a trapped forward trajectory are critical.
* `TauCeti.exists_tendsto_maximalIntegralCurve_neg_mgradient`: a trapped forward trajectory
  converges to a critical point when only finitely many critical points lie in the trap.
* `TauCeti.IsMorse.exists_tendsto_maximalIntegralCurve_neg_mgradient`: every forward negative
  gradient trajectory of a proper Morse function bounded below converges to a critical point.

## References

* M. W. Hirsch, S. Smale and R. L. Devaney, *Differential Equations, Dynamical Systems, and an
  Introduction to Chaos*, second edition, Academic Press, 2004, Chapter 9 (gradient systems).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Proposition 2.1.6.
-/

public section

open Bundle Filter Function MeasureTheory Set Topology TauCeti.Manifold
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I 2 M]
  [BoundarylessManifold I M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {f : M → ℝ} {x : M} {K : Set M} {t : ℝ}

/-- The maximal integral curve of `-grad f` is `C¹` on its interval of definition. -/
theorem contMDiffOn_maximalIntegralCurve_neg_mgradient (hf : ContMDiff I 𝓘(ℝ) 2 f) :
    ContMDiffOn 𝓘(ℝ) I 1 (maximalIntegralCurve (-mgradient I f) x)
      (maximalIntegralCurveInterval (-mgradient I f) x) :=
  (contMDiffOn_two_of_isMIntegralCurveOn isOpen_maximalIntegralCurveInterval.uniqueDiffOn
    (isMIntegralCurveOn_maximalIntegralCurve (contMDiff_neg_mgradient_one hf))
    fun _ _ ↦ (contMDiff_neg_mgradient_one hf).contMDiffAt).of_le one_le_two

/-! ### Energy dissipation -/

/-- **Energy dissipation along a negative gradient trajectory.** Along the maximal integral curve
`γ` of `-grad f`, the function `f` has derivative `-‖grad f (γ t)‖²`. -/
theorem hasDerivAt_comp_maximalIntegralCurve_neg_mgradient (hf : ContMDiff I 𝓘(ℝ) 2 f)
    (ht : t ∈ maximalIntegralCurveInterval (-mgradient I f) x) :
    HasDerivAt (fun s ↦ f (maximalIntegralCurve (-mgradient I f) x s))
      (-‖mgradient I f (maximalIntegralCurve (-mgradient I f) x t)‖ ^ 2) t := by
  have hγ := ((isMIntegralCurveOn_maximalIntegralCurve
    (contMDiff_neg_mgradient_one hf)).isMIntegralCurveAt
      (isOpen_maximalIntegralCurveInterval.mem_nhds ht)).hasMFDerivAt
  have h := hasDerivAt_comp_curve ((hf.mdifferentiable (by norm_num)) _) hγ
  rwa [Pi.neg_apply, map_neg, mvfderiv_apply_mgradient, real_inner_self_eq_norm_sq] at h

/-- **Energy monotonicity.** The function `f` is antitone along the maximal integral curve of its
negative gradient. -/
theorem antitoneOn_comp_maximalIntegralCurve_neg_mgradient (hf : ContMDiff I 𝓘(ℝ) 2 f) :
    AntitoneOn (fun s ↦ f (maximalIntegralCurve (-mgradient I f) x s))
      (maximalIntegralCurveInterval (-mgradient I f) x) := by
  have hderiv := fun s (hs : s ∈ maximalIntegralCurveInterval (-mgradient I f) x) ↦
    hasDerivAt_comp_maximalIntegralCurve_neg_mgradient hf hs
  have hint : interior (maximalIntegralCurveInterval (-mgradient I f) x) =
      maximalIntegralCurveInterval (-mgradient I f) x :=
    isOpen_maximalIntegralCurveInterval.interior_eq
  refine antitoneOn_of_deriv_nonpos ordConnected_maximalIntegralCurveInterval.convex
    (fun s hs ↦ (hderiv s hs).continuousAt.continuousWithinAt) ?_ ?_ <;> rw [hint]
  · exact fun s hs ↦ (hderiv s hs).differentiableAt.differentiableWithinAt
  · intro s hs
    rw [(hderiv s hs).deriv, neg_nonpos]
    positivity

/-- The function `-f` increases along a negative gradient trajectory at rate `‖grad f‖²`. -/
private theorem hasDerivAt_neg_comp_maximalIntegralCurve_neg_mgradient
    (hf : ContMDiff I 𝓘(ℝ) 2 f) (ht : t ∈ maximalIntegralCurveInterval (-mgradient I f) x) :
    HasDerivAt (fun s ↦ -f (maximalIntegralCurve (-mgradient I f) x s))
      (‖mgradient I f (maximalIntegralCurve (-mgradient I f) x t)‖ ^ 2) t := by
  have h := (hasDerivAt_comp_maximalIntegralCurve_neg_mgradient hf ht).neg
  rw [neg_neg] at h
  exact h

/-- The velocity of the maximal integral curve of `-grad f` is `-grad f`. -/
private theorem curveVelocity_maximalIntegralCurve_neg_mgradient (hf : ContMDiff I 𝓘(ℝ) 2 f)
    (ht : t ∈ maximalIntegralCurveInterval (-mgradient I f) x) :
    curveVelocity I (maximalIntegralCurve (-mgradient I f) x) t =
      -mgradient I f (maximalIntegralCurve (-mgradient I f) x t) := by
  rw [← curveVelocityWithin_univ]
  exact curveVelocityWithin_eq_of_hasMFDerivWithinAt
    ((isMIntegralCurveOn_maximalIntegralCurve (contMDiff_neg_mgradient_one hf)).isMIntegralCurveAt
      (isOpen_maximalIntegralCurveInterval.mem_nhds ht)).hasMFDerivAt.hasMFDerivWithinAt
    uniqueDiffWithinAt_univ

/-- **The energy identity on a bounded time interval.** Between two times `a` and `b` of its
interval of definition, the energy `½ ∫ ‖γ'‖²` of the maximal integral curve `γ` of `-grad f` is
half the drop `f (γ a) - f (γ b)`. -/
theorem energy_maximalIntegralCurve_neg_mgradient (hf : ContMDiff I 𝓘(ℝ) 2 f) {a b : ℝ}
    (hab : uIcc a b ⊆ maximalIntegralCurveInterval (-mgradient I f) x) :
    energy I (maximalIntegralCurve (-mgradient I f) x) a b =
      (f (maximalIntegralCurve (-mgradient I f) x a) -
        f (maximalIntegralCurve (-mgradient I f) x b)) / 2 := by
  have : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := 1)
  set γ := maximalIntegralCurve (-mgradient I f) x
  -- the speed `‖γ'‖ = ‖grad f ∘ γ‖` is continuous, as the norm of a continuous section along `γ`
  have hcont : ContinuousOn (fun s ↦ ‖curveVelocity I γ s‖ ^ 2) (uIcc a b) := by
    refine (((continuous_norm_bundle E (fun x : M ↦ TangentSpace I x)).comp_continuousOn
      ((contMDiff_neg_mgradient_one hf).continuous.comp_continuousOn
        (isMIntegralCurveOn_maximalIntegralCurve
          (contMDiff_neg_mgradient_one hf)).continuousOn)).pow 2).congr ?_ |>.mono hab
    intro s hs
    simp [γ, curveVelocity_maximalIntegralCurve_neg_mgradient hf hs]
  rw [energy_def, intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun s ↦ -f (γ s))
    (fun s hs ↦ ?_) hcont.intervalIntegrable]
  · ring
  rw [curveVelocity_maximalIntegralCurve_neg_mgradient hf (hab hs), norm_neg]
  exact hasDerivAt_neg_comp_maximalIntegralCurve_neg_mgradient hf (hab hs)

variable (hx : Ici 0 ⊆ maximalIntegralCurveInterval (-mgradient I f) x) {c : ℝ}
  (hc : Tendsto (fun s ↦ f (maximalIntegralCurve (-mgradient I f) x s)) atTop (𝓝 c))
include hx hc

/-- **The energy of a forward trajectory is finite.** If the maximal integral curve of `-grad f`
through `x` exists for all positive time and `f` has a limit along it, then `‖grad f‖²` is
integrable along it on `(0, ∞)`. -/
theorem integrableOn_Ioi_norm_mgradient_sq_maximalIntegralCurve (hf : ContMDiff I 𝓘(ℝ) 2 f) :
    IntegrableOn (fun s ↦ ‖mgradient I f (maximalIntegralCurve (-mgradient I f) x s)‖ ^ 2)
      (Ioi 0) :=
  integrableOn_Ioi_deriv_of_nonneg' (g := fun s ↦ -f (maximalIntegralCurve (-mgradient I f) x s))
    (fun _ hs ↦ hasDerivAt_neg_comp_maximalIntegralCurve_neg_mgradient hf (hx hs))
    (fun _ _ ↦ by positivity) hc.neg

/-- **The energy identity.** If the maximal integral curve of `-grad f` through `x` exists for all
positive time and `f` tends to `c` along it, then `∫₀^∞ ‖grad f (γ t)‖² dt = f x - c`. -/
theorem integral_Ioi_norm_mgradient_sq_maximalIntegralCurve (hf : ContMDiff I 𝓘(ℝ) 2 f) :
    ∫ s in Ioi 0, ‖mgradient I f (maximalIntegralCurve (-mgradient I f) x s)‖ ^ 2 = f x - c := by
  rw [integral_Ioi_of_hasDerivAt_of_nonneg'
    (g := fun s ↦ -f (maximalIntegralCurve (-mgradient I f) x s))
    (fun _ hs ↦ hasDerivAt_neg_comp_maximalIntegralCurve_neg_mgradient hf (hx hs))
    (fun _ _ ↦ by positivity) hc.neg, maximalIntegralCurve_zero (hx self_mem_Ici)]
  ring

omit hx hc

/-! ### Trapped trajectories -/

variable (hK : IsCompact K)
  (hmem : MapsTo (maximalIntegralCurve (-mgradient I f) x)
    (maximalIntegralCurveInterval (-mgradient I f) x ∩ Ici 0) K)
include hK hmem

/-- **A trapped forward trajectory exists for all positive time.** If the forward part of the
maximal integral curve of `-grad f` through `x` stays in a compact set, it is defined on `[0, ∞)`.
-/
theorem Ici_subset_maximalIntegralCurveInterval_neg_mgradient (hf : ContMDiff I 𝓘(ℝ) 2 f) :
    Ici 0 ⊆ maximalIntegralCurveInterval (-mgradient I f) x :=
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  Ici_subset_maximalIntegralCurveInterval_of_isCompact_of_mapsTo
    (contMDiff_neg_mgradient_one hf)
    (zero_mem_maximalIntegralCurveInterval (contMDiff_neg_mgradient_one hf).contMDiffAt) hK hmem

/-- Along a trapped forward trajectory of `-grad f`, the function `f` converges to its value at
every ω-limit point. -/
private theorem tendsto_comp_maximalIntegralCurve_neg_mgradient (hf : ContMDiff I 𝓘(ℝ) 2 f)
    {z : M} (hz : MapClusterPt z atTop (maximalIntegralCurve (-mgradient I f) x)) :
    Tendsto (fun s ↦ f (maximalIntegralCurve (-mgradient I f) x s)) atTop (𝓝 (f z)) := by
  set γ := maximalIntegralCurve (-mgradient I f) x
  have hx := Ici_subset_maximalIntegralCurveInterval_neg_mgradient hK hmem hf
  -- The function `f` is antitone along the forward trajectory and bounded below on `K`.
  obtain ⟨m, hm⟩ := (hK.image hf.continuous).bddBelow
  have hg := tendsto_atTop_ciInf_of_antitoneOn_Ici
    ((antitoneOn_comp_maximalIntegralCurve_neg_mgradient hf).mono hx)
    ⟨m, by rintro _ ⟨s, hs, rfl⟩; exact hm (mem_image_of_mem f (hmem ⟨hx hs, hs⟩))⟩
  -- The limit is the value of `f` at the cluster point `z`.
  have hne : NeBot (𝓝 (f z) ⊓ 𝓝 (⨅ s : Ici (0 : ℝ), f (γ s))) :=
    NeBot.mono (hz.continuousAt_comp hf.continuous.continuousAt) (inf_le_inf_left _ hg)
  rwa [eq_of_nhds_neBot hne]

/-- **The ω-limit points of a trapped trajectory are critical.** If the forward part of the
maximal integral curve of `-grad f` through `x` stays in a compact set, every cluster point of this
curve as `t → ∞` is a critical point of `f`. -/
theorem mem_criticalPoints_of_mapClusterPt_maximalIntegralCurve_neg_mgradient
    (hf : ContMDiff I 𝓘(ℝ) 2 f) {z : M}
    (hz : MapClusterPt z atTop (maximalIntegralCurve (-mgradient I f) x)) :
    z ∈ criticalPoints I f := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hx := Ici_subset_maximalIntegralCurveInterval_neg_mgradient hK hmem hf
  have hlim := tendsto_comp_maximalIntegralCurve_neg_mgradient hK hmem hf hz
  -- The ω-limit set is invariant under the local flow and `f` is constant on it, so `f` is
  -- constant along the trajectory through `z` near time `0`.
  have hz0 := zero_mem_maximalIntegralCurveInterval (x := z)
    (contMDiff_neg_mgradient_one hf).contMDiffAt
  have hconst : (fun s ↦ f (maximalIntegralCurve (-mgradient I f) z s)) =ᶠ[𝓝 0] fun _ ↦ f z := by
    filter_upwards [isOpen_maximalIntegralCurveInterval.mem_nhds hz0] with s hs
    exact tendsto_nhds_unique (tendsto_comp_maximalIntegralCurve_neg_mgradient hK hmem hf
      (mapClusterPt_atTop_maximalIntegralCurve (contMDiff_neg_mgradient_one hf) hx hz hs)) hlim
  -- Hence the derivative `-‖grad f z‖²` of `f` along that trajectory at time `0` vanishes.
  have hderiv := hasDerivAt_comp_maximalIntegralCurve_neg_mgradient hf hz0
  rw [maximalIntegralCurve_zero hz0] at hderiv
  have h0 := hderiv.unique ((hasDerivAt_const 0 (f z)).congr_of_eventuallyEq hconst)
  rw [neg_eq_zero, sq_eq_zero_iff, norm_eq_zero, mgradient_eq_zero_iff] at h0
  exact mem_criticalPoints.mpr h0

/-- **Convergence of a trapped negative gradient trajectory.** If the forward part of the maximal
integral curve of `-grad f` through `x` stays in a compact set `K` containing only finitely many
critical points of `f`, the trajectory converges to one of these critical points. That it exists for
all positive time is `TauCeti.Ici_subset_maximalIntegralCurveInterval_neg_mgradient`. -/
theorem exists_tendsto_maximalIntegralCurve_neg_mgradient (hf : ContMDiff I 𝓘(ℝ) 2 f)
    (hfin : (criticalPoints I f ∩ K).Finite) :
    ∃ p ∈ criticalPoints I f ∩ K,
      Tendsto (maximalIntegralCurve (-mgradient I f) x) atTop (𝓝 p) := by
  set γ := maximalIntegralCurve (-mgradient I f) x
  have hx := Ici_subset_maximalIntegralCurveInterval_neg_mgradient hK hmem hf
  have hmaps : MapsTo γ (Ici 0) K := fun s hs ↦ hmem ⟨hx hs, hs⟩
  -- The ω-limit set consists of critical points in `K`, of which there are finitely many.
  refine exists_tendsto_atTop_of_setOf_mapClusterPt_subset hK
    ((isMIntegralCurveOn_maximalIntegralCurve
      (contMDiff_neg_mgradient_one hf)).continuousOn.mono hx)
    hmaps hfin fun z hz ↦
      ⟨mem_criticalPoints_of_mapClusterPt_maximalIntegralCurve_neg_mgradient hK hmem hf hz,
        hK.isClosed.mem_of_mapClusterPt hz
          (by filter_upwards [eventually_ge_atTop 0] with s hs using hmaps hs)⟩

omit hK hmem

/-- **Negative gradient trajectories of a proper Morse function converge.** If `f` is a proper
Morse function bounded below, the maximal integral curve of `-grad f` through any point converges
to a critical point of `f`, for any `C¹` Riemannian metric. -/
theorem IsMorse.exists_tendsto_maximalIntegralCurve_neg_mgradient [I.Boundaryless]
    (hf : IsMorse I f) (hp : IsProperMap f) (hbdd : BddBelow (range f)) (x : M) :
    ∃ p ∈ criticalPoints I f, Tendsto (maximalIntegralCurve (-mgradient I f) x) atTop (𝓝 p) := by
  have hf2 : ContMDiff I 𝓘(ℝ) 2 f := hf.contMDiff.of_le (by norm_cast)
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨m, hm⟩ := hbdd
  -- The forward trajectory stays in the compact band `m ≤ f ≤ f x`.
  have hmem : MapsTo (maximalIntegralCurve (-mgradient I f) x)
      (maximalIntegralCurveInterval (-mgradient I f) x ∩ Ici 0) (f ⁻¹' Icc m (f x)) := by
    rintro s ⟨hs, hs0⟩
    have h0 := zero_mem_maximalIntegralCurveInterval (x := x)
      (contMDiff_neg_mgradient_one hf2).contMDiffAt
    refine ⟨hm (mem_range_self _), ?_⟩
    have h : f (maximalIntegralCurve (-mgradient I f) x s) ≤
        f (maximalIntegralCurve (-mgradient I f) x 0) :=
      antitoneOn_comp_maximalIntegralCurve_neg_mgradient hf2 h0 hs hs0
    rwa [maximalIntegralCurve_zero h0] at h
  obtain ⟨p, hp, htend⟩ := TauCeti.exists_tendsto_maximalIntegralCurve_neg_mgradient
    (hp.isCompact_preimage isCompact_Icc) hmem hf2
    (hf.finite_criticalPoints_inter (hp.isCompact_preimage isCompact_Icc))
  exact ⟨p, hp.1, htend⟩

end TauCeti
