/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Length
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Energy of a Riemannian curve

The energy of a parametrized curve is half the integral of its squared Riemannian speed. It is
the functional whose first variation detects geodesics with fixed endpoints. We use the same
manifold derivative as `Manifold.pathELength`, so both functionals measure speed with the
Riemannian norm on the tangent bundle.

Energy is additive over adjacent intervals, and on any parameter set containing the interval it
is the integral of half the squared norm of the within-set velocity `curveVelocityWithin`, since
the two velocities agree off the endpoints. The energy of a geodesic on a preconnected parameter
set, open or not, is its constant squared speed times half the duration.

## References

* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 9, §2.
-/

public section

open Bundle Manifold MeasureTheory Set
open scoped Bundle ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [EMetricSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

variable (I)

/-- The Riemannian energy of a curve from time `a` to time `b`. For a `C¹` curve this is
`(1/2) ∫ t in a..b, ‖γ'(t)‖²`. As with `pathELength`, the manifold derivative outside the
regularity domain has its usual junk value. The integral is directed: reversing the limits
negates the energy. -/
def riemannianEnergy (γ : ℝ → M) (a b : ℝ) : ℝ :=
  ∫ t in a..b, (‖mfderiv 𝓘(ℝ, ℝ) I γ t 1‖ ^ 2) / 2

/-- The energy of a constant curve vanishes. -/
@[simp]
theorem riemannianEnergy_const (x : M) (a b : ℝ) :
    riemannianEnergy I (fun _ : ℝ ↦ x) a b = 0 := by
  simp [riemannianEnergy, mfderiv_const]

/-- The energy on an interval of zero duration vanishes. -/
@[simp]
theorem riemannianEnergy_self (γ : ℝ → M) (a : ℝ) :
    riemannianEnergy I γ a a = 0 := by
  simp [riemannianEnergy]

/-- Reversing the time limits negates the directed energy. -/
theorem riemannianEnergy_symm (γ : ℝ → M) (a b : ℝ) :
    riemannianEnergy I γ b a = -riemannianEnergy I γ a b := by
  unfold riemannianEnergy
  exact intervalIntegral.integral_symm a b

/-- Energy is nonnegative when the terminal time is no earlier than the initial time. -/
theorem riemannianEnergy_nonneg (γ : ℝ → M) {a b : ℝ} (hab : a ≤ b) :
    0 ≤ riemannianEnergy I γ a b := by
  unfold riemannianEnergy
  exact intervalIntegral.integral_nonneg_of_forall hab fun t ↦
    div_nonneg (sq_nonneg _) (by norm_num)

/-- Energy is additive over adjacent intervals on which the squared speed is integrable. -/
theorem riemannianEnergy_add (γ : ℝ → M) {a b c : ℝ}
    (hab : IntervalIntegrable (fun t ↦ ‖mfderiv 𝓘(ℝ, ℝ) I γ t 1‖ ^ 2) volume a b)
    (hbc : IntervalIntegrable (fun t ↦ ‖mfderiv 𝓘(ℝ, ℝ) I γ t 1‖ ^ 2) volume b c) :
    riemannianEnergy I γ a b + riemannianEnergy I γ b c = riemannianEnergy I γ a c :=
  intervalIntegral.integral_add_adjacent_intervals (hab.div_const 2) (hbc.div_const 2)

/-- On any parameter set `s` containing the interval between `a` and `b`, the energy is half the
integral of the squared norm of the velocity within `s`. The two velocities agree on the open
interval, so no regularity of `γ` is needed. -/
theorem riemannianEnergy_eq_integral_curveVelocityWithin (γ : ℝ → M) {s : Set ℝ} {a b : ℝ}
    (hs : uIcc a b ⊆ s) :
    riemannianEnergy I γ a b = ∫ t in a..b, ‖curveVelocityWithin I γ s t‖ ^ 2 / 2 := by
  unfold riemannianEnergy
  refine intervalIntegral.integral_congr_uIoo fun t ht ↦ ?_
  have hmem : s ∈ 𝓝 t :=
    mem_interior_iff_mem_nhds.mp (interior_mono hs (by rwa [uIcc, interior_Icc]))
  have hvel : mfderiv 𝓘(ℝ, ℝ) I γ t 1 = curveVelocityWithin I γ s t :=
    ((curveVelocityWithin_of_mem_nhds hmem).trans (curveVelocity_apply (I := I))).symm
  simp only [hvel]

variable {I}

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- On an interval with endpoints in its preconnected domain, the energy of a geodesic is half
the square of its speed at any chosen time in that domain, multiplied by the duration. The domain
need not be open, so this applies to geodesic segments on closed intervals. -/
theorem IsGeodesicCurveOn.riemannianEnergy_eq {γ : ℝ → M} {s : Set ℝ}
    (hγ : IsGeodesicCurveOn I γ s) (hconn : IsPreconnected s)
    {a b c : ℝ} (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) :
    riemannianEnergy I γ a b =
      (b - a) * (‖curveVelocityWithin I γ s c‖ ^ 2 / 2) := by
  have hsub := hconn.ordConnected.uIcc_subset ha hb
  rw [riemannianEnergy_eq_integral_curveVelocityWithin I γ hsub,
    intervalIntegral.integral_congr (g := fun _ ↦ ‖curveVelocityWithin I γ s c‖ ^ 2 / 2)
      fun t ht ↦ by simp only [hγ.norm_curveVelocityWithin_eq hconn (hsub ht) hc]]
  simp only [intervalIntegral.integral_const, smul_eq_mul]

variable [I.Boundaryless] [T2Space (TangentBundle I M)]

/-- On any subinterval of its maximal domain, a geodesic has energy equal to half its
initial squared speed times the duration. -/
theorem riemannianEnergy_maximalGeodesic {p : M} {v : TangentSpace I p}
    {a b : ℝ} (ha : a ∈ geodesicInterval I M p v)
    (hb : b ∈ geodesicInterval I M p v) :
    riemannianEnergy I (maximalGeodesic I M p v) a b =
      (b - a) * (‖v‖ ^ 2 / 2) := by
  rw [(isGeodesicCurveOnFrom_maximalGeodesic (I := I) (M := M) p v).isGeodesicCurveOn
    |>.riemannianEnergy_eq isPreconnected_geodesicInterval ha hb zero_mem_geodesicInterval,
    norm_curveVelocityWithin_maximalGeodesic zero_mem_geodesicInterval]

end TauCeti.Manifold

end
