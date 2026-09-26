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

The energy of a maximal geodesic on a subinterval of its domain is its constant squared speed
times half the duration. This calculation provides the normalization needed for variation
formulas and the flat-space model.

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

variable {I}

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- On an interval contained in its open preconnected domain, the energy of a geodesic is half
the square of its speed at any chosen time in that domain, multiplied by the duration. -/
theorem IsGeodesicCurveOn.riemannianEnergy_eq {γ : ℝ → M} {s : Set ℝ}
    (hγ : IsGeodesicCurveOn I γ s) (hsopen : IsOpen s) (hconn : IsPreconnected s)
    {a b c : ℝ} (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) (hab : a ≤ b) :
    riemannianEnergy I γ a b =
      (b - a) * (‖curveVelocityWithin I γ s c‖ ^ 2 / 2) := by
  unfold riemannianEnergy
  rw [intervalIntegral.integral_congr_Ioo_of_le hab
    (g := fun _ ↦ ‖curveVelocityWithin I γ s c‖ ^ 2 / 2)]
  · simp only [intervalIntegral.integral_const, smul_eq_mul]
  · intro t ht
    have hmem : t ∈ s := Ioo_subset_Icc_self.trans (hconn.ordConnected.out ha hb) ht
    have hvel : mfderiv 𝓘(ℝ, ℝ) I γ t 1 = curveVelocityWithin I γ s t :=
      ((curveVelocityWithin_of_mem_nhds (hsopen.mem_nhds hmem)).trans
        (curveVelocity_apply (I := I))).symm
    simp only [hvel, hγ.norm_curveVelocityWithin_eq hconn hmem hc]

variable [I.Boundaryless] [T2Space (TangentBundle I M)]

/-- On any subinterval of its maximal domain, a geodesic has energy equal to half its
initial squared speed times the duration. -/
theorem riemannianEnergy_maximalGeodesic {p : M} {v : TangentSpace I p}
    {a b : ℝ} (ha : a ∈ geodesicInterval I M p v)
    (hb : b ∈ geodesicInterval I M p v) (hab : a ≤ b) :
    riemannianEnergy I (maximalGeodesic I M p v) a b =
      (b - a) * (‖v‖ ^ 2 / 2) := by
  rw [(isGeodesicCurveOnFrom_maximalGeodesic (I := I) (M := M) p v).isGeodesicCurveOn
    |>.riemannianEnergy_eq isOpen_geodesicInterval isPreconnected_geodesicInterval
      ha hb zero_mem_geodesicInterval hab,
    norm_curveVelocityWithin_maximalGeodesic zero_mem_geodesicInterval]

end TauCeti.Manifold

end
