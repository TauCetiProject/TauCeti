/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Riemannian.Basic
public import TauCeti.Geometry.Manifold.MFDeriv.Curve

/-!
# The energy of a curve

The *energy* of a curve `γ` in a Riemannian manifold between the parameters `a` and `b` is
`E(γ) = ½ ∫_a^b ‖γ'(t)‖² dt`, where `γ'` is the velocity `TauCeti.Manifold.curveVelocity`.  This
file defines it and records its elementary properties: it vanishes on constant curves and on
degenerate parameter intervals, changes sign under reversal of the parameter interval, and is
nonnegative on positively oriented ones, and adds over adjacent parameter intervals.  On a
parameter set `s` containing the interval, it may equally be computed from the within-set velocity
`TauCeti.Manifold.curveVelocityWithin`, which is the form used for geodesics on closed intervals,
where the unrestricted velocity can take junk values at the endpoints.  Its first
variation is in `TauCeti.Geometry.Manifold.Riemannian.FirstVariation`, and its value on geodesic
segments is in `TauCeti.Geometry.Manifold.Riemannian.Geodesic.ConstantSpeed`.

## Main definitions and results

* `TauCeti.Manifold.energy`: the energy of a curve between two parameters.
* `TauCeti.Manifold.energy_const`, `TauCeti.Manifold.energy_self`: the energy vanishes on a
  constant curve and on a degenerate parameter interval.
* `TauCeti.Manifold.energy_symm`, `TauCeti.Manifold.energy_nonneg`: the energy is odd in the
  orientation of the parameter interval and nonnegative on positively oriented ones.
* `TauCeti.Manifold.energy_add_adjacent`: the energy is additive over adjacent parameter
  intervals.
* `TauCeti.Manifold.energy_eq_integral_curveVelocityWithin`: the energy computed from the velocity
  within any parameter set containing the interval.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton, 1963, §12, the energy
  of a path.
* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 9, §2.
-/

public section

open Bundle Set
open scoped Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

variable (I) in
/-- The **energy** of a curve `γ` between the parameters `a` and `b`: half the integral of its
squared Riemannian speed, `E(γ) = ½ ∫_a^b ‖γ'(t)‖² dt`.  It is meant for curves which are `C¹`
near `[a, b]`; for other curves the integrand may take junk values. -/
def energy (γ : ℝ → M) (a b : ℝ) : ℝ :=
  (∫ t in a..b, ‖curveVelocity I γ t‖ ^ 2) / 2

/-- The defining formula for the energy. -/
theorem energy_def (γ : ℝ → M) (a b : ℝ) :
    energy I γ a b = (∫ t in a..b, ‖curveVelocity I γ t‖ ^ 2) / 2 :=
  (rfl)

/-- A constant curve has zero energy. -/
@[simp]
theorem energy_const (x : M) (a b : ℝ) : energy I (fun _ : ℝ ↦ x) a b = 0 := by
  simp [energy_def, curveVelocity_const]

/-- The energy over a degenerate parameter interval vanishes. -/
@[simp]
theorem energy_self (γ : ℝ → M) (a : ℝ) : energy I γ a a = 0 := by
  simp [energy_def]

/-- Reversing the parameter interval changes the sign of the energy. -/
theorem energy_symm (γ : ℝ → M) (a b : ℝ) : energy I γ b a = -energy I γ a b := by
  rw [energy_def, energy_def, intervalIntegral.integral_symm, neg_div]

/-- The energy over a positively oriented parameter interval is nonnegative. -/
theorem energy_nonneg (γ : ℝ → M) {a b : ℝ} (hab : a ≤ b) : 0 ≤ energy I γ a b :=
  div_nonneg (intervalIntegral.integral_nonneg hab fun _ _ ↦ sq_nonneg _) two_pos.le

/-- The energy is additive over adjacent parameter intervals, provided the squared speed is
integrable on both. -/
theorem energy_add_adjacent (γ : ℝ → M) {a b c : ℝ}
    (hab : IntervalIntegrable (fun t ↦ ‖curveVelocity I γ t‖ ^ 2) MeasureTheory.volume a b)
    (hbc : IntervalIntegrable (fun t ↦ ‖curveVelocity I γ t‖ ^ 2) MeasureTheory.volume b c) :
    energy I γ a b + energy I γ b c = energy I γ a c := by
  rw [energy_def, energy_def, energy_def, ← add_div,
    intervalIntegral.integral_add_adjacent_intervals hab hbc]

/-- On any parameter set `s` containing the interval between `a` and `b`, the energy may be
computed from the velocity within `s`.  The two velocities agree on the open interval, so no
regularity of `γ` is needed. -/
theorem energy_eq_integral_curveVelocityWithin (γ : ℝ → M) {s : Set ℝ} {a b : ℝ}
    (hs : uIcc a b ⊆ s) :
    energy I γ a b = (∫ t in a..b, ‖curveVelocityWithin I γ s t‖ ^ 2) / 2 := by
  rw [energy_def, intervalIntegral.integral_congr_uIoo fun t ht ↦ ?_]
  have hmem : s ∈ 𝓝 t :=
    mem_interior_iff_mem_nhds.mp (interior_mono hs (by rwa [uIcc, interior_Icc]))
  simp only [curveVelocityWithin_of_mem_nhds hmem]

end TauCeti.Manifold

end
