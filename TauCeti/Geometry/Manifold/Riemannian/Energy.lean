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
nonnegative on positively oriented ones.  Its first variation, and its value on geodesic
segments, are in `TauCeti.Geometry.Manifold.Riemannian.Geodesic.FirstVariation`.

## Main definitions and results

* `TauCeti.Manifold.energy`: the energy of a curve between two parameters.
* `TauCeti.Manifold.energy_const`, `TauCeti.Manifold.energy_self`: the energy vanishes on a
  constant curve and on a degenerate parameter interval.
* `TauCeti.Manifold.energy_symm`, `TauCeti.Manifold.energy_nonneg`: the energy is odd in the
  orientation of the parameter interval and nonnegative on positively oriented ones.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton, 1963, §12, the energy
  of a path.
* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 9, §2.
-/

public section

open Bundle
open scoped Manifold

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

end TauCeti.Manifold

end
