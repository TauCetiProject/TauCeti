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
variation is in `TauCeti.Geometry.Manifold.Riemannian.FirstVariation.Basic`, and its value on
geodesic segments is in `TauCeti.Geometry.Manifold.Riemannian.Geodesic.ConstantSpeed`.

## Main definitions and results

* `TauCeti.Manifold.energy`: the energy of a curve between two parameters.
* `TauCeti.Manifold.energy_const`, `TauCeti.Manifold.energy_self`: the energy vanishes on a
  constant curve and on a degenerate parameter interval.
* `TauCeti.Manifold.energy_symm`, `TauCeti.Manifold.energy_nonneg`: the energy is odd in the
  orientation of the parameter interval and nonnegative on positively oriented ones.
* `TauCeti.Manifold.energy_add_adjacent`: the energy is additive over adjacent parameter
  intervals.
* `TauCeti.Manifold.energy_congr`: energy depends only on the open-interval restriction.
* `TauCeti.Manifold.sum_energy_eq`: energy is additive over finite partitions.
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

/-- Curves agreeing near a parameter have the same Riemannian speed there. -/
theorem _root_.Filter.EventuallyEq.norm_curveVelocity_eq {γ δ : ℝ → M} {t : ℝ}
    (h : γ =ᶠ[𝓝 t] δ) : ‖curveVelocity I γ t‖ = ‖curveVelocity I δ t‖ := by
  -- The manifold derivative equality transports its target tangent space. Evaluate it before
  -- rewriting the base point, so the Riemannian norms use the same fibre metric.
  have hv : curveVelocity I γ t =
      tangentSpaceCast I (δ t) (γ t) (curveVelocity I δ t) := by
    rw [curveVelocity_apply, curveVelocity_apply]
    exact congrArg (fun L : TangentSpace 𝓘(ℝ, ℝ) t →L[ℝ] TangentSpace I (γ t) ↦
      L ((1 : ℝ) : TangentSpace 𝓘(ℝ, ℝ) t)) (h.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := I))
  rw [hv, h.self_of_nhds]
  rfl

/-- Energy depends only on the curve on the open parameter interval; values at its endpoints
and outside the interval do not affect the integral. -/
theorem energy_congr {γ δ : ℝ → M} {a b : ℝ} (h : EqOn γ δ (uIoo a b)) :
    energy I γ a b = energy I δ a b := by
  rw [energy_def, energy_def]
  congr 1
  apply intervalIntegral.integral_congr_uIoo
  intro t ht
  exact congrArg (· ^ 2) (Filter.EventuallyEq.norm_curveVelocity_eq (I := I)
    (Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds ht) h))

/-- Energy is additive over any finite partition on which the squared speed is integrable.
The partition need not be strict or increasing. -/
theorem sum_energy_eq (γ : ℝ → M) {n : ℕ} (τ : Fin (n + 1) → ℝ)
    (hint : ∀ i : Fin n, IntervalIntegrable (fun t ↦ ‖curveVelocity I γ t‖ ^ 2)
      MeasureTheory.volume (τ i.castSucc) (τ i.succ)) :
    ∑ i : Fin n, energy I γ (τ i.castSucc) (τ i.succ) =
      energy I γ (τ 0) (τ (Fin.last n)) := by
  suffices h : IntervalIntegrable (fun t ↦ ‖curveVelocity I γ t‖ ^ 2)
      MeasureTheory.volume (τ 0) (τ (Fin.last n)) ∧
      ∑ i : Fin n, energy I γ (τ i.castSucc) (τ i.succ) =
        energy I γ (τ 0) (τ (Fin.last n)) from h.2
  induction n with
  | zero => simp
  | succ n ih =>
    have hint' (i : Fin n) : IntervalIntegrable (fun t ↦ ‖curveVelocity I γ t‖ ^ 2)
        MeasureTheory.volume (τ i.castSucc.castSucc) (τ i.succ.castSucc) := by
      simpa only [Fin.succ_castSucc] using hint i.castSucc
    obtain ⟨hwhole, hsum⟩ := ih (fun i ↦ τ i.castSucc) hint'
    refine ⟨hwhole.trans (hint (Fin.last n)), ?_⟩
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.succ_castSucc]
    rw [hsum]
    exact energy_add_adjacent γ hwhole (hint (Fin.last n))

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
