/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.GradientFlow.Slope
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Relaxed descending slopes

The descending slope need not be lower semicontinuous. In the limit of a minimizing movement,
the appropriate lower bound for the slopes of the approximating points is its relaxation along
convergent sequences with uniformly bounded distance and energy.

`TauCeti.relaxedSlope l φ x` uses the convergence filter `l x`, which may be weaker than the
metric neighbourhood filter. Its competitors are sequences converging to `x` in this sense,
with a common finite upper bound for their distances from `x` and their energies. In particular,
on an extended metric space all competitors stay in the finite-distance component of `x`.
Energy convergence is not required. As for the descending slope, the interpretation as a slope
is on the effective domain of the energy; the definition is total.

`TauCeti.relaxedSlope_le_liminf` allows the bounds to hold only eventually. Its integral form,
`TauCeti.lintegral_relaxedSlope_rpow_le_liminf`, passes the slope part of an energy-dissipation
estimate to the limit by Fatou's lemma. It requires measurability of the approximating slopes,
without assuming measurability of the relaxed slope itself.

If the original slope is already lower semicontinuous, relaxation in the metric topology does
not change it. Local minima and constant energies have relaxed slope zero whenever the constant
sequence is an admissible competitor.

## References

* L. Ambrosio, N. Gigli, G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd ed., Birkhäuser 2008, Section 2.3 and Theorem 2.3.3.
-/

public section

noncomputable section

open Filter MeasureTheory Set Topology
open scoped ENNReal

namespace TauCeti

variable {X : Type*} [EMetricSpace X] {l l' : X → Filter X} {φ : X → EReal} {x : X}

/-- The relaxed descending slope, using sequences converging along `l x` with uniformly bounded
distance from `x` and uniformly bounded energy. Both bounds are finite, even on an extended
metric space. This is the bounded-energy relaxation, without an energy-convergence condition. -/
def relaxedSlope (l : X → Filter X) (φ : X → EReal) (x : X) : ℝ≥0∞ :=
  ⨅ u : ℕ → X, ⨅ (_ : Tendsto u atTop (l x)), ⨅ C : ℝ,
    ⨅ (_ : ∀ n, edist x (u n) ≤ ENNReal.ofReal C ∧ φ (u n) ≤ (C : EReal)),
      liminf (fun n ↦ descendingSlope φ (u n)) atTop

/-- The infimum formula characterizing the relaxed descending slope. -/
theorem relaxedSlope_def (l : X → Filter X) (φ : X → EReal) (x : X) :
    relaxedSlope l φ x =
      ⨅ u : ℕ → X, ⨅ (_ : Tendsto u atTop (l x)), ⨅ C : ℝ,
        ⨅ (_ : ∀ n, edist x (u n) ≤ ENNReal.ofReal C ∧ φ (u n) ≤ (C : EReal)),
          liminf (fun n ↦ descendingSlope φ (u n)) atTop :=
  (rfl)

/-- A number bounds the relaxed slope from below exactly when it bounds the lower limit of the
slopes of every admissible sequence. -/
theorem le_relaxedSlope_iff {a : ℝ≥0∞} :
    a ≤ relaxedSlope l φ x ↔ ∀ (u : ℕ → X), Tendsto u atTop (l x) → ∀ C : ℝ,
      (∀ n, edist x (u n) ≤ ENNReal.ofReal C ∧ φ (u n) ≤ (C : EReal)) →
        a ≤ liminf (fun n ↦ descendingSlope φ (u n)) atTop := by
  simp only [relaxedSlope_def, le_iInf_iff]

/-- Weakening the convergence filter can only decrease the relaxed slope. -/
theorem relaxedSlope_mono_filter (hl : l x ≤ l' x) :
    relaxedSlope l' φ x ≤ relaxedSlope l φ x := by
  rw [le_relaxedSlope_iff]
  intro u hu C hC
  rw [relaxedSlope_def]
  exact iInf_le_of_le u (iInf_le_of_le (hu.mono_right hl)
    (iInf_le_of_le C (iInf_le_of_le hC le_rfl)))

/-- The relaxed slope is bounded above by the lower limit of descending slopes along any
convergent sequence with eventually uniformly bounded distance and energy. Initial terms outside
the effective domain or the finite-distance component do not affect the bound. -/
theorem relaxedSlope_le_liminf {u : ℕ → X} (hu : Tendsto u atTop (l x)) {C : ℝ}
    (hC : ∀ᶠ n in atTop, edist x (u n) ≤ ENNReal.ofReal C ∧ φ (u n) ≤ (C : EReal)) :
    relaxedSlope l φ x ≤ liminf (fun n ↦ descendingSlope φ (u n)) atTop := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hC
  have hshift : Tendsto (fun n ↦ u (n + N)) atTop (l x) :=
    hu.comp (tendsto_add_atTop_nat N)
  have hbound : ∀ n, edist x (u (n + N)) ≤ ENNReal.ofReal C ∧
      φ (u (n + N)) ≤ (C : EReal) := fun n ↦ hN _ (Nat.le_add_left N n)
  calc
    relaxedSlope l φ x ≤ liminf (fun n ↦ descendingSlope φ (u (n + N))) atTop := by
      rw [relaxedSlope_def]
      exact iInf_le_of_le _ (iInf_le_of_le hshift
        (iInf_le_of_le C (iInf_le_of_le hbound le_rfl)))
    _ = _ := liminf_nat_add (fun n ↦ descendingSlope φ (u n)) N

/-- At a point with energy below `⊤`, relaxation can only decrease the slope, provided that
the constant sequence converges to the point in the chosen convergence filter. -/
theorem relaxedSlope_le_descendingSlope (hl : pure x ≤ l x) (hφ : φ x ≠ ⊤) :
    relaxedSlope l φ x ≤ descendingSlope φ x := by
  obtain ⟨C, hC, _⟩ := EReal.exists_between_coe_real (lt_top_iff_ne_top.2 hφ)
  have h := relaxedSlope_le_liminf (φ := φ)
    ((tendsto_const_pure : Tendsto (fun _ : ℕ ↦ x) atTop (pure x)).mono_right hl)
    (C := C) (Eventually.of_forall fun _ ↦ ⟨by simp, hC.le⟩)
  simpa using h

/-- A lower semicontinuous descending slope agrees with its metric-topology relaxation on
the effective domain. -/
theorem relaxedSlope_nhds_eq_of_lowerSemicontinuousAt (hφ : φ x ≠ ⊤)
    (hs : LowerSemicontinuousAt (descendingSlope φ) x) :
    relaxedSlope (𝓝 ·) φ x = descendingSlope φ x := by
  refine le_antisymm (relaxedSlope_le_descendingSlope (pure_le_nhds x) hφ) ?_
  rw [le_relaxedSlope_iff]
  intro u hu C hC
  exact hs.le_liminf.trans hu.liminf_le_liminf_comp

/-- A local minimum with energy below `⊤` has relaxed slope zero when the constant sequence
converges in the chosen filter. -/
theorem _root_.IsLocalMin.relaxedSlope_eq_zero (h : IsLocalMin φ x)
    (hl : pure x ≤ l x) (hφ : φ x ≠ ⊤) : relaxedSlope l φ x = 0 := by
  apply nonpos_iff_eq_zero.1
  exact (relaxedSlope_le_descendingSlope hl hφ).trans_eq h.descendingSlope_eq_zero

/-- Constant energies below `⊤` have relaxed slope zero whenever constant sequences converge. -/
@[simp]
theorem relaxedSlope_const (l : X → Filter X) (c : EReal) (x : X)
    (hl : pure x ≤ l x) (hc : c ≠ ⊤) : relaxedSlope l (fun _ ↦ c) x = 0 :=
  isLocalMin_const.relaxedSlope_eq_zero hl hc

/-- **Fatou's inequality for relaxed slopes.** Almost-everywhere convergence of a sequence of
maps, with eventually bounded distance and energy at almost every argument, bounds the integral
of the relaxed slope by the lower limit of the descending-slope integrals. The nonnegative
exponent is arbitrary. The left integrand need not be measurable. -/
theorem lintegral_relaxedSlope_rpow_le_liminf {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {u : Ω → X} {us : ℕ → Ω → X} {q : ℝ} (hq : 0 ≤ q)
    (hu : ∀ᵐ t ∂μ, Tendsto (fun n ↦ us n t) atTop (l (u t)))
    (hbound : ∀ᵐ t ∂μ, ∃ C : ℝ, ∀ᶠ n in atTop,
      edist (u t) (us n t) ≤ ENNReal.ofReal C ∧ φ (us n t) ≤ (C : EReal))
    (hmeas : ∀ n, AEMeasurable (fun t ↦ descendingSlope φ (us n t)) μ) :
    (∫⁻ t, relaxedSlope l φ (u t) ^ q ∂μ) ≤
      liminf (fun n ↦ ∫⁻ t, descendingSlope φ (us n t) ^ q ∂μ) atTop := by
  refine (lintegral_mono_ae ?_).trans (lintegral_liminf_le' fun n ↦ (hmeas n).pow_const q)
  filter_upwards [hu, hbound] with t ht hC
  obtain ⟨C, hC⟩ := hC
  exact (ENNReal.rpow_le_rpow (relaxedSlope_le_liminf ht hC) hq).trans_eq
    ((ENNReal.monotone_rpow_of_nonneg hq).map_liminf_of_continuousAt
      (fun n ↦ descendingSlope φ (us n t)) ENNReal.continuous_rpow_const.continuousAt)

end TauCeti
