/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.MaximumPrinciple.Weak

/-!
# Weak maximum principles with small drift

For a divergence-form operator with a first-order drift, the weak maximum principle follows
from an energy test when the drift is small relative to ellipticity and the diameter of the
domain. On a domain contained in a ball of radius `R`, the sufficient condition here is
`β²(2R)² < λ²`, where `λ` is the ellipticity floor and `β` bounds the drift.

The boundary conditions use positive-part membership in `W^{1,2}_0`, so they do not require
a trace operator or regularity of the boundary. The potential is bounded and nonnegative.
The same estimate gives maximum, constant-bound, and comparison principles.

The argument is the standard energy method for weak subsolutions; see L. C. Evans,
*Partial Differential Equations*, Chapter 6, Section 4.
-/

public section

noncomputable section

namespace TauCeti.PDE

open MeasureTheory Set TopologicalSpace

variable {n : ℕ} {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
  {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
  {b : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
  {c : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {lam Lam beta gamma : ℝ}

/-- A weak subsolution of `-div(a ∇u) + b · ∇u + cu` with nonpositive boundary data is
nonpositive almost everywhere when the drift bound satisfies `β²(2R)² < λ²`. -/
theorem UniformlyEllipticOn.value_nonpos_of_small_drift_of_subset_ball
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) a lam Lam)
    (ha : AEStronglyMeasurable a (volume.restrict Omega))
    (hb : AEStronglyMeasurable b (volume.restrict Omega))
    (hc : AEStronglyMeasurable c (volume.restrict Omega))
    (hb_bound : ∀ x ∈ Omega, ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ Omega, ‖c x‖ ≤ gamma)
    (hc_nonneg : ∀ x ∈ Omega, 0 ≤ c x)
    {z : EuclideanSpace ℝ (Fin (n + 1))} {R : ℝ}
    (hOmega : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ Metric.ball z R)
    (hsmall : beta ^ 2 * (2 * R) ^ 2 < lam ^ 2)
    {u : W1p volume Omega 2}
    (hboundary : W1p.posPart (by norm_num) u ∈ w1p0Submodule volume Omega 2)
    (hu : ∀ v : W1p0 volume Omega 2,
      (∀ᵐ x ∂volume.restrict Omega, 0 ≤ W1p.value (v : W1p volume Omega 2) x) →
        energyFormH1 a b c u (v : W1p volume Omega 2) ≤ 0) :
    ∀ᵐ x ∂volume.restrict Omega, W1p.value u x ≤ 0 := by
  have hC : 0 < (lam ^ 2 - beta ^ 2 * (2 * R) ^ 2) /
      (2 * lam * ((2 * R) ^ 2 + 1)) :=
    div_pos (sub_pos.mpr hsmall)
      (mul_pos (mul_pos (by norm_num) h.pos) (by positivity))
  refine value_nonpos_of_energyFormH1_nonpos hboundary hC ?_ hu
  intro w
  exact h.mul_norm_sq_le_energyFormH1_self_of_subset_ball ha hb hc hb_bound hc_bound
    hc_nonneg hOmega w.property

/-- A weak subsolution whose boundary values are at most `k ≥ 0` stays at most `k` almost
everywhere when the first-order drift satisfies the smallness condition. -/
theorem UniformlyEllipticOn.value_le_const_of_small_drift_of_subset_ball
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) a lam Lam)
    (ha : AEStronglyMeasurable a (volume.restrict Omega))
    (hb : AEStronglyMeasurable b (volume.restrict Omega))
    (hc : AEStronglyMeasurable c (volume.restrict Omega))
    (hb_bound : ∀ x ∈ Omega, ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ Omega, ‖c x‖ ≤ gamma)
    (hc_nonneg : ∀ x ∈ Omega, 0 ≤ c x)
    {z : EuclideanSpace ℝ (Fin (n + 1))} {R : ℝ}
    (hOmega : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ Metric.ball z R)
    (hsmall : beta ^ 2 * (2 * R) ^ 2 < lam ^ 2)
    {k : ℝ} (hk : 0 ≤ k) {u : W1p volume Omega 2}
    (hboundary : W1p.posPartAbove (by norm_num) hk u ∈ w1p0Submodule volume Omega 2)
    (hu : ∀ v : W1p0 volume Omega 2,
      (∀ᵐ x ∂volume.restrict Omega, 0 ≤ W1p.value (v : W1p volume Omega 2) x) →
        energyFormH1 a b c u (v : W1p volume Omega 2) ≤ 0) :
    ∀ᵐ x ∂volume.restrict Omega, W1p.value u x ≤ k := by
  have hcoeff := memLp_energyIntegrand_of_bounds h.upper_nonneg ha hb hc
    (fun x hx eta xi ↦ h.upper_bound hx eta xi) hb_bound hc_bound
  have hC : 0 < (lam ^ 2 - beta ^ 2 * (2 * R) ^ 2) /
      (2 * lam * ((2 * R) ^ 2 + 1)) :=
    div_pos (sub_pos.mpr hsmall)
      (mul_pos (mul_pos (by norm_num) h.pos) (by positivity))
  refine value_le_of_energyFormH1_nonpos hcoeff
    ((ae_restrict_mem Omega.isOpen.measurableSet).mono fun x hx ↦ hc_nonneg x hx)
    hk hboundary hC ?_ hu
  intro w
  exact h.mul_norm_sq_le_energyFormH1_self_of_subset_ball ha hb hc hb_bound hc_bound
    hc_nonneg hOmega w.property

/-- Ordered weak operator values and `(u - v)⁺ ∈ W^{1,2}_0(Ω)` imply `u ≤ v` almost
everywhere when the first-order drift satisfies the smallness condition. -/
theorem UniformlyEllipticOn.value_le_of_small_drift_of_subset_ball
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) a lam Lam)
    (ha : AEStronglyMeasurable a (volume.restrict Omega))
    (hb : AEStronglyMeasurable b (volume.restrict Omega))
    (hc : AEStronglyMeasurable c (volume.restrict Omega))
    (hb_bound : ∀ x ∈ Omega, ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ Omega, ‖c x‖ ≤ gamma)
    (hc_nonneg : ∀ x ∈ Omega, 0 ≤ c x)
    {z : EuclideanSpace ℝ (Fin (n + 1))} {R : ℝ}
    (hOmega : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ Metric.ball z R)
    (hsmall : beta ^ 2 * (2 * R) ^ 2 < lam ^ 2)
    {u v : W1p volume Omega 2}
    (hboundary : W1p.posPart (by norm_num) (u - v) ∈ w1p0Submodule volume Omega 2)
    (huv : ∀ w : W1p0 volume Omega 2,
      (∀ᵐ x ∂volume.restrict Omega, 0 ≤ W1p.value (w : W1p volume Omega 2) x) →
        energyFormH1 a b c u (w : W1p volume Omega 2) ≤
          energyFormH1 a b c v (w : W1p volume Omega 2)) :
    ∀ᵐ x ∂volume.restrict Omega, W1p.value u x ≤ W1p.value v x := by
  have hcoeff := memLp_energyIntegrand_of_bounds h.upper_nonneg ha hb hc
    (fun x hx eta xi ↦ h.upper_bound hx eta xi) hb_bound hc_bound
  have hC : 0 < (lam ^ 2 - beta ^ 2 * (2 * R) ^ 2) /
      (2 * lam * ((2 * R) ^ 2 + 1)) :=
    div_pos (sub_pos.mpr hsmall)
      (mul_pos (mul_pos (by norm_num) h.pos) (by positivity))
  refine value_le_of_energyFormH1_le hcoeff hboundary hC ?_ huv
  intro w
  exact h.mul_norm_sq_le_energyFormH1_self_of_subset_ball ha hb hc hb_bound hc_bound
    hc_nonneg hOmega w.property

end TauCeti.PDE
