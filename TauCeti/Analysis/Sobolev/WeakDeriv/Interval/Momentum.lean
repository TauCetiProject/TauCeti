/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Analysis.Sobolev.WeakDeriv.Interval
public import TauCeti.MeasureTheory.Integral.IntervalIntegral.Primitive
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Weak momentum and interval regularity

An integrable weak momentum has a continuous primitive. A continuous left inverse of its
kinetic coefficient gives a continuous velocity and C¹ regularity of the same integral path.
Testing against each fixed vector gives the vector integration-by-parts identity.

## References

* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, Lemma 7.2.
* The reduced-action development in `frenzymath/lean-eval-submissions` and
  `frenzymath/PoincareConjecture`.
-/

public section
noncomputable section

open MeasureTheory Set Filter Topology
open scoped intervalIntegral ContDiff Distributions

namespace TauCeti

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Interval integration against all compactly supported smooth tests gives the native weak
line derivative on the open interval. -/
theorem hasWeakLineDerivOn_of_intervalIntegral_test {a b : ℝ} (hab : a ≤ b)
    (P Q : ℝ → E) (hP : IntervalIntegrable P volume a b)
    (hQ : IntervalIntegrable Q volume a b)
    (hweak : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b → (∫ s in a..b, deriv φ s • P s) =
        -(∫ s in a..b, φ s • Q s)) :
    HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩ P Q 1 := by
  apply hasWeakLineDerivOn_iff_testFunction.mpr
  refine ⟨inferInstance,
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le hab).mp hP).locallyIntegrableOn,
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le hab).mp hQ).locallyIntegrableOn, ?_⟩
  intro φ
  rw [← setIntegral_lineDeriv_smul_eq_integral_lineDeriv_smul φ,
    ← setIntegral_smul_eq_integral_smul φ]
  have ht := hweak φ φ.contDiff φ.hasCompactSupport φ.tsupport_subset
  rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo,
    intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo] at ht
  simpa only [lineDeriv_one, TopologicalSpace.Opens.coe_mk] using ht

/-- A continuous invertible momentum coefficient upgrades weak velocity to a continuous
representative and its primitive to C¹, including the interval endpoints. -/
theorem exists_continuous_velocity_of_weak_momentum {a b : ℝ} (hab : a < b)
    (u w : ℝ → E)
    (hprimitive : ∀ s ∈ Icc a b, u s = u a + ∫ r in a..s, w r)
    (A B : ℝ → E →L[ℝ] E)
    (hA : ContinuousOn A (Icc a b)) (hB : ContinuousOn B (Icc a b))
    (hinv : ∀ s ∈ Icc a b, ∀ v : E, B s (A s v) = v)
    (Q : ℝ → E) (hQ : IntervalIntegrable Q volume a b)
    (hP : IntervalIntegrable (fun s ↦ A s (w s)) volume a b)
    (hweak : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b → (∫ s in a..b, deriv φ s • A s (w s)) =
        -(∫ s in a..b, φ s • Q s)) :
    ∃ (c : E) (q : ℝ → E),
      (∀ s, q s = B s (c + ∫ r in a..s, Q r)) ∧
      ContinuousOn q (Icc a b) ∧
      w =ᵐ[volume.restrict (Icc a b)] q ∧
      (∀ s ∈ Icc a b, A s (q s) = c + ∫ r in a..s, Q r) ∧
      (∀ s ∈ Icc a b, u s = u a + ∫ r in a..s, q r) ∧
      (∀ s ∈ Icc a b, HasDerivWithinAt u (q s) (Icc a b) s) ∧
      ContDiffOn ℝ 1 u (Icc a b) := by
  have hweak' := hasWeakLineDerivOn_of_intervalIntegral_test hab.le
    (fun s ↦ A s (w s)) Q hP hQ hweak
  obtain ⟨c, hc⟩ := hweak'.exists_ae_eq_add_intervalIntegral_left
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).mp hQ)
  rw [Measure.restrict_congr_set Ioo_ae_eq_Icc] at hc
  let q : ℝ → E := fun s ↦ B s (c + ∫ r in a..s, Q r)
  have hH : ContinuousOn (fun s ↦ c + ∫ r in a..s, Q r) (Icc a b) := by
    have h := intervalIntegral.continuousOn_primitive_interval' hQ left_mem_uIcc
    rw [uIcc_of_le hab.le] at h
    exact continuousOn_const.add h
  have hq : ContinuousOn q (Icc a b) := hB.clm_apply hH
  have hwq : w =ᵐ[volume.restrict (Icc a b)] q := by
    filter_upwards [hc, ae_restrict_mem measurableSet_Icc] with s hs hmem
    dsimp only [q]
    rw [← hs]
    exact (hinv s hmem (w s)).symm
  have hmomentum : ∀ s ∈ Icc a b, A s (q s) = c + ∫ r in a..s, Q r := by
    apply Measure.eqOn_Icc_of_ae_eq volume hab.ne
    · filter_upwards [hc, hwq] with s hs hws
      rw [← hws]
      exact hs
    · exact hA.clm_apply hq
    · exact hH
  have hprimitiveQ (s : ℝ) (hs : s ∈ Icc a b) :
      u s = u a + ∫ r in a..s, q r := by
    rw [hprimitive s hs]
    congr 1
    exact intervalIntegral.integral_eq_of_ae_eq_Icc hwq hs
  obtain ⟨hderiv, hC1⟩ :=
    intervalIntegral.hasDerivWithinAt_and_contDiffOn_of_forall_eq_add_integral
      hab u q hq hprimitiveQ
  exact ⟨c, q, fun _ ↦ rfl, hq, hwq, hmomentum, hprimitiveQ, hderiv, hC1⟩

end Normed

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- Scalar stationarity against every constant vector implies the vector weak momentum identity. -/
theorem integral_deriv_smul_eq_neg_integral_smul_of_forall_inner {a b : ℝ}
    (P Q : ℝ → F) (hP : IntervalIntegrable P volume a b)
    (hQ : IntervalIntegrable Q volume a b) (φ : ℝ → ℝ) (hφ : ContDiff ℝ 1 φ)
    (hstationary : ∀ z : F,
      (∫ s in a..b, deriv φ s * inner ℝ z (P s) + φ s * inner ℝ z (Q s)) = 0) :
    (∫ s in a..b, deriv φ s • P s) = -(∫ s in a..b, φ s • Q s) := by
  have hDP : IntervalIntegrable (fun s ↦ deriv φ s • P s) volume a b :=
    hP.continuousOn_smul (hφ.continuous_deriv (by norm_num)).continuousOn
  have hφQ : IntervalIntegrable (fun s ↦ φ s • Q s) volume a b :=
    hQ.continuousOn_smul hφ.continuous.continuousOn
  apply ext_inner_left ℝ
  intro z
  let l : F →L[ℝ] ℝ := innerSL ℝ z
  have hDPscalar : IntervalIntegrable (fun s ↦ l (deriv φ s • P s)) volume a b :=
    ⟨l.integrable_comp hDP.1, l.integrable_comp hDP.2⟩
  have hQscalar : IntervalIntegrable (fun s ↦ l (φ s • Q s)) volume a b :=
    ⟨l.integrable_comp hφQ.1, l.integrable_comp hφQ.2⟩
  have hzero : (∫ s in a..b, l (deriv φ s • P s)) +
      (∫ s in a..b, l (φ s • Q s)) = 0 := by
    rw [← intervalIntegral.integral_add hDPscalar hQscalar]
    simpa only [l, innerSL_apply_apply, inner_smul_right] using hstationary z
  -- The chosen inner-product functional is definitionally the scalar pairing in the goal.
  change l (∫ s in a..b, deriv φ s • P s) = l (-(∫ s in a..b, φ s • Q s))
  rw [map_neg, ← l.intervalIntegral_comp_comm hDP, ← l.intervalIntegral_comp_comm hφQ]
  linarith

end TauCeti
