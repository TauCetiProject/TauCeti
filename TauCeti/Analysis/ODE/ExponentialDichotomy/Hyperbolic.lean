/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import TauCeti.Analysis.Normed.Algebra.Exponential
import TauCeti.Analysis.Normed.Module.Complexification
import TauCeti.Analysis.Normed.Operator.Exponential
import TauCeti.Analysis.Polynomial.HalfPlaneSplitting

/-!
# Exponential dichotomy of a hyperbolic linear flow

Let `A` be a bounded operator on a finite-dimensional real normed space `E`. The linear flow
`exp (t • A)` is *hyperbolic* when no eigenvalue of `A` lies on the imaginary axis, that is, when
the characteristic polynomial of `A` has no root `z : ℂ` with `re z = 0`. This file shows that the
flow of a hyperbolic operator has an exponential dichotomy: there are an idempotent `P` commuting
with `A`, and constants `K, α > 0`, with

* `‖exp (t • A) (P v)‖ ≤ K * Real.exp (-α * t) * ‖v‖` for `t ≥ 0`, and
* `‖exp (t • A) (v - P v)‖ ≤ K * Real.exp (α * t) * ‖v‖` for `t ≤ 0`.

These are exactly the bounds taken as input by the Lyapunov–Perron construction of local stable
and unstable manifolds at a hyperbolic equilibrium (`TauCeti.Analysis.ODE.LyapunovPerron.Basic`),
whose linearization need not be symmetric. For a symmetric `A` the same bounds come from the
spectral theorem (`TauCeti.Analysis.ODE.ExponentialDichotomy`); no symmetry, inner product, or
real diagonalizability is assumed here.

The proof has two steps.

* **Decay.** If `A` is annihilated by a real polynomial whose complex roots all have negative real
  part, then `exp (t • A)` decays exponentially
  (`ContinuousLinearMap.exists_norm_exp_smul_le_of_aeval_eq_zero`). The complexification of `A` is
  annihilated by the same polynomial, so its spectrum lies in the open left half-plane, and by the
  spectral mapping theorem `ContinuousLinearMap.spectrum_exp` the spectrum of its exponential lies
  in the open unit disc. Gelfand's formula then bounds the Gelfand radius of `exp A` below one;
  complexification is isometric, so this transfers to the real operator, and
  `TauCeti.exists_norm_exp_smul_le_of_gelfandRadius_exp_lt_one` turns it into exponential decay.
* **Splitting.** An annihilating polynomial `q` with no root on the imaginary axis factors as
  `q = f * g` with `f` and `g` coprime, the roots of `f` in the left half-plane and those of `g` in
  the right half-plane (`Polynomial.exists_eq_mul_isCoprime_re_neg_re_nonneg`). From a Bézout
  identity `a * f + b * g = 1`, the operator `P = (b * g)(A)` is an idempotent commuting with `A`,
  and `f(A) P = 0`, `g(A) (1 - P) = 0`. The decay step, applied to `A` on the range of `P` and to
  `-A` on the range of `1 - P`, gives the two bounds.

## Main results

* `ContinuousLinearMap.exists_norm_exp_smul_le_of_aeval_eq_zero`: exponential decay of
  `exp (t • A)` when `A` is annihilated by a polynomial with roots in the open left half-plane.
* `ContinuousLinearMap.exists_projection_exponential_bounds_of_aeval_eq_zero`: the exponential
  dichotomy when `A` is annihilated by a polynomial with no root on the imaginary axis.
* `ContinuousLinearMap.exists_projection_exponential_bounds`: the exponential dichotomy of a
  hyperbolic operator, whose characteristic polynomial has no root on the imaginary axis.

## References

* W. A. Coppel, *Dichotomies in Stability Theory*, Lecture Notes in Mathematics 629, Springer,
  1978, Chapter 1 (exponential dichotomies of linear systems with constant coefficients).
* M. W. Hirsch, S. Smale, R. L. Devaney, *Differential Equations, Dynamical Systems, and an
  Introduction to Chaos*, Academic Press, 2004, Chapter 7 (stable and unstable subspaces of a
  hyperbolic linear system).
-/

public section

open Polynomial NormedSpace
open scoped NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Exponential decay of a stable linear flow.** If a bounded operator `A` on a
finite-dimensional real normed space is annihilated by a real polynomial `q` all of whose complex
roots have negative real part, then `‖exp (t • A)‖ ≤ K * Real.exp (-α * t)` for all `t ≥ 0`, for
some `K > 0` and `α > 0`. -/
theorem _root_.ContinuousLinearMap.exists_norm_exp_smul_le_of_aeval_eq_zero (A : E →L[ℝ] E)
    {q : ℝ[X]} (hq : aeval A q = 0) (hq_re : ∀ z : ℂ, aeval z q = 0 → z.re < 0) :
    ∃ K α : ℝ, 0 < K ∧ 0 < α ∧ ∀ t : ℝ, 0 ≤ t → ‖exp (t • A)‖ ≤ K * Real.exp (-α * t) := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  rcases subsingleton_or_nontrivial E with hE | hE
  · refine ⟨1, 1, one_pos, one_pos, fun t _ ↦ ?_⟩
    rw [Subsingleton.elim (exp (t • A)) 0, norm_zero]
    positivity
  refine exists_norm_exp_smul_le_of_gelfandRadius_exp_lt_one (a := A) ?_
  have : Nontrivial (Complexification E) := (Complexification.ofRealLI E).injective.nontrivial
  let +nondep : NormedAlgebra ℚ (E →L[ℝ] E) := .restrictScalars ℚ ℝ _
  let +nondep : NormedAlgebra ℚ (Complexification E →L[ℂ] Complexification E) :=
    .restrictScalars ℚ ℂ _
  set φ := ContinuousLinearMap.complexifyAlgHom E
  have hφ (T : E →L[ℝ] E) : φ T = T.complexify := ContinuousLinearMap.complexifyAlgHom_apply T
  have hexp : φ (exp A) = exp (φ A) := map_exp φ
    ((ContinuousLinearMap.complexifyₗᵢ E E).continuous.congr fun T ↦ by
      rw [ContinuousLinearMap.complexifyₗᵢ_apply, hφ]) A
  -- Complexification is isometric, so `exp A` and `exp (φ A)` have the same Gelfand radius.
  rw [gelfandRadius_eq_of_norm_pow_eq (b := exp (φ A)) fun n ↦ by
    rw [← hexp, ← map_pow, hφ, ContinuousLinearMap.norm_complexify]]
  -- The spectrum of `φ A` consists of roots of `q`, by the spectral mapping theorem for `q`.
  have hspec (z : ℂ) (hz : z ∈ spectrum ℂ (φ A)) : z.re < 0 := by
    have hq' : aeval (φ A) (q.map (algebraMap ℝ ℂ)) = 0 := by
      rw [aeval_map_algebraMap, aeval_algHom_apply, hq, map_zero]
    have hmap := spectrum.map_polynomial_aeval (φ A) (q.map (algebraMap ℝ ℂ))
    rw [hq', spectrum.zero_eq] at hmap
    have hmem : eval z (q.map (algebraMap ℝ ℂ)) ∈ ({0} : Set ℂ) := hmap ▸ ⟨z, hz, rfl⟩
    exact hq_re z (by simpa [eval_map_algebraMap] using hmem)
  -- Hence the spectrum of `exp (φ A)` lies in the open unit disc.
  have hlt : spectralRadius ℂ (exp (φ A)) < 1 := by
    refine spectrum.spectralRadius_lt_of_forall_lt _ fun μ hμ ↦ ?_
    obtain ⟨z, hz, rfl⟩ := (ContinuousLinearMap.spectrum_exp (φ A) ▸ hμ : μ ∈ exp '' _)
    rw [← NNReal.coe_lt_coe, coe_nnnorm, ← Complex.exp_eq_exp_ℂ, Complex.norm_exp,
      NNReal.coe_one, Real.exp_lt_one_iff]
    exact hspec z hz
  rw [spectrum.spectralRadius_eq_gelfandRadius] at hlt
  exact ENNReal.ofReal_lt_one.1 hlt

/-- Exponential decay of the flow of `A` on the range of an idempotent `Q` commuting with `A`, when
`f(A) Q = 0` for a polynomial `f` with roots in the open left half-plane. -/
private theorem exists_norm_exp_smul_apply_le_of_aeval_mul_eq_zero (A Q : E →L[ℝ] E)
    (hQ : IsIdempotentElem Q) (hAQ : Commute A Q) {f : ℝ[X]} (hf : aeval A f * Q = 0)
    (hf_re : ∀ z : ℂ, aeval z f = 0 → z.re < 0) :
    ∃ K α : ℝ, 0 < K ∧ 0 < α ∧
      ∀ t : ℝ, 0 ≤ t → ∀ v : E, ‖exp (t • A) (Q v)‖ ≤ K * Real.exp (-α * t) * ‖v‖ := by
  -- `B` agrees with `A` on the range of `Q`, is `-1` on its kernel, and is annihilated by
  -- `f * (X + 1)`.
  set B : E →L[ℝ] E := A * Q - (1 - Q)
  have hBQ : B * Q = A * Q := by
    simp only [B, sub_mul, one_mul, hQ.eq, sub_self, sub_zero, mul_assoc]
  have hcomm : Commute B Q :=
    (hAQ.mul_left (Commute.refl Q)).sub_left ((Commute.one_left Q).sub_left (Commute.refl Q))
  have hsemi : SemiconjBy Q B A := by rw [SemiconjBy, ← hcomm.eq, hBQ]
  have haeval (g : ℝ[X]) : aeval B g * Q = aeval A g * Q := by
    have hpow (n : ℕ) : B ^ n * Q = A ^ n * Q :=
      (hcomm.pow_left n).eq.trans (hsemi.pow_right n).eq
    simp only [aeval_eq_sum_range, Finset.sum_mul, smul_mul_assoc, hpow]
  have hB1 : B + 1 = (A + 1) * Q := by
    simp only [B]
    noncomm_ring
  have hBann : aeval B (f * (X + 1)) = 0 := by
    rw [map_mul, map_add, aeval_X, map_one, hB1, (hAQ.add_left (Commute.one_left Q)).eq,
      ← mul_assoc, haeval, hf, zero_mul]
  have hroots (z : ℂ) (hz : aeval z (f * (X + 1)) = 0) : z.re < 0 := by
    rw [map_mul, mul_eq_zero] at hz
    rcases hz with hz | hz
    · exact hf_re z hz
    · simp only [map_add, aeval_X, map_one] at hz
      simp [eq_neg_of_add_eq_zero_left hz]
  obtain ⟨K, α, hK, hα, hdecay⟩ := B.exists_norm_exp_smul_le_of_aeval_eq_zero hBann hroots
  refine ⟨K * (‖Q‖ + 1), α, by positivity, hα, fun t ht v ↦ ?_⟩
  -- `B` and `A` agree on the range of `Q`, and so do their flows.
  have hexpQ : exp (t • A) * Q = exp (t • B) * Q := by
    have : CompleteSpace E := FiniteDimensional.complete ℝ E
    let +nondep : NormedAlgebra ℚ (E →L[ℝ] E) := .restrictScalars ℚ ℝ _
    exact (hsemi.smul_right t).exp_right.eq.symm.trans (hcomm.smul_left t).exp_left.eq.symm
  calc ‖exp (t • A) (Q v)‖ = ‖(exp (t • B) * Q) v‖ := by rw [← hexpQ]; rfl
    _ ≤ ‖exp (t • B)‖ * ‖Q‖ * ‖v‖ :=
        ((exp (t • B) * Q).le_opNorm v).trans (by gcongr; exact norm_mul_le _ _)
    _ ≤ K * Real.exp (-α * t) * (‖Q‖ + 1) * ‖v‖ := by
        gcongr
        · exact hdecay t ht
        · linarith
    _ = K * (‖Q‖ + 1) * Real.exp (-α * t) * ‖v‖ := by ring

/-- **The exponential dichotomy of a hyperbolic linear flow**, for an operator `A` annihilated by a
real polynomial `q` with no complex root on the imaginary axis. There are an idempotent `P`
commuting with `A` and constants `K, α > 0` such that the flow `exp (t • A)` contracts the range of
`P` in forward time and the range of `1 - P` in backward time, both at rate `α`. -/
theorem _root_.ContinuousLinearMap.exists_projection_exponential_bounds_of_aeval_eq_zero
    (A : E →L[ℝ] E) {q : ℝ[X]} (hq : aeval A q = 0) (hq_re : ∀ z : ℂ, aeval z q = 0 → z.re ≠ 0) :
    ∃ P : E →L[ℝ] E, IsIdempotentElem P ∧ Commute A P ∧ ∃ K α : ℝ≥0, 0 < K ∧ 0 < α ∧
      (∀ t : ℝ, 0 ≤ t → ∀ v : E, ‖exp (t • A) (P v)‖ ≤ K * Real.exp (-α * t) * ‖v‖) ∧
      (∀ t : ℝ, t ≤ 0 → ∀ v : E, ‖exp (t • A) (v - P v)‖ ≤ K * Real.exp (α * t) * ‖v‖) := by
  have hq0 : q ≠ 0 := by
    rintro rfl
    exact hq_re 0 (map_zero _) Complex.zero_re
  -- Split `q = f * g` along the imaginary axis; with `a * f + b * g = 1`, take `P = (b * g)(A)`.
  obtain ⟨f, g, rfl, ⟨a, b, hab⟩, hf, hg⟩ := exists_eq_mul_isCoprime_re_neg_re_nonneg hq0
  set P := aeval A (b * g)
  have hP1 : 1 - P = aeval A (a * f) := by
    rw [sub_eq_iff_eq_add, ← map_add, hab, map_one]
  have hfP : aeval A f * P = 0 := by
    rw [← map_mul, show f * (b * g) = b * (f * g) by ring, map_mul, hq, mul_zero]
  have hgP : aeval A g * (1 - P) = 0 := by
    rw [hP1, ← map_mul, show g * (a * f) = a * (f * g) by ring, map_mul, hq, mul_zero]
  have hPidem : IsIdempotentElem P := by
    have h : P * (1 - P) = 0 := by
      rw [hP1, ← map_mul, show b * g * (a * f) = a * b * (f * g) by ring, map_mul, hq,
        mul_zero]
    rw [mul_sub, mul_one, sub_eq_zero] at h
    exact h.symm
  have hAP : Commute A P := by
    simpa only [aeval_X] using (Commute.all X (b * g)).map (aeval A)
  -- The stable half: `A` on the range of `P`, annihilated there by `f`.
  obtain ⟨K₁, α₁, hK₁, hα₁, h₁⟩ :=
    exists_norm_exp_smul_apply_le_of_aeval_mul_eq_zero A P hPidem hAP hfP hf
  -- The unstable half: `-A` on the range of `1 - P`, annihilated there by `g (-X)`.
  have hg' : aeval (-A) (g.comp (-X)) * (1 - P) = 0 := by
    rw [aeval_comp, map_neg, aeval_X, neg_neg, hgP]
  have hg're (z : ℂ) (hz : aeval z (g.comp (-X)) = 0) : z.re < 0 := by
    rw [aeval_comp, map_neg, aeval_X] at hz
    have h1 := hg (-z) hz
    have h2 := hq_re (-z) (by rw [map_mul, hz, mul_zero])
    rw [Complex.neg_re] at h1 h2
    exact lt_of_le_of_ne (neg_nonneg.1 h1) fun h ↦ h2 (by rw [h, neg_zero])
  obtain ⟨K₂, α₂, hK₂, hα₂, h₂⟩ :=
    exists_norm_exp_smul_apply_le_of_aeval_mul_eq_zero (-A) (1 - P) hPidem.one_sub
      ((Commute.one_right A).sub_right hAP).neg_left hg' hg're
  refine ⟨P, hPidem, hAP, (⟨max K₁ K₂, by positivity⟩ : ℝ≥0),
    (⟨min α₁ α₂, by positivity⟩ : ℝ≥0), NNReal.coe_pos.1 (lt_max_of_lt_left hK₁),
    NNReal.coe_pos.1 (lt_min hα₁ hα₂), fun t ht v ↦ ?_, fun t ht v ↦ ?_⟩
  · refine (h₁ t ht v).trans (mul_le_mul_of_nonneg_right (mul_le_mul (le_max_left K₁ K₂)
      (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (neg_le_neg (min_le_left α₁ α₂)) ht))
      (Real.exp_nonneg _) (le_max_of_le_left hK₁.le)) (norm_nonneg v))
  · have h := h₂ (-t) (neg_nonneg.2 ht) v
    rw [smul_neg, neg_smul, neg_neg, sub_apply, one_apply_eq_self] at h
    refine h.trans (mul_le_mul_of_nonneg_right (mul_le_mul (le_max_right K₁ K₂)
      (Real.exp_le_exp.2 ?_) (Real.exp_nonneg _) (le_max_of_le_left hK₁.le)) (norm_nonneg v))
    rw [neg_mul_neg]
    exact mul_le_mul_of_nonpos_right (min_le_right α₁ α₂) ht

/-- **The exponential dichotomy of a hyperbolic linear flow.** If no eigenvalue of the bounded
operator `A` on a finite-dimensional real normed space lies on the imaginary axis, that is, if its
characteristic polynomial has no complex root `z` with `re z = 0`, then there are an idempotent `P`
commuting with `A` and constants `K, α > 0` with
`‖exp (t • A) (P v)‖ ≤ K * Real.exp (-α * t) * ‖v‖` for `t ≥ 0` and
`‖exp (t • A) (v - P v)‖ ≤ K * Real.exp (α * t) * ‖v‖` for `t ≤ 0`. -/
theorem _root_.ContinuousLinearMap.exists_projection_exponential_bounds (A : E →L[ℝ] E)
    (hA : ∀ z : ℂ, aeval z (A : E →ₗ[ℝ] E).charpoly = 0 → z.re ≠ 0) :
    ∃ P : E →L[ℝ] E, IsIdempotentElem P ∧ Commute A P ∧ ∃ K α : ℝ≥0, 0 < K ∧ 0 < α ∧
      (∀ t : ℝ, 0 ≤ t → ∀ v : E, ‖exp (t • A) (P v)‖ ≤ K * Real.exp (-α * t) * ‖v‖) ∧
      (∀ t : ℝ, t ≤ 0 → ∀ v : E, ‖exp (t • A) (v - P v)‖ ≤ K * Real.exp (α * t) * ‖v‖) := by
  let φ : (E →L[ℝ] E) →ₐ[ℝ] Module.End ℝ E :=
    { ContinuousLinearMap.toLinearMapRingHom with commutes' := fun _ ↦ rfl }
  refine A.exists_projection_exponential_bounds_of_aeval_eq_zero
    (ContinuousLinearMap.coe_injective ?_) hA
  rw [ContinuousLinearMap.toLinearMap_zero]
  exact (aeval_algHom_apply φ A _).symm.trans (A : E →ₗ[ℝ] E).aeval_self_charpoly

end TauCeti
