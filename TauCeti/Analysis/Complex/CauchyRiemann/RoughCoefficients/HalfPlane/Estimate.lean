/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.Estimate
public import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.HalfPlane.Reflection
import TauCeti.Data.ENNReal.Holder
import TauCeti.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Estimates up to the real axis for rough Cauchy–Riemann equations

Let `Ω ⊆ ℂ` be an open set invariant under complex conjugation, write `z = s + i t`, let `V` be a
finite-dimensional real inner product space with an isometric involution `R` whose fixed vectors
lie in the boundary subspace `Λ`, and let `ξ` be a weak solution up to the real axis of
`∂_s ξ + J ∂_t ξ + S ξ = η` on `Ω ∩ {0 ≤ t}`, in the sense of `TauCeti.IsWeakCRSolutionHalf`.
This file proves the order-zero estimate up to the boundary (McDuff–Salamon, Lemma B.4.6 with a
totally real boundary condition): for every `U` with compact closure in `Ω`,

`‖ξ‖_{W^{1,r}(U ∩ {0 ≤ t})} ≤ C (‖η‖_{Lʳ(Ω ∩ {0 ≤ t})} + ‖ξ‖_{L^q(Ω ∩ {0 ≤ t})})`,

with `C` depending only on the exponents, `U`, `Ω`, `V` and a bound `M` for the norms of the
reflected coefficients `TauCeti.crReflectionCoeff R J` in `W^{1,p}(Ω)` and
`TauCeti.crReflectionZeroth R S` in `Lᵖ(Ω)`, which are assumed to be Sobolev coefficients on `Ω`.

The proof reflects: the twisted reflection of `ξ` solves the reflected equation on `Ω`
(`TauCeti.IsWeakCRSolutionHalf.isWeakCRSolution_crReflection`), so the interior estimates
`TauCeti.exists_eLpNormWkp_one_le_of_isWeakCRSolution` and
`TauCeti.exists_eLpNormWkp_one_le_of_isWeakCRSolution_of_le` apply on `Ω`. The left side
restricts to `U ∩ {0 ≤ t}`, where the reflection is `ξ` off the null axis, and the twisted
reflection by the isometry `R` at most doubles `Lᵖ` norms
(`TauCeti.eLpNorm_twistedReflection_le`), so the right side is at most twice the half-plane norms.

## Main results

* `TauCeti.exists_eLpNormWkp_one_le_of_isWeakCRSolutionHalf`: the order-zero estimate up to the
  real axis for `1/p + 1/q ≤ 1/r`.
* `TauCeti.exists_eLpNormWkp_one_le_of_isWeakCRSolutionHalf_of_le`: the `W^{1,r}` estimate up to
  the real axis for every `1 < r ≤ p` from a solution in `L^q_loc`, `1/p + 1/q < 1`.

Both constants are uniform over coefficients whose reflections are bounded by `M`.

* `TauCeti.exists_eLpNormWkp_one_le_of_isWeakCRSolutionHalf_of_hasWeakFDerivOn` and
  `TauCeti.exists_eLpNormWkp_one_le_of_isWeakCRSolutionHalf_of_le_of_hasWeakFDerivOn`: the same
  estimates with hypotheses on the half-plane coefficients in place of the hypothesis that the
  reflected coefficients are Sobolev coefficients: `J` continuous up to the axis with weak
  derivative `DJ`, anticommuting with `R` on the axis (the totally real boundary condition), and
  `DJ`, `S` locally `Lᵖ` up to the axis (`TauCeti.isSobolevCRCoefficients_crReflection`), and with
  the uniformity bound `M` on the norms of `J` in `W^{1,p}(Ω ∩ {0 ≤ t})` and of `S` in
  `Lᵖ(Ω ∩ {0 ≤ t})`.
* `TauCeti.eLpNormWkp_crReflectionCoeff_le`: under the totally real boundary condition, the
  reflection of `J` has at most twice the `W^{1,p}` norm of `J` up to the axis, and
  `TauCeti.isSobolevCRCoefficients_crReflection_of_le` combines it with
  `TauCeti.isSobolevCRCoefficients_crReflection`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.4, Lemma B.4.6.
-/

public section

open MeasureTheory TopologicalSpace Complex Set
open scoped ENNReal NNReal

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  {Ω : Opens ℂ} {Λ : Submodule ℝ V} {p q r : ℝ≥0∞} {R : V ≃ₗᵢ[ℝ] V} {U : Set ℂ}

omit [CompleteSpace V] in
/-- **The `W^{1,p}` bound for the reflected leading coefficient.** Let `Ω` be invariant under
conjugation, `1 ≤ p`, and `R` an isometry. Let `J` be continuous on `Ω ∩ {0 ≤ t}` with weak
derivative `DJ` on the open upper part, locally integrable up to the axis, and let `J(s)`
anticommute with `R` for `s ∈ Ω ∩ ℝ`. Then the reflection of `J` has at most twice the
`W^{1,p}` norm of `J` on `Ω ∩ {0 ≤ t}`. -/
theorem eLpNormWkp_crReflectionCoeff_le {J : ℂ → V →L[ℝ] V} {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V}
    (hΩ : MapsTo (starRingEnd ℂ) Ω Ω) (hp : 1 ≤ p)
    (hJW : HasWeakFDerivOn volume (Opens.interior ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})) J DJ)
    (hJc : ContinuousOn J ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hJR : ∀ x : ℝ, (x : ℂ) ∈ Ω → ∀ v, R (J x v) = -J x (R v))
    (hDJ : MemLpLoc 1 ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) DJ) :
    eLpNormWkp p Ω 1 (crReflectionCoeff R.toContinuousLinearEquiv J) ≤
      2 * eLpNormWkp p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) 1 J := by
  have hc := isSobolevCRCoefficients_crReflection (R := R.toContinuousLinearEquiv) (S := 0) hΩ
    le_rfl hJW hJc hJR hDJ memLpLoc_zero
  rw [eLpNormWkp_succ_eq_of_hasWeakFDerivOn hc.hasWeakFDerivOn,
    eLpNormWkp_succ_eq_of_hasWeakFDerivOn_interior (inter_setOf_im_nonneg_ae_eq_interior Ω) hJW,
    eLpNormWkp_zero, eLpNormWkp_zero, mul_add]
  exact add_le_add (eLpNorm_crReflectionCoeff_le hΩ hp J) (eLpNorm_crReflectionDeriv_le hΩ hp DJ)

omit [CompleteSpace V] in
/-- **The reflected coefficients are Sobolev coefficients with norms at most `2 M`.** Under the
hypotheses of `TauCeti.isSobolevCRCoefficients_crReflection` for an isometry `R`, if
`‖J‖_{W^{1,p}(Ω ∩ {0 ≤ t})} ≤ M` and `‖S‖_{Lᵖ(Ω ∩ {0 ≤ t})} ≤ M`, then the reflected coefficients
are Sobolev coefficients on `Ω` whose norms `‖crReflectionCoeff R J‖_{W^{1,p}(Ω)}` and
`‖crReflectionZeroth R S‖_{Lᵖ(Ω)}` are at most `2 M`. -/
theorem isSobolevCRCoefficients_crReflection_of_le {J S : ℂ → V →L[ℝ] V}
    {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V} {M : ℝ≥0} (hΩ : MapsTo (starRingEnd ℂ) Ω Ω) (hp : 1 ≤ p)
    (hJW : HasWeakFDerivOn volume (Opens.interior ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})) J DJ)
    (hJc : ContinuousOn J ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hJR : ∀ x : ℝ, (x : ℂ) ∈ Ω → ∀ v, R (J x v) = -J x (R v))
    (hDJ : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) DJ)
    (hS : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) S)
    (hJM : eLpNormWkp p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) 1 J ≤ M)
    (hSM : eLpNorm S p (volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})) ≤ M) :
    IsSobolevCRCoefficients p Ω (crReflectionCoeff R.toContinuousLinearEquiv J)
        (crReflectionDeriv R.toContinuousLinearEquiv DJ)
        (crReflectionZeroth R.toContinuousLinearEquiv S) ∧
      eLpNormWkp p Ω 1 (crReflectionCoeff R.toContinuousLinearEquiv J) ≤ ↑(2 * M) ∧
      eLpNorm (crReflectionZeroth R.toContinuousLinearEquiv S) p (volume.restrict Ω) ≤
        ↑(2 * M) :=
  ⟨isSobolevCRCoefficients_crReflection hΩ hp hJW hJc hJR hDJ hS,
    (eLpNormWkp_crReflectionCoeff_le hΩ hp hJW hJc hJR (hDJ.mono_exponent hp)).trans
      (by push_cast; gcongr),
    (eLpNorm_crReflectionZeroth_le hΩ hp S).trans (by push_cast; gcongr)⟩

omit [CompleteSpace V] in
/-- An estimate for the twisted reflection of `ξ` on `Ω` gives the estimate up to the real axis,
with the constant doubled: the left side restricts to `U ∩ {0 ≤ t}`, where the reflection is `ξ`
off the null axis, and the reflection at most doubles the norms on the right side. -/
private theorem eLpNormWkp_inter_le_of_twistedReflection (hΩ : MapsTo (starRingEnd ℂ) Ω Ω)
    (hq : 1 ≤ q) (hr : 1 ≤ r) {C : ℝ≥0} {ξ η : ℂ → V}
    (h : eLpNormWkp r U 1 (twistedReflection (R : V →L[ℝ] V) ξ) ≤
      C * (eLpNorm (twistedReflection (R : V →L[ℝ] V) η) r (volume.restrict Ω) +
        eLpNorm (twistedReflection (R : V →L[ℝ] V) ξ) q (volume.restrict Ω))) :
    eLpNormWkp r (U ∩ {z | 0 ≤ z.im}) 1 ξ ≤
      ↑(2 * C) * (eLpNorm η r (volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})) +
        eLpNorm ξ q (volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))) := by
  have hR (v : V) : ‖(R : V →L[ℝ] V) v‖ ≤ ‖v‖ := (R.norm_map v).le
  have hae : ξ =ᵐ[volume.restrict (U ∩ {z | 0 ≤ z.im})] twistedReflection (R : V →L[ℝ] V) ξ :=
    Filter.EventuallyEq.symm (ae_restrict_of_ae_restrict_of_subset inter_subset_right
      (twistedReflection_ae_eq_restrict _ ξ))
  rw [eLpNormWkp_congr_ae hae]
  refine (eLpNormWkp_mono_set inter_subset_left).trans (h.trans ?_)
  calc _ ≤ ↑C * (2 * eLpNorm η r (volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})) +
        2 * eLpNorm ξ q (volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))) := by
        gcongr
        · exact eLpNorm_twistedReflection_le hΩ hR hr η
        · exact eLpNorm_twistedReflection_le hΩ hR hq ξ
    _ = _ := by push_cast; ring

variable [FiniteDimensional ℝ V] (hR : Function.Involutive R)
include hR

omit [FiniteDimensional ℝ V] in
/-- An interior estimate on `Ω`, applied to the reflected solution and coefficients, gives the
estimate up to the real axis with the constant doubled. -/
private theorem eLpNormWkp_inter_le_of_interior (hΩ : MapsTo (starRingEnd ℂ) Ω Ω)
    (hΛ : ∀ v, R v = v → v ∈ Λ) (hpq : p⁻¹ + q⁻¹ ≤ 1) (hr : 1 ≤ r) {C M : ℝ≥0}
    (hC : ∀ (J S : ℂ → V →L[ℝ] V) (DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V) (ξ η : ℂ → V),
      IsWeakCRSolution q Ω J DJ S ξ η → IsSobolevCRCoefficients p Ω J DJ S →
      (∀ᵐ z ∂volume.restrict Ω, J z * J z = -1) → eLpNormWkp p Ω 1 J ≤ M →
      eLpNorm S p (volume.restrict Ω) ≤ M → MemLpLoc r Ω η →
      eLpNormWkp r U 1 ξ ≤ C * (eLpNorm η r (volume.restrict Ω) +
        eLpNorm ξ q (volume.restrict Ω)))
    {J S : ℂ → V →L[ℝ] V} {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V} {ξ η : ℂ → V}
    (h : IsWeakCRSolutionHalf q Ω Λ J DJ S ξ η)
    (hc : IsSobolevCRCoefficients p Ω (crReflectionCoeff R.toContinuousLinearEquiv J)
      (crReflectionDeriv R.toContinuousLinearEquiv DJ)
      (crReflectionZeroth R.toContinuousLinearEquiv S))
    (hJ2 : ∀ᵐ z ∂volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}), J z * J z = -1)
    (hJM : eLpNormWkp p Ω 1 (crReflectionCoeff R.toContinuousLinearEquiv J) ≤ M)
    (hSM : eLpNorm (crReflectionZeroth R.toContinuousLinearEquiv S) p (volume.restrict Ω) ≤ M)
    (hη : MemLpLoc r ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) η) :
    eLpNormWkp r (U ∩ {z | 0 ≤ z.im}) 1 ξ ≤
      ↑(2 * C) * (eLpNorm η r (volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})) +
        eLpNorm ξ q (volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))) := by
  refine eLpNormWkp_inter_le_of_twistedReflection (R := R) hΩ
    (ENNReal.one_le_right_of_inv_add_inv_le_one hpq) hr (hC _ _ _ _ _ ?_ hc
      (ae_crReflectionCoeff_mul_self hΩ hJ2) hJM hSM (hη.twistedReflection hΩ _))
  exact h.isWeakCRSolution_crReflection hR hΩ hΛ
    ((memLpLoc_crReflectionCoeff_iff hΩ).1 hc.memLpLoc_coeff)
    ((memLpLoc_crReflectionDeriv_iff hΩ).1 hc.memLpLoc_deriv)
    ((memLpLoc_crReflectionZeroth_iff hΩ).1 hc.memLpLoc_zeroth) hpq

/-- **The order-zero estimate up to the real axis** (McDuff–Salamon, Lemma B.4.6 with a totally
real boundary condition). Let `Ω` be invariant under conjugation, `R` an isometric involution of
the finite-dimensional space `V` whose fixed vectors lie in `Λ`, `p > 2`, `1 < r < ∞` and
`1/p + 1/q ≤ 1/r`, let `U` have compact closure in `Ω`, and let `M ≥ 0`. There is a constant `C`
such that for all coefficients `J`, `S` with `J² = -1` almost everywhere on `Ω ∩ {0 ≤ t}` whose
reflections are Sobolev coefficients on `Ω` with `‖crReflectionCoeff R J‖_{W^{1,p}(Ω)} ≤ M` and
`‖crReflectionZeroth R S‖_{Lᵖ(Ω)} ≤ M`, every weak solution `ξ ∈ L^q_loc` up to the real axis of
`∂_s ξ + J ∂_t ξ + S ξ = η` with boundary subspace `Λ` and `η ∈ Lʳ_loc` up to the axis satisfies
`‖ξ‖_{W^{1,r}(U ∩ {0 ≤ t})} ≤ C (‖η‖_{Lʳ(Ω ∩ {0 ≤ t})} + ‖ξ‖_{L^q(Ω ∩ {0 ≤ t})})`. -/
theorem exists_eLpNormWkp_one_le_of_isWeakCRSolutionHalf (hΩ : MapsTo (starRingEnd ℂ) Ω Ω)
    (hΛ : ∀ v, R v = v → v ∈ Λ) (hp : 2 < p) (hpqr : p⁻¹ + q⁻¹ ≤ r⁻¹) (hr : 1 < r)
    (hr_top : r ≠ ⊤) (hUc : IsCompact (closure U)) (hUΩ : closure U ⊆ Ω) (M : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ (J S : ℂ → V →L[ℝ] V) (DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V) (ξ η : ℂ → V),
      IsWeakCRSolutionHalf q Ω Λ J DJ S ξ η →
      IsSobolevCRCoefficients p Ω (crReflectionCoeff R.toContinuousLinearEquiv J)
        (crReflectionDeriv R.toContinuousLinearEquiv DJ)
        (crReflectionZeroth R.toContinuousLinearEquiv S) →
      (∀ᵐ z ∂volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}), J z * J z = -1) →
      eLpNormWkp p Ω 1 (crReflectionCoeff R.toContinuousLinearEquiv J) ≤ M →
      eLpNorm (crReflectionZeroth R.toContinuousLinearEquiv S) p (volume.restrict Ω) ≤ M →
      MemLpLoc r ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) η →
      eLpNormWkp r (U ∩ {z | 0 ≤ z.im}) 1 ξ ≤
        C * (eLpNorm η r (volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})) +
          eLpNorm ξ q (volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))) := by
  obtain ⟨C, hC⟩ := exists_eLpNormWkp_one_le_of_isWeakCRSolution (V := V) hp hpqr hr hr_top hUc
    hUΩ M
  exact ⟨2 * C, fun J S DJ ξ η => eLpNormWkp_inter_le_of_interior hR hΩ hΛ
    (hpqr.trans (ENNReal.inv_le_one.2 hr.le)) hr.le hC⟩

/-- **The `W^{1,r}` estimate up to the real axis** (McDuff–Salamon, Lemmas B.4.4 and B.4.6 with a
totally real boundary condition). Under the hypotheses of
`TauCeti.exists_eLpNormWkp_one_le_of_isWeakCRSolutionHalf`, with `1/p + 1/q < 1` and `r ≤ p` in
place of `1/p + 1/q ≤ 1/r`, there is a constant `C`, uniform over coefficients whose reflections
are bounded by `M`, such that every weak solution `ξ ∈ L^q_loc` up to the real axis satisfies
`‖ξ‖_{W^{1,r}(U ∩ {0 ≤ t})} ≤ C (‖η‖_{Lʳ(Ω ∩ {0 ≤ t})} + ‖ξ‖_{L^q(Ω ∩ {0 ≤ t})})`. -/
theorem exists_eLpNormWkp_one_le_of_isWeakCRSolutionHalf_of_le (hΩ : MapsTo (starRingEnd ℂ) Ω Ω)
    (hΛ : ∀ v, R v = v → v ∈ Λ) (hp : 2 < p) (hpq : p⁻¹ + q⁻¹ < 1) (hr : 1 < r)
    (hr_top : r ≠ ⊤) (hrp : r ≤ p) (hUc : IsCompact (closure U)) (hUΩ : closure U ⊆ Ω)
    (M : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ (J S : ℂ → V →L[ℝ] V) (DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V) (ξ η : ℂ → V),
      IsWeakCRSolutionHalf q Ω Λ J DJ S ξ η →
      IsSobolevCRCoefficients p Ω (crReflectionCoeff R.toContinuousLinearEquiv J)
        (crReflectionDeriv R.toContinuousLinearEquiv DJ)
        (crReflectionZeroth R.toContinuousLinearEquiv S) →
      (∀ᵐ z ∂volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}), J z * J z = -1) →
      eLpNormWkp p Ω 1 (crReflectionCoeff R.toContinuousLinearEquiv J) ≤ M →
      eLpNorm (crReflectionZeroth R.toContinuousLinearEquiv S) p (volume.restrict Ω) ≤ M →
      MemLpLoc r ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) η →
      eLpNormWkp r (U ∩ {z | 0 ≤ z.im}) 1 ξ ≤
        C * (eLpNorm η r (volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})) +
          eLpNorm ξ q (volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))) := by
  obtain ⟨C, hC⟩ := exists_eLpNormWkp_one_le_of_isWeakCRSolution_of_le (V := V) hp hpq hr hr_top
    hrp hUc hUΩ M
  exact ⟨2 * C, fun J S DJ ξ η => eLpNormWkp_inter_le_of_interior hR hΩ hΛ hpq.le hr.le hC⟩

/-- **The order-zero estimate up to the real axis for Sobolev coefficients** (McDuff–Salamon,
Lemma B.4.6 with a totally real boundary condition). Under the hypotheses of
`TauCeti.exists_eLpNormWkp_one_le_of_isWeakCRSolutionHalf`, the constant `C` applies to all
coefficients `J`, `S` such that `J` is continuous on `Ω ∩ {0 ≤ t}` with weak derivative `DJ` on
the open upper part and anticommutes with `R` on `Ω ∩ ℝ`, `DJ`, `S` are locally `Lᵖ` up to the
axis, `‖J‖_{W^{1,p}(Ω ∩ {0 ≤ t})} ≤ M` and `‖S‖_{Lᵖ(Ω ∩ {0 ≤ t})} ≤ M`. Then the reflected
coefficients are Sobolev coefficients on `Ω` (`TauCeti.isSobolevCRCoefficients_crReflection`) with
norms at most `2 M` (`TauCeti.eLpNormWkp_crReflectionCoeff_le`,
`TauCeti.eLpNorm_crReflectionZeroth_le`). -/
theorem exists_eLpNormWkp_one_le_of_isWeakCRSolutionHalf_of_hasWeakFDerivOn
    (hΩ : MapsTo (starRingEnd ℂ) Ω Ω) (hΛ : ∀ v, R v = v → v ∈ Λ) (hp : 2 < p)
    (hpqr : p⁻¹ + q⁻¹ ≤ r⁻¹) (hr : 1 < r) (hr_top : r ≠ ⊤) (hUc : IsCompact (closure U))
    (hUΩ : closure U ⊆ Ω) (M : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ (J S : ℂ → V →L[ℝ] V) (DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V) (ξ η : ℂ → V),
      IsWeakCRSolutionHalf q Ω Λ J DJ S ξ η →
      HasWeakFDerivOn volume (Opens.interior ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})) J DJ →
      ContinuousOn J ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) →
      (∀ x : ℝ, (x : ℂ) ∈ Ω → ∀ v, R (J x v) = -J x (R v)) →
      MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) DJ →
      MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) S →
      (∀ᵐ z ∂volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}), J z * J z = -1) →
      eLpNormWkp p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) 1 J ≤ M →
      eLpNorm S p (volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})) ≤ M →
      MemLpLoc r ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) η →
      eLpNormWkp r (U ∩ {z | 0 ≤ z.im}) 1 ξ ≤
        C * (eLpNorm η r (volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})) +
          eLpNorm ξ q (volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))) := by
  obtain ⟨C, hC⟩ := exists_eLpNormWkp_one_le_of_isWeakCRSolutionHalf hR hΩ hΛ hp hpqr hr hr_top
    hUc hUΩ (2 * M)
  refine ⟨C, fun J S DJ ξ η h hJW hJc hJR hDJ hS hJ2 hJM hSM => ?_⟩
  obtain ⟨hc, hJM', hSM'⟩ := isSobolevCRCoefficients_crReflection_of_le hΩ
    (one_le_two.trans hp.le) hJW hJc hJR hDJ hS hJM hSM
  exact hC J S DJ ξ η h hc hJ2 hJM' hSM'

/-- **The `W^{1,r}` estimate up to the real axis for Sobolev coefficients** (McDuff–Salamon,
Lemmas B.4.4 and B.4.6 with a totally real boundary condition). Under the hypotheses of
`TauCeti.exists_eLpNormWkp_one_le_of_isWeakCRSolutionHalf_of_le`, the constant `C` applies to all
coefficients `J`, `S` such that `J` is continuous on `Ω ∩ {0 ≤ t}` with weak derivative `DJ` on
the open upper part and anticommutes with `R` on `Ω ∩ ℝ`, `DJ`, `S` are locally `Lᵖ` up to the
axis, `‖J‖_{W^{1,p}(Ω ∩ {0 ≤ t})} ≤ M` and `‖S‖_{Lᵖ(Ω ∩ {0 ≤ t})} ≤ M`. -/
theorem exists_eLpNormWkp_one_le_of_isWeakCRSolutionHalf_of_le_of_hasWeakFDerivOn
    (hΩ : MapsTo (starRingEnd ℂ) Ω Ω) (hΛ : ∀ v, R v = v → v ∈ Λ) (hp : 2 < p)
    (hpq : p⁻¹ + q⁻¹ < 1) (hr : 1 < r) (hr_top : r ≠ ⊤) (hrp : r ≤ p)
    (hUc : IsCompact (closure U)) (hUΩ : closure U ⊆ Ω) (M : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ (J S : ℂ → V →L[ℝ] V) (DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V) (ξ η : ℂ → V),
      IsWeakCRSolutionHalf q Ω Λ J DJ S ξ η →
      HasWeakFDerivOn volume (Opens.interior ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})) J DJ →
      ContinuousOn J ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) →
      (∀ x : ℝ, (x : ℂ) ∈ Ω → ∀ v, R (J x v) = -J x (R v)) →
      MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) DJ →
      MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) S →
      (∀ᵐ z ∂volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}), J z * J z = -1) →
      eLpNormWkp p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) 1 J ≤ M →
      eLpNorm S p (volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})) ≤ M →
      MemLpLoc r ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) η →
      eLpNormWkp r (U ∩ {z | 0 ≤ z.im}) 1 ξ ≤
        C * (eLpNorm η r (volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})) +
          eLpNorm ξ q (volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))) := by
  obtain ⟨C, hC⟩ := exists_eLpNormWkp_one_le_of_isWeakCRSolutionHalf_of_le hR hΩ hΛ hp hpq hr
    hr_top hrp hUc hUΩ (2 * M)
  refine ⟨C, fun J S DJ ξ η h hJW hJc hJR hDJ hS hJ2 hJM hSM => ?_⟩
  obtain ⟨hc, hJM', hSM'⟩ := isSobolevCRCoefficients_crReflection_of_le hΩ
    (one_le_two.trans hp.le) hJW hJc hJR hDJ hS hJM hSM
  exact hC J S DJ ξ η h hc hJ2 hJM' hSM'

end TauCeti
