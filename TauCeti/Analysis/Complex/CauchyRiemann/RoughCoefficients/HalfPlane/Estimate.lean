/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.Estimate
public import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.HalfPlane.Reflection
import TauCeti.Data.ENNReal.Holder

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

end TauCeti
