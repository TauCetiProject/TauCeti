/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.Weak
import TauCeti.Analysis.Distribution.TestFunction.Inner
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Sobolev.WeakDeriv.Bilinear.Holder
import TauCeti.Analysis.Sobolev.WeakDeriv.Symmetry

/-!
# The `t`-derivative equation for real Cauchy–Riemann equations with Sobolev coefficients

Let `Ω ⊆ ℂ` be open, write `z = s + i t`, and let `V` be a finite-dimensional real inner product
space. For coefficients `J ∈ W^{1,p}_loc(Ω; End V)` and `S ∈ Lᵖ_loc(Ω; End V)` and a weak solution
`ξ ∈ L^q_loc(Ω)` of

`∂_s ξ + J ∂_t ξ + S ξ = η`

in the sense of `TauCeti.IsWeakCRSolution`, with `1/p + 1/q ≤ 1` and `p, q` finite, if `ξ` has a
weak derivative `Dξ ∈ L^q_loc(Ω)`, `S` has a weak derivative `DS ∈ Lᵖ_loc(Ω)`, and `η` has a weak
derivative `Dη`, then `∂_t ξ = Dξ · I` solves the differentiated `t`-equation

`∂_s (∂_t ξ) + J ∂_t (∂_t ξ) + (S + ∂_t J) ∂_t ξ = ∂_t η - (∂_t S) ξ`

weakly (`TauCeti.IsWeakCRSolution.apply_I_of_hasWeakFDerivOn`). Unlike the first row of
McDuff–Salamon's differentiated system, this equation does not involve `∂_s ∂_t J`. For full
higher-order interior `W^{k+1,q}_loc` regularity, see
`TauCeti.IsWeakCRSolution.memWkpLoc_of_le` in
`TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.Regularity`.

## Main results

* `TauCeti.IsWeakCRSolution.apply_I_of_hasWeakFDerivOn`: the weak equation for `∂_t ξ`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.4, Proposition B.4.9.
-/

public section

open MeasureTheory TopologicalSpace Complex ContinuousLinearMap
open scoped InnerProductSpace ENNReal NNReal Distributions LineDeriv

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  {Ω : Opens ℂ} {J S : ℂ → V →L[ℝ] V} {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V} {ξ η : ℂ → V}

/-- Adding `∂_t J` to the zeroth-order coefficient cancels the `∂_t J` term of the formal adjoint:
the formal adjoint of `∂_s + J ∂_t + (S + ∂_t J)` is `-∂_s - Jᵀ ∂_t + Sᵀ`. -/
private theorem inner_crFormalAdjoint_add_deriv_I (φ : ℂ → V) (z : ℂ) (w : V) :
    ⟪crFormalAdjoint J DJ (fun z => S z + DJ z I) φ z, w⟫_ℝ =
      -⟪fderiv ℝ φ z 1, w⟫_ℝ - ⟪fderiv ℝ φ z I, J z w⟫_ℝ + ⟪φ z, S z w⟫_ℝ := by
  rw [inner_crFormalAdjoint, add_apply, inner_add_right]
  ring

/-- **The `t`-derivative of the equation, tested against `φ`.** If `∂_s ξ + J ∂_t ξ + S ξ = η`
almost everywhere on `Ω`, with weak derivatives `Dξ`, `DS` and `Dη` of `ξ`, `S` and `η`, then
`∫ ⟪φ, ∂_t η - (∂_t S) ξ⟫ = -∫ ⟪∂_t φ, ∂_s ξ⟫ - ∫ ⟪∂_t φ, J ∂_t ξ⟫ + ∫ ⟪φ, S ∂_t ξ⟫`. -/
private theorem integral_inner_deriv_I_sub_eq [FiniteDimensional ℝ V] {p q : ℝ≥0∞}
    (hc : IsSobolevCRCoefficients p Ω J DJ S) (hpq : p⁻¹ + q⁻¹ ≤ 1) (hp : p ≠ ⊤) (hq : q ≠ ⊤)
    {DS : ℂ → ℂ →L[ℝ] V →L[ℝ] V} (hS : HasWeakFDerivOn volume Ω S DS) (hDS : MemLpLoc p Ω DS)
    {Dξ Dη : ℂ → ℂ →L[ℝ] V} (hξ : HasWeakFDerivOn volume Ω ξ Dξ) (hξq : MemLpLoc q Ω ξ)
    (hDξ : MemLpLoc q Ω Dξ) (hη : HasWeakFDerivOn volume Ω η Dη)
    (heq : ∀ᵐ z ∂volume.restrict Ω, Dξ z 1 + J z (Dξ z I) + S z (ξ z) = η z) (φ : 𝓓(Ω, V)) :
    ∫ z, ⟪(φ : ℂ → V) z, Dη z I - DS z I (ξ z)⟫_ℝ =
      -(∫ z, ⟪fderiv ℝ (φ : ℂ → V) z I, Dξ z 1⟫_ℝ) -
        (∫ z, ⟪fderiv ℝ (φ : ℂ → V) z I, J z (Dξ z I)⟫_ℝ) +
          ∫ z, ⟪(φ : ℂ → V) z, S z (Dξ z I)⟫_ℝ := by
  have : Fact (1 ≤ p) := ⟨ENNReal.inv_le_one.1 (le_self_add.trans hpq)⟩
  have hq1 : 1 ≤ q := ENNReal.inv_le_one.1 (le_add_self.trans hpq)
  have : Fact (1 ≤ q) := ⟨hq1⟩
  have hloc := Ω.isOpen.isLocallyClosed
  have hDξI : MemLpLoc q Ω (fun z => Dξ z I) := hDξ.clm_comp (apply ℝ V I)
  have hDSI : MemLpLoc p Ω (fun z => DS z I) := hDS.clm_comp (apply ℝ (V →L[ℝ] V) I)
  have hDSξ := φ.integrable_inner (hDSI.locallyIntegrableOn_clm_apply hξq hpq hloc)
  have hA₂ := φ.integrable_inner_fderiv
    (hc.memLpLoc_coeff.locallyIntegrableOn_clm_apply hDξI hpq hloc) I
  have hA₃ := φ.integrable_inner (hc.memLpLoc_zeroth.locallyIntegrableOn_clm_apply hDξI hpq hloc)
  have hDξ1 : MemLpLoc q Ω (fun z => Dξ z 1) := hDξ.clm_comp (apply ℝ V 1)
  have hB₁ := φ.integrable_inner_fderiv (hDξ1.locallyIntegrableOn hq1 hloc) I
  have hB₂ := φ.integrable_inner_fderiv
    (hc.memLpLoc_zeroth.locallyIntegrableOn_clm_apply hξq hpq hloc) I
  -- `∫ ⟪∂_t φ, S ξ⟫ = -∫ ⟪φ, (∂_t S) ξ⟫ - ∫ ⟪φ, S ∂_t ξ⟫`, by the weak Leibniz rule for `S ξ`.
  have hSξφ : ∫ z, ⟪fderiv ℝ (φ : ℂ → V) z I, S z (ξ z)⟫_ℝ =
      -((∫ z, ⟪(φ : ℂ → V) z, DS z I (ξ z)⟫_ℝ) + ∫ z, ⟪(φ : ℂ → V) z, S z (Dξ z I)⟫_ℝ) := by
    have h' := ((hS.hasWeakLineDerivOn I).bilin_of_memLp (ContinuousLinearMap.id ℝ (V →L[ℝ] V))
      hp hp hq hq hpq hpq hpq (hξ.hasWeakLineDerivOn I)
      (fun K hK hKΩ => memLpLoc_iff.1 hc.memLpLoc_zeroth K hKΩ hK)
      (fun K hK hKΩ => memLpLoc_iff.1 hDSI K hKΩ hK) (fun K hK hKΩ => memLpLoc_iff.1 hξq K hKΩ hK)
      (fun K hK hKΩ => memLpLoc_iff.1 hDξI K hKΩ hK)).integral_inner_lineDeriv_eq_neg φ
    simp only [TestFunction.lineDeriv_eq_fderiv, id_apply, inner_add_right] at h'
    rw [h', integral_add hDSξ hA₃]
  -- `∫ ⟪φ, ∂_t η⟫ = -∫ ⟪∂_t φ, η⟫`, and `η = ∂_s ξ + J ∂_t ξ + S ξ` on `Ω`.
  have hηφ : ∫ z, ⟪(φ : ℂ → V) z, Dη z I⟫_ℝ =
      -∫ z, ⟪fderiv ℝ (φ : ℂ → V) z I, Dξ z 1 + J z (Dξ z I) + S z (ξ z)⟫_ℝ := by
    have h' := (hη.hasWeakLineDerivOn I).integral_inner_lineDeriv_eq_neg φ
    simp only [TestFunction.lineDeriv_eq_fderiv] at h'
    have hcongr : ∫ z, ⟪fderiv ℝ (φ : ℂ → V) z I, η z⟫_ℝ =
        ∫ z, ⟪fderiv ℝ (φ : ℂ → V) z I, Dξ z 1 + J z (Dξ z I) + S z (ξ z)⟫_ℝ := by
      refine integral_congr_ae ?_
      filter_upwards [ae_imp_of_ae_restrict heq] with z hz
      by_cases hzΩ : z ∈ (Ω : Set ℂ)
      · rw [hz hzΩ]
      · simp [fderiv_of_notMem_tsupport ℝ fun h' => hzΩ (φ.tsupport_subset h')]
    rw [← hcongr, h', neg_neg]
  simp only [inner_sub_right]
  rw [integral_sub (φ.integrable_inner (hη.hasWeakLineDerivOn I).locallyIntegrableOn_deriv) hDSξ,
    hηφ]
  simp only [inner_add_right]
  rw [integral_add _ hB₂, integral_add hB₁ hA₂, hSξφ]
  · ring
  exact hB₁.add hA₂

namespace IsWeakCRSolution

/-- **The equation for `∂_t ξ`.** Let `ξ` be a weak solution of `∂_s ξ + J ∂_t ξ + S ξ = η` on
`Ω` with Sobolev coefficients, `1/p + 1/q ≤ 1` and `p, q` finite. Suppose that `ξ` has a weak
derivative `Dξ ∈ L^q_loc`, that `S` has a weak derivative `DS ∈ Lᵖ_loc`, and that `η` has a weak
derivative `Dη`. Then `∂_t ξ = Dξ · I` is a weak solution of

`∂_s (∂_t ξ) + J ∂_t (∂_t ξ) + (S + ∂_t J) ∂_t ξ = ∂_t η - (∂_t S) ξ`. -/
theorem apply_I_of_hasWeakFDerivOn [FiniteDimensional ℝ V] {p q : ℝ≥0∞}
    (h : IsWeakCRSolution q Ω J DJ S ξ η) (hc : IsSobolevCRCoefficients p Ω J DJ S)
    (hpq : p⁻¹ + q⁻¹ ≤ 1) (hp : p ≠ ⊤) (hq : q ≠ ⊤) {DS : ℂ → ℂ →L[ℝ] V →L[ℝ] V}
    (hS : HasWeakFDerivOn volume Ω S DS) (hDS : MemLpLoc p Ω DS) {Dξ Dη : ℂ → ℂ →L[ℝ] V}
    (hξ : HasWeakFDerivOn volume Ω ξ Dξ) (hDξ : MemLpLoc q Ω Dξ)
    (hη : HasWeakFDerivOn volume Ω η Dη) :
    IsWeakCRSolution q Ω J DJ (fun z => S z + DJ z I) (fun z => Dξ z I)
      (fun z => Dη z I - DS z I (ξ z)) := by
  have hq1 : 1 ≤ q := ENNReal.inv_le_one.1 (le_add_self.trans hpq)
  have hloc := Ω.isOpen.isLocallyClosed
  have hDξI : MemLpLoc q Ω (fun z => Dξ z I) := hDξ.clm_comp (apply ℝ V I)
  have heq := (hc.isWeakCRSolution_iff_ae hpq hξ h.memLpLoc hDξ h.locallyIntegrableOn).1 h
  refine isWeakCRSolution_iff.2 ⟨hDξI, (hη.hasWeakLineDerivOn I).locallyIntegrableOn_deriv.sub
    ((hDS.clm_comp (apply ℝ (V →L[ℝ] V) I)).locallyIntegrableOn_clm_apply h.memLpLoc hpq hloc),
    fun φ => ⟨(hc.add_zeroth (hc.memLpLoc_deriv_apply I)).integrable_inner_crFormalAdjoint hpq
      hDξI φ, ?_⟩⟩
  have hA₁ := φ.integrable_inner_fderiv (hDξI.locallyIntegrableOn hq1 hloc) 1
  have hA₂ := φ.integrable_inner_fderiv
    (hc.memLpLoc_coeff.locallyIntegrableOn_clm_apply hDξI hpq hloc) I
  have hA₃ := φ.integrable_inner (hc.memLpLoc_zeroth.locallyIntegrableOn_clm_apply hDξI hpq hloc)
  -- The mixed partials of `ξ` are symmetric against `φ`: `∫ ⟪∂_t φ, ∂_s ξ⟫ = ∫ ⟪∂_s φ, ∂_t ξ⟫`.
  have hmixed := (hξ.hasWeakLineDerivOn 1).integral_inner_lineDeriv_comm (hξ.hasWeakLineDerivOn I) φ
  simp only [TestFunction.lineDeriv_eq_fderiv] at hmixed
  simp only [inner_crFormalAdjoint_add_deriv_I]
  rw [integral_add _ hA₃, integral_sub _ hA₂, integral_neg,
    integral_inner_deriv_I_sub_eq hc hpq hp hq hS hDS hξ h.memLpLoc hDξ hη heq φ, hmixed]
  exacts [hA₁.neg, hA₁.neg.sub hA₂]

end IsWeakCRSolution

end TauCeti
