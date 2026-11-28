/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.Weak
import TauCeti.Analysis.Sobolev.Local.Morrey
import TauCeti.Analysis.Sobolev.Local.SobolevEmbedding
import TauCeti.Analysis.Sobolev.WeakDeriv.Bilinear.Holder
import TauCeti.Data.ENNReal.Holder

/-!
# Weak Cauchy–Riemann solutions from minimal weak differentiability and Morrey's embedding

For Sobolev Cauchy–Riemann coefficients `IsSobolevCRCoefficients p Ω J DJ S` with `2 < p ≤ ∞`, any
map `ξ : ℂ → V` into a finite-dimensional real inner product space that merely has a weak
derivative `Dξ` on `Ω` (with no `L^q_loc` hypothesis on `ξ` or `Dξ` beyond local integrability)
and satisfies `∂_s ξ + J ∂_t ξ + S ξ = η` almost everywhere on `Ω` is a weak solution
`TauCeti.IsWeakCRSolution 2 Ω J DJ S ξ η`.

The proof places `ξ ∈ W^{1,1}_loc(Ω) ⊆ L²_loc(Ω)` via the planar Sobolev embedding
`TauCeti.MemWkpLoc.memLpLoc_two`, replaces `J` by its continuous Morrey representative
`TauCeti.MeasureTheory.preciseRepresentative volume J`, applies the endpoint weak Leibniz rule
`TauCeti.HasWeakLineDerivOn.bilin_of_continuousOn` for `(J', ξ)` in `W^{1,p}_loc × L²_loc`, and
transfers the resulting weak equation back to `(J, DJ, S)` via
`TauCeti.isWeakCRSolution_congr_ae`.

Keeping this lemma in a separate module avoids importing Morrey and Sobolev embeddings into
`TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.Weak`.

## Main results

* `TauCeti.IsSobolevCRCoefficients.isWeakCRSolution_of_hasWeakFDerivOn`: conversion from
  `HasWeakFDerivOn` and an almost-everywhere Cauchy–Riemann equation to `IsWeakCRSolution 2`.
-/

public section

open Complex MeasureTheory TopologicalSpace
open scoped ENNReal NNReal

namespace TauCeti

/-- Any map `ξ` with weak derivative `Dξ` on `Ω` satisfying `∂_s ξ + J ∂_t ξ + S ξ = η` almost
everywhere on `Ω` for Sobolev coefficients at exponent `2 < p ≤ ∞` lies in `L²_loc(Ω)` (via the
planar embedding `W^{1,1}_loc ⊆ L²_loc`) and satisfies `IsWeakCRSolution 2 Ω J DJ S ξ η`. -/
theorem IsSobolevCRCoefficients.isWeakCRSolution_of_hasWeakFDerivOn
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    {Ω : Opens ℂ} {p : ℝ≥0∞} {J S : ℂ → V →L[ℝ] V} {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V}
    {ξ η : ℂ → V} {Dξ : ℂ → ℂ →L[ℝ] V}
    (hc : IsSobolevCRCoefficients p Ω J DJ S) (hp : 2 < p)
    (hDξ : HasWeakFDerivOn volume Ω ξ Dξ)
    (heq : ∀ᵐ z ∂volume.restrict Ω, Dξ z 1 + J z (Dξ z I) + S z (ξ z) = η z) :
    IsWeakCRSolution 2 Ω J DJ S ξ η := by
  have : CompleteSpace V := FiniteDimensional.completeSpace ℝ V
  have hloc := Ω.isOpen.isLocallyClosed
  have hp1 : 1 ≤ p := one_le_two.trans hp.le
  have hp2 : p⁻¹ + (2 : ℝ≥0∞)⁻¹ < 1 := ENNReal.inv_add_inv_two_lt_one_iff.2 hp
  -- `HasWeakFDerivOn` places `ξ ∈ W^{1,1}_loc(Ω) ⊆ L²_loc(Ω)` via the 2D Sobolev embedding.
  have hξ1 : MemWkpLoc 1 Ω 1 ξ :=
    memWkpLoc_succ_iff_of_isOpen.2
      ⟨(memLpLoc_one_iff_locallyIntegrableOn hloc).2 hDξ.locallyIntegrableOn, Dξ, hDξ,
        memWkpLoc_zero_iff.2 ((memLpLoc_one_iff_locallyIntegrableOn hloc).2
          hDξ.locallyIntegrableOn_deriv)⟩
  have hξ2 : MemLpLoc 2 Ω ξ := hξ1.memLpLoc_two le_rfl
  -- Replace `J` by its continuous Morrey representative `J'`.
  set J' := TauCeti.MeasureTheory.preciseRepresentative volume J
  have hJ'cont : ContinuousOn J' Ω := hc.memWkpLoc_coeff.continuousOn_preciseRepresentative hp
  have hJJ' : J =ᵐ[volume.restrict Ω] J' := hc.memLpLoc_coeff.ae_eq_preciseRepresentative hp1
  have hc' : IsSobolevCRCoefficients p Ω J' DJ S := hc.congr_ae hJJ' .rfl .rfl
  have heq' : ∀ᵐ z ∂volume.restrict Ω, Dξ z 1 + J' z (Dξ z I) + S z (ξ z) = η z := by
    filter_upwards [heq, hJJ'] with z hz hJ using by rwa [← hJ]
  have hJ'ξ : HasWeakLineDerivOn volume Ω (fun z => J' z (ξ z))
      (fun z => DJ z I (ξ z) + J' z (Dξ z I)) I := by
    simpa only [ContinuousLinearMap.id_apply] using
      (hc'.hasWeakFDerivOn.hasWeakLineDerivOn I).bilin_of_continuousOn
        (ContinuousLinearMap.id ℝ (V →L[ℝ] V)) hp2.le hJ'cont
        (fun K hKc hKΩ => memLpLoc_iff.1 (hc'.memLpLoc_deriv.clm_comp
          (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) I)) K hKΩ hKc)
        (hDξ.hasWeakLineDerivOn I) (fun K hKc hKΩ => memLpLoc_iff.1 hξ2 K hKΩ hKc)
  exact (isWeakCRSolution_congr_ae hJJ' .rfl .rfl .rfl .rfl).2 <|
    (hc'.isWeakCRSolution_iff_ae_of_hasWeakLineDerivOn hp2.le hDξ hξ2 hJ'ξ).2 heq'

end TauCeti
