/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.Weak
import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.OrderZero
import TauCeti.Analysis.Distribution.TestFunction.Inner
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.InnerProductSpace.Adjoint
import TauCeti.Analysis.Sobolev.WeakDeriv.Bilinear.Holder

/-!
# Partial derivatives of weak solutions with Sobolev coefficients

Let `Ω ⊆ ℂ` be open, write `z = s + i t`, and let `V` be a finite-dimensional real inner product
space. Consider the real Cauchy–Riemann operator `D ξ = ∂_s ξ + J ∂_t ξ + S ξ` with coefficients
`J ∈ W^{1,p}_loc(Ω; End V)` and `S ∈ Lᵖ_loc(Ω; End V)`. Let `ξ ∈ W^{1,q}_loc(Ω)` solve
`D ξ = η` almost everywhere on `Ω`, with `1/p + 1/q ≤ 1`. Formally, differentiating the equation
in a direction `e` gives

`D (∂_e ξ) = ∂_e η - (∂_e J) ∂_t ξ - (∂_e S) ξ`.

This file proves the weak form of this identity when `S` and `η` have weak derivatives in the
direction `e` (`TauCeti.IsSobolevCRCoefficients.isWeakCRSolution_partial`): the partial
derivative `∂_e ξ ∈ L^q_loc` is a weak solution, in the sense of `TauCeti.IsWeakCRSolution`, of
the equation above. Nothing beyond `W^{1,q}_loc` is assumed of `ξ`, and nothing beyond `W^{1,p}_loc`
of `J`, so neither `∂_e ∂_t ξ` nor `∂_e ∂_t J` need exist. This is what lets interior regularity
climb in the order of differentiation (McDuff–Salamon, Proposition B.4.9, Steps 2 and 3): for
`e = 1` and `e = i` the two equations are the components of the differentiated system for
`Ξ = (∂_s ξ, ∂_t ξ)`, whose zeroth-order coefficient is `TauCeti.differentiatedCRCoefficient`, so
the order-zero regularity of weak solutions applies to `Ξ`. The almost-everywhere form of the system
for `ξ ∈ W^{2,q}_loc` is `TauCeti.ae_differentiated_cauchyRiemann`.

The identity behind it is a Green's formula for `∂_e ξ`
(`TauCeti.IsSobolevCRCoefficients.integral_inner_crFormalAdjoint_partial`): for every test
function `φ`,

`∫ ⟪D* φ, ∂_e ξ⟫ = -∫ ⟪∂_e φ, D ξ⟫ - ∫ ⟪φ, (∂_e J) ∂_t ξ + (∂_e S) ξ⟫`.

For a smooth `J` this is integration by parts. For a Sobolev `J` the second derivative of `J` that
integration by parts would produce does not appear: the identity needed is the symmetry
`∫ ⟪∂_t Ψ, ∂_e ξ⟫ = ∫ ⟪∂_e Ψ, ∂_t ξ⟫` of the mixed weak derivatives of `ξ`, tested against the
field `Ψ = Jᵀ φ`, which is only of class `W^{1,p}`
(`TauCeti.HasWeakFDerivOn.setIntegral_inner_apply_comm`).

## Main results

* `TauCeti.IsSobolevCRCoefficients.integral_inner_crFormalAdjoint_partial`: Green's formula for a
  partial derivative of `ξ ∈ W^{1,q}_loc`.
* `TauCeti.IsSobolevCRCoefficients.isWeakCRSolution_partial`: a partial derivative `∂_e ξ` of a
  solution is a weak solution of the differentiated equation.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.4, Proposition B.4.9 and its proof.
-/

public section

open MeasureTheory TopologicalSpace Complex Set Metric Filter
open scoped InnerProductSpace ContDiff Distributions ENNReal Topology LineDeriv

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Ω : Opens ℂ} {p q : ℝ≥0∞} {J S S' : ℂ → V →L[ℝ] V} {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V}
  {ξ η η' : ℂ → V} {Dξ : ℂ → ℂ →L[ℝ] V}

/-! ### The field `Jᵀ φ` -/

/-- The bilinear map `(A, w) ↦ Aᵀ w`. -/
private noncomputable def adjointBilin : (V →L[ℝ] V) →L[ℝ] V →L[ℝ] V :=
  ContinuousLinearMap.adjointRealCLM (𝕜 := ℝ)

private theorem inner_adjointBilin (A : V →L[ℝ] V) (w x : V) :
    ⟪adjointBilin A w, x⟫_ℝ = ⟪w, A x⟫_ℝ := by
  rw [adjointBilin, ContinuousLinearMap.adjointRealCLM_apply,
    ContinuousLinearMap.adjoint_inner_left]

/-- The bilinear map `(D, w) ↦ (c ↦ (D c)ᵀ w)`. -/
private noncomputable def adjointDerivBilin : (ℂ →L[ℝ] V →L[ℝ] V) →L[ℝ] V →L[ℝ] ℂ →L[ℝ] V :=
  (ContinuousLinearMap.compL ℝ ℂ (V →L[ℝ] V) V).flip.bilinearComp
    (ContinuousLinearMap.id ℝ _) adjointBilin.flip

/-- The weak derivative `D(Jᵀ φ) = (DJ)ᵀ φ + Jᵀ Dφ` of the field `Jᵀ φ`. -/
private noncomputable def adjointFieldDeriv (J : ℂ → V →L[ℝ] V) (DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V)
    (φ : ℂ → V) (z : ℂ) : ℂ →L[ℝ] V :=
  adjointDerivBilin (DJ z) (φ z) + (adjointBilin (J z)).comp (fderiv ℝ φ z)

private theorem adjointFieldDeriv_def (φ : ℂ → V) (z : ℂ) :
    adjointFieldDeriv J DJ φ z =
      adjointDerivBilin (DJ z) (φ z) + (adjointBilin (J z)).comp (fderiv ℝ φ z) := (rfl)

private theorem adjointFieldDeriv_apply (φ : ℂ → V) (z c : ℂ) :
    adjointFieldDeriv J DJ φ z c = adjointBilin (DJ z c) (φ z) +
      adjointBilin (J z) (fderiv ℝ φ z c) := by
  simp [adjointFieldDeriv, adjointDerivBilin]

private theorem inner_adjointFieldDeriv_apply (φ : ℂ → V) (z c : ℂ) (x : V) :
    ⟪adjointFieldDeriv J DJ φ z c, x⟫_ℝ = ⟪φ z, DJ z c x⟫_ℝ + ⟪fderiv ℝ φ z c, J z x⟫_ℝ := by
  rw [adjointFieldDeriv_apply, inner_add_left, inner_adjointBilin, inner_adjointBilin]

/-- The field `Jᵀ φ` for a test function `φ` and a coefficient `J ∈ W^{1,p}_loc(Ω)` is a compactly
supported Sobolev field in the sense of `TauCeti.HasWeakFDerivOn.setIntegral_inner_apply_comm`. -/
private theorem adjointField_props (hc : IsSobolevCRCoefficients p Ω J DJ S)
    (hpq : p⁻¹ + q⁻¹ ≤ 1) (hp : p ≠ ⊤) (hq : q ≠ ⊤) (φ : 𝓓(Ω, V)) :
    HasWeakFDerivOn volume Ω (fun z => adjointBilin (J z) ((φ : ℂ → V) z))
        (adjointFieldDeriv J DJ φ) ∧
      HasCompactSupport (fun z => adjointBilin (J z) ((φ : ℂ → V) z)) ∧
      tsupport (fun z => adjointBilin (J z) ((φ : ℂ → V) z)) ⊆ Ω ∧
      MemLp (adjointFieldDeriv J DJ φ) p (volume.restrict Ω) := by
  have : Fact (1 ≤ p) := ⟨ENNReal.inv_le_one.1 (le_self_add.trans hpq)⟩
  have : Fact (1 ≤ q) := ⟨ENNReal.inv_le_one.1 (le_add_self.trans hpq)⟩
  have hφc : Continuous (φ : ℂ → V) := φ.continuous
  have hφd : Continuous (fderiv ℝ (φ : ℂ → V)) := φ.contDiff.continuous_fderiv (by simp)
  have h0 (z : ℂ) (hz : z ∉ tsupport (φ : ℂ → V)) :
      adjointBilin (J z) ((φ : ℂ → V) z) = 0 ∧ adjointFieldDeriv J DJ φ z = 0 := by
    refine ⟨by simp [image_eq_zero_of_notMem_tsupport hz], ContinuousLinearMap.ext fun c => ?_⟩
    simp [adjointFieldDeriv_apply, image_eq_zero_of_notMem_tsupport hz,
      fderiv_of_notMem_tsupport ℝ hz]
  have hs : Function.support (fun z => adjointBilin (J z) ((φ : ℂ → V) z)) ⊆ tsupport φ :=
    fun z hz => by_contra fun h' => hz (h0 z h').1
  have hA : MemLpLoc p Ω (fun z => adjointBilin (J z)) := hc.memLpLoc_coeff.clm_comp adjointBilin
  have hD1 : MemLpLoc p Ω (fun z => adjointDerivBilin (DJ z) ((φ : ℂ → V) z)) :=
    (hc.memLpLoc_deriv.clm_comp adjointDerivBilin).clm_apply_continuousOn hφc.continuousOn
  have hD2 : MemLpLoc p Ω (fun z => (adjointBilin (J z)).comp (fderiv ℝ (φ : ℂ → V) z)) :=
    hA.clm_comp_continuousOn hφd.continuousOn
  have hDΨ : MemLpLoc p Ω (adjointFieldDeriv J DJ φ) :=
    (hD1.add hD2).congr_mono (fun z _ => by simp only [Pi.add_apply, adjointFieldDeriv_def])
      subset_rfl
  -- the weak Leibniz rule for `Jᵀ φ`, direction by direction
  have hφw : HasWeakFDerivOn volume Ω (φ : ℂ → V) (fderiv ℝ (φ : ℂ → V)) :=
    (φ.contDiff.contDiffOn.of_le (by simp) : ContDiffOn ℝ 1 (φ : ℂ → V) Ω).hasWeakFDerivOn_fderiv
  have hw : HasWeakFDerivOn volume Ω (fun z => adjointBilin (J z) ((φ : ℂ → V) z))
      (adjointFieldDeriv J DJ φ) := by
    refine hasWeakFDerivOn_iff.2 fun c => ?_
    refine ((hc.hasWeakFDerivOn.hasWeakLineDerivOn c).bilin_of_memLp adjointBilin hp hp hq hq
      hpq hpq hpq (hφw.hasWeakLineDerivOn c)
      (fun K hK hKΩ => memLpLoc_iff.1 hc.memLpLoc_coeff K hKΩ hK)
      (fun K hK hKΩ => memLpLoc_iff.1 (hc.memLpLoc_deriv_apply c) K hKΩ hK)
      (fun K hK hKΩ => memLpLoc_iff.1 (hφc.continuousOn.memLpLoc (U := Ω)) K hKΩ hK)
      (fun K hK hKΩ => memLpLoc_iff.1
        ((hφd.clm_apply continuous_const).continuousOn.memLpLoc (U := Ω)) K hKΩ hK)).congr_ae_deriv
      (.of_forall fun z => ?_)
    simp only [adjointFieldDeriv_apply]
  exact ⟨hw, φ.hasCompactSupport.mono' hs,
    (closure_minimal hs (isClosed_tsupport _)).trans φ.tsupport_subset,
    (MemLpLoc.memLp_of_forall_notMem_eq_zero hDΨ φ.hasCompactSupport φ.tsupport_subset
      fun z hz => (h0 z hz).2).restrict _⟩

/-! ### Green's formula for a partial derivative -/

/-- The symmetry `∫ ⟪∂_t (Jᵀ φ), ∂_e ξ⟫ = ∫ ⟪∂_e (Jᵀ φ), ∂_t ξ⟫`, expanded by the Leibniz rule for
`Jᵀ φ`. -/
private theorem integral_inner_coeff_partial_comm (hc : IsSobolevCRCoefficients p Ω J DJ S)
    (hpq : p⁻¹ + q⁻¹ ≤ 1) (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hξ : HasWeakFDerivOn volume Ω ξ Dξ)
    (hDξq : MemLpLoc q Ω Dξ) (φ : 𝓓(Ω, V)) (e : ℂ) :
    (∫ z, ⟪(φ : ℂ → V) z, DJ z I (Dξ z e)⟫_ℝ) + ∫ z, ⟪fderiv ℝ (φ : ℂ → V) z I, J z (Dξ z e)⟫_ℝ =
      (∫ z, ⟪(φ : ℂ → V) z, DJ z e (Dξ z I)⟫_ℝ) +
        ∫ z, ⟪fderiv ℝ (φ : ℂ → V) z e, J z (Dξ z I)⟫_ℝ := by
  have hloc := Ω.isOpen.isLocallyClosed
  have hD (c : ℂ) : MemLpLoc q Ω (fun z => Dξ z c) :=
    hDξq.clm_comp (ContinuousLinearMap.apply ℝ V c)
  have hJ (c : ℂ) : LocallyIntegrableOn (fun z => J z (Dξ z c)) Ω :=
    hc.memLpLoc_coeff.locallyIntegrableOn_clm_apply (hD c) hpq hloc
  have hDJ (c d : ℂ) : LocallyIntegrableOn (fun z => DJ z c (Dξ z d)) Ω :=
    (hc.memLpLoc_deriv_apply c).locallyIntegrableOn_clm_apply (hD d) hpq hloc
  obtain ⟨hΨ, hΨc, hΨΩ, hDΨ⟩ := adjointField_props hc hpq hp hq φ
  have h := hξ.setIntegral_inner_apply_comm hDξq hΨ hΨc hΨΩ hDΨ hpq I e
  -- Off `Ω` the integrands vanish, so the integrals over `Ω` are integrals over the plane.
  have h0 (c d : ℂ) (z : ℂ) (hz : z ∉ (Ω : Set ℂ)) :
      ⟪adjointFieldDeriv J DJ φ z c, Dξ z d⟫_ℝ = 0 := by
    have hz' : z ∉ tsupport (φ : ℂ → V) := fun h' => hz (φ.tsupport_subset h')
    simp [inner_adjointFieldDeriv_apply, image_eq_zero_of_notMem_tsupport hz',
      fderiv_of_notMem_tsupport ℝ hz']
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (h0 I e),
    setIntegral_eq_integral_of_forall_compl_eq_zero (h0 e I)] at h
  simp only [inner_adjointFieldDeriv_apply] at h
  rwa [integral_add (φ.integrable_inner (hDJ I e)) (φ.integrable_inner_fderiv (hJ e) I),
    integral_add (φ.integrable_inner (hDJ e I)) (φ.integrable_inner_fderiv (hJ I) e)] at h

/-- **Green's formula for a partial derivative.** Let `J ∈ W^{1,p}_loc(Ω)` and `S ∈ Lᵖ_loc(Ω)` be
Sobolev coefficients, with `S` weakly differentiable in the direction `e` with derivative
`∂_e S ∈ Lᵖ_loc(Ω)`, and let `ξ ∈ L^q_loc(Ω)` have a weak derivative `Dξ ∈ L^q_loc(Ω)`, for finite
`p` and `q` with `1/p + 1/q ≤ 1`. Then for every test function `φ`,

`∫ ⟪D* φ, ∂_e ξ⟫ = -∫ ⟪∂_e φ, ∂_s ξ + J ∂_t ξ + S ξ⟫ - ∫ ⟪φ, (∂_e J) ∂_t ξ + (∂_e S) ξ⟫`,

the weak form of `D (∂_e ξ) = ∂_e (D ξ) - (∂_e J) ∂_t ξ - (∂_e S) ξ`. No second derivative of `ξ`
or of `J` is assumed to exist. -/
theorem IsSobolevCRCoefficients.integral_inner_crFormalAdjoint_partial
    (hc : IsSobolevCRCoefficients p Ω J DJ S) (hpq : p⁻¹ + q⁻¹ ≤ 1) (hp : p ≠ ⊤) (hq : q ≠ ⊤)
    (hξ : HasWeakFDerivOn volume Ω ξ Dξ) (hξq : MemLpLoc q Ω ξ) (hDξq : MemLpLoc q Ω Dξ)
    {e : ℂ} (hS : HasWeakLineDerivOn volume Ω S S' e) (hS' : MemLpLoc p Ω S') (φ : 𝓓(Ω, V)) :
    ∫ z, ⟪crFormalAdjoint J DJ S φ z, Dξ z e⟫_ℝ =
      -(∫ z, ⟪fderiv ℝ (φ : ℂ → V) z e, Dξ z 1 + J z (Dξ z I) + S z (ξ z)⟫_ℝ) -
        ∫ z, ⟪(φ : ℂ → V) z, DJ z e (Dξ z I) + S' z (ξ z)⟫_ℝ := by
  have hloc := Ω.isOpen.isLocallyClosed
  have hq1 : 1 ≤ q := ENNReal.inv_le_one.1 (le_add_self.trans hpq)
  have : Fact (1 ≤ p) := ⟨ENNReal.inv_le_one.1 (le_self_add.trans hpq)⟩
  have : Fact (1 ≤ q) := ⟨hq1⟩
  have hD (c : ℂ) : MemLpLoc q Ω (fun z => Dξ z c) :=
    hDξq.clm_comp (ContinuousLinearMap.apply ℝ V c)
  -- Local integrability of every field paired with `φ` or its derivatives.
  have hD1 : LocallyIntegrableOn (fun z => Dξ z 1) Ω := (hD 1).locallyIntegrableOn hq1 hloc
  have hJ : LocallyIntegrableOn (fun z => J z (Dξ z I)) Ω :=
    hc.memLpLoc_coeff.locallyIntegrableOn_clm_apply (hD I) hpq hloc
  have hDJ : LocallyIntegrableOn (fun z => DJ z e (Dξ z I)) Ω :=
    (hc.memLpLoc_deriv_apply e).locallyIntegrableOn_clm_apply (hD I) hpq hloc
  have hSξ : LocallyIntegrableOn (fun z => S z (ξ z)) Ω :=
    hc.memLpLoc_zeroth.locallyIntegrableOn_clm_apply hξq hpq hloc
  have hSD : LocallyIntegrableOn (fun z => S z (Dξ z e)) Ω :=
    hc.memLpLoc_zeroth.locallyIntegrableOn_clm_apply (hD e) hpq hloc
  have hS'ξ : LocallyIntegrableOn (fun z => S' z (ξ z)) Ω :=
    hS'.locallyIntegrableOn_clm_apply hξq hpq hloc
  -- `∫ ⟪∂_s φ, ∂_e ξ⟫ = ∫ ⟪∂_e φ, ∂_s ξ⟫`.
  have F1 := hξ.integral_inner_fderiv_apply_comm φ 1 e
  -- `∫ ⟪∂_t (Jᵀ φ), ∂_e ξ⟫ = ∫ ⟪∂_e (Jᵀ φ), ∂_t ξ⟫`.
  have F2 := integral_inner_coeff_partial_comm hc hpq hp hq hξ hDξq φ e
  -- `∫ ⟪∂_e φ, S ξ⟫ = -∫ ⟪φ, (∂_e S) ξ + S ∂_e ξ⟫`, by the weak Leibniz rule for `S ξ`.
  have hSξw : HasWeakLineDerivOn volume Ω (fun z => S z (ξ z))
      (fun z => S' z (ξ z) + S z (Dξ z e)) e := by
    simpa using hS.bilin_of_memLp (ContinuousLinearMap.id ℝ (V →L[ℝ] V)) hp hp hq hq hpq hpq hpq
      (hξ.hasWeakLineDerivOn e) (fun K hK hKΩ => memLpLoc_iff.1 hc.memLpLoc_zeroth K hKΩ hK)
      (fun K hK hKΩ => memLpLoc_iff.1 hS' K hKΩ hK) (fun K hK hKΩ => memLpLoc_iff.1 hξq K hKΩ hK)
      (fun K hK hKΩ => memLpLoc_iff.1 (hD e) K hKΩ hK)
  have F3 := hSξw.integral_inner_lineDeriv_eq_neg φ
  simp only [TestFunction.lineDeriv_eq_fderiv, inner_add_right] at F3
  rw [integral_add (φ.integrable_inner hS'ξ) (φ.integrable_inner hSD)] at F3
  -- Expand both sides into integrals of single pairings and compare.
  rw [hc.integral_inner_crFormalAdjoint_eq_terms hpq (hD e) φ]
  simp only [inner_add_right]
  rw [integral_add ?_ (φ.integrable_inner_fderiv hSξ e),
    integral_add (φ.integrable_inner_fderiv hD1 e) (φ.integrable_inner_fderiv hJ e),
    integral_add (φ.integrable_inner hDJ) (φ.integrable_inner hS'ξ)]
  · linarith
  · exact (φ.integrable_inner_fderiv hD1 e).add (φ.integrable_inner_fderiv hJ e)

/-! ### The differentiated equation -/

/-- **Partial derivatives of solutions solve the differentiated equation.** Let `J ∈ W^{1,p}_loc(Ω)`
and `S ∈ Lᵖ_loc(Ω)` be Sobolev coefficients, and let `ξ ∈ L^q_loc(Ω)` have a weak derivative
`Dξ ∈ L^q_loc(Ω)`, for finite `p` and `q` with `1/p + 1/q ≤ 1`. Suppose that
`∂_s ξ + J ∂_t ξ + S ξ = η` almost everywhere on `Ω`, and that `S` and `η` have weak derivatives
`∂_e S ∈ Lᵖ_loc(Ω)` and `∂_e η` in a direction `e`. Then `∂_e ξ` is a weak solution of

`∂_s (∂_e ξ) + J ∂_t (∂_e ξ) + S ∂_e ξ = ∂_e η - (∂_e J) ∂_t ξ - (∂_e S) ξ`

in the sense of `TauCeti.IsWeakCRSolution`. For `e = 1` and `e = i` these are the two components
of the differentiated system for `(∂_s ξ, ∂_t ξ)`, with zeroth-order coefficient
`TauCeti.differentiatedCRCoefficient`. -/
theorem IsSobolevCRCoefficients.isWeakCRSolution_partial
    (hc : IsSobolevCRCoefficients p Ω J DJ S) (hpq : p⁻¹ + q⁻¹ ≤ 1) (hp : p ≠ ⊤) (hq : q ≠ ⊤)
    (hξ : HasWeakFDerivOn volume Ω ξ Dξ) (hξq : MemLpLoc q Ω ξ) (hDξq : MemLpLoc q Ω Dξ)
    (heq : ∀ᵐ z ∂volume.restrict Ω, Dξ z 1 + J z (Dξ z I) + S z (ξ z) = η z)
    {e : ℂ} (hS : HasWeakLineDerivOn volume Ω S S' e) (hS' : MemLpLoc p Ω S')
    (hη : HasWeakLineDerivOn volume Ω η η' e) :
    IsWeakCRSolution q Ω J DJ S (fun z => Dξ z e)
      (fun z => η' z - DJ z e (Dξ z I) - S' z (ξ z)) := by
  have hloc := Ω.isOpen.isLocallyClosed
  have hD (c : ℂ) : MemLpLoc q Ω (fun z => Dξ z c) :=
    hDξq.clm_comp (ContinuousLinearMap.apply ℝ V c)
  have hDJ : LocallyIntegrableOn (fun z => DJ z e (Dξ z I)) Ω :=
    (hc.memLpLoc_deriv_apply e).locallyIntegrableOn_clm_apply (hD I) hpq hloc
  have hS'ξ : LocallyIntegrableOn (fun z => S' z (ξ z)) Ω :=
    hS'.locallyIntegrableOn_clm_apply hξq hpq hloc
  refine isWeakCRSolution_iff.2 ⟨hD e, (hη.locallyIntegrableOn_deriv.sub hDJ).sub hS'ξ,
    fun φ => ⟨hc.integrable_inner_crFormalAdjoint hpq (hD e) φ, ?_⟩⟩
  -- Replace `∂_s ξ + J ∂_t ξ + S ξ` by `η` and move the derivative from `φ` to `η`.
  have hφη : ∫ z, ⟪fderiv ℝ (φ : ℂ → V) z e, Dξ z 1 + J z (Dξ z I) + S z (ξ z)⟫_ℝ =
      ∫ z, ⟪fderiv ℝ (φ : ℂ → V) z e, η z⟫_ℝ := by
    refine integral_congr_ae ?_
    filter_upwards [ae_imp_of_ae_restrict heq] with z hz
    by_cases hzΩ : z ∈ (Ω : Set ℂ)
    · rw [hz hzΩ]
    · have hz' : z ∉ tsupport (φ : ℂ → V) := fun h' => hzΩ (φ.tsupport_subset h')
      simp [fderiv_of_notMem_tsupport ℝ hz']
  have hηw := hη.integral_inner_lineDeriv_eq_neg φ
  simp only [TestFunction.lineDeriv_eq_fderiv] at hηw
  rw [hc.integral_inner_crFormalAdjoint_partial hpq hp hq hξ hξq hDξq hS hS' φ, hφη, hηw]
  simp only [inner_sub_right, inner_add_right]
  rw [integral_sub ?_ (φ.integrable_inner hS'ξ),
    integral_sub (φ.integrable_inner hη.locallyIntegrableOn_deriv) (φ.integrable_inner hDJ),
    integral_add (φ.integrable_inner hDJ) (φ.integrable_inner hS'ξ)]
  · ring
  · exact (φ.integrable_inner hη.locallyIntegrableOn_deriv).sub (φ.integrable_inner hDJ)

end TauCeti
