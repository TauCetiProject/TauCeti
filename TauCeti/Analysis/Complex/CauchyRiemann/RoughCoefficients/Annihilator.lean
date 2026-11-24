/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.Adjoint
public import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.Interior
public import TauCeti.Analysis.Sobolev.Local.ChangeOfVariables
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

/-!
# Sobolev regularity of the annihilator of a real Cauchy–Riemann operator

Let `Ω ⊆ ℂ` be open, write `z = s + i t`, and let `D φ = ∂_s φ + J ∂_t φ + S φ` be a real
Cauchy–Riemann operator on maps `φ : Ω → V` into a finite-dimensional real vector space, with a
`C¹` complex structure `J` (`J² = -1`) and a continuous zeroth-order coefficient `S`. A field `η`
annihilating `D φ` for every test function `φ` is a weak solution of the adjoint equation
`D* η = 0`. In Fredholm theory such fields are the elements of the cokernel of a Sobolev
realization of `D`, and a priori they are only locally `L^q`. This file proves that they are in
`W^{1,r}_loc(Ω)` for every finite `r > 1`, in two forms:

* for a vector field `η` in a real inner product space, paired with `D φ` by `∫ ⟪D φ, η⟫`
  (`TauCeti.memWkpLoc_one_of_forall_integral_inner_cauchyRiemann_eq_zero`), and more generally
  for Sobolev coefficients `J ∈ W^{1,p}_loc`, `S ∈ Lᵖ_loc` with `p > 2` and `J² = -1` a.e.
  (`TauCeti.IsSobolevCRCoefficients.memWkpLoc_one_of_forall_integral_inner_eq_zero`), where
  `r ≤ p` is required;
* for a covector field `η : Ω → V →L[ℝ] ℝ` on a finite-dimensional normed space, paired with
  `D φ` by `∫ η(D φ)` (`TauCeti.memWkpLoc_one_of_forall_integral_apply_cauchyRiemann_eq_zero`).
  This form needs no inner product on `V`.

After the reflection `ρ(z) = -conj z`, an annihilator of `D` is a weak solution of a homogeneous
real Cauchy–Riemann equation whose leading coefficient again squares to `-1`
(`TauCeti.IsSobolevCRCoefficients.forall_integral_inner_eq_zero_iff`,
`TauCeti.crReflectedAdjointCoeff_mul_self_eq_neg_one_iff`), and interior regularity
(`TauCeti.IsWeakCRSolution.memWkpLoc_one_of_le`) applies to it. Continuous coefficients are
locally bounded, so they are Sobolev coefficients for the exponent `∞` and every `q > 1` is
allowed. The covector form follows from the vector form in a Euclidean model of `V`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.4 (Proposition B.4.9) and Section 3.1 (the formal adjoint of a real Cauchy–Riemann
  operator).
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace Complex Set Module
open scoped InnerProductSpace Distributions ENNReal ComplexConjugate

namespace TauCeti

/-- **The annihilator of a real Cauchy–Riemann operator with Sobolev coefficients is
`W^{1,r}_loc`.** Let `Ω ⊆ ℂ` be open, `V` a finite-dimensional real inner product space, and
`(J, DJ, S)` Sobolev coefficients on `Ω` (`J ∈ W^{1,p}_loc` with weak derivative `DJ`,
`S ∈ Lᵖ_loc`), with `p > 2` and `J² = -1` almost everywhere on `Ω`. If a locally `L^q` field
`v` with `1/p + 1/q < 1` satisfies `∫ ⟪∂_s φ + J ∂_t φ + S φ, v⟫ = 0` for every test function
`φ` on `Ω`, then `v ∈ W^{1,r}_loc(Ω)` for every finite `r > 1` with `r ≤ p`. -/
theorem IsSobolevCRCoefficients.memWkpLoc_one_of_forall_integral_inner_eq_zero {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] {Ω : Opens ℂ}
    {J S : ℂ → V →L[ℝ] V} {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V} {p q r : ℝ≥0∞}
    (hc : IsSobolevCRCoefficients p Ω J DJ S) (hp : 2 < p)
    (hJ2 : ∀ᵐ z ∂volume.restrict Ω, J z * J z = -1) (hpq : p⁻¹ + q⁻¹ < 1) {v : ℂ → V}
    (hv : MemLpLoc q Ω v)
    (h : ∀ φ : 𝓓(Ω, V), ∫ z, ⟪fderiv ℝ (φ : ℂ → V) z 1 + J z (fderiv ℝ (φ : ℂ → V) z I) +
      S z ((φ : ℂ → V) z), v z⟫_ℝ = 0)
    (hr : 1 < r) (hr_top : r ≠ ⊤) (hrp : r ≤ p) : MemWkpLoc r Ω 1 v := by
  -- After the reflection `ρ z = -conj z`, `v` solves a homogeneous Cauchy–Riemann equation.
  set Ω' : Opens ℂ := ⟨(fun z ↦ -conj z) ⁻¹' Ω, Ω.isOpen.preimage (by fun_prop)⟩
  have hweak := (hc.forall_integral_inner_eq_zero_iff hpq.le (Ω' := Ω') (fun _ ↦ Iff.rfl) hv).1 h
  -- `ρ` preserves Lebesgue measure, so `J² = -1` a.e. on `Ω` gives `J'² = -1` a.e. on `Ω'`.
  have hρ : MeasurePreserving (fun z : ℂ ↦ -conj z) :=
    (conjLIE.trans (LinearIsometryEquiv.neg ℝ)).measurePreserving
  have hJ2' : ∀ᵐ z ∂volume.restrict Ω',
      crReflectedAdjointCoeff J z * crReflectedAdjointCoeff J z = -1 := by
    rw [ae_restrict_iff' Ω'.isOpen.measurableSet]
    filter_upwards [hρ.quasiMeasurePreserving.ae
      ((ae_restrict_iff' Ω.isOpen.measurableSet).1 hJ2)] with z hz hzΩ'
    exact (crReflectedAdjointCoeff_mul_self_eq_neg_one_iff z).2 (hz hzΩ')
  have hW := hweak.memWkpLoc_one_of_le (hc.crReflectedAdjoint fun _ hz ↦ hz) hp hJ2' hpq
    hr hr_top hrp continuousOn_const.memLpLoc
  -- Reflecting back along `ρ`, using `ρ ∘ ρ = id`.
  simpa using hW.comp_neg_conj fun z hz ↦ by simpa [Ω'] using hz

/-- **The annihilator of a real Cauchy–Riemann operator is `W^{1,r}_loc`.** Let `Ω ⊆ ℂ` be open,
`V` a finite-dimensional real inner product space, `J` a `C¹` field of complex structures on `V`
and `S` a continuous field of endomorphisms over `Ω`. If a locally `L^q` field `v` (`q > 1`)
satisfies `∫ ⟪∂_s φ + J ∂_t φ + S φ, v⟫ = 0` for every test function `φ` on `Ω`, then
`v ∈ W^{1,r}_loc(Ω)` for every finite `r > 1`. -/
theorem memWkpLoc_one_of_forall_integral_inner_cauchyRiemann_eq_zero {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] {Ω : Opens ℂ}
    {J S : ℂ → V →L[ℝ] V} (hJ : ContDiffOn ℝ 1 J Ω) (hS : ContinuousOn S Ω)
    (hJ2 : ∀ z ∈ Ω, J z * J z = -1)
    {v : ℂ → V} {q r : ℝ≥0∞} (hq : 1 < q) (hv : MemLpLoc q Ω v)
    (h : ∀ φ : 𝓓(Ω, V), ∫ z, ⟪fderiv ℝ (φ : ℂ → V) z 1 + J z (fderiv ℝ (φ : ℂ → V) z I) +
      S z ((φ : ℂ → V) z), v z⟫_ℝ = 0)
    (hr : 1 < r) (hr_top : r ≠ ⊤) : MemWkpLoc r Ω 1 v := by
  -- Continuous coefficients are Sobolev coefficients for the exponent `∞`.
  exact (IsSobolevCRCoefficients.of_contDiffOn hJ hS ⊤)
    |>.memWkpLoc_one_of_forall_integral_inner_eq_zero (by simp)
    (ae_restrict_of_forall_mem Ω.isOpen.measurableSet hJ2)
    (by simpa using ENNReal.inv_lt_one.2 hq) hv h hr hr_top le_top

/-- **The annihilator of a real Cauchy–Riemann operator, for covector fields.** Let `Ω ⊆ ℂ` be
open, `V` a finite-dimensional real normed space, `J` a `C¹` field of complex structures on `V`
and `S` a continuous field of endomorphisms over `Ω`. If a locally `L^q` covector field `η`
(`q > 1`) satisfies `∫ η (∂_s φ + J ∂_t φ + S φ) = 0` for every test function `φ` on `Ω`, then
`η ∈ W^{1,r}_loc(Ω)` for every finite `r > 1`. -/
theorem memWkpLoc_one_of_forall_integral_apply_cauchyRiemann_eq_zero {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {Ω : Opens ℂ}
    {J S : ℂ → V →L[ℝ] V} (hJ : ContDiffOn ℝ 1 J Ω) (hS : ContinuousOn S Ω)
    (hJ2 : ∀ z ∈ Ω, J z * J z = -1)
    {η : ℂ → V →L[ℝ] ℝ} {q r : ℝ≥0∞} (hq : 1 < q) (hη : MemLpLoc q Ω η)
    (h : ∀ φ : 𝓓(Ω, V), ∫ z, η z (fderiv ℝ (φ : ℂ → V) z 1 + J z (fderiv ℝ (φ : ℂ → V) z I) +
      S z ((φ : ℂ → V) z)) = 0)
    (hr : 1 < r) (hr_top : r ≠ ⊤) : MemWkpLoc r Ω 1 η := by
  -- Transport everything to a Euclidean model `W` of `V`, and covectors to vectors in `W`.
  let L : V ≃L[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ V)) := toEuclidean
  let P := L.arrowCongr L
  let Q := L.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)
  -- Over `ℝ`, the inverse Riesz map `InnerProductSpace.toDual` is a real-linear equivalence.
  let T : StrongDual ℝ (EuclideanSpace ℝ (Fin (finrank ℝ V))) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (finrank ℝ V)) :=
    (InnerProductSpace.toDual ℝ _).symm.toContinuousLinearEquiv
  have hT (f : StrongDual ℝ (EuclideanSpace ℝ (Fin (finrank ℝ V))))
      (x : EuclideanSpace ℝ (Fin (finrank ℝ V))) : ⟪x, T f⟫_ℝ = f x := by
    rw [real_inner_comm]
    exact InnerProductSpace.toDual_symm_apply
  have hP2 (z : ℂ) (hz : z ∈ Ω) : P (J z) * P (J z) = -1 := by
    refine ContinuousLinearMap.ext fun x ↦ ?_
    simpa [P] using congrArg L (congrArg (fun A : V →L[ℝ] V ↦ A (L.symm x)) (hJ2 z hz))
  have hv := memWkpLoc_one_of_forall_integral_inner_cauchyRiemann_eq_zero (S := fun z ↦ P (S z))
    (P.contDiff.comp_contDiffOn hJ) (P.continuous.comp_continuousOn hS) hP2 hq
    ((hη.clm_comp Q.toContinuousLinearMap).clm_comp T.toContinuousLinearMap) (fun φ ↦ ?_) hr hr_top
  · simpa using (hv.clm_comp T.symm.toContinuousLinearMap).clm_comp Q.symm.toContinuousLinearMap
  · -- The test function `L⁻¹ ∘ φ` on `V` gives the same integrand.
    rw [← h (TestFunction.postcompCLM (L.symm : _ →L[ℝ] V) φ)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z ↦ ?_)
    simp [hT, P, Q, L.symm.comp_fderiv]

end TauCeti
