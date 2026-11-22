/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.Adjoint
public import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.Interior
public import TauCeti.Analysis.Sobolev.Local.ChangeOfVariables
import Mathlib.Analysis.Normed.Affine.MazurUlam

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
  (`TauCeti.memWkpLoc_one_of_forall_integral_inner_eq_zero`), and more generally for Sobolev
  coefficients `J ∈ W^{1,p}_loc`, `S ∈ Lᵖ_loc` with `p > 2`
  (`TauCeti.IsSobolevCRCoefficients.memWkpLoc_one_of_forall_integral_inner_eq_zero`), where
  `r ≤ p` is required;
* for a covector field `η : Ω → V →L[ℝ] ℝ` on a finite-dimensional normed space, paired with
  `D φ` by `∫ η(D φ)` (`TauCeti.memWkpLoc_one_of_forall_integral_apply_eq_zero`). This form needs
  no inner product on `V`.

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
`S ∈ Lᵖ_loc`), with `p > 2` and `J² = -1` on `Ω`. If a locally `L^q` field `v` with
`1/p + 1/q < 1` satisfies `∫ ⟪∂_s φ + J ∂_t φ + S φ, v⟫ = 0` for every test function `φ` on `Ω`,
then `v ∈ W^{1,r}_loc(Ω)` for every finite `r > 1` with `r ≤ p`. -/
theorem IsSobolevCRCoefficients.memWkpLoc_one_of_forall_integral_inner_eq_zero {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] {Ω : Opens ℂ}
    {J S : ℂ → V →L[ℝ] V} {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V} {p q r : ℝ≥0∞}
    (hc : IsSobolevCRCoefficients p Ω J DJ S) (hp : 2 < p) (hJ2 : ∀ z ∈ Ω, J z * J z = -1)
    (hpq : p⁻¹ + q⁻¹ < 1) {v : ℂ → V} (hv : MemLpLoc q Ω v)
    (h : ∀ φ : 𝓓(Ω, V), ∫ z, ⟪fderiv ℝ (φ : ℂ → V) z 1 + J z (fderiv ℝ (φ : ℂ → V) z I) +
      S z ((φ : ℂ → V) z), v z⟫_ℝ = 0)
    (hr : 1 < r) (hr_top : r ≠ ⊤) (hrp : r ≤ p) : MemWkpLoc r Ω 1 v := by
  -- After the reflection `ρ z = -conj z`, `v` solves a homogeneous Cauchy–Riemann equation.
  set Ω' : Opens ℂ := ⟨(fun z ↦ -conj z) ⁻¹' Ω, Ω.isOpen.preimage (by fun_prop)⟩
  have hweak := (hc.forall_integral_inner_eq_zero_iff hpq.le (Ω' := Ω') (fun _ ↦ Iff.rfl) hv).1 h
  have hJ2' : ∀ᵐ z ∂volume.restrict Ω',
      crReflectedAdjointCoeff J z * crReflectedAdjointCoeff J z = -1 :=
    ae_restrict_of_forall_mem Ω'.isOpen.measurableSet fun z hz ↦
      (crReflectedAdjointCoeff_mul_self_eq_neg_one_iff z).2 (hJ2 _ hz)
  have hW := hweak.memWkpLoc_one_of_le (hc.crReflectedAdjoint fun _ hz ↦ hz) hp hJ2' hpq
    hr hr_top hrp continuousOn_const.memLpLoc
  -- Reflecting back: `ρ` is the real-linear equivalence `A`, and `ρ ∘ ρ = id`.
  set A : ℂ ≃L[ℝ] ℂ := conjCLE.trans (ContinuousLinearEquiv.neg ℝ)
  have hA (z : ℂ) : A z + 0 = -conj z := by simp [A]
  have hmem (z : ℂ) : z ∈ (Ω' : Set ℂ) ↔ -conj z ∈ (Ω : Set ℂ) := Iff.rfl
  have hmaps : MapsTo (fun z ↦ A z + 0) Ω Ω' := fun z hz ↦
    (hmem _).2 (by simpa only [hA, map_neg, conj_conj, neg_neg] using hz)
  simpa [hA] using hW.comp_continuousLinearEquiv_add A 0 hmaps

/-- **The annihilator of a real Cauchy–Riemann operator is `W^{1,r}_loc`.** Let `Ω ⊆ ℂ` be open,
`V` a finite-dimensional real inner product space, `J` a `C¹` field of complex structures on `V`
and `S` a continuous field of endomorphisms over `Ω`. If a locally `L^q` field `v` (`q > 1`)
satisfies `∫ ⟪∂_s φ + J ∂_t φ + S φ, v⟫ = 0` for every test function `φ` on `Ω`, then
`v ∈ W^{1,r}_loc(Ω)` for every finite `r > 1`. -/
theorem memWkpLoc_one_of_forall_integral_inner_eq_zero {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] {Ω : Opens ℂ} {J S : ℂ → V →L[ℝ] V}
    (hJ : ContDiffOn ℝ 1 J Ω) (hS : ContinuousOn S Ω) (hJ2 : ∀ z ∈ Ω, J z * J z = -1)
    {v : ℂ → V} {q r : ℝ≥0∞} (hq : 1 < q) (hv : MemLpLoc q Ω v)
    (h : ∀ φ : 𝓓(Ω, V), ∫ z, ⟪fderiv ℝ (φ : ℂ → V) z 1 + J z (fderiv ℝ (φ : ℂ → V) z I) +
      S z ((φ : ℂ → V) z), v z⟫_ℝ = 0)
    (hr : 1 < r) (hr_top : r ≠ ⊤) : MemWkpLoc r Ω 1 v := by
  -- Continuous coefficients are Sobolev coefficients for the exponent `∞`.
  have hJ' : ContinuousOn (fderiv ℝ J) Ω := hJ.continuousOn_fderiv_of_isOpen Ω.isOpen le_rfl
  have hc : IsSobolevCRCoefficients ⊤ Ω J (fderiv ℝ J) S :=
    ⟨hasWeakFDerivOn_of_differentiableOn (hJ'.locallyIntegrableOn Ω.isOpen.measurableSet)
      fun z hz ↦ (hJ.differentiableOn one_ne_zero z hz).differentiableAt (Ω.isOpen.mem_nhds hz),
      hJ.continuousOn.memLpLoc, hJ'.memLpLoc, hS.memLpLoc⟩
  exact hc.memWkpLoc_one_of_forall_integral_inner_eq_zero (by simp) hJ2
    (by simpa using ENNReal.inv_lt_one.2 hq) hv h hr hr_top le_top

/-- **The annihilator of a real Cauchy–Riemann operator, for covector fields.** Let `Ω ⊆ ℂ` be
open, `V` a finite-dimensional real normed space, `J` a `C¹` field of complex structures on `V`
and `S` a continuous field of endomorphisms over `Ω`. If a locally `L^q` covector field `η`
(`q > 1`) satisfies `∫ η (∂_s φ + J ∂_t φ + S φ) = 0` for every test function `φ` on `Ω`, then
`η ∈ W^{1,r}_loc(Ω)` for every finite `r > 1`. -/
theorem memWkpLoc_one_of_forall_integral_apply_eq_zero {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] {Ω : Opens ℂ} {J S : ℂ → V →L[ℝ] V}
    (hJ : ContDiffOn ℝ 1 J Ω) (hS : ContinuousOn S Ω) (hJ2 : ∀ z ∈ Ω, J z * J z = -1)
    {η : ℂ → V →L[ℝ] ℝ} {q r : ℝ≥0∞} (hq : 1 < q) (hη : MemLpLoc q Ω η)
    (h : ∀ φ : 𝓓(Ω, V), ∫ z, η z (fderiv ℝ (φ : ℂ → V) z 1 + J z (fderiv ℝ (φ : ℂ → V) z I) +
      S z ((φ : ℂ → V) z)) = 0)
    (hr : 1 < r) (hr_top : r ≠ ⊤) : MemWkpLoc r Ω 1 η := by
  -- Transport everything to a Euclidean model `W` of `V`, and covectors to vectors in `W`.
  let L : V ≃L[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ V)) :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  let P := L.arrowCongr L
  let Q := L.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)
  -- The Riesz map `InnerProductSpace.toDual` is conjugate-linear, hence real-linear.
  let T : StrongDual ℝ (EuclideanSpace ℝ (Fin (finrank ℝ V))) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (finrank ℝ V)) :=
    ((InnerProductSpace.toDual ℝ _).toIsometryEquiv.toRealLinearIsometryEquivOfMapZero
      (map_zero (InnerProductSpace.toDual ℝ _))).symm.toContinuousLinearEquiv
  have hT (f : StrongDual ℝ (EuclideanSpace ℝ (Fin (finrank ℝ V))))
      (x : EuclideanSpace ℝ (Fin (finrank ℝ V))) : ⟪x, T f⟫_ℝ = f x := by
    -- `T` is `toDual⁻¹`, regarded as a real-linear equivalence.
    have hTf : T f = (InnerProductSpace.toDual ℝ _).symm f := rfl
    rw [real_inner_comm, hTf, InnerProductSpace.toDual_symm_apply]
  have hP2 (z : ℂ) (hz : z ∈ Ω) : P (J z) * P (J z) = -1 := by
    refine ContinuousLinearMap.ext fun x ↦ ?_
    simpa [P] using congrArg L (congrArg (fun A : V →L[ℝ] V ↦ A (L.symm x)) (hJ2 z hz))
  have hv := memWkpLoc_one_of_forall_integral_inner_eq_zero (S := fun z ↦ P (S z))
    (P.contDiff.comp_contDiffOn hJ) (P.continuous.comp_continuousOn hS) hP2 hq
    ((hη.clm_comp Q.toContinuousLinearMap).clm_comp T.toContinuousLinearMap) (fun φ ↦ ?_) hr hr_top
  · simpa using (hv.clm_comp T.symm.toContinuousLinearMap).clm_comp Q.symm.toContinuousLinearMap
  · -- The test function `L⁻¹ ∘ φ` on `V` gives the same integrand.
    rw [← h (TestFunction.postcompCLM (L.symm : _ →L[ℝ] V) φ)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z ↦ ?_)
    simp [hT, P, Q, L.symm.comp_fderiv]

end TauCeti
