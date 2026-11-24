/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.Adjoint
public import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.HigherOrder
public import TauCeti.Analysis.Sobolev.Local.ChangeOfVariables
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

/-!
# Sobolev regularity of the annihilator of a real Cauchy–Riemann operator

Let `Ω ⊆ ℂ` be open, write `z = s + i t`, and let `D φ = ∂_s φ + J ∂_t φ + S φ` be a real
Cauchy–Riemann operator on maps `φ : Ω → V` into a finite-dimensional real vector space, with a
complex structure `J` (`J² = -1`) and a zeroth-order coefficient `S`. A field `η` annihilating
`D φ` for every test function `φ` is a weak solution of the adjoint equation `D* η = 0`. In
Fredholm theory such fields are the elements of the cokernel of a Sobolev realization of `D`, and
a priori they are only locally `L^q`. This file proves that they gain as many derivatives as the
coefficients allow: for `J` of class `Cᵏ⁺¹` and `S` of class `Cᵏ` they are in `W^{k+1,r}_loc(Ω)`
for every finite `r`. In particular, for `C²` coefficients `J` and `C¹` coefficients `S` an
annihilator is in `W^{2,r}_loc` for every finite `r`, so by Morrey's embedding it agrees almost
everywhere with a `C¹` field (`TauCeti.MemWkpLoc.contDiffOn_one_of_continuousOn`): this is the
regularity that unique continuation for `D*` requires. The results come in three forms:

* for Sobolev coefficients `J ∈ W^{1,p}_loc`, `S ∈ Lᵖ_loc` with `p > 2` and `J² = -1` a.e.: an
  annihilator is in `W^{1,r}_loc` for every finite `r > 1` with `r ≤ p`
  (`TauCeti.IsSobolevCRCoefficients.memWkpLoc_one_of_forall_integral_inner_eq_zero`), and in
  `W^{k+1,q}_loc` when moreover `J ∈ W^{k+1,p}_loc` and `S ∈ W^{k,p}_loc`, for its own exponent
  `q ≤ p` (`TauCeti.IsSobolevCRCoefficients.memWkpLoc_succ_of_forall_integral_inner_eq_zero`);
* for a vector field `η` in a real inner product space, paired with `D φ` by `∫ ⟪D φ, η⟫`, and
  smooth coefficients (`TauCeti.memWkpLoc_succ_of_forall_integral_inner_cauchyRiemann_eq_zero`);
* for a covector field `η : Ω → V →L[ℝ] ℝ` on a finite-dimensional normed space, paired with
  `D φ` by `∫ η(D φ)`, and smooth coefficients
  (`TauCeti.memWkpLoc_succ_of_forall_integral_apply_cauchyRiemann_eq_zero`). This form needs no
  inner product on `V`.

After the reflection `ρ(z) = -conj z`, an annihilator of `D` is a weak solution of a homogeneous
real Cauchy–Riemann equation whose leading coefficient again squares to `-1`
(`TauCeti.IsSobolevCRCoefficients.forall_integral_inner_eq_zero_iff`,
`TauCeti.crReflectedAdjointCoeff_mul_self_eq_neg_one_iff`). Interior regularity applies to it: at
order one with the exponent ladder of `TauCeti.IsWeakCRSolution.memWkpLoc_one_of_le`, and at
higher order by `TauCeti.IsWeakCRSolution.memWkpLoc_succ`. The reflected coefficients
`J' = -(J ∘ ρ)ᵀ` and `S' = (S ∘ ρ)ᵀ - (∂_t J ∘ ρ)ᵀ` lose one derivative of `J`, which is why `J`
needs one derivative more than `S`. Continuous coefficients are locally bounded, so at order one
they are Sobolev coefficients for the exponent `∞` and every `q > 1` is allowed; this first puts
an annihilator in every `L^r_loc`, after which smooth coefficients are Sobolev coefficients of
every finite exponent. The covector form follows from the vector form in a Euclidean model of `V`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.4 (Proposition B.4.9) and Section 3.1 (the formal adjoint of a real Cauchy–Riemann
  operator).
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace Complex Set Module
open scoped InnerProductSpace Distributions ENNReal NNReal ComplexConjugate

namespace TauCeti

/-- After the reflection `ρ z = -conj z`, an annihilator `v` of `∂_s + J ∂_t + S` on `Ω` is a weak
solution of the homogeneous reflected equation on `Ω' = ρ⁻¹ Ω`, whose leading coefficient squares
to `-1` almost everywhere on `Ω'`. -/
private theorem IsSobolevCRCoefficients.isWeakCRSolution_of_forall_integral_inner_eq_zero
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    {Ω Ω' : Opens ℂ} {J S : ℂ → V →L[ℝ] V} {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V} {p q : ℝ≥0∞}
    (hc : IsSobolevCRCoefficients p Ω J DJ S) (hJ2 : ∀ᵐ z ∂volume.restrict Ω, J z * J z = -1)
    (hpq : p⁻¹ + q⁻¹ ≤ 1) (hΩ : ∀ z, z ∈ Ω' ↔ -conj z ∈ Ω) {v : ℂ → V} (hv : MemLpLoc q Ω v)
    (h : ∀ φ : 𝓓(Ω, V), ∫ z, ⟪fderiv ℝ (φ : ℂ → V) z 1 + J z (fderiv ℝ (φ : ℂ → V) z I) +
      S z ((φ : ℂ → V) z), v z⟫_ℝ = 0) :
    IsWeakCRSolution q Ω' (crReflectedAdjointCoeff J) (crReflectedAdjointDeriv DJ)
        (crReflectedAdjointZeroth DJ S) (fun z ↦ v (-conj z)) 0 ∧
      ∀ᵐ z ∂volume.restrict Ω', crReflectedAdjointCoeff J z * crReflectedAdjointCoeff J z = -1 := by
  refine ⟨(hc.forall_integral_inner_eq_zero_iff hpq hΩ hv).1 h, ?_⟩
  -- `ρ` preserves Lebesgue measure, so `J² = -1` a.e. on `Ω` gives `J'² = -1` a.e. on `Ω'`.
  have hρ : MeasurePreserving (fun z : ℂ ↦ -conj z) :=
    (conjLIE.trans (LinearIsometryEquiv.neg ℝ)).measurePreserving
  rw [ae_restrict_iff' Ω'.isOpen.measurableSet]
  filter_upwards [hρ.quasiMeasurePreserving.ae
    ((ae_restrict_iff' Ω.isOpen.measurableSet).1 hJ2)] with z hz hzΩ'
  exact (crReflectedAdjointCoeff_mul_self_eq_neg_one_iff z).2 (hz ((hΩ z).1 hzΩ'))

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
  obtain ⟨hweak, hJ2'⟩ := hc.isWeakCRSolution_of_forall_integral_inner_eq_zero hJ2 hpq.le
    (Ω' := Ω') (fun _ ↦ Iff.rfl) hv h
  have hW := hweak.memWkpLoc_one_of_le (hc.crReflectedAdjoint fun _ hz ↦ hz) hp hJ2' hpq
    hr hr_top hrp continuousOn_const.memLpLoc
  -- Reflecting back along `ρ`, using `ρ ∘ ρ = id`.
  simpa using hW.comp_neg_conj fun z hz ↦ by simpa [Ω'] using hz

/-- **Higher regularity of the annihilator of a real Cauchy–Riemann operator with Sobolev
coefficients.** Let `Ω ⊆ ℂ` be open, `V` a finite-dimensional real inner product space, and
`(J, DJ, S)` Sobolev coefficients on `Ω` with finite `p > 2` and `J² = -1` almost everywhere on
`Ω`. If moreover `J ∈ W^{k+1,p}_loc` and `S ∈ W^{k,p}_loc`, then a locally `L^q` field `v` with
`1/p + 1/q < 1` and `q ≤ p` satisfying `∫ ⟪∂_s φ + J ∂_t φ + S φ, v⟫ = 0` for every test function
`φ` on `Ω` is in `W^{k+1,q}_loc(Ω)`. For `k = 0` this is the case `r = q` of
`TauCeti.IsSobolevCRCoefficients.memWkpLoc_one_of_forall_integral_inner_eq_zero`. -/
theorem IsSobolevCRCoefficients.memWkpLoc_succ_of_forall_integral_inner_eq_zero {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] {Ω : Opens ℂ}
    {J S : ℂ → V →L[ℝ] V} {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V} {p q : ℝ≥0} {k : ℕ}
    (hc : IsSobolevCRCoefficients p Ω J DJ S) (hp : 2 < p)
    (hJ2 : ∀ᵐ z ∂volume.restrict Ω, J z * J z = -1) (hpq : (p : ℝ≥0∞)⁻¹ + (q : ℝ≥0∞)⁻¹ < 1)
    (hqp : q ≤ p) (hJ : MemWkpLoc p Ω (k + 1) J) (hS : MemWkpLoc p Ω k S) {v : ℂ → V}
    (hv : MemLpLoc q Ω v)
    (h : ∀ φ : 𝓓(Ω, V), ∫ z, ⟪fderiv ℝ (φ : ℂ → V) z 1 + J z (fderiv ℝ (φ : ℂ → V) z I) +
      S z ((φ : ℂ → V) z), v z⟫_ℝ = 0) :
    MemWkpLoc q Ω (k + 1) v := by
  -- After the reflection `ρ z = -conj z`, `v` solves a homogeneous Cauchy–Riemann equation.
  set Ω' : Opens ℂ := ⟨(fun z ↦ -conj z) ⁻¹' Ω, Ω.isOpen.preimage (by fun_prop)⟩
  have hρ : MapsTo (fun z : ℂ ↦ -conj z) Ω' Ω := fun _ hz ↦ hz
  obtain ⟨hweak, hJ2'⟩ := hc.isWeakCRSolution_of_forall_integral_inner_eq_zero hJ2 hpq.le
    (Ω' := Ω') (fun _ ↦ Iff.rfl) hv h
  -- The reflected coefficients `J'` and `S'` are in `W^{k,p}_loc`; `S'` involves `DJ`.
  have hDJ : MemWkpLoc p Ω k DJ := hJ.memWkpLoc_of_hasWeakFDerivOn hc.hasWeakFDerivOn
  have hW := hweak.memWkpLoc_succ (hc.crReflectedAdjoint hρ) hp hJ2' hpq hqp
    (hJ.of_succ.crReflectedAdjointCoeff hρ) (hDJ.crReflectedAdjointZeroth hS hρ)
    memWkpLoc_zero_fun
  -- Reflecting back along `ρ`, using `ρ ∘ ρ = id`.
  simpa using hW.comp_neg_conj fun z hz ↦ by simpa [Ω'] using hz

/-- **The annihilator of a real Cauchy–Riemann operator gains `k + 1` derivatives.** Let
`Ω ⊆ ℂ` be open, `V` a finite-dimensional real inner product space, `J` a `Cᵏ⁺¹` field of complex
structures on `V` and `S` a `Cᵏ` field of endomorphisms over `Ω`. If a locally `L^q` field `v`
(`q > 1`) satisfies `∫ ⟪∂_s φ + J ∂_t φ + S φ, v⟫ = 0` for every test function `φ` on `Ω`, then
`v ∈ W^{k+1,r}_loc(Ω)` for every finite `r`. -/
theorem memWkpLoc_succ_of_forall_integral_inner_cauchyRiemann_eq_zero {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] {Ω : Opens ℂ}
    {J S : ℂ → V →L[ℝ] V} {k : ℕ} (hJ : ContDiffOn ℝ (k + 1) J Ω) (hS : ContDiffOn ℝ k S Ω)
    (hJ2 : ∀ z ∈ Ω, J z * J z = -1)
    {v : ℂ → V} {q r : ℝ≥0∞} (hq : 1 < q) (hv : MemLpLoc q Ω v)
    (h : ∀ φ : 𝓓(Ω, V), ∫ z, ⟪fderiv ℝ (φ : ℂ → V) z 1 + J z (fderiv ℝ (φ : ℂ → V) z I) +
      S z ((φ : ℂ → V) z), v z⟫_ℝ = 0)
    (hr_top : r ≠ ⊤) : MemWkpLoc r Ω (k + 1) v := by
  have hJ1 : ContDiffOn ℝ 1 J Ω := hJ.of_le le_add_self
  have hJ2' := ae_restrict_of_forall_mem (μ := volume) Ω.isOpen.measurableSet hJ2
  -- A finite exponent `P ≥ max r 4`, so that `1/P + 1/P < 1`.
  set P : ℝ≥0 := max r.toNNReal 4
  have hP4 : (4 : ℝ≥0) ≤ P := le_max_right _ _
  have hrP : r ≤ P := by
    rw [← ENNReal.coe_toNNReal hr_top]
    exact ENNReal.coe_le_coe.2 (le_max_left _ _)
  have hPinv : (P : ℝ≥0∞)⁻¹ + (P : ℝ≥0∞)⁻¹ < 1 := by
    have h4 : (P : ℝ≥0∞)⁻¹ ≤ 4⁻¹ := ENNReal.inv_le_inv.2 (by exact_mod_cast hP4)
    calc (P : ℝ≥0∞)⁻¹ + (P : ℝ≥0∞)⁻¹ ≤ 4⁻¹ + 4⁻¹ := add_le_add h4 h4
      _ < 1 := by
        rw [← two_mul, ← div_eq_mul_inv, ENNReal.div_lt_iff (by simp) (by simp)]
        norm_num
  -- Continuous coefficients are Sobolev coefficients for the exponent `∞`, so at order one `v`
  -- is in `W^{1,P}_loc`, hence locally `L^P`.
  have hvP : MemLpLoc P Ω v :=
    ((IsSobolevCRCoefficients.of_contDiffOn hJ1 hS.continuousOn ⊤)
      |>.memWkpLoc_one_of_forall_integral_inner_eq_zero (by simp) hJ2'
      (by simpa using ENNReal.inv_lt_one.2 hq) hv h
      (lt_of_lt_of_le (by norm_num) (ENNReal.coe_le_coe.2 hP4)) ENNReal.coe_ne_top le_top).memLpLoc
  -- Smooth coefficients are Sobolev coefficients of every finite exponent and every order.
  have hW := (IsSobolevCRCoefficients.of_contDiffOn hJ1 hS.continuousOn P)
    |>.memWkpLoc_succ_of_forall_integral_inner_eq_zero
      (lt_of_lt_of_le (by norm_num) hP4) hJ2' hPinv le_rfl
      (hJ.memWkpLoc (by exact_mod_cast le_rfl)) (hS.memWkpLoc le_rfl) hvP h
  exact hW.mono_exponent hrP

/-- **The annihilator of a real Cauchy–Riemann operator, for covector fields.** Let `Ω ⊆ ℂ` be
open, `V` a finite-dimensional real normed space, `J` a `Cᵏ⁺¹` field of complex structures on `V`
and `S` a `Cᵏ` field of endomorphisms over `Ω`. If a locally `L^q` covector field `η` (`q > 1`)
satisfies `∫ η (∂_s φ + J ∂_t φ + S φ) = 0` for every test function `φ` on `Ω`, then
`η ∈ W^{k+1,r}_loc(Ω)` for every finite `r`. -/
theorem memWkpLoc_succ_of_forall_integral_apply_cauchyRiemann_eq_zero {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {Ω : Opens ℂ}
    {J S : ℂ → V →L[ℝ] V} {k : ℕ} (hJ : ContDiffOn ℝ (k + 1) J Ω) (hS : ContDiffOn ℝ k S Ω)
    (hJ2 : ∀ z ∈ Ω, J z * J z = -1)
    {η : ℂ → V →L[ℝ] ℝ} {q r : ℝ≥0∞} (hq : 1 < q) (hη : MemLpLoc q Ω η)
    (h : ∀ φ : 𝓓(Ω, V), ∫ z, η z (fderiv ℝ (φ : ℂ → V) z 1 + J z (fderiv ℝ (φ : ℂ → V) z I) +
      S z ((φ : ℂ → V) z)) = 0)
    (hr_top : r ≠ ⊤) : MemWkpLoc r Ω (k + 1) η := by
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
  have hv := memWkpLoc_succ_of_forall_integral_inner_cauchyRiemann_eq_zero (S := fun z ↦ P (S z))
    (P.contDiff.comp_contDiffOn hJ) (P.contDiff.comp_contDiffOn hS) hP2 hq
    ((hη.clm_comp Q.toContinuousLinearMap).clm_comp T.toContinuousLinearMap) (fun φ ↦ ?_) hr_top
  · simpa using (hv.clm_comp T.symm.toContinuousLinearMap).clm_comp Q.symm.toContinuousLinearMap
  · -- The test function `L⁻¹ ∘ φ` on `V` gives the same integrand.
    rw [← h (TestFunction.postcompCLM (L.symm : _ →L[ℝ] V) φ)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z ↦ ?_)
    simp [hT, P, Q, L.symm.comp_fderiv]

end TauCeti
