/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.Adjoint
public import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.HigherOrder.Basic
public import TauCeti.Analysis.Sobolev.Local.ChangeOfVariables
public import TauCeti.Analysis.Normed.Operator.ComplexLinearPart
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import TauCeti.Analysis.Sobolev.Local.Morrey.Higher
import TauCeti.Data.ENNReal.Holder
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Sobolev.WeakDeriv.IntegrationByParts

/-!
# Sobolev regularity of the annihilator of a real Cauchy–Riemann operator

Let `Ω ⊆ ℂ` be open, write `z = s + i t`, and let `D φ = ∂_s φ + J ∂_t φ + S φ` be a real
Cauchy–Riemann operator on maps `φ : Ω → V` into a finite-dimensional real vector space, with a
field of complex structures `J` (`J² = -1`) and a zeroth-order coefficient `S`. A field `η`
annihilating `D φ` for every test function `φ` is a weak solution of the adjoint equation
`D* η = 0`. In Fredholm theory such fields are the elements of the cokernel of a Sobolev
realization of `D`, and a priori they are only locally `L^q`. This file proves that they are as
regular as the coefficients allow:

* for Sobolev coefficients `J ∈ W^{1,p}_loc`, `S ∈ Lᵖ_loc` with `p > 2` and `J² = -1` a.e., a
  vector field `η` in a real inner product space, paired with `D φ` by `∫ ⟪D φ, η⟫`, is in
  `W^{1,r}_loc(Ω)` for every finite `r > 1` with `r ≤ p`
  (`TauCeti.IsSobolevCRCoefficients.memWkpLoc_one_of_forall_integral_inner_eq_zero`), and in
  `W^{k+1,q}_loc` when moreover `J ∈ W^{k+1,p}_loc` and `S ∈ W^{k,p}_loc`, for its own exponent
  `q ≤ p` (`TauCeti.IsSobolevCRCoefficients.memWkpLoc_succ_of_forall_integral_inner_eq_zero`);
* for a `C^{k+1}` field `J` and a `Cᵏ` field `S`, such a vector field is in `W^{k+1,r}_loc(Ω)` for
  every finite `r` (`TauCeti.memWkpLoc_succ_of_forall_integral_inner_cauchyRiemann_eq_zero`);
* the same holds for a covector field `η : Ω → V →L[ℝ] ℝ` on a finite-dimensional normed space,
  paired with `D φ` by `∫ η(D φ)`
  (`TauCeti.memWkpLoc_succ_of_forall_integral_apply_cauchyRiemann_eq_zero`). This form needs no
  inner product on `V`. For `J ∈ C^{ℓ+1}` and `S ∈ C^ℓ`, `ℓ ≤ ∞`, such a covector field agrees
  almost everywhere with a `C^ℓ` field
  (`TauCeti.exists_contDiffOn_ae_eq_of_forall_integral_apply_cauchyRiemann_eq_zero`);
* by duality, a locally `L^q` function `u` (`q > 1`) with a weak derivative that solves
  `∂_s u + J ∂_t u + S u = 0` almost everywhere, for `J ∈ C^{ℓ+1}` and `S ∈ C^ℓ`, agrees almost
  everywhere with a `C^ℓ` function
  (`TauCeti.exists_contDiffOn_ae_eq_of_hasWeakFDerivOn_cauchyRiemann`): the field of evaluations
  `z ↦ (ψ ↦ ψ (u z))` annihilates the transposed operator on covector test functions;
* the adjoint equation `∫ η ((∂bar φ + Z φ)(1)) = 0` of an operator written with the complex
  antilinear part of the derivative is the covector form for `J = i` and `S = 2 Z(·)(1)`
  (`TauCeti.integral_apply_cauchyRiemann_eq_zero_of_integral_eq_zero`).

After the reflection `ρ(z) = -conj z`, an annihilator of `D` is a weak solution of a homogeneous
real Cauchy–Riemann equation whose leading coefficient again squares to `-1`
(`TauCeti.IsSobolevCRCoefficients.forall_integral_inner_eq_zero_iff`,
`TauCeti.crReflectedAdjointCoeff_mul_self_eq_neg_one_iff`). Interior regularity of order one
(`TauCeti.IsWeakCRSolution.memWkpLoc_one_of_le`) applies to it for Sobolev coefficients, and of
higher order (`TauCeti.IsWeakCRSolution.memWkpLoc_succ`) for Sobolev coefficients of higher order:
the reflected coefficients `J' = -(J ∘ ρ)ᵀ` and `S' = (S ∘ ρ)ᵀ - (∂_t J ∘ ρ)ᵀ` lose one derivative
of `J`, which is why `J` needs one derivative more than `S`. For
smooth coefficients the reflected coefficients `J'` and `S'` are `C^{k+1}` and `Cᵏ`, the
annihilator is locally `Lᵖ` for every finite `p` by the first case, and interior regularity of
every order (`TauCeti.IsWeakCRSolution.memWkpLoc_succ`) applies. The covector form follows from the
vector form in a Euclidean model of `V`. By Morrey's embedding
(`TauCeti.MemWkpLoc.exists_contDiffOn_ae_eq`), an annihilator for a `C^{k+1}` field `J` and a `Cᵏ`
field `S` therefore agrees almost everywhere with a `Cᵏ` field.

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

/-- `ρ(z) = -conj z` preserves Lebesgue measure, so `J² = -1` almost everywhere on `Ω` gives
`J'² = -1` almost everywhere on any open `Ω'` that `ρ` maps into `Ω`. -/
private theorem ae_crReflectedAdjointCoeff_mul_self_eq_neg_one {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V] {Ω Ω' : Opens ℂ}
    {J : ℂ → V →L[ℝ] V} (hρ : MapsTo (fun z : ℂ ↦ -conj z) Ω' Ω)
    (hJ2 : ∀ᵐ z ∂volume.restrict Ω, J z * J z = -1) :
    ∀ᵐ z ∂volume.restrict Ω', crReflectedAdjointCoeff J z * crReflectedAdjointCoeff J z = -1 := by
  have hρm : MeasurePreserving (fun z : ℂ ↦ -conj z) :=
    (conjLIE.trans (LinearIsometryEquiv.neg ℝ)).measurePreserving
  rw [ae_restrict_iff' Ω'.isOpen.measurableSet]
  filter_upwards [hρm.quasiMeasurePreserving.ae
    ((ae_restrict_iff' Ω.isOpen.measurableSet).1 hJ2)] with z hz hzΩ'
  exact (crReflectedAdjointCoeff_mul_self_eq_neg_one_iff z).2 (hz (hρ hzΩ'))

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
  have hρ : MapsTo (fun z : ℂ ↦ -conj z) Ω' Ω := fun _ hz ↦ hz
  have hW := hweak.memWkpLoc_one_of_le (hc.crReflectedAdjoint hρ) hp
    (ae_crReflectedAdjointCoeff_mul_self_eq_neg_one hρ hJ2) hpq hr hr_top hrp
    continuousOn_const.memLpLoc
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
  have hweak := (hc.forall_integral_inner_eq_zero_iff hpq.le (Ω' := Ω') (fun _ ↦ Iff.rfl) hv).1 h
  -- The reflected coefficients `J'` and `S'` are in `W^{k,p}_loc`; `S'` involves `DJ`.
  have hDJ : MemWkpLoc p Ω k DJ := hJ.memWkpLoc_of_hasWeakFDerivOn hc.hasWeakFDerivOn
  have hW := hweak.memWkpLoc_succ (hc.crReflectedAdjoint hρ) (by exact_mod_cast hp)
    (ae_crReflectedAdjointCoeff_mul_self_eq_neg_one hρ hJ2) hpq
    (ENNReal.inv_lt_one.1 (lt_of_le_of_lt le_add_self hpq)) ENNReal.coe_ne_top
    (by exact_mod_cast hqp) (hJ.of_succ.crReflectedAdjointCoeff hρ)
    (hDJ.crReflectedAdjointZeroth hS hρ) memWkpLoc_zero_fun
  -- Reflecting back along `ρ`, using `ρ ∘ ρ = id`.
  simpa using hW.comp_neg_conj fun z hz ↦ by simpa [Ω'] using hz

/-- **The annihilator of a real Cauchy–Riemann operator is `W^{k+1,r}_loc`.** Let `Ω ⊆ ℂ` be
open, `V` a finite-dimensional real inner product space, `J` a `C^{k+1}` field of complex structures
on `V` and `S` a `Cᵏ` field of endomorphisms over `Ω`. If a locally `L^q` field `v` (`q > 1`)
satisfies `∫ ⟪∂_s φ + J ∂_t φ + S φ, v⟫ = 0` for every test function `φ` on `Ω`, then
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
  have hP2 : (2 : ℝ≥0∞) < P := lt_of_lt_of_le (by norm_num) (ENNReal.coe_le_coe.2 hP4)
  -- Continuous coefficients are Sobolev coefficients for the exponent `∞`, so at order one `v`
  -- is in `W^{1,P}_loc`, hence locally `L^P`.
  have hvP : MemLpLoc P Ω v :=
    ((IsSobolevCRCoefficients.of_contDiffOn hJ1 hS.continuousOn ⊤)
      |>.memWkpLoc_one_of_forall_integral_inner_eq_zero (by simp) hJ2'
      (by simpa using ENNReal.inv_lt_one.2 hq) hv h
      (ENNReal.one_lt_two.trans hP2) ENNReal.coe_ne_top le_top).memLpLoc
  -- Smooth coefficients are Sobolev coefficients of every finite exponent and every order.
  have hW := (IsSobolevCRCoefficients.of_contDiffOn hJ1 hS.continuousOn P)
    |>.memWkpLoc_succ_of_forall_integral_inner_eq_zero
      (by exact_mod_cast hP2) hJ2' (ENNReal.inv_add_inv_lt_one_of_two_lt hP2) le_rfl
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
  have hv := memWkpLoc_succ_of_forall_integral_inner_cauchyRiemann_eq_zero
    (S := fun z ↦ P (S z)) (P.contDiff.comp_contDiffOn hJ) (P.contDiff.comp_contDiffOn hS) hP2 hq
    ((hη.clm_comp Q.toContinuousLinearMap).clm_comp T.toContinuousLinearMap) (fun φ ↦ ?_) hr_top
  · simpa using (hv.clm_comp T.symm.toContinuousLinearMap).clm_comp Q.symm.toContinuousLinearMap
  · -- The test function `L⁻¹ ∘ φ` on `V` gives the same integrand.
    rw [← h (TestFunction.postcompCLM (L.symm : _ →L[ℝ] V) φ)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z ↦ ?_)
    simp [hT, P, Q, L.symm.comp_fderiv]

/-- **Regularity of annihilators of a real Cauchy–Riemann operator.** Let `Ω ⊆ ℂ` be open, `V` a
finite-dimensional real normed space, `ℓ ≤ ∞`, `J` a `C^{ℓ+1}` field of complex structures on `V`
and `S` a `C^ℓ` field of endomorphisms over `Ω`. If a locally `L^q` covector field `η` (`q > 1`)
satisfies `∫ η (∂_s φ + J ∂_t φ + S φ) = 0` for every test function `φ` on `Ω`, then `η` agrees
almost everywhere on `Ω` with a `C^ℓ` covector field. -/
theorem exists_contDiffOn_ae_eq_of_forall_integral_apply_cauchyRiemann_eq_zero {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {Ω : Opens ℂ}
    {J S : ℂ → V →L[ℝ] V} {ℓ : ℕ∞} (hJ : ContDiffOn ℝ ((ℓ + 1 : ℕ∞) : WithTop ℕ∞) J Ω)
    (hS : ContDiffOn ℝ (ℓ : WithTop ℕ∞) S Ω) (hJ2 : ∀ z ∈ Ω, J z * J z = -1)
    {η : ℂ → V →L[ℝ] ℝ} {q : ℝ≥0∞} (hq : 1 < q) (hη : MemLpLoc q Ω η)
    (h : ∀ φ : 𝓓(Ω, V), ∫ z, η z (fderiv ℝ (φ : ℂ → V) z 1 + J z (fderiv ℝ (φ : ℂ → V) z I) +
      S z ((φ : ℂ → V) z)) = 0) :
    ∃ g : ℂ → V →L[ℝ] ℝ, ContDiffOn ℝ (ℓ : WithTop ℕ∞) g Ω ∧ η =ᵐ[volume.restrict Ω] g := by
  have hreg (k : ℕ) (hk : (k : ℕ∞) ≤ ℓ) : MemWkpLoc 3 Ω (k + 1) η :=
    memWkpLoc_succ_of_forall_integral_apply_cauchyRiemann_eq_zero
      (hJ.of_le (by exact_mod_cast (show ((k + 1 : ℕ) : ℕ∞) ≤ ℓ + 1 by
        push_cast; exact add_le_add_left hk 1))) (hS.of_le (by exact_mod_cast hk))
      hJ2 hq hη h (by simp)
  -- Morrey's embedding at order zero gives a continuous representative, `C^k` for `k ≤ ℓ`.
  obtain ⟨g, hg, hηg⟩ := (hreg 0 (by simp)).exists_contDiffOn_ae_eq (by norm_num)
  have hC (k : ℕ) (hk : (k : ℕ∞) ≤ ℓ) : ContDiffOn ℝ k g Ω :=
    (hreg k hk).contDiffOn_of_continuousOn (by norm_num) hg.continuousOn hηg
  refine ⟨g, ?_, hηg⟩
  induction ℓ using ENat.recTopCoe with
  | top => exact contDiffOn_infty.2 fun k ↦ hC k le_top
  | coe n => exact_mod_cast hC n le_rfl

/-! ### Weak solutions of a real Cauchy–Riemann equation, by duality -/

/-- **The transposed equation.** If `u` has weak derivative `Du` and solves
`∂_s u + J ∂_t u + S u = 0` almost everywhere on `Ω`, for a `C¹` field `J`, then for every covector
test function `ψ`, `∫ (∂_s ψ + Jᵀ ∂_t ψ + (∂_t J - S)ᵀ ψ)(u) = 0`, where `Aᵀ ψ = ψ ∘ A`. -/
private theorem integral_apply_cauchyRiemann_transpose_eq_zero {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {Ω : Opens ℂ}
    {J S : ℂ → V →L[ℝ] V} (hJ : ContDiffOn ℝ 1 J Ω) {u : ℂ → V} {Du : ℂ → ℂ →L[ℝ] V}
    (hDu : HasWeakFDerivOn volume Ω u Du)
    (h : ∀ᵐ z ∂volume.restrict Ω, Du z 1 + J z (Du z I) + S z (u z) = 0)
    (ψ : 𝓓(Ω, V →L[ℝ] ℝ)) :
    ∫ z, fderiv ℝ (ψ : ℂ → V →L[ℝ] ℝ) z 1 (u z) +
      (ContinuousLinearMap.compL ℝ V V ℝ).flip (J z) (fderiv ℝ (ψ : ℂ → V →L[ℝ] ℝ) z I) (u z) +
        (ContinuousLinearMap.compL ℝ V V ℝ).flip (fderiv ℝ J z I - S z) (ψ z) (u z) = 0 := by
  set T : (V →L[ℝ] V) →L[ℝ] (V →L[ℝ] ℝ) →L[ℝ] V →L[ℝ] ℝ :=
    (ContinuousLinearMap.compL ℝ V V ℝ).flip
  have hψ : ContDiff ℝ 1 (ψ : ℂ → V →L[ℝ] ℝ) := ψ.contDiff.of_le (by simp)
  -- The test function `Φ = Jᵀ ψ` is `C¹` with support in that of `ψ`.
  set Φ : ℂ → V →L[ℝ] ℝ := fun z ↦ T (J z) (ψ z)
  have hΦ : ContDiff ℝ 1 Φ :=
    T.contDiff_of_tsupport_subset_right hJ hψ.contDiffOn Ω.isOpen ψ.tsupport_subset
  have hΦψ : Function.support Φ ⊆ Function.support ψ :=
    Function.support_subset_iff'.2 fun z hz ↦ by simp [Φ, Function.notMem_support.1 hz]
  have hΦc : HasCompactSupport Φ := ψ.hasCompactSupport.mono hΦψ
  have hΦs : tsupport Φ ⊆ Ω := (closure_mono hΦψ).trans ψ.tsupport_subset
  have hdΦ (z : ℂ) : fderiv ℝ Φ z I (u z) =
      T (J z) (fderiv ℝ (ψ : ℂ → V →L[ℝ] ℝ) z I) (u z) + T (fderiv ℝ J z I) (ψ z) (u z) := by
    rw [T.fderiv_of_tsupport_subset_right (hJ.differentiableOn one_ne_zero)
      (hψ.differentiable one_ne_zero) Ω.isOpen ψ.tsupport_subset z]
    simp
  -- Integration by parts in both directions, and the equation for the zeroth-order term.
  have h₁ := (hDu.hasWeakLineDerivOn 1).integral_fderiv_apply_eq_neg hψ ψ.hasCompactSupport
    ψ.tsupport_subset
  have h₂ := (hDu.hasWeakLineDerivOn I).integral_fderiv_apply_eq_neg hΦ hΦc hΦs
  have hi₁ := hDu.locallyIntegrableOn.integrable_clm_apply_of_hasCompactSupport
    ((hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const).continuousOn
    (ψ.hasCompactSupport.fderiv_apply ℝ 1) ((tsupport_fderiv_apply_subset ℝ 1).trans
      ψ.tsupport_subset)
  have hi₂ := hDu.locallyIntegrableOn.integrable_clm_apply_of_hasCompactSupport
    ((hΦ.continuous_fderiv one_ne_zero).clm_apply continuous_const).continuousOn
    (hΦc.fderiv_apply ℝ I) ((tsupport_fderiv_apply_subset ℝ I).trans hΦs)
  have hj₁ := (hDu.hasWeakLineDerivOn 1).locallyIntegrableOn_deriv
    |>.integrable_clm_apply_of_hasCompactSupport hψ.continuous.continuousOn ψ.hasCompactSupport
      ψ.tsupport_subset
  have hj₂ := (hDu.hasWeakLineDerivOn I).locallyIntegrableOn_deriv
    |>.integrable_clm_apply_of_hasCompactSupport hΦ.continuous.continuousOn hΦc hΦs
  have hS : (fun z ↦ ψ z (S z (u z))) =ᵐ[volume] fun z ↦ -(ψ z (Du z 1) + Φ z (Du z I)) := by
    filter_upwards [(ae_restrict_iff' Ω.isOpen.measurableSet).1 h] with z hz
    by_cases hzΩ : z ∈ Ω
    · simp only [Φ, T, ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply,
        ContinuousLinearMap.comp_apply, ← map_add]
      rw [eq_neg_of_add_eq_zero_right (hz hzΩ), map_neg]
    · simp [Φ, image_eq_zero_of_notMem_tsupport fun h ↦ hzΩ (ψ.tsupport_subset h)]
  calc _ = ∫ z, fderiv ℝ (ψ : ℂ → V →L[ℝ] ℝ) z 1 (u z) + fderiv ℝ Φ z I (u z) -
        ψ z (S z (u z)) := integral_congr_ae (.of_forall fun z ↦ by simp [hdΦ, T]; abel)
    _ = 0 := by
      have hi : Integrable (fun z ↦ fderiv ℝ (ψ : ℂ → V →L[ℝ] ℝ) z 1 (u z) +
          fderiv ℝ Φ z I (u z)) := hi₁.add hi₂
      have hj : Integrable (fun z ↦ ψ z (Du z 1) + Φ z (Du z I)) := hj₁.add hj₂
      rw [integral_sub hi (hj.neg.congr hS.symm), integral_add hi₁ hi₂,
        integral_congr_ae hS, integral_neg, integral_add hj₁ hj₂, h₁, h₂]
      ring

/-- **Weak solutions of a real Cauchy–Riemann equation are regular at every exponent.** Let
`Ω ⊆ ℂ` be open, `V` a finite-dimensional real normed space, `ℓ ≤ ∞`, `J` a `C^{ℓ+1}` field of
complex structures on `V` and `S` a `C^ℓ` field of endomorphisms over `Ω`. If a locally `L^q`
function `u` (`q > 1`) with weak derivative `Du` satisfies `∂_s u + J ∂_t u + S u = 0` almost
everywhere on `Ω`, then `u` agrees almost everywhere on `Ω` with a `C^ℓ` function.

Unlike the bootstrap for `IsWeakCauchyRiemannOn`, this needs no exponent above `2`. By weak
integration by parts, the field of evaluations `z ↦ (ψ ↦ ψ (u z))` annihilates the transposed
operator `∂_s ψ + Jᵀ ∂_t ψ + (∂_t J - S)ᵀ ψ` on covector test functions `ψ`, whose leading
coefficient `Jᵀ` again squares to `-1`; so the regularity theorem for annihilators applies. -/
theorem exists_contDiffOn_ae_eq_of_hasWeakFDerivOn_cauchyRiemann {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {Ω : Opens ℂ}
    {J S : ℂ → V →L[ℝ] V} {ℓ : ℕ∞} (hJ : ContDiffOn ℝ ((ℓ + 1 : ℕ∞) : WithTop ℕ∞) J Ω)
    (hS : ContDiffOn ℝ (ℓ : WithTop ℕ∞) S Ω) (hJ2 : ∀ z ∈ Ω, J z * J z = -1)
    {u : ℂ → V} {Du : ℂ → ℂ →L[ℝ] V} {q : ℝ≥0∞} (hq : 1 < q) (hu : MemLpLoc q Ω u)
    (hDu : HasWeakFDerivOn volume Ω u Du)
    (h : ∀ᵐ z ∂volume.restrict Ω, Du z 1 + J z (Du z I) + S z (u z) = 0) :
    ∃ g : ℂ → V, ContDiffOn ℝ (ℓ : WithTop ℕ∞) g Ω ∧ u =ᵐ[volume.restrict Ω] g := by
  -- `T A ψ = ψ ∘ A` transposes endomorphisms of `V` to endomorphisms of its dual.
  let T : (V →L[ℝ] V) →L[ℝ] (V →L[ℝ] ℝ) →L[ℝ] V →L[ℝ] ℝ :=
    (ContinuousLinearMap.compL ℝ V V ℝ).flip
  have hdJ : ContDiffOn ℝ (ℓ : WithTop ℕ∞) (fun z ↦ fderiv ℝ J z I) Ω :=
    (hJ.fderiv_of_isOpen Ω.isOpen (by exact_mod_cast le_rfl)).clm_apply contDiffOn_const
  let ev : V →L[ℝ] (V →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ
  have hη : MemLpLoc q Ω (fun z ↦ ev (u z)) := hu.clm_comp (G := (V →L[ℝ] ℝ) →L[ℝ] ℝ) ev
  obtain ⟨g, hg, hug⟩ := exists_contDiffOn_ae_eq_of_forall_integral_apply_cauchyRiemann_eq_zero
    (Ω := Ω) (ℓ := ℓ) (J := fun z ↦ T (J z)) (S := fun z ↦ T (fderiv ℝ J z I - S z))
    (contDiffOn_const.clm_apply hJ) (contDiffOn_const.clm_apply (hdJ.sub hS))
    (fun z hz ↦ by ext ψ v; simp [T, ← mul_apply_eq_comp, hJ2 z hz]) hq hη
    fun ψ ↦ integral_apply_cauchyRiemann_transpose_eq_zero (hJ.of_le (by simp)) hDu h ψ
  -- `u` is recovered from its evaluations on the coordinate functionals of a basis.
  let b := Module.finBasis ℝ V
  refine ⟨fun z ↦ ∑ j, g z (LinearMap.toContinuousLinearMap (b.coord j)) • b j,
    ContDiffOn.sum fun j _ ↦ (hg.clm_apply contDiffOn_const).smul contDiffOn_const, ?_⟩
  filter_upwards [hug] with z hz
  rw [← hz]
  exact (b.sum_repr (u z)).symm

/-! ### The adjoint equation of an operator `∂bar + Z` -/

section ComplexAntilinear

open ContinuousLinearMap (complexAntilinearPartL complexAntilinearPartL_apply_one lsmul)

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F]

/-- **The adjoint equation in planar form.** For a covector field `η`, a field `Z` of zeroth-order
terms and a function `φ`, if `η` annihilates the value on `1` of `∂bar φ + Z φ` in integral, it
annihilates `∂ₛφ + i ∂ₜφ + 2 Z(φ)(1)`, which is twice that value. This is the form of the adjoint
equation for `J = i` and `S = 2 Z(·)(1)` taken by the planar regularity theorems. -/
theorem integral_apply_cauchyRiemann_eq_zero_of_integral_eq_zero {η : ℂ → F →L[ℝ] ℝ}
    {Z : ℂ → F →L[ℝ] ℂ →L[ℝ] F} {φ : ℂ → F}
    (h : ∫ z, η z ((complexAntilinearPartL (fderiv ℝ φ z) + Z z (φ z)) 1) = 0) :
    ∫ z, η z (fderiv ℝ φ z 1 + lsmul ℝ ℂ Complex.I (fderiv ℝ φ z Complex.I) +
      ((2 : ℝ) • (ContinuousLinearMap.apply ℝ F (1 : ℂ)).comp (Z z)) (φ z)) = 0 := by
  have h2 := congrArg ((2 : ℝ) * ·) h
  rw [mul_zero, ← integral_const_mul] at h2
  rw [← h2]
  refine integral_congr_ae (.of_forall fun z ↦ ?_)
  simp only [add_apply, complexAntilinearPartL_apply_one,
    smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply, map_add, map_smul, smul_eq_mul]
  ring

end ComplexAntilinear

end TauCeti
