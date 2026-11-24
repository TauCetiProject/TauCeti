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
import TauCeti.Data.ENNReal.Holder

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
  (`TauCeti.IsSobolevCRCoefficients.memWkpLoc_one_of_forall_integral_inner_eq_zero`);
* for a `C^{k+1}` field `J` and a `Cᵏ` field `S`, such a vector field is in `W^{k+1,r}_loc(Ω)` for
  every finite `r` (`TauCeti.memWkpLoc_succ_of_forall_integral_inner_cauchyRiemann_eq_zero`);
* the same holds for a covector field `η : Ω → V →L[ℝ] ℝ` on a finite-dimensional normed space,
  paired with `D φ` by `∫ η(D φ)`
  (`TauCeti.memWkpLoc_succ_of_forall_integral_apply_cauchyRiemann_eq_zero`). This form needs no
  inner product on `V`.

After the reflection `ρ(z) = -conj z`, an annihilator of `D` is a weak solution of a homogeneous
real Cauchy–Riemann equation whose leading coefficient again squares to `-1`
(`TauCeti.IsSobolevCRCoefficients.forall_integral_inner_eq_zero_iff`,
`TauCeti.crReflectedAdjointCoeff_mul_self_eq_neg_one_iff`). Interior regularity of order one
(`TauCeti.IsWeakCRSolution.memWkpLoc_one_of_le`) applies to it for Sobolev coefficients. For
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
  -- Work with the exponent `p = max r 3 > 2`, which bounds `r`.
  set p : ℝ≥0 := max r.toNNReal 3
  have hp : 2 < p := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hpp : (p : ℝ≥0∞)⁻¹ + (p : ℝ≥0∞)⁻¹ < 1 :=
    ENNReal.inv_add_inv_lt_one_of_two_lt (by exact_mod_cast hp)
  have hJ1 : ContDiffOn ℝ 1 J Ω := hJ.of_le le_add_self
  have hc := IsSobolevCRCoefficients.of_contDiffOn hJ1 hS.continuousOn ⊤
  have hJ2' : ∀ᵐ z ∂volume.restrict Ω, J z * J z = -1 :=
    ae_restrict_of_forall_mem Ω.isOpen.measurableSet hJ2
  have hqinv : (⊤ : ℝ≥0∞)⁻¹ + q⁻¹ < 1 := by simpa using ENNReal.inv_lt_one.2 hq
  -- First `v` is locally `Lᵖ`, by regularity of order one for Sobolev coefficients.
  have h1 : MemWkpLoc p Ω 1 v := hc.memWkpLoc_one_of_forall_integral_inner_eq_zero (by simp) hJ2'
    hqinv hv h (by exact_mod_cast one_lt_two.trans hp) ENNReal.coe_ne_top le_top
  -- After the reflection `ρ z = -conj z`, `v` solves a homogeneous Cauchy–Riemann equation.
  set Ω' : Opens ℂ := ⟨(fun z ↦ -conj z) ⁻¹' Ω, Ω.isOpen.preimage (by fun_prop)⟩
  have hρ : MapsTo (fun z : ℂ ↦ -conj z) Ω' Ω := fun _ hz ↦ hz
  have hweak := ((hc.forall_integral_inner_eq_zero_iff hqinv.le (Ω' := Ω') (fun _ ↦ Iff.rfl)
    hv).1 h).of_memLpLoc (h1.comp_neg_conj hρ).memLpLoc
  -- The reflected coefficients are `C^{k+1}` and `Cᵏ`, so interior regularity of every order
  -- (`IsWeakCRSolution.memWkpLoc_succ`) applies.
  have hDJ : ContDiffOn ℝ k (fderiv ℝ J) Ω := hJ.fderiv_of_isOpen Ω.isOpen le_rfl
  have hJk : MemWkpLoc p Ω' k (crReflectedAdjointCoeff J) :=
    ((hJ.of_le le_self_add).crReflectedAdjointCoeff hρ).memWkpLoc subset_rfl
  have hSk : MemWkpLoc p Ω' k (crReflectedAdjointZeroth (fderiv ℝ J) S) :=
    (hDJ.crReflectedAdjointZeroth hS hρ).memWkpLoc subset_rfl
  have hc' := (IsSobolevCRCoefficients.of_contDiffOn hJ1 hS.continuousOn p).crReflectedAdjoint hρ
  have hW := hweak.memWkpLoc_succ hc' hp (ae_crReflectedAdjointCoeff_mul_self_eq_neg_one hρ hJ2')
    hpp le_rfl hJk hSk memWkpLoc_zero_fun
  -- Reflecting back along `ρ`, using `ρ ∘ ρ = id`, and lowering the exponent to `r`.
  have hrp : r ≤ p := by
    rw [← ENNReal.coe_toNNReal hr_top]
    exact_mod_cast le_max_left _ _
  simpa using (hW.comp_neg_conj fun z hz ↦ by simpa [Ω'] using hz).mono_exponent hrp

/-- **The annihilator of a real Cauchy–Riemann operator, for covector fields.** Let `Ω ⊆ ℂ` be
open, `V` a finite-dimensional real normed space, `J` a `C^{k+1}` field of complex structures on `V`
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

end TauCeti
