/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.HalfPlane
import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.Interior
import TauCeti.Analysis.Complex.Wirtinger.RealBoundary.Reflection
import TauCeti.Analysis.Distribution.TestFunction.Inner
import TauCeti.Analysis.Distribution.TestFunction.LinearEquiv
import TauCeti.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Order-zero reflection for rough Cauchy–Riemann equations with a totally real boundary condition

Let `Ω ⊆ ℂ` be an open set invariant under complex conjugation, write `z = s + i t`, and let `V`
be a real inner product space with an isometric involution `R` (for `V = ℂⁿ`, coordinatewise
conjugation). Let `ξ` be a weak solution up to the real axis of `∂_s ξ + J ∂_t ξ + S ξ = η` on
`Ω ∩ {0 ≤ t}`, in the sense of `TauCeti.IsWeakCRSolutionHalf`, for a boundary subspace `Λ`
containing the fixed vectors of `R`. This file reflects the solution and the data across `ℝ`:

* `ξ(conj z) = R ξ(z)` and `η(conj z) = R η(z)` (`TauCeti.crReflection`),
* `J(conj z) = -R J(z) R⁻¹` (`TauCeti.crReflectionCoeff`), with derivative
  `DJ(conj z) h = -R DJ(z)(conj h) R⁻¹` (`TauCeti.crReflectionDeriv`),
* `S(conj z) = R S(z) R⁻¹` (`TauCeti.crReflectionZeroth`),

and proves that the reflected solution is a weak solution of the reflected equation on all of
`Ω` (`TauCeti.IsWeakCRSolutionHalf.isWeakCRSolution_crReflection`). The sign in the reflection of
`J` is forced by `∂_t (ξ(conj z)) = -(∂_t ξ)(conj z)`. For `J = i` and `R = conj` the reflected
coefficient is `i` again (`TauCeti.crReflectionCoeff_conj_I`): this is the setting of
McDuff–Salamon, where `J(s) = i` on `ℝ` makes the reflected coefficient continuous across the
axis. The weak identity itself needs no condition on `J` along `ℝ`.

A test function `φ` on `Ω` is
paired with its reflection `φ^R(z) = R φ(conj z)`; the sum `φ + φ^R` takes values in the fixed
space of `R` on `ℝ`, so it is admissible for the boundary condition, and the lower half-plane
part of the doubled pairing is the upper half-plane pairing with `φ^R`, by the
measure-preserving substitution `z ↦ conj z`. Pointwise, `R` applied to the reflected formal
adjoint of `φ` at `conj z` is the formal adjoint `TauCeti.crFormalAdjoint` of `φ^R` at `z`.
Integrability on the doubled domain comes from the Hölder condition
`1/p + 1/q ≤ 1` for coefficients `J, DJ, S ∈ Lᵖ_loc` up to the boundary.

Combined with the interior regularity theorem `TauCeti.IsWeakCRSolution.memWkpLoc_one_of_le`, this
gives `W^{1,r}` regularity up to the boundary (`TauCeti.IsWeakCRSolutionHalf.memWkpLoc_one`),
once the reflected coefficients are Sobolev coefficients on `Ω`. For the constant structure
`J = i` on `V = ℂ` this holds outright (`TauCeti.IsWeakCRSolutionHalf.memWkpLoc_one_of_I`). For
a variable `J ∈ W^{1,p}` up to the boundary, the reflected coefficient is the even reflection of
the part of `J` anticommuting with `R` plus the odd reflection of the part commuting with `R`;
the boundary condition `J(s) = i` says that the second part vanishes on `ℝ`, which is what makes
its odd reflection Sobolev. That gluing step is not part of this file.

## Main results

* `TauCeti.IsWeakCRSolutionHalf.isWeakCRSolution_crReflection`: the reflected solution is a weak
  solution of the reflected equation on the doubled domain.
* `TauCeti.IsWeakCRSolutionHalf.memWkpLoc_one`: if the reflected coefficients are Sobolev
  coefficients with `J² = -1` and `p > 2`, and `η ∈ Lʳ_loc` up to the boundary with
  `1 < r ≤ p`, then `ξ ∈ W^{1,r}_loc(Ω ∩ {0 ≤ t})`.
* `TauCeti.IsWeakCRSolutionHalf.memWkpLoc_one_of_I`: the case `V = ℂ`, `J = i`, `S = 0`, real
  boundary values.
* Checks: `TauCeti.crReflection_conj_id`, the reflection of `ξ = z` with `R = conj` is `z` again,
  and `TauCeti.crReflection_refl_id_ne`, the reflection without `R` is not.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.4, equation (B.4.3) and Lemma B.4.6.
-/

public noncomputable section

open MeasureTheory TopologicalSpace Complex Set Filter
open scoped InnerProductSpace ContDiff Distributions ENNReal ComplexConjugate

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {Ω : Opens ℂ} {Λ : Submodule ℝ V} {p q r : ℝ≥0∞} {R : V ≃ₗᵢ[ℝ] V}
  {J S : ℂ → V →L[ℝ] V} {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V} {ξ η : ℂ → V}

/-! ### Reflected data -/

/-- The **reflection of a field** across the real axis by the isometry `R`: `ξ` on the closed
upper half-plane and `R ξ(conj z)` below it. -/
def crReflection (R : V ≃ₗᵢ[ℝ] V) (ξ : ℂ → V) (z : ℂ) : V :=
  if 0 ≤ z.im then ξ z else R (ξ (conj z))

/-- The **reflection of the leading coefficient** across the real axis by the isometry `R`: `J`
on the closed upper half-plane and `-R J(conj z) R⁻¹` below it, so that `∂_s + J' ∂_t`, for this
reflected coefficient `J'`, maps reflected fields to reflected fields. -/
def crReflectionCoeff (R : V ≃ₗᵢ[ℝ] V) (J : ℂ → V →L[ℝ] V) (z : ℂ) : V →L[ℝ] V :=
  if 0 ≤ z.im then J z else -R.toContinuousLinearEquiv.conjContinuousAlgEquiv (J (conj z))

/-- The **reflection of the derivative of the leading coefficient**: `DJ` on the closed upper
half-plane and `h ↦ -R DJ(conj z)(conj h) R⁻¹` below it, the derivative of
`TauCeti.crReflectionCoeff R J` there when `DJ` is that of `J`. -/
def crReflectionDeriv (R : V ≃ₗᵢ[ℝ] V) (DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V) (z : ℂ) :
    ℂ →L[ℝ] V →L[ℝ] V :=
  if 0 ≤ z.im then DJ z else
    -(R.toContinuousLinearEquiv.conjContinuousAlgEquiv.toContinuousLinearEquiv :
      (V →L[ℝ] V) →L[ℝ] V →L[ℝ] V).comp ((DJ (conj z)).comp (conjCLE : ℂ →L[ℝ] ℂ))

/-- The **reflection of the zeroth-order coefficient**: `S` on the closed upper half-plane and
`R S(conj z) R⁻¹` below it. -/
def crReflectionZeroth (R : V ≃ₗᵢ[ℝ] V) (S : ℂ → V →L[ℝ] V) (z : ℂ) : V →L[ℝ] V :=
  if 0 ≤ z.im then S z else R.toContinuousLinearEquiv.conjContinuousAlgEquiv (S (conj z))

section Apply

variable {z : ℂ}

@[simp]
theorem crReflection_of_im_nonneg (hz : 0 ≤ z.im) : crReflection R ξ z = ξ z := ite_eq_left hz

@[simp]
theorem crReflection_of_im_neg (hz : z.im < 0) : crReflection R ξ z = R (ξ (conj z)) :=
  ite_eq_right (not_le.2 hz)

@[simp]
theorem crReflectionCoeff_of_im_nonneg (hz : 0 ≤ z.im) : crReflectionCoeff R J z = J z :=
  ite_eq_left hz

@[simp]
theorem crReflectionCoeff_apply_of_im_neg (hz : z.im < 0) (v : V) :
    crReflectionCoeff R J z v = -R (J (conj z) (R.symm v)) := by
  simp [crReflectionCoeff, not_le.2 hz]

@[simp]
theorem crReflectionDeriv_of_im_nonneg (hz : 0 ≤ z.im) : crReflectionDeriv R DJ z = DJ z :=
  ite_eq_left hz

@[simp]
theorem crReflectionDeriv_apply_of_im_neg (hz : z.im < 0) (h : ℂ) (v : V) :
    crReflectionDeriv R DJ z h v = -R (DJ (conj z) (conj h) (R.symm v)) := by
  simp [crReflectionDeriv, not_le.2 hz]

@[simp]
theorem crReflectionZeroth_of_im_nonneg (hz : 0 ≤ z.im) : crReflectionZeroth R S z = S z :=
  ite_eq_left hz

@[simp]
theorem crReflectionZeroth_apply_of_im_neg (hz : z.im < 0) (v : V) :
    crReflectionZeroth R S z v = R (S (conj z) (R.symm v)) := by
  simp [crReflectionZeroth, not_le.2 hz]

/-- Below the axis the reflected coefficient squares to `-1` where `J` does at the conjugate
point: `(R J R⁻¹)² = R J² R⁻¹`. -/
theorem crReflectionCoeff_mul_self_of_im_neg (hz : z.im < 0)
    (hJ : J (conj z) * J (conj z) = -1) :
    crReflectionCoeff R J z * crReflectionCoeff R J z = -1 := by
  ext v
  have h := congrArg (fun M : V →L[ℝ] V => M (R.symm v)) hJ
  simp only [mul_apply_eq_comp, neg_apply, one_apply_eq_self] at h
  simp [crReflectionCoeff_apply_of_im_neg hz, h]

end Apply

/-- The reflection of the zero derivative field is zero. -/
@[simp]
theorem crReflectionDeriv_zero : crReflectionDeriv R (0 : ℂ → ℂ →L[ℝ] V →L[ℝ] V) = 0 := by
  funext z
  rcases le_or_gt 0 z.im with hz | hz
  · exact crReflectionDeriv_of_im_nonneg hz
  · ext h v
    simp [crReflectionDeriv_apply_of_im_neg hz]

/-- The reflection of the zero zeroth-order coefficient is zero. -/
@[simp]
theorem crReflectionZeroth_zero : crReflectionZeroth R (0 : ℂ → V →L[ℝ] V) = 0 := by
  funext z
  rcases le_or_gt 0 z.im with hz | hz
  · exact crReflectionZeroth_of_im_nonneg hz
  · ext v
    simp [crReflectionZeroth_apply_of_im_neg hz]

/-- The reflected field agrees with the field on the closed upper half-plane. -/
theorem eqOn_crReflection (R : V ≃ₗᵢ[ℝ] V) (ξ : ℂ → V) (U : Set ℂ) :
    EqOn (crReflection R ξ) ξ (U ∩ {z | 0 ≤ z.im}) := fun _ hz => crReflection_of_im_nonneg hz.2

/-! ### Local integrability on the doubled domain -/

section Integrability

variable (R)

/-- A field locally `Lᵖ` up to the real axis reflects to a field locally `Lᵖ` on the doubled
domain. -/
theorem MemLpLoc.crReflection {U : Set ℂ} (hU : MapsTo (starRingEnd ℂ) U U)
    (hξ : MemLpLoc p (U ∩ {z | 0 ≤ z.im}) ξ) : MemLpLoc p U (crReflection R ξ) := by
  convert hξ.ite_conj hU (R.toContinuousLinearEquiv : V →L[ℝ] V) using 1
  funext z
  by_cases hz : 0 ≤ z.im
  · simp [hz]
  · simp [crReflection_of_im_neg (not_le.1 hz), hz]

/-- A leading coefficient locally `Lᵖ` up to the real axis reflects to one locally `Lᵖ` on the
doubled domain. -/
theorem MemLpLoc.crReflectionCoeff {U : Set ℂ} (hU : MapsTo (starRingEnd ℂ) U U)
    (hJ : MemLpLoc p (U ∩ {z | 0 ≤ z.im}) J) : MemLpLoc p U (crReflectionCoeff R J) := by
  convert hJ.ite_conj hU (-(R.toContinuousLinearEquiv.conjContinuousAlgEquiv.toContinuousLinearEquiv
    : (V →L[ℝ] V) →L[ℝ] V →L[ℝ] V)) using 1
  funext z
  by_cases hz : 0 ≤ z.im
  · simp [hz]
  · ext v
    simp [crReflectionCoeff_apply_of_im_neg (not_le.1 hz), hz]

/-- A derivative field locally `Lᵖ` up to the real axis reflects to one locally `Lᵖ` on the
doubled domain. -/
theorem MemLpLoc.crReflectionDeriv {U : Set ℂ} (hU : MapsTo (starRingEnd ℂ) U U)
    (hDJ : MemLpLoc p (U ∩ {z | 0 ≤ z.im}) DJ) : MemLpLoc p U (crReflectionDeriv R DJ) := by
  convert hDJ.ite_conj hU (-((ContinuousLinearMap.compL ℝ ℂ (V →L[ℝ] V) (V →L[ℝ] V)
    (R.toContinuousLinearEquiv.conjContinuousAlgEquiv.toContinuousLinearEquiv :
      (V →L[ℝ] V) →L[ℝ] V →L[ℝ] V)).comp ((ContinuousLinearMap.compL ℝ ℂ ℂ (V →L[ℝ] V)).flip
        (conjCLE : ℂ →L[ℝ] ℂ)))) using 1
  funext z
  by_cases hz : 0 ≤ z.im
  · simp [hz]
  · ext h v
    simp [crReflectionDeriv_apply_of_im_neg (not_le.1 hz), hz]

/-- A zeroth-order coefficient locally `Lᵖ` up to the real axis reflects to one locally `Lᵖ` on
the doubled domain. -/
theorem MemLpLoc.crReflectionZeroth {U : Set ℂ} (hU : MapsTo (starRingEnd ℂ) U U)
    (hS : MemLpLoc p (U ∩ {z | 0 ≤ z.im}) S) : MemLpLoc p U (crReflectionZeroth R S) := by
  convert hS.ite_conj hU (R.toContinuousLinearEquiv.conjContinuousAlgEquiv.toContinuousLinearEquiv
    : (V →L[ℝ] V) →L[ℝ] V →L[ℝ] V) using 1
  funext z
  by_cases hz : 0 ≤ z.im
  · simp [hz]
  · ext v
    simp [crReflectionZeroth_apply_of_im_neg (not_le.1 hz), hz]

/-- A field locally integrable up to the real axis reflects to a locally integrable field on the
doubled domain. -/
theorem locallyIntegrableOn_crReflection (hΩ : MapsTo (starRingEnd ℂ) Ω Ω)
    (hη : LocallyIntegrableOn η ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})) :
    LocallyIntegrableOn (crReflection R η) Ω :=
  (memLpLoc_one_iff_locallyIntegrableOn Ω.isOpen.isLocallyClosed).1
    (((memLpLoc_one_iff_locallyIntegrableOn
      (Ω.isOpen.isLocallyClosed_inter_setOfPred_le_im 0)).2 hη).crReflection R hΩ)

end Integrability

variable [CompleteSpace V]

/-! ### The reflection theorem -/

section Reflection

variable (hR : ∀ v, R (R v) = v)
include hR

/-- The test function `z ↦ R φ(conj z)` on a conjugation-invariant open set. -/
private def reflectTest (hΩ : MapsTo (starRingEnd ℂ) Ω Ω) (φ : 𝓓(Ω, V)) : 𝓓(Ω, V) :=
  TestFunction.postcompCLM (R.toContinuousLinearEquiv : V →L[ℝ] V) (TestFunction.compConj hΩ φ)

omit [CompleteSpace V] hR in
private theorem reflectTest_apply (hΩ : MapsTo (starRingEnd ℂ) Ω Ω) (φ : 𝓓(Ω, V)) (z : ℂ) :
    (reflectTest (R := R) hΩ φ : ℂ → V) z = R ((φ : ℂ → V) (conj z)) := by
  simp [reflectTest]

omit [CompleteSpace V] hR in
private theorem fderiv_reflectTest (hΩ : MapsTo (starRingEnd ℂ) Ω Ω) (φ : 𝓓(Ω, V)) (z v : ℂ) :
    fderiv ℝ (reflectTest (R := R) hΩ φ : ℂ → V) z v =
      R (fderiv ℝ (φ : ℂ → V) (conj z) (conj v)) := by
  have hφ := (TestFunction.compConj hΩ φ).contDiff.differentiable (by simp) z
  have h : (reflectTest (R := R) hΩ φ : ℂ → V) =
      (R.toContinuousLinearEquiv : V →L[ℝ] V) ∘ (TestFunction.compConj hΩ φ : ℂ → V) := by
    simp [reflectTest]
  rw [h, fderiv_comp z (ContinuousLinearMap.differentiableAt _) hφ, ContinuousLinearMap.fderiv,
    ContinuousLinearMap.comp_apply, TestFunction.fderiv_compConj_apply]
  simp

/-- **The pointwise reflection identity.** At a point `z` of the open upper half-plane, the
doubled pairing at `z` and at `conj z` adds up to the pairing of the formal adjoint of
`φ + R φ(conj ·)` with `ξ` at `z`. -/
private theorem inner_crFormalAdjoint_crReflection_add (hΩ : MapsTo (starRingEnd ℂ) Ω Ω)
    (φ : 𝓓(Ω, V)) {z : ℂ} (hz : 0 < z.im) :
    ⟪crFormalAdjoint (crReflectionCoeff R J) (crReflectionDeriv R DJ) (crReflectionZeroth R S)
        φ z, crReflection R ξ z⟫_ℝ +
      ⟪crFormalAdjoint (crReflectionCoeff R J) (crReflectionDeriv R DJ) (crReflectionZeroth R S)
        φ (conj z), crReflection R ξ (conj z)⟫_ℝ =
      ⟪crFormalAdjoint J DJ S (φ + reflectTest (R := R) hΩ φ : 𝓓(Ω, V)) z, ξ z⟫_ℝ := by
  have hz' : (conj z).im < 0 := by simpa using hz
  have hd (v : ℂ) : fderiv ℝ ((φ + reflectTest (R := R) hΩ φ : 𝓓(Ω, V)) : ℂ → V) z v =
      fderiv ℝ (φ : ℂ → V) z v + R (fderiv ℝ (φ : ℂ → V) (conj z) (conj v)) := by
    rw [FunLike.coe_add, fderiv_add (φ.contDiff.differentiable (by simp) z)
      ((reflectTest hΩ φ).contDiff.differentiable (by simp) z),
      add_apply, fderiv_reflectTest]
  rw [inner_crFormalAdjoint, inner_crFormalAdjoint, inner_crFormalAdjoint, hd, hd]
  simp only [crReflection_of_im_nonneg hz.le, crReflectionCoeff_of_im_nonneg hz.le,
    crReflectionDeriv_of_im_nonneg hz.le, crReflectionZeroth_of_im_nonneg hz.le,
    crReflection_of_im_neg hz', crReflectionCoeff_apply_of_im_neg hz',
    crReflectionDeriv_apply_of_im_neg hz', crReflectionZeroth_apply_of_im_neg hz', conj_conj,
    FunLike.coe_add, Pi.add_apply, reflectTest_apply, conj_I, map_one, map_neg, neg_apply,
    LinearIsometryEquiv.symm_apply_apply, inner_add_left, inner_neg_right, inner_neg_left]
  have hadj (v w : V) : ⟪R v, w⟫_ℝ = ⟪v, R w⟫_ℝ := by
    rw [R.inner_map_eq_flip, R.symm_apply_eq.2 (hR w).symm]
  simp only [← hadj]
  ring

/-- **Order-zero reflection for rough Cauchy–Riemann equations.** Let `Ω`
be invariant under conjugation, `R` an isometric involution of `V` whose fixed vectors lie in
the boundary subspace `Λ`, and `J`, `DJ`, `S` locally `Lᵖ` up to the real axis with
`1/p + 1/q ≤ 1`. If `ξ` is a weak solution up to the real axis of `∂_s ξ + J ∂_t ξ + S ξ = η`
with boundary subspace `Λ`, then its reflection `TauCeti.crReflection R ξ` is a weak solution on
all of `Ω` of the equation with reflected coefficients and right-hand side. -/
theorem IsWeakCRSolutionHalf.isWeakCRSolution_crReflection
    (h : IsWeakCRSolutionHalf q Ω Λ J DJ S ξ η) (hΩ : MapsTo (starRingEnd ℂ) Ω Ω)
    (hΛ : ∀ v, R v = v → v ∈ Λ) (hJ : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) J)
    (hDJ : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) DJ)
    (hS : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) S) (hpq : p⁻¹ + q⁻¹ ≤ 1) :
    IsWeakCRSolution q Ω (crReflectionCoeff R J) (crReflectionDeriv R DJ)
      (crReflectionZeroth R S) (crReflection R ξ) (crReflection R η) := by
  have hH : MeasurableSet {z : ℂ | 0 < z.im} := measurableSet_lt measurable_const measurable_im
  have hξ := h.memLpLoc.crReflection R hΩ
  have hη := locallyIntegrableOn_crReflection R hΩ h.locallyIntegrableOn
  have hint (φ : 𝓓(Ω, V)) := integrable_inner_crFormalAdjoint_of_memLpLoc
    (hJ.crReflectionCoeff R hΩ) (hDJ.crReflectionDeriv R hΩ) (hS.crReflectionZeroth R hΩ) hpq hξ φ
  refine isWeakCRSolution_iff.2 ⟨hξ, hη, fun φ => ⟨hint φ, ?_⟩⟩
  -- `φ + R φ(conj ·)` takes values in the fixed space of `R` on the real axis.
  have hψΛ (s : ℝ) : ((φ + reflectTest (R := R) hΩ φ : 𝓓(Ω, V)) : ℂ → V) s ∈ Λ := by
    refine hΛ _ ?_
    simp only [FunLike.coe_add, Pi.add_apply, reflectTest_apply, conj_ofReal, map_add, hR]
    exact add_comm _ _
  rw [Complex.integral_eq_setIntegral_add_comp_conj (hint φ),
    Complex.integral_eq_setIntegral_add_comp_conj (φ.integrable_inner hη),
    setIntegral_congr_fun hH fun z hz => inner_crFormalAdjoint_crReflection_add hR hΩ φ hz,
    h.setIntegral_inner_crFormalAdjoint _ hψΛ]
  refine setIntegral_congr_fun hH fun z hz => ?_
  have hz0 : 0 < z.im := hz.out
  have hz' : (conj z).im < 0 := by simpa using hz0
  simp only [FunLike.coe_add, Pi.add_apply, reflectTest_apply, crReflection_of_im_nonneg hz0.le,
    crReflection_of_im_neg hz', conj_conj, inner_add_left, R.inner_map_eq_flip,
    R.symm_apply_eq.2 (hR _).symm]

/-! ### Regularity up to the boundary -/

/-- **`W^{1,r}` regularity up to the real axis** (McDuff–Salamon, Lemma B.4.6 with a totally real
boundary condition). Let `Ω` be invariant under conjugation, `R` an isometric involution of the
finite-dimensional space `V` whose fixed vectors lie in `Λ`, and suppose that the reflected
coefficients are Sobolev coefficients on `Ω` for some `p > 2`, with `J² = -1` almost everywhere
on `Ω ∩ {0 ≤ t}`. If `ξ ∈ L^q_loc` is a weak solution up to the real axis with `1/p + 1/q < 1`,
and `η ∈ Lʳ_loc` up to the axis with `1 < r ≤ p` finite, then `ξ ∈ W^{1,r}_loc(Ω ∩ {0 ≤ t})`. -/
theorem IsWeakCRSolutionHalf.memWkpLoc_one [FiniteDimensional ℝ V]
    (h : IsWeakCRSolutionHalf q Ω Λ J DJ S ξ η) (hΩ : MapsTo (starRingEnd ℂ) Ω Ω)
    (hΛ : ∀ v, R v = v → v ∈ Λ)
    (hc : IsSobolevCRCoefficients p Ω (crReflectionCoeff R J) (crReflectionDeriv R DJ)
      (crReflectionZeroth R S))
    (hp : 2 < p) (hJ2 : ∀ᵐ z ∂volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}), J z * J z = -1)
    (hpq : p⁻¹ + q⁻¹ < 1) (hr : 1 < r) (hr_top : r ≠ ⊤) (hrp : r ≤ p)
    (hη : MemLpLoc r ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) η) :
    MemWkpLoc r ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) 1 ξ := by
  have hsub : (Ω : Set ℂ) ∩ {z | 0 ≤ z.im} ⊆ Ω := inter_subset_left
  have hw := h.isWeakCRSolution_crReflection hR hΩ hΛ
    (hc.memLpLoc_coeff.congr_mono (fun _ hz => (crReflectionCoeff_of_im_nonneg hz.2).symm) hsub)
    (hc.memLpLoc_deriv.congr_mono (fun _ hz => (crReflectionDeriv_of_im_nonneg hz.2).symm) hsub)
    (hc.memLpLoc_zeroth.congr_mono (fun _ hz => (crReflectionZeroth_of_im_nonneg hz.2).symm)
      hsub) hpq.le
  -- The reflected coefficient squares to `-1`: below the axis it squares to `R J² R = -R² = -1`.
  have hJ2' : ∀ᵐ z ∂volume, z ∈ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im} → J z * J z = -1 :=
    (ae_restrict_iff' (Ω.isOpen.measurableSet.inter
      (measurableSet_le measurable_const measurable_im))).1 hJ2
  have hJ2c := conjLIE.measurePreserving.quasiMeasurePreserving.ae hJ2'
  have hJJ : ∀ᵐ z ∂volume.restrict Ω,
      crReflectionCoeff R J z * crReflectionCoeff R J z = -1 := by
    refine (ae_restrict_iff' Ω.isOpen.measurableSet).2 ?_
    filter_upwards [hJ2', hJ2c] with z hz hzc hzΩ
    rcases le_or_gt 0 z.im with h0 | h0
    · rw [crReflectionCoeff_of_im_nonneg h0]
      exact hz ⟨hzΩ, h0⟩
    · have hJz := hzc ⟨hΩ hzΩ, by simpa using h0.le⟩
      simp only [conjLIE_apply] at hJz
      exact crReflectionCoeff_mul_self_of_im_neg h0 hJz
  have hηR : MemLpLoc r Ω (crReflection R η) := hη.crReflection R hΩ
  exact (hw.memWkpLoc_one_of_le hc hp hJJ hpq hr hr_top hrp hηR).congr_mono
    (eqOn_crReflection R ξ Ω).symm hsub

end Reflection

/-! ### The constant structure `J = i` with real boundary values -/

/-- For `J = i` and `R = conj` on `V = ℂ`, the reflected coefficient is `i` again. -/
theorem crReflectionCoeff_conj_I :
    crReflectionCoeff conjLIE (fun _ => I • ContinuousLinearMap.id ℝ ℂ) =
      fun _ => I • ContinuousLinearMap.id ℝ ℂ := by
  funext z
  rcases le_or_gt 0 z.im with hz | hz
  · exact crReflectionCoeff_of_im_nonneg hz
  · ext v
    simp [crReflectionCoeff_apply_of_im_neg hz]

/-- **Check.** The reflection of the real-boundary solution `ξ = z` by `R = conj` is `z` on the
whole plane: below the axis, `ξ(conj z)` conjugated is `z`. -/
theorem crReflection_conj_id : crReflection conjLIE id = id := by
  funext z
  rcases le_or_gt 0 z.im with hz | hz
  · exact crReflection_of_im_nonneg hz
  · rw [crReflection_of_im_neg hz]
    simp

/-- **Check.** The even reflection of `ξ = z`, without `R`, is `s + i|t|`, which differs from `z`
below the axis: the conjugation is what makes the doubled function holomorphic. -/
theorem crReflection_refl_id_ne {z : ℂ} (hz : z.im < 0) :
    crReflection (LinearIsometryEquiv.refl ℝ ℂ) id z ≠ z := by
  rw [crReflection_of_im_neg hz]
  intro h
  have := congrArg Complex.im h
  simp only [LinearIsometryEquiv.coe_refl, id_eq, conj_im] at this
  linarith

/-- **`W^{1,r}` regularity up to the real axis for `J = i`.** On a conjugation-invariant open set,
a locally `L^q` weak solution up to the real axis of `∂_s ξ + i ∂_t ξ = η` with real boundary
values, for `1 < q` and `η ∈ Lʳ_loc` up to the axis with `1 < r < ∞`, lies in
`W^{1,r}_loc(Ω ∩ {0 ≤ t})`. -/
theorem IsWeakCRSolutionHalf.memWkpLoc_one_of_I {ξ η : ℂ → ℂ}
    (h : IsWeakCRSolutionHalf q Ω (Submodule.span ℝ {(1 : ℂ)})
      (fun _ => I • ContinuousLinearMap.id ℝ ℂ) 0 0 ξ η)
    (hΩ : MapsTo (starRingEnd ℂ) Ω Ω) (hq : 1 < q) (hr : 1 < r) (hr_top : r ≠ ⊤)
    (hη : MemLpLoc r ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) η) :
    MemWkpLoc r ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) 1 ξ := by
  -- The coefficients are bounded, so the exponent `p = ∞` applies.
  have hc : IsSobolevCRCoefficients ⊤ Ω
      (crReflectionCoeff conjLIE fun _ => I • ContinuousLinearMap.id ℝ ℂ)
      (crReflectionDeriv conjLIE 0) (crReflectionZeroth conjLIE 0) := by
    rw [crReflectionCoeff_conj_I, crReflectionDeriv_zero, crReflectionZeroth_zero]
    simpa [fderiv_const] using IsSobolevCRCoefficients.of_contDiffOn
      (J := fun _ => I • ContinuousLinearMap.id ℝ ℂ) (S := 0) contDiffOn_const continuousOn_const ⊤
  have hR (v : ℂ) : conjLIE (conjLIE v) = v := by simp
  have hΛ (v : ℂ) (hv : conjLIE v = v) : v ∈ Submodule.span ℝ {(1 : ℂ)} :=
    Submodule.mem_span_singleton.2 ⟨v.re, by
      simpa [Complex.real_smul] using Complex.conj_eq_iff_re.1 (by simpa using hv)⟩
  have hJ2 : ∀ᵐ z ∂volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}),
      (fun _ => I • ContinuousLinearMap.id ℝ ℂ) z * (fun _ => I • ContinuousLinearMap.id ℝ ℂ) z =
        (-1 : ℂ →L[ℝ] ℂ) := .of_forall fun _ => by
    ext v
    simp [← mul_assoc]
  have hpq : (⊤ : ℝ≥0∞)⁻¹ + q⁻¹ < 1 := by simpa [ENNReal.inv_lt_one] using hq
  exact h.memWkpLoc_one hR hΩ hΛ hc (by simp) hJ2 hpq hr hr_top le_top hη

end TauCeti
