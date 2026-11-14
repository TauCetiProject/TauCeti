/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.Weak
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import TauCeti.Analysis.Distribution.TestFunction.LinearEquiv
import TauCeti.Analysis.Sobolev.Local.ChangeOfVariables

/-!
# The formal adjoint of a real Cauchy–Riemann operator as a Cauchy–Riemann operator

Let `Ω ⊆ ℂ` be open, write `z = s + i t`, and let `V` be a real Hilbert space
(finite-dimensional in the applications). The real Cauchy–Riemann operator
`D φ = ∂_s φ + J ∂_t φ + S φ` with Sobolev coefficients has formal adjoint
`D* η = -∂_s η - Jᵀ ∂_t η - (∂_t J)ᵀ η + Sᵀ η`, an operator of `∂`-type: the sign of `∂_s` is
reversed. Precomposing with the reflection `ρ z = -conj z`, that is
`(s, t) ↦ (-s, t)`, turns it back into an operator of the form `∂_s + J' ∂_t + S'`, with

* `J' z = -(J (ρ z))ᵀ`,
* `S' z = (S (ρ z))ᵀ - (∂_t J (ρ z))ᵀ`,
* `DJ' z v = -(DJ (ρ z) (ρ v))ᵀ`, the weak derivative of `J'` by the chain rule.

The defining identity is `D'* (φ ∘ ρ) = (D φ) ∘ ρ` (`TauCeti.crFormalAdjoint_crReflectedAdjoint`):
the term `-(∂_t J')ᵀ` of `D'*` is `∂_t J ∘ ρ`, and the correction `-(∂_t J)ᵀ` in `S'` cancels it.
Since `ρ` preserves Lebesgue measure, a locally `L^q` field `η` satisfies
`∫ ⟪D φ, η⟫ = ∫ ⟪φ, ζ⟫` for every test function `φ` on `Ω` exactly when `η ∘ ρ` is a weak
solution of `D' (η ∘ ρ) = ζ ∘ ρ` on `ρ⁻¹ Ω` in the sense of `TauCeti.IsWeakCRSolution`. In
particular an element annihilating the range of `D` on test functions is, after reflection, a weak
solution of a homogeneous real Cauchy–Riemann equation with Sobolev coefficients, so the interior
regularity theory of such equations applies to it. The reflection `ρ` preserves the closed upper
half-plane, which is what makes it suitable for boundary problems as well.

## Main declarations

* `TauCeti.crReflectedAdjointCoeff`, `TauCeti.crReflectedAdjointDeriv`,
  `TauCeti.crReflectedAdjointZeroth`: the coefficients `J'`, `DJ'` and `S'`.
* `TauCeti.fderiv_crReflectedAdjointCoeff`: `DJ'` is the derivative of `J'` when `DJ` is that
  of `J`; `TauCeti.crReflectedAdjointCoeff_crReflectedAdjointCoeff` and its companions: the
  reflected adjoint is an involution on coefficient triples.
* `TauCeti.crFormalAdjoint_crReflectedAdjoint`: `D'* (φ ∘ ρ) = (D φ) ∘ ρ`.
* `TauCeti.HasWeakFDerivOn.crReflectedAdjoint`, `TauCeti.MemWkpLoc.crReflectedAdjointCoeff`,
  `ContDiffOn.crReflectedAdjointCoeff` and their analogues for `DJ'` and `S'`: weak derivatives,
  local Sobolev classes of every order and smoothness transfer to the reflected coefficients.
* `TauCeti.IsSobolevCRCoefficients.crReflectedAdjoint`: Sobolev coefficients transfer to
  `(J', DJ', S')` on every open set mapped into `Ω` by `ρ`.
* `TauCeti.crReflectedAdjointCoeff_mul_self_eq_neg_one_iff`: `J'² = -1` exactly when
  `J² = -1` at the reflected point; `TauCeti.crReflectedAdjointCoeff_eq_of_adjoint_mul_self`:
  `J' = J ∘ ρ` for orthogonal complex structures `J`.
* The weak equation for the adjoint, after reflection:
  `IsSobolevCRCoefficients.forall_integral_inner_eq_iff_isWeakCRSolution_crReflectedAdjoint`;
  `TauCeti.IsSobolevCRCoefficients.forall_integral_inner_eq_zero_iff` is its homogeneous case,
  the annihilator of the range.
* `TauCeti.crReflectedAdjointCoeff_mul_I`,
  `TauCeti.integral_inner_fderiv_add_I_mul_fderiv_conj_eq_zero`: for
  `J = i` the reflected coefficient is `i` again, and `η = conj` annihilates the range of
  `∂_s + i ∂_t`, since `η ∘ ρ = -id` is holomorphic.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix C.1 and the proof of Theorem C.2.3.
-/

public noncomputable section

open MeasureTheory TopologicalSpace Complex Set
open scoped InnerProductSpace ComplexConjugate Distributions ENNReal

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  {Ω Ω' : Opens ℂ} {p q : ℝ≥0∞}
  {J S : ℂ → V →L[ℝ] V} {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V}

/-- The reflection `z ↦ -conj z` across the imaginary axis, as a real-linear equivalence. -/
private def negConj : ℂ ≃L[ℝ] ℂ := Complex.conjCLE.trans (ContinuousLinearEquiv.neg ℝ)

private theorem negConj_apply (z : ℂ) : negConj z = -conj z := by
  simp [negConj]

/-- The Hilbert adjoint on `V →L[ℝ] V`, as a real-linear equivalence. -/
private def adjointCLE : (V →L[ℝ] V) ≃L[ℝ] V →L[ℝ] V :=
  (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := V) (F := V)).toContinuousLinearEquiv

private theorem adjointCLE_apply (A : V →L[ℝ] V) :
    adjointCLE A = ContinuousLinearMap.adjoint A := by
  simp [adjointCLE]

private theorem negConj_symm_apply (z : ℂ) : negConj.symm z = -conj z := by
  rw [ContinuousLinearEquiv.symm_apply_eq, negConj_apply, map_neg, conj_conj, neg_neg]

private theorem negConj_negConj (z : ℂ) : -conj (-conj z) = z := by
  rw [map_neg, conj_conj, neg_neg]

/-- The reflection `z ↦ -conj z` preserves Lebesgue integrals. -/
private theorem integral_comp_negConj {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℂ → E) : ∫ z, g (-conj z) = ∫ z, g z := by
  simpa using integral_comp (Complex.conjLIE.trans (LinearIsometryEquiv.neg ℝ (E := ℂ))) g

/-! ### The reflected adjoint coefficients -/

/-- The coefficient `J' z = -(J (-conj z))ᵀ` of the reflected formal adjoint of
`∂_s + J ∂_t + S`, with `ᵀ` the Hilbert adjoint. -/
def crReflectedAdjointCoeff (J : ℂ → V →L[ℝ] V) (z : ℂ) : V →L[ℝ] V :=
  -ContinuousLinearMap.adjoint (J (-conj z))

/-- The weak derivative `DJ' z v = -(DJ (-conj z) (-conj v))ᵀ` of the reflected adjoint
coefficient `TauCeti.crReflectedAdjointCoeff J`, by the chain rule from a weak derivative `DJ` of
`J`. -/
def crReflectedAdjointDeriv (DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V) (z : ℂ) : ℂ →L[ℝ] V →L[ℝ] V :=
  -((adjointCLE (V := V) : (V →L[ℝ] V) →L[ℝ] V →L[ℝ] V).comp
    ((DJ (-conj z)).comp (negConj : ℂ →L[ℝ] ℂ)))

/-- The zeroth-order coefficient `S' z = (S (-conj z))ᵀ - (DJ (-conj z) I)ᵀ` of the reflected
formal adjoint of `∂_s + J ∂_t + S`. The second term cancels the derivative of `J'` in the formal
adjoint of `∂_s + J' ∂_t + S'`. -/
def crReflectedAdjointZeroth (DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V) (S : ℂ → V →L[ℝ] V) (z : ℂ) :
    V →L[ℝ] V :=
  ContinuousLinearMap.adjoint (S (-conj z)) - ContinuousLinearMap.adjoint (DJ (-conj z) I)

theorem crReflectedAdjointCoeff_apply (z : ℂ) :
    crReflectedAdjointCoeff J z = -ContinuousLinearMap.adjoint (J (-conj z)) := (rfl)

theorem crReflectedAdjointDeriv_apply (z v : ℂ) :
    crReflectedAdjointDeriv DJ z v = -ContinuousLinearMap.adjoint (DJ (-conj z) (-conj v)) := by
  simp [crReflectedAdjointDeriv, adjointCLE_apply, negConj_apply]

theorem crReflectedAdjointZeroth_apply (z : ℂ) :
    crReflectedAdjointZeroth DJ S z =
      ContinuousLinearMap.adjoint (S (-conj z)) - ContinuousLinearMap.adjoint (DJ (-conj z) I) :=
  (rfl)

/-- `J'` is `J` precomposed with the reflection and postcomposed with the negated adjoint. -/
private theorem crReflectedAdjointCoeff_eq_comp (J : ℂ → V →L[ℝ] V) :
    crReflectedAdjointCoeff J = fun z => -adjointCLE (J (negConj z)) := by
  funext z
  simp [crReflectedAdjointCoeff_apply, adjointCLE_apply, negConj_apply]

/-- `DJ'` is `DJ` precomposed with the reflection in both arguments and postcomposed with the
negated adjoint. -/
private theorem crReflectedAdjointDeriv_eq_comp (DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V) :
    crReflectedAdjointDeriv DJ = fun z =>
      -(adjointCLE (V := V) : (V →L[ℝ] V) →L[ℝ] V →L[ℝ] V).comp
        ((DJ (negConj z)).comp (negConj : ℂ →L[ℝ] ℂ)) := by
  funext z
  ext v : 1
  simp [crReflectedAdjointDeriv_apply, adjointCLE_apply, negConj_apply]

/-- `S'` is assembled from `S` and `DJ` precomposed with the reflection and the adjoint. -/
private theorem crReflectedAdjointZeroth_eq_comp (DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V)
    (S : ℂ → V →L[ℝ] V) :
    crReflectedAdjointZeroth DJ S = fun z =>
      adjointCLE (S (negConj z)) - adjointCLE (DJ (negConj z) I) := by
  funext z
  simp [crReflectedAdjointZeroth_apply, adjointCLE_apply, negConj_apply]

@[simp]
theorem crReflectedAdjointCoeff_zero : crReflectedAdjointCoeff (0 : ℂ → V →L[ℝ] V) = 0 := by
  funext z
  simp [crReflectedAdjointCoeff_apply]

@[simp]
theorem crReflectedAdjointDeriv_zero :
    crReflectedAdjointDeriv (0 : ℂ → ℂ →L[ℝ] V →L[ℝ] V) = 0 := by
  funext z
  ext v : 1
  simp [crReflectedAdjointDeriv_apply]

@[simp]
theorem crReflectedAdjointZeroth_zero :
    crReflectedAdjointZeroth (0 : ℂ → ℂ →L[ℝ] V →L[ℝ] V) (0 : ℂ → V →L[ℝ] V) = 0 := by
  funext z
  simp [crReflectedAdjointZeroth_apply]

/-- Reflecting the adjoint twice recovers the coefficient: `J'' = J`. -/
@[simp]
theorem crReflectedAdjointCoeff_crReflectedAdjointCoeff (J : ℂ → V →L[ℝ] V) :
    crReflectedAdjointCoeff (crReflectedAdjointCoeff J) = J := by
  funext z
  simp [crReflectedAdjointCoeff_apply]

/-- Reflecting the adjoint twice recovers the derivative: `DJ'' = DJ`. -/
@[simp]
theorem crReflectedAdjointDeriv_crReflectedAdjointDeriv (DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V) :
    crReflectedAdjointDeriv (crReflectedAdjointDeriv DJ) = DJ := by
  funext z
  ext v : 1
  simp [crReflectedAdjointDeriv_apply]

/-- Reflecting the adjoint twice recovers the zeroth-order coefficient: `S'' = S`, the two
corrections by `∂_t J` cancelling. -/
@[simp]
theorem crReflectedAdjointZeroth_crReflectedAdjointDeriv_crReflectedAdjointZeroth
    (DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V) (S : ℂ → V →L[ℝ] V) :
    crReflectedAdjointZeroth (crReflectedAdjointDeriv DJ) (crReflectedAdjointZeroth DJ S) = S := by
  funext z
  simp [crReflectedAdjointZeroth_apply, crReflectedAdjointDeriv_apply]

/-- The reflected adjoint derivative of the Fréchet derivative of `J` is the Fréchet derivative of
the reflected adjoint coefficient. -/
theorem fderiv_crReflectedAdjointCoeff (J : ℂ → V →L[ℝ] V) :
    fderiv ℝ (crReflectedAdjointCoeff J) = crReflectedAdjointDeriv (fderiv ℝ J) := by
  have h : crReflectedAdjointCoeff J =
      (adjointCLE.trans (ContinuousLinearEquiv.neg ℝ)) ∘ (J ∘ negConj) := by
    simp [crReflectedAdjointCoeff_eq_comp, Function.comp_def]
  funext z
  rw [h, ContinuousLinearEquiv.comp_fderiv, ContinuousLinearEquiv.comp_right_fderiv,
    crReflectedAdjointDeriv_eq_comp]
  ext v : 1
  simp

/-- **The reflected adjoint identity.** The formal adjoint of `∂_s + J' ∂_t + S'` applied to
`φ ∘ ρ`, with `ρ z = -conj z`, is `(∂_s φ + J ∂_t φ + S φ) ∘ ρ`. This holds for every
`φ : ℂ → V` and arbitrary coefficient fields. -/
@[simp]
theorem crFormalAdjoint_crReflectedAdjoint (φ : ℂ → V) (z : ℂ) :
    crFormalAdjoint (crReflectedAdjointCoeff J) (crReflectedAdjointDeriv DJ)
        (crReflectedAdjointZeroth DJ S) (fun z => φ (-conj z)) z =
      fderiv ℝ φ (-conj z) 1 + J (-conj z) (fderiv ℝ φ (-conj z) I) +
        S (-conj z) (φ (-conj z)) := by
  have hφ : fderiv ℝ (fun z => φ (-conj z)) z =
      (fderiv ℝ φ (-conj z)).comp (negConj : ℂ →L[ℝ] ℂ) := by
    simpa only [Function.comp_def, negConj_apply] using negConj.comp_right_fderiv (f := φ) (x := z)
  simp only [crFormalAdjoint_def, hφ, crReflectedAdjointCoeff_apply, crReflectedAdjointDeriv_apply,
    crReflectedAdjointZeroth_apply, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    negConj_apply, map_neg, map_sub, ContinuousLinearMap.adjoint_adjoint, conj_I, map_one,
    neg_neg, neg_apply, sub_apply]
  abel

/-- The integral form of `TauCeti.crFormalAdjoint_crReflectedAdjoint`: since `ρ z = -conj z`
preserves Lebesgue measure, pairing the reflected adjoint of `φ ∘ ρ` with `η ∘ ρ` integrates to
the pairing of `∂_s φ + J ∂_t φ + S φ` with `η`. -/
theorem integral_inner_crFormalAdjoint_crReflectedAdjoint (φ η : ℂ → V) :
    ∫ z, ⟪crFormalAdjoint (crReflectedAdjointCoeff J) (crReflectedAdjointDeriv DJ)
        (crReflectedAdjointZeroth DJ S) (fun z => φ (-conj z)) z, η (-conj z)⟫_ℝ =
      ∫ z, ⟪fderiv ℝ φ z 1 + J z (fderiv ℝ φ z I) + S z (φ z), η z⟫_ℝ := by
  simp only [crFormalAdjoint_crReflectedAdjoint]
  exact integral_comp_negConj (fun w => ⟪fderiv ℝ φ w 1 + J w (fderiv ℝ φ w I) + S w (φ w), η w⟫_ℝ)

/-! ### Algebraic properties of the reflected coefficient -/

/-- `J'² = -1` at `z` exactly when `J² = -1` at the reflected point `-conj z`. -/
@[simp]
theorem crReflectedAdjointCoeff_mul_self_eq_neg_one_iff (z : ℂ) :
    crReflectedAdjointCoeff J z * crReflectedAdjointCoeff J z = -1 ↔
      J (-conj z) * J (-conj z) = -1 := by
  rw [← (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := V) (F := V)).injective.eq_iff]
  simp [crReflectedAdjointCoeff_apply, ContinuousLinearMap.mul_def,
    ← ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.one_def,
    ContinuousLinearMap.adjoint_id]

/-- For an orthogonal complex structure, `J' = J ∘ ρ`: if `J (-conj z)` squares to `-1` and is
orthogonal, then its negative adjoint is itself. -/
theorem crReflectedAdjointCoeff_eq_of_adjoint_mul_self {z : ℂ}
    (h₂ : J (-conj z) * J (-conj z) = -1)
    (ho : ContinuousLinearMap.adjoint (J (-conj z)) * J (-conj z) = 1) :
    crReflectedAdjointCoeff J z = J (-conj z) := by
  rw [crReflectedAdjointCoeff_apply, neg_eq_iff_eq_neg]
  calc ContinuousLinearMap.adjoint (J (-conj z))
      = ContinuousLinearMap.adjoint (J (-conj z)) * -(J (-conj z) * J (-conj z)) := by
        rw [h₂, neg_neg, mul_one]
    _ = -J (-conj z) := by rw [mul_neg, ← mul_assoc, ho, one_mul]

/-! ### Sobolev coefficients -/

/-- Weak derivatives transfer to the reflected adjoint coefficients: if `DJ` is a weak derivative
of `J` on `Ω` and `ρ z = -conj z` maps `Ω'` into `Ω`, then `DJ'` is a weak derivative of `J'` on
`Ω'`. -/
theorem HasWeakFDerivOn.crReflectedAdjoint (hJ : HasWeakFDerivOn volume Ω J DJ)
    (hΩ : MapsTo (fun z : ℂ => -conj z) Ω' Ω) :
    HasWeakFDerivOn volume Ω' (crReflectedAdjointCoeff J) (crReflectedAdjointDeriv DJ) := by
  rw [crReflectedAdjointCoeff_eq_comp, crReflectedAdjointDeriv_eq_comp]
  simpa using (hJ.comp_continuousLinearEquiv_add negConj 0
    (by simpa [negConj_apply] using hΩ)).clm_comp
    (-(adjointCLE (V := V) : (V →L[ℝ] V) →L[ℝ] V →L[ℝ] V))

/-- Local Sobolev classes of every order transfer to the reflected adjoint coefficient: if `J` lies
in `MemWkpLoc p U k` and `ρ z = -conj z` maps `U'` into `U`, then `J'` lies in
`MemWkpLoc p U' k`. -/
theorem MemWkpLoc.crReflectedAdjointCoeff {U U' : Set ℂ} {k : ℕ} (hJ : MemWkpLoc p U k J)
    (hU : MapsTo (fun z : ℂ => -conj z) U' U) :
    MemWkpLoc p U' k (TauCeti.crReflectedAdjointCoeff J) := by
  rw [crReflectedAdjointCoeff_eq_comp]
  simpa using (hJ.comp_continuousLinearEquiv_add negConj 0
    (by simpa [negConj_apply] using hU)).clm_comp
    (-(adjointCLE (V := V) : (V →L[ℝ] V) →L[ℝ] V →L[ℝ] V))

/-- Local Sobolev classes of every order transfer to the reflected adjoint derivative, under the
hypotheses of `TauCeti.MemWkpLoc.crReflectedAdjointCoeff`. -/
theorem MemWkpLoc.crReflectedAdjointDeriv {U U' : Set ℂ} {k : ℕ} (hDJ : MemWkpLoc p U k DJ)
    (hU : MapsTo (fun z : ℂ => -conj z) U' U) :
    MemWkpLoc p U' k (TauCeti.crReflectedAdjointDeriv DJ) := by
  rw [crReflectedAdjointDeriv_eq_comp]
  simpa using ((hDJ.comp_continuousLinearEquiv_add negConj 0
    (by simpa [negConj_apply] using hU)).clm_comp (G := ℂ →L[ℝ] V →L[ℝ] V)
      ((ContinuousLinearMap.compL ℝ ℂ ℂ (V →L[ℝ] V)).flip (negConj : ℂ →L[ℝ] ℂ))).clm_comp
    (G := ℂ →L[ℝ] V →L[ℝ] V) (-ContinuousLinearMap.compL ℝ ℂ (V →L[ℝ] V) (V →L[ℝ] V)
      (adjointCLE (V := V) : (V →L[ℝ] V) →L[ℝ] V →L[ℝ] V))

/-- Local Sobolev classes of every order transfer to the reflected zeroth-order coefficient, under
the hypotheses of `TauCeti.MemWkpLoc.crReflectedAdjointCoeff` for `DJ` and `S`. -/
theorem MemWkpLoc.crReflectedAdjointZeroth {U U' : Set ℂ} {k : ℕ} (hDJ : MemWkpLoc p U k DJ)
    (hS : MemWkpLoc p U k S) (hU : MapsTo (fun z : ℂ => -conj z) U' U) :
    MemWkpLoc p U' k (TauCeti.crReflectedAdjointZeroth DJ S) := by
  have hU' : MapsTo (fun z => negConj z + 0) U' U := by simpa [negConj_apply] using hU
  rw [crReflectedAdjointZeroth_eq_comp]
  simpa [Pi.sub_def] using ((hS.comp_continuousLinearEquiv_add negConj 0 hU').clm_comp
    (adjointCLE (V := V) : (V →L[ℝ] V) →L[ℝ] V →L[ℝ] V)).sub
    ((hDJ.comp_continuousLinearEquiv_add negConj 0 hU').clm_comp
      ((adjointCLE (V := V) : (V →L[ℝ] V) →L[ℝ] V →L[ℝ] V) ∘L
        ContinuousLinearMap.apply ℝ (V →L[ℝ] V) I))

/-- Sobolev coefficients transfer to the reflected adjoint coefficients: if `(J, DJ, S)` are
Sobolev coefficients on `Ω` and `ρ z = -conj z` maps `Ω'` into `Ω`, then
`(J', DJ', S')` are Sobolev coefficients on `Ω'`. -/
theorem IsSobolevCRCoefficients.crReflectedAdjoint (hc : IsSobolevCRCoefficients p Ω J DJ S)
    (hΩ : MapsTo (fun z : ℂ => -conj z) Ω' Ω) :
    IsSobolevCRCoefficients p Ω' (crReflectedAdjointCoeff J) (crReflectedAdjointDeriv DJ)
      (crReflectedAdjointZeroth DJ S) where
  hasWeakFDerivOn := hc.hasWeakFDerivOn.crReflectedAdjoint hΩ
  memLpLoc_coeff :=
    memWkpLoc_zero_iff.1 ((memWkpLoc_zero_iff.2 hc.memLpLoc_coeff).crReflectedAdjointCoeff hΩ)
  memLpLoc_deriv :=
    memWkpLoc_zero_iff.1 ((memWkpLoc_zero_iff.2 hc.memLpLoc_deriv).crReflectedAdjointDeriv hΩ)
  memLpLoc_zeroth := memWkpLoc_zero_iff.1 (MemWkpLoc.crReflectedAdjointZeroth
    (memWkpLoc_zero_iff.2 hc.memLpLoc_deriv) (memWkpLoc_zero_iff.2 hc.memLpLoc_zeroth) hΩ)

/-! ### Smoothness of the reflected coefficients -/

section ContDiffOn

variable {n : WithTop ℕ∞} {s t : Set ℂ}

/-- Smoothness transfers to the reflected adjoint coefficient: if `J` is `Cⁿ` on `s` and
`ρ z = -conj z` maps `t` into `s`, then `J'` is `Cⁿ` on `t`. -/
theorem _root_.ContDiffOn.crReflectedAdjointCoeff (hJ : ContDiffOn ℝ n J s)
    (hst : MapsTo (fun z : ℂ => -conj z) t s) :
    ContDiffOn ℝ n (crReflectedAdjointCoeff J) t := by
  rw [crReflectedAdjointCoeff_eq_comp]
  exact ((hJ.comp (n := n) negConj.contDiff.contDiffOn
    (by simpa [MapsTo, negConj_apply] using hst)).continuousLinearMap_comp
    (adjointCLE (V := V) : (V →L[ℝ] V) →L[ℝ] V →L[ℝ] V)).neg

/-- Smoothness transfers to the reflected adjoint derivative, under the hypotheses of
`ContDiffOn.crReflectedAdjointCoeff`. -/
theorem _root_.ContDiffOn.crReflectedAdjointDeriv (hDJ : ContDiffOn ℝ n DJ s)
    (hst : MapsTo (fun z : ℂ => -conj z) t s) :
    ContDiffOn ℝ n (TauCeti.crReflectedAdjointDeriv DJ) t := by
  rw [crReflectedAdjointDeriv_eq_comp]
  exact (contDiffOn_const.clm_comp ((hDJ.comp (n := n) negConj.contDiff.contDiffOn
    (by simpa [MapsTo, negConj_apply] using hst)).clm_comp contDiffOn_const)).neg

/-- Smoothness transfers to the reflected zeroth-order coefficient, under the hypotheses of
`ContDiffOn.crReflectedAdjointCoeff` for `DJ` and `S`. -/
theorem _root_.ContDiffOn.crReflectedAdjointZeroth (hDJ : ContDiffOn ℝ n DJ s)
    (hS : ContDiffOn ℝ n S s) (hst : MapsTo (fun z : ℂ => -conj z) t s) :
    ContDiffOn ℝ n (TauCeti.crReflectedAdjointZeroth DJ S) t := by
  have hst' : MapsTo negConj t s := by simpa [MapsTo, negConj_apply] using hst
  rw [crReflectedAdjointZeroth_eq_comp]
  exact (adjointCLE.contDiff.comp_contDiffOn
    (hS.comp (n := n) negConj.contDiff.contDiffOn hst')).sub
    ((adjointCLE.contDiff.comp (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) I).contDiff).comp_contDiffOn
      (hDJ.comp (n := n) negConj.contDiff.contDiffOn hst'))

end ContDiffOn

/-! ### The adjoint equation as a weak Cauchy–Riemann equation -/

/-- **The adjoint equation after reflection.** Let `(J, DJ, S)` be Sobolev coefficients on `Ω`
with `1/p + 1/q ≤ 1`, let `Ω' = ρ⁻¹ Ω` for `ρ z = -conj z`, let `η` be locally `L^q` and `ζ`
locally integrable on `Ω`. Then `∫ ⟪∂_s φ + J ∂_t φ + S φ, η⟫ = ∫ ⟪φ, ζ⟫` for every test
function `φ` on `Ω` exactly when `η ∘ ρ` is a weak solution of
`∂_s ξ + J' ∂_t ξ + S' ξ = ζ ∘ ρ` on `Ω'`. -/
theorem IsSobolevCRCoefficients.forall_integral_inner_eq_iff_isWeakCRSolution_crReflectedAdjoint
    (hc : IsSobolevCRCoefficients p Ω J DJ S) (hpq : p⁻¹ + q⁻¹ ≤ 1)
    (hΩ : ∀ z, z ∈ Ω' ↔ -conj z ∈ Ω) {η ζ : ℂ → V} (hη : MemLpLoc q Ω η)
    (hζ : LocallyIntegrableOn ζ Ω) :
    (∀ φ : 𝓓(Ω, V), ∫ z, ⟪fderiv ℝ (φ : ℂ → V) z 1 + J z (fderiv ℝ (φ : ℂ → V) z I) +
        S z ((φ : ℂ → V) z), η z⟫_ℝ = ∫ z, ⟪(φ : ℂ → V) z, ζ z⟫_ℝ) ↔
      IsWeakCRSolution q Ω' (crReflectedAdjointCoeff J) (crReflectedAdjointDeriv DJ)
        (crReflectedAdjointZeroth DJ S) (fun z => η (-conj z)) (fun z => ζ (-conj z)) := by
  have hρ : MapsTo (fun z : ℂ => -conj z) Ω' Ω := fun z hz => (hΩ z).1 hz
  have hmaps : MapsTo negConj Ω' Ω := fun z hz => by simpa [negConj_apply] using hρ hz
  have hmaps' : MapsTo negConj.symm Ω Ω' := fun z hz => (hΩ _).2 (by
    simpa [negConj_symm_apply, negConj_negConj] using hz)
  have hηρ : MemLpLoc q Ω' (fun z => η (-conj z)) := by
    simpa [negConj_apply] using
      hη.comp_continuousLinearEquiv_add negConj 0 (by simpa [negConj_apply] using hρ)
  have hζρ : LocallyIntegrableOn (fun z => ζ (-conj z)) Ω' := by
    simpa [negConj_apply] using hζ.comp_continuousLinearEquiv_of_mapsTo negConj hmaps
  have hrhs (φ : ℂ → V) : ∫ z, ⟪φ (-conj z), ζ (-conj z)⟫_ℝ = ∫ z, ⟪φ z, ζ z⟫_ℝ :=
    integral_comp_negConj (fun w => ⟪φ w, ζ w⟫_ℝ)
  simp only [isWeakCRSolution_iff, hηρ, hζρ, true_and]
  constructor
  · intro h ψ
    refine ⟨(hc.crReflectedAdjoint hρ).integrable_inner_crFormalAdjoint hpq hηρ ψ, ?_⟩
    have hψ : (ψ : ℂ → V) = fun z => (negConj.transportTestFunction hmaps ψ : ℂ → V) (-conj z) :=
      funext fun z => by simp [negConj_symm_apply]
    rw [hψ, integral_inner_crFormalAdjoint_crReflectedAdjoint, hrhs]
    exact h _
  · intro h φ
    have hψ : (negConj.symm.transportTestFunction hmaps' φ : ℂ → V) = fun z => φ (-conj z) :=
      funext fun z => by simp [negConj_apply]
    have h' := (h (negConj.symm.transportTestFunction hmaps' φ)).2
    rwa [hψ, integral_inner_crFormalAdjoint_crReflectedAdjoint, hrhs] at h'

/-- **The annihilator of the range.** Under the hypotheses of
`TauCeti.IsSobolevCRCoefficients.forall_integral_inner_eq_iff_isWeakCRSolution_crReflectedAdjoint`,
a locally `L^q` field `η` is `L²`-orthogonal to `∂_s φ + J ∂_t φ + S φ` for every test function
`φ` on `Ω` exactly when `η ∘ ρ` is a weak solution of the homogeneous equation
`∂_s ξ + J' ∂_t ξ + S' ξ = 0` on `Ω' = ρ⁻¹ Ω`. -/
theorem IsSobolevCRCoefficients.forall_integral_inner_eq_zero_iff
    (hc : IsSobolevCRCoefficients p Ω J DJ S) (hpq : p⁻¹ + q⁻¹ ≤ 1)
    (hΩ : ∀ z, z ∈ Ω' ↔ -conj z ∈ Ω) {η : ℂ → V} (hη : MemLpLoc q Ω η) :
    (∀ φ : 𝓓(Ω, V), ∫ z, ⟪fderiv ℝ (φ : ℂ → V) z 1 + J z (fderiv ℝ (φ : ℂ → V) z I) +
        S z ((φ : ℂ → V) z), η z⟫_ℝ = 0) ↔
      IsWeakCRSolution q Ω' (crReflectedAdjointCoeff J) (crReflectedAdjointDeriv DJ)
        (crReflectedAdjointZeroth DJ S) (fun z => η (-conj z)) 0 := by
  simpa [← Pi.zero_def] using
    hc.forall_integral_inner_eq_iff_isWeakCRSolution_crReflectedAdjoint hpq hΩ hη (ζ := 0)
      locallyIntegrableOn_zero

/-! ### Checks -/

/-- For the standard complex structure `J = i` on `ℂ`, the reflected adjoint coefficient is again
`i`: the adjoint of multiplication by `i` for the real inner product is multiplication by `-i`. -/
@[simp]
theorem crReflectedAdjointCoeff_mul_I :
    crReflectedAdjointCoeff (fun _ => ContinuousLinearMap.mul ℝ ℂ I) =
      fun _ => ContinuousLinearMap.mul ℝ ℂ I := by
  funext z
  rw [crReflectedAdjointCoeff_apply, neg_eq_iff_eq_neg, eq_comm,
    ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  simp [Complex.inner, mul_comm]
  ring

/-- **The annihilator of `∂_s + i ∂_t` contains `conj`.** For `J = i` and `S = 0` the operator
`∂_s + J ∂_t` is twice the Wirtinger derivative in `conj z`, and the antiholomorphic function
`η = conj` annihilates its range on test functions: `η ∘ ρ = -id` is holomorphic, so it is a weak
solution of the reflected equation, which is `∂_s + i ∂_t` again. -/
theorem integral_inner_fderiv_add_I_mul_fderiv_conj_eq_zero (Ω : Opens ℂ) (φ : 𝓓(Ω, ℂ)) :
    ∫ z, ⟪fderiv ℝ (φ : ℂ → ℂ) z 1 + I * fderiv ℝ (φ : ℂ → ℂ) z I, conj z⟫_ℝ = 0 := by
  set M : ℂ →L[ℝ] ℂ := ContinuousLinearMap.mul ℝ ℂ I
  let Ω' : Opens ℂ := ⟨(fun z : ℂ => -conj z) ⁻¹' Ω, Ω.isOpen.preimage (by fun_prop)⟩
  have hc : IsSobolevCRCoefficients 2 Ω (fun _ => M) 0 0 :=
    ⟨hasWeakFDerivOn_iff.2 fun v => hasWeakLineDerivOn_const M, memLpLoc_const M, memLpLoc_zero,
      memLpLoc_zero⟩
  have hD : crReflectedAdjointDeriv (0 : ℂ → ℂ →L[ℝ] ℂ →L[ℝ] ℂ) = fderiv ℝ fun _ : ℂ => M := by
    simp
  have key := (hc.forall_integral_inner_eq_zero_iff (q := 2)
    (by simp [ENNReal.inv_two_add_inv_two]) (Ω' := Ω') (fun z => by simp [Ω'])
    (η := fun z => conj z) continuous_conj.continuousOn.memLpLoc).2 (by
      rw [crReflectedAdjointCoeff_mul_I, hD, crReflectedAdjointZeroth_zero,
        isWeakCRSolution_iff_of_contDiffOn contDiffOn_const continuous_zero.continuousOn
        (by simpa only [map_neg, conj_conj] using contDiff_neg.contDiffOn)
        continuous_zero.continuousOn]
      intro z _
      simp only [map_neg, conj_conj]
      rw [fderiv_fun_neg (f := fun z : ℂ => z), fderiv_fun_id]
      simp)
  simpa [M] using key φ

end TauCeti
