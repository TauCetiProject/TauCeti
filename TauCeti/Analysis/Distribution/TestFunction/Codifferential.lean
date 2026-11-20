/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import TauCeti.Analysis.Distribution.TestFunction.ExtDeriv
public import TauCeti.Analysis.InnerProductSpace.HodgeStar.AlternatingForm
import TauCeti.Analysis.Calculus.DifferentialForm.Integral
import TauCeti.Analysis.Distribution.TestFunction.Postcomp

/-!
# The codifferential of test forms

The pointwise Hodge star acts by changing the coefficient space of smooth compactly supported
forms on an open set in a finite-dimensional real inner product space. Composing two such stars
with `TestFunction.extDerivCLM` gives the codifferential `δ` as a continuous linear map on test
forms, with `⋆δψ = (-1) ^ (k + 1) d⋆ψ` for a test `(k + 1)`-form `ψ`.

The codifferential is the formal adjoint of the exterior derivative for the integral of the Gram
inner product. The identity is stated both on the ambient space and with volume restricted to the
open set. In particular the adjoint test can be used in defining weak exterior derivatives.

The sign convention and formal adjointness are those of Arnold–Falk–Winther, *Finite element
exterior calculus, homological techniques, and applications* (2006), §2.2, (2.7)–(2.8).
The Hodge star is `Orientation.formHodgeStar`, and integration by parts uses
`Module.Basis.integral_extDeriv_wedge_eq_integral_wedge_extDeriv`. The computation of the sign in
`⋆δ` follows `TauCeti.SmoothForm.hodgeStar_codifferential`.
-/

public section

noncomputable section

open MeasureTheory Module TauCeti TestFunction TopologicalSpace
open scoped Distributions

namespace Orientation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {n k l : ℕ} [hn : Fact (finrank ℝ E = n)] {Ω : Opens E}

/-- The pointwise Hodge star on test forms of complementary degrees, as a continuous linear
change of coefficients. -/
def testFormHodgeStar (o : Orientation ℝ E (Fin n)) (h : k + l = n) :
    𝓓(Ω, E [⋀^Fin k]→L[ℝ] ℝ) ≃L[ℝ] 𝓓(Ω, E [⋀^Fin l]→L[ℝ] ℝ) :=
  postcompCLE (o.formHodgeStar (h.trans hn.out.symm)).toContinuousLinearEquiv

/-- Evaluation of the Hodge star on a test form. -/
@[simp]
theorem testFormHodgeStar_apply (o : Orientation ℝ E (Fin n)) (h : k + l = n)
    (φ : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] ℝ)) (x : E) :
    o.testFormHodgeStar h φ x = o.formHodgeStar (h.trans hn.out.symm) (φ x) := by
  simp [testFormHodgeStar, LinearEquiv.coe_toContinuousLinearEquiv']

/-- The Hodge star preserves the topological support of a test form. -/
@[simp]
theorem tsupport_testFormHodgeStar (o : Orientation ℝ E (Fin n)) (h : k + l = n)
    (φ : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] ℝ)) :
    tsupport (o.testFormHodgeStar h φ) = tsupport φ := by
  rw [testFormHodgeStar, tsupport_postcompCLE]

/-- Squaring the Hodge star on test forms gives multiplication by `(-1) ^ (k * l)`. -/
theorem testFormHodgeStar_testFormHodgeStar (o : Orientation ℝ E (Fin n))
    (h : k + l = n) (φ : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] ℝ)) :
    o.testFormHodgeStar (show l + k = n by omega) (o.testFormHodgeStar h φ) =
      (-1 : ℝ) ^ (k * l) • φ := by
  ext x : 1
  simp [formHodgeStar_formHodgeStar]

/-- The codifferential of test `(k + 1)`-forms is `(-1) ^ (n * (k + 2) + 1) ⋆ d ⋆`, where the
first star takes them to degree `l = n - (k + 1)`. -/
def testFormCodifferentialCLM (o : Orientation ℝ E (Fin n)) (h : k + 1 + l = n) :
    𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] ℝ) →L[ℝ] 𝓓(Ω, E [⋀^Fin k]→L[ℝ] ℝ) :=
  (-1 : ℝ) ^ (n * (k + 2) + 1) •
    (o.testFormHodgeStar (show l + 1 + k = n by omega)).toContinuousLinearMap ∘L
      extDerivCLM ∘L (o.testFormHodgeStar h).toContinuousLinearMap

/-- The codifferential in terms of the two Hodge stars and the exterior derivative. -/
theorem testFormCodifferentialCLM_apply (o : Orientation ℝ E (Fin n)) (h : k + 1 + l = n)
    (ψ : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] ℝ)) :
    o.testFormCodifferentialCLM h ψ = (-1 : ℝ) ^ (n * (k + 2) + 1) •
      o.testFormHodgeStar (show l + 1 + k = n by omega) (extDerivCLM (o.testFormHodgeStar h ψ)) :=
  (rfl)

/-- The Hodge star of the codifferential on test `(k + 1)`-forms is `(-1) ^ (k + 1) d ⋆`. -/
@[simp]
theorem testFormHodgeStar_testFormCodifferentialCLM (o : Orientation ℝ E (Fin n))
    (h : k + 1 + l = n) (ψ : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] ℝ)) :
    o.testFormHodgeStar (show k + (l + 1) = n by omega) (o.testFormCodifferentialCLM h ψ) =
      (-1 : ℝ) ^ (k + 1) • extDerivCLM (o.testFormHodgeStar h ψ) := by
  have hsign : (-1 : ℝ) ^ (n * (k + 2) + 1) * (-1) ^ ((l + 1) * k) = (-1) ^ (k + 1) := by
    subst n
    rw [← pow_add]
    apply neg_one_pow_congr
    simp only [Nat.even_add, Nat.even_mul, Nat.even_add_one]
    tauto
  rw [testFormCodifferentialCLM_apply, map_smul, testFormHodgeStar_testFormHodgeStar,
    smul_smul, hsign]

/-- The codifferential does not enlarge the support of a test form. -/
theorem tsupport_testFormCodifferentialCLM_subset (o : Orientation ℝ E (Fin n))
    (h : k + 1 + l = n) (ψ : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] ℝ)) :
    tsupport (o.testFormCodifferentialCLM h ψ) ⊆ tsupport ψ := by
  rw [testFormCodifferentialCLM_apply]
  rw [FunLike.coe_smul]
  refine (tsupport_smul_subset_right (fun _ : E ↦ (-1 : ℝ) ^ (n * (k + 2) + 1))
    (o.testFormHodgeStar _ (extDerivCLM (o.testFormHodgeStar h ψ)))).trans ?_
  rw [tsupport_testFormHodgeStar, ← tsupport_testFormHodgeStar o h ψ]
  exact tsupport_extDerivCLM_subset _

/-- The codifferential squares to zero on test forms of degree `k + 2`. -/
@[simp]
theorem testFormCodifferentialCLM_testFormCodifferentialCLM (o : Orientation ℝ E (Fin n))
    (h : k + 2 + l = n) (ψ : 𝓓(Ω, E [⋀^Fin (k + 2)]→L[ℝ] ℝ)) :
    o.testFormCodifferentialCLM (show k + 1 + (l + 1) = n by omega)
      (o.testFormCodifferentialCLM h ψ) = 0 := by
  apply (o.testFormHodgeStar (show k + (l + 2) = n by omega)).injective
  simp

variable [MeasurableSpace E] [BorelSpace E]

/-- The codifferential is the formal adjoint of the exterior derivative on test forms, paired
using the pointwise Gram inner product and integrated against ambient volume. -/
theorem integral_alternatingFormInner_extDerivCLM_eq_codifferential
    (o : Orientation ℝ E (Fin n))
    (h : k + 1 + l = n) (φ : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] ℝ))
    (ψ : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] ℝ)) :
    ∫ x, alternatingFormInner E (k + 1) (extDerivCLM φ x) (ψ x) =
      ∫ x, alternatingFormInner E k (φ x) (o.testFormCodifferentialCLM h ψ x) := by
  let b := o.finOrthonormalBasis (by omega : 0 < n) hn.out
  have hb : o.volumeForm b = 1 := by
    rw [o.volumeForm_robust b (o.finOrthonormalBasis_orientation _ _),
      ← OrthonormalBasis.coe_toBasis, Basis.det_self]
  -- Evaluate both wedge products in the integration-by-parts formula on this oriented frame.
  have hw {a c : ℕ} (hac : a + c = n) (α β : E [⋀^Fin a]→L[ℝ] ℝ) :
      α.wedge (o.formHodgeStar (hac.trans hn.out.symm) β) (b ∘ Fin.cast hac) =
        alternatingFormInner E a α β := by
    rw [o.wedge_formHodgeStar_apply]
    simp [Function.comp_def, hb]
  let η := o.testFormHodgeStar h ψ
  have hparts := b.toBasis.integral_extDeriv_wedge_eq_integral_wedge_extDeriv
    (φ := φ) (ψ := η) (by omega) (φ.contDiff.of_le (by simp)) (η.contDiff.of_le (by simp))
    η.hasCompactSupport
  rw [b.addHaar_eq_volume, ← integral_const_mul] at hparts
  convert hparts using 1
  · apply integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
    rw [OrthonormalBasis.coe_toBasis, ← extDerivCLM_apply, testFormHodgeStar_apply]
    exact (hw h _ _).symm
  · apply integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
    have h' : k + (l + 1) = n := by omega
    have hδ := hw h' (φ x) (o.testFormCodifferentialCLM h ψ x)
    rw [← o.testFormHodgeStar_apply h' (o.testFormCodifferentialCLM h ψ) x,
      testFormHodgeStar_testFormCodifferentialCLM,
      FunLike.coe_smul, Pi.smul_apply, ContinuousAlternatingMap.wedge_smul_right,
      ContinuousAlternatingMap.smul_apply, smul_eq_mul] at hδ
    rw [← hδ, ← extDerivCLM_apply, OrthonormalBasis.coe_toBasis, pow_succ, mul_neg_one]

/-- Formal adjointness of the exterior derivative and the codifferential on an open set. Both
integrals use volume restricted to the open set on which the forms are tested. -/
theorem setIntegral_alternatingFormInner_extDerivCLM_eq_codifferential
    (o : Orientation ℝ E (Fin n))
    (h : k + 1 + l = n) (φ : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] ℝ))
    (ψ : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] ℝ)) :
    ∫ x in (Ω : Set E), alternatingFormInner E (k + 1) (extDerivCLM φ x) (ψ x) =
      ∫ x in (Ω : Set E), alternatingFormInner E k (φ x) (o.testFormCodifferentialCLM h ψ x) := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero,
    setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact o.integral_alternatingFormInner_extDerivCLM_eq_codifferential h φ ψ
  · intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun hφ ↦ hx (φ.tsupport_subset hφ))]
    simp
  · intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun hψ ↦ hx (ψ.tsupport_subset hψ))]
    simp

end Orientation
