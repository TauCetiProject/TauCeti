/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Covector
public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.Distribution.Distribution
import TauCeti.Analysis.Sobolev.DifferentialForm.LocallyIntegrable

/-!
# Weak exterior derivatives

`HasWeakExtDerivOn μ Ω u w` is the coordinate integration-by-parts definition of a weak exterior
derivative. Both forms are locally integrable. Testing against scalar test functions in every
constant tuple of vectors recovers the alternating sum of directional derivatives, without
requiring the individual coefficient derivatives of `u` to be functions.

The measure is arbitrary for locality, linearity and uniqueness. The classical agreement theorem
assumes an additive Haar measure. For other measures the identity describes
the adjoint of directional differentiation relative to that measure, as in `HasWeakFDerivOn`.
When open sets are measurable, local integrability ensures that every tested integrand is
integrable (`HasWeakExtDerivOn.integrable_testFunction` and
`HasWeakExtDerivOn.integrable_lineDeriv_testFunction`), so none of the integrals is a junk value.

The basic API supplies restriction, almost-everywhere congruence, linearity and uniqueness.
`HasWeakFDerivOn.hasWeakExtDerivOn` identifies the weak exterior derivative with alternatization
of a weak Fréchet derivative; `ContDiffOn.hasWeakExtDerivOn_extDeriv` and
`HasWeakExtDerivOn.ae_eq_extDeriv` give agreement with Mathlib's classical `extDeriv`.
`hasWeakExtDerivOn_zero_iff` recovers scalar weak differentiation in degree zero.
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace
open scoped Distributions

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] {μ : Measure V} {Ω : Opens V} {k : ℕ}
  {u : V → Covector V k} {w : V → Covector V (k + 1)}

/-- A locally integrable form `w` is the weak exterior derivative of `u` when their coefficients
satisfy the alternating integration-by-parts identity against every scalar test function. -/
def HasWeakExtDerivOn (μ : Measure V) (Ω : Opens V) (u : V → Covector V k)
    (w : V → Covector V (k + 1)) : Prop :=
  LocallyIntegrableOn u Ω μ ∧ LocallyIntegrableOn w Ω μ ∧
    ∀ (φ : 𝓓(Ω, ℝ)) (v : Fin (k + 1) → V),
      ∫ x, φ x • (w x).ofCovector v ∂μ =
        -∑ i : Fin (k + 1), (-1 : ℝ) ^ (i : ℕ) •
          ∫ x, lineDeriv ℝ (φ : V → ℝ) x (v i) • (u x).ofCovector (i.removeNth v) ∂μ

/-- Constructor and eliminator for the sealed weak exterior derivative predicate. -/
theorem hasWeakExtDerivOn_iff_testFunction :
    HasWeakExtDerivOn μ Ω u w ↔
      LocallyIntegrableOn u Ω μ ∧ LocallyIntegrableOn w Ω μ ∧
        ∀ (φ : 𝓓(Ω, ℝ)) (v : Fin (k + 1) → V),
          ∫ x, φ x • (w x).ofCovector v ∂μ =
            -∑ i : Fin (k + 1), (-1 : ℝ) ^ (i : ℕ) •
              ∫ x, lineDeriv ℝ (φ : V → ℝ) x (v i) •
                (u x).ofCovector (i.removeNth v) ∂μ := Iff.rfl

/-- The original form is locally integrable. -/
theorem HasWeakExtDerivOn.locallyIntegrableOn (h : HasWeakExtDerivOn μ Ω u w) :
    LocallyIntegrableOn u Ω μ := h.1

/-- The weak exterior derivative is locally integrable. -/
theorem HasWeakExtDerivOn.locallyIntegrableOn_deriv (h : HasWeakExtDerivOn μ Ω u w) :
    LocallyIntegrableOn w Ω μ := h.2.1

/-- The coordinate testing identity for a weak exterior derivative. -/
theorem HasWeakExtDerivOn.integral_testFunction (h : HasWeakExtDerivOn μ Ω u w)
    (φ : 𝓓(Ω, ℝ)) (v : Fin (k + 1) → V) :
    ∫ x, φ x • (w x).ofCovector v ∂μ =
      -∑ i : Fin (k + 1), (-1 : ℝ) ^ (i : ℕ) •
        ∫ x, lineDeriv ℝ (φ : V → ℝ) x (v i) •
          (u x).ofCovector (i.removeNth v) ∂μ := h.2.2 φ v

/-- The testing identity written with the Fréchet derivative of the scalar test function. -/
theorem HasWeakExtDerivOn.integral_testFunction_fderiv (h : HasWeakExtDerivOn μ Ω u w)
    (φ : 𝓓(Ω, ℝ)) (v : Fin (k + 1) → V) :
    ∫ x, φ x • (w x).ofCovector v ∂μ =
      -∑ i : Fin (k + 1), (-1 : ℝ) ^ (i : ℕ) •
        ∫ x, fderiv ℝ (φ : V → ℝ) x (v i) •
          (u x).ofCovector (i.removeNth v) ∂μ := by
  convert h.integral_testFunction φ v using 1
  simp_rw [(φ.contDiff.differentiable (by simp) _).lineDeriv_eq_fderiv]

/-- Weak exterior derivatives restrict to smaller open sets. -/
theorem HasWeakExtDerivOn.mono {Ω' : Opens V} (h : HasWeakExtDerivOn μ Ω u w)
    (hΩ : Ω' ≤ Ω) : HasWeakExtDerivOn μ Ω' u w :=
  ⟨h.locallyIntegrableOn.mono_set hΩ, h.locallyIntegrableOn_deriv.mono_set hΩ,
    fun φ v ↦ h.integral_testFunction
      ⟨φ, φ.contDiff, φ.hasCompactSupport, φ.tsupport_subset.trans hΩ⟩ v⟩

section Measurable

variable [OpensMeasurableSpace V]

/-- Every term testing the candidate exterior derivative is integrable. -/
theorem HasWeakExtDerivOn.integrable_testFunction (h : HasWeakExtDerivOn μ Ω u w)
    (φ : 𝓓(Ω, ℝ)) (v : Fin (k + 1) → V) :
    Integrable (fun x ↦ φ x • (w x).ofCovector v) μ :=
  φ.integrable_smul (h.locallyIntegrableOn_deriv.covector_coefficient v)

/-- Each directional testing term is integrable, so the defining integrals are genuine. -/
theorem HasWeakExtDerivOn.integrable_lineDeriv_testFunction
    (h : HasWeakExtDerivOn μ Ω u w) (φ : 𝓓(Ω, ℝ)) (v : Fin (k + 1) → V)
    (i : Fin (k + 1)) :
    Integrable (fun x ↦ lineDeriv ℝ (φ : V → ℝ) x (v i) •
      (u x).ofCovector (i.removeNth v)) μ :=
  integrable_lineDeriv_smul_of_locallyIntegrableOn
    (h.locallyIntegrableOn.covector_coefficient _) φ _

omit [OpensMeasurableSpace V] in
/-- The zero form has zero weak exterior derivative for every measure. -/
@[simp]
theorem hasWeakExtDerivOn_zero : HasWeakExtDerivOn μ Ω (0 : V → Covector V k) 0 := by
  refine ⟨locallyIntegrableOn_zero, locallyIntegrableOn_zero, ?_⟩
  intro φ v
  simp

/-- Weak exterior differentiation is additive. -/
theorem HasWeakExtDerivOn.add {u₁ u₂ : V → Covector V k}
    {w₁ w₂ : V → Covector V (k + 1)} (h₁ : HasWeakExtDerivOn μ Ω u₁ w₁)
    (h₂ : HasWeakExtDerivOn μ Ω u₂ w₂) : HasWeakExtDerivOn μ Ω (u₁ + u₂) (w₁ + w₂) := by
  refine ⟨h₁.locallyIntegrableOn.add h₂.locallyIntegrableOn,
    h₁.locallyIntegrableOn_deriv.add h₂.locallyIntegrableOn_deriv, ?_⟩
  intro φ v
  simp only [Pi.add_apply, Covector.ofCovector_add, ContinuousAlternatingMap.add_apply, smul_add]
  rw [integral_add (h₁.integrable_testFunction φ v) (h₂.integrable_testFunction φ v),
    h₁.integral_testFunction, h₂.integral_testFunction]
  simp_rw [integral_add (h₁.integrable_lineDeriv_testFunction φ v _)
    (h₂.integrable_lineDeriv_testFunction φ v _), smul_add]
  rw [Finset.sum_add_distrib, neg_add]

omit [OpensMeasurableSpace V] in
/-- Weak exterior differentiation commutes with multiplication by a real constant. -/
theorem HasWeakExtDerivOn.const_smul (h : HasWeakExtDerivOn μ Ω u w) (c : ℝ) :
    HasWeakExtDerivOn μ Ω (c • u) (c • w) := by
  refine ⟨h.locallyIntegrableOn.smul c, h.locallyIntegrableOn_deriv.smul c, ?_⟩
  intro φ v
  simp only [Pi.smul_apply, Covector.ofCovector_smul, ContinuousAlternatingMap.smul_apply,
    smul_comm (φ _) c, smul_comm (lineDeriv ℝ _ _ _) c]
  simp_rw [integral_smul, smul_comm ((-1 : ℝ) ^ _) c]
  rw [← Finset.smul_sum, ← smul_neg, h.integral_testFunction]

omit [OpensMeasurableSpace V] in
/-- Weak exterior differentiation commutes with negation. -/
theorem HasWeakExtDerivOn.neg (h : HasWeakExtDerivOn μ Ω u w) :
    HasWeakExtDerivOn μ Ω (-u) (-w) := by
  simpa using h.const_smul (-1)

/-- Weak exterior differentiation commutes with subtraction. -/
theorem HasWeakExtDerivOn.sub {u₁ u₂ : V → Covector V k}
    {w₁ w₂ : V → Covector V (k + 1)} (h₁ : HasWeakExtDerivOn μ Ω u₁ w₁)
    (h₂ : HasWeakExtDerivOn μ Ω u₂ w₂) : HasWeakExtDerivOn μ Ω (u₁ - u₂) (w₁ - w₂) := by
  simpa [sub_eq_add_neg] using h₁.add h₂.neg

/-- Alternating the weak Fréchet derivative gives the weak exterior derivative. -/
theorem HasWeakFDerivOn.hasWeakExtDerivOn {U : V → V →L[ℝ] Covector V k}
    (h : HasWeakFDerivOn μ Ω u U) :
    HasWeakExtDerivOn μ Ω u (fun x ↦ Covector.toCovector
      (ContinuousAlternatingMap.alternatizeUncurryFin
        ((Covector.ofCovectorL V k).toContinuousLinearMap.comp (U x)))) := by
  let L := (Covector.ofCovectorL V k).toContinuousLinearMap
  have hU := (h.clm_comp L).locallyIntegrableOn_deriv
  have hA := (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ V ℝ
    (n := k)).locallyIntegrableOn_comp hU
  have hw := (Covector.ofCovectorL V (k + 1)).symm.toContinuousLinearMap.locallyIntegrableOn_comp hA
  refine ⟨h.locallyIntegrableOn, ?_, ?_⟩
  · simpa [L, Function.comp_def] using hw
  intro φ v
  have hi (i : Fin (k + 1)) :=
    ((h.hasWeakLineDerivOn (v i)).clm_comp (Covector.coefficientCLM (i.removeNth v)))
      |>.integral_lineDeriv_smul_eq_neg_integral_smul φ
  have hI (i : Fin (k + 1)) :
      Integrable (fun x ↦ φ x • (U x (v i)).ofCovector (i.removeNth v)) μ :=
    φ.integrable_smul
      ((h.hasWeakLineDerivOn (v i)).locallyIntegrableOn_deriv.covector_coefficient _)
  simp only [ContinuousAlternatingMap.alternatizeUncurryFin_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, Covector.ofCovectorL_apply, Finset.smul_sum]
  simp only [← Int.cast_smul_eq_zsmul ℝ, Int.cast_pow, Int.cast_neg, Int.cast_one]
  have he : (fun x ↦ ∑ i : Fin (k + 1),
      φ x • ((-1 : ℝ) ^ (i : ℕ) • (U x (v i)).ofCovector (i.removeNth v))) =
      (fun x ↦ ∑ i : Fin (k + 1),
        (-1 : ℝ) ^ (i : ℕ) • (φ x • (U x (v i)).ofCovector (i.removeNth v))) := by
    funext x
    apply Finset.sum_congr rfl
    intro i _
    exact smul_comm _ _ _
  rw [he]
  rw [integral_finsetSum Finset.univ
    (f := fun (i : Fin (k + 1)) x ↦
      (-1 : ℝ) ^ (i : ℕ) • (φ x • (U x (v i)).ofCovector (i.removeNth v)))
    (fun i _ ↦ (hI i).smul ((-1 : ℝ) ^ (i : ℕ)))]
  simp_rw [integral_smul]
  have hi' (i : Fin (k + 1)) :
      ∫ x, lineDeriv ℝ (φ : V → ℝ) x (v i) •
        (u x).ofCovector (i.removeNth v) ∂μ =
      -∫ x, φ x • (U x (v i)).ofCovector (i.removeNth v) ∂μ := by
    simpa only [Function.comp_def, Covector.coefficientCLM_apply] using hi i
  simp_rw [hi', smul_neg, Finset.sum_neg_distrib, neg_neg]

omit [OpensMeasurableSpace V] in
/-- In degree zero the weak exterior derivative is exactly the scalar weak Fréchet derivative,
using Mathlib's canonical identifications of zero-forms and one-forms. -/
theorem hasWeakExtDerivOn_zero_iff {f : V → ℝ} {U : V → V →L[ℝ] ℝ} :
    HasWeakExtDerivOn μ Ω
      (fun x ↦ Covector.toCovector
        (ContinuousAlternatingMap.constOfIsEmptyLIE ℝ V ℝ (Fin 0) (f x)))
      (fun x ↦ Covector.toCovector
        (ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1) (U x))) ↔
      HasWeakFDerivOn μ Ω f U := by
  constructor
  · intro h
    apply hasWeakFDerivOn_iff.mpr
    intro v
    apply hasWeakLineDerivOn_iff_testFunction.mpr
    refine ⟨inferInstance, ?_, ?_, ?_⟩
    · simpa using h.locallyIntegrableOn.covector_coefficient (0 : Fin 0 → V)
    · simpa using h.locallyIntegrableOn_deriv.covector_coefficient (fun _ : Fin 1 ↦ v)
    · intro φ
      have hh := h.integral_testFunction φ (fun _ : Fin 1 ↦ v)
      simpa [Nat.zero_add, Fin.sum_univ_one] using (congrArg Neg.neg hh).symm
  · intro h
    let L₀ := (Covector.ofCovectorL V 0).symm.toContinuousLinearMap.comp
      (ContinuousAlternatingMap.constOfIsEmptyLIE ℝ V ℝ (Fin 0)).toContinuousLinearMap
    let L₁ := (Covector.ofCovectorL V 1).symm.toContinuousLinearMap.comp
      (ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1)).toContinuousLinearMap
    refine ⟨?_, ?_, ?_⟩
    · simpa [L₀, Function.comp_def] using L₀.locallyIntegrableOn_comp h.locallyIntegrableOn
    · simpa [L₁, Function.comp_def] using L₁.locallyIntegrableOn_comp h.locallyIntegrableOn_deriv
    · intro φ v
      have hh := (h.hasWeakLineDerivOn (v 0)).integral_lineDeriv_smul_eq_neg_integral_smul φ
      simpa [Nat.zero_add, Fin.sum_univ_one] using (congrArg Neg.neg hh).symm

end Measurable

/-- Replacing the original form by an almost-everywhere equal form preserves its weak
exterior derivative. -/
theorem HasWeakExtDerivOn.congr_ae {u' : V → Covector V k}
    (h : HasWeakExtDerivOn μ Ω u w) (hu : u =ᵐ[μ.restrict Ω] u') :
    HasWeakExtDerivOn μ Ω u' w := by
  refine ⟨h.locallyIntegrableOn.congr hu, h.locallyIntegrableOn_deriv, ?_⟩
  intro φ v
  rw [h.integral_testFunction]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_imp_of_ae_restrict hu] with x hx
  by_cases hxΩ : x ∈ (Ω : Set V)
  · rw [hx hxΩ]
  · rw [lineDeriv_of_notMem_tsupport (fun h' ↦ hxΩ (φ.tsupport_subset h'))]
    simp

/-- Replacing the candidate exterior derivative by an almost-everywhere equal form preserves
the weak exterior derivative relation. -/
theorem HasWeakExtDerivOn.congr_ae_deriv {w' : V → Covector V (k + 1)}
    (h : HasWeakExtDerivOn μ Ω u w) (hw : w =ᵐ[μ.restrict Ω] w') :
    HasWeakExtDerivOn μ Ω u w' := by
  refine ⟨h.locallyIntegrableOn, h.locallyIntegrableOn_deriv.congr hw, ?_⟩
  intro φ v
  rw [← h.integral_testFunction]
  apply integral_congr_ae
  filter_upwards [ae_imp_of_ae_restrict hw] with x hx
  by_cases hxΩ : x ∈ (Ω : Set V)
  · rw [hx hxΩ]
  · rw [image_eq_zero_of_notMem_tsupport (fun h' ↦ hxΩ (φ.tsupport_subset h'))]
    simp

section Uniqueness

variable [BorelSpace V]

/-- A weak exterior derivative is unique almost everywhere on its open domain. -/
theorem HasWeakExtDerivOn.ae_eq {w₁ w₂ : V → Covector V (k + 1)}
    (h₁ : HasWeakExtDerivOn μ Ω u w₁) (h₂ : HasWeakExtDerivOn μ Ω u w₂) :
    w₁ =ᵐ[μ.restrict Ω] w₂ := by
  have hc (v : Fin (k + 1) → V) :
      (fun x ↦ (w₁ x).ofCovector v) =ᵐ[μ.restrict Ω] fun x ↦ (w₂ x).ofCovector v := by
    apply Distribution.ofFun_injective (n := ⊤)
      (h₁.locallyIntegrableOn_deriv.covector_coefficient v)
      (h₂.locallyIntegrableOn_deriv.covector_coefficient v)
    ext φ
    rw [Distribution.ofFun_apply (h₁.locallyIntegrableOn_deriv.covector_coefficient v),
      Distribution.ofFun_apply (h₂.locallyIntegrableOn_deriv.covector_coefficient v)]
    exact (h₁.integral_testFunction φ v).trans (h₂.integral_testFunction φ v).symm
  let b := Module.finBasis ℝ V
  have hb (f : Fin (k + 1) → Fin (Module.finrank ℝ V)) := hc (fun i ↦ b (f i))
  filter_upwards [Filter.eventually_all.2 hb] with x hx
  apply Covector.ext
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  exact b.ext_alternating fun f _ ↦ hx f

end Uniqueness

section Classical

variable [BorelSpace V] [μ.IsAddHaarMeasure]

/-- A continuously differentiable covector field has its classical exterior derivative as its
weak exterior derivative. -/
theorem _root_.ContDiffOn.hasWeakExtDerivOn_extDeriv (hu : ContDiffOn ℝ 1 u Ω) :
    HasWeakExtDerivOn μ Ω u (fun x ↦ Covector.toCovector
      (extDeriv (fun y ↦ (u y).ofCovector) x)) := by
  apply hu.hasWeakFDerivOn_fderiv.hasWeakExtDerivOn.congr_ae_deriv
  filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with x hx
  congr 1
  let L := (Covector.ofCovectorL V k).toContinuousLinearMap
  have hux := (hu.differentiableOn one_ne_zero).differentiableAt (Ω.isOpen.mem_nhds hx)
  have heq : (fun y ↦ (u y).ofCovector) = L ∘ u := by
    funext y
    simp [L]
  rw [extDeriv, heq, fderiv_comp x L.differentiableAt hux, L.fderiv]

/-- On a continuously differentiable form the weak exterior derivative agrees almost everywhere
with the classical exterior derivative. -/
theorem HasWeakExtDerivOn.ae_eq_extDeriv (h : HasWeakExtDerivOn μ Ω u w)
    (hu : ContDiffOn ℝ 1 u Ω) :
    w =ᵐ[μ.restrict Ω] fun x ↦ Covector.toCovector
      (extDeriv (fun y ↦ (u y).ofCovector) x) :=
  h.ae_eq hu.hasWeakExtDerivOn_extDeriv

end Classical

end TauCeti
