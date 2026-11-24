/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
public import TauCeti.Analysis.Complex.Wirtinger.Holomorphic
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars

/-!
# Weak conjugate Wirtinger derivatives

`HasWeakConjWirtingerDerivOn μ Ω u g` expresses `\bar∂u = g` by integration by parts against real
smooth compactly supported test functions. The normalization is `\bar∂ = (∂₁ + I ∂ᵢ)/2`.
This does not require either real first derivative of `u` to be represented by a function.

The codomain is complete and both functions are locally integrable, preventing the totalized
Bochner integral from making the defining identity vacuous. With a Haar measure the identity
is the distributional equation; for a general measure it is the corresponding adjoint relation.

## Main results

The relation is local, complex-linear, invariant under almost-everywhere replacement and
compatible with continuous complex-linear maps. Its value is unique almost everywhere.
`hasWeakConjWirtingerDerivOn_of_hasWeakLineDerivOn` and
`HasWeakFDerivOn.hasWeakConjWirtingerDerivOn` compare it with the native real weak derivatives,
and `HasWeakConjWirtingerDerivOn.weakLineDeriv` differentiates the equation in a real direction.
`hasWeakConjWirtingerDerivOn_of_contDiffOn` compares it with the classical normalized operator;
for real `C¹` maps, its vanishing is equivalent to holomorphy.
Every holomorphic map solves the distributional equation.
`hasWeakConjWirtingerDerivOn_conj` computes the weak derivative of conjugation as `1`,
which rules out an almost-everywhere equal holomorphic representative on nonempty open sets.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.
-/

public noncomputable section

open Complex MeasureTheory TopologicalSpace
open scoped ContDiff Distributions ComplexConjugate

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  {μ : Measure ℂ} {Ω : Opens ℂ} {u g : ℂ → F}

/-- The normalized distributional equation `\bar∂u = g`, relative to `μ`, with locally integrable
source and derivative and a complete codomain. Real tests suffice for a complex-linear equation. -/
def HasWeakConjWirtingerDerivOn (μ : Measure ℂ) (Ω : Opens ℂ) (u g : ℂ → F) : Prop :=
  CompleteSpace F ∧ LocallyIntegrableOn u Ω μ ∧ LocallyIntegrableOn g Ω μ ∧
    ∀ φ : 𝓓(Ω, ℝ),
      (∫ z, lineDeriv ℝ (φ : ℂ → ℝ) z 1 • u z ∂μ) +
          I • (∫ z, lineDeriv ℝ (φ : ℂ → ℝ) z I • u z ∂μ) =
        -(2 : ℂ) • ∫ z, (φ : ℂ → ℝ) z • g z ∂μ

/-- The defining conditions, usable without unfolding the sealed definition. -/
theorem hasWeakConjWirtingerDerivOn_iff :
    HasWeakConjWirtingerDerivOn μ Ω u g ↔
      CompleteSpace F ∧ LocallyIntegrableOn u Ω μ ∧ LocallyIntegrableOn g Ω μ ∧
        ∀ φ : 𝓓(Ω, ℝ),
          (∫ z, lineDeriv ℝ (φ : ℂ → ℝ) z 1 • u z ∂μ) +
              I • (∫ z, lineDeriv ℝ (φ : ℂ → ℝ) z I • u z ∂μ) =
            -(2 : ℂ) • ∫ z, (φ : ℂ → ℝ) z • g z ∂μ := Iff.rfl

/-- The codomain of a weak conjugate Wirtinger derivative is complete. -/
theorem HasWeakConjWirtingerDerivOn.completeSpace (h : HasWeakConjWirtingerDerivOn μ Ω u g) :
    CompleteSpace F := h.1

/-- The source is locally integrable. -/
theorem HasWeakConjWirtingerDerivOn.locallyIntegrableOn
    (h : HasWeakConjWirtingerDerivOn μ Ω u g) : LocallyIntegrableOn u Ω μ := h.2.1

/-- The weak conjugate Wirtinger derivative is locally integrable. -/
theorem HasWeakConjWirtingerDerivOn.locallyIntegrableOn_deriv
    (h : HasWeakConjWirtingerDerivOn μ Ω u g) : LocallyIntegrableOn g Ω μ := h.2.2.1

namespace HasWeakConjWirtingerDerivOn

/-- Integration by parts for the normalized conjugate Wirtinger derivative. -/
theorem integral_lineDeriv_smul_add_I_smul_eq_neg_two_smul_integral_smul
    (h : HasWeakConjWirtingerDerivOn μ Ω u g) (φ : 𝓓(Ω, ℝ)) :
    (∫ z, lineDeriv ℝ (φ : ℂ → ℝ) z 1 • u z ∂μ) +
        I • (∫ z, lineDeriv ℝ (φ : ℂ → ℝ) z I • u z ∂μ) =
      -(2 : ℂ) • ∫ z, (φ : ℂ → ℝ) z • g z ∂μ := h.2.2.2 φ

end HasWeakConjWirtingerDerivOn

/-- Weak conjugate Wirtinger differentiation restricts to smaller open sets. -/
theorem HasWeakConjWirtingerDerivOn.mono {Ω' : Opens ℂ}
    (h : HasWeakConjWirtingerDerivOn μ Ω u g) (hΩ : Ω' ≤ Ω) :
    HasWeakConjWirtingerDerivOn μ Ω' u g :=
  ⟨h.completeSpace, h.locallyIntegrableOn.mono_set hΩ,
    h.locallyIntegrableOn_deriv.mono_set hΩ, fun φ ↦
      h.integral_lineDeriv_smul_add_I_smul_eq_neg_two_smul_integral_smul
      ⟨φ, φ.contDiff, φ.hasCompactSupport, φ.tsupport_subset.trans hΩ⟩⟩

/-- The zero function has weak conjugate Wirtinger derivative zero. -/
@[simp]
theorem hasWeakConjWirtingerDerivOn_zero [CompleteSpace F] :
    HasWeakConjWirtingerDerivOn μ Ω (0 : ℂ → F) 0 :=
  ⟨inferInstance, locallyIntegrableOn_zero, locallyIntegrableOn_zero, fun _ ↦ by simp⟩

/-- Weak conjugate Wirtinger differentiation commutes with negation. -/
theorem HasWeakConjWirtingerDerivOn.neg (h : HasWeakConjWirtingerDerivOn μ Ω u g) :
    HasWeakConjWirtingerDerivOn μ Ω (-u) (-g) := by
  refine ⟨h.completeSpace, h.locallyIntegrableOn.neg, h.locallyIntegrableOn_deriv.neg, ?_⟩
  intro φ
  simpa only [Pi.neg_apply, smul_neg, integral_neg, ← neg_add, neg_smul] using
    congrArg Neg.neg (h.integral_lineDeriv_smul_add_I_smul_eq_neg_two_smul_integral_smul φ)

/-- Weak conjugate Wirtinger differentiation commutes with addition. -/
theorem HasWeakConjWirtingerDerivOn.add {v k : ℂ → F}
    (h : HasWeakConjWirtingerDerivOn μ Ω u g) (hv : HasWeakConjWirtingerDerivOn μ Ω v k) :
    HasWeakConjWirtingerDerivOn μ Ω (u + v) (g + k) := by
  refine ⟨h.completeSpace, h.locallyIntegrableOn.add hv.locallyIntegrableOn,
    h.locallyIntegrableOn_deriv.add hv.locallyIntegrableOn_deriv, ?_⟩
  intro φ
  simp only [Pi.add_apply, smul_add]
  rw [integral_add (integrable_lineDeriv_smul_of_locallyIntegrableOn h.locallyIntegrableOn φ 1)
    (integrable_lineDeriv_smul_of_locallyIntegrableOn hv.locallyIntegrableOn φ 1),
    integral_add (integrable_lineDeriv_smul_of_locallyIntegrableOn h.locallyIntegrableOn φ I)
      (integrable_lineDeriv_smul_of_locallyIntegrableOn hv.locallyIntegrableOn φ I),
    integral_add (φ.integrable_smul h.locallyIntegrableOn_deriv)
      (φ.integrable_smul hv.locallyIntegrableOn_deriv), smul_add, smul_add]
  calc
    _ = ((∫ z, lineDeriv ℝ (φ : ℂ → ℝ) z 1 • u z ∂μ) +
          I • (∫ z, lineDeriv ℝ (φ : ℂ → ℝ) z I • u z ∂μ)) +
        ((∫ z, lineDeriv ℝ (φ : ℂ → ℝ) z 1 • v z ∂μ) +
          I • (∫ z, lineDeriv ℝ (φ : ℂ → ℝ) z I • v z ∂μ)) := by abel
    _ = _ := by
      rw [h.integral_lineDeriv_smul_add_I_smul_eq_neg_two_smul_integral_smul φ,
        hv.integral_lineDeriv_smul_add_I_smul_eq_neg_two_smul_integral_smul φ]

/-- Weak conjugate Wirtinger differentiation commutes with subtraction. -/
theorem HasWeakConjWirtingerDerivOn.sub {v k : ℂ → F}
    (h : HasWeakConjWirtingerDerivOn μ Ω u g) (hv : HasWeakConjWirtingerDerivOn μ Ω v k) :
    HasWeakConjWirtingerDerivOn μ Ω (u - v) (g - k) := by
  simpa [sub_eq_add_neg] using h.add hv.neg

/-- A complex continuous linear map commutes with the weak conjugate Wirtinger derivative. -/
theorem HasWeakConjWirtingerDerivOn.clm_comp {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℂ G] [CompleteSpace G] (h : HasWeakConjWirtingerDerivOn μ Ω u g)
    (L : F →L[ℂ] G) :
    HasWeakConjWirtingerDerivOn μ Ω (fun z ↦ L (u z)) (fun z ↦ L (g z)) := by
  have := h.completeSpace
  refine ⟨inferInstance, L.locallyIntegrableOn_comp h.locallyIntegrableOn,
    L.locallyIntegrableOn_comp h.locallyIntegrableOn_deriv, ?_⟩
  intro φ
  have hi (w : ℂ → F) (hw : LocallyIntegrableOn w Ω μ) (ψ : 𝓓(Ω, ℝ)) :
      (∫ z, (ψ : ℂ → ℝ) z • L (w z) ∂μ) = L (∫ z, (ψ : ℂ → ℝ) z • w z ∂μ) := by
    rw [← L.integral_comp_comm (ψ.integrable_smul hw)]
    simp
  have hi' (v : ℂ) :
      (∫ z, lineDeriv ℝ (φ : ℂ → ℝ) z v • L (u z) ∂μ) =
        L (∫ z, lineDeriv ℝ (φ : ℂ → ℝ) z v • u z ∂μ) := by
    simpa only [TestFunction.lineDerivOp_apply] using
      hi u h.locallyIntegrableOn (LineDeriv.lineDerivOp v φ)
  rw [hi' 1, hi' I, ← map_smul, ← map_add,
    h.integral_lineDeriv_smul_add_I_smul_eq_neg_two_smul_integral_smul φ,
    map_smul, hi g h.locallyIntegrableOn_deriv φ]

/-- Weak conjugate Wirtinger differentiation is complex-linear. -/
theorem HasWeakConjWirtingerDerivOn.const_smul (h : HasWeakConjWirtingerDerivOn μ Ω u g)
    (c : ℂ) : HasWeakConjWirtingerDerivOn μ Ω (c • u) (c • g) := by
  have := h.completeSpace
  simpa only [smul_apply, ContinuousLinearMap.id_apply, Pi.smul_def] using
    h.clm_comp (c • ContinuousLinearMap.id ℂ F)

/-- Almost-everywhere replacement on the open set preserves the source of a weak derivative. -/
theorem HasWeakConjWirtingerDerivOn.congr_ae {v : ℂ → F}
    (h : HasWeakConjWirtingerDerivOn μ Ω u g) (huv : u =ᵐ[μ.restrict Ω] v) :
    HasWeakConjWirtingerDerivOn μ Ω v g := by
  refine ⟨h.completeSpace, h.locallyIntegrableOn.congr huv, h.locallyIntegrableOn_deriv, ?_⟩
  intro φ
  have he (a : ℂ) :
      (∫ z, lineDeriv ℝ (φ : ℂ → ℝ) z a • v z ∂μ) =
        ∫ z, lineDeriv ℝ (φ : ℂ → ℝ) z a • u z ∂μ := by
    apply integral_congr_ae
    filter_upwards [(ae_restrict_iff' Ω.isOpen.measurableSet).1 huv] with z hz
    by_cases hzΩ : z ∈ (Ω : Set ℂ)
    · rw [hz hzΩ]
    · rw [lineDeriv_of_notMem_tsupport (fun h' ↦ hzΩ (φ.tsupport_subset h')) a]
      simp
  rw [he 1, he I]
  exact h.integral_lineDeriv_smul_add_I_smul_eq_neg_two_smul_integral_smul φ

/-- Almost-everywhere replacement preserves the weak conjugate Wirtinger derivative. -/
theorem HasWeakConjWirtingerDerivOn.congr_ae_deriv {k : ℂ → F}
    (h : HasWeakConjWirtingerDerivOn μ Ω u g) (hgk : g =ᵐ[μ.restrict Ω] k) :
    HasWeakConjWirtingerDerivOn μ Ω u k := by
  refine ⟨h.completeSpace, h.locallyIntegrableOn, h.locallyIntegrableOn_deriv.congr hgk, ?_⟩
  intro φ
  rw [h.integral_lineDeriv_smul_add_I_smul_eq_neg_two_smul_integral_smul φ]
  congr 1
  apply integral_congr_ae
  filter_upwards [(ae_restrict_iff' Ω.isOpen.measurableSet).1 hgk] with z hz
  by_cases hzΩ : z ∈ (Ω : Set ℂ)
  · rw [hz hzΩ]
  · rw [image_eq_zero_of_notMem_tsupport (fun h' ↦ hzΩ (φ.tsupport_subset h'))]
    simp

/-- The weak conjugate Wirtinger derivative is unique almost everywhere on the open set. -/
theorem HasWeakConjWirtingerDerivOn.ae_eq {k : ℂ → F}
    (h : HasWeakConjWirtingerDerivOn μ Ω u g) (hk : HasWeakConjWirtingerDerivOn μ Ω u k) :
    g =ᵐ[μ.restrict Ω] k := by
  have := h.completeSpace
  have key : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ (Ω : Set ℂ) → ∫ z, φ z • (g - k) z ∂μ = 0 := by
    intro φ hφ hφc hφs
    let ψ : 𝓓(Ω, ℝ) := ⟨φ, hφ, hφc, hφs⟩
    have he := (h.integral_lineDeriv_smul_add_I_smul_eq_neg_two_smul_integral_smul ψ).symm.trans
      (hk.integral_lineDeriv_smul_add_I_smul_eq_neg_two_smul_integral_smul ψ)
    have he' : (∫ z, φ z • g z ∂μ) = ∫ z, φ z • k z ∂μ := by
      have hc : -(2 : ℂ) ≠ 0 := by norm_num
      simpa [ψ, inv_smul_smul₀ hc] using congrArg (fun x : F ↦ (-(2 : ℂ))⁻¹ • x) he
    simp only [Pi.sub_apply, smul_sub]
    have hi₁ : Integrable (fun z ↦ φ z • g z) μ := by
      simpa [ψ] using ψ.integrable_smul h.locallyIntegrableOn_deriv
    have hi₂ : Integrable (fun z ↦ φ z • k z) μ := by
      simpa [ψ] using ψ.integrable_smul hk.locallyIntegrableOn_deriv
    rw [integral_sub hi₁ hi₂, he', sub_self]
  have hz := Ω.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (h.locallyIntegrableOn_deriv.sub hk.locallyIntegrableOn_deriv) key
  rw [Filter.EventuallyEq, ae_restrict_iff' Ω.isOpen.measurableSet]
  filter_upwards [hz] with z hz hzΩ
  simpa [sub_eq_zero] using hz hzΩ

/-- The two weak real partial derivatives combine to the normalized weak `\bar∂` derivative. -/
theorem hasWeakConjWirtingerDerivOn_of_hasWeakLineDerivOn {us ut : ℂ → F}
    (hs : HasWeakLineDerivOn μ Ω u us 1) (ht : HasWeakLineDerivOn μ Ω u ut I) :
    HasWeakConjWirtingerDerivOn μ Ω u
      (fun z ↦ (2 : ℂ)⁻¹ • (us z + I • ut z)) := by
  have := hs.completeSpace
  refine ⟨inferInstance, hs.locallyIntegrableOn,
    (hs.locallyIntegrableOn_deriv.add (ht.locallyIntegrableOn_deriv.smul I)).smul
      ((2 : ℂ)⁻¹), ?_⟩
  intro φ
  simp_rw [smul_comm (_ : ℝ) ((2 : ℂ)⁻¹), smul_add, smul_comm (_ : ℝ) I]
  have his : Integrable (fun z ↦ (2 : ℂ)⁻¹ • ((φ : ℂ → ℝ) z • us z)) μ :=
    (φ.integrable_smul hs.locallyIntegrableOn_deriv).smul _
  have hit : Integrable (fun z ↦ (2 : ℂ)⁻¹ • (I • ((φ : ℂ → ℝ) z • ut z))) μ :=
    ((φ.integrable_smul ht.locallyIntegrableOn_deriv).smul I).smul _
  rw [integral_add his hit, integral_smul, integral_smul, integral_smul,
    hs.integral_lineDeriv_smul_eq_neg_integral_smul φ,
    ht.integral_lineDeriv_smul_eq_neg_integral_smul φ]
  module

/-- A weak Fréchet derivative determines the weak conjugate Wirtinger derivative. -/
theorem HasWeakFDerivOn.hasWeakConjWirtingerDerivOn {D : ℂ → ℂ →L[ℝ] F}
    (h : HasWeakFDerivOn μ Ω u D) :
    HasWeakConjWirtingerDerivOn μ Ω u
      (fun z ↦ (2 : ℂ)⁻¹ • (D z 1 + I • D z I)) :=
  hasWeakConjWirtingerDerivOn_of_hasWeakLineDerivOn
    (h.hasWeakLineDerivOn 1) (h.hasWeakLineDerivOn I)

/-- The classical conjugate Wirtinger derivative of a `C¹` function is its weak derivative. -/
theorem hasWeakConjWirtingerDerivOn_of_contDiffOn [CompleteSpace F] [μ.IsAddHaarMeasure]
    (hu : ContDiffOn ℝ 1 u Ω) :
    HasWeakConjWirtingerDerivOn μ Ω u (fun z ↦ conjWirtingerDeriv u z 1) := by
  have h := hasWeakFDerivOn_of_differentiableOn (μ := μ)
    ((hu.continuousOn_fderiv_of_isOpen Ω.isOpen le_rfl).locallyIntegrableOn
      Ω.isOpen.measurableSet)
    (fun z hz ↦ (hu.differentiableOn one_ne_zero).differentiableAt (Ω.isOpen.mem_nhds hz))
  simpa only [conjWirtingerDeriv_apply, smul_eq_mul, mul_one] using
    h.hasWeakConjWirtingerDerivOn

/-- Conjugation has normalized weak `\bar∂` derivative `1`, fixing both its sign and factor. -/
theorem hasWeakConjWirtingerDerivOn_conj [μ.IsAddHaarMeasure] :
    HasWeakConjWirtingerDerivOn μ Ω conj (fun _ ↦ (1 : ℂ)) := by
  have hcoe : (Complex.conjCLE : ℂ → ℂ) = conj := funext Complex.conjCLE_apply
  have hc : ContDiffOn ℝ 1 (conj : ℂ → ℂ) Ω := by
    simpa only [hcoe] using
      (Complex.conjCLE.contDiff.contDiffOn : ContDiffOn ℝ 1 (fun z ↦ Complex.conjCLE z) Ω)
  have hd (z : ℂ) : conjWirtingerDeriv (conj : ℂ → ℂ) z 1 = 1 := by
    have hf : HasFDerivAt (conj : ℂ → ℂ) Complex.conjCLE.toContinuousLinearMap z := by
      simpa only [hcoe] using Complex.conjCLE.hasFDerivAt (x := z)
    rw [conjWirtingerDeriv_apply, hf.fderiv]
    norm_num [smul_eq_mul, Complex.conjCLE_apply]
  simpa only [hd] using hasWeakConjWirtingerDerivOn_of_contDiffOn (μ := μ) hc

/-- For a function of class `C¹` over `ℝ`, the weak equation `\bar∂u=0` is precisely holomorphy. -/
theorem hasWeakConjWirtingerDerivOn_zero_iff_of_contDiffOn
    [CompleteSpace F] [μ.IsAddHaarMeasure] (hu : ContDiffOn ℝ 1 u Ω) :
    HasWeakConjWirtingerDerivOn μ Ω u 0 ↔ DifferentiableOn ℂ u Ω := by
  have hr (z : ℂ) (hz : z ∈ (Ω : Set ℂ)) : DifferentiableAt ℝ u z :=
    (hu.differentiableOn one_ne_zero).differentiableAt (Ω.isOpen.mem_nhds hz)
  constructor
  · intro h
    have he := (hasWeakConjWirtingerDerivOn_of_contDiffOn hu).ae_eq h
    have hD := hu.continuousOn_fderiv_of_isOpen Ω.isOpen le_rfl
    have hg : ContinuousOn (fun z ↦ conjWirtingerDeriv u z 1) Ω := by
      simp only [conjWirtingerDeriv_apply, smul_eq_mul, mul_one]
      exact continuousOn_const.smul ((hD.clm_apply continuousOn_const).add
        (continuousOn_const.smul (hD.clm_apply continuousOn_const)))
    have hz := Measure.eqOn_open_of_ae_eq he Ω.isOpen hg continuousOn_const
    intro z hzu
    exact ((differentiableAt_iff_conjWirtingerDeriv_apply_one_eq_zero (hr z hzu)).2
      (hz hzu)).differentiableWithinAt
  · intro h
    apply (hasWeakConjWirtingerDerivOn_of_contDiffOn hu).congr_ae_deriv
    rw [Filter.EventuallyEq, ae_restrict_iff' Ω.isOpen.measurableSet]
    filter_upwards [] with z hz
    simp [(h.differentiableAt (Ω.isOpen.mem_nhds hz)).conjWirtingerDeriv_eq_zero]

/-- Every holomorphic function with Banach coefficients solves the distributional equation. -/
theorem _root_.DifferentiableOn.hasWeakConjWirtingerDerivOn_zero
    [CompleteSpace F] [μ.IsAddHaarMeasure] (h : DifferentiableOn ℂ u Ω) :
    HasWeakConjWirtingerDerivOn μ Ω u 0 :=
  (hasWeakConjWirtingerDerivOn_zero_iff_of_contDiffOn
    ((h.contDiffOn Ω.isOpen).restrict_scalars ℝ)).2 h

/-- Conjugation cannot agree almost everywhere with a holomorphic function on a nonempty
open set: its weak `\bar∂` derivative is `1`, while a holomorphic representative has
derivative `0`. -/
theorem not_exists_differentiableOn_ae_eq_conj [μ.IsAddHaarMeasure]
    (hΩ : (Ω : Set ℂ).Nonempty) :
    ¬ ∃ v : ℂ → ℂ, DifferentiableOn ℂ v Ω ∧ (conj : ℂ → ℂ) =ᵐ[μ.restrict Ω] v := by
  rintro ⟨v, hv, hae⟩
  have hzero := hv.hasWeakConjWirtingerDerivOn_zero.congr_ae hae.symm
  have he := (hasWeakConjWirtingerDerivOn_conj (μ := μ) (Ω := Ω)).ae_eq hzero
  have hμ : μ (Ω : Set ℂ) = 0 := by
    simpa [Filter.EventuallyEq, ae_iff] using he
  exact (Ω.isOpen.measure_pos (μ := μ) hΩ).ne' hμ

open LineDeriv in
/-- A weak directional derivative of a solution of `\bar∂u = f` solves the differentiated
equation `\bar∂(∂ᵥu) = ∂ᵥf`. No other derivative of `u` or `f` is assumed. -/
theorem HasWeakConjWirtingerDerivOn.weakLineDeriv {f u' f' : ℂ → F} {v : ℂ}
    (h : HasWeakConjWirtingerDerivOn μ Ω u f)
    (hu : HasWeakLineDerivOn μ Ω u u' v) (hf : HasWeakLineDerivOn μ Ω f f' v) :
    HasWeakConjWirtingerDerivOn μ Ω u' f' := by
  refine hasWeakConjWirtingerDerivOn_iff.2
    ⟨h.completeSpace, hu.locallyIntegrableOn_deriv, hf.locallyIntegrableOn_deriv, fun φ => ?_⟩
  have hw (w : ℂ) : ∫ z, lineDeriv ℝ (φ : ℂ → ℝ) z w • u' z ∂μ =
      -∫ z, lineDeriv ℝ (∂_{v} φ : 𝓓(Ω, ℝ)) z w • u z ∂μ := by
    calc ∫ z, lineDeriv ℝ (φ : ℂ → ℝ) z w • u' z ∂μ
        = ∫ z, (∂_{w} φ : 𝓓(Ω, ℝ)) z • u' z ∂μ := by
          simp only [TestFunction.lineDerivOp_apply]
      _ = -∫ z, lineDeriv ℝ (∂_{w} φ : 𝓓(Ω, ℝ)) z v • u z ∂μ := by
          rw [hu.integral_lineDeriv_smul_eq_neg_integral_smul, neg_neg]
      _ = _ := by simp only [TestFunction.lineDeriv_lineDerivOp_comm φ w v]
  have hfv : ∫ z, (∂_{v} φ : 𝓓(Ω, ℝ)) z • f z ∂μ = -∫ z, (φ : ℂ → ℝ) z • f' z ∂μ := by
    simpa only [TestFunction.lineDerivOp_apply] using
      hf.integral_lineDeriv_smul_eq_neg_integral_smul φ
  have hφ := h.integral_lineDeriv_smul_add_I_smul_eq_neg_two_smul_integral_smul (∂_{v} φ)
  rw [hw 1, hw I, smul_neg, ← neg_add, hφ, hfv]
  module

end TauCeti
