/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Examples.Dynamics.Ergodic.WeakMixing
public import TauCeti.MeasureTheory.Measure.AddCircle
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Dynamics.Ergodic.Action.Basic
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Checks: eigenfunctions of actions of `ℝ`

Checks for the eigenfunction criterion of weak mixing
(`MeasureTheory.Measure.isWeaklyMixing_iff_forall_eigenfunction`), whose eigenfunction equation
for `f : X → ℂ` and `a ∈ ℝ` reads `f(t +ᵥ x) = exp(2πiat) f(x)` for almost every `x`, for every
`t`.

* **Constants and zero.** The zero function satisfies the equation for every `a`, and a constant
  function for `a = 0`; both are almost everywhere constant, so the criterion's quantification
  over all measurable `f` is harmless. On the one-point probability space `f = 1` satisfies it for
  `a = 0` only.
* **Nonzero eigenvalues.** If `f` satisfies the equation for some `a ≠ 0` and is not almost
  everywhere zero, then `f` is not almost everywhere constant: at `t = 1/(2a)` the equation reads
  `f(t +ᵥ x) = -f(x)`.
* **Weak mixing of the first factor is needed for the multiplier property.** For the translation
  flow on `AddCircle 1`, which is not weakly mixing, the function `e₁(x) conj(e₁(y))` on
  `AddCircle 1 × AddCircle 1` is invariant under the diagonal flow and not almost everywhere
  constant, its integral being `0` and its modulus `1`.
* **Ergodicity of the second factor is needed.** For the one-point space and the two-point space
  with the trivial action and the uniform measure, the diagonal action on the product is not
  ergodic: `univ ×ˢ {x}` is invariant of measure `1/2`.
-/

public section

noncomputable section

open MeasureTheory Measure Set Complex ProbabilityTheory TauCeti.Examples.WeakMixing
open scoped Real ComplexConjugate

namespace TauCeti.Examples.Eigenfunction

/-! ### Constants and zero -/

section General

variable {X : Type*} [MeasurableSpace X] [AddAction ℝ X] {μ : Measure X}

/-- The zero function satisfies the eigenfunction equation for every `a`. -/
example (a t : ℝ) : (fun x => (0 : X → ℂ) (t +ᵥ x)) =ᵐ[μ]
    fun x => Complex.exp (2 * π * a * t * I) * (0 : X → ℂ) x := by
  simp

/-- A constant function satisfies the eigenfunction equation for `a = 0`. -/
example (c : ℂ) (t : ℝ) : (fun x => Function.const X c (t +ᵥ x)) =ᵐ[μ]
    fun x => Complex.exp (2 * π * (0 : ℝ) * t * I) * Function.const X c x := by
  simp

/-- At `t = 1/(2a)` the eigenfunction factor `exp(2πiat)` is `-1`. -/
theorem exp_two_pi_mul_I_inv {a : ℝ} (ha : a ≠ 0) :
    Complex.exp (2 * π * a * (1 / (2 * a) : ℝ) * I) = -1 := by
  have : (2 * π * a * (1 / (2 * a) : ℝ) * I : ℂ) = π * I := by
    have ha' : (a : ℂ) ≠ 0 := ofReal_ne_zero.2 ha
    push_cast
    field_simp
  rw [this, Complex.exp_pi_mul_I]

/-- **A nonzero eigenvalue forces a nonconstant eigenfunction.** For an action preserving `μ`, if
`f` satisfies the eigenfunction equation for some `a ≠ 0` and is not almost everywhere zero, then
`f` is not almost everywhere constant. -/
theorem not_exists_ae_eq_const_of_eigenfunction [MeasurableConstVAdd ℝ X]
    [VAddInvariantMeasure ℝ X μ] {f : X → ℂ} {a : ℝ} (ha : a ≠ 0)
    (heig : ∀ t : ℝ, (fun x => f (t +ᵥ x)) =ᵐ[μ]
      fun x => Complex.exp (2 * π * a * t * I) * f x)
    (hf : ¬ f =ᵐ[μ] 0) : ¬ ∃ c : ℂ, f =ᵐ[μ] Function.const X c := by
  rintro ⟨c, hc⟩
  have hc' : (fun x => f ((1 / (2 * a) : ℝ) +ᵥ x)) =ᵐ[μ] fun _ => c :=
    (measurePreserving_vadd ((1 / (2 * a) : ℝ)) μ).quasiMeasurePreserving.ae_eq_comp hc
  refine hf ?_
  filter_upwards [hc, hc', heig (1 / (2 * a))] with x h₁ h₂ h₃
  rw [exp_two_pi_mul_I_inv ha, h₂, h₁, Function.const_apply, neg_one_mul] at h₃
  rw [h₁, Function.const_apply, Pi.zero_apply]
  linear_combination h₃ / 2

end General

/-! ### The one-point space -/

/-- A one-point space, carrying the trivial action of `ℝ`. -/
def OnePoint : Type := Unit

/-- The one-point space carries the discrete σ-algebra of `Unit`. -/
instance instMeasurableSpaceOnePoint : MeasurableSpace OnePoint :=
  inferInstanceAs (MeasurableSpace Unit)

instance instMeasurableSingletonClassOnePoint : MeasurableSingletonClass OnePoint :=
  inferInstanceAs (MeasurableSingletonClass Unit)

/-- The point of the one-point space. -/
def OnePoint.pt : OnePoint := ()

/-- The trivial action of `ℝ` on the one-point space. -/
instance instAddActionOnePoint : AddAction ℝ OnePoint where
  vadd _ x := x
  zero_vadd _ := rfl
  add_vadd _ _ _ := rfl

/-- On the one-point probability space, `f = 1` satisfies the eigenfunction equation exactly for
`a = 0`. -/
theorem onePoint_one_eigenfunction_iff (a : ℝ) :
    (∀ t : ℝ, (fun _ : OnePoint => (1 : ℂ)) =ᵐ[dirac OnePoint.pt]
      fun _ => Complex.exp (2 * π * a * t * I) * 1) ↔ a = 0 := by
  simp only [Filter.EventuallyEq, ae_dirac_eq, Filter.eventually_pure, mul_one]
  refine ⟨fun h => ?_, fun h t => by simp [h]⟩
  by_contra ha
  have := h (1 / (2 * a))
  rw [exp_two_pi_mul_I_inv ha] at this
  norm_num at this

/-! ### The multiplier property needs weak mixing of the first factor -/

/-- The function `e₁(x) conj(e₁(y))` on `AddCircle 1 × AddCircle 1`. -/
def diagonalMode (p : AddCircle (1 : ℝ) × AddCircle (1 : ℝ)) : ℂ :=
  fourier 1 p.1 * conj (fourier 1 p.2)

/-- `e₁(x) conj(e₁(y))` is invariant under the diagonal translation flow:
`exp(2πit) exp(-2πit) = 1`. -/
theorem diagonalMode_vadd (t : ℝ) (p : AddCircle (1 : ℝ) × AddCircle (1 : ℝ)) :
    diagonalMode (t +ᵥ p) = diagonalMode p := by
  obtain ⟨x, y⟩ := p
  have h : (AddCircle.toCircle (t : AddCircle (1 : ℝ)) : ℂ) *
      conj (AddCircle.toCircle (t : AddCircle (1 : ℝ)) : ℂ) = 1 := by
    rw [Complex.mul_conj, Circle.normSq_coe, ofReal_one]
  simp only [diagonalMode, Prod.vadd_mk, AddCircle.vadd_eq_add, fourier_one,
    AddCircle.toCircle_add, Circle.coe_mul, map_mul]
  linear_combination ((AddCircle.toCircle x : ℂ) * conj (AddCircle.toCircle y : ℂ)) * h

/-- The mode `e₁` has integral `0` for the normalized Haar measure. -/
theorem integral_fourier_one :
    ∫ x, fourier 1 x ∂AddCircle.haarAddCircle (T := 1) = 0 := by
  have := congrFun (fourierCoeff_fourier (T := 1) 1) 0
  simpa [fourierCoeff, fourier_zero] using this

/-- **`e₁(x) conj(e₁(y))` is not almost everywhere constant** for the product of the normalized
Haar measures: its integral is `0`, while it vanishes nowhere. -/
theorem not_exists_ae_eq_const_diagonalMode :
    ¬ ∃ c : ℂ, diagonalMode =ᵐ[(AddCircle.haarAddCircle (T := 1)).prod
      (AddCircle.haarAddCircle (T := 1))] Function.const _ c := by
  rintro ⟨c, hc⟩
  have hint : ∫ p, diagonalMode p ∂(AddCircle.haarAddCircle (T := 1)).prod
      (AddCircle.haarAddCircle (T := 1)) = 0 := by
    simp only [diagonalMode]
    rw [integral_prod_mul (fun x => fourier 1 x) (fun y => conj (fourier 1 y)), integral_conj,
      integral_fourier_one, zero_mul]
  rw [integral_congr_ae hc] at hint
  simp only [Function.const_apply, integral_const, probReal_univ, one_smul] at hint
  obtain ⟨p, hp⟩ := hc.exists
  rw [hint, Function.const_apply] at hp
  simp [diagonalMode] at hp

/-! ### The multiplier property needs ergodicity of the second factor -/

/-- The set `univ ×ˢ {x}` of the product of the one-point and two-point spaces. -/
abbrev pointSet : Set (OnePoint × TwoPoint) := univ ×ˢ {TwoPoint.pt true}

/-- `univ ×ˢ {x}` has measure `1/2` for the product of the Dirac and uniform measures. -/
theorem prod_pointSet :
    (dirac OnePoint.pt).prod (uniformOn (univ : Set TwoPoint)) pointSet = 2⁻¹ := by
  rw [Measure.prod_prod, measure_univ, one_mul, uniformOn_univ, TwoPoint.card_eq]
  simp

/-- **The product of the one-point space with the trivial two-point space is not ergodic.** The
set `univ ×ˢ {x}` is invariant under the diagonal action, of measure `1/2`. -/
theorem not_ergodicVAdd_onePoint_prod_twoPoint :
    ¬ ErgodicVAdd ℝ (OnePoint × TwoPoint)
      ((dirac OnePoint.pt).prod (uniformOn (univ : Set TwoPoint))) := by
  intro h
  have hs : MeasurableSet pointSet := MeasurableSet.univ.prod (measurableSet_singleton _)
  have hconst := h.aeconst_of_forall_preimage_vadd_ae_eq hs fun t => by
    have : (fun x : OnePoint × TwoPoint => t +ᵥ x) ⁻¹' pointSet = pointSet := rfl
    rw [this]
  rcases Filter.eventuallyEmptyOrUniv_iff.1 hconst with h₁ | h₁
  · have h₂ := (prob_compl_eq_zero_iff hs).1 (ae_iff.1 h₁)
    rw [prod_pointSet] at h₂
    norm_num at h₂
  · have h₂ := measure_eq_zero_iff_ae_notMem.2 h₁
    rw [prod_pointSet] at h₂
    norm_num at h₂

end TauCeti.Examples.Eigenfunction
