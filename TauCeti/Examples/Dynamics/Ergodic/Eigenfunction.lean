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
import TauCeti.Dynamics.Ergodic.Action.Eigenfunction

/-!
# Checks: eigenfunctions of actions of `ℝ`

Checks for the eigenfunction criterion of weak mixing
(`MeasureTheory.Measure.isWeaklyMixing_iff_forall_eigenfunction`), whose eigenfunction equation
for `f : X → ℂ` and `a ∈ ℝ` reads `f(t +ᵥ x) = exp(2πiat) f(x)` for almost every `x`, for every
`t`.

It also gives counterexamples for the *multiplier property* of weak mixing, which is not yet in
the library: for measure-preserving actions of `ℝ` on probability spaces `X` and `Y`, if the
action on `X` is weakly mixing and the action on `Y` is ergodic, then the diagonal action
`t +ᵥ (x, y) = (t +ᵥ x, t +ᵥ y)` on `X × Y` is ergodic. Each counterexample drops one of the two
hypotheses and the conclusion fails.

* **Constants and zero.** The zero function satisfies the equation for every `a`, and a constant
  function for `a = 0`; both are almost everywhere constant, so the criterion's quantification
  over all measurable `f` is harmless. On the one-point probability space `f = 1` satisfies it for
  `a = 0` only.
* **Nonzero eigenvalues.** If `f` satisfies the equation for some `a ≠ 0` and is not almost
  everywhere zero, then `f` is not almost everywhere constant: at `t = 1/(2a)` the equation reads
  `f(t +ᵥ x) = -f(x)`.
* **The multiplier property needs `X` weakly mixing.** Take `X = Y = AddCircle 1` with the
  translation flow and the normalized Haar measure: `Y` is ergodic, but `X` is not weakly mixing,
  `e₁` being an eigenfunction of frequency `1`. The function `e₁(x) conj(e₁(y))` on `X × Y` is
  invariant under the diagonal flow and not almost everywhere constant, its integral being `0`
  and its modulus `1`, so the diagonal flow is not ergodic.
* **The multiplier property needs `Y` ergodic.** Take `X` the one-point space, whose trivial
  action is weakly mixing, and `Y` the two-point space with the trivial action and the uniform
  measure, which is not ergodic. The diagonal action on `X × Y` is not ergodic:
  `univ ×ˢ {y}` is invariant of measure `1/2`.
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
  rw [exp_two_pi_mul_one_div_two_mul_mul_I_eq_neg_one ha, h₂, h₁, Function.const_apply,
    neg_one_mul] at h₃
  rw [h₁, Function.const_apply, Pi.zero_apply]
  linear_combination h₃ / 2

end General

/-! ### The one-point space -/

/-- A one-point space, carrying the trivial action of `ℝ`. -/
def SinglePoint : Type := Unit

/-- The one-point space carries the discrete σ-algebra of `Unit`. -/
instance instMeasurableSpaceSinglePoint : MeasurableSpace SinglePoint :=
  inferInstanceAs (MeasurableSpace Unit)

instance instMeasurableSingletonClassSinglePoint : MeasurableSingletonClass SinglePoint :=
  inferInstanceAs (MeasurableSingletonClass Unit)

/-- The point of the one-point space. -/
def SinglePoint.pt : SinglePoint := ()

/-- The trivial action of `ℝ` on the one-point space. -/
instance instAddActionSinglePoint : AddAction ℝ SinglePoint where
  vadd _ x := x
  zero_vadd _ := rfl
  add_vadd _ _ _ := rfl

/-- The action of `ℝ` on the one-point space is trivial. -/
theorem SinglePoint.vadd_eq (t : ℝ) (x : SinglePoint) : t +ᵥ x = x := rfl

/-- On the one-point probability space, `f = 1` satisfies the eigenfunction equation exactly for
`a = 0`. -/
theorem singlePoint_one_eigenfunction_iff (a : ℝ) :
    (∀ t : ℝ, (fun _ : SinglePoint => (1 : ℂ)) =ᵐ[dirac SinglePoint.pt]
      fun _ => Complex.exp (2 * π * a * t * I) * 1) ↔ a = 0 := by
  simp only [Filter.EventuallyEq, ae_dirac_eq, Filter.eventually_pure, mul_one]
  refine ⟨fun h => ?_, fun h t => by simp [h]⟩
  by_contra ha
  have := h (1 / (2 * a))
  rw [exp_two_pi_mul_one_div_two_mul_mul_I_eq_neg_one ha] at this
  norm_num at this

/-! ### The multiplier property needs `X` weakly mixing -/

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
      AddCircle.integral_fourier_haarAddCircle]
    simp
  rw [integral_congr_ae hc] at hint
  simp only [Function.const_apply, integral_const, probReal_univ, one_smul] at hint
  obtain ⟨p, hp⟩ := hc.exists
  rw [hint, Function.const_apply] at hp
  simp [diagonalMode] at hp

/-! ### The multiplier property needs `Y` ergodic -/

/-- The set `univ ×ˢ {x}` of the product of the one-point and two-point spaces. -/
abbrev pointSet : Set (SinglePoint × TwoPoint) := univ ×ˢ {TwoPoint.pt true}

/-- `univ ×ˢ {x}` has measure `1/2` for the product of the Dirac and uniform measures. -/
theorem prod_pointSet :
    (dirac SinglePoint.pt).prod (uniformOn (univ : Set TwoPoint)) pointSet = 2⁻¹ := by
  rw [Measure.prod_prod, measure_univ, one_mul, uniformOn_univ, TwoPoint.card_eq]
  simp

/-- **The product of the one-point space with the trivial two-point space is not ergodic.** The
set `univ ×ˢ {x}` is invariant under the diagonal action, of measure `1/2`. -/
theorem not_ergodicVAdd_singlePoint_prod_twoPoint :
    ¬ ErgodicVAdd ℝ (SinglePoint × TwoPoint)
      ((dirac SinglePoint.pt).prod (uniformOn (univ : Set TwoPoint))) := by
  intro h
  have hs : MeasurableSet pointSet := MeasurableSet.univ.prod (measurableSet_singleton _)
  have hconst := h.aeconst_of_forall_preimage_vadd_ae_eq hs fun t => by
    have : (fun x : SinglePoint × TwoPoint => t +ᵥ x) ⁻¹' pointSet = pointSet := by
      ext ⟨x, y⟩
      simp only [mem_preimage, Prod.vadd_mk, SinglePoint.vadd_eq, TwoPoint.vadd_eq]
    rw [this]
  rcases Filter.eventuallyEmptyOrUniv_iff.1 hconst with h₁ | h₁
  · have h₂ := (prob_compl_eq_zero_iff hs).1 (ae_iff.1 h₁)
    rw [prod_pointSet] at h₂
    norm_num at h₂
  · have h₂ := measure_eq_zero_iff_ae_notMem.2 h₁
    rw [prod_pointSet] at h₂
    norm_num at h₂

end TauCeti.Examples.Eigenfunction
