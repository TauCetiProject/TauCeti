/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Martingale.Basic

/-!
# Martingales frozen at a date, bounded positions taken at a date, and division by a process

`MeasureTheory.StronglyAdapted.martingale_iff_setIntegral_eq` characterizes martingales
among adapted integrable processes by equality of set integrals at two dates. This is useful
for transporting martingales between measures without comparing conditional-expectation
representatives.

Two closure properties of martingales indexed by a linear order, the building blocks of the
elementary stochastic integral:

* a martingale `X` with values in a Banach space, frozen at a fixed date `w`, `t ↦ X (min w t)`,
  is a martingale (`MeasureTheory.Martingale.const_min`);
* if a real martingale `Y` vanishes up to a date `r`, then multiplying it by a random variable
  known at time `r` gives a martingale, provided every product is integrable, as it is for a
  bounded multiplier (`MeasureTheory.Martingale.mul_left_of_eq_zero`).

Together they show that a position chosen at `r`, times the change of a martingale over
`(r, r']`, is a martingale whenever this product is integrable at every time.

If `V / N` is a martingale under `Q` for a real process `N`, then `V` is recovered from its value
at a later date `j` as `V i = N i * Q[V j / N j | ℱ i]` wherever `N i` does not vanish
(`MeasureTheory.Martingale.ae_eq_mul_condExp_div`), so two such processes agreeing at `j` agree at
every earlier date (`MeasureTheory.Martingale.ae_eq_of_ae_eq_of_div`). In finance `N` is a
numeraire, the first statement is the conditional pricing formula and the second the law of one
price.
-/

public section

noncomputable section

open Filter

namespace MeasureTheory

/-- An adapted integrable process is a martingale exactly when its integrals on every
event known at an earlier date are unchanged between the two dates. -/
theorem StronglyAdapted.martingale_iff_setIntegral_eq {Ω ι E : Type*}
    {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [Preorder ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {ℱ : Filtration ι mΩ} [SigmaFiniteFiltration μ ℱ] {X : ι → Ω → E}
    (hX : StronglyAdapted ℱ X) (hint : ∀ t, Integrable (X t) μ) :
    Martingale X ℱ μ ↔ ∀ s t, s ≤ t → ∀ A, MeasurableSet[ℱ s] A →
      ∫ ω in A, X s ω ∂μ = ∫ ω in A, X t ω ∂μ := by
  refine ⟨fun h s t hst A hA ↦ h.setIntegral_eq hst hA, fun h ↦ ⟨hX, ?_⟩⟩
  intro s t hst
  exact (ae_eq_condExp_of_forall_setIntegral_eq (ℱ.le s) (hint t)
    (fun _ _ _ ↦ (hint s).integrableOn) (fun A hA _ ↦ h s t hst A hA)
    (hX s).aestronglyMeasurable).symm

section Div

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {P Q : Measure Ω} [Preorder ι]
  {ℱ : Filtration ι mΩ} {V V' N : ι → Ω → ℝ} {i j : ι}

/-- If `V / N` is a martingale under a measure `Q` with `P ≪ Q`, then `V` is determined by its
value at a later date `j`: at every date `i ≤ j` at which `N` does not vanish,
`V_i = N_i E_Q[V_j / N_j | ℱ_i]`, `P`-almost surely. For the wealth `V` of a strategy and a
numeraire `N`, this is the conditional pricing formula. -/
theorem Martingale.ae_eq_mul_condExp_div (hV : Martingale (V / N) ℱ Q) (hPQ : P ≪ Q)
    (hN : ∀ᵐ ω ∂P, N i ω ≠ 0) (hij : i ≤ j) :
    V i =ᵐ[P] N i * Q[V j / N j | ℱ i] := by
  filter_upwards [hPQ.ae_le (hV.condExp_ae_eq hij), hN] with ω hω hNω
  simp only [Pi.mul_apply, Pi.div_apply] at hω ⊢
  rw [hω]
  field_simp

/-- If `V / N` and `V' / N` are martingales under a measure `Q` equivalent to `P`, and `V` and
`V'` agree at a date `j`, then they agree at every earlier date `i` at which `N` does not
vanish. For the wealth of two strategies and a common numeraire `N`, this is the law of one
price: in particular the two strategies have the same initial cost. -/
theorem Martingale.ae_eq_of_ae_eq_of_div (hV : Martingale (V / N) ℱ Q)
    (hV' : Martingale (V' / N) ℱ Q) (hPQ : P ≪ Q) (hQP : Q ≪ P) (hN : ∀ᵐ ω ∂P, N i ω ≠ 0)
    (hij : i ≤ j) (hj : V j =ᵐ[P] V' j) : V i =ᵐ[P] V' i := by
  have hcond : Q[V j / N j | ℱ i] =ᵐ[Q] Q[V' j / N j | ℱ i] := by
    refine condExp_congr_ae ?_
    filter_upwards [hQP.ae_le hj] with ω hω
    simp only [Pi.div_apply, hω]
  filter_upwards [hV.ae_eq_mul_condExp_div hPQ hN hij, hV'.ae_eq_mul_condExp_div hPQ hN hij,
    hPQ.ae_le hcond] with ω h₁ h₂ h₃
  rw [h₁, h₂, Pi.mul_apply, Pi.mul_apply, h₃]

end Div

variable {Ω ι E : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [LinearOrder ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {ℱ : Filtration ι mΩ} {X : ι → Ω → E} {Y : ι → Ω → ℝ}

/-- A martingale frozen at a fixed date `w`, `t ↦ X (min w t)`, is a martingale. -/
theorem Martingale.const_min [SigmaFiniteFiltration μ ℱ] (hX : Martingale X ℱ μ) (w : ι) :
    Martingale (fun t ↦ X (min w t)) ℱ μ := by
  refine ⟨fun t ↦ hX.stronglyAdapted.stronglyMeasurable_le (min_le_right _ _),
    fun s t hst ↦ ?_⟩
  beta_reduce
  rcases le_or_gt w s with hws | hsw
  · rw [min_eq_left (hws.trans hst), min_eq_left hws,
      condExp_of_stronglyMeasurable (ℱ.le s) ((hX.stronglyAdapted w).mono (ℱ.mono hws))
        (hX.integrable w)]
  · rw [min_eq_right hsw.le]
    exact hX.condExp_ae_eq (le_min hsw.le hst)

/-- If a martingale `Y` vanishes up to a date `r`, and `a` is a random variable known at time `r`
such that every product `a * Y t` is integrable, then `t ↦ a * Y t` is a martingale. -/
theorem Martingale.mul_left_of_eq_zero [SigmaFiniteFiltration μ ℱ] {a : Ω → ℝ} {r : ι}
    (hY : Martingale Y ℱ μ) (hY₀ : ∀ t ≤ r, Y t = 0) (ha : StronglyMeasurable[ℱ r] a)
    (hmul : ∀ t, Integrable (a * Y t) μ) : Martingale (fun t ↦ a * Y t) ℱ μ := by
  -- Once `a` is known, it factors out of the conditional expectation.
  have hlate : ∀ s t, r ≤ s → s ≤ t → μ[a * Y t | ℱ s] =ᵐ[μ] a * Y s := fun s t hrs hst ↦
    (condExp_mul_of_stronglyMeasurable_left (ha.mono (ℱ.mono hrs)) (hmul t)
      (hY.integrable t)).trans ((EventuallyEq.refl _ _).mul (hY.condExp_ae_eq hst))
  refine ⟨fun t ↦ ?_, fun s t hst ↦ ?_⟩
  · rcases le_or_gt r t with hrt | htr
    · exact (ha.mono (ℱ.mono hrt)).mul (hY.stronglyMeasurable t)
    · simp only [hY₀ t htr.le, mul_zero]
      exact stronglyMeasurable_zero
  beta_reduce
  rcases le_or_gt r s with hrs | hsr
  · exact hlate s t hrs hst
  rw [hY₀ s hsr.le, mul_zero]
  rcases le_or_gt t r with htr | hrt
  · rw [hY₀ t htr, mul_zero, condExp_zero]
  -- Otherwise condition first on the information at `r`, where `Y` still vanishes.
  calc μ[a * Y t | ℱ s]
      =ᵐ[μ] μ[μ[a * Y t | ℱ r] | ℱ s] :=
        (condExp_condExp_of_le (ℱ.mono hsr.le) (ℱ.le r)).symm
    _ =ᵐ[μ] μ[a * Y r | ℱ s] := condExp_congr_ae (hlate r t le_rfl hrt.le)
    _ = 0 := by rw [hY₀ r le_rfl, mul_zero, condExp_zero]

end MeasureTheory
