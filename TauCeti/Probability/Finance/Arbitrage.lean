/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Martingale.Basic
public import TauCeti.Probability.Finance.SimpleStrategy

/-!
# Arbitrage and its absence under an equivalent martingale measure

A trade with initial cost `v` and terminal wealth `X` is an *arbitrage* under the physical
measure `P` (`TauCeti.Finance.IsArbitrage`) when it costs nothing, never loses money and makes a
profit with positive probability:

`v = 0` and `X ≥ 0` `P`-almost surely, and `P {X > 0} > 0`.

This notion depends on `P` only through its null sets, so it is the same under every equivalent
measure `Q` (`TauCeti.Finance.isArbitrage_congr_measure`), and it does not depend on the unit of
account: dividing the cost and the wealth by a positive numeraire preserves it
(`TauCeti.Finance.IsArbitrage.div`). Under `Q` an arbitrage has strictly positive expected
profit (`TauCeti.Finance.IsArbitrage.integral_lt_integral`). Hence, whenever the wealth of a
trading strategy measured in units of a positive numeraire `N`, such as the bond, is a
supermartingale under a measure `Q` equivalent to `P`, the strategy is not an arbitrage between
any two dates (`MeasureTheory.Supermartingale.not_isArbitrage`). In particular this applies when
the discounted wealth is a `Q`-martingale, the defining property of an admissible strategy in a
market with an equivalent martingale measure.

Discounted martingale wealth is also determined by its terminal value: it is the conditional
price `V_t = N_t E_Q[V_T / N_T | ℱ_t]` (`MeasureTheory.Martingale.ae_eq_mul_condExp_div`), so two
such strategies with the same terminal wealth have the same wealth at every earlier date, and in
particular the same initial cost (`MeasureTheory.Martingale.ae_eq_of_ae_eq`). This is the law of
one price.

For simple strategies the martingale property is proved rather than assumed. The gains
`∫₀ᵗ a dX` of a simple strategy with bounded positions, each chosen at the start of its trading
interval, from trading a `Q`-martingale `X` form a `Q`-martingale
(`MeasureTheory.Martingale.simpleGains`). So if the discounted stock `S / β` is a `Q`-martingale,
every self-financing simple strategy with bounded stock positions has martingale discounted gains,
and none is an arbitrage (`TauCeti.Finance.IsSelfFinancing.not_isArbitrage`).

## Main declarations

* `TauCeti.Finance.IsArbitrage`: an arbitrage, given by its initial cost and terminal wealth.
* `MeasureTheory.Supermartingale.not_isArbitrage`: no arbitrage when the wealth in units of a
  positive numeraire is a supermartingale under an equivalent measure.
* `MeasureTheory.Martingale.ae_eq_mul_condExp_div`, `MeasureTheory.Martingale.ae_eq_of_ae_eq`:
  the value process of discounted martingale wealth, and the law of one price.
* `MeasureTheory.Martingale.simpleGains`: the gains of a bounded simple strategy from trading a
  martingale form a martingale.
* `TauCeti.Finance.IsSelfFinancing.not_isArbitrage`: no self-financing simple strategy is an
  arbitrage when the discounted stock is a martingale under an equivalent measure.

## References

* H. Föllmer, A. Schied, *Stochastic Finance: An Introduction in Discrete Time*, 4th ed.,
  de Gruyter, 2016, §1.2 and §5.2.
* S. E. Shreve, *Stochastic Calculus for Finance II: Continuous-Time Models*, Springer, 2004,
  §5.4.
-/

public section

noncomputable section

open MeasureTheory Filter Finset

namespace TauCeti.Finance

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P Q : Measure Ω} {v X : Ω → ℝ}

/-! ### Arbitrage -/

/-- A trade with initial cost `v` and terminal wealth `X` is an *arbitrage* under `P` when it
costs nothing, never loses money and makes a profit with positive probability. -/
structure IsArbitrage (P : Measure Ω) (v X : Ω → ℝ) : Prop where
  /-- The trade costs nothing. -/
  cost_ae_eq_zero : v =ᵐ[P] 0
  /-- The trade never loses money. -/
  ae_nonneg : 0 ≤ᵐ[P] X
  /-- The trade makes a profit with positive probability. -/
  measure_pos : 0 < P {ω | 0 < X ω}

/-- Unfolding lemma for `IsArbitrage`. -/
theorem isArbitrage_iff :
    IsArbitrage P v X ↔ v =ᵐ[P] 0 ∧ 0 ≤ᵐ[P] X ∧ 0 < P {ω | 0 < X ω} :=
  ⟨fun h ↦ ⟨h.1, h.2, h.3⟩, fun h ↦ ⟨h.1, h.2.1, h.2.2⟩⟩

/-- Being an arbitrage depends on the measure only through its null sets, so it is the same
under equivalent measures. -/
theorem isArbitrage_congr_measure (hPQ : P ≪ Q) (hQP : Q ≪ P) :
    IsArbitrage P v X ↔ IsArbitrage Q v X := by
  -- One direction suffices, by symmetry of the hypotheses.
  have key : ∀ {P Q : Measure Ω}, P ≪ Q → Q ≪ P → IsArbitrage P v X → IsArbitrage Q v X :=
    fun hPQ hQP h ↦ ⟨hQP.ae_le h.1, hQP.ae_le h.2,
      pos_iff_ne_zero.2 fun h0 ↦ (pos_iff_ne_zero.1 h.3) (hPQ h0)⟩
  exact ⟨key hPQ hQP, key hQP hPQ⟩

/-- Arbitrage does not depend on the unit of account: dividing the cost by any random variable
and the terminal wealth by an almost surely positive one, such as the bond price at the initial
and terminal dates, preserves an arbitrage. -/
theorem IsArbitrage.div {N : Ω → ℝ} (h : IsArbitrage P v X) (hN : ∀ᵐ ω ∂P, 0 < N ω)
    (N₀ : Ω → ℝ) : IsArbitrage P (v / N₀) (X / N) where
  cost_ae_eq_zero := by filter_upwards [h.1] with ω hω; simp [hω]
  ae_nonneg := by
    filter_upwards [h.2, hN] with ω hX hNω using div_nonneg hX hNω.le
  measure_pos := by
    refine h.3.trans_eq (measure_congr ?_)
    filter_upwards [hN] with ω hNω
    simp [hNω]

/-- Under the measure defining it, an integrable arbitrage has strictly positive expected
profit: its expected terminal wealth exceeds its expected cost. -/
theorem IsArbitrage.integral_lt_integral (h : IsArbitrage P v X) (hX : Integrable X P) :
    ∫ ω, v ω ∂P < ∫ ω, X ω ∂P := by
  rw [integral_congr_ae h.1]
  simp only [Pi.zero_apply, integral_zero]
  rw [integral_pos_iff_support_of_nonneg_ae h.2 hX]
  exact h.3.trans_le (measure_mono fun ω (hω : 0 < X ω) ↦ hω.ne')

/-- A trade whose terminal wealth has, under a measure `Q` equivalent to `P`, at most the
expected value of its cost is not an arbitrage under `P`. -/
theorem not_isArbitrage_of_integral_le (hPQ : P ≪ Q) (hQP : Q ≪ P) (hX : Integrable X Q)
    (hle : ∫ ω, X ω ∂Q ≤ ∫ ω, v ω ∂Q) : ¬IsArbitrage P v X := fun h ↦
  (((isArbitrage_congr_measure hPQ hQP).1 h).integral_lt_integral hX).not_ge hle

end TauCeti.Finance

/-! ### Wealth that is a supermartingale in units of a numeraire -/

namespace MeasureTheory

open TauCeti.Finance

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {P Q : Measure Ω} [Preorder ι]
  {ℱ : Filtration ι mΩ} {V V' N : ι → Ω → ℝ} {i j : ι}

/-- **No arbitrage under an equivalent supermartingale measure.** If the wealth `V` of a strategy,
measured in units of a numeraire `N` that is positive at the later date `j`, is a supermartingale
under a measure `Q` equivalent to `P`, then trading from `i` to `j ≥ i` is not an arbitrage under
`P`. -/
theorem Supermartingale.not_isArbitrage [SigmaFiniteFiltration Q ℱ]
    (hV : Supermartingale (V / N) ℱ Q) (hPQ : P ≪ Q) (hQP : Q ≪ P) (hN : ∀ᵐ ω ∂P, 0 < N j ω)
    (hij : i ≤ j) : ¬IsArbitrage P (V i) (V j) := fun h ↦ by
  refine not_isArbitrage_of_integral_le hPQ hQP (hV.integrable j) ?_ (h.div hN (N i))
  simpa only [setIntegral_univ, Pi.div_apply] using hV.setIntegral_le hij MeasurableSet.univ

/-- The wealth `V` of a strategy whose value in units of a numeraire `N` is a martingale under a
measure `Q` with `P ≪ Q` is determined by its value at a later date `j`: at every date `i ≤ j`
at which the numeraire does not vanish, `V_i = N_i E_Q[V_j / N_j | ℱ_i]`, `P`-almost surely. -/
theorem Martingale.ae_eq_mul_condExp_div (hV : Martingale (V / N) ℱ Q) (hPQ : P ≪ Q)
    (hN : ∀ᵐ ω ∂P, N i ω ≠ 0) (hij : i ≤ j) :
    V i =ᵐ[P] N i * Q[V j / N j | ℱ i] := by
  filter_upwards [hPQ.ae_le (hV.condExp_ae_eq hij), hN] with ω hω hNω
  simp only [Pi.mul_apply, Pi.div_apply] at hω ⊢
  rw [hω]
  field_simp

/-- **The law of one price.** Two strategies whose wealth in units of a common numeraire `N` is a
martingale under a measure `Q` equivalent to `P`, and whose wealth agrees at a date `j`, have the
same wealth at every earlier date `i` at which the numeraire does not vanish; in particular the
same initial cost. -/
theorem Martingale.ae_eq_of_ae_eq (hV : Martingale (V / N) ℱ Q) (hV' : Martingale (V' / N) ℱ Q)
    (hPQ : P ≪ Q) (hQP : Q ≪ P) (hN : ∀ᵐ ω ∂P, N i ω ≠ 0) (hij : i ≤ j)
    (hj : V j =ᵐ[P] V' j) : V i =ᵐ[P] V' i := by
  have hcond : Q[V j / N j | ℱ i] =ᵐ[Q] Q[V' j / N j | ℱ i] := by
    refine condExp_congr_ae ?_
    filter_upwards [hQP.ae_le hj] with ω hω
    simp only [Pi.div_apply, hω]
  filter_upwards [hV.ae_eq_mul_condExp_div hPQ hN hij, hV'.ae_eq_mul_condExp_div hPQ hN hij,
    hPQ.ae_le hcond] with ω h₁ h₂ h₃
  rw [h₁, h₂, Pi.mul_apply, Pi.mul_apply, h₃]

end MeasureTheory

/-! ### The gains of a simple strategy from trading a martingale -/

namespace MeasureTheory

open TauCeti.Finance

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {Q : Measure Ω} [LinearOrder ι]
  {ℱ : Filtration ι mΩ} {τ : ℕ → ι} {n : ℕ} {a : ℕ → Ω → ℝ} {X : ι → Ω → ℝ}

/-- **The gains of a simple strategy from trading a martingale form a martingale.** If `X` is a
martingale and the position `a j` held on `(τ j, τ (j + 1)]` is bounded and chosen at time
`τ j`, then the elementary integral `t ↦ ∫₀ᵗ a dX` is a martingale. -/
theorem Martingale.simpleGains [SigmaFiniteFiltration Q ℱ] (hX : Martingale X ℱ Q)
    (hτ : MonotoneOn τ (Set.Iic n)) (ha : ∀ j < n, StronglyMeasurable[ℱ (τ j)] (a j))
    (ha_bdd : ∀ j < n, ∃ C, ∀ᵐ ω ∂Q, |a j ω| ≤ C) :
    Martingale (TauCeti.Finance.simpleGains τ n a X) ℱ Q := by
  -- The gains on the `j`-th interval up to time `t` are `a j * D j t`.
  obtain ⟨D, hD⟩ :
      ∃ D : ℕ → ι → Ω → ℝ, ∀ j t, D j t = X (min (τ (j + 1)) t) - X (min (τ j) t) :=
    ⟨_, fun _ _ ↦ rfl⟩
  have hDint : ∀ j t, Integrable (D j t) Q := fun j t ↦ by
    rw [hD]
    exact (hX.integrable _).sub (hX.integrable _)
  -- A martingale stopped at a deterministic date `w` is a martingale, hence so is each `D j`.
  have hstop : ∀ w s t, s ≤ t → Q[X (min w t) | ℱ s] =ᵐ[Q] X (min w s) := by
    intro w s t hst
    rcases le_or_gt w s with hws | hsw
    · rw [min_eq_left (hws.trans hst), min_eq_left hws,
        condExp_of_stronglyMeasurable (ℱ.le s) ((hX.stronglyAdapted w).mono (ℱ.mono hws))
          (hX.integrable w)]
    · rw [min_eq_right hsw.le]
      exact hX.condExp_ae_eq (le_min hsw.le hst)
  have hDmart : ∀ j s t, s ≤ t → Q[D j t | ℱ s] =ᵐ[Q] D j s := fun j s t hst ↦ by
    rw [hD, hD]
    exact (condExp_sub (hX.integrable _) (hX.integrable _) _).trans
      ((hstop _ s t hst).sub (hstop _ s t hst))
  have hmul : ∀ j < n, ∀ t, Integrable (a j * D j t) Q := fun j hj t ↦ by
    obtain ⟨C, hC⟩ := ha_bdd j hj
    exact (hDint j t).bdd_mul ((ha j hj).mono (ℱ.le _)).aestronglyMeasurable
      (hC.mono fun ω hω ↦ by rwa [Real.norm_eq_abs])
  have hterm : ∀ j < n, ∀ s t, s ≤ t → Q[a j * D j t | ℱ s] =ᵐ[Q] a j * D j s := by
    intro j hj
    have hjj : τ j ≤ τ (j + 1) := hτ hj.le (Nat.succ_le_of_lt hj) (Nat.le_succ j)
    -- Before the interval starts there are no gains.
    have hD₀ : ∀ t ≤ τ j, D j t = 0 := fun t ht ↦ by
      rw [hD, min_eq_right ht, min_eq_right (ht.trans hjj), sub_self]
    -- Once the position is known, it factors out of the conditional expectation.
    have hlate : ∀ s t, τ j ≤ s → s ≤ t → Q[a j * D j t | ℱ s] =ᵐ[Q] a j * D j s :=
      fun s t hjs hst ↦ (condExp_mul_of_stronglyMeasurable_left
        ((ha j hj).mono (ℱ.mono hjs)) (hmul j hj t) (hDint j t)).trans
          ((EventuallyEq.refl _ _).mul (hDmart j s t hst))
    intro s t hst
    rcases le_or_gt (τ j) s with hjs | hsj
    · exact hlate s t hjs hst
    rw [hD₀ s hsj.le, mul_zero]
    rcases le_or_gt t (τ j) with htj | hjt
    · rw [hD₀ t htj, mul_zero, condExp_zero]
    -- Otherwise condition first on the information at `τ j`, where the gains still vanish.
    calc Q[a j * D j t | ℱ s]
        =ᵐ[Q] Q[Q[a j * D j t | ℱ (τ j)] | ℱ s] :=
          (condExp_condExp_of_le (ℱ.mono hsj.le) (ℱ.le (τ j))).symm
      _ =ᵐ[Q] Q[a j * D j (τ j) | ℱ s] := condExp_congr_ae (hlate (τ j) t le_rfl hjt.le)
      _ = 0 := by rw [hD₀ _ le_rfl, mul_zero, condExp_zero]
  have hsum : ∀ u, TauCeti.Finance.simpleGains τ n a X u = ∑ j ∈ range n, a j * D j u :=
    fun u ↦ funext fun ω ↦ by simp [simpleGains_def, hD, Finset.sum_apply]
  refine ⟨stronglyAdapted_simpleGains hτ ha hX.stronglyAdapted, fun s t hst ↦ ?_⟩
  rw [hsum t, hsum s]
  refine (condExp_finsetSum (fun j hj ↦ hmul j (mem_range.1 hj) t) _).trans ?_
  filter_upwards [(Finset.eventually_all _).2 fun j hj ↦ hterm j (mem_range.1 hj) s t hst]
    with ω hω
  simp only [Finset.sum_apply]
  exact Finset.sum_congr rfl hω

end MeasureTheory

namespace TauCeti.Finance

open MeasureTheory

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {P Q : Measure Ω} [LinearOrder ι]
  {ℱ : Filtration ι mΩ} {τ : ℕ → ι} {n : ℕ} {a b : ℕ → Ω → ℝ} {S β : ι → Ω → ℝ}

/-- **No arbitrage with simple strategies.** Suppose the bond price `β` is positive during the
trading period `[τ 0, τ (n + 1)]` and the discounted stock `S / β` is a martingale under a measure
`Q` equivalent to `P`. Then a self-financing simple strategy whose stock positions are bounded
and chosen at the start of their trading intervals is not an arbitrage: its initial cost
`a 0 S (τ 0) + b 0 β (τ 0)` and terminal wealth `a n S (τ (n + 1)) + b n β (τ (n + 1))` do not
form one. -/
theorem IsSelfFinancing.not_isArbitrage [SigmaFiniteFiltration Q ℱ]
    (h : IsSelfFinancing τ (n + 1) a b S β) (hτ : MonotoneOn τ (Set.Iic (n + 1)))
    (hβ : ∀ t ∈ Set.Icc (τ 0) (τ (n + 1)), ∀ ω, 0 < β t ω) (hX : Martingale (S / β) ℱ Q)
    (ha : ∀ j < n + 1, StronglyMeasurable[ℱ (τ j)] (a j))
    (ha_bdd : ∀ j < n + 1, ∃ C, ∀ᵐ ω ∂Q, |a j ω| ≤ C) (hPQ : P ≪ Q) (hQP : Q ≪ P) :
    ¬IsArbitrage P (fun ω ↦ a 0 ω * S (τ 0) ω + b 0 ω * β (τ 0) ω)
      (fun ω ↦ a n ω * S (τ (n + 1)) ω + b n ω * β (τ (n + 1)) ω) := fun hA ↦ by
  have hG : Martingale (simpleGains τ (n + 1) a (S / β)) ℱ Q := hX.simpleGains hτ ha ha_bdd
  have hT : τ (n + 1) ∈ Set.Icc (τ 0) (τ (n + 1)) :=
    ⟨hτ (Nat.zero_le _) Set.self_mem_Iic (Nat.zero_le _), le_rfl⟩
  have hA' := hA.div (ae_of_all _ (hβ _ hT)) (β (τ 0))
  -- Discounted, the terminal wealth is the initial discounted cost, which vanishes, plus the gains.
  have hdisc := (isSelfFinancing_iff_discounted hτ fun t ht ω ↦ (hβ t ht ω).ne').1 h n
    (Nat.lt_succ_self n)
  have hwealth : (fun ω ↦ a n ω * S (τ (n + 1)) ω + b n ω * β (τ (n + 1)) ω) / β (τ (n + 1))
      =ᵐ[Q] simpleGains τ (n + 1) a (S / β) (τ (n + 1)) := by
    filter_upwards [hQP.ae_le hA'.1] with ω hω
    simp only [Pi.div_apply]
    rw [hdisc ω _ ⟨hτ (Nat.le_succ n) Set.self_mem_Iic (Nat.le_succ n), le_rfl⟩]
    simp only [Pi.div_apply, Pi.zero_apply] at hω
    rw [hω, zero_add]
  -- The gains start at `0` and form a martingale, so their expectation vanishes.
  have hG₀ : ∫ ω, simpleGains τ (n + 1) a (S / β) (τ (n + 1)) ω ∂Q = 0 := by
    rw [← setIntegral_univ, ← hG.setIntegral_eq hT.1 MeasurableSet.univ, setIntegral_univ]
    simp [simpleGains_of_le hτ le_rfl]
  refine not_isArbitrage_of_integral_le hPQ hQP ((hG.integrable _).congr hwealth.symm) ?_ hA'
  rw [integral_congr_ae hwealth, hG₀, integral_congr_ae (hQP.ae_le hA'.1)]
  simp

end TauCeti.Finance
