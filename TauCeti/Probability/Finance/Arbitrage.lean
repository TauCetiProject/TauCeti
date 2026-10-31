/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import TauCeti.Probability.Finance.SimpleStrategy

/-!
# Arbitrage and martingale measures for simple strategies

A trade with initial cost `v` and terminal wealth `V` is an **arbitrage** under a probability
measure `P` (`TauCeti.Finance.IsArbitrage`) if it costs nothing almost surely, never ends with a
loss almost surely, and ends with a gain with positive probability. The notion depends only on
the null sets of `P` (`TauCeti.Finance.isArbitrage_iff_of_absolutelyContinuous`) and not on the
unit of account (`TauCeti.Finance.isArbitrage_mul_iff`). An arbitrage with integrable terminal
wealth has positive expected terminal wealth (`TauCeti.Finance.IsArbitrage.integral_pos`).

This file proves the easy half of the fundamental theorem of asset pricing for the simple
strategies of `TauCeti.Probability.Finance.SimpleStrategy`. Suppose that, under a measure `Q`,
the discounted stock price `X = S / β` is a martingale along the trading dates `τ 0, …, τ n`:
each `X (τ j)` is integrable and `ℱ (τ j)`-measurable, and `E_Q[X (τ (j + 1)) | ℱ (τ j)] = X (τ j)`.
Then for a stock holding `a j` chosen at `τ j` with integrable trading gains:

* the gains `∫ a dX` are a `Q`-martingale along the trading dates
  (`TauCeti.Finance.condExp_simpleGains`) with mean zero
  (`TauCeti.Finance.integral_simpleGains`);
* the discounted wealth of a self-financing strategy at each trading date is the conditional
  expectation of its discounted terminal wealth
  (`TauCeti.Finance.IsSelfFinancing.condExp_discounted_wealth`), so the terminal wealth determines
  the wealth at every trading date;
* if moreover `Q` and `P` have the same null sets and the bond price is positive, no
  self-financing strategy is an arbitrage under `P`
  (`TauCeti.Finance.IsSelfFinancing.not_isArbitrage`).

No integrability of the holdings themselves is assumed beyond that of each trading gain
`a j (X (τ (j + 1)) - X (τ j))`, and the bond holdings need no integrability at all.

## References

* J. M. Harrison, S. R. Pliska, *Martingales and stochastic integrals in the theory of continuous
  trading*, Stochastic Process. Appl. 11 (1981), 215–260, §2–§3.
* H. Föllmer, A. Schied, *Stochastic Finance: An Introduction in Discrete Time*, 4th ed.,
  de Gruyter, 2016, §5.2.
* S. E. Shreve, *Stochastic Calculus for Finance II: Continuous-Time Models*, Springer, 2004,
  §5.4.3.
-/

public section

noncomputable section

open MeasureTheory Finset

namespace TauCeti.Finance

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {P Q : Measure Ω} {v V c₀ c : Ω → ℝ}

/-! ### Arbitrage -/

/-- A trade with initial cost `v` and terminal wealth `V` is an **arbitrage** under `P` if it
costs nothing almost surely, its terminal wealth is nonnegative almost surely, and its terminal
wealth is positive with positive probability. -/
def IsArbitrage (P : Measure Ω) (v V : Ω → ℝ) : Prop :=
  v =ᵐ[P] 0 ∧ 0 ≤ᵐ[P] V ∧ 0 < P {ω | 0 < V ω}

/-- Unfolding lemma for `IsArbitrage`. -/
theorem isArbitrage_iff :
    IsArbitrage P v V ↔ v =ᵐ[P] 0 ∧ 0 ≤ᵐ[P] V ∧ 0 < P {ω | 0 < V ω} :=
  Iff.rfl

/-- Arbitrage depends only on the null sets of the measure: it is the same under equivalent
measures. -/
theorem isArbitrage_iff_of_absolutelyContinuous (hPQ : P ≪ Q) (hQP : Q ≪ P) :
    IsArbitrage P v V ↔ IsArbitrage Q v V := by
  refine and_congr ⟨hQP.ae_eq, hPQ.ae_eq⟩
    (and_congr ⟨fun h ↦ hQP.ae_le h, fun h ↦ hPQ.ae_le h⟩ ?_)
  simp only [pos_iff_ne_zero]
  exact ⟨mt fun h ↦ hPQ h, mt fun h ↦ hQP h⟩

/-- Arbitrage does not depend on the unit of account: rescaling the initial cost by a nonvanishing
factor and the terminal wealth by a positive factor preserves it. -/
theorem isArbitrage_mul_iff (hc₀ : ∀ ω, c₀ ω ≠ 0) (hc : ∀ ω, 0 < c ω) :
    IsArbitrage P (c₀ * v) (c * V) ↔ IsArbitrage P v V := by
  have hv : ∀ ω, (c₀ * v) ω = 0 ↔ v ω = 0 := fun ω ↦ by simp [hc₀ ω]
  have hV : ∀ ω, 0 ≤ (c * V) ω ↔ 0 ≤ V ω := fun ω ↦ by simp [mul_nonneg_iff_of_pos_left (hc ω)]
  have hV' : ∀ ω, 0 < (c * V) ω ↔ 0 < V ω := fun ω ↦ by simp [mul_pos_iff_of_pos_left (hc ω)]
  simp only [isArbitrage_iff, Filter.EventuallyEq, Filter.EventuallyLE, Pi.zero_apply, hv, hV,
    hV']

/-- An arbitrage with integrable terminal wealth has positive expected terminal wealth. -/
theorem IsArbitrage.integral_pos (h : IsArbitrage P v V) (hV : Integrable V P) :
    0 < ∫ ω, V ω ∂P :=
  (integral_pos_iff_support_of_nonneg_ae h.2.1 hV).2 <|
    h.2.2.trans_le (measure_mono fun _ hω ↦ ne_of_gt hω)

/-! ### Gains from trading a martingale -/

section Gains

variable [LinearOrder ι] {ℱ : Filtration ι mΩ} {τ : ℕ → ι} {n k m : ℕ} {a : ℕ → Ω → ℝ}
  {X : ι → Ω → ℝ}

/-- The gains of a simple strategy at a trading date are integrable when each of its trades has
integrable gains. -/
theorem integrable_simpleGains (hτ : MonotoneOn τ (Set.Iic n))
    (hint : ∀ j < n, Integrable (a j * (X (τ (j + 1)) - X (τ j))) Q) (hm : m ≤ n) :
    Integrable (simpleGains τ n a X (τ m)) Q := by
  simp_rw [funext (simpleGains_apply_eq_sum hτ hm X)]
  exact integrable_finsetSum _ fun i hi ↦ hint i ((mem_range.1 hi).trans_le hm)

variable [IsFiniteMeasure Q]

/-- **Gains from trading a martingale form a martingale.** If `X` is a `Q`-martingale along the
trading dates of a simple strategy whose holdings `a j` are chosen at `τ j` and whose trades have
integrable gains, then for `k ≤ m ≤ n` the conditional expectation given `ℱ (τ k)` of the gains up
to `τ m` is the gains up to `τ k`. -/
theorem condExp_simpleGains (hτ : MonotoneOn τ (Set.Iic n))
    (hXm : ∀ j ≤ n, StronglyMeasurable[ℱ (τ j)] (X (τ j)))
    (hXi : ∀ j ≤ n, Integrable (X (τ j)) Q)
    (hX : ∀ j < n, Q[X (τ (j + 1)) | ℱ (τ j)] =ᵐ[Q] X (τ j))
    (ha : ∀ j < n, StronglyMeasurable[ℱ (τ j)] (a j))
    (hint : ∀ j < n, Integrable (a j * (X (τ (j + 1)) - X (τ j))) Q) (hkm : k ≤ m) (hm : m ≤ n) :
    Q[simpleGains τ n a X (τ m) | ℱ (τ k)] =ᵐ[Q] simpleGains τ n a X (τ k) := by
  have hle : ∀ i j, i ≤ j → j ≤ n → ℱ (τ i) ≤ ℱ (τ j) := fun i j hij hj ↦
    ℱ.mono (hτ (hij.trans hj) hj hij)
  -- Each trade has conditional mean zero given the information at its start.
  have htrade : ∀ i < n, Q[a i * (X (τ (i + 1)) - X (τ i)) | ℱ (τ i)] =ᵐ[Q] 0 := fun i hi ↦ by
    filter_upwards [condExp_mul_of_stronglyMeasurable_left (ha i hi) (hint i hi)
        ((hXi _ hi).sub (hXi _ hi.le)), condExp_sub (hXi _ hi) (hXi _ hi.le) (ℱ (τ i)), hX i hi]
      with ω h₁ h₂ h₃
    rw [h₁, Pi.mul_apply, h₂, Pi.sub_apply, h₃,
      condExp_of_stronglyMeasurable (ℱ.le _) (hXm i hi.le) (hXi i hi.le), sub_self, mul_zero,
      Pi.zero_apply]
  -- So does every later trade, given the information at `τ k`.
  have hlater : ∀ i ∈ Ico k m, Q[a i * (X (τ (i + 1)) - X (τ i)) | ℱ (τ k)] =ᵐ[Q] 0 :=
    fun i hi ↦ by
      obtain ⟨hki, him⟩ := mem_Ico.1 hi
      have hin : i < n := him.trans_le hm
      refine (condExp_condExp_of_le (hle k i hki hin.le) (ℱ.le _)).symm.trans ?_
      exact (condExp_congr_ae (htrade i hin)).trans (by rw [condExp_zero])
  -- The gains up to `τ m` are the gains up to `τ k` plus the trades in between.
  have hsplit : simpleGains τ n a X (τ m) =
      simpleGains τ n a X (τ k) + ∑ i ∈ Ico k m, a i * (X (τ (i + 1)) - X (τ i)) := by
    ext ω
    simp only [simpleGains_apply_eq_sum hτ hm, simpleGains_apply_eq_sum hτ (hkm.trans hm),
      Pi.add_apply, Finset.sum_apply, Pi.mul_apply, Pi.sub_apply, sum_range_add_sum_Ico _ hkm]
  have hGk : StronglyMeasurable[ℱ (τ k)] (simpleGains τ n a X (τ k)) := by
    simp_rw [funext (simpleGains_apply_eq_sum hτ (hkm.trans hm) X)]
    refine Finset.stronglyMeasurable_fun_sum _ fun i hi ↦ ?_
    have hik : i + 1 ≤ k := mem_range.1 hi
    have hin : i + 1 ≤ n := hik.trans (hkm.trans hm)
    exact ((ha i hin).mono (hle i k (by omega) (hkm.trans hm))).mul
      (((hXm _ hin).mono (hle _ k hik (hkm.trans hm))).sub
        ((hXm i (by omega)).mono (hle i k (by omega) (hkm.trans hm))))
  have hGki := integrable_simpleGains hτ hint (hkm.trans hm)
  have htradei : ∀ i ∈ Ico k m, Integrable (a i * (X (τ (i + 1)) - X (τ i))) Q :=
    fun i hi ↦ hint i ((mem_Ico.1 hi).2.trans_le hm)
  rw [hsplit]
  filter_upwards [condExp_add hGki (integrable_finsetSum' _ htradei) (ℱ (τ k)),
    condExp_finsetSum htradei (ℱ (τ k)), (Filter.eventually_all_finset _).2 hlater] with ω h₁ h₂ h₃
  rw [h₁, Pi.add_apply, h₂, condExp_of_stronglyMeasurable (ℱ.le _) hGk hGki, Finset.sum_apply,
    sum_eq_zero h₃, add_zero]

/-- **Gains from trading a martingale have mean zero.** Under the hypotheses of
`TauCeti.Finance.condExp_simpleGains`, the gains up to every trading date `τ m` have
`Q`-expectation zero. -/
theorem integral_simpleGains (hτ : MonotoneOn τ (Set.Iic n))
    (hXm : ∀ j ≤ n, StronglyMeasurable[ℱ (τ j)] (X (τ j)))
    (hXi : ∀ j ≤ n, Integrable (X (τ j)) Q)
    (hX : ∀ j < n, Q[X (τ (j + 1)) | ℱ (τ j)] =ᵐ[Q] X (τ j))
    (ha : ∀ j < n, StronglyMeasurable[ℱ (τ j)] (a j))
    (hint : ∀ j < n, Integrable (a j * (X (τ (j + 1)) - X (τ j))) Q) (hm : m ≤ n) :
    ∫ ω, simpleGains τ n a X (τ m) ω ∂Q = 0 := by
  rw [← integral_condExp (ℱ.le (τ 0)),
    integral_congr_ae (condExp_simpleGains hτ hXm hXi hX ha hint (Nat.zero_le m) hm)]
  simp [simpleGains_of_le hτ le_rfl]

end Gains

/-! ### Self-financing strategies under a martingale measure -/

section SelfFinancing

variable [LinearOrder ι] {ℱ : Filtration ι mΩ} {τ : ℕ → ι} {n k : ℕ} {a b : ℕ → Ω → ℝ}
  {S β : ι → Ω → ℝ} [IsFiniteMeasure Q]

/-- **The discounted wealth process is a martingale.** Let the discounted stock price `S / β` be a
`Q`-martingale along the trading dates of a self-financing simple strategy whose stock holdings
`a j` are chosen at `τ j` and whose trades in the discounted stock have integrable gains, and let
the discounted initial cost be integrable and known at `τ 0`. Then for every `k ≤ n` the discounted
cost of the portfolio formed at `τ k` is the conditional expectation given `ℱ (τ k)` of the
discounted terminal wealth. In particular the terminal wealth determines the wealth at every
trading date. -/
theorem IsSelfFinancing.condExp_discounted_wealth (h : IsSelfFinancing τ (n + 1) a b S β)
    (hτ : MonotoneOn τ (Set.Iic (n + 1))) (hβ : ∀ t ∈ Set.Icc (τ 0) (τ (n + 1)), ∀ ω, β t ω ≠ 0)
    (hvm : StronglyMeasurable[ℱ (τ 0)]
      fun ω ↦ (a 0 ω * S (τ 0) ω + b 0 ω * β (τ 0) ω) / β (τ 0) ω)
    (hvi : Integrable (fun ω ↦ (a 0 ω * S (τ 0) ω + b 0 ω * β (τ 0) ω) / β (τ 0) ω) Q)
    (hXm : ∀ j ≤ n + 1, StronglyMeasurable[ℱ (τ j)] ((S / β) (τ j)))
    (hXi : ∀ j ≤ n + 1, Integrable ((S / β) (τ j)) Q)
    (hX : ∀ j < n + 1, Q[(S / β) (τ (j + 1)) | ℱ (τ j)] =ᵐ[Q] (S / β) (τ j))
    (ha : ∀ j < n + 1, StronglyMeasurable[ℱ (τ j)] (a j))
    (hint : ∀ j < n + 1, Integrable (a j * ((S / β) (τ (j + 1)) - (S / β) (τ j))) Q)
    (hk : k ≤ n) :
    Q[fun ω ↦ (a n ω * S (τ (n + 1)) ω + b n ω * β (τ (n + 1)) ω) / β (τ (n + 1)) ω | ℱ (τ k)]
      =ᵐ[Q] fun ω ↦ (a k ω * S (τ k) ω + b k ω * β (τ k) ω) / β (τ k) ω := by
  have hdisc := (isSelfFinancing_iff_discounted hτ hβ).1 h
  have hle : τ 0 ≤ τ (k + 1) := hτ (Nat.zero_le _) (by simp; omega) (Nat.zero_le _)
  have hk' : τ k ≤ τ (k + 1) := hτ (by simp; omega) (by simp; omega) (Nat.le_succ k)
  -- Both sides are the discounted initial cost plus the gains from the discounted stock.
  have hT : (fun ω ↦ (a n ω * S (τ (n + 1)) ω + b n ω * β (τ (n + 1)) ω) / β (τ (n + 1)) ω) =
      (fun ω ↦ (a 0 ω * S (τ 0) ω + b 0 ω * β (τ 0) ω) / β (τ 0) ω) +
        simpleGains τ (n + 1) a (S / β) (τ (n + 1)) := by
    ext ω
    exact hdisc n (Nat.lt_succ_self n) ω _
      ⟨hτ (by simp) (by simp) (Nat.le_succ n), le_rfl⟩
  have hK : (fun ω ↦ (a k ω * S (τ k) ω + b k ω * β (τ k) ω) / β (τ k) ω) =
      (fun ω ↦ (a 0 ω * S (τ 0) ω + b 0 ω * β (τ 0) ω) / β (τ 0) ω) +
        simpleGains τ (n + 1) a (S / β) (τ k) := by
    ext ω
    exact hdisc k (by omega) ω _ ⟨le_rfl, hk'⟩
  have hvk := hvm.mono (ℱ.mono (hτ (Nat.zero_le _) (by simp; omega) (Nat.zero_le k)))
  rw [hT, hK]
  filter_upwards [condExp_add hvi (integrable_simpleGains hτ hint le_rfl) (ℱ (τ k)),
    condExp_simpleGains hτ hXm hXi hX ha hint (by omega : k ≤ n + 1) le_rfl] with ω h₁ h₂
  rw [h₁, Pi.add_apply, Pi.add_apply, h₂, condExp_of_stronglyMeasurable (ℱ.le _) hvk hvi]

/-- **No arbitrage under an equivalent martingale measure.** Let `Q` have the same null sets as
`P`, let the bond price be positive and let the discounted stock price `S / β` be a `Q`-martingale
along the trading dates. Then no self-financing simple strategy whose stock holdings `a j` are
chosen at `τ j` and whose trades in the discounted stock have `Q`-integrable gains is an
arbitrage under `P`. -/
theorem IsSelfFinancing.not_isArbitrage (hPQ : P ≪ Q) (hQP : Q ≪ P)
    (h : IsSelfFinancing τ (n + 1) a b S β) (hτ : MonotoneOn τ (Set.Iic (n + 1)))
    (hβ : ∀ t ∈ Set.Icc (τ 0) (τ (n + 1)), ∀ ω, 0 < β t ω)
    (hXm : ∀ j ≤ n + 1, StronglyMeasurable[ℱ (τ j)] ((S / β) (τ j)))
    (hXi : ∀ j ≤ n + 1, Integrable ((S / β) (τ j)) Q)
    (hX : ∀ j < n + 1, Q[(S / β) (τ (j + 1)) | ℱ (τ j)] =ᵐ[Q] (S / β) (τ j))
    (ha : ∀ j < n + 1, StronglyMeasurable[ℱ (τ j)] (a j))
    (hint : ∀ j < n + 1, Integrable (a j * ((S / β) (τ (j + 1)) - (S / β) (τ j))) Q) :
    ¬ IsArbitrage P (fun ω ↦ a 0 ω * S (τ 0) ω + b 0 ω * β (τ 0) ω)
      (fun ω ↦ a n ω * S (τ (n + 1)) ω + b n ω * β (τ (n + 1)) ω) := by
  intro harb
  have h₀ : τ 0 ∈ Set.Icc (τ 0) (τ (n + 1)) := ⟨le_rfl, hτ (by simp) (by simp) (Nat.zero_le _)⟩
  have hT : τ (n + 1) ∈ Set.Icc (τ 0) (τ (n + 1)) := ⟨h₀.2, le_rfl⟩
  -- Measured in bond shares, the trade is still an arbitrage, now under `Q`.
  have hdarb := (isArbitrage_mul_iff (c₀ := fun ω ↦ (β (τ 0) ω)⁻¹)
    (c := fun ω ↦ (β (τ (n + 1)) ω)⁻¹) (fun ω ↦ inv_ne_zero (hβ _ h₀ ω).ne')
    (fun ω ↦ inv_pos.2 (hβ _ hT ω))).2 ((isArbitrage_iff_of_absolutelyContinuous hPQ hQP).1 harb)
  -- Its discounted terminal wealth is the discounted initial cost, zero, plus the gains.
  have hwealth : ∀ ω, ((fun ω ↦ (β (τ (n + 1)) ω)⁻¹) *
      fun ω ↦ a n ω * S (τ (n + 1)) ω + b n ω * β (τ (n + 1)) ω) ω =
      ((fun ω ↦ (β (τ 0) ω)⁻¹) * fun ω ↦ a 0 ω * S (τ 0) ω + b 0 ω * β (τ 0) ω) ω +
        simpleGains τ (n + 1) a (S / β) (τ (n + 1)) ω := fun ω ↦ by
    simpa only [Pi.mul_apply, inv_mul_eq_div] using
      (isSelfFinancing_iff_discounted hτ fun t ht ω ↦ (hβ t ht ω).ne').1 h n (Nat.lt_succ_self n)
        ω _ ⟨hτ (by simp) (by simp) (Nat.le_succ n), le_rfl⟩
  have hgains : ((fun ω ↦ (β (τ (n + 1)) ω)⁻¹) *
      fun ω ↦ a n ω * S (τ (n + 1)) ω + b n ω * β (τ (n + 1)) ω) =ᵐ[Q]
      simpleGains τ (n + 1) a (S / β) (τ (n + 1)) := by
    filter_upwards [hdarb.1] with ω hω
    rw [hwealth ω, hω, Pi.zero_apply, zero_add]
  have hG := integrable_simpleGains hτ hint le_rfl
  have hpos := hdarb.integral_pos (hG.congr hgains.symm)
  rw [integral_congr_ae hgains, integral_simpleGains hτ hXm hXi hX ha hint le_rfl] at hpos
  exact lt_irrefl 0 hpos

end SelfFinancing

end TauCeti.Finance
