/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Finance.SimpleStrategy.Basic

/-!
# Trading a mispriced static claim against its replication

Suppose a self-financing simple stock/bond strategy costs `q` and replicates a terminal claim
`H`. If the same claim can be traded statically at price `p`, hold `c` claims, sell `c` copies
of the replicating strategy, and invest the initial surplus `c * (q - p)` in the bond.
The combined trade costs zero and pays `c * (q - p) * β_T / β_0` at maturity.

The stock and bond holdings are explicitly `(-c) • a` and
`(-c) • b + (fun _ _ => c * (q - p) / B₀)`. Their properties are exposed separately:
`IsSelfFinancing.staticClaim_offset` proves self-financing. Given bond measurability `hb`,
`(hb.const_mul (-c)).add stronglyMeasurable_const` proves measurability of the offset bond
holding; stock measurability follows from `StronglyMeasurable.const_mul`.
`staticClaim_offset_initial_cost` and `staticClaim_offset_terminal_payoff` give the cash-flow
identities. The claim is held separately
until maturity: self-financing refers to the stock/bond part after its initial purchase, not to
an assumed martingale property of the mispriced claim.

`exists_staticClaim_payoff` chooses the profitable sign when both `N` and `-N` units of the
claim are permitted. For positive `N`, distinct prices, and positive deterministic initial and
terminal bond prices, its constant payoff `N * |q - p| * β_T / β_0` is strictly positive.
One such trade has only that fixed surplus. Unbounded sure profit requires scaling:
`exists_staticClaim_profit_gt` assumes explicitly that every positive and negative integer
claim position is permitted. Stock and bond positions are unrestricted. These payoff lemmas
need only terminal replication; combine them with the separate initial-cost, self-financing,
and measurability lemmas to obtain the corresponding zero-cost simple trades.

These are cash-flow constructions, not a completeness theorem or a stochastic-integral
admissibility criterion. No integrability of the claim is needed because its payoff cancels
against the replication almost surely. There is at least one holding interval; holdings at the
last date mean the portfolio from the preceding interval, as in `SimpleStrategy`.

## References

* H. Föllmer, A. Schied, *Stochastic Finance: An Introduction in Discrete Time*, 4th ed.,
  de Gruyter, 2016, §5.3 (pricing attainable contingent claims); §5.1 for the strategy setup.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti.Finance

variable {Ω ι : Type*} {τ : ℕ → ι} {n : ℕ}
  {a b : ℕ → Ω → ℝ} {S β : ι → Ω → ℝ} {H : Ω → ℝ}
  {p q B₀ Bₜ : ℝ}

/-- Selling `c` copies of a self-financing strategy and adding a constant bond position
preserves self-financing. The added bond position invests the claim/replication price surplus. -/
theorem IsSelfFinancing.staticClaim_offset (hsf : IsSelfFinancing τ n a b S β) (c p q B₀ : ℝ) :
    IsSelfFinancing τ n ((-c) • a)
      ((-c) • b + (fun _ _ => c * (q - p) / B₀)) S β := by
  have hconst : IsSelfFinancing τ n 0 (fun _ _ => c * (q - p) / B₀) S β :=
    isSelfFinancing_const 0 _
  simpa only [add_zero] using (hsf.smul (-c)).add hconst

/-- The static claim and its offsetting stock/bond holdings have zero combined initial cost
when the replication costs `q` and the initial bond price is the nonzero constant `B₀`. -/
theorem staticClaim_offset_initial_cost
    (hB₀ : B₀ ≠ 0) (hβ₀ : ∀ ω, β (τ 0) ω = B₀)
    (hq : ∀ ω, a 0 ω * S (τ 0) ω + b 0 ω * β (τ 0) ω = q) (c p : ℝ) (ω : Ω) :
    (-c * a 0 ω) * S (τ 0) ω + (-c * b 0 ω + c * (q - p) / B₀) * β (τ 0) ω +
      c * p = 0 := by
  have hq' := hq ω
  rw [hβ₀ ω] at hq' ⊢
  field_simp
  linear_combination -c * hq'

/-- Against an almost-sure replication, the offsetting trade pays only the financed surplus.
No initial-cost or self-financing assumption is needed for this terminal identity. -/
theorem staticClaim_offset_terminal_payoff {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    (hH : ∀ᵐ ω ∂P, a n ω * S (τ (n + 1)) ω + b n ω * β (τ (n + 1)) ω = H ω)
    (c p q B₀ : ℝ) :
    ∀ᵐ ω ∂P, (-c * a n ω) * S (τ (n + 1)) ω +
      (-c * b n ω + c * (q - p) / B₀) * β (τ (n + 1)) ω + c * H ω =
        c * (q - p) * β (τ (n + 1)) ω / B₀ := by
  filter_upwards [hH] with ω hω
  linear_combination -c * hω

variable {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- If both signs of an `N`-unit claim position are permitted, choose the sign that yields
terminal surplus `N * |q - p| * Bₜ / B₀` almost surely. This is strictly positive when `N`,
`B₀`, and `Bₜ` are positive and `p ≠ q`. The set `A` constrains only static claim positions. -/
theorem exists_staticClaim_payoff
    (hβₜ : ∀ᵐ ω ∂P, β (τ (n + 1)) ω = Bₜ)
    (hH : ∀ᵐ ω ∂P, a n ω * S (τ (n + 1)) ω + b n ω * β (τ (n + 1)) ω = H ω)
    (p q B₀ : ℝ) {A : Set ℝ} {N : ℝ} (hA : N ∈ A) (hA' : -N ∈ A) :
    ∃ c ∈ A, ∀ᵐ ω ∂P, (-c * a n ω) * S (τ (n + 1)) ω +
      (-c * b n ω + c * (q - p) / B₀) * β (τ (n + 1)) ω + c * H ω =
        N * |q - p| * Bₜ / B₀ := by
  -- Select the cheaper side of the claim/replication pair; only the surplus remains exposed.
  obtain ⟨c, hc, hsign⟩ : ∃ c ∈ A, c * (q - p) = N * |q - p| := by
    rcases le_total p q with h | h
    · exact ⟨N, hA, by rw [abs_of_nonneg (sub_nonneg.mpr h)]⟩
    · refine ⟨-N, hA', ?_⟩
      rw [abs_of_nonpos (sub_nonpos.mpr h)]
      ring
  refine ⟨c, hc, ?_⟩
  filter_upwards [staticClaim_offset_terminal_payoff hH c p q B₀, hβₜ] with ω hω hβω
  simpa only [hβω, hsign] using hω

/-- With unrestricted positive and negative integer scaling of static claim positions, a
mispricing relative to a simple replication gives terminal wealth exceeding any prescribed
real bound almost surely. Combined with `staticClaim_offset_initial_cost` and
`IsSelfFinancing.staticClaim_offset`, these are zero-cost self-financing offsets. The scaling
premise is `hscale`; one fixed permitted trade does not imply unbounded profit. -/
theorem exists_staticClaim_profit_gt
    (hB₀ : 0 < B₀) (hBₜ : 0 < Bₜ) (hβₜ : ∀ᵐ ω ∂P, β (τ (n + 1)) ω = Bₜ)
    (hH : ∀ᵐ ω ∂P, a n ω * S (τ (n + 1)) ω + b n ω * β (τ (n + 1)) ω = H ω)
    (hpq : p ≠ q) {A : Set ℝ}
    (hscale : ∀ N : ℕ, 0 < N → (N : ℝ) ∈ A ∧ -(N : ℝ) ∈ A)
    (R : ℝ) :
    ∃ c ∈ A, ∀ᵐ ω ∂P, max R 0 < (-c * a n ω) * S (τ (n + 1)) ω +
      (-c * b n ω + c * (q - p) / B₀) * β (τ (n + 1)) ω + c * H ω := by
  have habs : 0 < |q - p| := abs_pos.mpr (sub_ne_zero.mpr hpq.symm)
  have hg : 0 < |q - p| * Bₜ / B₀ := by positivity
  obtain ⟨N, hN⟩ := exists_nat_gt (max R 0 / (|q - p| * Bₜ / B₀))
  have hNpos : 0 < (N : ℝ) := (div_nonneg (le_max_right R 0) hg.le).trans_lt hN
  have hNnat : 0 < N := by exact_mod_cast hNpos
  have hbound : max R 0 < (N : ℝ) * |q - p| * Bₜ / B₀ := by
    simpa only [mul_div_assoc, mul_assoc] using (div_lt_iff₀ hg).mp hN
  obtain ⟨c, hc, hpay⟩ := exists_staticClaim_payoff hβₜ hH p q B₀
    (hscale N hNnat).1 (hscale N hNnat).2
  refine ⟨c, hc, ?_⟩
  filter_upwards [hpay] with ω hω
  rw [hω]
  exact hbound

end TauCeti.Finance
