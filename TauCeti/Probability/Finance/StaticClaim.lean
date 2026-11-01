/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Finance.SimpleStrategy

/-!
# Trading a mispriced static claim against its replication

Suppose a self-financing simple stock/bond strategy costs `q` and replicates a terminal claim
`H`. If the same claim can be traded statically at price `p`, hold `c` claims, sell `c` copies
of the replicating strategy, and invest the initial surplus `c * (q - p)` in the bond.
The combined trade costs zero and pays `c * (q - p) * β_T / β_0` at maturity.

`IsSelfFinancing.exists_staticClaim_offset` constructs the stock and bond holdings, preserves
their measurability at each trading date, and proves both cash-flow identities. The claim is
held separately until maturity: self-financing refers to the stock/bond part after its initial
purchase, not to an assumed martingale property of the mispriced claim.

`IsSelfFinancing.exists_staticClaim_sure_profit` chooses the profitable sign when both `N` and
`-N` units of the claim are permitted. For a deterministic positive terminal bond price it
produces the strictly positive constant payoff `N * |q - p| * β_T / β_0`, almost surely.
One such trade has only that fixed surplus. Unbounded sure profit requires scaling:
`IsSelfFinancing.exists_staticClaim_profit_gt` assumes explicitly that every positive and
negative integer claim position is permitted. Stock and bond positions are unrestricted.

These are cash-flow constructions, not a completeness theorem or a stochastic-integral
admissibility criterion. No integrability of the claim is needed because its payoff cancels
against the replication almost surely. There is at least one holding interval; holdings at the
last date mean the portfolio from the preceding interval, as in `SimpleStrategy`.

## References

* H. Föllmer, A. Schied, *Stochastic Finance: An Introduction in Discrete Time*, 4th ed.,
  de Gruyter, 2016, §5.1.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti.Finance

variable {Ω ι : Type*} [Preorder ι] {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ι mΩ} {τ : ℕ → ι} {n : ℕ}
  {a b : ℕ → Ω → ℝ} {S β : ι → Ω → ℝ} {H : Ω → ℝ}
  {p q B₀ Bₜ : ℝ}

/-- Offset `c` statically traded claims at price `p` by selling `c` copies of a simple
replication costing `q`, and invest the surplus in the bond. The resulting stock/bond part is
self-financing, chosen at the trading dates, costs `-c * p`, and cancels the claim at maturity,
leaving only the financed surplus. The initial bond price is the nonzero constant `B₀`. -/
theorem IsSelfFinancing.exists_staticClaim_offset
    (hsf : IsSelfFinancing τ (n + 1) a b S β)
    (ha : ∀ j ≤ n, StronglyMeasurable[ℱ (τ j)] (a j))
    (hb : ∀ j ≤ n, StronglyMeasurable[ℱ (τ j)] (b j))
    (hB₀ : B₀ ≠ 0) (hβ₀ : ∀ ω, β (τ 0) ω = B₀)
    (hq : ∀ ω, a 0 ω * S (τ 0) ω + b 0 ω * β (τ 0) ω = q)
    (hH : ∀ᵐ ω ∂P, a n ω * S (τ (n + 1)) ω + b n ω * β (τ (n + 1)) ω = H ω)
    (c : ℝ) :
    ∃ a' b' : ℕ → Ω → ℝ,
      IsSelfFinancing τ (n + 1) a' b' S β ∧
      (∀ j ≤ n, StronglyMeasurable[ℱ (τ j)] (a' j) ∧
        StronglyMeasurable[ℱ (τ j)] (b' j)) ∧
      (∀ ω, a' 0 ω * S (τ 0) ω + b' 0 ω * β (τ 0) ω + c * p = 0) ∧
      ∀ᵐ ω ∂P, a' n ω * S (τ (n + 1)) ω + b' n ω * β (τ (n + 1)) ω + c * H ω =
        c * (q - p) * β (τ (n + 1)) ω / B₀ := by
  refine ⟨fun j ω => -c * a j ω, fun j ω => -c * b j ω + c * (q - p) / B₀,
    ?_, ?_, ?_, ?_⟩
  · rw [isSelfFinancing_iff] at hsf ⊢
    intro j hj ω
    linear_combination -c * hsf j hj ω
  · intro j hj
    exact ⟨(ha j hj).const_mul _, ((hb j hj).const_mul _).add stronglyMeasurable_const⟩
  · intro ω
    have hq' := hq ω
    rw [hβ₀ ω] at hq' ⊢
    field_simp
    linear_combination -c * hq'
  · filter_upwards [hH] with ω hω
    linear_combination -c * hω

/-- If both signs of an `N`-unit claim position are permitted and `p ≠ q`, a zero-cost trade
against a simple replication yields the strictly positive, constant terminal surplus
`N * |q - p| * Bₜ / B₀`. The set `A` specifies permitted static claim positions; no constraint
is imposed on stock or bond positions. The bond prices at the initial and terminal dates are
the positive deterministic constants `B₀` and, almost surely, `Bₜ`. -/
theorem IsSelfFinancing.exists_staticClaim_sure_profit
    (hsf : IsSelfFinancing τ (n + 1) a b S β)
    (ha : ∀ j ≤ n, StronglyMeasurable[ℱ (τ j)] (a j))
    (hb : ∀ j ≤ n, StronglyMeasurable[ℱ (τ j)] (b j))
    (hB₀ : 0 < B₀) (hβ₀ : ∀ ω, β (τ 0) ω = B₀)
    (hBₜ : 0 < Bₜ) (hβₜ : ∀ᵐ ω ∂P, β (τ (n + 1)) ω = Bₜ)
    (hq : ∀ ω, a 0 ω * S (τ 0) ω + b 0 ω * β (τ 0) ω = q)
    (hH : ∀ᵐ ω ∂P, a n ω * S (τ (n + 1)) ω + b n ω * β (τ (n + 1)) ω = H ω)
    (hpq : p ≠ q) {A : Set ℝ} {N : ℝ} (hN : 0 < N) (hA : N ∈ A) (hA' : -N ∈ A) :
    0 < N * |q - p| * Bₜ / B₀ ∧
    ∃ c ∈ A, ∃ a' b' : ℕ → Ω → ℝ,
      IsSelfFinancing τ (n + 1) a' b' S β ∧
      (∀ j ≤ n, StronglyMeasurable[ℱ (τ j)] (a' j) ∧
        StronglyMeasurable[ℱ (τ j)] (b' j)) ∧
      (∀ ω, a' 0 ω * S (τ 0) ω + b' 0 ω * β (τ 0) ω + c * p = 0) ∧
      ∀ᵐ ω ∂P, a' n ω * S (τ (n + 1)) ω + b' n ω * β (τ (n + 1)) ω + c * H ω =
        N * |q - p| * Bₜ / B₀ := by
  have habs : 0 < |q - p| := abs_pos.mpr (sub_ne_zero.mpr hpq.symm)
  refine ⟨by positivity, ?_⟩
  -- Select the cheaper side of the claim/replication pair; only the surplus remains exposed.
  obtain ⟨c, hc, hsign⟩ : ∃ c ∈ A, c * (q - p) = N * |q - p| := by
    rcases lt_or_gt_of_ne hpq with h | h
    · exact ⟨N, hA, by rw [abs_of_pos (sub_pos.mpr h)]⟩
    · refine ⟨-N, hA', ?_⟩
      rw [abs_of_neg (sub_neg.mpr h)]
      ring
  obtain ⟨a', b', hs, hm, hcost, hpay⟩ :=
    hsf.exists_staticClaim_offset ha hb hB₀.ne' hβ₀ hq hH c
  refine ⟨c, hc, a', b', hs, hm, hcost, ?_⟩
  filter_upwards [hpay, hβₜ] with ω hω hβω
  simpa only [hβω, hsign] using hω

/-- With unrestricted positive and negative integer scaling of static claim positions, a
mispricing relative to a simple replication gives zero-cost trades whose terminal wealth
exceeds any prescribed real bound almost surely. The scaling premise is `hscale`; the result
does not infer unbounded profit from permission to make just one trade. -/
theorem IsSelfFinancing.exists_staticClaim_profit_gt
    (hsf : IsSelfFinancing τ (n + 1) a b S β)
    (ha : ∀ j ≤ n, StronglyMeasurable[ℱ (τ j)] (a j))
    (hb : ∀ j ≤ n, StronglyMeasurable[ℱ (τ j)] (b j))
    (hB₀ : 0 < B₀) (hβ₀ : ∀ ω, β (τ 0) ω = B₀)
    (hBₜ : 0 < Bₜ) (hβₜ : ∀ᵐ ω ∂P, β (τ (n + 1)) ω = Bₜ)
    (hq : ∀ ω, a 0 ω * S (τ 0) ω + b 0 ω * β (τ 0) ω = q)
    (hH : ∀ᵐ ω ∂P, a n ω * S (τ (n + 1)) ω + b n ω * β (τ (n + 1)) ω = H ω)
    (hpq : p ≠ q) {A : Set ℝ}
    (hscale : ∀ N : ℕ, 0 < N → (N : ℝ) ∈ A ∧ -(N : ℝ) ∈ A)
    (R : ℝ) :
    ∃ c ∈ A, ∃ a' b' : ℕ → Ω → ℝ,
      IsSelfFinancing τ (n + 1) a' b' S β ∧
      (∀ j ≤ n, StronglyMeasurable[ℱ (τ j)] (a' j) ∧
        StronglyMeasurable[ℱ (τ j)] (b' j)) ∧
      (∀ ω, a' 0 ω * S (τ 0) ω + b' 0 ω * β (τ 0) ω + c * p = 0) ∧
      ∀ᵐ ω ∂P, max R 0 <
        a' n ω * S (τ (n + 1)) ω + b' n ω * β (τ (n + 1)) ω + c * H ω := by
  have habs : 0 < |q - p| := abs_pos.mpr (sub_ne_zero.mpr hpq.symm)
  have hg : 0 < |q - p| * Bₜ / B₀ := by positivity
  obtain ⟨N, hN⟩ := exists_nat_gt (max R 0 / (|q - p| * Bₜ / B₀))
  have hNpos : 0 < (N : ℝ) := (div_nonneg (le_max_right R 0) hg.le).trans_lt hN
  have hNnat : 0 < N := by exact_mod_cast hNpos
  have hbound : max R 0 < (N : ℝ) * |q - p| * Bₜ / B₀ := by
    simpa only [mul_div_assoc, mul_assoc] using (div_lt_iff₀ hg).mp hN
  obtain ⟨_, c, hc, a', b', hs, hm, hcost, hpay⟩ :=
    hsf.exists_staticClaim_sure_profit ha hb hB₀ hβ₀ hBₜ hβₜ hq hH hpq hNpos
      (hscale N hNnat).1 (hscale N hNnat).2
  refine ⟨c, hc, a', b', hs, hm, hcost, ?_⟩
  filter_upwards [hpay] with ω hω
  rw [hω]
  exact hbound

end TauCeti.Finance
