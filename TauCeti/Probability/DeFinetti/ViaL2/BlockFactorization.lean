/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Exchangeability.CondExp
public import TauCeti.Probability.Process.Cylinder
public import TauCeti.Probability.Process.Tail.ConditionalLaw.Basic
import TauCeti.MeasureTheory.Function.ConditionalExpectation
import TauCeti.MeasureTheory.Integral.Bochner.Basic
import TauCeti.Probability.DeFinetti.ViaL2.WindowProduct
import TauCeti.Probability.Process.Tail.ConditionalLaw.Integral

/-!
# The finite-block factorization, via `L²`

For a contractable process on a standard Borel state space, the conditional law of any finite
strictly monotone block, given the process tail, factorizes into the directing measure's marginals:

```text
μ[blockIndicatorProd X k B | tailProcess X] =ᵐ[μ] ∏ i, (tailConditionalMeasure μ X ·).real (B i).
```

This is the single theorem the file provides. Integrating it over a tail event is what supplies
`hcore`, the hypothesis of `conditionallyIIDWith_of_measure_inter_blockCylinder_eq_setLIntegral`,
and hence `ConditionallyIIDWith μ X (tailConditionalProbabilityMeasure μ X)`; that integration step
is separate and does not live here.

## Why this route exists

`DeFinetti/BlockFactorization.lean` proves the same factorization through the reverse martingale
convergence theorem. This file reaches it from the `L²` averaging library instead, and imports
neither that module nor `TailFactorization`, `JointRectangle` or `Martingale.Convergence` — the
point of the `viaL2` route is that the factorization does not need a martingale.

Two inputs meet, and neither knows about the other:

*Selection invariance.* `Contractable.condExp_block_comp_tailProcess_ae_eq` says the conditional
law of a block given the tail is the same for every strictly monotone selection of that length.
The tuples appearing in a product of disjoint-window block averages are exactly such selections —
factor `i` reads its own window, and the windows are ordered, so `window_lt_window` makes each
tuple strictly monotone.

*Averaging.* `prod_blockAverage_window_eq_expect` writes a product of disjoint-window block
averages as a plain average over those tuples, so conditioning it on the tail returns the single
common value. Meanwhile the same product converges in `L¹` to `∏ i, (tailConditionalMeasure ω).real
(B i)` by the disjoint-window convergence theorem in `ViaL2/WindowProduct.lean`.
A constant sequence that converges must equal its limit, which is the factorization.

## Relation to the martingale route

`DeFinetti/BlockFactorization.lean` proves
`condExp_blockIndicatorProd_prefix_ae_eq_prod_directingMeasure`, the same factorization for the
*prefix* selection, through `TailFactorization` and reverse-martingale convergence. The overlap is
intentional: the two are the corresponding steps of the two proof routes. Their names record the
difference in what they *say* — `_prefix_` against `_strictMono_` — rather than how they are proved;
the `_viaL2` suffix is reserved for the public route endpoints.

This statement is strictly stronger than the prefix form: it holds for every strictly monotone
selection, not only `i ↦ i`, and does not assume `StandardBorelSpace Ω`. So the implication does
run one way — specializing `k` to `fun i : Fin r => (i : ℕ)` turns this into the prefix statement,
and any module importing this one can derive it (its `StandardBorelSpace Ω` hypothesis then being
unused). The converse is unavailable, the prefix form being weaker.

What separate proofs buy is therefore not logical independence but independent **import closures**.
A single Lean declaration carries a single proof and a single import closure, so making this
theorem the canonical source of the prefix statement would put the `L²` averaging library beneath
the martingale route. The genuinely shared ingredients — tail-conditioned selection invariance,
directing-measure integrability, the `ℝ≥0∞` conversion — are already factored into neutral modules
that both routes import.

## References

* Not adapted from the pinned `cameronfreer/exchangeability` sources: the argument here is built
  from this repository's `L²` averaging library and its tail-conditioned selection invariance,
  and deliberately diverges from that development's `ViaL2` material.
-/

public section

noncomputable section

open Filter MeasureTheory

open scoped Topology

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- The product-of-indicators observable on a block is measurable. -/
private theorem measurable_prod_indicator {r : ℕ} {B : Fin r → Set α}
    (hB : ∀ i, MeasurableSet (B i)) :
    Measurable fun x : Fin r → α => ∏ i, (B i).indicator (fun _ => (1 : ℝ)) (x i) :=
  Finset.measurable_prod _ fun i _ =>
    (measurable_const.indicator (hB i)).comp (measurable_pi_apply i)

namespace Contractable

/-- **Selection invariance for indicator blocks.** The `Fin r`-indexed indicator observable is a
measurable function of the block, so `condExp_block_comp_tailProcess_ae_eq` applies to it. -/
private theorem condExp_prod_indicator_ae_eq {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ → Ω → α}
    (hX : Contractable μ X) (hX_meas : ∀ n, Measurable (X n)) {r : ℕ} {k l : Fin r → ℕ}
    (hk : StrictMono k) (hl : StrictMono l) {B : Fin r → Set α}
    (hB : ∀ i, MeasurableSet (B i)) :
    μ[fun ω => ∏ i, (B i).indicator (fun _ => (1 : ℝ)) (X (k i) ω) | tailProcess X]
      =ᵐ[μ] μ[fun ω => ∏ i, (B i).indicator (fun _ => (1 : ℝ)) (X (l i) ω) | tailProcess X] :=
  hX.condExp_block_comp_tailProcess_ae_eq hX_meas hk hl (measurable_prod_indicator hB)

/-- A product of indicators along any selection `s` of the process is integrable. -/
private theorem integrable_prod_indicator_comp {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ → Ω → α}
    (hX_meas : ∀ n, Measurable (X n)) {r : ℕ} (s : Fin r → ℕ) {B : Fin r → Set α}
    (hB : ∀ i, MeasurableSet (B i)) :
    Integrable (fun ω => ∏ i, (B i).indicator (fun _ => (1 : ℝ)) (X (s i) ω)) μ :=
  (integrable_blockIndicatorProd (fun i => (hX_meas (s i)).aemeasurable) hB).congr
    (ae_of_all _ fun ω => blockIndicatorProd_apply X s B ω)

omit [MeasurableSpace Ω] in
/-- The product of block averages over the disjoint windows is a plain average over tuples. -/
private theorem prod_blockAverage_disjointWindow_eq_smul_sum {r : ℕ} (Y : Fin r → ℕ → Ω → ℝ)
    (n : ℕ) :
    (fun ω => ∏ i : Fin r, blockAverage (Y i) (disjointWindow (i : ℕ) n) ω) =
      ((Fintype.card (Fin r → Fin (n + 1)) : ℝ))⁻¹ •
        ∑ js : Fin r → Fin (n + 1), fun ω => ∏ i, Y i (window (n + 1) (i : ℕ) (js i : ℕ)) ω := by
  funext ω
  have hexp := prod_blockAverage_window_eq_expect (N := n + 1) Y ω
  rw [Fintype.expect_eq_sum_div_card, div_eq_inv_mul] at hexp
  simpa using hexp

/-- **Constancy of the averaged product.** Every product of disjoint-window block averages of
indicators has the same conditional expectation given the tail, namely that of the block product
along `k`, since each tuple it averages over is a strictly monotone selection. -/
private theorem condExp_prod_blockAverage_disjointWindow_ae_eq {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} (hX : Contractable μ X) (hX_meas : ∀ n, Measurable (X n)) {r : ℕ}
    {k : Fin r → ℕ} (hk : StrictMono k) {B : Fin r → Set α} (hB : ∀ i, MeasurableSet (B i))
    (n : ℕ) :
    μ[fun ω => ∏ i : Fin r, blockAverage (fun c ω => (B i).indicator (fun _ => (1 : ℝ)) (X c ω))
        (disjointWindow (i : ℕ) n) ω | tailProcess X]
      =ᵐ[μ] μ[fun ω => ∏ i, (B i).indicator (fun _ => (1 : ℝ)) (X (k i) ω) | tailProcess X] := by
  set c : ℝ := (Fintype.card (Fin r → Fin (n + 1)) : ℝ) with hc
  have hcard : c ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  set G : (Fin r → Fin (n + 1)) → Ω → ℝ :=
    fun js ω => ∏ i, (B i).indicator (fun _ => (1 : ℝ)) (X (window (n + 1) (i : ℕ) (js i : ℕ)) ω)
  -- Every tuple is a strictly monotone selection, so all the terms share one conditional law.
  have hterm : ∀ js, μ[G js | tailProcess X]
      =ᵐ[μ] μ[fun ω => ∏ i, (B i).indicator (fun _ => (1 : ℝ)) (X (k i) ω) | tailProcess X] :=
    fun js => hX.condExp_prod_indicator_ae_eq hX_meas (window_selection_strictMono js) hk hB
  have hsum : μ[∑ js, G js | tailProcess X] =ᵐ[μ] fun ω =>
      c * μ[fun ω => ∏ i, (B i).indicator (fun _ => (1 : ℝ)) (X (k i) ω) | tailProcess X] ω := by
    refine (condExp_finsetSum (fun js _ => integrable_prod_indicator_comp hX_meas _ hB)
      (tailProcess X)).trans ?_
    filter_upwards [(eventually_all_finset (Finset.univ : Finset (Fin r → Fin (n + 1)))).2
      fun js _ => hterm js] with ω hω
    rw [Finset.sum_apply, Finset.sum_congr rfl fun js hjs => hω js hjs]
    simp [hc, Finset.card_univ]
  calc _ =ᵐ[μ] μ[c⁻¹ • ∑ js, G js | tailProcess X] := by
        rw [prod_blockAverage_disjointWindow_eq_smul_sum _ n]
    _ =ᵐ[μ] c⁻¹ • μ[∑ js, G js | tailProcess X] := condExp_smul _ _ _
    _ =ᵐ[μ] _ := by
        filter_upwards [hsum] with ω hω
        simp only [Pi.smul_apply, hω, smul_eq_mul, inv_mul_cancel_left₀ hcard]

/-- **The finite-block factorization, conditionally on the tail.** For a contractable process on a
standard Borel state space and any strictly monotone block `k`, the conditional expectation of
`∏ i, 𝟙_{B i} ∘ X (k i)` given `tailProcess X` is the product of the directing measure's
marginals. -/
theorem condExp_blockIndicatorProd_strictMono_tailProcess_ae_eq_prod_directingMeasure
    [StandardBorelSpace α] [Nonempty α]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ → Ω → α} (hX : Contractable μ X)
    (hX_meas : ∀ n, Measurable (X n)) {r : ℕ} {k : Fin r → ℕ} (hk : StrictMono k)
    {B : Fin r → Set α} (hB : ∀ i, MeasurableSet (B i)) :
    μ[blockIndicatorProd X k B | tailProcess X]
      =ᵐ[μ] fun ω => ∏ i, (tailConditionalMeasure μ X ω).real (B i) := by
  classical
  rw [funext fun ω => blockIndicatorProd_apply X k B ω]
  have hTail : tailProcess X ≤ (inferInstance : MeasurableSpace Ω) :=
    tailProcess_le_ambient 0 fun c _ => hX_meas c
  set Y : Fin r → ℕ → Ω → ℝ := fun i c ω => (B i).indicator (fun _ => (1 : ℝ)) (X c ω)
  set Z : Ω → ℝ := fun ω => ∏ i, Y i (k i) ω
  set W : Ω → ℝ := fun ω => ∏ i, (tailConditionalMeasure μ X ω).real (B i)
  -- `W` is tail-measurable, so it is its own conditional expectation.
  have hW_tail : Measurable[tailProcess X] W :=
    Finset.measurable_prod _ fun i _ =>
      (measurable_tailProcess_tailConditionalMeasure_coe (hB i)).ennreal_toReal
  have hW_int : Integrable W μ := integrable_prod_tailConditionalMeasure_real hTail hB
  have hcondW : μ[W | tailProcess X] =ᵐ[μ] W := by
    rw [condExp_of_stronglyMeasurable hTail hW_tail.stronglyMeasurable hW_int]
  -- The product of disjoint-window block averages, whose conditional expectation is `μ[Z | tail]`
  -- at every length and which converges in `L¹` to `W`.
  set P : ℕ → Ω → ℝ :=
    fun n ω => ∏ i : Fin r, blockAverage (Y i) (disjointWindow (i : ℕ) n) ω with hP
  have hP_int : ∀ n, Integrable (P n) μ := by
    intro n
    rw [show P n = _ from prod_blockAverage_disjointWindow_eq_smul_sum Y n]
    exact (integrable_finsetSum' _ fun js _ =>
      integrable_prod_indicator_comp hX_meas _ hB).smul
      (((Fintype.card (Fin r → Fin (n + 1)) : ℝ))⁻¹)
  have hconst : ∀ n, μ[P n | tailProcess X] =ᵐ[μ] μ[Z | tailProcess X] :=
    condExp_prod_blockAverage_disjointWindow_ae_eq hX hX_meas hk hB
  -- `L¹` convergence of the same product to `W`.
  have hlim : Tendsto (fun n => ∫ ω, |P n ω - W ω| ∂μ) atTop (𝓝 0) :=
    hX.tendsto_integral_abs_prod_blockAverage_indicator_disjointWindow_sub_prod_directingMeasure
      hX_meas B hB
  -- `L¹` convergence of the constant conditional expectations identifies `μ[Z | tail]` with `W`.
  have hL1 : Tendsto (fun n => eLpNorm (W - P n) 1 μ) atTop (𝓝 0) := by
    simpa only [eLpNorm_sub_comm W] using
      TauCeti.MeasureTheory.tendsto_eLpNorm_one_of_tendsto_integral_norm_sub
        (Eventually.of_forall fun n => (hP_int n).sub hW_int)
        (by simpa [Real.norm_eq_abs] using hlim)
  exact (hcondW.symm.trans
    (TauCeti.MeasureTheory.condExp_ae_eq_of_forall_condExp_ae_eq_of_tendsto_eLpNorm
      hW_int hP_int hconst hL1)).symm

end Contractable

end Probability

end TauCeti

end
