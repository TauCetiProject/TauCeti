/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.InteriorMorrey
public import TauCeti.Analysis.Sobolev.Wkp.LineDeriv
public import TauCeti.Analysis.Sobolev.Wkp.PreciseRepresentative
import TauCeti.Analysis.Sobolev.W1p.SobolevEmbedding
import TauCeti.Topology.Sets.Opens

/-!
# Continuity of `W^{2,p}` functions for `p` at least the dimension

Let `Ω` be an open subset of a finite-dimensional real inner product space of dimension `n`, with
an additive Haar measure, and let `n ≤ p ≤ ∞`. This file proves that every `u ∈ W^{2,p}(Ω)` is
continuous in `Ω`, and locally Hölder continuous with every exponent `1 - n / q`, `n < q < ∞`:
its precise representative `u*`, the limit of its averages over shrinking balls, which agrees with
`u` almost everywhere on `Ω` (`TauCeti.Wkp.ae_eq_preciseRepresentative`), is continuous on `Ω`
and `(1 - n / q)`-Hölder continuous on every compact subset of `Ω`. No regularity of `∂Ω` is
needed.

The case `p = n` is the borderline one: `W^{1,n}` functions need not be continuous or even locally
bounded once `n ≥ 2`, but one more derivative restores continuity. This is the continuity of
`W^{2,n}` strong solutions of non-divergence-form equations used in the Krylov–Safonov theory,
whose estimates are stated for a continuous representative.

## The argument

On an open set `V` with compact closure in `Ω`, every `W^{1,p}(Ω)` function lies in `L^q(V)` for
every finite `q` (`TauCeti.W1p.memLp_value_of_isCompact_closure_of_finrank_le`). When `n ≥ 1`
and `p ≤ q` are finite this is the borderline Sobolev inequality, since then
`1/p - 1/q < 1/n`; smaller `q` follow because `V` has finite measure, and `n = 0` is trivial.
The directional weak derivatives `∂ᵥu` of `u ∈ W^{2,p}(Ω)` lie in `W^{1,p}(Ω)`
(`TauCeti.Wkp.exists_hasWeakLineDerivOn_value`), so `u` and all its first weak derivatives lie in
`L^q(V)`, and `u` represents an element of `W^{1,q}(V)`
(`TauCeti.Wkp.exists_w1p_value_ae_eq_of_isCompact_closure`). For `q > n` the interior Morrey
embedding of `W^{1,q}(V)` (`TauCeti.W1p.continuousOn_preciseRepresentative`,
`TauCeti.W1p.exists_holderOnWith_preciseRepresentative_of_isCompact`) applies, and the precise
representative only depends on `u` near each point (`preciseRepresentative_congr_ae_nhds`).

## Main declarations

* `TauCeti.Wkp.exists_w1p_value_ae_eq_of_isCompact_closure`: `W^{2,p}(Ω) ⊆ W^{1,q}(V)` for every
  finite `q ≥ 1`, when `n ≤ p` and `V` is open with compact closure in `Ω`.
* `TauCeti.Wkp.continuousOn_preciseRepresentative`: the precise representative of
  `u ∈ W^{2,p}(Ω)`, `n ≤ p`, is continuous on `Ω`.
* `TauCeti.Wkp.exists_holderOnWith_preciseRepresentative_of_isCompact`: it is
  `(1 - n / q)`-Hölder continuous on every compact subset of `Ω`, for every finite `q > n`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorems 7.15 and 7.17 and Corollary 7.11.
* L. C. Evans, *Partial Differential Equations*, §5.6.3, Theorem 6.
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace Module TauCeti.MeasureTheory
open scoped ENNReal NNReal

namespace TauCeti

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **`W^{2,p}(Ω) ⊆ W^{1,q}(V)` for `n ≤ p`.** Let `n ≤ p ≤ ∞`, where `n` is the dimension, and let
`V` be an open set with compact closure in `Ω`. Every `u ∈ W^{2,p}(Ω)` agrees almost everywhere
on `V` with an element of `W^{1,q}(V)`, for every finite `q ≥ 1`. -/
theorem Wkp.exists_w1p_value_ae_eq_of_isCompact_closure (hp : (finrank ℝ E : ℝ≥0∞) ≤ p)
    (u : Wkp mu Omega p 2) {V : Opens E} (hVc : IsCompact (closure (V : Set E)))
    (hVΩ : closure (V : Set E) ⊆ Omega) (q : ℝ≥0) [Fact (1 ≤ (q : ℝ≥0∞))] :
    ∃ w : W1p mu V q, W1p.value w =ᵐ[mu.restrict V] Wkp.value 2 u := by
  have hV : V ≤ Omega := SetLike.coe_subset_coe.1 (subset_closure.trans hVΩ)
  -- The directional weak derivatives of `u` are `W^{1,p}(Ω)` functions.
  choose d hd using fun v : E => Wkp.exists_hasWeakLineDerivOn_value 1 u v
  obtain ⟨w, hw⟩ := Wkp.exists_value_one_ae_eq_of_forall_hasWeakLineDerivOn (Omega := V)
    (p := (q : ℝ≥0∞)) (w := Wkp.value 2 u)
    (by simpa only [Wkp.value_lowerOrder_one] using
      W1p.memLp_value_of_isCompact_closure_of_finrank_le hp hVc hVΩ q (Wkp.lowerOrder 1 u))
    (fun v => Wkp.value 1 (d v))
    (fun v => by
      simpa only [Wkp.value_one] using
        W1p.memLp_value_of_isCompact_closure_of_finrank_le hp hVc hVΩ q (d v))
    fun v => (hd v).mono hV
  exact ⟨w, by simpa only [Wkp.value_one] using hw⟩

/-- **Continuity of `W^{2,p}` functions for `p` at least the dimension.** If `n ≤ p ≤ ∞`, where `n`
is the dimension, the precise representative of any `u ∈ W^{2,p}(Ω)`, which agrees with `u` almost
everywhere on `Ω` (`TauCeti.Wkp.ae_eq_preciseRepresentative`), is continuous on `Ω`. -/
theorem Wkp.continuousOn_preciseRepresentative (hp : (finrank ℝ E : ℝ≥0∞) ≤ p)
    (u : Wkp mu Omega p 2) :
    ContinuousOn (preciseRepresentative mu (Wkp.value 2 u)) Omega := by
  intro x hx
  obtain ⟨V, hxV, hVΩ, hVc⟩ :=
    Opens.exists_between_and_isCompact_closure isCompact_singleton (singleton_subset_iff.2 hx)
  -- On `V`, `u` is a `W^{1,n+1}` function, to which Morrey's embedding applies.
  have : Fact (1 ≤ ((finrank ℝ E + 1 : ℝ≥0) : ℝ≥0∞)) := ⟨by simp⟩
  obtain ⟨w, hw⟩ := Wkp.exists_w1p_value_ae_eq_of_isCompact_closure hp u hVc hVΩ
    (finrank ℝ E + 1)
  have heq : EqOn (preciseRepresentative mu (W1p.value w))
      (preciseRepresentative mu (Wkp.value 2 u)) V :=
    fun z hz => preciseRepresentative_congr_ae_nhds (V.isOpen.mem_nhds hz) hw
  exact (((W1p.continuousOn_preciseRepresentative
    (by exact_mod_cast lt_add_one (finrank ℝ E)) w).congr heq.symm).continuousAt
    (V.isOpen.mem_nhds (hxV rfl))).continuousWithinAt

/-- **Hölder continuity of `W^{2,p}` functions for `p` at least the dimension.** If `n ≤ p ≤ ∞`,
where `n` is the dimension, then for every finite `q > n` the precise representative of any
`u ∈ W^{2,p}(Ω)` is Hölder continuous with exponent `1 - n / q` on every compact subset of `Ω`. -/
theorem Wkp.exists_holderOnWith_preciseRepresentative_of_isCompact
    (hp : (finrank ℝ E : ℝ≥0∞) ≤ p) (u : Wkp mu Omega p 2) {q : ℝ≥0}
    (hq : (finrank ℝ E : ℝ≥0∞) < q) {K : Set E} (hK : IsCompact K) (hKΩ : K ⊆ Omega) :
    ∃ C : ℝ≥0, HolderOnWith C ((1 : ℝ≥0∞) - finrank ℝ E / q).toNNReal
      (preciseRepresentative mu (Wkp.value 2 u)) K := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · exact ⟨0, Set.subsingleton_of_subsingleton.holderOnWith _ _ _⟩
  have : Fact (1 ≤ (q : ℝ≥0∞)) := ⟨(Nat.one_le_cast.2 finrank_pos).trans hq.le⟩
  obtain ⟨V, hKV, hVΩ, hVc⟩ := Opens.exists_between_and_isCompact_closure hK hKΩ
  obtain ⟨w, hw⟩ := Wkp.exists_w1p_value_ae_eq_of_isCompact_closure hp u hVc hVΩ q
  obtain ⟨C, hC⟩ := W1p.exists_holderOnWith_preciseRepresentative_of_isCompact hq w hK hKV
  have heq : EqOn (preciseRepresentative mu (W1p.value w))
      (preciseRepresentative mu (Wkp.value 2 u)) K :=
    fun z hz => preciseRepresentative_congr_ae_nhds (V.isOpen.mem_nhds (hKV hz)) hw
  refine ⟨C, fun x hx y hy => ?_⟩
  rw [← heq hx, ← heq hy]
  exact hC x hx y hy

end TauCeti
