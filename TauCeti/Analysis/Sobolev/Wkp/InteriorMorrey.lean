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
import TauCeti.Analysis.Sobolev.WeakDeriv.Classical
import TauCeti.Analysis.Sobolev.Wkp.Embedding
import TauCeti.MeasureTheory.Measure.OpenPos
import TauCeti.Topology.Sets.Opens

/-!
# Continuity and differentiability of `W^{2,p}` functions in the interior

Let `Ω` be an open subset of a finite-dimensional real inner product space of dimension `n`, with
an additive Haar measure, and let `u ∈ W^{2,p}(Ω)`, `1 ≤ p ≤ ∞`. Its precise representative `u*`,
the limit of its averages over shrinking balls, agrees with `u` almost everywhere on `Ω`
(`TauCeti.Wkp.ae_eq_preciseRepresentative`). This file proves the interior embeddings of
`W^{2,p}(Ω)` into spaces of continuous and of continuously differentiable functions:

* for `p > n / 2`, `u*` is continuous on `Ω`; it is `(2 - n / p)`-Hölder continuous on every
  compact subset of `Ω` when `n / 2 < p < n`, and `(1 - n / q)`-Hölder continuous there for every
  finite `q > n` when `p ≥ n`;
* for `p > n`, `u*` is `C¹` on `Ω`, its derivative in a direction `v` is the precise representative
  of the weak derivative `∂ᵥu`, and its derivative is `(1 - n / p)`-Hölder continuous on every
  compact subset of `Ω`.

No regularity of `∂Ω` is needed. The bound `p > n / 2` cannot be lowered to `p = n / 2` once
`n ≥ 3`: `log log (1 + 1 / |x|)` lies in `W^{2,n/2}` of the unit ball and is unbounded. (For
`n = 2` and Lebesgue measure, `W^{2,1}(Ω)` is still continuous, by the critical embedding
`TauCeti.Wkp.exists_continuousOn_ae_eq_of_finrank_le`.) For a `W^{2,p}` strong solution of a
non-divergence-form equation, this is the sense in which it is a continuous, respectively `C¹`,
function. The case `p = n` is the borderline one: `W^{1,n}` functions need not be continuous or
even locally bounded once `n ≥ 2`, but one more derivative restores continuity, as used in the
Krylov–Safonov theory.

## The argument

Let `V` be open with compact closure in `Ω`.

* If `n / 2 < p < n`, the interior Sobolev embedding of order two
  (`TauCeti.Wkp.exists_sobolevEmbeddingL_of_isCompact_closure`) puts `u` in `W^{1,p⋆}(V)`, where
  `1 / p⋆ = 1 / p - 1 / n`
  (`TauCeti.Wkp.exists_w1p_value_ae_eq_of_isCompact_closure_of_lt_finrank`). Then `p⋆ > n`
  exactly because `p > n / 2`, and Morrey's exponent is `1 - n / p⋆ = 2 - n / p`.
* If `n ≤ p`, every `W^{1,p}(Ω)` function lies in `L^q(V)` for every finite `q`
  (`TauCeti.W1p.memLp_value_of_isCompact_closure_of_finrank_le`), and the first weak derivatives
  `∂ᵥu` of `u` lie in `W^{1,p}(Ω)` (`TauCeti.Wkp.exists_hasWeakLineDerivOn_value`), so `u`
  represents an element of `W^{1,q}(V)` (`TauCeti.Wkp.exists_w1p_value_ae_eq_of_isCompact_closure`).

In both cases the interior Morrey embedding of `W^{1,q}(V)` for some `q > n`
(`TauCeti.W1p.continuousOn_preciseRepresentative`,
`TauCeti.W1p.exists_holderOnWith_preciseRepresentative_of_isCompact`) applies, and the precise
representative only depends on `u` near each point (`preciseRepresentative_congr_ae_nhds`).

If `p > n`, Morrey's embedding applies to the derivatives `∂ᵢu ∈ W^{1,p}(Ω)` along an orthonormal
basis themselves: their precise representatives are continuous weak derivatives of the continuous
function `u*`, so `u*` is `C¹` (`TauCeti.contDiffOn_succ_of_forall_hasWeakLineDerivOn`), and its
derivative is the sum of their `(1 - n / p)`-Hölder continuous coordinates.

## Main declarations

* `TauCeti.Wkp.exists_w1p_value_ae_eq_of_isCompact_closure`: `W^{2,p}(Ω) ⊆ W^{1,q}(V)` for every
  finite `q ≥ 1`, when `n ≤ p` and `V` is open with compact closure in `Ω`.
* `TauCeti.Wkp.exists_w1p_value_ae_eq_of_isCompact_closure_of_lt_finrank`:
  `W^{2,p}(Ω) ⊆ W^{1,p⋆}(V)`, `1 / p⋆ = 1 / p - 1 / n`, when `p < n` and `V` is open with compact
  closure in `Ω`.
* `TauCeti.Wkp.continuousOn_preciseRepresentative`: the precise representative of
  `u ∈ W^{2,p}(Ω)`, `n < 2 p`, is continuous on `Ω`.
* `TauCeti.Wkp.preciseRepresentative_le_of_ae_le`, `TauCeti.Wkp.le_preciseRepresentative_of_ae_le`:
  almost everywhere comparison against a continuous function on an open subset of `Ω` transfers
  pointwise to the precise representative.
* `TauCeti.Wkp.abs_preciseRepresentative_le`: an almost-everywhere bound `|u| ≤ M` on an open
  subset of `Ω` holds at every point for the precise representative.
* `TauCeti.Wkp.exists_holderOnWith_preciseRepresentative_of_isCompact_of_lt_finrank`: it is
  `(2 - n / p)`-Hölder continuous on every compact subset of `Ω`, when `n < 2 p` and `p < n`.
* `TauCeti.Wkp.exists_holderOnWith_preciseRepresentative_of_isCompact`: it is
  `(1 - n / q)`-Hölder continuous on every compact subset of `Ω`, for every finite `q > n`, when
  `n ≤ p`.
* `TauCeti.Wkp.contDiffOn_preciseRepresentative`: for `p > n`, it is `C¹` on `Ω`.
* `TauCeti.Wkp.fderiv_preciseRepresentative_apply`: for `p > n`, its derivative in the direction
  `v` is the precise representative of the weak derivative `∂ᵥu = TauCeti.Wkp.lineDerivL v 1 u`.
* `TauCeti.Wkp.exists_holderOnWith_fderiv_preciseRepresentative_of_isCompact`: for `p > n`, its
  derivative is `(1 - n / p)`-Hölder continuous on every compact subset of `Ω`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorems 7.10, 7.15, 7.17 and 7.26 and Corollary 7.11.
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

/-- **`W^{2,p}(Ω) ⊆ W^{1,p⋆}(V)` for `p < n`.** Let `p < n`, where `n` is the dimension, let
`1 / p⋆ = 1 / p - 1 / n`, and let `V` be an open set with compact closure in `Ω`. Then `1 ≤ p⋆`, and
every `u ∈ W^{2,p}(Ω)` agrees almost everywhere on `V` with an element of `W^{1,p⋆}(V)`. -/
theorem Wkp.exists_w1p_value_ae_eq_of_isCompact_closure_of_lt_finrank
    (hpn : p < finrank ℝ E) (u : Wkp mu Omega p 2) {V : Opens E}
    (hVc : IsCompact (closure (V : Set E))) (hVΩ : closure (V : Set E) ⊆ Omega) :
    ∃ (_ : Fact (1 ≤ (p⁻¹ - (finrank ℝ E : ℝ≥0∞)⁻¹)⁻¹)),
      ∃ w : W1p mu V (p⁻¹ - (finrank ℝ E : ℝ≥0∞)⁻¹)⁻¹,
        W1p.value w =ᵐ[mu.restrict V] Wkp.value 2 u := by
  have hinv : (finrank ℝ E : ℝ≥0∞)⁻¹ < p⁻¹ := ENNReal.inv_lt_inv.2 hpn
  have hexp : (p⁻¹ - (finrank ℝ E : ℝ≥0∞)⁻¹)⁻¹⁻¹ + (finrank ℝ E : ℝ≥0∞)⁻¹ = p⁻¹ := by
    rw [inv_inv, tsub_add_cancel_of_le hinv.le]
  let _ := Fact.mk (one_le_of_inv_add_eq_inv hexp)
  obtain ⟨T, hT⟩ := Wkp.exists_sobolevEmbeddingL_of_isCompact_closure (mu := mu)
    (ENNReal.inv_ne_top.2 (tsub_pos_of_lt hinv).ne') hexp hVc hVΩ 1
  exact ⟨inferInstance, T u, by simpa only [Wkp.value_one] using hT u⟩

/-- The exponent bookkeeping below the dimension: if `n / 2 < p < n` and `1 / p⋆ = 1 / p - 1 / n`,
then `p⋆` exceeds `n` and has Morrey exponent `1 - n / p⋆ = 2 - n / p`. -/
private theorem exponent_facts_of_lt {n : ℝ≥0∞} (hn : n ≠ ⊤) (hp2 : n < 2 * p) (hpn : p < n) :
    n < (p⁻¹ - n⁻¹)⁻¹ ∧
      ((1 : ℝ≥0∞) - n / (p⁻¹ - n⁻¹)⁻¹).toNNReal = ((2 : ℝ≥0∞) - n / p).toNNReal := by
  have hp1 : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp1).ne'
  have hptop : p ≠ ⊤ := (hpn.trans_le le_top).ne
  have hn0 : n ≠ 0 := (zero_lt_one.trans_le (hp1.trans hpn.le)).ne'
  have hinv : n⁻¹ < p⁻¹ := ENNReal.inv_lt_inv.2 hpn
  -- `1 / p < 2 / n`, i.e. `1 / p - 1 / n < 1 / n`.
  have hinv2 : p⁻¹ < n⁻¹ + n⁻¹ := by
    rw [← two_mul, ← div_eq_mul_inv, ENNReal.lt_div_iff_mul_lt (Or.inl hn0) (Or.inl hn),
      mul_comm, ← div_eq_mul_inv, ENNReal.div_lt_iff (Or.inl hp0) (Or.inl hptop)]
    exact hp2
  refine ⟨?_, ?_⟩
  · rw [← ENNReal.inv_lt_inv, inv_inv]
    exact ENNReal.sub_lt_of_lt_add hinv.le hinv2
  · -- Both exponents are `2 - n / p`: `n / p⋆ = n (1 / p - 1 / n) = n / p - 1`.
    have hnp : n / (p⁻¹ - n⁻¹)⁻¹ = n / p - 1 := by
      rw [div_eq_mul_inv, inv_inv, ENNReal.mul_sub fun _ _ => hn, ENNReal.mul_inv_cancel hn0 hn,
        ← div_eq_mul_inv]
    have h1 : (1 : ℝ≥0∞) ≤ n / p := by
      rw [ENNReal.le_div_iff_mul_le (Or.inl hp0) (Or.inl hptop), one_mul]
      exact hpn.le
    rw [hnp, ← tsub_tsub_tsub_cancel_right h1 (a := 2), ← one_add_one_eq_two,
      ENNReal.add_sub_cancel_right ENNReal.one_ne_top]

/-- For `n < 2 p`, on every open `V` with compact closure in `Ω`, an element of `W^{2,p}(Ω)` agrees
almost everywhere with an element of `W^{1,q}(V)` for some `q > n`. -/
private theorem Wkp.exists_w1p_value_ae_eq_of_lt_two_mul (hp : (finrank ℝ E : ℝ≥0∞) < 2 * p)
    (u : Wkp mu Omega p 2) {V : Opens E} (hVc : IsCompact (closure (V : Set E)))
    (hVΩ : closure (V : Set E) ⊆ Omega) :
    ∃ (q : ℝ≥0∞) (_ : Fact (1 ≤ q)), (finrank ℝ E : ℝ≥0∞) < q ∧
      ∃ w : W1p mu V q, W1p.value w =ᵐ[mu.restrict V] Wkp.value 2 u := by
  rcases le_or_gt (finrank ℝ E : ℝ≥0∞) p with hnp | hpn
  · have : Fact (1 ≤ ((finrank ℝ E + 1 : ℝ≥0) : ℝ≥0∞)) := ⟨by simp⟩
    exact ⟨_, this, by exact_mod_cast lt_add_one (finrank ℝ E),
      Wkp.exists_w1p_value_ae_eq_of_isCompact_closure hnp u hVc hVΩ _⟩
  · obtain ⟨_, w, hw⟩ :=
      Wkp.exists_w1p_value_ae_eq_of_isCompact_closure_of_lt_finrank hpn u hVc hVΩ
    exact ⟨_, inferInstance, (exponent_facts_of_lt (ENNReal.natCast_ne_top _) hp hpn).1, w, hw⟩

/-- **Continuity of `W^{2,p}` functions for `p` above half the dimension.** If `n < 2 p`, where `n`
is the dimension, the precise representative of any `u ∈ W^{2,p}(Ω)`, which agrees with `u` almost
everywhere on `Ω` (`TauCeti.Wkp.ae_eq_preciseRepresentative`), is continuous on `Ω`. -/
theorem Wkp.continuousOn_preciseRepresentative (hp : (finrank ℝ E : ℝ≥0∞) < 2 * p)
    (u : Wkp mu Omega p 2) :
    ContinuousOn (preciseRepresentative mu (Wkp.value 2 u)) Omega := by
  intro x hx
  obtain ⟨V, hxV, hVΩ, hVc⟩ := Opens.exists_mem_and_isCompact_closure hx
  -- On `V`, `u` is a `W^{1,q}` function with `q > n`, to which Morrey's embedding applies.
  obtain ⟨q, _, hq, w, hw⟩ := Wkp.exists_w1p_value_ae_eq_of_lt_two_mul hp u hVc hVΩ
  have heq : EqOn (preciseRepresentative mu (W1p.value w))
      (preciseRepresentative mu (Wkp.value 2 u)) V :=
    fun z hz => preciseRepresentative_congr_ae_nhds (V.isOpen.mem_nhds hz) hw
  exact (((W1p.continuousOn_preciseRepresentative hq w).congr heq.symm).continuousAt
    (V.isOpen.mem_nhds hxV)).continuousWithinAt

/-- If `u ∈ W^{2,p}(Ω)` with `n < 2 p` satisfies `u ≤ g` almost everywhere on an open subset `U ⊆ Ω`
and `g` is continuous on `U`, then its precise representative satisfies `u* ≤ g` everywhere on
`U`. -/
theorem Wkp.preciseRepresentative_le_of_ae_le (hp : (finrank ℝ E : ℝ≥0∞) < 2 * p)
    (u : Wkp mu Omega p 2) {U : Set E} (hU : IsOpen U) (hUΩ : U ⊆ Omega) {g : E → ℝ}
    (hg : ContinuousOn g U) (hle : ∀ᵐ x ∂mu.restrict U, Wkp.value 2 u x ≤ g x) :
    ∀ x ∈ U, preciseRepresentative mu (Wkp.value 2 u) x ≤ g x := by
  have hae := (Wkp.ae_eq_preciseRepresentative 2 u).filter_mono
    (ae_mono (Measure.restrict_mono hUΩ le_rfl))
  refine ((Wkp.continuousOn_preciseRepresentative hp u).mono hUΩ).le_of_ae_le
    (μ := mu) hU hg ?_
  filter_upwards [hae, hle] with x hx h
  exact hx ▸ h

/-- If `u ∈ W^{2,p}(Ω)` with `n < 2 p` satisfies `g ≤ u` almost everywhere on an open subset `U ⊆ Ω`
and `g` is continuous on `U`, then its precise representative satisfies `g ≤ u*` everywhere on
`U`. -/
theorem Wkp.le_preciseRepresentative_of_ae_le (hp : (finrank ℝ E : ℝ≥0∞) < 2 * p)
    (u : Wkp mu Omega p 2) {U : Set E} (hU : IsOpen U) (hUΩ : U ⊆ Omega) {g : E → ℝ}
    (hg : ContinuousOn g U) (hle : ∀ᵐ x ∂mu.restrict U, g x ≤ Wkp.value 2 u x) :
    ∀ x ∈ U, g x ≤ preciseRepresentative mu (Wkp.value 2 u) x := by
  have hae := (Wkp.ae_eq_preciseRepresentative 2 u).filter_mono
    (ae_mono (Measure.restrict_mono hUΩ le_rfl))
  refine hg.le_of_ae_le (μ := mu) hU ((Wkp.continuousOn_preciseRepresentative hp u).mono hUΩ) ?_
  filter_upwards [hae, hle] with x hx h
  exact hx ▸ h

/-- **Pointwise bounds on the continuous representative.** If `n < 2 p`, where `n` is the
dimension, and `u ∈ W^{2,p}(Ω)` satisfies `|u| ≤ M` almost everywhere on an open set `U ⊆ Ω`, then
its precise representative is bounded by `M` in absolute value at every point of `U`. -/
theorem Wkp.abs_preciseRepresentative_le (hp : (finrank ℝ E : ℝ≥0∞) < 2 * p)
    (u : Wkp mu Omega p 2) {U : Set E} (hU : IsOpen U) (hUΩ : U ⊆ Omega) {M : ℝ}
    (hM : ∀ᵐ x ∂mu.restrict U, |Wkp.value 2 u x| ≤ M) {x : E} (hx : x ∈ U) :
    |preciseRepresentative mu (Wkp.value 2 u) x| ≤ M := by
  have hcU : ContinuousOn (preciseRepresentative mu (Wkp.value 2 u)) U :=
    (Wkp.continuousOn_preciseRepresentative hp u).mono hUΩ
  refine hcU.abs.le_of_ae_le (μ := mu) hU continuousOn_const ?_ x hx
  filter_upwards [hM, ae_restrict_of_ae_restrict_of_subset hUΩ
    (Wkp.ae_eq_preciseRepresentative 2 u)] with y hy hyū
  rwa [← hyū]

/-- Hölder continuity on a compact set transfers from a `W^{1,q}(V)` function to an element of
`W^{2,p}(Ω)` agreeing with it almost everywhere on an open `V ⊇ K`. -/
private theorem holderOnWith_preciseRepresentative_of_ae_eq {q : ℝ≥0∞} [Fact (1 ≤ q)]
    {u : Wkp mu Omega p 2} {V : Opens E} {w : W1p mu V q}
    (hw : W1p.value w =ᵐ[mu.restrict V] Wkp.value 2 u) {K : Set E} (hKV : K ⊆ V) {C α : ℝ≥0}
    (hC : HolderOnWith C α (preciseRepresentative mu (W1p.value w)) K) :
    HolderOnWith C α (preciseRepresentative mu (Wkp.value 2 u)) K :=
  hC.congr fun _ hz => preciseRepresentative_congr_ae_nhds (V.isOpen.mem_nhds (hKV hz)) hw

/-- **Hölder continuity of `W^{2,p}` functions for `n / 2 < p < n`.** If `n < 2 p` and `p < n`,
where `n` is the dimension, the precise representative of any `u ∈ W^{2,p}(Ω)` is Hölder
continuous with exponent `2 - n / p` on every compact subset of `Ω`. -/
theorem Wkp.exists_holderOnWith_preciseRepresentative_of_isCompact_of_lt_finrank
    (hp : (finrank ℝ E : ℝ≥0∞) < 2 * p) (hpn : p < finrank ℝ E) (u : Wkp mu Omega p 2)
    {K : Set E} (hK : IsCompact K) (hKΩ : K ⊆ Omega) :
    ∃ C : ℝ≥0, HolderOnWith C ((2 : ℝ≥0∞) - finrank ℝ E / p).toNNReal
      (preciseRepresentative mu (Wkp.value 2 u)) K := by
  obtain ⟨hq, hα⟩ := exponent_facts_of_lt (ENNReal.natCast_ne_top _) hp hpn
  obtain ⟨V, hKV, hVΩ, hVc⟩ := Opens.exists_between_and_isCompact_closure hK hKΩ
  obtain ⟨_, w, hw⟩ := Wkp.exists_w1p_value_ae_eq_of_isCompact_closure_of_lt_finrank hpn u hVc hVΩ
  obtain ⟨C, hC⟩ := W1p.exists_holderOnWith_preciseRepresentative_of_isCompact hq w hK hKV
  rw [hα] at hC
  exact ⟨C, holderOnWith_preciseRepresentative_of_ae_eq hw hKV hC⟩

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
  exact ⟨C, holderOnWith_preciseRepresentative_of_ae_eq hw hKV hC⟩

/-! ### Differentiability for `p` above the dimension -/

/-- The precise representative of the weak derivative `∂ᵥu` of `u ∈ W^{2,p}(Ω)` is a weak
derivative of the precise representative of `u` in the direction `v`. -/
private theorem Wkp.hasWeakLineDerivOn_preciseRepresentative_lineDerivL (v : E)
    (u : Wkp mu Omega p 2) :
    HasWeakLineDerivOn mu Omega (preciseRepresentative mu (Wkp.value 2 u))
      (preciseRepresentative mu (Wkp.value 1 (Wkp.lineDerivL v 1 u))) v :=
  ((Wkp.hasWeakLineDerivOn_lineDerivL v 1 u).congr_ae
    (Wkp.ae_eq_preciseRepresentative 2 u)).congr_ae_deriv (Wkp.ae_eq_preciseRepresentative 1 _)

/-- For `p > n`, the precise representative of the weak derivative `∂ᵥu` of `u ∈ W^{2,p}(Ω)` is
continuous on `Ω`. -/
private theorem Wkp.continuousOn_preciseRepresentative_lineDerivL
    (hp : (finrank ℝ E : ℝ≥0∞) < p) (v : E) (u : Wkp mu Omega p 2) :
    ContinuousOn (preciseRepresentative mu (Wkp.value 1 (Wkp.lineDerivL v 1 u))) Omega := by
  simpa only [Wkp.value_one] using
    W1p.continuousOn_preciseRepresentative hp (Wkp.lineDerivL v 1 u)

/-- For `p > n`, the precise representative `u*` of `u ∈ W^{2,p}(Ω)` is `C¹` on `Ω`, and its
derivative is assembled from the precise representatives of the weak derivatives `∂ᵢu` along an
orthonormal basis. -/
private theorem Wkp.contDiffOn_preciseRepresentative_and_fderiv_eq {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (hp : (finrank ℝ E : ℝ≥0∞) < p) (u : Wkp mu Omega p 2) :
    ContDiffOn ℝ 1 (preciseRepresentative mu (Wkp.value 2 u)) Omega ∧
      ∀ x ∈ Omega, fderiv ℝ (preciseRepresentative mu (Wkp.value 2 u)) x =
        ∑ i, preciseRepresentative mu (Wkp.value 1 (Wkp.lineDerivL (b i) 1 u)) x •
          innerSL ℝ (b i) := by
  set G : ι → E → ℝ := fun i => preciseRepresentative mu (Wkp.value 1 (Wkp.lineDerivL (b i) 1 u))
  have hGc : ∀ i, ContinuousOn (G i) Omega := fun i =>
    Wkp.continuousOn_preciseRepresentative_lineDerivL hp (b i) u
  -- The precise representatives of the `∂ᵢu` are weak derivatives of that of `u`.
  have hdG : ∀ i, HasWeakLineDerivOn mu Omega (preciseRepresentative mu (Wkp.value 2 u)) (G i)
      (b i) := fun i => Wkp.hasWeakLineDerivOn_preciseRepresentative_lineDerivL (b i) u
  have hcont : ContinuousOn (preciseRepresentative mu (Wkp.value 2 u)) Omega :=
    Wkp.continuousOn_preciseRepresentative
      (hp.trans_le (le_mul_of_one_le_left' one_le_two)) u
  obtain ⟨hD, hvD⟩ := contDiffOn_sum_innerSL_and_hasWeakFDerivOn
    (fun i => contDiffOn_zero.2 (hGc i)) (hcont.locallyIntegrableOn Omega.isOpen.measurableSet)
    hdG
  exact ⟨by simpa using hvD.contDiffOn_succ hcont hD (n := 0),
    fun x hx => hvD.fderiv_eq_of_continuousOn hcont hD.continuousOn hx⟩

/-- **`W^{2,p}` functions are `C¹` for `p` above the dimension.** If `n < p ≤ ∞`, where `n` is the
dimension, the precise representative of any `u ∈ W^{2,p}(Ω)` is continuously differentiable on
`Ω`. -/
theorem Wkp.contDiffOn_preciseRepresentative (hp : (finrank ℝ E : ℝ≥0∞) < p)
    (u : Wkp mu Omega p 2) :
    ContDiffOn ℝ 1 (preciseRepresentative mu (Wkp.value 2 u)) Omega :=
  (Wkp.contDiffOn_preciseRepresentative_and_fderiv_eq (stdOrthonormalBasis ℝ E) hp u).1

/-- **The classical derivative is the weak derivative.** If `n < p ≤ ∞`, where `n` is the
dimension, the derivative of the precise representative of `u ∈ W^{2,p}(Ω)` in the direction `v`
is, at every point of `Ω`, the precise representative of the weak derivative
`∂ᵥu = TauCeti.Wkp.lineDerivL v 1 u`. -/
theorem Wkp.fderiv_preciseRepresentative_apply (hp : (finrank ℝ E : ℝ≥0∞) < p)
    (u : Wkp mu Omega p 2) (v : E) {x : E} (hx : x ∈ Omega) :
    fderiv ℝ (preciseRepresentative mu (Wkp.value 2 u)) x v =
      preciseRepresentative mu (Wkp.value 1 (Wkp.lineDerivL v 1 u)) x := by
  set ū := preciseRepresentative mu (Wkp.value 2 u)
  have hū : ContDiffOn ℝ 1 ū Omega := Wkp.contDiffOn_preciseRepresentative hp u
  -- Both sides are continuous weak derivatives of `ū` in the direction `v`.
  have h₁ : HasWeakLineDerivOn mu Omega ū (fun y => fderiv ℝ ū y v) v :=
    (hū.hasWeakFDerivOn_fderiv (μ := mu)).hasWeakLineDerivOn v
  have hc₁ : ContinuousOn (fun y => fderiv ℝ ū y v) Omega :=
    ((hū.continuousOn_fderiv_of_isOpen Omega.isOpen le_rfl).clm_apply continuousOn_const)
  exact Measure.eqOn_open_of_ae_eq
    (h₁.ae_eq (Wkp.hasWeakLineDerivOn_preciseRepresentative_lineDerivL v u)) Omega.isOpen hc₁
    (Wkp.continuousOn_preciseRepresentative_lineDerivL hp v u) hx

/-- **Hölder continuity of the derivative of `W^{2,p}` functions for `p` above the dimension.** If
`n < p ≤ ∞`, where `n` is the dimension, the derivative of the precise representative of any
`u ∈ W^{2,p}(Ω)` is Hölder continuous with exponent `1 - n / p` on every compact subset of `Ω`. -/
theorem Wkp.exists_holderOnWith_fderiv_preciseRepresentative_of_isCompact
    (hp : (finrank ℝ E : ℝ≥0∞) < p) (u : Wkp mu Omega p 2) {K : Set E} (hK : IsCompact K)
    (hKΩ : K ⊆ Omega) :
    ∃ C : ℝ≥0, HolderOnWith C ((1 : ℝ≥0∞) - finrank ℝ E / p).toNNReal
      (fderiv ℝ (preciseRepresentative mu (Wkp.value 2 u))) K := by
  set b := stdOrthonormalBasis ℝ E
  have hfd := (Wkp.contDiffOn_preciseRepresentative_and_fderiv_eq b hp u).2
  -- Each coordinate `G i` of the derivative is Hölder continuous by Morrey's embedding.
  choose C hC using fun i => by
    simpa only [Wkp.value_one] using
      W1p.exists_holderOnWith_preciseRepresentative_of_isCompact hp (Wkp.lineDerivL (b i) 1 u)
        hK hKΩ
  refine ⟨∑ i, C i, HolderOnWith.of_dist_le fun x hx y hy => ?_⟩
  simp only [hfd x (hKΩ hx), hfd y (hKΩ hy), dist_eq_norm, ← Finset.sum_sub_distrib,
    NNReal.coe_sum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  simpa [← sub_smul, norm_smul, b.orthonormal.1 i, ← dist_eq_norm] using (hC i).dist_le hx hy

end TauCeti
