/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.LipschitzDomain.RellichKondrachov
public import TauCeti.Analysis.Sobolev.RellichKondrachov
public import TauCeti.Analysis.Sobolev.W1p.SobolevEmbedding
public import TauCeti.MeasureTheory.Function.Lp.Holder

/-!
# Compact multiplication by `Lᵖ` functions on first-order Sobolev spaces

Let `Ω` be a bounded open subset of a finite-dimensional real inner product space of dimension
`n ≥ 1`, let `n < p < ∞` and `1 ≤ q ≤ p`. For `α ∈ Lᵖ(Ω, G)`, multiplication

`u ↦ u α : W^{1,q}_0(Ω) → L^q(Ω, G)`

is a compact operator. The same holds on all of `W^{1,q}(Ω)` when `Ω` is a bounded Lipschitz
domain. This is the local form of McDuff--Salamon, Lemma C.2.2: a zeroth-order term of class
`Lᵖ` is a compact perturbation of a first-order operator `W^{1,q} → L^q`.

Put `1/s = 1/q - 1/p`. Since `1/q - 1/s = 1/p < 1/n`, the inclusion `W^{1,q} → L^s(Ω)` is bounded:
by the subcritical Sobolev embedding when `q < p`, and by Morrey's embedding into `L^∞` when
`q = p`. Hölder's inequality then makes multiplication by `α` a bounded operator into `L^q`.
Compactness does not need a compact embedding into `L^s`: multiplication by a simple function
factors through the Rellich--Kondrachov embedding `W^{1,q} → L^q`, and simple functions are
dense in `Lᵖ` (`ContinuousLinearMap.isCompactOperator_holderL_comp_of_ae_eq`).

## Main declarations

* `TauCeti.W1p0.exists_isCompactOperator_value_smul`: compact multiplication on
  `W^{1,q}_0(Ω)` for bounded open `Ω`.
* `TauCeti.W1p.exists_isCompactOperator_value_smul_of_isLipschitzDomainWith`: compact
  multiplication on `W^{1,q}(Ω)` for a bounded Lipschitz domain `Ω`.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Lemma C.2.2.
* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Corollary 9.14 and Theorem 9.16.
-/

public section

noncomputable section

open Bornology MeasureTheory Module Set TopologicalSpace
open scoped ENNReal NNReal

namespace TauCeti

/-- For `0 < q < p`, the exponent `s` with `1/s = 1/q - 1/p` is at least `q` and completes a
Hölder triple `1/p + 1/s = 1/q`. -/
private theorem exists_holderTriple_of_lt {p q : ℝ≥0} (hq : 0 < q) (hqp : q < p) :
    ∃ s : ℝ≥0, q ≤ s ∧ (q : ℝ)⁻¹ - (s : ℝ)⁻¹ = (p : ℝ)⁻¹ ∧
      ENNReal.HolderTriple (p : ℝ≥0∞) (s : ℝ≥0∞) (q : ℝ≥0∞) := by
  have hp : 0 < p := hq.trans hqp
  have hlt : p⁻¹ < q⁻¹ := inv_strictAnti₀ hq hqp
  have hd : 0 < q⁻¹ - p⁻¹ := tsub_pos_of_lt hlt
  refine ⟨(q⁻¹ - p⁻¹)⁻¹, ?_, ?_, ⟨?_⟩⟩
  · rw [le_inv_comm₀ hq hd]
    exact tsub_le_self
  · rw [NNReal.coe_inv, inv_inv, NNReal.coe_sub hlt.le, NNReal.coe_inv, NNReal.coe_inv]
    ring
  · rw [← ENNReal.coe_inv hp.ne', ← ENNReal.coe_inv (inv_pos.2 hd).ne', inv_inv,
      ← ENNReal.coe_inv hq.ne', ← ENNReal.coe_add, add_tsub_cancel_of_le hlt.le]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure] {p q : ℝ≥0} [Fact (1 ≤ (q : ℝ≥0∞))]

/-- For `n < p` and `1 ≤ q ≤ p`, there is an exponent `s` with `1/p + 1/s = 1/q` such that the
inclusion `W^{1,q}(E) → L^s(V)` is bounded on every set `V` with compact closure. -/
private theorem W1p.exists_holderTriple_lpEmbeddingL (hnp : (finrank ℝ E : ℝ≥0) < p)
    (hqp : q ≤ p) {V : Set E} (hVc : IsCompact (closure V)) :
    ∃ (s : ℝ≥0∞) (_ : Fact (1 ≤ s)) (_ : ENNReal.HolderTriple (p : ℝ≥0∞) s (q : ℝ≥0∞)),
      ∃ S : W1p μ ⊤ (q : ℝ≥0∞) →L[ℝ] Lp ℝ s (μ.restrict V),
        ∀ u, S u =ᵐ[μ.restrict V] W1p.value u := by
  rcases hqp.lt_or_eq with hqp | rfl
  · -- Below the diagonal, `s` is finite and the gain `1/q - 1/s = 1/p` is subcritical.
    have hq : 0 < q := by
      have h : (1 : ℝ≥0∞) ≤ q := Fact.out
      exact ENNReal.coe_pos.1 (zero_lt_one.trans_le h)
    obtain ⟨s, hqs, hgap, hhol⟩ := exists_holderTriple_of_lt hq hqp
    have hs : Fact (1 ≤ (s : ℝ≥0∞)) :=
      ⟨(Fact.out : (1 : ℝ≥0∞) ≤ q).trans (ENNReal.coe_le_coe.2 hqs)⟩
    have hn : (0 : ℝ) < finrank ℝ E := by exact_mod_cast finrank_pos
    have hgap' : (q : ℝ)⁻¹ - (s : ℝ)⁻¹ < (finrank ℝ E : ℝ)⁻¹ := by
      rw [hgap]
      exact inv_strictAnti₀ hn (by exact_mod_cast hnp)
    obtain ⟨S, hS⟩ := W1p.exists_sobolevEmbeddingL_of_subcritical_gain (μ := μ) (Ω := ⊤) hqs
      hgap' hVc (subset_univ _)
    exact ⟨s, hs, hhol, S, hS⟩
  · -- On the diagonal, `s = ∞` and Morrey's embedding applies.
    obtain ⟨S, hS⟩ := W1p.exists_lpInftyEmbeddingL_of_isCompact_closure (μ := μ) (Ω := ⊤) hnp
      hVc (subset_univ _)
    exact ⟨∞, inferInstance, inferInstance, S, hS⟩

/-- Compact multiplication on a Sobolev space `X` over `Ω` from an extension operator into
`W^{1,q}(E)` that preserves values on `Ω`, and a compact value map into `L^q(Ω)`. -/
private theorem exists_isCompactOperator_value_smul_of_extensionL {X : Type*}
    [SeminormedAddCommGroup X] [NormedSpace ℝ X] {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [CompleteSpace G] {Ω : Set E} (hΩ : IsBounded Ω)
    (hnp : (finrank ℝ E : ℝ≥0) < p) (hqp : q ≤ p)
    (T : X →L[ℝ] W1p μ ⊤ (q : ℝ≥0∞)) {V : X →L[ℝ] Lp ℝ q (μ.restrict Ω)}
    (hV : IsCompactOperator V) (hTV : ∀ u, W1p.value (T u) =ᵐ[μ.restrict Ω] V u)
    (α : Lp G p (μ.restrict Ω)) :
    ∃ M : X →L[ℝ] Lp G q (μ.restrict Ω),
      (∀ u, M u =ᵐ[μ.restrict Ω] fun x => V u x • α x) ∧ IsCompactOperator M := by
  have hp : Fact (1 ≤ (p : ℝ≥0∞)) :=
    ⟨(Fact.out : (1 : ℝ≥0∞) ≤ q).trans (ENNReal.coe_le_coe.2 hqp)⟩
  obtain ⟨s, _, _, S, hS⟩ :=
    W1p.exists_holderTriple_lpEmbeddingL (μ := μ) hnp hqp hΩ.isCompact_closure
  let B : G →L[ℝ] ℝ →L[ℝ] G := (ContinuousLinearMap.lsmul ℝ ℝ).flip
  have hι (u : X) : (S.comp T) u =ᵐ[μ.restrict Ω] V u := (hS (T u)).trans (hTV u)
  refine ⟨(B.holderL _ p s q α).comp (S.comp T), fun u => ?_,
    B.isCompactOperator_holderL_comp_of_ae_eq ENNReal.coe_ne_top hV (S.comp T) hι α⟩
  filter_upwards [B.coeFn_holder (r := (q : ℝ≥0∞)) α ((S.comp T) u), hι u] with x h₁ h₂
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.holderL_apply_apply, h₁, h₂]
  rfl

/-- **Compact multiplication by `Lᵖ` functions on `W^{1,q}_0`.** Let `Ω` be a bounded open
subset of a finite-dimensional real inner product space of dimension `n ≥ 1`, and let
`n < p < ∞` and `1 ≤ q ≤ p`. For `α ∈ Lᵖ(Ω, G)`, multiplication `u ↦ u α` is a compact operator
`W^{1,q}_0(Ω) → L^q(Ω, G)`.

No boundary regularity is needed. This is the local form of McDuff--Salamon, Lemma C.2.2. -/
theorem W1p0.exists_isCompactOperator_value_smul {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [CompleteSpace G] {Ω : Opens E} (hΩ : IsBounded (Ω : Set E))
    (hnp : (finrank ℝ E : ℝ≥0) < p) (hqp : q ≤ p) (α : Lp G p (μ.restrict Ω)) :
    ∃ M : W1p0 μ Ω q →L[ℝ] Lp G q (μ.restrict Ω),
      (∀ u, M u =ᵐ[μ.restrict Ω] fun x => W1p.value (u : W1p μ Ω q) x • α x) ∧
        IsCompactOperator M := by
  -- Extension by zero preserves values on `Ω`.
  let T : W1p0 μ Ω q →L[ℝ] W1p μ ⊤ q :=
    (w1p0Submodule μ ⊤ q).toSubmodule.subtypeL.comp (W1p0.extendByZeroL le_top)
  have hT (u : W1p0 μ Ω q) :
      W1p.value (T u) =ᵐ[μ.restrict Ω] W1p0.valueL (mu := μ) u := by
    rw [W1p0.valueL_apply]
    simp only [T, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
    rw [W1p0.value_extendByZeroL]
    exact coeFn_extendByZeroLpₗᵢ_restrict ℝ Ω.isOpen.measurableSet
      (SetLike.coe_subset_coe.mpr (le_top : Ω ≤ ⊤)) (W1p.value (u : W1p μ Ω q))
  obtain ⟨M, hM, hMc⟩ := exists_isCompactOperator_value_smul_of_extensionL hΩ hnp hqp T
    (W1p0.isCompactOperator_valueL ENNReal.coe_ne_top hΩ) hT α
  exact ⟨M, fun u => by simpa only [W1p0.valueL_apply] using hM u, hMc⟩

omit [Nontrivial E] in
/-- **Compact multiplication by `Lᵖ` functions on bounded Lipschitz domains.** Let
`Ω ⊆ ℝ × E` be a bounded Lipschitz domain of dimension `n`, and let `n < p < ∞` and
`1 ≤ q ≤ p`. For `α ∈ Lᵖ(Ω, G)`, multiplication `u ↦ u α` is a compact operator
`W^{1,q}(Ω) → L^q(Ω, G)`. -/
theorem W1p.exists_isCompactOperator_value_smul_of_isLipschitzDomainWith {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {Ω : Opens (WithLp 2 (ℝ × E))} {L : ℝ≥0}
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E))))
    (hnp : (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0) < p) (hqp : q ≤ p)
    (α : Lp G p (volume.restrict (Ω : Set (WithLp 2 (ℝ × E))))) :
    ∃ M : W1p volume Ω q →L[ℝ] Lp G q (volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))),
      (∀ u, M u =ᵐ[volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))]
        fun x => W1p.value u x • α x) ∧ IsCompactOperator M := by
  obtain ⟨T, hT⟩ := W1p.exists_extensionL_of_isLipschitzDomainWith (p := q) hΩ hb
  -- The extension restricts back to the original function on `Ω`.
  have hTV (u : W1p volume Ω q) :
      W1p.value (T u) =ᵐ[volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))]
        W1p.valueL (mu := volume) u := by
    have hu : W1p.restrictL le_top (T u) = u := by
      simpa using congrArg (· u) hT
    rw [W1p.valueL_apply]
    filter_upwards [W1p.value_restrictL_ae le_top (T u)] with x hx
    rw [← hx, hu]
  obtain ⟨M, hM, hMc⟩ := exists_isCompactOperator_value_smul_of_extensionL hb hnp hqp T
    (W1p.isCompactOperator_valueL_of_isLipschitzDomainWith ENNReal.coe_ne_top hΩ hb) hTV α
  exact ⟨M, fun u => by simpa only [W1p.valueL_apply] using hM u, hMc⟩

end TauCeti

end
