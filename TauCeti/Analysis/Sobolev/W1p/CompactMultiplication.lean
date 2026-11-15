/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.LipschitzDomain.RellichKondrachov
public import TauCeti.Analysis.Sobolev.RellichKondrachov
public import TauCeti.Analysis.Sobolev.W1p.MixedMultiplication
public import TauCeti.MeasureTheory.Function.Lp.Holder

/-!
# Compact multiplication by `Lᵖ` functions on first-order Sobolev spaces

Let `Ω` be a bounded open subset of a finite-dimensional real inner product space of dimension
`n ≥ 1`, let `n < p < ∞` and `1 ≤ q ≤ p`. For `α ∈ Lᵖ(Ω, G)`, multiplication

`u ↦ u α : W^{1,q}_0(Ω) → L^q(Ω, G)`

is a compact operator. The same holds on all of `W^{1,q}(Ω)` for a bounded Lipschitz domain
`Ω ⊆ ℝ × E` with Lebesgue measure, where now `n = dim (ℝ × E) = 1 + dim E`. This is the local
form of McDuff--Salamon, Lemma C.2.2: a zeroth-order term of class `Lᵖ` is a compact perturbation
of a first-order operator `W^{1,q} → L^q`.

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
  multiplication on `W^{1,q}(Ω)` for a bounded Lipschitz domain `Ω ⊆ ℝ × E` (Lebesgue measure).

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

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure] {p q : ℝ≥0} [Fact (1 ≤ (q : ℝ≥0∞))]

/-- Compact multiplication on a Sobolev space `X` over `Ω` from an extension operator into
`W^{1,q}(E)` that preserves values on `Ω`, and a compact value map into `L^q(Ω)`. The operator is
the mixed product `W1p.mixedBilinL` composed with the extension. -/
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
  let B : G →L[ℝ] ℝ →L[ℝ] G := (ContinuousLinearMap.lsmul ℝ ℝ).flip
  let P := W1p.mixedBilinL (μ := μ) (Ω := ⊤) hnp hqp hΩ.isCompact_closure (subset_univ _) B
  refine ⟨(P α).comp T, fun u => ?_, ?_⟩
  · filter_upwards [W1p.coeFn_mixedBilinL hnp hqp hΩ.isCompact_closure (subset_univ _) B α (T u),
      hTV u] with x h₁ h₂
    simp only [ContinuousLinearMap.comp_apply, P, h₁, h₂, B, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.lsmul_apply]
  -- The mixed product is Hölder multiplication after the value embedding into `L^s`.
  obtain ⟨s, hs, hhs, S, hS⟩ := W1p.exists_mixed_valueEmbedding (μ := μ) (Ω := ⊤) hnp hqp
    hΩ.isCompact_closure (subset_univ _)
  let : Fact (1 ≤ s) := ⟨hs⟩
  let : ENNReal.HolderTriple (p : ℝ≥0∞) s (q : ℝ≥0∞) := hhs
  have hP : (B.holderL _ p s q).bilinearComp (ContinuousLinearMap.id ℝ _) S = P :=
    W1p.mixedBilinL_unique hnp hqp hΩ.isCompact_closure (subset_univ _) B fun f g => by
      rw [ContinuousLinearMap.bilinearComp_apply, ContinuousLinearMap.id_apply]
      filter_upwards [B.coeFn_holder (r := (q : ℝ≥0∞)) f (S g), hS g] with x h₁ h₂
      rw [ContinuousLinearMap.holderL_apply_apply, h₁, h₂]
  have hPT : (P α).comp T = (B.holderL _ p s q α).comp (S.comp T) := by
    rw [← hP]
    ext u : 1
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.bilinearComp_apply,
      ContinuousLinearMap.id_apply]
  rw [hPT]
  exact B.isCompactOperator_holderL_comp_of_ae_eq ENNReal.coe_ne_top hV (S.comp T)
    (fun u => (hS (T u)).trans (hTV u)) α

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
`Ω ⊆ ℝ × E` be a bounded Lipschitz domain, let `n = dim (ℝ × E) = 1 + dim E`, and let
`n < p < ∞` and `1 ≤ q ≤ p`. For `α ∈ Lᵖ(Ω, G)`, multiplication `u ↦ u α` is a compact operator
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
  have hTV (u : W1p volume Ω q) :
      W1p.value (T u) =ᵐ[volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))]
        W1p.valueL (mu := volume) u := by
    rw [W1p.valueL_apply]
    exact W1p.value_ae_eq_of_restrictL_comp_eq_id le_top hT u
  obtain ⟨M, hM, hMc⟩ := exists_isCompactOperator_value_smul_of_extensionL hb hnp hqp T
    (W1p.isCompactOperator_valueL_of_isLipschitzDomainWith hΩ hb) hTV α
  exact ⟨M, fun u => by simpa only [W1p.valueL_apply] using hM u, hMc⟩

end TauCeti

end
