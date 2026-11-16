/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.LipschitzDomain.Wkp.Embedding
public import TauCeti.Analysis.Sobolev.W1p.CompactMultiplication.Basic
import TauCeti.Data.ENNReal.Inv

/-!
# Compact multiplication by Sobolev coefficients at every exponent

Let `Ω` be a bounded open subset of a finite-dimensional real inner product space of dimension
`n`. Multiplication by `α ∈ Lʳ(Ω)` with `n < r` is compact from `W^{1,q}_0(Ω)` to `L^q(Ω)`
only for `q ≤ r` (`TauCeti.W1p0.exists_isCompactOperator_value_smul`). A coefficient of class
`W^{1,p}` with `n ≤ p` is better: on a set whose closure is a compact subset of its domain it lies
in `L^s` for every finite `s` (and is bounded when `n < p`, by Morrey), so multiplication by it is
compact `W^{1,q}_0(Ω) → L^q(Ω)` for *every* finite `q ≥ 1`, including `q > p`. The same holds on
all of `W^{1,q}(Ω)` for a bounded Lipschitz domain `Ω ⊆ ℝ × E` and `n ≤ p`, and for a coefficient
of class `W^{m+1,p}(Ω)` with `n ≤ (m + 1) p`, which for finite `p` embeds in `W^{1,(m+1)p}(Ω)`.

## Main declarations

* `TauCeti.W1p0.exists_isCompactOperator_value_smul_of_w1p`: compact multiplication on
  `W^{1,q}_0(Ω)` at every finite `q ≥ 1` by a `W^{1,p}` coefficient, `n ≤ p`, defined on a
  neighbourhood of `closure Ω`.
* `TauCeti.W1p0.exists_isCompactOperator_value_smul_of_wkp`: the same for a `W^{m+1,p}`
  coefficient.
* `TauCeti.W1p.exists_isCompactOperator_value_smul_of_w1p_of_isLipschitzDomainWith` and
  `TauCeti.W1p.exists_isCompactOperator_value_smul_of_wkp_of_isLipschitzDomainWith`: the
  versions on all of `W^{1,q}(Ω)` for a bounded Lipschitz domain `Ω ⊆ ℝ × E`, for `n ≤ p` and
  `n ≤ (m + 1) p` respectively.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Theorem C.1.10
  and Lemma C.2.2.
-/

public section

noncomputable section

open Bornology MeasureTheory Module Set TopologicalSpace
open scoped ENNReal NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {q : ℝ≥0} [Fact (1 ≤ (q : ℝ≥0∞))]

section Interior

variable {μ : Measure E} [μ.IsAddHaarMeasure]

/-- **Compact multiplication by `W^{1,p}` coefficients on `W^{1,q}_0`, every finite `q`.** Let
`Ω` be a bounded open set whose closure lies in an open set `Ω'`, let `n = dim E`,
`1 ≤ p ≤ ∞` with `n ≤ p`, and `α ∈ W^{1,p}(Ω')`. Then multiplication `u ↦ u α` is a compact
operator `W^{1,q}_0(Ω) → L^q(Ω)` for every finite `q ≥ 1`, including `q > p`: `α` lies in
`L^s(Ω)` for every finite `s` (`TauCeti.W1p.memLp_value_of_isCompact_closure_of_finrank_le`). -/
theorem W1p0.exists_isCompactOperator_value_smul_of_w1p {Ω Ω' : Opens E}
    (hΩ : IsBounded (Ω : Set E)) (hΩΩ' : closure (Ω : Set E) ⊆ Ω') {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hnp : (finrank ℝ E : ℝ≥0∞) ≤ p) (α : W1p μ Ω' p) :
    ∃ M : W1p0 μ Ω q →L[ℝ] Lp ℝ q (μ.restrict Ω),
      (∀ u, M u =ᵐ[μ.restrict Ω] fun x => W1p.value (u : W1p μ Ω q) x • W1p.value α x) ∧
        IsCompactOperator M :=
  -- `α` lies in `Lˢ(Ω)` for the finite exponent `s = max q (n + 1)`, with `n < s` and `q ≤ s`.
  W1p0.exists_isCompactOperator_value_smul_of_memLp hΩ
    ((lt_add_one _).trans_le (le_max_right _ _)) (le_max_left _ _)
    (W1p.memLp_value_of_isCompact_closure_of_finrank_le hnp hΩ.isCompact_closure hΩΩ'
      (max q (finrank ℝ E + 1)) α)

/-- **Compact multiplication by `W^{m+1,p}` coefficients on `W^{1,q}_0`, every finite `q`.**
The higher-order form of `TauCeti.W1p0.exists_isCompactOperator_value_smul_of_w1p`, under the
same hypothesis `n ≤ p`. -/
theorem W1p0.exists_isCompactOperator_value_smul_of_wkp {Ω Ω' : Opens E}
    (hΩ : IsBounded (Ω : Set E)) (hΩΩ' : closure (Ω : Set E) ⊆ Ω') {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hnp : (finrank ℝ E : ℝ≥0∞) ≤ p) (m : ℕ)
    (α : Wkp μ Ω' p (m + 1)) :
    ∃ M : W1p0 μ Ω q →L[ℝ] Lp ℝ q (μ.restrict Ω),
      (∀ u, M u =ᵐ[μ.restrict Ω] fun x =>
        W1p.value (u : W1p μ Ω q) x • Wkp.value (m + 1) α x) ∧ IsCompactOperator M := by
  obtain ⟨M, hM, hMc⟩ :=
    W1p0.exists_isCompactOperator_value_smul_of_w1p (q := q) hΩ hΩΩ' hnp (Wkp.firstOrder m α)
  exact ⟨M, fun u => by rw [← Wkp.value_firstOrder]; exact hM u, hMc⟩

end Interior

section LipschitzDomain

variable {Ω : Opens (WithLp 2 (ℝ × E))} {L : ℝ≥0}

/-- **Compact multiplication by `W^{1,p}` coefficients on bounded Lipschitz domains, every
finite `q`.** Let `Ω ⊆ ℝ × E` be a bounded Lipschitz domain, `n = dim (ℝ × E)`, `1 ≤ p ≤ ∞`
with `n ≤ p`, and `α ∈ W^{1,p}(Ω)`. Then multiplication `u ↦ u α` is a compact operator
`W^{1,q}(Ω) → L^q(Ω)` for every finite `q ≥ 1`, including `q > p`: `α` lies in `L^s(Ω)` for
every finite `s`. -/
theorem W1p.exists_isCompactOperator_value_smul_of_w1p_of_isLipschitzDomainWith
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hnp : (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0∞) ≤ p) (α : W1p volume Ω p) :
    ∃ M : W1p volume Ω q →L[ℝ] Lp ℝ q (volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))),
      (∀ u, M u =ᵐ[volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))]
        fun x => W1p.value u x • W1p.value α x) ∧ IsCompactOperator M := by
  have hps : p⁻¹ < ((max ((finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0) + 1) q : ℝ≥0) : ℝ≥0∞)⁻¹ +
      (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0∞)⁻¹ := by
    calc p⁻¹ ≤ (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0∞)⁻¹ := ENNReal.inv_le_inv.2 hnp
      _ < _ := by
          rw [add_comm]
          exact ENNReal.lt_add_right (by simp [Module.finrank_pos.ne']) (by simp)
  obtain ⟨C, hC⟩ :=
    W1p.exists_eLpNorm_value_le_of_subcritical_gain_of_isLipschitzDomainWith ENNReal.coe_ne_top
      hps hΩ hb
  exact W1p.exists_isCompactOperator_value_smul_of_memLp_of_isLipschitzDomainWith hΩ hb
    ((lt_add_one _).trans_le (le_max_left _ _)) (le_max_right _ _)
    ((hC α).trans_lt (by finiteness))

/-- **Compact multiplication by `W^{m+1,p}` coefficients on bounded Lipschitz domains, every
finite `q`.** Let `Ω ⊆ ℝ × E` be a bounded Lipschitz domain, `n = dim (ℝ × E)`, `1 ≤ p ≤ ∞` with
`n ≤ (m + 1) p`, and `α ∈ W^{m+1,p}(Ω)`. Then multiplication `u ↦ u α` is a compact operator
`W^{1,q}(Ω) → L^q(Ω)` for every finite `q ≥ 1`: for finite `p`, `α` lies in `W^{1,(m+1)p}(Ω)`,
and `TauCeti.W1p.exists_isCompactOperator_value_smul_of_w1p_of_isLipschitzDomainWith` applies. -/
theorem W1p.exists_isCompactOperator_value_smul_of_wkp_of_isLipschitzDomainWith
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) {p : ℝ≥0∞} [Fact (1 ≤ p)] (m : ℕ)
    (hnp : (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0∞) ≤ (m + 1) * p)
    (α : Wkp volume Ω p (m + 1)) :
    ∃ M : W1p volume Ω q →L[ℝ] Lp ℝ q (volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))),
      (∀ u, M u =ᵐ[volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))]
        fun x => W1p.value u x • Wkp.value (m + 1) α x) ∧ IsCompactOperator M := by
  by_cases hp : p = ∞
  · -- A `W^{m+1,∞}` coefficient is in particular a `W^{1,∞}` coefficient.
    exact (W1p.exists_isCompactOperator_value_smul_of_w1p_of_isLipschitzDomainWith (q := q) hΩ hb
      (hp ▸ le_top) (Wkp.firstOrder m α)).imp fun M hM =>
        ⟨fun u => by rw [← Wkp.value_firstOrder]; exact hM.1 u, hM.2⟩
  -- Otherwise `p` is finite and `α` lies in `W^{1,(m+1)p}(Ω)`.
  have hr : ((p.toNNReal : ℝ≥0) : ℝ≥0∞) = p := ENNReal.coe_toNNReal hp
  have hr₁ : (1 : ℝ≥0) ≤ p.toNNReal := by exact_mod_cast hr ▸ (Fact.out : (1 : ℝ≥0∞) ≤ p)
  have hrr : p.toNNReal ≤ (m + 1 : ℕ) * p.toNNReal := le_mul_of_one_le_left zero_le (by simp)
  have : Fact (1 ≤ (((m + 1 : ℕ) * p.toNNReal : ℝ≥0) : ℝ≥0∞)) :=
    ⟨by exact_mod_cast hr₁.trans hrr⟩
  have hnr : (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0) ≤ (m + 1 : ℕ) * p.toNNReal := by
    rw [← hr] at hnp
    exact_mod_cast hnp
  have h := ENNReal.inv_le_inv_mul_add_and_inv_mul_le_inv hnr
  rw [hr] at h
  obtain ⟨T, hT⟩ :=
    Wkp.exists_w1pEmbeddingL_of_isLipschitzDomainWith m ENNReal.coe_ne_top h.1 h.2 hΩ hb
  have hnr' : (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0∞) ≤
      (((m + 1 : ℕ) * p.toNNReal : ℝ≥0) : ℝ≥0∞) := by
    exact_mod_cast hnr
  refine (W1p.exists_isCompactOperator_value_smul_of_w1p_of_isLipschitzDomainWith (q := q) hΩ hb
    hnr' (T α)).imp fun M hM => ⟨fun u => ?_, hM.2⟩
  filter_upwards [hM.1 u, hT α] with x h₁ h₂
  rw [h₁, h₂]

end LipschitzDomain

end TauCeti

end
