/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.LipschitzDomain.Wkp.Embedding
public import TauCeti.Analysis.Sobolev.W1p.CompactMultiplication.Basic

/-!
# Compact multiplication by Sobolev coefficients at every exponent

Let `Ω` be a bounded open subset of a finite-dimensional real inner product space of dimension
`n`. Multiplication by `α ∈ Lʳ(Ω)` with `n < r` is compact from `W^{1,q}_0(Ω)` to `L^q(Ω)`
only for `q ≤ r` (`TauCeti.W1p0.exists_isCompactOperator_value_smul`). A coefficient of class
`W^{1,p}` with `n ≤ p` is better: on a set whose closure is a compact subset of its domain it lies
in `L^s` for every finite `s` (and is bounded when `n < p`, by Morrey), so multiplication by it is
compact `W^{1,q}_0(Ω) → L^q(Ω)` for *every* `q ≥ 1`, including `q > p`. The same holds on all of
`W^{1,q}(Ω)` for a bounded Lipschitz domain `Ω ⊆ ℝ × E` and `n ≤ p`, and for a coefficient of
class `W^{m+1,p}(Ω)` with `n ≤ (m + 1) p`, which embeds in `W^{1,(m+1)p}(Ω)`.

## Main declarations

* `TauCeti.W1p0.exists_isCompactOperator_value_smul_of_w1p`: compact multiplication on
  `W^{1,q}_0(Ω)` at every `q` by a `W^{1,p}` coefficient, `n ≤ p`, defined on a neighbourhood of
  `closure Ω`.
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
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

section Interior

variable {μ : Measure E} [μ.IsAddHaarMeasure]

/-- Compact multiplication on `W^{1,q}_0(Ω)` by a coefficient `α ∈ Lʳ(Ω, G)` given as a function,
for `n < r` and `q ≤ r`. -/
private theorem W1p0.exists_isCompactOperator_value_smul_of_memLp [Nontrivial E] {Ω : Opens E}
    (hΩ : IsBounded (Ω : Set E)) {r : ℝ≥0} (hnr : (finrank ℝ E : ℝ≥0) < r) (hqr : q ≤ r)
    {α : E → G} (hα : MemLp α r (μ.restrict Ω)) :
    ∃ M : W1p0 μ Ω q →L[ℝ] Lp G q (μ.restrict Ω),
      (∀ u, M u =ᵐ[μ.restrict Ω] fun x => W1p.value (u : W1p μ Ω q) x • α x) ∧
        IsCompactOperator M := by
  obtain ⟨M, hM, hMc⟩ :=
    W1p0.exists_isCompactOperator_value_smul (μ := μ) hΩ hnr hqr (hα.toLp α)
  refine ⟨M, fun u => ?_, hMc⟩
  filter_upwards [hM u, hα.coeFn_toLp] with x h₁ h₂
  rw [h₁, h₂]

/-- **Compact multiplication by `W^{1,p}` coefficients on `W^{1,q}_0`, every `q`.** Let `Ω` be
a bounded open set whose closure lies in an open set `Ω'`, let `n ≤ p < ∞` and
`α ∈ W^{1,p}(Ω')`. Then multiplication `u ↦ u α` is a compact operator
`W^{1,q}_0(Ω) → L^q(Ω)` for every `q ≥ 1`, including `q > p`: `α` lies in `L^s(Ω)` for every
finite `s`. -/
theorem W1p0.exists_isCompactOperator_value_smul_of_w1p {Ω Ω' : Opens E}
    (hΩ : IsBounded (Ω : Set E)) (hΩΩ' : closure (Ω : Set E) ⊆ Ω') {p : ℝ≥0}
    [Fact (1 ≤ (p : ℝ≥0∞))] (hnp : (finrank ℝ E : ℝ≥0) ≤ p) (α : W1p μ Ω' p) :
    ∃ M : W1p0 μ Ω q →L[ℝ] Lp ℝ q (μ.restrict Ω),
      (∀ u, M u =ᵐ[μ.restrict Ω] fun x => W1p.value (u : W1p μ Ω q) x • W1p.value α x) ∧
        IsCompactOperator M := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · -- In a trivial space `n = 0 < p`, so Morrey's embedding bounds `α` on `Ω`.
    have hnp' : (finrank ℝ E : ℝ≥0) < p := by
      rw [finrank_zero_of_subsingleton, Nat.cast_zero]
      exact zero_lt_one.trans_le (by exact_mod_cast (Fact.out : (1 : ℝ≥0∞) ≤ p))
    obtain ⟨S, hS⟩ :=
      W1p.exists_lpInftyEmbeddingL_of_isCompact_closure (μ := μ) hnp' hΩ.isCompact_closure hΩΩ'
    exact W1p0.exists_isCompactOperator_value_smul_of_memLp_top hΩ
      ((Lp.memLp (S α)).ae_eq (hS α))
  -- Otherwise `α` lies in `Lˢ(Ω)` for a finite `s` with `n < s` and `q ≤ s`.
  set s : ℝ≥0 := max p (max q (finrank ℝ E + 1))
  have hns : (finrank ℝ E : ℝ≥0) < s := (lt_add_one _).trans_le
    ((le_max_right _ _).trans (le_max_right _ _))
  have hgap : (p : ℝ)⁻¹ - (s : ℝ)⁻¹ < (finrank ℝ E : ℝ)⁻¹ := by
    have hs : (0 : ℝ) < s := by exact_mod_cast zero_le.trans_lt hns
    calc (p : ℝ)⁻¹ - (s : ℝ)⁻¹ < (p : ℝ)⁻¹ := sub_lt_self _ (inv_pos.2 hs)
      _ ≤ (finrank ℝ E : ℝ)⁻¹ := inv_anti₀ (by exact_mod_cast finrank_pos) (by exact_mod_cast hnp)
  obtain ⟨C, hC⟩ := W1p.exists_eLpNorm_value_le_of_subcritical_gain (μ := μ) (s := s)
    (le_max_left _ _) hgap hΩ.isCompact_closure hΩΩ'
  exact W1p0.exists_isCompactOperator_value_smul_of_memLp hΩ hns
    ((le_max_left _ _).trans (le_max_right _ _))
    ((hC α).trans_lt (by finiteness))

/-- **Compact multiplication by `W^{m+1,p}` coefficients on `W^{1,q}_0`, every `q`.** The
higher-order form of `TauCeti.W1p0.exists_isCompactOperator_value_smul_of_w1p`. -/
theorem W1p0.exists_isCompactOperator_value_smul_of_wkp {Ω Ω' : Opens E}
    (hΩ : IsBounded (Ω : Set E)) (hΩΩ' : closure (Ω : Set E) ⊆ Ω') {p : ℝ≥0}
    [Fact (1 ≤ (p : ℝ≥0∞))] (hnp : (finrank ℝ E : ℝ≥0) ≤ p) (m : ℕ)
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

/-- Compact multiplication on `W^{1,q}(Ω)` for a bounded Lipschitz domain `Ω ⊆ ℝ × E` by a
coefficient `α ∈ Lʳ(Ω, G)` given as a function, for `n < r` and `q ≤ r`. -/
private theorem W1p.exists_isCompactOperator_value_smul_of_memLp_of_isLipschitzDomainWith
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) {r : ℝ≥0}
    (hnr : (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0) < r) (hqr : q ≤ r)
    {α : WithLp 2 (ℝ × E) → G} (hα : MemLp α r (volume.restrict (Ω : Set (WithLp 2 (ℝ × E))))) :
    ∃ M : W1p volume Ω q →L[ℝ] Lp G q (volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))),
      (∀ u, M u =ᵐ[volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))]
        fun x => W1p.value u x • α x) ∧ IsCompactOperator M := by
  obtain ⟨M, hM, hMc⟩ :=
    W1p.exists_isCompactOperator_value_smul_of_isLipschitzDomainWith hΩ hb hnr hqr (hα.toLp α)
  refine ⟨M, fun u => ?_, hMc⟩
  filter_upwards [hM u, hα.coeFn_toLp] with x h₁ h₂
  rw [h₁, h₂]

/-- **Compact multiplication by `W^{1,p}` coefficients on bounded Lipschitz domains, every
`q`.** Let `Ω ⊆ ℝ × E` be a bounded Lipschitz domain, `n = dim (ℝ × E)`, `n ≤ p < ∞` and
`α ∈ W^{1,p}(Ω)`. Then multiplication `u ↦ u α` is a compact operator `W^{1,q}(Ω) → L^q(Ω)` for
every `q ≥ 1`, including `q > p`: `α` lies in `L^s(Ω)` for every finite `s`. -/
theorem W1p.exists_isCompactOperator_value_smul_of_w1p_of_isLipschitzDomainWith
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]
    (hnp : (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0) ≤ p) (α : W1p volume Ω p) :
    ∃ M : W1p volume Ω q →L[ℝ] Lp ℝ q (volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))),
      (∀ u, M u =ᵐ[volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))]
        fun x => W1p.value u x • W1p.value α x) ∧ IsCompactOperator M := by
  have hps : (p : ℝ≥0∞)⁻¹ <
      ((max ((finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0) + 1) q : ℝ≥0) : ℝ≥0∞)⁻¹ +
        (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0∞)⁻¹ := by
    calc (p : ℝ≥0∞)⁻¹ ≤ (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0∞)⁻¹ := by
          gcongr
          exact_mod_cast hnp
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
`q`.** Let `Ω ⊆ ℝ × E` be a bounded Lipschitz domain, `n = dim (ℝ × E)`, `1 ≤ p < ∞` with
`n ≤ (m + 1) p`, and `α ∈ W^{m+1,p}(Ω)`. Then multiplication `u ↦ u α` is a compact operator
`W^{1,q}(Ω) → L^q(Ω)` for every `q ≥ 1`: `α` lies in `W^{1,(m+1)p}(Ω)`, and
`TauCeti.W1p.exists_isCompactOperator_value_smul_of_w1p_of_isLipschitzDomainWith` applies. -/
theorem W1p.exists_isCompactOperator_value_smul_of_wkp_of_isLipschitzDomainWith
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] (m : ℕ)
    (hnp : (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0) ≤ (m + 1) * p)
    (α : Wkp volume Ω p (m + 1)) :
    ∃ M : W1p volume Ω q →L[ℝ] Lp ℝ q (volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))),
      (∀ u, M u =ᵐ[volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))]
        fun x => W1p.value u x • Wkp.value (m + 1) α x) ∧ IsCompactOperator M := by
  have hp : (1 : ℝ≥0) ≤ p := by exact_mod_cast (Fact.out : (1 : ℝ≥0∞) ≤ p)
  have hpr : p ≤ (m + 1) * p := le_mul_of_one_le_left zero_le le_add_self
  have : Fact (1 ≤ (((m + 1) * p : ℝ≥0) : ℝ≥0∞)) := ⟨by exact_mod_cast hp.trans hpr⟩
  have hn : (0 : ℝ≥0) < finrank ℝ (WithLp 2 (ℝ × E)) := by exact_mod_cast finrank_pos
  -- `1/p - 1/((m+1)p) = m/((m+1)p) ≤ m/n`.
  have h₁ : (p : ℝ≥0∞)⁻¹ ≤ (((m + 1) * p : ℝ≥0) : ℝ≥0∞)⁻¹ +
      m * (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0∞)⁻¹ := by
    have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
    have hr0 : (m + 1) * p ≠ 0 := mul_ne_zero (by positivity) hp0
    have hnr : ((m + 1) * p)⁻¹ ≤ ((finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0))⁻¹ :=
      inv_anti₀ hn hnp
    rw [← ENNReal.coe_natCast (finrank ℝ (WithLp 2 (ℝ × E))), ← ENNReal.coe_natCast m,
      ← ENNReal.coe_inv hp0, ← ENNReal.coe_inv hr0, ← ENNReal.coe_inv hn.ne', ← ENNReal.coe_mul,
      ← ENNReal.coe_add, ENNReal.coe_le_coe]
    calc p⁻¹ = ((m + 1) * p)⁻¹ + m * ((m + 1) * p)⁻¹ := by
          field_simp
          ring
      _ ≤ _ := by gcongr
  obtain ⟨T, hT⟩ := Wkp.exists_w1pEmbeddingL_of_isLipschitzDomainWith m ENNReal.coe_ne_top h₁
    (ENNReal.inv_le_inv.2 (ENNReal.coe_le_coe.2 hpr)) hΩ hb
  obtain ⟨M, hM, hMc⟩ :=
    W1p.exists_isCompactOperator_value_smul_of_w1p_of_isLipschitzDomainWith (q := q) hΩ hb hnp
      (T α)
  refine ⟨M, fun u => ?_, hMc⟩
  filter_upwards [hM u, hT α] with x h₁ h₂
  rw [h₁, h₂]

end LipschitzDomain

end TauCeti

end
