/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.LipschitzDomain.Morrey
public import TauCeti.Analysis.Sobolev.LipschitzDomain.Wkp.Embedding

/-!
# Higher-order Morrey embeddings on bounded Lipschitz domains

Let `Ω ⊆ ℝ × E` be a bounded Lipschitz domain of dimension `n`, let `1 ≤ p < ∞` and let `k ≥ 1`
with `n < k p`. Every `u ∈ W^{k,p}(Ω)` has a representative which extends continuously to the
closure of `Ω` and is Hölder there, and the resulting map `W^{k,p}(Ω) → C^{0,γ}(closure Ω)` is a
bounded linear map. In particular members of `W^{k,p}(Ω)` with `n < k p` have continuous
representatives up to the boundary.

The proof lowers the order one step at a time with the Sobolev embedding
`W^{j+1,r}(Ω) → W^{j,s}(Ω)`, valid whenever `1/r ≤ 1/s + 1/n` with `s < ∞`, until it reaches
`W^{1,q}(Ω)` with `n < q < ∞`, and then applies Morrey's embedding
`TauCeti.W1p.exists_morreyEmbeddingL_of_isLipschitzDomainWith`. When `1/r < 1/s + 1/n` the step
uses the subcritical estimate
`TauCeti.W1p.exists_eLpNorm_value_le_of_subcritical_gain_of_isLipschitzDomainWith`, which also
covers `r ≥ n`, where the first-order Sobolev embedding has no finite target.

* If `k p < n + p` and `(k - 1) p < n`, the exponents `1/q = 1/p - (k - 1)/n` of the exact Sobolev
  chain stay positive and the Hölder exponent is the sharp `1 - n/q = k - n/p`.
* In general, the chain with equal steps `1/(k p)` reaches `q = k p` and gives the exponent
  `1 - n/(k p)`.

Composed with the compact inclusion of Hölder spaces, the embedding into `C^{0,β}(closure Ω)` is a
compact operator for every small enough `β > 0`.

## Main declarations

* `TauCeti.Wkp.exists_morreyEmbeddingL_of_isLipschitzDomainWith`: the embedding
  `W^{k+1,p}(Ω) →L[ℝ] C^{0,1-n/q}(closure Ω)` for `1/q + k/n = 1/p` and `n < q < ∞`.
* `TauCeti.Wkp.exists_holderEmbeddingL_of_isLipschitzDomainWith`: for `n < k p` a Hölder
  embedding `W^{k,p}(Ω) →L[ℝ] C^{0,γ}(closure Ω)` with some `γ > 0`.
* `TauCeti.Wkp.exists_isCompactOperator_holder_of_isLipschitzDomainWith`: the embedding into
  `C^{0,β}(closure Ω)` is compact for every `β` below that `γ`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.6.3, Theorem 6 (ii).
* R. A. Adams, J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., Theorem 4.12, Part II, and
  Theorem 6.3, Part IV.
-/

public section

noncomputable section

open Bornology MeasureTheory Module Set TopologicalSpace
open scoped ENNReal NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {Ω : Opens (WithLp 2 (ℝ × E))} {L : ℝ≥0} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Iteration of the first-order embedding with steps `t ≤ 1/n` down to `W^{1,q}(Ω)`, where
`1/q + k t = 1/p`. Each step `W^{1,p}(Ω) → L^r(Ω)` with `1/r + t = 1/p` is the subcritical
estimate when `t < 1/n` and the Sobolev embedding when `t = 1/n`. -/
private theorem exists_lipschitzWkpW1pEmbedding
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) {t : ℝ≥0∞}
    (ht : t ≤ (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0∞)⁻¹) :
    ∀ (k : ℕ) {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)], q ≠ ∞ → q⁻¹ + k * t = p⁻¹ →
      ∃ T : Wkp volume Ω p (k + 1) →L[ℝ] W1p volume Ω q,
        ∀ u, W1p.value (T u) =ᵐ[volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))]
          Wkp.value (k + 1) u
  | 0, p, q, _, _, _, hexp => by
    obtain rfl : q = p := by simpa using hexp
    exact ⟨Wkp.firstOrderL 0, fun u ↦ by rw [Wkp.firstOrderL_apply, Wkp.value_firstOrder]⟩
  | k + 1, p, q, _, _, hq, hexp => by
    set r : ℝ≥0∞ := (q⁻¹ + k * t)⁻¹
    have hrinv : r⁻¹ = q⁻¹ + k * t := inv_inv _
    have hrexp : r⁻¹ + t = p⁻¹ := by
      rw [hrinv, ← hexp]
      push_cast
      ring
    have hr : r ≠ ∞ := by
      rw [← ENNReal.inv_ne_zero, hrinv]
      exact (add_pos_of_pos_of_nonneg (ENNReal.inv_pos.2 hq) zero_le).ne'
    have : Fact (1 ≤ r) := ⟨one_le_of_inv_add_eq_inv hrexp⟩
    have hle : p⁻¹ ≤ r⁻¹ + (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0∞)⁻¹ := by
      rw [← hrexp]
      gcongr
    obtain ⟨S, hS⟩ : ∃ S : W1p volume Ω p →L[ℝ]
        Lp ℝ r (volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))),
        ∀ u, S u =ᵐ[volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))] W1p.value u := by
      rcases hle.lt_or_eq with hlt | heq
      · exact W1p.exists_lpEmbeddingL_of_eLpNorm_value_le subset_rfl
          (W1p.exists_eLpNorm_value_le_of_subcritical_gain_of_isLipschitzDomainWith hr hlt hΩ hb)
      · exact W1p.exists_sobolevEmbeddingL_of_isLipschitzDomainWith hr heq.symm hΩ hb
    obtain ⟨S', hS'⟩ := Wkp.exists_sobolevEmbeddingL_of_ae_eq S hS (k + 1)
    obtain ⟨T, hT⟩ := exists_lipschitzWkpW1pEmbedding hΩ hb ht k (p := r) (q := q) hq
      hrinv.symm
    exact ⟨T.comp S', fun u ↦ (hT (S' u)).trans (hS' u)⟩

/-- The ladder `exists_lipschitzWkpW1pEmbedding` followed by Morrey's embedding of
`W^{1,q}(Ω)`, `n < q < ∞`, into `C^{0,1-n/q}(closure Ω)`. -/
private theorem exists_lipschitzWkpHolderEmbedding
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) {t : ℝ≥0∞}
    (ht : t ≤ (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0∞)⁻¹) (k : ℕ) {q : ℝ≥0}
    [Fact (1 ≤ (q : ℝ≥0∞))] (hq : (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0) < q)
    (hexp : (q : ℝ≥0∞)⁻¹ + k * t = p⁻¹) :
    ∃ T : Wkp volume Ω p (k + 1) →L[ℝ] HolderSpace (1 - finrank ℝ (WithLp 2 (ℝ × E)) / q)
        (closure (Ω : Set (WithLp 2 (ℝ × E)))) ℝ,
      ∀ u, ∀ᵐ x ∂volume, ∀ hx : x ∈ Ω, T u ⟨x, subset_closure hx⟩ = Wkp.value (k + 1) u x := by
  obtain ⟨T₁, hT₁⟩ := exists_lipschitzWkpW1pEmbedding hΩ hb ht k ENNReal.coe_ne_top hexp
  obtain ⟨M, hM⟩ := W1p.exists_morreyEmbeddingL_of_isLipschitzDomainWith hq hΩ hb
  refine ⟨M.comp T₁, fun u ↦ ?_⟩
  filter_upwards [hM (T₁ u), (ae_restrict_iff' Ω.isOpen.measurableSet).1 (hT₁ u)]
    with x h₁ h₂ hx
  rw [ContinuousLinearMap.comp_apply, h₁ hx, h₂ hx]

/-- **Higher-order Morrey embedding on bounded Lipschitz domains.** If `Ω ⊆ ℝ × E` is a bounded
Lipschitz domain of dimension `n`, `1 ≤ p`, and `1/q + k/n = 1/p` with `n < q < ∞`, then every
`u ∈ W^{k+1,p}(Ω)` agrees almost everywhere on `Ω` with a function on `closure Ω` which is Hölder
of exponent `1 - n/q = k + 1 - n/p`, and this representative depends linearly and boundedly on
`u`. The hypotheses say that `k p < n < (k + 1) p` (or `n < p` for `k = 0`), and the exponent is
the sharp one. By `IsOpen.ext_closure_of_ae_eq` the representative is unique. -/
theorem Wkp.exists_morreyEmbeddingL_of_isLipschitzDomainWith (k : ℕ) {q : ℝ≥0}
    (hq : (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0) < q)
    (hexp : (q : ℝ≥0∞)⁻¹ + k * (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0∞)⁻¹ = p⁻¹)
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) :
    ∃ T : Wkp volume Ω p (k + 1) →L[ℝ] HolderSpace (1 - finrank ℝ (WithLp 2 (ℝ × E)) / q)
        (closure (Ω : Set (WithLp 2 (ℝ × E)))) ℝ,
      ∀ u, ∀ᵐ x ∂volume, ∀ hx : x ∈ Ω, T u ⟨x, subset_closure hx⟩ = Wkp.value (k + 1) u x := by
  have : Fact (1 ≤ (q : ℝ≥0∞)) := ⟨one_le_of_inv_add_eq_inv hexp⟩
  exact exists_lipschitzWkpHolderEmbedding hΩ hb le_rfl k hq hexp

/-- **Hölder embedding of `W^{k,p}` with `n < k p` on bounded Lipschitz domains.** If
`Ω ⊆ ℝ × E` is a bounded Lipschitz domain of dimension `n`, `1 ≤ p < ∞` and `n < k p`, then
there is `γ > 0` such that every `u ∈ W^{k,p}(Ω)` agrees almost everywhere on `Ω` with a function
on `closure Ω` which is Hölder of exponent `γ`, depending linearly and boundedly on `u`. For the
sharp exponent see `TauCeti.Wkp.exists_morreyEmbeddingL_of_isLipschitzDomainWith`. -/
theorem Wkp.exists_holderEmbeddingL_of_isLipschitzDomainWith {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]
    {k : ℕ} (hkp : (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0) < k * p)
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) :
    ∃ γ : ℝ≥0, 0 < γ ∧ ∃ T : Wkp volume Ω p k →L[ℝ]
        HolderSpace γ (closure (Ω : Set (WithLp 2 (ℝ × E)))) ℝ,
      ∀ u, ∀ᵐ x ∂volume, ∀ hx : x ∈ Ω, T u ⟨x, subset_closure hx⟩ = Wkp.value k u x := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := Nat.exists_eq_succ_of_ne_zero (by
    rintro rfl
    simp at hkp)
  -- The ladder with equal steps `1/(k p)` ends at `q = k p`, giving `γ = 1 - n/(k p)`.
  have hq1 : (1 : ℝ≥0∞) ≤ (((j + 1 : ℕ) * p : ℝ≥0) : ℝ≥0∞) := by
    push_cast
    exact one_le_mul_of_one_le_of_one_le (by exact_mod_cast Nat.le_add_left 1 j) Fact.out
  have : Fact (1 ≤ (((j + 1 : ℕ) * p : ℝ≥0) : ℝ≥0∞)) := ⟨hq1⟩
  have hp0 : (p : ℝ≥0∞) ≠ 0 := (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
  have hq : (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0) < (j + 1 : ℕ) * p := by exact_mod_cast hkp
  have hγ : 0 < 1 - (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0) / ((j + 1 : ℕ) * p) :=
    tsub_pos_of_lt ((div_lt_one (zero_le.trans_lt hq)).2 hq)
  refine ⟨_, hγ, exists_lipschitzWkpHolderEmbedding hΩ hb
    (t := (((j + 1 : ℕ) * p : ℝ≥0) : ℝ≥0∞)⁻¹) ?_ j hq ?_⟩
  · rw [ENNReal.inv_le_inv]
    exact_mod_cast hkp.le
  · push_cast
    rw [ENNReal.mul_inv (Or.inl (by positivity)) (Or.inl (by simp)), ← one_add_mul,
      ← mul_assoc, add_comm (1 : ℝ≥0∞), ENNReal.mul_inv_cancel (by positivity) (by simp),
      one_mul]

/-- **Hölder compactness of `W^{k,p}` with `n < k p` on bounded Lipschitz domains.** Under the
hypotheses of `TauCeti.Wkp.exists_holderEmbeddingL_of_isLipschitzDomainWith`, there is `γ > 0`
such that for every `β < γ` the Hölder representative gives a compact operator
`W^{k,p}(Ω) → C^{0,β}(closure Ω)`. -/
theorem Wkp.exists_isCompactOperator_holder_of_isLipschitzDomainWith {p : ℝ≥0}
    [Fact (1 ≤ (p : ℝ≥0∞))] {k : ℕ} (hkp : (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0) < k * p)
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) :
    ∃ γ : ℝ≥0, 0 < γ ∧ ∀ β < γ, ∃ T : Wkp volume Ω p k →L[ℝ]
        HolderSpace β (closure (Ω : Set (WithLp 2 (ℝ × E)))) ℝ,
      IsCompactOperator T ∧
        ∀ u, ∀ᵐ x ∂volume, ∀ hx : x ∈ Ω, T u ⟨x, subset_closure hx⟩ = Wkp.value k u x := by
  have : CompactSpace (closure (Ω : Set (WithLp 2 (ℝ × E)))) :=
    isCompact_iff_compactSpace.1 hb.isCompact_closure
  obtain ⟨γ, hγ, T, hT⟩ := Wkp.exists_holderEmbeddingL_of_isLipschitzDomainWith hkp hΩ hb
  refine ⟨γ, hγ, fun β hβ ↦ ⟨(HolderSpace.inclusionL hβ.le).comp T,
    (HolderSpace.isCompactOperator_inclusionL hβ).comp_clm T, fun u ↦ ?_⟩⟩
  filter_upwards [hT u] with x hx hxΩ
  rw [ContinuousLinearMap.comp_apply, HolderSpace.inclusionL_apply, hx hxΩ]

end TauCeti

end
