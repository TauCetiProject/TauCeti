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

The proof lowers the order to `W^{1,q}(Ω)` with `n < q < ∞` with the embedding
`TauCeti.Wkp.exists_w1pEmbeddingL_of_isLipschitzDomainWith`, which holds whenever
`1/p - k/n ≤ 1/q ≤ 1/p` and so also covers `k p ≥ n`, where the first-order Sobolev embedding
has no finite target, and then applies Morrey's embedding
`TauCeti.W1p.exists_morreyEmbeddingL_of_isLipschitzDomainWith`. The resulting Hölder exponent is
`1 - n/q`.

* If `k p < n < (k + 1) p`, the choice `1/q = 1/p - k/n` gives the sharp exponent
  `1 - n/q = k + 1 - n/p` for `W^{k+1,p}(Ω)`.
* If `k p ≥ n`, every `q > n` with `q ≥ p` is allowed and every exponent below `1` is reached.
* For `W^{k,p}(Ω)` with `n < k p`, the choice `q = k p` gives the exponent `1 - n/(k p)`.

Composed with the compact inclusion of Hölder spaces, the embedding into `C^{0,β}(closure Ω)` is a
compact operator for every `β` below the respective exponent.

## Main declarations

* `TauCeti.Wkp.exists_morreyEmbeddingL_of_isLipschitzDomainWith`: the embedding
  `W^{k+1,p}(Ω) →L[ℝ] C^{0,1-n/q}(closure Ω)` for `1/p - k/n ≤ 1/q ≤ 1/p` and `n < q < ∞`.
* `TauCeti.Wkp.exists_isCompactOperator_morrey_of_isLipschitzDomainWith`: the embedding into
  `C^{0,β}(closure Ω)` is compact for every `β < 1 - n/q`.
* `TauCeti.Wkp.exists_holderEmbeddingL_of_isLipschitzDomainWith`: for `n < k p` the Hölder
  embedding `W^{k,p}(Ω) →L[ℝ] C^{0,1-n/(k p)}(closure Ω)`.
* `TauCeti.Wkp.exists_isCompactOperator_holder_of_isLipschitzDomainWith`: the embedding into
  `C^{0,β}(closure Ω)` is compact for every `β < 1 - n/(k p)`.

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

/-- **Higher-order Morrey embedding on bounded Lipschitz domains.** If `Ω ⊆ ℝ × E` is a bounded
Lipschitz domain of dimension `n`, `1 ≤ p`, and `1/p - k/n ≤ 1/q ≤ 1/p` with `n < q < ∞`, then
every `u ∈ W^{k+1,p}(Ω)` agrees almost everywhere on `Ω` with a function on `closure Ω` which is
Hölder of exponent `1 - n/q`, and this representative depends linearly and boundedly on `u`. At
`1/q = 1/p - k/n`, possible when `k p < n < (k + 1) p` (or `n < p` for `k = 0`), the exponent is
the sharp `1 - n/q = k + 1 - n/p`; when `k p ≥ n` every exponent below `1` is reached. By
`IsOpen.ext_closure_of_ae_eq` the representative is unique. -/
theorem Wkp.exists_morreyEmbeddingL_of_isLipschitzDomainWith (k : ℕ) {q : ℝ≥0}
    (hq : (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0) < q)
    (hq₁ : p⁻¹ ≤ (q : ℝ≥0∞)⁻¹ + k * (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0∞)⁻¹)
    (hq₂ : (q : ℝ≥0∞)⁻¹ ≤ p⁻¹)
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) :
    ∃ T : Wkp volume Ω p (k + 1) →L[ℝ] HolderSpace (1 - finrank ℝ (WithLp 2 (ℝ × E)) / q)
        (closure (Ω : Set (WithLp 2 (ℝ × E)))) ℝ,
      ∀ u, ∀ᵐ x ∂volume, ∀ hx : x ∈ Ω, T u ⟨x, subset_closure hx⟩ = Wkp.value (k + 1) u x := by
  have : Fact (1 ≤ (q : ℝ≥0∞)) :=
    ⟨ENNReal.inv_le_one.1 (hq₂.trans (ENNReal.inv_le_one.2 Fact.out))⟩
  obtain ⟨T₁, hT₁⟩ :=
    Wkp.exists_w1pEmbeddingL_of_isLipschitzDomainWith k ENNReal.coe_ne_top hq₁ hq₂ hΩ hb
  obtain ⟨M, hM⟩ := W1p.exists_morreyEmbeddingL_of_isLipschitzDomainWith hq hΩ hb
  refine ⟨M.comp T₁, fun u ↦ ?_⟩
  filter_upwards [hM (T₁ u), (ae_restrict_iff' Ω.isOpen.measurableSet).1 (hT₁ u)]
    with x h₁ h₂ hx
  rw [ContinuousLinearMap.comp_apply, h₁ hx, h₂ hx]

/-- **Higher-order Morrey compactness on bounded Lipschitz domains.** Under the hypotheses of
`TauCeti.Wkp.exists_morreyEmbeddingL_of_isLipschitzDomainWith`, for every `β < 1 - n/q` the
Hölder representative gives a compact operator `W^{k+1,p}(Ω) → C^{0,β}(closure Ω)`. -/
theorem Wkp.exists_isCompactOperator_morrey_of_isLipschitzDomainWith (k : ℕ) {q : ℝ≥0}
    (hq : (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0) < q)
    (hq₁ : p⁻¹ ≤ (q : ℝ≥0∞)⁻¹ + k * (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0∞)⁻¹)
    (hq₂ : (q : ℝ≥0∞)⁻¹ ≤ p⁻¹)
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) {β : ℝ≥0}
    (hβ : β < 1 - finrank ℝ (WithLp 2 (ℝ × E)) / q) :
    ∃ T : Wkp volume Ω p (k + 1) →L[ℝ] HolderSpace β (closure (Ω : Set (WithLp 2 (ℝ × E)))) ℝ,
      IsCompactOperator T ∧
        ∀ u, ∀ᵐ x ∂volume, ∀ hx : x ∈ Ω, T u ⟨x, subset_closure hx⟩ = Wkp.value (k + 1) u x := by
  have : Fact (1 ≤ (q : ℝ≥0∞)) :=
    ⟨ENNReal.inv_le_one.1 (hq₂.trans (ENNReal.inv_le_one.2 Fact.out))⟩
  obtain ⟨T₁, hT₁⟩ :=
    Wkp.exists_w1pEmbeddingL_of_isLipschitzDomainWith k ENNReal.coe_ne_top hq₁ hq₂ hΩ hb
  obtain ⟨K, hK, hKv⟩ := W1p.exists_isCompactOperator_holder_of_isLipschitzDomainWith hq hΩ hb hβ
  refine ⟨K.comp T₁, hK.comp_clm T₁, fun u ↦ ?_⟩
  filter_upwards [hKv (T₁ u), (ae_restrict_iff' Ω.isOpen.measurableSet).1 (hT₁ u)]
    with x h₁ h₂ hx
  rw [ContinuousLinearMap.comp_apply, h₁ hx, h₂ hx]

/-- For `n < (j + 1) p`, the exponent `q = (j + 1) p` satisfies the hypotheses
`1/p - j/n ≤ 1/q ≤ 1/p` of `TauCeti.Wkp.exists_morreyEmbeddingL_of_isLipschitzDomainWith`: the
ladder with equal steps `1/((j + 1) p)` ends there. -/
private theorem inv_le_inv_mul_add_and_inv_mul_le_inv {n j : ℕ} {p : ℝ≥0}
    (hkp : (n : ℝ≥0) < (j + 1 : ℕ) * p) :
    (p : ℝ≥0∞)⁻¹ ≤ (((j + 1 : ℕ) * p : ℝ≥0) : ℝ≥0∞)⁻¹ + j * (n : ℝ≥0∞)⁻¹ ∧
      (((j + 1 : ℕ) * p : ℝ≥0) : ℝ≥0∞)⁻¹ ≤ (p : ℝ≥0∞)⁻¹ := by
  have hkp0 : ((j + 1 : ℕ) * p : ℝ≥0) ≠ 0 := (zero_le.trans_lt hkp).ne'
  have hp0 : p ≠ 0 := right_ne_zero_of_mul hkp0
  have heq : (((j + 1 : ℕ) * p : ℝ≥0) : ℝ≥0∞)⁻¹ + j * (((j + 1 : ℕ) * p : ℝ≥0) : ℝ≥0∞)⁻¹ =
      (p : ℝ≥0∞)⁻¹ := by
    rw [← ENNReal.coe_inv hkp0, ← ENNReal.coe_inv hp0]
    norm_cast
    field_simp
    push_cast
    ring
  refine ⟨heq.symm.le.trans ?_, le_self_add.trans_eq heq⟩
  gcongr
  exact_mod_cast hkp.le

/-- **Hölder embedding of `W^{k,p}` with `n < k p` on bounded Lipschitz domains.** If
`Ω ⊆ ℝ × E` is a bounded Lipschitz domain of dimension `n`, `1 ≤ p < ∞` and `n < k p`, then
every `u ∈ W^{k,p}(Ω)` agrees almost everywhere on `Ω` with a function on `closure Ω` which is
Hölder of the positive exponent `1 - n/(k p)`, depending linearly and boundedly on `u`. This is
the case `q = k p` of `TauCeti.Wkp.exists_morreyEmbeddingL_of_isLipschitzDomainWith`, which
gives larger exponents. -/
theorem Wkp.exists_holderEmbeddingL_of_isLipschitzDomainWith {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]
    {k : ℕ} (hkp : (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0) < k * p)
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) :
    ∃ T : Wkp volume Ω p k →L[ℝ] HolderSpace (1 - finrank ℝ (WithLp 2 (ℝ × E)) / (k * p))
        (closure (Ω : Set (WithLp 2 (ℝ × E)))) ℝ,
      ∀ u, ∀ᵐ x ∂volume, ∀ hx : x ∈ Ω, T u ⟨x, subset_closure hx⟩ = Wkp.value k u x := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := Nat.exists_eq_succ_of_ne_zero (by
    rintro rfl
    simp at hkp)
  obtain ⟨hq₁, hq₂⟩ := inv_le_inv_mul_add_and_inv_mul_le_inv hkp
  exact Wkp.exists_morreyEmbeddingL_of_isLipschitzDomainWith j hkp hq₁ hq₂ hΩ hb

/-- **Hölder compactness of `W^{k,p}` with `n < k p` on bounded Lipschitz domains.** Under the
hypotheses of `TauCeti.Wkp.exists_holderEmbeddingL_of_isLipschitzDomainWith`, for every
`β < 1 - n/(k p)` the Hölder representative gives a compact operator
`W^{k,p}(Ω) → C^{0,β}(closure Ω)`. -/
theorem Wkp.exists_isCompactOperator_holder_of_isLipschitzDomainWith {p : ℝ≥0}
    [Fact (1 ≤ (p : ℝ≥0∞))] {k : ℕ} (hkp : (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0) < k * p)
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) {β : ℝ≥0}
    (hβ : β < 1 - finrank ℝ (WithLp 2 (ℝ × E)) / (k * p)) :
    ∃ T : Wkp volume Ω p k →L[ℝ] HolderSpace β (closure (Ω : Set (WithLp 2 (ℝ × E)))) ℝ,
      IsCompactOperator T ∧
        ∀ u, ∀ᵐ x ∂volume, ∀ hx : x ∈ Ω, T u ⟨x, subset_closure hx⟩ = Wkp.value k u x := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := Nat.exists_eq_succ_of_ne_zero (by
    rintro rfl
    simp at hkp)
  obtain ⟨hq₁, hq₂⟩ := inv_le_inv_mul_add_and_inv_mul_le_inv hkp
  exact Wkp.exists_isCompactOperator_morrey_of_isLipschitzDomainWith j hkp hq₁ hq₂ hΩ hb hβ

end TauCeti

end
