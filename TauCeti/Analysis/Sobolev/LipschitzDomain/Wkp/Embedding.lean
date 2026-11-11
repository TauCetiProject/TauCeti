/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.LipschitzDomain.SobolevEmbedding
public import TauCeti.Analysis.Sobolev.Wkp.Embedding
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# Higher-order Sobolev embeddings on bounded Lipschitz domains

Let `Ω ⊆ ℝ × E` be a bounded Lipschitz domain of dimension `n`, let `1 ≤ p` and let `p⋆` be the
Sobolev conjugate, `1/p⋆ = 1/p - 1/n`, with `p⋆ < ∞`, that is `p < n`. Every derivative of order
at most `k` of a function in `W^{k+1,p}(Ω)` lies in `W^{1,p}(Ω)`, so by the first-order embedding
`TauCeti.W1p.exists_sobolevEmbeddingL_of_isLipschitzDomainWith` it lies in `L^{p⋆}(Ω)`. Keeping
all the weak derivatives, the inclusion is therefore a continuous linear map
`W^{k+1,p}(Ω) → W^{k,p⋆}(Ω)`. Iterating, `W^{k,p}(Ω) → L^q(Ω)` for `1/q = 1/p - k/n > 0`.
With the subcritical first-order estimate for smaller steps, the iteration more generally gives
`W^{k+1,p}(Ω) → W^{1,q}(Ω)` whenever `1/p - k/n ≤ 1/q ≤ 1/p` and `q < ∞`, also when `k p ≥ n`.

The passage from the first-order embedding to higher order holds on any open set and is
`TauCeti.Wkp.exists_sobolevEmbeddingL_succ_of_ae_eq`; this file supplies the first-order embedding
on bounded Lipschitz domains and iterates the exponent bookkeeping.

## Main declarations

* `TauCeti.Wkp.exists_sobolevEmbeddingL_of_isLipschitzDomainWith`: the embedding
  `W^{k+1,p}(Ω) →L[ℝ] W^{k,p⋆}(Ω)`, which preserves the value.
* `TauCeti.Wkp.exists_sobolevEmbeddingL_succ_of_isLipschitzDomainWith`: at positive target
  order, the embedding `W^{k+2,p}(Ω) →L[ℝ] W^{k+1,p⋆}(Ω)` also preserves the highest weak
  derivative.
* `TauCeti.Wkp.exists_w1pEmbeddingL_of_isLipschitzDomainWith`: the embedding
  `W^{k+1,p}(Ω) →L[ℝ] W^{1,q}(Ω)` for `1/p - k/n ≤ 1/q ≤ 1/p`, `q < ∞`.
* `TauCeti.Wkp.exists_lpEmbeddingL_of_isLipschitzDomainWith`: the embedding
  `W^{k,p}(Ω) →L[ℝ] L^q(Ω)` for `1/q + k/n = 1/p`, `q < ∞`.
* `TauCeti.Wkp.exists_eLpNorm_value_le_of_isLipschitzDomainWith`: the estimate
  `‖u‖_{L^r(Ω)} ≤ C ‖u‖_{W^{k,p}(Ω)}` for `r ≤ q`.
* `TauCeti.Wkp.memLp_value_of_isLipschitzDomainWith`: every `u ∈ W^{k,p}(Ω)` lies in `L^r(Ω)`
  for `r ≤ q`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.6.3, Theorem 6 (i).
* R. A. Adams, J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., Theorem 4.12, Part I, Case B.
-/

public section

noncomputable section

open Bornology MeasureTheory Module Set TopologicalSpace
open scoped ENNReal NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {Ω : Opens (WithLp 2 (ℝ × E))} {L : ℝ≥0} {p pstar : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Higher-order Sobolev embedding on bounded Lipschitz domains.** If `Ω ⊆ ℝ × E` is a bounded
Lipschitz domain of dimension `n`, `1 ≤ p` and `1/p⋆ + 1/n = 1/p` with `p⋆ < ∞`, then for every
`k` inclusion is a continuous linear map `W^{k+2,p}(Ω) → W^{k+1,p⋆}(Ω)`. It preserves the value
and the highest weak derivative of the target, the order-`k + 1` derivative; by uniqueness of weak
derivatives it therefore preserves every weak derivative of order at most `k + 1`. -/
theorem Wkp.exists_sobolevEmbeddingL_succ_of_isLipschitzDomainWith (hpstar : pstar ≠ ∞)
    (hexp : pstar⁻¹ + (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0∞)⁻¹ = p⁻¹)
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) (k : ℕ) :
    letI := Fact.mk (one_le_of_inv_add_eq_inv hexp)
    ∃ T : Wkp volume Ω p (k + 2) →L[ℝ] Wkp volume Ω pstar (k + 1),
      ∀ u, Wkp.value (k + 1) (T u) =ᵐ[volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))]
          Wkp.value (k + 2) u ∧
        Wkp.iteratedGradient k (T u) =ᵐ[volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))]
          Wkp.iteratedGradient k (Wkp.lowerOrder (k + 1) u) := by
  let _ := Fact.mk (one_le_of_inv_add_eq_inv hexp)
  obtain ⟨S, hS⟩ := W1p.exists_sobolevEmbeddingL_of_isLipschitzDomainWith hpstar hexp hΩ hb
  exact Wkp.exists_sobolevEmbeddingL_succ_of_ae_eq S hS k

/-- **Higher-order Sobolev embedding on bounded Lipschitz domains.** If `Ω ⊆ ℝ × E` is a bounded
Lipschitz domain of dimension `n`, `1 ≤ p` and `1/p⋆ + 1/n = 1/p` with `p⋆ < ∞`, then for every
`k` inclusion is a continuous linear map `W^{k+1,p}(Ω) → W^{k,p⋆}(Ω)`, preserving the value.
At positive target order the highest derivative is preserved as well
(`TauCeti.Wkp.exists_sobolevEmbeddingL_succ_of_isLipschitzDomainWith`). -/
theorem Wkp.exists_sobolevEmbeddingL_of_isLipschitzDomainWith (hpstar : pstar ≠ ∞)
    (hexp : pstar⁻¹ + (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0∞)⁻¹ = p⁻¹)
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) (k : ℕ) :
    letI := Fact.mk (one_le_of_inv_add_eq_inv hexp)
    ∃ T : Wkp volume Ω p (k + 1) →L[ℝ] Wkp volume Ω pstar k,
      ∀ u, Wkp.value k (T u) =ᵐ[volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))]
        Wkp.value (k + 1) u := by
  let _ := Fact.mk (one_le_of_inv_add_eq_inv hexp)
  obtain ⟨S, hS⟩ := W1p.exists_sobolevEmbeddingL_of_isLipschitzDomainWith hpstar hexp hΩ hb
  exact Wkp.exists_sobolevEmbeddingL_of_ae_eq S hS k

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
    obtain ⟨r, hr, hrinv⟩ := exists_inv_eq_inv_add_of_ne_top hq (k * t)
    have hrexp : r⁻¹ + t = p⁻¹ := by
      rw [hrinv, ← hexp]
      push_cast
      ring
    have : Fact (1 ≤ r) := ⟨one_le_of_inv_add_eq_inv hrexp⟩
    have hle : p⁻¹ ≤ r⁻¹ + (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0∞)⁻¹ := by
      rw [← hrexp]
      gcongr
    obtain ⟨S, hS⟩ : ∃ S : Wkp volume Ω p (k + 2) →L[ℝ] Wkp volume Ω r (k + 1),
        ∀ u, Wkp.value (k + 1) (S u) =ᵐ[volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))]
          Wkp.value (k + 2) u := by
      rcases hle.lt_or_eq with hlt | heq
      · obtain ⟨S₁, hS₁⟩ := W1p.exists_lpEmbeddingL_of_eLpNorm_value_le subset_rfl
          (W1p.exists_eLpNorm_value_le_of_subcritical_gain_of_isLipschitzDomainWith hr hlt hΩ hb)
        exact Wkp.exists_sobolevEmbeddingL_of_ae_eq S₁ hS₁ (k + 1)
      · exact Wkp.exists_sobolevEmbeddingL_of_isLipschitzDomainWith hr heq.symm hΩ hb (k + 1)
    obtain ⟨T, hT⟩ := exists_lipschitzWkpW1pEmbedding hΩ hb ht k (p := r) (q := q) hq
      hrinv.symm
    exact ⟨T.comp S, fun u ↦ (hT (S u)).trans (hS u)⟩

/-- **Higher-order Sobolev embedding into `W^{1,q}` on bounded Lipschitz domains.** If
`Ω ⊆ ℝ × E` is a bounded Lipschitz domain of dimension `n`, `1 ≤ p` and
`1/p - k/n ≤ 1/q ≤ 1/p` with `q < ∞`, then inclusion is a continuous linear map
`W^{k+1,p}(Ω) → W^{1,q}(Ω)`, preserving the value. At `1/q = 1/p - k/n` this is the iterated exact
Sobolev embedding; the other exponents also reach targets with `k p ≥ n`. -/
theorem Wkp.exists_w1pEmbeddingL_of_isLipschitzDomainWith (k : ℕ) {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (hq : q ≠ ∞) (hq₁ : p⁻¹ ≤ q⁻¹ + k * (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0∞)⁻¹)
    (hq₂ : q⁻¹ ≤ p⁻¹)
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) :
    ∃ T : Wkp volume Ω p (k + 1) →L[ℝ] W1p volume Ω q,
      ∀ u, W1p.value (T u) =ᵐ[volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))]
        Wkp.value (k + 1) u := by
  rcases eq_or_ne k 0 with rfl | hk
  · refine exists_lipschitzWkpW1pEmbedding hΩ hb zero_le 0 hq ?_
    simpa using hq₂.antisymm (by simpa using hq₁)
  -- The ladder with equal steps `t = (1/p - 1/q)/k ≤ 1/n`.
  refine exists_lipschitzWkpW1pEmbedding hΩ hb (t := (p⁻¹ - q⁻¹) / k) ?_ k hq ?_
  · refine ENNReal.div_le_of_le_mul ?_
    rwa [tsub_le_iff_left, mul_comm]
  · rw [ENNReal.mul_div_cancel (Nat.cast_ne_zero.2 hk) (ENNReal.natCast_ne_top k),
      add_tsub_cancel_of_le hq₂]

/-- **Higher-order Sobolev embedding into Lebesgue spaces on bounded Lipschitz domains.** If
`Ω ⊆ ℝ × E` is a bounded Lipschitz domain of dimension `n`, `1 ≤ p`, and
`1/q + k/n = 1/p` with `q < ∞`, that is `kp < n`, then inclusion is a continuous linear map
`W^{k,p}(Ω) → L^q(Ω)`. -/
theorem Wkp.exists_lpEmbeddingL_of_isLipschitzDomainWith (k : ℕ) {q : ℝ≥0∞} (hq : q ≠ ∞)
    (hexp : q⁻¹ + k * (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0∞)⁻¹ = p⁻¹)
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) :
    letI := Fact.mk (one_le_of_inv_add_eq_inv hexp)
    ∃ T : Wkp volume Ω p k →L[ℝ] Lp ℝ q (volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))),
      ∀ u, T u =ᵐ[volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))] Wkp.value k u := by
  let _ := Fact.mk (one_le_of_inv_add_eq_inv hexp)
  rcases k with _ | k
  · obtain rfl : q = p := by simpa using hexp
    exact ⟨ContinuousLinearMap.id ℝ _, fun u ↦ by simp⟩
  -- The ladder with steps `1/n` down to `W^{1,r}`, `1/r = 1/q + 1/n`, then the first-order
  -- Sobolev embedding `W^{1,r}(Ω) → L^q(Ω)`.
  set n : ℝ≥0∞ := (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0∞)
  obtain ⟨r, hr, hrinv⟩ := exists_inv_eq_inv_add_of_ne_top hq n⁻¹
  have hrexp : r⁻¹ + k * n⁻¹ = p⁻¹ := by
    rw [hrinv, ← hexp]
    push_cast
    ring
  let _ : Fact (1 ≤ r) := ⟨one_le_of_inv_add_eq_inv hrexp⟩
  obtain ⟨T, hT⟩ := Wkp.exists_w1pEmbeddingL_of_isLipschitzDomainWith k hr hrexp.ge
    (le_self_add.trans_eq hrexp) hΩ hb
  obtain ⟨S, hS⟩ := W1p.exists_sobolevEmbeddingL_of_isLipschitzDomainWith hq hrinv.symm hΩ hb
  exact ⟨S.comp T, fun u ↦ (hS (T u)).trans (hT u)⟩

/-- **The higher-order Sobolev inequality on bounded Lipschitz domains.** If `Ω ⊆ ℝ × E` is a
bounded Lipschitz domain of dimension `n`, `1 ≤ p`, and `1/q + k/n = 1/p` with `q < ∞`, then for
every `r ≤ q` there is a constant `C` with `‖u‖_{L^r(Ω)} ≤ C ‖u‖_{W^{k,p}(Ω)}`. -/
theorem Wkp.exists_eLpNorm_value_le_of_isLipschitzDomainWith (k : ℕ) {q : ℝ≥0∞} (hq : q ≠ ∞)
    (hexp : q⁻¹ + k * (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0∞)⁻¹ = p⁻¹)
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) {r : ℝ≥0∞} (hr : r ≤ q) :
    ∃ C : ℝ≥0, ∀ u : Wkp volume Ω p k,
      eLpNorm (Wkp.value k u) r (volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))) ≤ C * ‖u‖ₑ := by
  let _ := Fact.mk (one_le_of_inv_add_eq_inv hexp)
  obtain ⟨T, hT⟩ := Wkp.exists_lpEmbeddingL_of_isLipschitzDomainWith k hq hexp hΩ hb
  have hμ : volume.restrict (Ω : Set (WithLp 2 (ℝ × E))) univ ≠ ∞ := by
    rw [Measure.restrict_apply_univ]
    exact hb.measure_lt_top.ne
  exact exists_eLpNorm_le_mul_enorm_of_ae_eq hμ hr T hT

/-- **Integrability on bounded Lipschitz domains at higher order.** If `Ω ⊆ ℝ × E` is a bounded
Lipschitz domain of dimension `n`, every `u ∈ W^{k,p}(Ω)` lies in `L^r(Ω)` for every `r ≤ q`,
where `1/q + k/n = 1/p` and `q < ∞`. -/
theorem Wkp.memLp_value_of_isLipschitzDomainWith (k : ℕ) {q : ℝ≥0∞} (hq : q ≠ ∞)
    (hexp : q⁻¹ + k * (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0∞)⁻¹ = p⁻¹)
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) {r : ℝ≥0∞} (hr : r ≤ q)
    (u : Wkp volume Ω p k) :
    MemLp (Wkp.value k u) r (volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))) := by
  obtain ⟨C, hC⟩ := Wkp.exists_eLpNorm_value_le_of_isLipschitzDomainWith k hq hexp hΩ hb hr
  have hfin : C * ‖u‖ₑ < ∞ := by finiteness
  exact (hC u).trans_lt hfin

end TauCeti

end
