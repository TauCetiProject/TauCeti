/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.LipschitzDomain.GlobalExtension
public import TauCeti.Analysis.Sobolev.W1p.SobolevEmbedding

/-!
# The Sobolev embedding on bounded Lipschitz domains

For a bounded Lipschitz domain `Ω ⊆ ℝ × E` of dimension `n`, an exponent `1 ≤ p < n` and the
Sobolev conjugate `p⋆ = np/(n - p)`, so that `1/p⋆ + 1/n = 1/p`, the inclusion
`W^{1,p}(Ω) → L^{p⋆}(Ω)` is a continuous linear map, and so `‖u‖_{L^q(Ω)} ≤ C ‖u‖_{W^{1,p}(Ω)}`
for every `q ≤ p⋆`. Unlike `TauCeti.W1p0.sobolevEmbeddingL`, this concerns the whole Sobolev
space, with no vanishing boundary values; unlike the interior form
`TauCeti.W1p.exists_sobolevEmbeddingL_of_isCompact_closure`, the estimate reaches the boundary.

The boundary regularity enters only through the extension operator
`TauCeti.W1p.exists_extensionL_of_isLipschitzDomainWith`: the inclusion factors as extension to
`W^{1,p}(ℝ × E)`, the whole-space embedding `TauCeti.W1p.sobolevEmbeddingTopL`, and restriction
to `Ω`. Some regularity of `∂Ω` is genuinely needed: on a bounded domain with a sufficiently
sharp outward cusp, `W^{1,p}(Ω)` is not contained in `L^{p⋆}(Ω)`.

## Main declarations

* `TauCeti.W1p.exists_sobolevEmbeddingL_of_isLipschitzDomainWith`: the embedding
  `W^{1,p}(Ω) →L[ℝ] L^{p⋆}(Ω)`.
* `TauCeti.W1p.exists_eLpNorm_value_le_of_isLipschitzDomainWith`: the estimate
  `‖u‖_{L^q(Ω)} ≤ C ‖u‖_{W^{1,p}(Ω)}` for `q ≤ p⋆`.
* `TauCeti.W1p.memLp_value_of_isLipschitzDomainWith`: every `u ∈ W^{1,p}(Ω)` lies in `L^q(Ω)`
  for `q ≤ p⋆`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.6.1, Theorem 2.
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

/-- **The Sobolev embedding on bounded Lipschitz domains.** If `Ω ⊆ ℝ × E` is a bounded Lipschitz
domain of dimension `n`, `1 ≤ p` and `1/p⋆ + 1/n = 1/p` with `p⋆ < ∞`, then inclusion is a
continuous linear map `W^{1,p}(Ω) → L^{p⋆}(Ω)`. -/
theorem W1p.exists_sobolevEmbeddingL_of_isLipschitzDomainWith (hpstar : pstar ≠ ∞)
    (hexp : pstar⁻¹ + (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0∞)⁻¹ = p⁻¹)
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) :
    letI := Fact.mk (one_le_of_inv_add_eq_inv hexp)
    ∃ S : W1p volume Ω p →L[ℝ] Lp ℝ pstar (volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))),
      ∀ u, S u =ᵐ[volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))] W1p.value u := by
  let _ := Fact.mk (one_le_of_inv_add_eq_inv hexp)
  obtain ⟨T, hT⟩ := W1p.exists_extensionL_of_isLipschitzDomainWith (p := p) hΩ hb
  have hle : volume.restrict (Ω : Set (WithLp 2 (ℝ × E))) ≤
      (1 : ℝ≥0∞) • volume.restrict ((⊤ : Opens (WithLp 2 (ℝ × E))) : Set (WithLp 2 (ℝ × E))) := by
    rw [one_smul]
    exact Measure.restrict_mono_set volume (by simp)
  refine ⟨(Lp.LpToLpOfMeasureLeSMul ENNReal.one_ne_top hle).comp
    ((W1p.sobolevEmbeddingTopL hpstar hexp).comp T), fun u => ?_⟩
  have hu : W1p.restrictL le_top (T u) = u := by
    simpa using congrArg (· u) hT
  filter_upwards [Lp.coeFn_LpToLpOfMeasureLeSMul ENNReal.one_ne_top hle
      (W1p.sobolevEmbeddingTopL hpstar hexp (T u)),
    ae_restrict_of_ae_restrict_of_subset (by simp)
      (W1p.coeFn_sobolevEmbeddingTopL hpstar hexp (T u)),
    W1p.value_restrictL_ae le_top (T u)] with x h1 h2 h3
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, h1, h2, ← h3, hu]

/-- **The Sobolev inequality on bounded Lipschitz domains.** If `Ω ⊆ ℝ × E` is a bounded Lipschitz
domain of dimension `n`, `1 ≤ p` and `1/p⋆ + 1/n = 1/p` with `p⋆ < ∞`, then for every `q ≤ p⋆`
there is a constant `C` with `‖u‖_{L^q(Ω)} ≤ C ‖u‖_{W^{1,p}(Ω)}` for all `u ∈ W^{1,p}(Ω)`. -/
theorem W1p.exists_eLpNorm_value_le_of_isLipschitzDomainWith (hpstar : pstar ≠ ∞)
    (hexp : pstar⁻¹ + (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0∞)⁻¹ = p⁻¹)
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) {q : ℝ≥0∞} (hq : q ≤ pstar) :
    ∃ C : ℝ≥0, ∀ u : W1p volume Ω p,
      eLpNorm (W1p.value u) q (volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))) ≤ C * ‖u‖ₑ := by
  let _ := Fact.mk (one_le_of_inv_add_eq_inv hexp)
  obtain ⟨S, hS⟩ := W1p.exists_sobolevEmbeddingL_of_isLipschitzDomainWith hpstar hexp hΩ hb
  exact W1p.exists_eLpNorm_value_le_of_ae_eq hb.measure_lt_top.ne hq S hS

/-- **Integrability on bounded Lipschitz domains.** If `Ω ⊆ ℝ × E` is a bounded Lipschitz domain
of dimension `n`, every `u ∈ W^{1,p}(Ω)` lies in `L^q(Ω)` for every `q ≤ p⋆`, where
`1/p⋆ + 1/n = 1/p` and `p⋆ < ∞`. -/
theorem W1p.memLp_value_of_isLipschitzDomainWith (hpstar : pstar ≠ ∞)
    (hexp : pstar⁻¹ + (finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0∞)⁻¹ = p⁻¹)
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) {q : ℝ≥0∞} (hq : q ≤ pstar)
    (u : W1p volume Ω p) :
    MemLp (W1p.value u) q (volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))) := by
  obtain ⟨C, hC⟩ := W1p.exists_eLpNorm_value_le_of_isLipschitzDomainWith hpstar hexp hΩ hb hq
  have hfin : C * ‖u‖ₑ < ∞ := by finiteness
  exact (hC u).trans_lt hfin

end TauCeti

end
