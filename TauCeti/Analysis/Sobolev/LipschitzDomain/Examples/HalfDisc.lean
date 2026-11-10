/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.LipschitzDomain.HalfDisc.Basic
public import TauCeti.Analysis.Sobolev.LipschitzDomain.Morrey
public import TauCeti.Analysis.Sobolev.LipschitzDomain.RellichKondrachov
public import TauCeti.Analysis.Sobolev.LipschitzDomain.Trace.Frontier
public import TauCeti.Analysis.Sobolev.LipschitzDomain.Wkp.Embedding

/-!
# Sobolev analysis on the half-disc

The open half-disc `TauCeti.halfDisc r` of `WithLp 2 (ℝ × ℝ)` is a bounded Lipschitz domain
(`TauCeti.exists_isLipschitzDomainWith_halfDisc`), so the general theory of
`TauCeti.Analysis.Sobolev.LipschitzDomain` applies to it. Its first coordinate is the normal
coordinate, so in the complex coordinate `z = s + it` the flat edge `{0} × (-r, r)` is the real
segment of a boundary half-disc chart of a surface with boundary. This file records, in the
dimension `2` of the plane, the consequences used for Sobolev sections in half-disc charts:

* Rellich compactness: the value map `W^{1,p} → Lᵖ` is compact, and so is the embedding into
  `L^q` for every `q` below the Sobolev exponent `p⋆`;
* a bounded extension operator `W^{1,p}(D⁺) → W^{1,p}(ℝ²)` and the Sobolev embedding;
* a bounded trace operator onto `Lᵖ` of the frontier, that is of the flat segment together with
  the closed arc, for the one-dimensional Hausdorff measure;
* for `p > 2`, Morrey's embedding into `C^{0,1-2/p}` of the closed half-disc, its compact Hölder
  variant, and multiplication;
* for `p > 2`, the trace of `u` is the restriction of the continuous representative of `u`, in
  particular on the flat edge;
* the higher-order embeddings `W^{k+1,p} → W^{k,p⋆}` and `W^{k,p} → L^q`.

## Main declarations

* `TauCeti.W1p.isCompactOperator_valueL_halfDisc`,
  `TauCeti.W1p.exists_isCompactOperator_halfDisc`: Rellich compactness.
* `TauCeti.W1p.exists_extensionL_halfDisc`: extension to the plane.
* `TauCeti.W1p.exists_trace_halfDisc`: the trace on the segment and the arc.
* `TauCeti.W1p.exists_morreyEmbeddingL_halfDisc`: Morrey's embedding up to the flat edge.
* `TauCeti.W1p.frontierTrace_ae_eq_continuousOn_halfDisc`: the trace is the boundary value of
  the continuous representative.
* `TauCeti.Wkp.exists_sobolevEmbeddingL_halfDisc`, `TauCeti.Wkp.exists_lpEmbeddingL_halfDisc`:
  higher-order embeddings.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Appendix B.
* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.4 to §5.7.
-/

public section

noncomputable section

namespace TauCeti

open Bornology Metric MeasureTheory Module Set TopologicalSpace
open scoped ENNReal NNReal

/-- The Euclidean plane `WithLp 2 (ℝ × ℝ)` has dimension `2`. -/
private theorem finrank_withLp_two_real_prod : finrank ℝ (WithLp 2 (ℝ × ℝ)) = 2 := by
  rw [(WithLp.linearEquiv 2 ℝ (ℝ × ℝ)).finrank_eq, Module.finrank_prod, Module.finrank_self]

section Exponent

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Rellich compactness on the half-disc.** For `1 ≤ p ≤ ∞`, the value map
`W^{1,p}(D⁺) → Lᵖ(D⁺)` of the half-disc is a compact operator. -/
theorem W1p.isCompactOperator_valueL_halfDisc (r : ℝ) :
    IsCompactOperator (W1p.valueL (mu := volume) (Omega := halfDisc r) (p := p)) :=
  (exists_isLipschitzDomainWith_halfDisc r).elim fun _ hL =>
    W1p.isCompactOperator_valueL_of_isLipschitzDomainWith hL (isBounded_halfDisc r)

/-- **Rellich compactness into `L^q` on the half-disc.** If `1 ≤ q < ∞` lies below the Sobolev
exponent, `1/p < 1/q + 1/2`, the embedding `W^{1,p}(D⁺) → L^q(D⁺)` is a compact operator. -/
theorem W1p.exists_isCompactOperator_halfDisc (r : ℝ) {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : q ≠ ∞)
    (hpq : p⁻¹ < q⁻¹ + 2⁻¹) :
    ∃ S : W1p volume (halfDisc r) p →L[ℝ]
        Lp ℝ q (volume.restrict (halfDisc r : Set (WithLp 2 (ℝ × ℝ)))),
      IsCompactOperator S ∧
        ∀ u, S u =ᵐ[volume.restrict (halfDisc r : Set (WithLp 2 (ℝ × ℝ)))] W1p.value u := by
  obtain ⟨L, hL⟩ := exists_isLipschitzDomainWith_halfDisc r
  refine W1p.exists_isCompactOperator_of_isLipschitzDomainWith hq ?_ hL (isBounded_halfDisc r)
  rwa [finrank_withLp_two_real_prod, Nat.cast_ofNat]

/-- **Extension from the half-disc.** There is a bounded linear extension operator
`W^{1,p}(D⁺) → W^{1,p}(ℝ²)` whose composite with restriction to the half-disc is the identity. -/
theorem W1p.exists_extensionL_halfDisc (r : ℝ) :
    ∃ T : W1p volume (halfDisc r) p →L[ℝ] W1p volume (⊤ : Opens (WithLp 2 (ℝ × ℝ))) p,
      (W1p.restrictL le_top).comp T = ContinuousLinearMap.id ℝ (W1p volume (halfDisc r) p) :=
  (exists_isLipschitzDomainWith_halfDisc r).elim fun _ hL =>
    W1p.exists_extensionL_of_isLipschitzDomainWith hL (isBounded_halfDisc r)

/-- **The Sobolev embedding on the half-disc.** If `1/p⋆ + 1/2 = 1/p` with `p⋆ < ∞`, inclusion is
a bounded linear map `W^{1,p}(D⁺) → L^{p⋆}(D⁺)`. -/
theorem W1p.exists_sobolevEmbeddingL_halfDisc (r : ℝ) {pstar : ℝ≥0∞} (hpstar : pstar ≠ ∞)
    (hexp : pstar⁻¹ + 2⁻¹ = p⁻¹) :
    letI := Fact.mk (one_le_of_inv_add_eq_inv hexp)
    ∃ S : W1p volume (halfDisc r) p →L[ℝ]
        Lp ℝ pstar (volume.restrict (halfDisc r : Set (WithLp 2 (ℝ × ℝ)))),
      ∀ u, S u =ᵐ[volume.restrict (halfDisc r : Set (WithLp 2 (ℝ × ℝ)))] W1p.value u := by
  obtain ⟨L, hL⟩ := exists_isLipschitzDomainWith_halfDisc r
  refine W1p.exists_sobolevEmbeddingL_of_isLipschitzDomainWith hpstar ?_ hL (isBounded_halfDisc r)
  rwa [finrank_withLp_two_real_prod, Nat.cast_ofNat]

/-- **Trace on the boundary of the half-disc.** For `0 < r` and `1 ≤ p < ∞` there is a bounded
linear trace operator from `W^{1,p}(D⁺)` to `Lᵖ` of the frontier, the flat segment
`{0} × [-r, r]` together with the closed arc, for the one-dimensional Hausdorff measure. It sends
every function continuous on the closed half-disc to its restriction to the frontier. -/
theorem W1p.exists_trace_halfDisc (hp : p ≠ ∞) {r : ℝ} (hr : 0 < r) :
    ∃ T : W1p volume (halfDisc r) p →L[ℝ]
        Lp ℝ p ((μHE[1] : Measure (WithLp 2 (ℝ × ℝ))).restrict
          (closedBall 0 r ∩ {x | x.fst = 0} ∪ sphere 0 r ∩ {x | 0 ≤ x.fst})),
      ∀ (u : W1p volume (halfDisc r) p) (f : WithLp 2 (ℝ × ℝ) → ℝ),
        ContinuousOn f (closedBall 0 r ∩ {x | 0 ≤ x.fst}) →
        W1p.value u =ᵐ[volume.restrict (halfDisc r : Set (WithLp 2 (ℝ × ℝ)))] f →
        T u =ᵐ[(μHE[1] : Measure (WithLp 2 (ℝ × ℝ))).restrict
          (closedBall 0 r ∩ {x | x.fst = 0} ∪ sphere 0 r ∩ {x | 0 ≤ x.fst})] f := by
  obtain ⟨L, hL⟩ := exists_isLipschitzDomainWith_halfDisc r
  have h := W1p.exists_frontierTrace hp hL (isBounded_halfDisc r)
  rwa [finrank_self, frontier_halfDisc hr, closure_halfDisc hr] at h

end Exponent

section Morrey

variable {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]

/-- **Morrey's embedding on the half-disc.** For `2 < p < ∞`, every `u ∈ W^{1,p}(D⁺)` agrees almost
everywhere with a function on the closed half-disc which is Hölder of exponent `1 - 2/p` up to the
flat edge and the arc, and this representative depends linearly and boundedly on `u`. -/
theorem W1p.exists_morreyEmbeddingL_halfDisc (hp : 2 < p) (r : ℝ) :
    ∃ T : W1p volume (halfDisc r) p →L[ℝ]
        HolderSpace (1 - 2 / p) (closure (halfDisc r : Set (WithLp 2 (ℝ × ℝ)))) ℝ,
      ∀ u, ∀ᵐ x ∂volume, ∀ hx : x ∈ halfDisc r, T u ⟨x, subset_closure hx⟩ = W1p.value u x := by
  obtain ⟨L, hL⟩ := exists_isLipschitzDomainWith_halfDisc r
  have h := W1p.exists_morreyEmbeddingL_of_isLipschitzDomainWith
    (by rwa [finrank_withLp_two_real_prod, Nat.cast_ofNat]) hL (isBounded_halfDisc r)
  rwa [finrank_withLp_two_real_prod, Nat.cast_ofNat] at h

/-- **Compact Hölder embedding on the half-disc.** For `2 < p < ∞` and `β < 1 - 2/p`, the
embedding of `W^{1,p}(D⁺)` into `C^{0,β}` of the closed half-disc is a compact operator. -/
theorem W1p.exists_isCompactOperator_holder_halfDisc (hp : 2 < p) (r : ℝ) {β : ℝ≥0}
    (hβ : β < 1 - 2 / p) :
    ∃ T : W1p volume (halfDisc r) p →L[ℝ]
        HolderSpace β (closure (halfDisc r : Set (WithLp 2 (ℝ × ℝ)))) ℝ,
      IsCompactOperator T ∧
        ∀ u, ∀ᵐ x ∂volume, ∀ hx : x ∈ halfDisc r, T u ⟨x, subset_closure hx⟩ = W1p.value u x := by
  obtain ⟨L, hL⟩ := exists_isLipschitzDomainWith_halfDisc r
  have hp' : (finrank ℝ (WithLp 2 (ℝ × ℝ)) : ℝ≥0) < p := by
    rwa [finrank_withLp_two_real_prod, Nat.cast_ofNat]
  have hβ' : β < 1 - finrank ℝ (WithLp 2 (ℝ × ℝ)) / p := by
    rwa [finrank_withLp_two_real_prod, Nat.cast_ofNat]
  exact W1p.exists_isCompactOperator_holder_of_isLipschitzDomainWith hp' hL (isBounded_halfDisc r)
    hβ'

/-- Multiplication on the half-disc for a given Lipschitz constant. Stating the Lipschitz
hypothesis in this file keeps the instance unification with the general lemma cheap. -/
private theorem W1p.exists_mulL_halfDisc_of_isLipschitzDomainWith (hp : 2 < p) {r : ℝ}
    {L : ℝ≥0} (hL : (halfDisc r : Set (WithLp 2 (ℝ × ℝ))).IsLipschitzDomainWith L) :
    ∃ M : W1p volume (halfDisc r) p →L[ℝ] W1p volume (halfDisc r) p →L[ℝ]
        W1p volume (halfDisc r) p,
      ∀ u v, W1p.value (M u v) =ᵐ[volume.restrict (halfDisc r : Set (WithLp 2 (ℝ × ℝ)))]
        fun x => W1p.value u x * W1p.value v x := by
  have hp' : (finrank ℝ (WithLp 2 (ℝ × ℝ)) : ℝ≥0) < p := by
    rwa [finrank_withLp_two_real_prod, Nat.cast_ofNat]
  have h := W1p.exists_mulL_of_isLipschitzDomainWith (E := ℝ) hp' hL (isBounded_halfDisc r)
  exact h

/-- **Multiplication on the half-disc.** For `2 < p < ∞`, pointwise multiplication is a bounded
bilinear map `W^{1,p}(D⁺) × W^{1,p}(D⁺) → W^{1,p}(D⁺)`. -/
theorem W1p.exists_mulL_halfDisc (hp : 2 < p) (r : ℝ) :
    ∃ M : W1p volume (halfDisc r) p →L[ℝ] W1p volume (halfDisc r) p →L[ℝ]
        W1p volume (halfDisc r) p,
      ∀ u v, W1p.value (M u v) =ᵐ[volume.restrict (halfDisc r : Set (WithLp 2 (ℝ × ℝ)))]
        fun x => W1p.value u x * W1p.value v x :=
  (exists_isLipschitzDomainWith_halfDisc r).elim fun _ hL =>
    W1p.exists_mulL_halfDisc_of_isLipschitzDomainWith hp hL

/-- **Continuous representatives up to the boundary.** For `2 < p < ∞` and `0 < r`, every
`u ∈ W^{1,p}(D⁺)` agrees almost everywhere on the half-disc with a function continuous on the
closed half-disc. -/
theorem W1p.exists_continuousOn_ae_eq_halfDisc (hp : 2 < p) {r : ℝ} (hr : 0 < r)
    (u : W1p volume (halfDisc r) p) :
    ∃ f : WithLp 2 (ℝ × ℝ) → ℝ, ContinuousOn f (closedBall 0 r ∩ {x | 0 ≤ x.fst}) ∧
      W1p.value u =ᵐ[volume.restrict (halfDisc r : Set (WithLp 2 (ℝ × ℝ)))] f := by
  classical
  obtain ⟨T, hT⟩ := W1p.exists_morreyEmbeddingL_halfDisc hp r
  refine ⟨fun x => if hx : x ∈ closure (halfDisc r : Set (WithLp 2 (ℝ × ℝ))) then T u ⟨x, hx⟩
    else 0, ?_, ?_⟩
  · rw [← closure_halfDisc hr, continuousOn_iff_continuous_domRestrict]
    convert (T u).continuous using 1
    ext x
    exact dite_eq_left x.property
  · refine (ae_restrict_iff' (halfDisc r).isOpen.measurableSet).2 ?_
    filter_upwards [hT u] with x hx hxΩ
    rw [dite_eq_left (subset_closure hxΩ)]
    exact (hx hxΩ).symm

/-- **The trace is the boundary value of the continuous representative.** For `2 < p < ∞` and
`0 < r`, every `u ∈ W^{1,p}(D⁺)` has a representative continuous on the closed half-disc whose
restriction to the frontier is the trace `W1p.frontierTrace u`, almost everywhere for the
one-dimensional Hausdorff measure; in particular this holds on the flat edge `{0} × [-r, r]`. -/
theorem W1p.frontierTrace_ae_eq_continuousOn_halfDisc (hp : 2 < p) {r : ℝ} (hr : 0 < r) {L : ℝ≥0}
    (hL : (halfDisc r : Set (WithLp 2 (ℝ × ℝ))).IsLipschitzDomainWith L)
    (u : W1p volume (halfDisc r) p) :
    ∃ f : WithLp 2 (ℝ × ℝ) → ℝ, ContinuousOn f (closedBall 0 r ∩ {x | 0 ≤ x.fst}) ∧
      W1p.value u =ᵐ[volume.restrict (halfDisc r : Set (WithLp 2 (ℝ × ℝ)))] f ∧
      W1p.frontierTrace ENNReal.coe_ne_top hL (isBounded_halfDisc r) u
        =ᵐ[(μHE[1] : Measure (WithLp 2 (ℝ × ℝ))).restrict
          (frontier (halfDisc r : Set (WithLp 2 (ℝ × ℝ))))] f ∧
      W1p.frontierTrace ENNReal.coe_ne_top hL (isBounded_halfDisc r) u
        =ᵐ[(μHE[1] : Measure (WithLp 2 (ℝ × ℝ))).restrict
          (closedBall 0 r ∩ {x | x.fst = 0})] f := by
  obtain ⟨f, hf, hu⟩ := W1p.exists_continuousOn_ae_eq_halfDisc hp hr u
  have htr := W1p.frontierTrace_ae_eq_of_continuousOn ENNReal.coe_ne_top hL (isBounded_halfDisc r)
    (by rwa [closure_halfDisc hr]) hu
  have hμ : ∀ (s : Set (WithLp 2 (ℝ × ℝ))) (g : WithLp 2 (ℝ × ℝ) → ℝ),
      g =ᵐ[(μHE[finrank ℝ ℝ] : Measure (WithLp 2 (ℝ × ℝ))).restrict s] f →
        g =ᵐ[(μHE[1] : Measure (WithLp 2 (ℝ × ℝ))).restrict s] f := by
    rw [finrank_self]
    exact fun _ _ h => h
  replace htr := hμ _ _ htr
  refine ⟨f, hf, hu, htr, ae_restrict_of_ae_restrict_of_subset ?_ htr⟩
  rw [frontier_halfDisc hr]
  exact subset_union_left

end Morrey

section Higher

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Higher-order Sobolev embedding on the half-disc.** If `1/p⋆ + 1/2 = 1/p` with `p⋆ < ∞`, then
for every `k` inclusion is a bounded linear map `W^{k+1,p}(D⁺) → W^{k,p⋆}(D⁺)`. -/
theorem Wkp.exists_sobolevEmbeddingL_halfDisc (r : ℝ) {pstar : ℝ≥0∞} (hpstar : pstar ≠ ∞)
    (hexp : pstar⁻¹ + 2⁻¹ = p⁻¹) (k : ℕ) :
    letI := Fact.mk (one_le_of_inv_add_eq_inv hexp)
    ∃ T : Wkp volume (halfDisc r) p (k + 1) →L[ℝ] Wkp volume (halfDisc r) pstar k,
      ∀ u, Wkp.value k (T u) =ᵐ[volume.restrict (halfDisc r : Set (WithLp 2 (ℝ × ℝ)))]
        Wkp.value (k + 1) u := by
  obtain ⟨L, hL⟩ := exists_isLipschitzDomainWith_halfDisc r
  refine Wkp.exists_sobolevEmbeddingL_of_isLipschitzDomainWith hpstar ?_ hL
    (isBounded_halfDisc r) k
  rwa [finrank_withLp_two_real_prod, Nat.cast_ofNat]

/-- **Higher-order embedding into Lebesgue spaces on the half-disc.** If `1/q + k/2 = 1/p` with
`q < ∞`, that is `kp < 2`, inclusion is a bounded linear map `W^{k,p}(D⁺) → L^q(D⁺)`. -/
theorem Wkp.exists_lpEmbeddingL_halfDisc (r : ℝ) (k : ℕ) {q : ℝ≥0∞} (hq : q ≠ ∞)
    (hexp : q⁻¹ + k * 2⁻¹ = p⁻¹) :
    letI := Fact.mk (one_le_of_inv_add_eq_inv hexp)
    ∃ T : Wkp volume (halfDisc r) p k →L[ℝ]
        Lp ℝ q (volume.restrict (halfDisc r : Set (WithLp 2 (ℝ × ℝ)))),
      ∀ u, T u =ᵐ[volume.restrict (halfDisc r : Set (WithLp 2 (ℝ × ℝ)))] Wkp.value k u := by
  obtain ⟨L, hL⟩ := exists_isLipschitzDomainWith_halfDisc r
  refine Wkp.exists_lpEmbeddingL_of_isLipschitzDomainWith k hq ?_ hL (isBounded_halfDisc r)
  rwa [finrank_withLp_two_real_prod, Nat.cast_ofNat]

end Higher

end TauCeti
