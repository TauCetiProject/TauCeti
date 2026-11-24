/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.HolomorphicFunctions.NormalFamilies
import TauCeti.Topology.ContinuousMap.Ascoli

/-!
# Montel's theorem: local boundedness and relative compactness

A family of holomorphic maps on an open subset `Ω` of a proper complex normed space `V`, such as
`ℂ` or `ℂⁿ`, with values in a proper complex normed space `E`, is locally bounded exactly when its
continuous restrictions have compact closure in `C(↥Ω, E)`.
This space carries the compact-open topology, whose convergence is locally uniform convergence.
The compactness equivalence supplies the input for the subsequence selection theorem in
`HolomorphicFunctions/Montel/Basic.lean`.

The converse is proved in `TauCeti/Analysis/Normed/Group/LocallyBounded.lean` as
`TauCeti.isLocallyBoundedOn_of_totallyBounded_range`: it needs no holomorphicity, holds on any
topological domain, with values in any seminormed group, and assumes only that the continuous
restrictions are totally bounded for the uniformity of compact convergence.

The theorems take an ambient family `F` and continuous restrictions `f`, related by
`⇑(f i) = Ω.domRestrict (F i)`. Given `hF : ∀ i, ContinuousOn (F i) Ω`, one can take
`f i = ⟨Ω.domRestrict (F i), (hF i).domRestrict⟩`, making this equality reflexive.

## Main results

* `TauCeti.isCompact_closure_range_of_isLocallyBoundedOn`: a locally bounded holomorphic family
  with proper target has relatively compact continuous restrictions.
* `TauCeti.isCompact_closure_range_iff_isLocallyBoundedOn`: for holomorphic families on an open
  set with proper target, relative compactness and local boundedness are equivalent.

The forward direction uses `ArzelaAscoli.isCompact_closure_range_of_equicontinuous` and the
equicontinuity theorem `TauCeti.IsLocallyBoundedOn.equicontinuousOn`. Properness of `E` turns the
pointwise norm bounds into pointwise relative compactness; properness of `V` makes closed balls
compact, so that local boundedness bounds the family on a ball around each point. For a complex
normed space, properness is equivalent to finite-dimensionality.

This is the **analytic** normal-families theorem; it is deliberately not routed through Mathlib's
`Analysis/LocallyConvex/Montel.lean` (`MontelSpace`), which is an unrelated notion.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 5 §5.
* J. B. Conway, *Functions of One Complex Variable I* (GTM 11), Ch. VII §2.
* The Montel equicontinuity result in the Riemann mapping development
  [mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505).
-/

public section

open Complex Metric Filter Topology Set

namespace TauCeti

variable {ι V E : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [ProperSpace V]
  [NormedAddCommGroup E] [NormedSpace ℂ E] {Ω : Set V} {F : ι → V → E} {f : ι → C(Ω, E)}

/-- **Montel's theorem, relative-compactness form.** A locally bounded family of holomorphic
maps of an open subset `Ω` of a proper complex normed space `V`, such as `ℂⁿ`, into a proper
complex normed space `E` restricts to a relatively compact family in the space `C(↥Ω, E)` of
continuous maps with the compact-open topology.

The sequential selection theorem `TauCeti.montel` follows from this compactness result.
Properness of `E` is essential: a bounded family of constant maps can fail to be relatively
compact in an infinite-dimensional target. -/
theorem isCompact_closure_range_of_isLocallyBoundedOn [ProperSpace E] (hΩ : IsOpen Ω)
    (hF : ∀ i, DifferentiableOn ℂ (F i) Ω) (hb : IsLocallyBoundedOn F Ω)
    (hf : ∀ i, ⇑(f i) = Ω.domRestrict (F i)) :
    IsCompact (closure (Set.range f)) := by
  have heq : Equicontinuous fun i => (f i : Ω → E) := by
    rw [funext hf]
    exact (equicontinuous_restrict_iff F).mpr (hb.equicontinuousOn hΩ hF)
  -- Arzelà–Ascoli in the compact-open topology: equicontinuity comes from the Schwarz lemma and
  -- pointwise relative compactness from local boundedness.
  refine ArzelaAscoli.isCompact_closure_range_of_equicontinuous heq fun x => ?_
  obtain ⟨C, hC⟩ := hb.exists_forall_norm_le x.property
  refine ⟨closedBall 0 C, isCompact_closedBall _ _, fun i => ?_⟩
  simpa [hf i, mem_closedBall, dist_zero_right] using hC i

/-- **Montel's theorem as an equivalence.** For a family of holomorphic maps of an open subset
`Ω` of a proper complex normed space `V` into a proper complex normed space `E`, being locally
bounded on `Ω` and being relatively compact in `C(↥Ω, E)` are the same condition. -/
theorem isCompact_closure_range_iff_isLocallyBoundedOn [ProperSpace E] (hΩ : IsOpen Ω)
    (hF : ∀ i, DifferentiableOn ℂ (F i) Ω) (hf : ∀ i, ⇑(f i) = Ω.domRestrict (F i)) :
    IsCompact (closure (Set.range f)) ↔ IsLocallyBoundedOn F Ω :=
  ⟨fun h => isLocallyBoundedOn_of_totallyBounded_range hf
      (h.totallyBounded.subset subset_closure),
    fun hb => isCompact_closure_range_of_isLocallyBoundedOn hΩ hF hb hf⟩

end TauCeti
