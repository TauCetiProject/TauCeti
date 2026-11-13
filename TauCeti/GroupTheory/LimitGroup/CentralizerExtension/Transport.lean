/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.LimitGroup.CentralizerExtension.Iterated
public import TauCeti.GroupTheory.LimitGroup.CentralizerExtension.Map

/-!
# Iterated extensions of centralizers along an embedding of the base

A chain of admissible extensions of centralizers over `G` can be transported along an embedding
`f : G →* E` of `G` in a fully residually free group `E`: the top `K` of the chain embeds in the
top of a chain over `E`, compatibly with the coefficient homomorphisms.

The steps of the chain are transported one at a time. If `g : K →* E'` embeds the top of a chain
over `G` in the top of a chain over `E`, the homomorphism `K(u, ℤⁿ) →* E'(g u, ℤⁿ)` induced by `g`
is injective (`TauCeti.LimitGroup.CentralizerExt.map_injective`). The parameter `g u` may be a
proper power in `E'`; since `E'` is again fully residually free, `g u` has a root `r` that is not
a proper power with the same centralizer, and `E'(g u, ℤⁿ)` is the admissible extension
`E'(r, ℤⁿ)` (`TauCeti.LimitGroup.CentralizerExt.congr`).

## Main results

* `TauCeti.LimitGroup.ICE.exists_embedding_of_injective`: transport of a chain of extensions of
  centralizers along an embedding of the base in a fully residually free group.

## References

* O. Kharlampovich, A. Myasnikov, *Irreducible affine varieties over a free group. I:
  Irreducibility of quadratic equations and Nullstellensatz*, J. Algebra 200 (1998), §0.
* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §2.5.
-/

public section

universe u v

namespace TauCeti.LimitGroup

namespace ICE

variable {G K : Type u} {E : Type v} [Group G] [Group K] [Group E]

/-- **Transport of an iterated extension of centralizers along an embedding of the base.** If `G`
embeds in a fully residually free group `E` by `f`, then every ICE group `K` over `G` embeds in an
ICE group `E'` over `E`, by an embedding `g` restricting to `f` on the coefficients:
`g ∘ j = j' ∘ f`, where `j : G →* K` and `j' : E →* E'` are the coefficient inclusions.

If `E` is itself an ICE group over some `F`, appending the new chain (`ICE.append`) gives a chain
over `F` whose top contains `K`. -/
theorem exists_embedding_of_injective (hE : IsFullyResiduallyFree E) {f : G →* E}
    (hf : Function.Injective f) {j : G →* K} (d : ICE G K j) :
    ∃ (E' : Type v) (_ : Group E') (j' : E →* E') (_ : ICE E E' j') (g : K →* E'),
      Function.Injective g ∧ g.comp j = j'.comp f := by
  induction d with
  | refl => exact ⟨E, _, .id E, refl, f, hf, by simp⟩
  | @step K _ j _ u n h ih =>
    obtain ⟨E', _, j', c, g, hg, hgj⟩ := ih
    -- `E'` is fully residually free, so `g u ≠ 1` is a power of some `r` that is not a proper
    -- power, with the same centralizer.
    obtain ⟨r, -, -, -, hr, hC⟩ :=
      (c.isFullyResiduallyFree hE).isResiduallyFree.centralizerExt_root_reduction
        ((map_ne_one_iff g hg).2 h.ne_one)
    -- Embed `K(u, ℤⁿ)` in `E'(g u, ℤⁿ)`, which is the admissible extension `E'(r, ℤⁿ)`.
    refine ⟨CentralizerExt r n, _, CentralizerExt.of.comp j',
      c.step (isAdmissibleCentralizerStep_iff.2 ⟨hr, h.pos⟩),
      (CentralizerExt.congr hC).toMonoidHom.comp (CentralizerExt.map g u n),
      (CentralizerExt.congr hC).injective.comp (CentralizerExt.map_injective hg u n), ?_⟩
    ext x
    simpa using DFunLike.congr_fun hgj x

end ICE

end TauCeti.LimitGroup
