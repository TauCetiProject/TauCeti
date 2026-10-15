/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.ExchangeableGraphLaw.Coding
public import TauCeti.Combinatorics.DenseGraphLimits.ExchangeableGraphLaw.Infinite.Mixture
import TauCeti.Probability.Exchangeability.Arrays.AldousHoover.Joint.Representation

/-!
# Aldous–Hoover codings and graphon mixing measures

The graph law of a joint Boolean coding is a mixture of the sampling laws of its frozen
coding graphons. Here we identify its unique mixing measure on graphon space: it is the
pushforward of the uniform global variable along the classes of those graphons. Thus the
Aldous–Hoover representation and the Diaconis–Janson correspondence agree on their mixing
measure, independently of the choice of coding or strict graphon representatives.

Every exchangeable graph law admits a coding of its adjacency array with this mixing measure.
The coding need not be pointwise symmetric or have a prescribed diagonal: `graphLawOfArray`
symmetrizes its entries and discards its diagonal.

## References

* P. Diaconis, S. Janson, *Graph limits and exchangeable random graphs*, Rend. Mat. Appl. (7) 28
  (2008), 33–61, Theorem 5.3 and Section 7.
* O. Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005, Chapter 7.
-/

public section

noncomputable section

open MeasureTheory unitInterval TauCeti.Probability.AldousHoover

namespace TauCeti

namespace DenseGraphLimits

/-- The mixing measure of the graph law of a joint coding is the law of the graphon class
obtained by freezing its uniform global variable. This identifies the mixing measure for any
coding of the graph law, without pointwise symmetry or diagonal assumptions on the coding. -/
theorem graphonMixtureLawEquiv_symm_eq_map_codingGraphon (L : InfiniteExchangeableGraphLaw)
    {f : I × I × I × I → Bool} (hf : Measurable f)
    (hL : graphLawOfArray ((noiseMeasure Unit (Sym2 ℕ)).map
      fun u p => jointArray f p u) = L.law) :
    graphonMixtureLawEquiv.symm L =
      ProbabilityMeasure.map (⟨volume, inferInstance⟩ : ProbabilityMeasure I) fun t =>
        (SeparationQuotient.mk
          (codingGraphon (fun q => f (t, q)) (hf.comp measurable_prodMk_left)) :
            GraphonSpaceI) := by
  have hW := measurable_graphonSpace_mk
    (W := fun t => codingGraphon (fun q => f (t, q)) (hf.comp measurable_prodMk_left))
    (measurable_codingGraphon hf)
  simpa only [toGraphonSpaceI_eq_self] using
    graphonMixtureLawEquiv_symm_eq_map L (⟨volume, inferInstance⟩ : ProbabilityMeasure I)
      hW.aemeasurable (hL.symm.trans (graphLawOfArray_map_jointArray hf))

/-- Every exchangeable graph law has an Aldous–Hoover coding of its adjacency array whose
frozen coding graphons induce exactly its Diaconis–Janson mixing measure. -/
theorem InfiniteExchangeableGraphLaw.exists_jointCoding_mixingMeasure
    (L : InfiniteExchangeableGraphLaw) :
    ∃ (f : I × I × I × I → Bool) (hf : Measurable f),
      (noiseMeasure Unit (Sym2 ℕ)).map (fun u p => jointArray f p u) = arrayLaw L.law ∧
      graphonMixtureLawEquiv.symm L =
        ProbabilityMeasure.map (⟨volume, inferInstance⟩ : ProbabilityMeasure I) fun t =>
          (SeparationQuotient.mk
            (codingGraphon (fun q => f (t, q)) (hf.comp measurable_prodMk_left)) :
              GraphonSpaceI) := by
  obtain ⟨f, hf, hcode⟩ :=
    (jointlyExchangeable_arrayLaw L.exchangeable).exists_map_jointArray_eq
  refine ⟨f, hf, hcode, graphonMixtureLawEquiv_symm_eq_map_codingGraphon L hf ?_⟩
  rw [hcode, graphLawOfArray_arrayLaw]

end DenseGraphLimits

end TauCeti
