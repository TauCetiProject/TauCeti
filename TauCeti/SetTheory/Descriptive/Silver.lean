/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.SetTheory.Descriptive.Antichain
public import TauCeti.SetTheory.Descriptive.GSGraph
import TauCeti.Topology.Baire.KuratowskiUlam
import TauCeti.Topology.Baire.Mycielski
import TauCeti.Topology.Perfect

/-!
# The category route to Silver's theorem

Silver's theorem says that a Borel equivalence relation `E` on a Polish space has countably many
classes or a continuous injection of Cantor space whose distinct points are `E`-inequivalent.
B. D. Miller's category proof splits it into two halves. The G₀ dichotomy, applied to the
inequivalence relation of `E`, turns uncountably many classes into a continuous map
`φ : (ℕ → Bool) → X` sending the edges of `gSGraph S` to `E`-inequivalent pairs, for a dense set of
words `S`. This file proves the second half: such a map already yields a Cantor antichain.

The argument runs entirely on Cantor space. The pulled-back relation `E.comap φ` is Borel in the
square. Each of its classes `{b | E (φ a) (φ b)}` is a Borel set containing no edge of
`gSGraph S`, hence meagre by Miller's independence lemma
(`TauCeti.isMeagre_setOf_comp_of_forall_gSGraph_adj`). By the Kuratowski–Ulam theorem a Borel
subset of the square all of whose sections are meagre is meagre. Mycielski's theorem then gives a
continuous map `f` of Cantor space into itself whose distinct points are `E.comap φ`-inequivalent,
and `φ ∘ f` is a Cantor antichain for `E` inside the range of `φ`.

No topological hypothesis on `X` is needed beyond its Borel σ-algebra, which makes the continuous
map `φ` measurable; the meagreness statement needs only a measurable `φ` and no topology on `X`.

## Main results

* `Setoid.isMeagre_comap_of_forall_gSGraph_adj`: the relation pulled back along a measurable map
  sending the edges of `gSGraph S` to inequivalent pairs is meagre, for dense `S`.
* `Setoid.hasCantorAntichainOn_range_of_forall_gSGraph_adj`: such a continuous map carries a
  Cantor antichain of `E` inside its range.

## References

* B. D. Miller, *The graph-theoretic approach to descriptive set theory*, Bulletin of Symbolic
  Logic 18 (2012), 554–575, the proof of Silver's theorem from the G₀ dichotomy.
* B. D. Miller, *Forceless, ineffective, powerless proofs of descriptive dichotomy theorems*,
  lecture notes, Lecture I (Silver's theorem by the category route).
* J. H. Silver, *Counting the number of equivalence classes of Borel and coanalytic equivalence
  relations*, Annals of Mathematical Logic 18 (1980), 1–28.
* The same composition of Miller's lemma, Kuratowski–Ulam and Mycielski's theorem is carried out
  by `categoryReductionHypothesis_of_gSGraphHom` and `gandy_harrington_of_category_route` in
  `InfinitaryLogic/Conditional/SilverCategoryRoute.lean` of `cameronfreer/infinitary-logic`
  (Apache-2.0), checkpoint `518a366cba97b1ae8c4dc64a297a396939bc3e0b`. There it is stated for one
  fixed set of words and a complete separable metric target space; here it is stated for every
  dense set of words and any topological space with its Borel σ-algebra.
-/

public section

open Set TauCeti

namespace Setoid

variable {X : Type*} {S : Set (List Bool)} {φ : (ℕ → Bool) → X}

/-- Let `E` be a Borel equivalence relation and `φ` a measurable map from Cantor space sending the
edges of `gSGraph S` to `E`-inequivalent pairs. If `S` is dense, the pulled-back relation
`E.comap φ` is meagre in the square of Cantor space. -/
theorem isMeagre_comap_of_forall_gSGraph_adj [MeasurableSpace X] (E : Setoid X)
    (hE : MeasurableSet {p : X × X | E p.1 p.2}) (hS : DenseWords S) (hφ : Measurable φ)
    (hφE : ∀ ⦃y z⦄, (gSGraph S).Adj y z → ¬ E (φ y) (φ z)) :
    IsMeagre {p : (ℕ → Bool) × (ℕ → Bool) | E.comap φ p.1 p.2} :=
  -- The pulled-back relation is Borel, and each of its sections is a meagre class.
  (hE.preimage (hφ.prodMap hφ)).baireMeasurableSet.isMeagre_of_forall_isMeagre_curry_left
    (isMeagre_setOf_comp_of_forall_gSGraph_adj hS (fun _ => measurable_prodMk_left hE) hφ hφE)

/-- **The category route to Silver's theorem.** Let `E` be a Borel equivalence relation and `φ` a
continuous map from Cantor space sending the edges of `gSGraph S` to `E`-inequivalent pairs. If `S`
is dense, the range of `φ` carries a Cantor antichain for `E`. -/
theorem hasCantorAntichainOn_range_of_forall_gSGraph_adj [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] (E : Setoid X) (hE : MeasurableSet {p : X × X | E p.1 p.2})
    (hS : DenseWords S) (hφ : Continuous φ)
    (hφE : ∀ ⦃y z⦄, (gSGraph S).Adj y z → ¬ E (φ y) (φ z)) :
    E.HasCantorAntichainOn (range φ) := by
  obtain ⟨f, hf, -, hfE⟩ := hasCantorAntichainOn_iff.1 <|
    (E.comap φ).hasCantorAntichainOn_univ_of_isMeagre
      (E.isMeagre_comap_of_forall_gSGraph_adj hE hS hφ.measurable hφE)
  exact hasCantorAntichainOn_iff.2 ⟨φ ∘ f, hφ.comp hf, fun _ => mem_range_self _, hfE⟩

end Setoid
