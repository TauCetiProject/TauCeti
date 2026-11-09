/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.SetTheory.Descriptive.Antichain
public import TauCeti.SetTheory.Descriptive.BorelReducibility
public import TauCeti.SetTheory.Descriptive.GSGraph
import TauCeti.SetTheory.Descriptive.GZeroDichotomy
import TauCeti.Topology.MetricSpace.Polish.Pi
import TauCeti.Topology.Baire.KuratowskiUlam
import TauCeti.Topology.Baire.Mycielski
import TauCeti.Topology.Perfect

/-!
# Silver's theorem

Silver's theorem says that a Borel equivalence relation `E` on a Polish space has countably many
classes or a continuous injection of Cantor space whose distinct points are `E`-inequivalent.
B. D. Miller's category proof splits it into two halves. The G₀ dichotomy, applied to the
inequivalence relation of `E`, turns uncountably many classes into a continuous map
`φ : (ℕ → Bool) → X` sending the edges of `gSGraph S` to `E`-inequivalent pairs, for every set of
words `S` with at most one word of each length
(`Setoid.exists_continuous_forall_gSGraph_adj_not`). This file proves the second half: for a dense
set `S`, such a map already yields a Cantor antichain. The set `canonicalWords` is both, so the two
halves combine into the theorem, which this file then states in the forms in which it is used.

The argument runs entirely on Cantor space. The pulled-back relation `E.comap φ` is Borel in the
square. Each of its classes `{b | E (φ a) (φ b)}` is a Borel set containing no edge of
`gSGraph S`, hence meagre by Miller's independence lemma
(`TauCeti.isMeagre_setOf_comp_of_forall_gSGraph_adj`). By the Kuratowski–Ulam theorem a Borel
subset of the square all of whose sections are meagre is meagre. Mycielski's theorem then gives a
continuous map `f` of Cantor space into itself whose distinct points are `E.comap φ`-inequivalent,
and `φ ∘ f` is a Cantor antichain for `E` inside the range of `φ`.

No topological hypothesis on `X` is needed beyond its Borel σ-algebra, which makes the continuous
map `φ` measurable; the meagreness statement needs only a measurable `φ` and no topology on `X`.

Once the theorem holds on Polish spaces, the other forms follow by changing the topology. A
standard Borel space carries a Polish topology generating its σ-algebra, and a continuous
injection of Cantor space is a measurable embedding for it. A Borel subset `A` of a Polish space
is standard Borel, so a Borel equivalence relation `F` on `A` has countably many classes or a
measurable embedding of Cantor space into `A` with `F`-inequivalent values; transporting the
identity of Cantor space along that embedding gives a Cantor antichain on `A` for the topology of
the ambient space and for any finer relation `R`.

## Main results

* `Setoid.isMeagre_comap_of_forall_gSGraph_adj`: the relation pulled back along a measurable map
  sending the edges of `gSGraph S` to inequivalent pairs is meagre, for dense `S`.
* `Setoid.hasCantorAntichainOn_range_of_forall_gSGraph_adj`: such a continuous map carries a
  Cantor antichain of `E` inside its range.
* `Setoid.silver_dichotomy`: **Silver's theorem**, a Borel equivalence relation on a Polish space
  has countably many classes or a Cantor antichain on the whole space.
* `Setoid.silver_dichotomy_standardBorel`: on a standard Borel space, countably many classes or a
  measurable embedding of Cantor space with pairwise inequivalent values.
* `Setoid.mk_quotient_le_aleph0_or_eq_continuum`: the cardinality form, on a standard Borel space
  a Borel equivalence relation has at most `ℵ₀` or exactly `𝔠` classes.
* `Setoid.countable_or_hasCantorAntichainOn_of_measurableSet`: the relative form, for a Borel
  equivalence relation `F` on a Borel subset `A` of a Polish space and any relation `R` on the
  ambient space refining `F`, countably many `F`-classes or a Cantor antichain on `A` for `R`.
* `Setoid.borelReducible_bot_iff_not_countable_quotient`: the reducibility form, equality on
  Cantor space Borel reduces to a Borel equivalence relation on a standard Borel space exactly
  when the latter has uncountably many classes.

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
* The forms of the theorem follow `gandy_harrington_for_relation`, `silver_core_polish` and
  `silverBurgessDichotomy` in `InfinitaryLogic/Conditional/GandyHarrington.lean`, and
  `silver_countable_or_cantorAntichain` in `InfinitaryLogic/Conditional/SilverAntichain.lean`, of
  `cameronfreer/infinitary-logic` (Apache-2.0), checkpoint
  `518a366cba97b1ae8c4dc64a297a396939bc3e0b`. There the Polish form assumes a complete separable
  metric space, the cardinality form is the Prop-valued definition `SilverBurgessDichotomy`, and
  the relative form refines the topology to make the Borel set clopen. Here the Polish form
  assumes `PolishSpace`, the cardinality form is stated directly, and the relative form transports
  a measurable embedding of Cantor space by `hasCantorAntichainOn_image_iff`.
-/

public section

open Cardinal Set TauCeti

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

/-! ### The forms of Silver's theorem -/

/-- **Silver's theorem.** A Borel equivalence relation on a Polish space has countably many
classes, or a Cantor antichain on the whole space: a continuous map of Cantor space sending
distinct points to inequivalent points. -/
theorem silver_dichotomy [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    (E : Setoid X) (hE : MeasurableSet {p : X × X | E p.1 p.2}) :
    Countable (Quotient E) ∨ E.HasCantorAntichainOn univ := by
  refine or_iff_not_imp_left.2 fun hc => ?_
  obtain ⟨φ, hφ, hφE⟩ :=
    E.exists_continuous_forall_gSGraph_adj_not hE hc sparseWords_canonicalWords
  exact (E.hasCantorAntichainOn_range_of_forall_gSGraph_adj hE denseWords_canonicalWords hφ
    hφE).mono (subset_univ _)

/-- **Silver's theorem on a standard Borel space.** A Borel equivalence relation on a standard
Borel space has countably many classes, or a measurable embedding of Cantor space sending distinct
points to inequivalent points. -/
theorem silver_dichotomy_standardBorel [MeasurableSpace X] [StandardBorelSpace X] (E : Setoid X)
    (hE : MeasurableSet {p : X × X | E p.1 p.2}) :
    Countable (Quotient E) ∨
      ∃ f : (ℕ → Bool) → X, MeasurableEmbedding f ∧ ∀ a b, a ≠ b → ¬ E (f a) (f b) := by
  let := upgradeStandardBorel X
  refine (silver_dichotomy E hE).imp_right fun h => ?_
  obtain ⟨f, hf, -, hinj, hfE⟩ := h.exists_injective
  exact ⟨f, hf.measurableEmbedding hinj, hfE⟩

/-- **The cardinality form of Silver's theorem.** A Borel equivalence relation on a standard Borel
space has at most `ℵ₀` or exactly `𝔠` classes. -/
theorem mk_quotient_le_aleph0_or_eq_continuum [MeasurableSpace X] [StandardBorelSpace X]
    (E : Setoid X) (hE : MeasurableSet {p : X × X | E p.1 p.2}) :
    #(Quotient E) ≤ ℵ₀ ∨ #(Quotient E) = 𝔠 := by
  let := upgradeStandardBorel X
  exact (silver_dichotomy E hE).imp (fun h => mk_le_aleph0_iff.2 h) (·.mk_quotient_eq_continuum)

/-- **Silver's theorem relative to a Borel subset.** Let `A` be a Borel subset of a Polish space
`X`, `F` a Borel equivalence relation on `A`, and `R` any equivalence relation on `X` whose
restriction to `A` refines `F`. Then `F` has countably many classes, or `A` carries a Cantor
antichain for `R`, continuous for the topology of `X`. -/
theorem countable_or_hasCantorAntichainOn_of_measurableSet [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X] {A : Set X} (hA : MeasurableSet A) (R : Setoid X)
    (F : Setoid A) (hRF : ∀ x y : A, R x y → F x y)
    (hF : MeasurableSet {p : A × A | F p.1 p.2}) :
    Countable (Quotient F) ∨ R.HasCantorAntichainOn A := by
  have := hA.standardBorel
  refine (silver_dichotomy_standardBorel F hF).imp_right fun ⟨f, hf, hfF⟩ => ?_
  -- Pulled back along the embedding `(↑) ∘ f` of Cantor space into `X`, the relation `R` is
  -- equality, whose Cantor antichain on the whole space is the identity.
  have hg := (MeasurableEmbedding.subtype_coe hA).comp hf
  have hid : (R.comap ((↑) ∘ f)).HasCantorAntichainOn univ :=
    hasCantorAntichainOn_iff.2 ⟨id, continuous_id, fun _ => trivial,
      fun a b hab h => hfF a b hab (hRF _ _ ((comap_rel _ _ _ _).1 h))⟩
  exact ((hasCantorAntichainOn_image_iff (F := R) hg (fun _ _ => (comap_rel _ _ _ _).symm)
    univ).2 hid).mono <| by
    rintro _ ⟨a, -, rfl⟩
    exact (f a).2

/-- **Silver's theorem in reducibility form.** Equality on Cantor space is Borel reducible to a
Borel equivalence relation on a standard Borel space exactly when the latter has uncountably many
classes. -/
theorem borelReducible_bot_iff_not_countable_quotient [MeasurableSpace X] [StandardBorelSpace X]
    (E : Setoid X) (hE : MeasurableSet {p : X × X | E p.1 p.2}) :
    (⊥ : Setoid (ℕ → Bool)).BorelReducible E ↔ ¬ Countable (Quotient E) := by
  refine ⟨fun h hc => ?_, fun hc => ?_⟩
  · -- A reduction of equality is injective on classes, so Cantor space would be countable.
    obtain ⟨g, -, hg⟩ := h.exists_measurable_injective_quotient
    have := mk_le_aleph0_iff.2 (hg.comp quotientBotEquiv.symm.injective).countable
    exact (by simpa using aleph0_lt_continuum : ℵ₀ < #(ℕ → Bool)).not_ge this
  · let := upgradeStandardBorel X
    exact ((silver_dichotomy E hE).resolve_left hc).borelReducible_bot

end Setoid
