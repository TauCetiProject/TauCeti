/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.RelationalConfiguration.GraphClass
public import TauCeti.ModelTheory.RelationalConfiguration.NotBorel

/-!
# The Friedman–Stanley obstruction to Borel completeness

Let `K` be a set of codes of countable structures in a countable relational language, not assumed
Borel or isomorphism invariant, and let `ρ` assign an ordinal to every code. Write
`K_α = K ∩ {c | ρ c ≤ α}`. If isomorphism on each `K_α` with `α < ω₁` is Borel (for the product
of the subtype σ-algebras), and `ρ` is bounded below `ω₁` on every analytic subset of `K`, then
`K` is not Borel complete (`TauCeti.RelationalConfiguration.not_borelComplete_of_rank_bounded`).

The proof follows Friedman and Stanley: a Borel reduction of isomorphism of countable graphs to
isomorphism on `K` has analytic image, contained in some `K_α`, so it reduces isomorphism of
countable graphs to isomorphism on `K_α`, which would make the former Borel
(`TauCeti.RelationalConfiguration.not_measurableSet_classIso_of_borelComplete` for
`TauCeti.RelationalConfiguration.graphClass`).

## Main results

* `TauCeti.RelationalConfiguration.not_borelComplete_of_rank_bounded`: a class with a rank
  bounded on analytic subsets and Borel isomorphism on each level is not Borel complete.

## References

* H. Friedman and L. Stanley, *A Borel reducibility theory for classes of countable
  structures*, J. Symbolic Logic 54 (1989), §4.
* G. Hjorth and A. S. Kechris, *Borel equivalence relations and classifications of countable
  models*, Ann. Pure Appl. Logic 82 (1996), §§4–5.
-/

public section

open FirstOrder Language MeasureTheory Ordinal Set

namespace TauCeti.RelationalConfiguration

variable {L : Language.{u, v}} [L.IsRelational] [∀ n, Countable (L.Relations n)]

/-- **The Friedman–Stanley obstruction.** Let `K` be any set of codes and `ρ` any ordinal-valued
function on codes, and write `K_α = K ∩ {c | ρ c ≤ α}`. If (a) for every `α < ω₁` the set of
pairs of `K_α × K_α` with isomorphic entries is measurable for the product of the subtype
σ-algebras, and (b) `ρ` is bounded by some `α < ω₁` on every analytic subset of `K`, then `K` is
not Borel complete. -/
theorem not_borelComplete_of_rank_bounded {K : Set (RelationalConfiguration L ℕ)}
    (ρ : RelationalConfiguration L ℕ → Ordinal.{0})
    (ha : ∀ α < ω₁, MeasurableSet {p : ↥(K ∩ {c | ρ c ≤ α}) × ↥(K ∩ {c | ρ c ≤ α}) |
      classIso (K ∩ {c | ρ c ≤ α}) p.1 p.2})
    (hb : ∀ A ⊆ K, AnalyticSet A → ∃ α < ω₁, ∀ c ∈ A, ρ c ≤ α) :
    ¬ BorelComplete K := by
  intro hK
  obtain ⟨f, hf, hfiso⟩ := Setoid.borelReducible_iff.1 <|
    borelComplete_iff.1 hK Language.graph graphClass measurableSet_graphClass
      isomorphismInvariant_graphClass
  -- the image of the reduction is analytic, as the image of the Polish space `graphClass`
  have : PolishSpace graphClass := isClosed_graphClass.polishSpace
  have hA : AnalyticSet (range fun x ↦ (f x : RelationalConfiguration L ℕ)) := by
    rw [← image_univ]
    exact MeasurableSet.univ.analyticSet_image (measurable_subtypeVal.comp hf)
  obtain ⟨α, hα, hρ⟩ := hb _ (by rintro _ ⟨x, rfl⟩; exact (f x).property) hA
  -- so the reduction lands in the level `K_α`
  let f' : graphClass → ↥(K ∩ {c | ρ c ≤ α}) := fun x ↦ ⟨f x, (f x).property, hρ _ ⟨x, rfl⟩⟩
  have hf' : Measurable f' := (measurable_subtypeVal.comp hf).subtype_mk
  apply not_measurableSet_classIso_of_borelComplete borelComplete_graphClass
  convert (ha α hα).preimage (hf'.prodMap hf') using 1
  ext p
  exact hfiso p.1 p.2

end TauCeti.RelationalConfiguration
