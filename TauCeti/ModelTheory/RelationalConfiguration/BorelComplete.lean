/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.RelationalConfiguration.ClassIso
public import TauCeti.ModelTheory.RelationalConfiguration.LanguageMap
public import TauCeti.ModelTheory.Infinitary.SmallPresentation

/-!
# Borel complete classes of configurations

A class `K` of configurations on `ℕ` is **Borel complete** when isomorphism on every isomorphism
invariant Borel class, in every countable relational language, is Borel reducible to isomorphism
on `K`. Such a class sits at the top of the Borel reducibility order among isomorphism relations of
classes of countable structures: classifying its members up to isomorphism is as hard as
classifying the countable models of any `L_{ω₁ω}` sentence. Countable graphs and countable linear
orders are the classical examples (Friedman–Stanley).

The source languages in the definition live in `FirstOrder.Language.{0, 0}`. Every countable
language in any universes has a small presentation in universe `0`, and transport along a language
equivalence preserves and reflects isomorphism, so any other universe gives the same notion
(`TauCeti.RelationalConfiguration.BorelComplete.borelReducible`). For the same reason Borel
completeness does not depend on the naming of the symbols of the target language. Borel
completeness passes up the Borel reducibility order and so to larger classes. It can also be
tested on the whole coding space of each countable relational language, or on its Borel classes,
invariant or not.

## Main definitions

* `TauCeti.RelationalConfiguration.BorelComplete K`: the class `K` is Borel complete.

## Main results

* `TauCeti.RelationalConfiguration.BorelComplete.of_borelReducible` and
  `TauCeti.RelationalConfiguration.BorelComplete.mono`: Borel completeness passes up the Borel
  reducibility order, and to larger classes.
* `TauCeti.RelationalConfiguration.borelComplete_iff_of_borelBireducible`: Borel bireducible
  classes are Borel complete together.
* `TauCeti.RelationalConfiguration.not_borelComplete_empty`: the empty class is not Borel
  complete.
* `TauCeti.RelationalConfiguration.BorelComplete.borelReducible`: a Borel complete class receives
  isomorphism on invariant Borel classes of countable relational languages in any universes.
* `TauCeti.RelationalConfiguration.borelComplete_image_onConfiguration_iff`: Borel completeness
  is invariant under renaming the symbols of the target language.
* `TauCeti.RelationalConfiguration.borelComplete_iff_forall_isoSetoid` and
  `TauCeti.RelationalConfiguration.borelComplete_iff_forall_measurableSet`: it suffices to reduce
  isomorphism on the whole coding space of each countable relational language, and then
  isomorphism on every Borel class, invariant or not, reduces.

## References

* G. Paolini and S. Shelah, *Torsion-free abelian groups are Borel complete*, Ann. of Math. 199
  (2024), arXiv:2102.12371, Definition 1.6.
* R. Camerlo and S. Gao, *The completeness of the isomorphism relation for countable Boolean
  algebras*, Trans. Amer. Math. Soc. 353 (2001), §1.
* H. Friedman and L. Stanley, *A Borel reducibility theory for classes of countable structures*,
  J. Symbolic Logic 54 (1989).
-/

public section

universe u v u' v' u₂ v₂

open FirstOrder FirstOrder.Language Set

namespace TauCeti.RelationalConfiguration

variable {L : Language.{u, v}} [L.IsRelational] {L₂ : Language.{u₂, v₂}} [L₂.IsRelational]
  {K : Set (RelationalConfiguration L ℕ)} {K₂ : Set (RelationalConfiguration L₂ ℕ)}

/-- A class `K` of configurations on `ℕ` is **Borel complete** when, for every relational language
`L'` in `FirstOrder.Language.{0, 0}` with countably many relation symbols of each arity and every
isomorphism-invariant Borel class `K'` of configurations of `L'` on `ℕ`, isomorphism on `K'` is
Borel reducible to isomorphism on `K`. The universe of the source languages is immaterial
(`BorelComplete.borelReducible`). -/
def BorelComplete (K : Set (RelationalConfiguration L ℕ)) : Prop :=
  ∀ (L' : Language.{0, 0}) [L'.IsRelational] [∀ n, Countable (L'.Relations n)]
    (K' : Set (RelationalConfiguration L' ℕ)), MeasurableSet K' → IsomorphismInvariant K' →
      (classIso K').BorelReducible (classIso K)

/-- Unfolding lemma for `BorelComplete`. -/
theorem borelComplete_iff :
    BorelComplete K ↔ ∀ (L' : Language.{0, 0}) [L'.IsRelational]
      [∀ n, Countable (L'.Relations n)] (K' : Set (RelationalConfiguration L' ℕ)),
        MeasurableSet K' → IsomorphismInvariant K' → (classIso K').BorelReducible (classIso K) :=
  Iff.rfl

/-- **Transfer.** If isomorphism on a Borel complete class is Borel reducible to isomorphism on
`K₂`, then `K₂` is Borel complete. -/
theorem BorelComplete.of_borelReducible (hK : BorelComplete K)
    (h : (classIso K).BorelReducible (classIso K₂)) : BorelComplete K₂ :=
  fun L' _ _ K' hm hi => (hK L' K' hm hi).trans h

/-- A class containing a Borel complete class is Borel complete. -/
theorem BorelComplete.mono {K₁ : Set (RelationalConfiguration L ℕ)} (hK : BorelComplete K₁)
    (h : K₁ ⊆ K) : BorelComplete K :=
  hK.of_borelReducible (borelReducible_classIso_of_subset h)

/-- Classes with Borel bireducible isomorphism relations are Borel complete together. -/
theorem borelComplete_iff_of_borelBireducible
    (h : (classIso K).BorelBireducible (classIso K₂)) : BorelComplete K ↔ BorelComplete K₂ :=
  ⟨fun hK => hK.of_borelReducible (Setoid.borelBireducible_iff.1 h).1,
    fun hK => hK.of_borelReducible (Setoid.borelBireducible_iff.1 h).2⟩

/-- The empty class is not Borel complete: the whole coding space of the empty language is
nonempty, and no map from it to the empty class exists. -/
theorem not_borelComplete_empty : ¬ BorelComplete (∅ : Set (RelationalConfiguration L ℕ)) := by
  intro h
  have := borelReducible_classIso_empty_iff.1 <|
    h Language.empty univ MeasurableSet.univ isomorphismInvariant_univ
  exact (eq_empty_iff_forall_notMem.1 this) (mk fun _ => false) (mem_univ _)

/-- **Universes.** A Borel complete class receives isomorphism on every isomorphism-invariant
Borel class of a countable relational language in any universes: transport the class to the small
presentation of its language, in universe `0`. -/
theorem BorelComplete.borelReducible {L' : Language.{u', v'}} [L'.IsRelational]
    [∀ n, Countable (L'.Relations n)] {K' : Set (RelationalConfiguration L' ℕ)}
    (hK : BorelComplete K) (hm : MeasurableSet K') (hi : IsomorphismInvariant K') :
    (classIso K').BorelReducible (classIso K) := by
  let e := L'.smallPresentationEquiv
  have hiso : ∀ c d, isoSetoid _ ℕ (e.onConfigurationMeasurableEquiv c)
      (e.onConfigurationMeasurableEquiv d) ↔ isoSetoid L' ℕ c d := fun _ _ => by
    rw [LEquiv.coe_onConfigurationMeasurableEquiv, e.isoSetoid_onConfiguration_iff]
  refine (Setoid.borelBireducible_iff.1 (borelBireducible_classIso_image _ hiso K')).1.trans <|
    hK _ _ ?_ ?_
  · exact e.onConfigurationMeasurableEquiv.measurableSet_image.2 hm
  · exact hi.image e.onConfigurationMeasurableEquiv.toEquiv hiso

/-- **Renaming.** Borel completeness is invariant under renaming the symbols of the target
language along a language equivalence. -/
@[simp]
theorem borelComplete_image_onConfiguration_iff (e : L ≃ᴸ L₂) :
    BorelComplete (e.onConfiguration '' K) ↔ BorelComplete K := by
  rw [← LEquiv.coe_onConfigurationMeasurableEquiv]
  exact (borelComplete_iff_of_borelBireducible (borelBireducible_classIso_image _
    (fun _ _ => by simp [e.isoSetoid_onConfiguration_iff]) K)).symm

/-- A class is Borel complete exactly when isomorphism on the whole coding space of every
countable relational language in `FirstOrder.Language.{0, 0}` is Borel reducible to isomorphism on
the class. -/
theorem borelComplete_iff_forall_isoSetoid :
    BorelComplete K ↔ ∀ (L' : Language.{0, 0}) [L'.IsRelational]
      [∀ n, Countable (L'.Relations n)], (isoSetoid L' ℕ).BorelReducible (classIso K) := by
  refine ⟨fun hK L' _ _ => ?_, fun h L' _ _ K' _ _ => ?_⟩
  · exact (Setoid.borelBireducible_iff.1 borelBireducible_classIso_univ).2.trans
      (hK L' univ MeasurableSet.univ isomorphismInvariant_univ)
  · exact (borelReducible_classIso_of_subset (subset_univ K')).trans
      ((Setoid.borelBireducible_iff.1 borelBireducible_classIso_univ).1.trans (h L'))

/-- A class is Borel complete exactly when it receives isomorphism on every Borel class, invariant
or not, of every countable relational language in `FirstOrder.Language.{0, 0}`. -/
theorem borelComplete_iff_forall_measurableSet :
    BorelComplete K ↔ ∀ (L' : Language.{0, 0}) [L'.IsRelational]
      [∀ n, Countable (L'.Relations n)] (B : Set (RelationalConfiguration L' ℕ)),
        MeasurableSet B → (classIso B).BorelReducible (classIso K) := by
  refine ⟨fun hK L' _ _ B _ => ?_, fun h L' _ _ K' hm _ => h L' K' hm⟩
  exact (borelReducible_classIso_of_subset (subset_univ B)).trans
    (hK L' univ MeasurableSet.univ isomorphismInvariant_univ)

end TauCeti.RelationalConfiguration
