/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.RelationalConfiguration.BorelComplete
public import TauCeti.ModelTheory.RelationalConfiguration.Functional.ClassIso

/-!
# Borel completeness for classes with function symbols

A class `K` of functional configurations on `ℕ`, for a language with function symbols, is
**Borel complete** when its image under the graph code is Borel complete in the sense of
`TauCeti.RelationalConfiguration.BorelComplete`. Isomorphism on `K` and on its graph codes are
Borel bireducible (`TauCeti.FunctionalConfiguration.borelBireducible_classIso_image_graphCode`),
so a Borel complete class, relational or functional, receives isomorphism on every isomorphism
invariant Borel class of every countable language, with or without function symbols. Conversely
every relational class is, up to Borel bireducibility of isomorphism, a class of functional
configurations with the empty function table. So quantifying over relational languages in the
definition of Borel completeness loses nothing: a class is Borel complete exactly when it receives
isomorphism on the invariant Borel classes of all countable languages.

## Main definitions

* `TauCeti.FunctionalConfiguration.BorelComplete K`: the class `K` of functional configurations
  is Borel complete.

## Main results

* `TauCeti.RelationalConfiguration.BorelComplete.borelReducible_functional`: a Borel complete
  relational class receives isomorphism on every invariant Borel class of functional
  configurations, for every countable language in any universes.
* `TauCeti.FunctionalConfiguration.BorelComplete.borelReducible`: the same for a Borel complete
  functional class.
* `TauCeti.FunctionalConfiguration.BorelComplete.of_borelReducible`: Borel completeness passes up
  the Borel reducibility order.
* `TauCeti.FunctionalConfiguration.borelBireducible_classIso_preimage_rel`: for a relational
  language, isomorphism on a class `K` of configurations and on the class of functional
  configurations whose relational part lies in `K` are Borel bireducible.
* `TauCeti.RelationalConfiguration.borelComplete_iff_forall_functional` and
  `TauCeti.FunctionalConfiguration.borelComplete_iff_forall`: a class is Borel complete exactly
  when it receives isomorphism on every invariant Borel class of functional configurations of every
  countable language in `FirstOrder.Language.{0, 0}`.

## References

* G. Paolini and S. Shelah, *Torsion-free abelian groups are Borel complete*, Ann. of Math. 199
  (2024), arXiv:2102.12371, Definition 1.6.
* R. Camerlo and S. Gao, *The completeness of the isomorphism relation for countable Boolean
  algebras*, Trans. Amer. Math. Soc. 353 (2001), §1.
-/

public section

universe u v u' v'

open FirstOrder FirstOrder.Language Set

namespace TauCeti

open RelationalConfiguration

namespace FunctionalConfiguration

section Relational

variable {L : Language.{u, v}} [L.IsRelational] {V : Type*}

/-- For a relational language there are no function arguments. -/
instance isEmpty_arg : IsEmpty (Arg L V) :=
  inferInstanceAs (IsEmpty (Σ f : (Σ l, L.Functions l), Fin f.1 → V))

/-- For a relational language a functional configuration is determined by its relational part. -/
theorem rel_injective : Function.Injective (rel : FunctionalConfiguration L V → _) :=
  fun _ _ h => ext (funext isEmptyElim) h

/-- For a relational language every relational configuration is the relational part of the
functional configuration with the empty table. -/
theorem rel_surjective : Function.Surjective (rel : FunctionalConfiguration L V → _) :=
  fun c => ⟨mk isEmptyElim c, rel_mk _ _⟩

/-- For a relational language two functional configurations are isomorphic exactly when their
relational parts are. -/
theorem isoSetoid_iff_isoSetoid_rel {F G : FunctionalConfiguration L V} :
    isoSetoid L V F G ↔ RelationalConfiguration.isoSetoid L V F.rel G.rel := by
  rw [isoSetoid_iff_exists_perm_smul_eq, RelationalConfiguration.isoSetoid_iff_exists_perm_smul_eq]
  refine exists_congr fun σ => ⟨fun h => h ▸ (rel_perm_smul σ F).symm, fun h => ?_⟩
  exact rel_injective ((rel_perm_smul σ F).trans h)

/-- For a relational language, the functional configurations whose relational part lies in an
invariant class form an invariant class. -/
theorem IsomorphismInvariant.preimage_rel {K : Set (RelationalConfiguration L V)}
    (hK : RelationalConfiguration.IsomorphismInvariant K) :
    IsomorphismInvariant (rel ⁻¹' K : Set (FunctionalConfiguration L V)) := by
  rw [isomorphismInvariant_iff]
  intro F G h hF
  exact RelationalConfiguration.isomorphismInvariant_iff.1 hK
    (isoSetoid_iff_isoSetoid_rel.1 h) hF

variable [TopologicalSpace V]

/-- **Relational classes as functional classes.** For a relational language, isomorphism on a
class `K` of configurations and isomorphism on the class of functional configurations whose
relational part lies in `K` are Borel bireducible, through the relational part and the empty
function table. -/
theorem borelBireducible_classIso_preimage_rel [∀ n, Countable (L.Relations n)] [Countable V]
    (K : Set (RelationalConfiguration L V)) :
    (classIso L V (rel ⁻¹' K)).BorelBireducible (RelationalConfiguration.classIso K) := by
  have hrel : Continuous (rel : FunctionalConfiguration L V → _) := continuous_rel
  have hmk : Continuous fun c : RelationalConfiguration L V =>
      (mk isEmptyElim c : FunctionalConfiguration L V) :=
    continuous_mk continuous_const continuous_id
  have hmem (c : K) : (mk isEmptyElim c.val : FunctionalConfiguration L V) ∈ rel ⁻¹' K := by
    simp [rel_mk]
  refine Setoid.borelBireducible_iff.2 ⟨Setoid.borelReducible_iff.2
    ⟨fun F => ⟨F.val.rel, F.property⟩, (hrel.measurable.comp measurable_subtypeVal).subtype_mk,
      fun F G => ?_⟩, Setoid.borelReducible_iff.2
    ⟨fun c => ⟨mk isEmptyElim c.val, hmem c⟩,
      (hmk.measurable.comp measurable_subtypeVal).subtype_mk (h := hmem), fun c d => ?_⟩⟩
  · rw [classIso_apply, RelationalConfiguration.classIso_apply, isoSetoid_iff_isoSetoid_rel]
  · rw [classIso_apply, RelationalConfiguration.classIso_apply, isoSetoid_iff_isoSetoid_rel,
      rel_mk, rel_mk]

end Relational

variable {L : Language.{u, v}}

/-- A class `K` of functional configurations on `ℕ` is **Borel complete** when its image under the
graph code, a class of configurations of the relational language `L.graphLanguage`, is Borel
complete. -/
def BorelComplete (K : Set (FunctionalConfiguration L ℕ)) : Prop :=
  RelationalConfiguration.BorelComplete (graphCode '' K)

/-- Unfolding lemma for `FunctionalConfiguration.BorelComplete`. -/
theorem borelComplete_iff {K : Set (FunctionalConfiguration L ℕ)} :
    BorelComplete K ↔ RelationalConfiguration.BorelComplete (graphCode '' K) :=
  Iff.rfl

end FunctionalConfiguration

namespace RelationalConfiguration

variable {L₀ : Language.{u, v}} [L₀.IsRelational] {K₀ : Set (RelationalConfiguration L₀ ℕ)}

/-- **Function symbols lose nothing.** A Borel complete class of configurations receives
isomorphism on every isomorphism-invariant Borel class of functional configurations, for every
language in any universes with countably many function and relation symbols of each arity. -/
theorem BorelComplete.borelReducible_functional (hK₀ : BorelComplete K₀) {L' : Language.{u', v'}}
    [∀ n, Countable (L'.Functions n)] [∀ n, Countable (L'.Relations n)]
    {K' : Set (FunctionalConfiguration L' ℕ)} (hm : MeasurableSet K')
    (hi : FunctionalConfiguration.IsomorphismInvariant K') :
    (FunctionalConfiguration.classIso L' ℕ K').BorelReducible (classIso K₀) :=
  (Setoid.borelBireducible_iff.1
    (FunctionalConfiguration.borelBireducible_classIso_image_graphCode K')).1.trans
    (hK₀.borelReducible (FunctionalConfiguration.measurableSet_image_graphCode hm)
      (FunctionalConfiguration.isomorphismInvariant_image_graphCode hi))

/-- **Borel completeness through functional classes.** A class of configurations is Borel complete
exactly when it receives isomorphism on every isomorphism-invariant Borel class of functional
configurations of every language in `FirstOrder.Language.{0, 0}` with countably many function and
relation symbols of each arity. -/
theorem borelComplete_iff_forall_functional :
    BorelComplete K₀ ↔ ∀ (L' : Language.{0, 0}) [∀ n, Countable (L'.Functions n)]
      [∀ n, Countable (L'.Relations n)] (K' : Set (FunctionalConfiguration L' ℕ)),
        MeasurableSet K' → FunctionalConfiguration.IsomorphismInvariant K' →
          (FunctionalConfiguration.classIso L' ℕ K').BorelReducible (classIso K₀) := by
  refine ⟨fun hK₀ L' _ _ K' hm hi => hK₀.borelReducible_functional hm hi,
    fun h => borelComplete_iff.2 fun L' _ _ K' hm hi => ?_⟩
  exact (Setoid.borelBireducible_iff.1
    (FunctionalConfiguration.borelBireducible_classIso_preimage_rel K')).2.trans
    (h L' _ (FunctionalConfiguration.continuous_rel.measurable hm)
      (FunctionalConfiguration.IsomorphismInvariant.preimage_rel hi))

end RelationalConfiguration

namespace FunctionalConfiguration

variable {L : Language.{u, v}} [∀ n, Countable (L.Functions n)] [∀ n, Countable (L.Relations n)]
  {K K₂ : Set (FunctionalConfiguration L ℕ)}

/-- Isomorphism on a class of functional configurations and on its graph codes are Borel
bireducible; on `ℕ`, as used for Borel completeness. -/
private theorem borelBireducible_graphCode (K : Set (FunctionalConfiguration L ℕ)) :
    (classIso L ℕ K).BorelBireducible (RelationalConfiguration.classIso (graphCode '' K)) :=
  borelBireducible_classIso_image_graphCode K

/-- **A Borel complete functional class** receives isomorphism on every isomorphism-invariant Borel
class of functional configurations, for every countable language in any universes. -/
theorem BorelComplete.borelReducible (hK : BorelComplete K) {L' : Language.{u', v'}}
    [∀ n, Countable (L'.Functions n)] [∀ n, Countable (L'.Relations n)]
    {K' : Set (FunctionalConfiguration L' ℕ)} (hm : MeasurableSet K')
    (hi : IsomorphismInvariant K') : (classIso L' ℕ K').BorelReducible (classIso L ℕ K) :=
  (RelationalConfiguration.BorelComplete.borelReducible_functional hK hm hi).trans
    (Setoid.borelBireducible_iff.1 (borelBireducible_graphCode K)).2

/-- **Transfer.** If isomorphism on a Borel complete functional class is Borel reducible to
isomorphism on `K₂`, then `K₂` is Borel complete. -/
theorem BorelComplete.of_borelReducible (hK : BorelComplete K)
    (h : (classIso L ℕ K).BorelReducible (classIso L ℕ K₂)) : BorelComplete K₂ :=
  RelationalConfiguration.BorelComplete.of_borelReducible hK <|
    (Setoid.borelBireducible_iff.1 (borelBireducible_graphCode K)).2.trans <|
      h.trans (Setoid.borelBireducible_iff.1 (borelBireducible_graphCode K₂)).1

/-- A functional class is Borel complete exactly when it receives isomorphism on every
isomorphism-invariant Borel class of functional configurations of every language in
`FirstOrder.Language.{0, 0}` with countably many function and relation symbols of each arity. -/
theorem borelComplete_iff_forall :
    BorelComplete K ↔ ∀ (L' : Language.{0, 0}) [∀ n, Countable (L'.Functions n)]
      [∀ n, Countable (L'.Relations n)] (K' : Set (FunctionalConfiguration L' ℕ)),
        MeasurableSet K' → IsomorphismInvariant K' →
          (classIso L' ℕ K').BorelReducible (classIso L ℕ K) := by
  rw [borelComplete_iff, RelationalConfiguration.borelComplete_iff_forall_functional]
  have h := Setoid.borelBireducible_iff.1 (borelBireducible_graphCode K)
  exact forall_congr' fun L' => forall_congr' fun _ => forall_congr' fun _ => forall_congr'
    fun K' => forall_congr' fun _ => forall_congr' fun _ => ⟨fun h' => h'.trans h.2,
      fun h' => h'.trans h.1⟩

end FunctionalConfiguration

end TauCeti
