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
* `TauCeti.FunctionalConfiguration.borelComplete_preimage_rel_iff`: for a relational language, the
  functional configurations whose relational part lies in `K` form a Borel complete class exactly
  when `K` is Borel complete.
* `TauCeti.RelationalConfiguration.borelComplete_iff_forall_functional` and
  `TauCeti.FunctionalConfiguration.borelComplete_iff_forall_functional`: a class is Borel
  complete exactly when it receives isomorphism on every invariant Borel class of functional
  configurations of every countable language in `FirstOrder.Language.{0, 0}`.

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

/-- A class containing a Borel complete functional class is Borel complete. -/
theorem BorelComplete.mono {K₁ K : Set (FunctionalConfiguration L ℕ)} (hK : BorelComplete K₁)
    (h : K₁ ⊆ K) : BorelComplete K :=
  RelationalConfiguration.BorelComplete.mono hK (image_mono h)

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
      (FunctionalConfiguration.isomorphismInvariant_preimage_rel hi))

end RelationalConfiguration

namespace FunctionalConfiguration

variable {L : Language.{u, v}} [∀ n, Countable (L.Functions n)] [∀ n, Countable (L.Relations n)]
  {K K₂ : Set (FunctionalConfiguration L ℕ)}

/-- **A Borel complete functional class** receives isomorphism on every isomorphism-invariant Borel
class of functional configurations, for every countable language in any universes. -/
theorem BorelComplete.borelReducible (hK : BorelComplete K) {L' : Language.{u', v'}}
    [∀ n, Countable (L'.Functions n)] [∀ n, Countable (L'.Relations n)]
    {K' : Set (FunctionalConfiguration L' ℕ)} (hm : MeasurableSet K')
    (hi : IsomorphismInvariant K') : (classIso L' ℕ K').BorelReducible (classIso L ℕ K) :=
  (RelationalConfiguration.BorelComplete.borelReducible_functional hK hm hi).trans
    (Setoid.borelBireducible_iff.1 (borelBireducible_classIso_image_graphCode K)).2

/-- **Transfer.** If isomorphism on a Borel complete functional class is Borel reducible to
isomorphism on `K₂`, then `K₂` is Borel complete. -/
theorem BorelComplete.of_borelReducible (hK : BorelComplete K)
    (h : (classIso L ℕ K).BorelReducible (classIso L ℕ K₂)) : BorelComplete K₂ :=
  RelationalConfiguration.BorelComplete.of_borelReducible hK <|
    (Setoid.borelBireducible_iff.1 (borelBireducible_classIso_image_graphCode K)).2.trans <|
      h.trans (Setoid.borelBireducible_iff.1 (borelBireducible_classIso_image_graphCode K₂)).1

/-- Functional classes with Borel bireducible isomorphism relations are Borel complete together. -/
theorem borelComplete_iff_of_borelBireducible
    (h : (classIso L ℕ K).BorelBireducible (classIso L ℕ K₂)) :
    BorelComplete K ↔ BorelComplete K₂ :=
  ⟨fun hK => hK.of_borelReducible (Setoid.borelBireducible_iff.1 h).1,
    fun hK => hK.of_borelReducible (Setoid.borelBireducible_iff.1 h).2⟩

/-- A functional class is Borel complete exactly when it receives isomorphism on every
isomorphism-invariant Borel class of functional configurations of every language in
`FirstOrder.Language.{0, 0}` with countably many function and relation symbols of each arity. -/
theorem borelComplete_iff_forall_functional :
    BorelComplete K ↔ ∀ (L' : Language.{0, 0}) [∀ n, Countable (L'.Functions n)]
      [∀ n, Countable (L'.Relations n)] (K' : Set (FunctionalConfiguration L' ℕ)),
        MeasurableSet K' → IsomorphismInvariant K' →
          (classIso L' ℕ K').BorelReducible (classIso L ℕ K) := by
  rw [borelComplete_iff, RelationalConfiguration.borelComplete_iff_forall_functional]
  have h := Setoid.borelBireducible_iff.1 (borelBireducible_classIso_image_graphCode K)
  exact forall_congr' fun L' => forall_congr' fun _ => forall_congr' fun _ => forall_congr'
    fun K' => forall_congr' fun _ => forall_congr' fun _ => ⟨fun h' => h'.trans h.2,
      fun h' => h'.trans h.1⟩

/-- **Relational classes as functional classes.** For a relational language, the class of
functional configurations whose relational part lies in `K₀` is Borel complete exactly when `K₀`
is. -/
theorem borelComplete_preimage_rel_iff {L₀ : Language.{u, v}} [L₀.IsRelational]
    [∀ n, Countable (L₀.Relations n)] {K₀ : Set (RelationalConfiguration L₀ ℕ)} :
    BorelComplete (rel ⁻¹' K₀) ↔ RelationalConfiguration.BorelComplete K₀ :=
  RelationalConfiguration.borelComplete_iff_of_borelBireducible
    ((borelBireducible_classIso_image_graphCode _).symm.trans
      (borelBireducible_classIso_preimage_rel K₀))

end FunctionalConfiguration

end TauCeti
