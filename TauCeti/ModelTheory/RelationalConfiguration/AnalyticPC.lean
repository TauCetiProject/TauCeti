/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Interpolation.PCClass
public import TauCeti.ModelTheory.RelationalConfiguration.Isomorphism
public import TauCeti.ModelTheory.RelationalConfiguration.LanguageMap
public import TauCeti.ModelTheory.RelationalConfiguration.PCSentence
public import TauCeti.ModelTheory.RelationalConfiguration.Topology
public import TauCeti.ModelTheory.Infinitary.Symbols

/-!
# Projective classes of codes are analytic

Let `g : L →ᴸ L'` be a map of relational languages and `Θ` an `L_{ω₁ω}` sentence of `L'`. The
codes `c` on a carrier `V` whose decoded `L`-structure lies in the projective class of `Θ` along
`g` (`LHom.PCMem`) are exactly the reducts along `g` of the codes satisfying `Θ`
(`FirstOrder.Language.LHom.setOf_pcMem_eq_image_modelsOf`). When `L'` has countably many relation
symbols of each arity and `V` is countable, the model class of `Θ` is a Borel subset of a Polish
space and the reduct map is continuous, so this class of codes is analytic
(`FirstOrder.Language.LHom.analyticSet_setOf_pcMem`). This is the converse direction of the
characterization of invariant analytic classes as projective classes. No countability is needed
for `L` itself.

The forward direction (an invariant analytic class is a projective class) holds when `L` has
countably many relation symbols of each arity: an analytic class of codes on `ℕ` is the projection
of the body of a tree `T` read through the query code, and invariance lets the enumeration of a
model of `pcSentence T` be absorbed (`TauCeti.RelationalConfiguration.analyticSet_iff_exists_pc`).
The countability of `L` cannot be dropped. A single sentence mentions only countably many relation
symbols, so if `L` has uncountably many relation symbols then on a nonempty carrier no
projective class along an injective `g` is a single code
(`FirstOrder.Language.LHom.setOf_pcMem_ne_singleton`): reversing the value of a relation symbol in
the image of `g` that the sentence does not mention gives a second member. Singletons are analytic,
and the singleton of a code fixed by every permutation of the carrier is isomorphism invariant.

## Main results

* `FirstOrder.Language.LHom.setOf_pcMem_eq_image_modelsOf`: projective classes of codes are the
  images of model classes under the reduct map.
* `FirstOrder.Language.LHom.analyticSet_setOf_pcMem`: they are analytic.
* `TauCeti.RelationalConfiguration.analyticSet_iff_exists_pc`: an isomorphism-invariant class of
  codes on `ℕ` is analytic exactly when it is a projective class along `LHom.sumInl`.
* `FirstOrder.Language.LHom.setOf_pcMem_ne_singleton`: with uncountably many relation symbols, no
  projective class along an injective language map is a singleton.
-/

public section

universe u v u' v' w

open TauCeti TauCeti.RelationalConfiguration MeasureTheory

namespace FirstOrder.Language.LHom

variable {L : Language.{u, v}} {L' : Language.{u', v'}} [L.IsRelational] [L'.IsRelational]
  {V : Type w}

/-- **Projective classes of codes are images of model classes.** A code on `V` lies in the
projective class of `Θ` along `g` exactly when it is the reduct along `g` of a code satisfying
`Θ`. -/
theorem setOf_pcMem_eq_image_modelsOf (g : L →ᴸ L') (Θ : L'.Sentenceω) :
    {c : RelationalConfiguration L V | @PCMem L L' g Θ V c.toStructure} =
      g.reductConfiguration '' modelsOf Θ := by
  ext c
  constructor
  · intro hc
    obtain ⟨S, hS, hΘ⟩ := (@pcMem_iff _ _ g Θ V c.toStructure).1 hc
    refine ⟨@ofStructure L' V S, by rwa [mem_modelsOf, toStructure_ofStructure], ?_⟩
    apply equivStructure.injective
    rw [equivStructure_apply, equivStructure_apply, toStructure_reductConfiguration,
      toStructure_ofStructure]
    exact @reduct_eq_of_isExpansionOn _ _ g V c.toStructure S hS
  · rintro ⟨d, hd, rfl⟩
    refine (@pcMem_iff _ _ g Θ V (g.reductConfiguration d).toStructure).2
      ⟨d.toStructure, ?_, mem_modelsOf.1 hd⟩
    have := @isExpansionOn_reduct L L' g V d.toStructure
    rwa [← toStructure_reductConfiguration g d] at this

/-- **Projective classes of codes are analytic.** For a map `g : L →ᴸ L'` of relational languages,
`L'` with countably many relation symbols of each arity, and a countable carrier `V`, the codes on
`V` whose decoded structures lie in the projective class of an `L_{ω₁ω}` sentence `Θ` along `g`
form an analytic set: the image of the Borel set `modelsOf Θ` under the continuous reduct map. -/
theorem analyticSet_setOf_pcMem [∀ n, Countable (L'.Relations n)] [Countable V] (g : L →ᴸ L')
    (Θ : L'.Sentenceω) :
    AnalyticSet {c : RelationalConfiguration L V | @PCMem L L' g Θ V c.toStructure} := by
  rw [setOf_pcMem_eq_image_modelsOf]
  exact (measurableSet_modelsOf Θ).analyticSet.image_of_continuous
    g.continuous_reductConfiguration

/-- The structure `S` with the relation symbol `R₀` reversed: `R₀(x)` holds exactly when it fails
in `S`, and every other symbol is read as in `S`. -/
@[instance_reducible]
private noncomputable def reverseRelation {M : Type w} (S : L.Structure M) {k : ℕ}
    (R₀ : L.Relations k) : L.Structure M where
  funMap f := isEmptyElim f
  RelMap {n} Q xs := haveI := Classical.propDecidable
    if (⟨n, Q⟩ : Σ n, L.Relations n) = ⟨k, R₀⟩ then ¬ @Structure.RelMap L M S n Q xs
    else @Structure.RelMap L M S n Q xs

omit [L'.IsRelational] in
/-- Reversing `R₀` does not change the other relation symbols. -/
private theorem relMap_reverseRelation_of_ne {M : Type w} (S : L.Structure M) {k n : ℕ}
    {R₀ : L.Relations k} {Q : L.Relations n} (h : (⟨n, Q⟩ : Σ n, L.Relations n) ≠ ⟨k, R₀⟩)
    (xs : Fin n → M) :
    @Structure.RelMap L M (reverseRelation S R₀) n Q xs ↔ @Structure.RelMap L M S n Q xs :=
  Iff.of_eq (ite_eq_right_of_eq_false _ _ (eq_false h))

omit [L'.IsRelational] in
/-- Reversing `R₀` negates it. -/
private theorem relMap_reverseRelation_self {M : Type w} (S : L.Structure M) {k : ℕ}
    (R₀ : L.Relations k) (xs : Fin k → M) :
    @Structure.RelMap L M (reverseRelation S R₀) k R₀ xs ↔ ¬ @Structure.RelMap L M S k R₀ xs :=
  Iff.of_eq (ite_eq_left_of_eq_true _ _ (eq_true rfl))

/-- **No projective class is a single code when there are uncountably many symbols.** If the
relational language `L` has uncountably many relation symbols and `g : L →ᴸ L'` is injective, then
on a nonempty carrier the projective class of a sentence `ψ` along `g` is never a single code:
`ψ` mentions only countably many relation symbols, and reversing the value of an unmentioned
symbol in the image of `g` in an expansion satisfying `ψ` gives a second member. -/
theorem setOf_pcMem_ne_singleton [Nonempty V] (g : L →ᴸ L') (hg : g.Injective)
    (hL : ¬ Countable (Σ n, L.Relations n)) (ψ : L'.Sentenceω) (c : RelationalConfiguration L V) :
    {d : RelationalConfiguration L V | @PCMem L L' g ψ V d.toStructure} ≠ {c} := by
  intro h
  rw [setOf_pcMem_eq_image_modelsOf] at h
  obtain ⟨e, he, hec⟩ := (Set.ext_iff.1 h c).2 rfl
  -- Some relation symbol of `L` is not mentioned, through `g`, by `ψ`.
  let i : (Σ n, L.Relations n) → Σ n, L'.Relations n := Sigma.map id fun _ R => g.onRelation R
  have hi : Function.Injective i := Function.injective_id.sigma_map fun _ => hg.onRelation
  obtain ⟨⟨k, R⟩, hR⟩ : ∃ R, i R ∉ BoundedFormulaInf.relationsIn ψ := by
    by_contra! hall
    exact hL (Set.countable_univ_iff.1
      ((ψ.relationsIn_countable.preimage hi).mono fun R _ => hall R))
  -- Reverse the value of `g R` in the structure decoded from `e`.
  let S' : L'.Structure V := reverseRelation e.toStructure (g.onRelation R)
  have hψ : @SentenceInf.Realize _ ℕ ψ V S' := by
    refine (SentenceInf.realize_congr_of_agreeOn ψ S' e.toStructure (fun f => isEmptyElim f)
      fun Q hQ xs => relMap_reverseRelation_of_ne _ (fun hQR => hR ?_) xs).2 (mem_modelsOf.1 he)
    rwa [hQR] at hQ
  have he' : @ofStructure L' V S' ∈ modelsOf ψ := by
    rw [mem_modelsOf, toStructure_ofStructure]
    exact hψ
  obtain ⟨x⟩ : Nonempty (Fin k → V) := inferInstance
  refine absurd ((Set.ext_iff.1 h _).1 ⟨_, he', rfl⟩) fun hc => ?_
  -- The two reducts agree at the atom `R(x)`, but `S'` reverses `(g R)(x)`.
  have hx := congrArg (fun d => d.eval (atom R x)) (hc.trans hec.symm)
  have hS' := relMap_reverseRelation_self e.toStructure (g.onRelation R) x
  simp only [eval_reductConfiguration, onAtom_atom, eval_ofStructure] at hx
  rw [toStructure_relMap, ← hx] at hS'
  simp only [decide_eq_true_eq, iff_not_self] at hS'

end FirstOrder.Language.LHom

namespace TauCeti.RelationalConfiguration

open FirstOrder FirstOrder.Language

variable {L : FirstOrder.Language.{u, v}} [L.IsRelational] [∀ n, Countable (L.Relations n)]

/-- **The projective class of the PC sentence of an analytic class.** If `B` is the projection of
the body of `T` read through the query code and `B` is isomorphism invariant, then `B` is the
projective class of `pcSentence T` along `LHom.sumInl`. -/
theorem eq_setOf_pcMem_pcSentence {B : Set (RelationalConfiguration L ℕ)}
    (hB : IsomorphismInvariant B) {T : Descriptive.tree (Bool × ℕ)}
    (hT : B = {c | ∃ g : ℕ → ℕ, (fun n => (queryCode c n, g n)) ∈ Descriptive.Tree.body T}) :
    B = {c | @LHom.PCMem L _ LHom.sumInl (pcSentence T) ℕ c.toStructure} := by
  ext c
  change c ∈ B ↔ @LHom.PCMem L _ LHom.sumInl (pcSentence T) ℕ c.toStructure
  rw [@pcMem_pcSentence_iff L _ ℕ c.toStructure T]
  constructor
  · intro hc
    obtain ⟨g, hg⟩ := hT ▸ hc
    refine ⟨Equiv.refl ℕ, g, ?_⟩
    rwa [@Equiv.encodeVia_refl L ℕ c.toStructure, ofStructure_toStructure]
  · rintro ⟨e, g, hg⟩
    rw [← perm_smul_eq_encodeVia (σ := (e : Equiv.Perm ℕ))] at hg
    refine (hB.mem_iff (isoSetoid_perm_smul (e : Equiv.Perm ℕ) c)).2 ?_
    rw [hT]
    exact ⟨g, hg⟩

/-- **Invariant analytic classes are projective classes.** For a relational language `L` with
countably many relation symbols of each arity, an isomorphism-invariant set `B` of codes on `ℕ` is
analytic exactly when it is the class of codes whose decoded structures lie in the projective
class of a single `L_{ω₁ω}` sentence `ψ` of `L.sum pcWitnessLanguage` along `LHom.sumInl`. The
forward direction takes `ψ = pcSentence T` for a tree `T` representing `B`; the converse is
`FirstOrder.Language.LHom.analyticSet_setOf_pcMem`. -/
theorem analyticSet_iff_exists_pc {B : Set (RelationalConfiguration L ℕ)}
    (hB : IsomorphismInvariant B) :
    AnalyticSet B ↔ ∃ ψ : (L.sum pcWitnessLanguage).Sentenceω,
      B = {c | @LHom.PCMem L _ LHom.sumInl ψ ℕ c.toStructure} := by
  refine ⟨fun h => ?_, fun ⟨ψ, hψ⟩ => ?_⟩
  · obtain ⟨T, hT⟩ := exists_tree_of_analyticSet h
    exact ⟨pcSentence T, eq_setOf_pcMem_pcSentence hB hT⟩
  · have : ∀ n, Countable ((L.sum pcWitnessLanguage).Relations n) := fun n =>
      inferInstanceAs (Countable (L.Relations n ⊕ pcWitnessLanguage.Relations n))
    exact hψ ▸ LHom.analyticSet_setOf_pcMem LHom.sumInl ψ

end TauCeti.RelationalConfiguration
