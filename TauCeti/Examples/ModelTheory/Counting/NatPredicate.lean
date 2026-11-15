/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Basic
public import TauCeti.ModelTheory.Counting.Classes
public import TauCeti.ModelTheory.Scott.NatPredicate

/-!
# Continuum many one-element models

In the language with unary predicates indexed by `ℕ`, the sentence asserting that there is
exactly one element has continuum many countable models up to isomorphism. Each model records
an arbitrary sequence of truth values for the predicates. The configurations on `Fin 1` form
a copy of Cantor space, and no two distinct configurations are isomorphic.

The perfect-set witness is entirely on `Fin 1`: the sentence has no models on `ℕ`, on the empty
carrier, or on any `Fin n` with `n ≠ 1`. Thus counting only models on `ℕ` would miss all its
models, not merely a countable contribution. In particular, a vacuous bound on ranks of its
models on `ℕ` cannot rule out continuum many finite models.

The models are `TauCeti.natPredicateLanguage`-structures built from `TauCeti.natPredicateStructure`.
The cardinality assertion uses Mathlib's finitary sentences `FirstOrder.Language.Sentence.cardGe`.
-/

public section

open FirstOrder FirstOrder.Language Cardinal Set

namespace TauCeti.NatPredicateCounting

open RelationalConfiguration

/-- The sentence asserting that there is exactly one element, in the language of countably many
unary predicates. It places no restrictions on the predicates. -/
def oneElementSentence : natPredicateLanguage.Sentenceω :=
  (Sentence.cardGe natPredicateLanguage 1).toInf ⊓
    (Sentence.cardGe natPredicateLanguage 2).toInf.not

/-- The sentence holds exactly on carriers of cardinality one, including when the carrier lies
in a larger universe. -/
@[simp]
theorem realize_oneElementSentence_iff {M : Type*} [natPredicateLanguage.Structure M] :
    SentenceInf.Realize oneElementSentence M ↔ #M = 1 := by
  simp only [oneElementSentence, SentenceInf.realize_inf, SentenceInf.realize_not,
    Sentence.realize_toInf, Sentence.realize_cardGe, Nat.cast_one, Nat.cast_ofNat,
    not_le]
  -- Express `2` as a successor to apply the cardinal bound for a finite successor.
  rw [show (2 : Cardinal) = (1 : ℕ) + 1 by norm_num, Cardinal.lt_natCast_add_one_iff]
  exact ⟨fun h => le_antisymm h.2 h.1, fun h => by simp [h]⟩

/-- Every configuration on the one-element carrier satisfies the sentence. -/
@[simp]
theorem modelsOf_oneElementSentence_fin_one :
    modelsOf (V := Fin 1) oneElementSentence = Set.univ := by
  ext c
  simp

/-- The one-element sentence has no models on the countably infinite carrier `ℕ`. -/
@[simp]
theorem modelsOf_oneElementSentence_nat :
    modelsOf (V := ℕ) oneElementSentence = ∅ := by
  ext c
  simp [one_lt_aleph0.ne']

/-- No finite tier other than `Fin 1` contributes a model, including the empty tier. -/
@[simp]
theorem modelsOf_oneElementSentence_fin {n : ℕ} (hn : n ≠ 1) :
    modelsOf (V := Fin n) oneElementSentence = ∅ := by
  ext c
  simp [hn]

private noncomputable def code (z : ℕ → Bool) :
    RelationalConfiguration natPredicateLanguage (Fin 1) :=
  letI := natPredicateStructure {i | z i = true}
  (Equiv.ofUnique Unit (Fin 1)).encodeVia

private theorem eval_code (z : ℕ → Bool) (i : ℕ) (x : Fin 1 → Fin 1) :
    (code z).eval (atom (NatPredicateRel.pred i) x) = z i := by
  exact (@Equiv.eval_encodeVia natPredicateLanguage Unit (Fin 1)
    (natPredicateStructure {i | z i = true}) (Equiv.ofUnique Unit (Fin 1)) 1
    (NatPredicateRel.pred i) x).trans (by simp [relMap_natPredicateStructure])

/-- A Boolean sequence specifies the truth values of all the unary predicates on `Fin 1`.
This is a homeomorphism: every one-element configuration is obtained uniquely this way. -/
noncomputable def configuration :
    (ℕ → Bool) ≃ₜ RelationalConfiguration natPredicateLanguage (Fin 1) where
  toFun := code
  invFun c i := c.eval (atom (NatPredicateRel.pred i) (fun _ => 0))
  left_inv z := funext fun i => eval_code z i _
  right_inv c := by
    apply RelationalConfiguration.ext
    intro a
    induction a using Atom.induction_atom with
    | h R x =>
      cases R with
      | pred i =>
        -- Every tuple into `Fin 1` is the constant tuple used by the inverse map.
        have hx : x = fun _ => (0 : Fin 1) := Subsingleton.elim _ _
        simp [eval_code, hx]
  continuous_toFun := continuous_iff.2 fun a => by
    induction a using Atom.induction_atom with
    | h R x =>
      cases R with
      | pred i => simpa only [eval_code] using (continuous_apply i :
          Continuous fun z : ℕ → Bool => z i)
  continuous_invFun := continuous_pi fun i => continuous_eval _

/-- The coordinate for predicate `i` is the `i`th bit, independently of the argument tuple. -/
@[simp]
theorem eval_configuration (z : ℕ → Bool) (i : ℕ) (x : Fin 1 → Fin 1) :
    (configuration z).eval (atom (NatPredicateRel.pred i) x) = z i := by
  exact eval_code z i x

/-- The inverse homeomorphism reads the truth values of the unary predicates. -/
@[simp]
theorem configuration_symm_apply (c : RelationalConfiguration natPredicateLanguage (Fin 1))
    (i : ℕ) : configuration.symm c i = c.eval (atom (NatPredicateRel.pred i) (fun _ => 0)) :=
  (rfl)

/-- Isomorphism in this Cantor family is equality of the truth sequences: a one-element carrier
has no nontrivial permutation that could change the predicates. -/
@[simp]
theorem isoSetoid_configuration_iff (z w : ℕ → Bool) :
    isoSetoid natPredicateLanguage (Fin 1) (configuration z) (configuration w) ↔ z = w := by
  constructor
  · intro h
    obtain ⟨σ, hσ⟩ := isoSetoid_iff_exists_perm_smul_eq.1 h
    have hs : σ = 1 := Subsingleton.elim _ _
    rw [hs, one_smul] at hσ
    exact configuration.injective hσ
  · rintro rfl
    exact (isoSetoid natPredicateLanguage (Fin 1)).refl _

/-- The one-element models contain a continuous Cantor family of pairwise non-isomorphic
structures, explicitly given by `configuration`. -/
theorem hasCantorAntichainOn_oneElementSentence_fin_one :
    (isoSetoid natPredicateLanguage (Fin 1)).HasCantorAntichainOn
      (modelsOf oneElementSentence) := by
  apply Setoid.hasCantorAntichainOn_iff.2
  refine ⟨configuration, configuration.continuous, fun z => ?_, fun z w hzw h => ?_⟩
  · simp
  · exact hzw ((isoSetoid_configuration_iff z w).1 h)

/-- There is a nonempty perfect set of pairwise non-isomorphic one-element models. -/
theorem hasPerfectAntichainOn_oneElementSentence_fin_one :
    (isoSetoid natPredicateLanguage (Fin 1)).HasPerfectAntichainOn
      (modelsOf oneElementSentence) :=
  hasCantorAntichainOn_oneElementSentence_fin_one.hasPerfectAntichainOn

/-- The one-element sentence has perfectly many countable models, witnessed on a finite tier
rather than on `ℕ`. -/
theorem hasPerfectlyManyCountableModels_oneElementSentence :
    HasPerfectlyManyCountableModels oneElementSentence :=
  .of_fin hasPerfectAntichainOn_oneElementSentence_fin_one

/-- There are continuum many isomorphism classes already on the one-element tier. -/
theorem mk_quotient_isoSetoidOn_fin_one_oneElementSentence :
    #(Quotient (isoSetoidOn (Fin 1) oneElementSentence)) = 𝔠 := by
  exact (mk_quotient_isoSetoidOn_le_continuum (Fin 1) oneElementSentence).antisymm
    hasCantorAntichainOn_oneElementSentence_fin_one.continuum_le_mk_quotient_comap

/-- The sentence has exactly continuum many countable models, all with one element. -/
theorem countableModelCount_oneElementSentence : countableModelCount oneElementSentence = 𝔠 :=
  hasPerfectlyManyCountableModels_oneElementSentence.countableModelCount_eq

end TauCeti.NatPredicateCounting
