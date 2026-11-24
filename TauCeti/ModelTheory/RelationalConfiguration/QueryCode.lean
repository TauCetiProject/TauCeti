/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.RelationalConfiguration.Topology
public import TauCeti.SetTheory.Descriptive.WellFoundedTree

/-!
# The query code of a relational configuration

In a relational vocabulary with countably many symbols of each arity, over a countable carrier
`V`, the atoms of `TauCeti.RelationalConfiguration L V` are countable. Fixing the enumeration of
atoms given by `Encodable.ofCountable`, the **query code** of a configuration `c` is the sequence
`queryCode c : ℕ → Bool` whose `n`-th term is the value of `c` at the atom that the enumeration
decodes from `n`, and `false` where decoding fails.

The query code is a closed embedding of the coding space into Cantor space `ℕ → Bool`. The
decoder need not be injective on the indices where it succeeds, so its range consists of the
sequences that vanish where decoding fails and agree at any two indices decoding to the same
atom. Transferring the tree representation of analytic subsets of Cantor space along it, every
analytic set of configurations is the projection of the body of a tree on `Bool × ℕ`, read through
the query code. This is how a tree, a countable object, describes an analytic class of countable
structures.

## Main definitions

* `TauCeti.RelationalConfiguration.queryCode`: the query code of a configuration.

## Main results

* `TauCeti.RelationalConfiguration.queryCode_encode`: the query code reads the configuration at
  the code of each atom.
* `TauCeti.RelationalConfiguration.isClosedEmbedding_queryCode` and
  `TauCeti.RelationalConfiguration.range_queryCode`: the query code is a closed embedding into
  Cantor space, with the stated range.
* `TauCeti.RelationalConfiguration.exists_tree_of_analyticSet`: the tree representation of
  analytic sets of configurations.

## References

* Alexander S. Kechris, *Classical Descriptive Set Theory*, Graduate Texts in Mathematics 156,
  Springer, 1995, Sections 16.C and 25.A.
* David Marker, *Lectures on infinitary model theory*, Chapter 9, the tree representation of
  `Σ¹₁` sets after Theorem 9.27.
* The query code also appears in the formalization `cameronfreer/infinitary-logic`
  (`InfinitaryLogic/Descriptive/QueryCode.lean`), for the carrier `ℕ`.
-/

public section

open Function Set Topology MeasureTheory Descriptive Descriptive.Tree

namespace TauCeti.RelationalConfiguration

open _root_.FirstOrder (Language)

variable {L : Language} {V : Type*} [∀ n, Countable (L.Relations n)] [Countable V]

/-- The **query code** of a configuration: the sequence reading, at each index `n`, the value of
the configuration at the atom that `Encodable.ofCountable` decodes from `n`, and `false` where
decoding fails. -/
noncomputable def queryCode (c : RelationalConfiguration L V) (n : ℕ) : Bool :=
  (@Encodable.decode (Atom L V) (Encodable.ofCountable _) n).elim false c.eval

/-- Unfolding the query code at an index. -/
theorem queryCode_apply (c : RelationalConfiguration L V) (n : ℕ) :
    queryCode c n = (@Encodable.decode (Atom L V) (Encodable.ofCountable _) n).elim false c.eval :=
  (rfl)

/-- At an index decoding to the atom `a`, the query code reads the configuration at `a`. -/
theorem queryCode_of_decode_eq_some {n : ℕ} {a : Atom L V}
    (h : @Encodable.decode (Atom L V) (Encodable.ofCountable _) n = some a)
    (c : RelationalConfiguration L V) : queryCode c n = c.eval a := by
  rw [queryCode_apply, h, Option.elim_some]

/-- At an index where decoding fails, the query code is `false`. -/
theorem queryCode_of_decode_eq_none {n : ℕ}
    (h : @Encodable.decode (Atom L V) (Encodable.ofCountable _) n = none)
    (c : RelationalConfiguration L V) : queryCode c n = false := by
  rw [queryCode_apply, h, Option.elim_none]

/-- The query code reads the configuration at the code of each atom. -/
@[simp]
theorem queryCode_encode (c : RelationalConfiguration L V) (a : Atom L V) :
    queryCode c (@Encodable.encode (Atom L V) (Encodable.ofCountable _) a) = c.eval a :=
  queryCode_of_decode_eq_some (@Encodable.encodek _ (Encodable.ofCountable _) a) c

/-- If there are no atoms, the query code is constantly `false`. -/
theorem queryCode_of_isEmpty [IsEmpty (Atom L V)] (c : RelationalConfiguration L V) :
    queryCode c = fun _ => false :=
  funext fun _ => queryCode_of_decode_eq_none (Option.eq_none_iff_forall_ne_some.2 isEmptyElim) c

/-- Distinct configurations have distinct query codes. -/
theorem queryCode_injective : Injective (queryCode : RelationalConfiguration L V → ℕ → Bool) :=
  fun c d h => ext fun a => by rw [← queryCode_encode c, ← queryCode_encode d, h]

/-- The query code is continuous. -/
@[fun_prop]
theorem continuous_queryCode : Continuous (queryCode : RelationalConfiguration L V → ℕ → Bool) := by
  refine continuous_pi fun n => ?_
  rcases h : @Encodable.decode (Atom L V) (Encodable.ofCountable _) n with _ | a
  · simpa only [queryCode_of_decode_eq_none h] using continuous_const
  · simpa only [queryCode_of_decode_eq_some h] using continuous_eval a

/-- **The query code is a closed embedding** of the coding space into Cantor space. -/
theorem isClosedEmbedding_queryCode :
    IsClosedEmbedding (queryCode : RelationalConfiguration L V → ℕ → Bool) :=
  continuous_queryCode.isClosedEmbedding queryCode_injective

/-- The query code is a measurable embedding into Cantor space. -/
theorem measurableEmbedding_queryCode :
    MeasurableEmbedding (queryCode : RelationalConfiguration L V → ℕ → Bool) :=
  isClosedEmbedding_queryCode.measurableEmbedding

/-- **The range of the query code** consists of the sequences that are `false` where decoding fails
and agree at any two indices decoding to the same atom. -/
theorem range_queryCode :
    range (queryCode : RelationalConfiguration L V → ℕ → Bool) =
      {x | (∀ n, @Encodable.decode (Atom L V) (Encodable.ofCountable _) n = none → x n = false) ∧
        ∀ m n, @Encodable.decode (Atom L V) (Encodable.ofCountable _) m =
          @Encodable.decode (Atom L V) (Encodable.ofCountable _) n → x m = x n} := by
  let := Encodable.ofCountable (Atom L V)
  ext x
  refine ⟨?_, fun ⟨hnone, hsame⟩ => ⟨mk fun a => x (Encodable.encode a), funext fun n => ?_⟩⟩
  · rintro ⟨c, rfl⟩
    exact ⟨fun n h => queryCode_of_decode_eq_none h c, fun m n h => by
      simp only [queryCode_apply, h]⟩
  · rcases h : (Encodable.decode n : Option (Atom L V)) with _ | a
    · rw [queryCode_of_decode_eq_none h, hnone n h]
    · rw [queryCode_of_decode_eq_some h, eval_mk, hsame _ _ ((Encodable.encodek a).trans h.symm)]

/-- **Tree representation of analytic sets of configurations.** Every analytic set `B` of
configurations is the projection of the body of a tree on `Bool × ℕ`, read through the query
code: `c ∈ B` iff some `g : ℕ → ℕ` makes `n ↦ (queryCode c n, g n)` a branch. -/
theorem exists_tree_of_analyticSet {B : Set (RelationalConfiguration L V)} (hB : AnalyticSet B) :
    ∃ T : tree (Bool × ℕ),
      B = {c | ∃ g : ℕ → ℕ, (fun n => (queryCode c n, g n)) ∈ body T} := by
  obtain ⟨T, hT⟩ := exists_tree_of_analyticSet_cantor (hB.image_of_continuous continuous_queryCode)
  refine ⟨T, Set.ext fun c => ?_⟩
  rw [← queryCode_injective.mem_set_image, hT]
  exact Iff.rfl

end TauCeti.RelationalConfiguration
