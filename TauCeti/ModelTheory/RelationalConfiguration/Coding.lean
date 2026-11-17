/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.RelationalConfiguration.Topology
public import TauCeti.ModelTheory.Infinitary.IndexCoding

/-!
# The query code of a configuration

When each arity has countably many relation symbols, the atoms over `ℕ` are countable, and
reading a configuration along `Encodable.decode` for `Encodable.ofCountable` gives its **query
code**, a sequence of Booleans padded with `false` where decoding fails: the padding
`TauCeti.IndexCoding.pad` of its coordinates along `TauCeti.IndexCoding.ofEncodableWith`. The
query code is a
closed embedding of the coding space into Cantor space `ℕ → Bool`. The decoder need not be
injective on the indices where it succeeds, so the range is the set of sequences that are `false`
where decoding fails and agree at any two indices decoding to the same atom.

See Gao, *Invariant Descriptive Set Theory*, for these spaces of structures.

## Main definitions

* `TauCeti.RelationalConfiguration.queryCode`: the coordinates of a configuration on `ℕ` read
  along the decoder of `Encodable.ofCountable`, padded with `false`.

## Main results

* `TauCeti.RelationalConfiguration.isClosedEmbedding_queryCode`: the query code is a closed
  embedding into Cantor space, with range `range_queryCode`.
-/

public section

open Topology

namespace TauCeti.RelationalConfiguration

variable {L : FirstOrder.Language} {V : Type*}

/-! ### The query code -/

section QueryCode

variable [∀ n, Countable (L.Relations n)]

/-- The **query code** of a configuration on `ℕ`: at `n`, the value of the atom that the decoder of
`Encodable.ofCountable` returns at `n`, and `false` where decoding fails. It embeds the coding space
into Cantor space (`isClosedEmbedding_queryCode`). -/
noncomputable def queryCode (c : RelationalConfiguration L ℕ) : ℕ → Bool :=
  (IndexCoding.ofEncodableWith (Encodable.ofCountable (Atom L ℕ))).pad false c.eval

/-- The query code is the padding of the coordinates along the coding of `Encodable.ofCountable`. -/
theorem queryCode_def (c : RelationalConfiguration L ℕ) :
    queryCode c =
      (IndexCoding.ofEncodableWith (Encodable.ofCountable (Atom L ℕ))).pad false c.eval :=
  (rfl)

/-- The query code reads, at `n`, the atom decoded at `n`, and is `false` where decoding fails. -/
theorem queryCode_apply (c : RelationalConfiguration L ℕ) (n : ℕ) :
    queryCode c n =
      (@Encodable.decode (Atom L ℕ) (Encodable.ofCountable _) n).elim false c.eval := by
  rw [queryCode_def, IndexCoding.pad_apply, IndexCoding.ofEncodableWith_decode]

/-- The query code reads the atom `a` at its index `Encodable.encode a`. -/
@[simp]
theorem queryCode_encode (c : RelationalConfiguration L ℕ) (a : Atom L ℕ) :
    queryCode c (@Encodable.encode (Atom L ℕ) (Encodable.ofCountable _) a) = c.eval a := by
  rw [queryCode_def, ← IndexCoding.ofEncodableWith_encode, IndexCoding.pad_encode]

/-- The query code is `false` at the indices where decoding fails. -/
theorem queryCode_of_decode_eq_none (c : RelationalConfiguration L ℕ) {n : ℕ}
    (hn : @Encodable.decode (Atom L ℕ) (Encodable.ofCountable _) n = none) :
    queryCode c n = false := by
  rw [queryCode_def, IndexCoding.pad_of_decode_none]
  rwa [IndexCoding.ofEncodableWith_decode]

/-- The query code is `c.eval a` at an index decoding to `a`. -/
theorem queryCode_of_decode_eq_some (c : RelationalConfiguration L ℕ) {n : ℕ} {a : Atom L ℕ}
    (hn : @Encodable.decode (Atom L ℕ) (Encodable.ofCountable _) n = some a) :
    queryCode c n = c.eval a := by
  rw [queryCode_def, IndexCoding.pad_of_decode_some]
  rwa [IndexCoding.ofEncodableWith_decode]

/-- The query code is continuous: each coordinate reads one atom or is constantly `false`. -/
@[fun_prop]
theorem continuous_queryCode : Continuous (queryCode (L := L)) := by
  refine continuous_pi fun n => ?_
  cases h : @Encodable.decode (Atom L ℕ) (Encodable.ofCountable _) n with
  | none => simpa only [queryCode_of_decode_eq_none _ h] using continuous_const
  | some a => simpa only [queryCode_of_decode_eq_some _ h] using continuous_eval a

/-- The query code is injective: it reads every atom. -/
theorem queryCode_injective : Function.Injective (queryCode (L := L)) :=
  fun c d h => ext fun a => by
    rw [← queryCode_encode c a, ← queryCode_encode d a, h]

/-- **The query code is a closed embedding** of the coding space into Cantor space. -/
theorem isClosedEmbedding_queryCode : IsClosedEmbedding (queryCode (L := L)) :=
  continuous_queryCode.isClosedEmbedding queryCode_injective

/-- The range of the query code: the sequences that are `false` where decoding fails and agree at
any two indices decoding to the same atom. -/
theorem range_queryCode :
    Set.range (queryCode (L := L)) =
      {x : ℕ → Bool |
        (∀ n, @Encodable.decode (Atom L ℕ) (Encodable.ofCountable _) n = none → x n = false) ∧
          ∀ m n, @Encodable.decode (Atom L ℕ) (Encodable.ofCountable _) m =
            @Encodable.decode (Atom L ℕ) (Encodable.ofCountable _) n → x m = x n} := by
  let : Encodable (Atom L ℕ) := Encodable.ofCountable _
  ext x
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨fun n hn => queryCode_of_decode_eq_none c hn, fun m n hmn => ?_⟩
    rw [queryCode_apply, queryCode_apply, hmn]
  · rintro ⟨hnone, hsame⟩
    refine ⟨mk fun a => x (Encodable.encode a), funext fun n => ?_⟩
    cases h : (Encodable.decode n : Option (Atom L ℕ)) with
    | none => rw [queryCode_of_decode_eq_none _ h, hnone n h]
    | some a =>
      rw [queryCode_of_decode_eq_some _ h, eval_mk]
      exact hsame _ _ ((Encodable.encodek a).trans h.symm)

end QueryCode

end TauCeti.RelationalConfiguration
