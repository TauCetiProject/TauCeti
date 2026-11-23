/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.PositiveDegrees.Word
import Mathlib.Data.Fintype.List
import Mathlib.Data.Set.Finite.List

/-!
# Finite degree and encounter records

An itinerary record consists of the nonzero degree shifts and one encounter block
before, between, and after the shifts. If each block visits each label at most once,
a finite alphabet of encounter labels and a fixed degree cutoff give finitely many
records. Mathlib's `fintypeNodupList` supplies the finite alphabet of blocks, and
`List.finite_length_eq` bounds lists of blocks with the required length.

Adapted from `Mei/Algebra/PositiveDegrees/Word.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`bf3986029ff4d3eb4025d4067489511b0724374e`, released under Apache 2.0.
-/

public section

namespace TauCeti.ScatteringDiagram

variable {N : Type*} [AddCommMonoid N] (d : PositiveDegrees N)

/-- With finitely many encounter labels, there are finitely many records comprising a
word in the degree cutoff `k` and one duplicate-free encounter block before, between,
and after its degree changes. -/
theorem finite_degree_encounter_words_cutoff_nodup {ι : Type*} [Finite ι] (k : ℕ) :
    Set.Finite {p : List N × List (List ι) |
      p.1 ∈ d.wordCutoff k ∧ p.2.length = p.1.length + 1 ∧ ∀ b ∈ p.2, b.Nodup} := by
  classical
  let := Fintype.ofFinite ι
  let Block := {b : List ι // b.Nodup}
  apply ((d.finite_wordCutoff k).biUnion (fun l _ =>
    (List.finite_length_eq Block (l.length + 1)).image
      (fun bs => (l, bs.map Subtype.val)))).subset
  rintro ⟨l, blocks⟩ ⟨hl, hlen, hb⟩
  refine Set.mem_iUnion.mpr ⟨l, Set.mem_iUnion.mpr ⟨hl, ?_⟩⟩
  refine ⟨blocks.attachWith List.Nodup hb, ?_, ?_⟩
  · change (blocks.attachWith List.Nodup hb).length = l.length + 1
    rw [List.length_attachWith]
    exact hlen
  · exact Prod.ext rfl (List.attachWith_map_subtype_val hb)

end TauCeti.ScatteringDiagram
