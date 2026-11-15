/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Rank24.Glue.Pattern
public import TauCeti.LinearAlgebra.IntegralLattice.Rank24.GlueWord

/-!
# Decoding Conway--Sloane glue-generator patterns

A glue-generator pattern denotes a finite set of digit words (`TauCeti.GluePattern.expand`), and a
digit word that passes the length and label-range checks decodes to a glue word in the component
alphabets of an ordered family of ADE components (`TauCeti.decodeGlueWord`). This file combines the
two: `TauCeti.GluePattern.decodedWords` is the set of glue words whose labels form an expanded
word of the pattern.

Since the expansion of a pattern is the orbit of its seed under the coordinate permutations the
pattern indicates (`TauCeti.GluePattern.mem_expand_iff_exists_mem_symmetries`), permuting the
components by an indicated symmetry `g` reindexes the decoded words
(`TauCeti.GluePattern.decodedWords_comp`): the decoded words for the components `k ↦ t (g k)`
are exactly the words `k ↦ w (g k)` for `w` decoded for `t`. When `g` permutes components of
equal type, as the rotations of a marked block and the even permutations in the table do, the
decoded set is therefore stable under the corresponding coordinate permutation of glue words.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*,
  3rd edition, Chapter 4 §3 and Chapter 16 §1, Table 16.1.
-/

public section

namespace TauCeti

namespace GluePattern

variable {n : ℕ} (t : Fin n → DynkinType) (ht : ∀ i, (t i).IsSimplyLaced)

/-- The glue words denoted by a pattern for an ordered family of components: the words whose
digit labels form an expanded word of the pattern, that is, the decodings of the valid expanded
words. -/
def decodedWords (p : GluePattern) : Set (∀ i, (t i).glueAlphabet (ht i)) :=
  {w | encodeGlueWord t ht w ∈ p.expand}

/-- A glue word is denoted by a pattern exactly when its labels form an expanded word. -/
@[simp]
theorem mem_decodedWords_iff (p : GluePattern) (w : ∀ i, (t i).glueAlphabet (ht i)) :
    w ∈ p.decodedWords t ht ↔ encodeGlueWord t ht w ∈ p.expand :=
  Iff.rfl

/-- The glue words denoted by a pattern are the decodings of its expanded words. -/
theorem mem_decodedWords_iff_exists_decodeGlueWord (p : GluePattern)
    (w : ∀ i, (t i).glueAlphabet (ht i)) :
    w ∈ p.decodedWords t ht ↔ ∃ l ∈ p.expand, decodeGlueWord t ht l = some w := by
  simp

/-- An expanded word of a pattern that decodes gives a glue word denoted by the pattern. -/
theorem mem_decodedWords_of_decodeGlueWord_eq_some {p : GluePattern} {l : List ℕ}
    (hl : l ∈ p.expand) {w : ∀ i, (t i).glueAlphabet (ht i)}
    (hw : decodeGlueWord t ht l = some w) : w ∈ p.decodedWords t ht :=
  (mem_decodedWords_iff_exists_decodeGlueWord t ht p w).mpr ⟨l, hl, hw⟩

/-- **Decoded patterns are natural under their indicated coordinate permutations.** For a
symmetry `g` of the pattern, the glue words denoted for the reindexed components `k ↦ t (g k)`
are the reindexings `k ↦ w (g k)` of the glue words `w` denoted for `t`. -/
theorem decodedWords_comp (p : GluePattern) (t : Fin p.length → DynkinType)
    (ht : ∀ i, (t i).IsSimplyLaced) {g : Equiv.Perm (Fin p.length)} (hg : g ∈ p.symmetries) :
    p.decodedWords (fun k ↦ t (g k)) (fun k ↦ ht (g k)) =
      (Equiv.piCongrLeft (fun i ↦ (t i).glueAlphabet (ht i)) g).symm '' p.decodedWords t ht := by
  ext v
  obtain ⟨w, rfl⟩ := (Equiv.piCongrLeft (fun i ↦ (t i).glueAlphabet (ht i)) g).symm.surjective v
  rw [(Equiv.piCongrLeft _ g).symm.injective.mem_set_image, mem_decodedWords_iff,
    mem_decodedWords_iff, encodeGlueWord_def, encodeGlueWord_def]
  simp only [Equiv.piCongrLeft_symm_apply]
  exact p.ofFn_comp_mem_expand_iff (fun i ↦ (((t i).glueLabelEquiv (ht i)).symm (w i)).val) hg

end GluePattern

end TauCeti
