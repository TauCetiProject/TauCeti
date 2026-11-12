/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.BraidWord.PDCode
public import TauCeti.KnotTheory.PDCode.Circle
public import TauCeti.KnotTheory.PDCode.Oriented.Reidemeister.Equivalence
import TauCeti.Data.List.Rotate
import TauCeti.KnotTheory.BraidWord.Components

/-!
# The closure of a braid word with an added uncrossed strand

The word `TauCeti.BraidWord.strandIncl w` is `w` on one strand more, whose new top strand no letter
crosses. In its closure the new strand closes up to a crossing-free circle, and the rest of the
closure is that of `w`: the closure of `w.strandIncl` is the closure of `w` with a circle adjoined,
up to renaming crossings and half-edges along the equality of lengths
(`TauCeti.BraidWord.closure_strandIncl`). This is the diagram-level form of the fact that adding
an uncrossed strand to a braid adds a split unknot to its closure.

## Main results

* `TauCeti.BraidWord.crossingsAt_strandIncl_castSucc` and
  `TauCeti.BraidWord.crossingsAt_strandIncl_last`: along an old position the word with an added
  strand meets the same crossings, and the new position meets none.
* `TauCeti.BraidWord.closure_strandIncl`: the closure gains one crossing-free circle.
* `TauCeti.BraidWord.normalizedKauffmanBracket_closure_strandIncl`: so its normalized Kauffman
  bracket is multiplied by the loop value.

## References

* J. Birman, *Braids, Links, and Mapping Class Groups*, Annals of Mathematics Studies 82 (1974),
  Chapter 2.
-/

public section

namespace TauCeti.BraidWord

open BraidGroup PDCode

variable {n : ℕ} (w : BraidWord (n + 1))

/-- The crossings of `w.strandIncl` are those of `w`. -/
private abbrev strandInclCross : Fin w.length ≃ Fin (w.strandIncl).length :=
  finCongr (length_strandIncl w).symm

private theorem getElem_strandIncl (j : Fin w.length) :
    (w.strandIncl)[(w.strandInclCross j).1] = ((w[j.1].1.castSucc : Fin (n + 1)), w[j.1].2) := by
  simp only [strandInclCross, finCongr_apply, Fin.val_cast, strandIncl_def]
  rw [List.getElem_map]

/-- Along an old strand position, the word with an added strand meets the same crossings as `w`.
-/
theorem crossingsAt_strandIncl_castSucc (p : Fin (n + 1)) :
    (w.strandIncl).crossingsAt p.castSucc =
      (w.crossingsAt p).map (finCongr (length_strandIncl w).symm) := by
  have hmono : StrictMono (finCongr (length_strandIncl w).symm) := fun a b h ↦
    Fin.lt_def.mpr (by simp only [finCongr_apply, Fin.val_cast]; exact Fin.lt_def.mp h)
  refine List.SortedLT.eq_of_mem_iff (sortedLT_crossingsAt w.strandIncl p.castSucc)
    (hmono.sortedLT_listMap.mpr (sortedLT_crossingsAt w p)) fun j ↦ ?_
  obtain ⟨j, rfl⟩ := (w.strandInclCross).surjective j
  simp only [mem_crossingsAt, getElem_strandIncl, strand_castSucc, strandSucc_castSucc,
    Fin.castSucc_inj, List.mem_map, (w.strandInclCross).injective.eq_iff, exists_eq_right]

/-- No letter of the word with an added strand crosses the new top strand. -/
@[simp]
theorem crossingsAt_strandIncl_last : (w.strandIncl).crossingsAt (Fin.last (n + 1)) = [] := by
  rw [crossingsAt_eq_nil_iff]
  intro j
  obtain ⟨j, rfl⟩ := (w.strandInclCross).surjective j
  rw [getElem_strandIncl, strand_castSucc, strandSucc_castSucc]
  exact ⟨(Fin.castSucc_ne_last _).symm, (Fin.castSucc_ne_last _).symm⟩

private theorem nextCrossing_strandIncl_castSucc (p : Fin (n + 1)) (j : Fin w.length) :
    (w.strandIncl).nextCrossing p.castSucc (w.strandInclCross j) =
      w.strandInclCross (w.nextCrossing p j) := by
  rw [nextCrossing_def, crossingsAt_strandIncl_castSucc,
    List.formPerm_map_apply (w.strandInclCross).injective, nextCrossing_def]

private theorem incomingSlot_strandIncl {j : Fin w.length} {p : Fin (n + 1)}
    (hj : j ∈ w.crossingsAt p) :
    (w.strandIncl).incomingSlot (w.strandInclCross j) p.castSucc = w.incomingSlot j p := by
  have hs := (w.strandIncl).incomingSlot_strand (w.strandInclCross j)
  have hs' := (w.strandIncl).incomingSlot_strandSucc (w.strandInclCross j)
  rw [getElem_strandIncl, strand_castSucc] at hs
  rw [getElem_strandIncl, strandSucc_castSucc] at hs'
  rcases (w.mem_crossingsAt).1 hj with rfl | rfl
  · rw [hs, incomingSlot_strand]
  · rw [hs', incomingSlot_strandSucc]

private theorem outgoingSlot_strandIncl {j : Fin w.length} {p : Fin (n + 1)}
    (hj : j ∈ w.crossingsAt p) :
    (w.strandIncl).outgoingSlot (w.strandInclCross j) p.castSucc = w.outgoingSlot j p := by
  have hs := (w.strandIncl).outgoingSlot_strand (w.strandInclCross j)
  have hs' := (w.strandIncl).outgoingSlot_strandSucc (w.strandInclCross j)
  rw [getElem_strandIncl, strand_castSucc] at hs
  rw [getElem_strandIncl, strandSucc_castSucc] at hs'
  rcases (w.mem_crossingsAt).1 hj with rfl | rfl
  · rw [hs, outgoingSlot_strand]
  · rw [hs', outgoingSlot_strandSucc]

private theorem crossinglessComponentCount_closure_strandIncl :
    (closure w.strandIncl).crossinglessComponentCount =
      w.closure.crossinglessComponentCount + 1 := by
  simp only [crossinglessComponentCount_closure, Finset.card_filter, Fin.sum_univ_castSucc,
    crossingsAt_strandIncl_castSucc, List.map_eq_nil_iff, crossingsAt_strandIncl_last, ite_true]

/-- **Adding an uncrossed strand adds a circle.** The closure of `w.strandIncl` is the closure of
`w` with a crossing-free circle adjoined, with crossings and half-edges renamed along the equality
of the lengths of the two words. -/
theorem closure_strandIncl :
    closure w.strandIncl =
      (OrientedPDCode.adjoinCircle w.closure true).relabel
        (crossingBlockEquiv (finCongr (length_strandIncl w).symm))
        (finCongr (length_strandIncl w).symm) := by
  have hcount := crossinglessComponentCount_closure_strandIncl w
  apply OrientedPDCode.ext
  · apply PDCode.ext
    · rw [halfEdge_closure]
      refine Equiv.ext fun h ↦ ?_
      obtain ⟨⟨j, s⟩, rfl⟩ := (crossingSlotEquiv _).surjective h
      simp
    · refine edgePair_closure_eq_of_outgoingSlot _ fun j p hj ↦ ?_
      obtain ⟨j, rfl⟩ := (w.strandInclCross).surjective j
      induction p using Fin.lastCases with
      | last => simp at hj
      | cast p =>
        have hj' : j ∈ w.crossingsAt p := by
          simpa [crossingsAt_strandIncl_castSucc, (w.strandInclCross).injective.eq_iff] using hj
        have hnext := w.nextCrossing_mem_crossingsAt_iff.mpr hj'
        have hlhs := edgePair_closure_outgoingSlot w.strandIncl hj
        rw [outgoingSlot_strandIncl w hj', nextCrossing_strandIncl_castSucc,
          incomingSlot_strandIncl w hnext] at hlhs
        have hrhs := edgePair_closure_outgoingSlot w hj'
        simp only [crossing_closure] at hlhs hrhs
        rw [outgoingSlot_strandIncl w hj', hlhs,
          ← crossingBlockEquiv_apply_crossingSlotEquiv (finCongr (length_strandIncl w).symm) j,
          ← crossingBlockEquiv_apply_crossingSlotEquiv (finCongr (length_strandIncl w).symm)
            (w.nextCrossing p j),
          OrientedPDCode.relabel_toPDCode, PDCode.relabel_edgePair,
          PerfectMatching.congr_val_apply_apply, OrientedPDCode.toPDCode_adjoinCircle,
          PDCode.adjoinCircle_edgePair, hrhs]
    · simpa using hcount
    · funext j
      obtain ⟨j, rfl⟩ := (w.strandInclCross).surjective j
      simp only [overPair_closure, getElem_strandIncl, OrientedPDCode.relabel_toPDCode,
        PDCode.relabel_overPair, Equiv.symm_apply_apply, OrientedPDCode.toPDCode_adjoinCircle,
        PDCode.adjoinCircle_overPair]
  · funext h
    obtain ⟨⟨j, s⟩, rfl⟩ := (crossingSlotEquiv _).surjective h
    rw [orientation_closure, OrientedPDCode.relabel_orientation, crossingBlockEquiv_symm,
      crossingBlockEquiv_apply_crossingSlotEquiv, OrientedPDCode.orientation_adjoinCircle,
      orientation_closure]
  · simp only [crossinglessComponents_closure, OrientedPDCode.relabel_crossinglessComponents,
      OrientedPDCode.crossinglessComponents_adjoinCircle]
    rw [← crossinglessComponentCount_closure, ← crossinglessComponentCount_closure, hcount,
      Multiset.replicate_succ]

/-- Adding an uncrossed strand multiplies the normalized Kauffman bracket of the closure by the
loop value `δ = -(A² + A⁻²)`. -/
theorem normalizedKauffmanBracket_closure_strandIncl {R : Type*} [CommRing R] (a : Rˣ) :
    (closure w.strandIncl).normalizedKauffmanBracket a =
      TemperleyLieb.jonesDelta a * w.closure.normalizedKauffmanBracket a := by
  rw [closure_strandIncl,
    ← (OrientedPDCode.reidemeisterEquiv_relabel _ _ _).normalizedKauffmanBracket_eq,
    OrientedPDCode.normalizedKauffmanBracket_adjoinCircle _ _ (componentCount_closure_pos w)]

end TauCeti.BraidWord
