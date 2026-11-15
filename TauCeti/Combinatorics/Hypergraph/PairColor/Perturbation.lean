/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.PairColor.Diagonal
import Mathlib.Tactic.Linarith

/-!
# Regular pairs after moving vertices

Rebalancing vertex cells can add vertices as well as remove them, so the slicing lemma alone
does not preserve regularity. An `ε`-regular pair remains `4ε`-regular on disjoint new cells if
each new cell has at least half the size of the old cell and at most an `ε²`-fraction of its
vertices come from outside the old cell. The old cells may overlap, and the palette and its
reversal need not be symmetric or finite.

The partition version matches new cells injectively to old cells and restores regularity of
the full lower skeleton by filling the diagonal with a fresh color. The diagonal size condition
is explicit: densities exclude equal vertices, so coincident singleton tests must be ruled out.
The existing diagonal-cleanup edit estimates apply unchanged.

The density comparison reuses `Rel.abs_edgeDensity_sub_edgeDensity_le_two_mul` from Mathlib.

## References

* J. Komlós and M. Simonovits, *Szemerédi's regularity lemma and its applications in graph
  theory*, in Combinatorics, Paul Erdős is Eighty, Vol. 2 (1996), for slicing regular pairs.
* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007), for rebalancing in regular approximation.
-/

public section

open Finset

namespace TauCeti.PairColorSystem

variable {κ V : Type*} {S : PairColorSystem κ V} {ε : ℝ}

/-- Large tests in the new cells have densities close to the original regular pair's density.
The retained tests pass the old thresholds, and incoming vertices cost at most `ε`. -/
private theorem abs_pairColorDensity_sub_old_le [DecidableEq V] {s t a b x y : Finset V}
    (h : S.IsRegularPair ε s t) (hab : Disjoint a b) (hε : 0 < ε) (hε' : ε < 1 / 4)
    (hsa : (#s : ℝ) ≤ 2 * #a) (htb : (#t : ℝ) ≤ 2 * #b)
    (ha : (#(a \ s) : ℝ) ≤ ε ^ 2 * #a) (hb : (#(b \ t) : ℝ) ≤ ε ^ 2 * #b)
    (hx : x ⊆ a) (hy : y ⊆ b) (hlargeX : 4 * ε * #a ≤ #x)
    (hlargeY : 4 * ε * #b ≤ #y) (c : κ) :
    |(pairColorDensity S c x y : ℝ) - pairColorDensity S c s t| ≤ 2 * ε := by
  classical
  -- A large test retains enough vertices both for old regularity and for density stability.
  have retained {u v w : Finset V} (hsize : (#u : ℝ) ≤ 2 * #v)
      (hnew : (#(v \ u) : ℝ) ≤ ε ^ 2 * #v) (hw : w ⊆ v)
      (hlarge : 4 * ε * #v ≤ #w) :
      ε * #u ≤ #(w ∩ u) ∧ (1 - ε / 2) * #w ≤ #(w ∩ u) := by
    have hdiff : (#(w \ u) : ℝ) ≤ #(v \ u) := by
      exact_mod_cast card_le_card (sdiff_subset_sdiff hw (Subset.refl u))
    have hsplit : (#(w \ u) : ℝ) + #(w ∩ u) = #w := by
      exact_mod_cast card_sdiff_add_card_inter w u
    have hmul := mul_le_mul_of_nonneg_left hlarge (by positivity : 0 ≤ ε / 2)
    have hsq : ε ^ 2 ≤ ε := by nlinarith
    have hbound := mul_le_mul_of_nonneg_right hsq (Nat.cast_nonneg #v : (0 : ℝ) ≤ #v)
    have hold := mul_le_mul_of_nonneg_left hsize hε.le
    constructor <;> nlinarith [Nat.cast_nonneg (α := ℝ) #v]
  obtain ⟨hxold, hxret⟩ := retained hsa ha hx hlargeX
  obtain ⟨hyold, hyret⟩ := retained htb hb hy hlargeY
  have hold := isRegularPair_iff.mp h c (x ∩ s) inter_subset_right (y ∩ t)
    inter_subset_right hxold hyold
  -- On disjoint rectangles, the two density normalizations agree.
  have htest : |(pairColorDensity S c (x ∩ s) (y ∩ t) : ℝ) -
      pairColorDensity S c x y| ≤ ε := by
    rw [pairColorDensity_eq_edgeDensity_of_disjoint S c
        ((hab.mono hx hy).mono inter_subset_left inter_subset_left),
      pairColorDensity_eq_edgeDensity_of_disjoint S c (hab.mono hx hy)]
    have hd := Rel.abs_edgeDensity_sub_edgeDensity_le_two_mul
      (fun u v ↦ S.colorOfPair u v = some c) inter_subset_left inter_subset_left
      (by positivity : 0 ≤ ε / 2) hxret hyret
    linarith
  calc
    _ ≤ |(pairColorDensity S c x y : ℝ) - pairColorDensity S c (x ∩ s) (y ∩ t)| +
        |(pairColorDensity S c (x ∩ s) (y ∩ t) : ℝ) - pairColorDensity S c s t| :=
      abs_sub_le _ _ _
    _ ≤ 2 * ε := by rw [abs_sub_comm]; linarith

/-- **Vertex perturbation of a regular pair.** Suppose `(s, t)` is `ε`-regular and the new
cells `a, b` are disjoint. If each new cell has at least half the old size and at most an
`ε²`-fraction of its vertices outside the corresponding old cell, the new pair is
`4ε`-regular. No restriction is imposed on colors of the incoming vertices. -/
theorem IsRegularPair.of_card_sdiff_le [DecidableEq V] {s t a b : Finset V}
    (h : S.IsRegularPair ε s t) (hab : Disjoint a b)
    (hε : 0 < ε) (hsa : (#s : ℝ) ≤ 2 * #a) (htb : (#t : ℝ) ≤ 2 * #b)
    (ha : (#(a \ s) : ℝ) ≤ ε ^ 2 * #a) (hb : (#(b \ t) : ℝ) ≤ ε ^ 2 * #b) :
    S.IsRegularPair (4 * ε) a b := by
  classical
  by_cases hbig : 1 ≤ 4 * ε
  · exact isRegularPair_of_one_le hbig
  have hsmall : ε < 1 / 4 := by linarith
  apply isRegularPair_iff.mpr
  intro c x hx y hy hlargeX hlargeY
  have htest := abs_pairColorDensity_sub_old_le h hab hε hsmall hsa htb ha hb
    hx hy hlargeX hlargeY c
  have hfull := abs_pairColorDensity_sub_old_le h hab hε hsmall hsa htb ha hb
    (Subset.refl a) (Subset.refl b)
    (mul_le_of_le_one_left (Nat.cast_nonneg _) (by linarith))
    (mul_le_of_le_one_left (Nat.cast_nonneg _) (by linarith)) c
  calc
    _ ≤ |(pairColorDensity S c x y : ℝ) - pairColorDensity S c s t| +
        |(pairColorDensity S c s t : ℝ) - pairColorDensity S c a b| := abs_sub_le _ _ _
    _ ≤ 4 * ε := by rw [abs_sub_comm (pairColorDensity S c s t : ℝ)]; linarith

/-- Matched perturbations of vertex cells preserve off-diagonal regularity. Filling the new
diagonal then gives a regular lower skeleton, provided its cells exclude singleton tests.
The matching need only be injective; the new partition may have fewer cells. -/
theorem isPairColorRegular_fillDiagonal_of_card_sdiff_le [Fintype V] [DecidableEq V]
    {P Q : Finpartition (univ : Finset V)} (f : Q.parts ↪ P.parts)
    (hreg : ∀ A ∈ P.parts, ∀ B ∈ P.parts, A ≠ B → S.IsRegularPair ε A B)
    (hsize : ∀ A : Q.parts, (#(f A).val : ℝ) ≤ 2 * #A.val)
    (hnew : ∀ A : Q.parts, (#(A.val \ (f A).val) : ℝ) ≤ ε ^ 2 * #A.val)
    (hdiag : ∀ A ∈ Q.parts, 1 < 4 * ε * #A) :
    (⟨Q, S.fillDiagonal Q⟩ : PairSkeleton3 (Option κ) V).IsPairColorRegular (4 * ε) := by
  refine S.isPairColorRegular_fillDiagonal Q hdiag fun A hA B hB hAB ↦ ?_
  have hε : 0 < ε := by
    by_contra! h
    nlinarith [hdiag A hA, (Nat.cast_nonneg #A : (0 : ℝ) ≤ #A)]
  let a : Q.parts := ⟨A, hA⟩
  let b : Q.parts := ⟨B, hB⟩
  have hne : (f a).val ≠ (f b).val := fun heq ↦
    hAB (congrArg Subtype.val (f.injective (Subtype.ext heq)))
  exact (hreg _ (f a).property _ (f b).property hne).of_card_sdiff_le
    (Q.disjoint hA hB hAB) hε (hsize a) (hsize b) (hnew a) (hnew b)

end TauCeti.PairColorSystem
