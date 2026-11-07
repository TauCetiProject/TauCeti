/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Basic.Real.Basic
public import Mathlib.Topology.Compactification.OnePoint.Basic
import TauCeti.Data.Fin.Basic

/-!
# The range of a map from the projective line onto a closed polygonal chain

A map from the projective line `OnePoint ℝ` into a real vector space, which agrees with a map `B`
on the reals, sends `∞` to a vertex `V`, and whose restrictions to the intervals cut out by finitely
many ordered points trace consecutive sides of a polygonal chain, has range exactly the union of
the sides. The bounded intervals map onto the sides between consecutive vertices, and the two
unbounded intervals onto the two sides at `V` with `V` omitted.

## Main results

* `TauCeti.range_subset_union_segments`: the range lies in the union of the sides.
* `TauCeti.union_segments_subset_range`: the union of the sides lies in the range.
-/

public section

open Set
open scoped OnePoint

namespace TauCeti

/-- Let `g` be a map from the projective line to a real vector space `E` with `g ∞ = V` that
agrees with `B` on the reals.  If `B` carries each interval between consecutive `a i` onto the side
between consecutive vertices `P`, and the two unbounded intervals onto the two sides at `V` with `V`
omitted, then the range of `g` lies in the union of the sides. -/
theorem range_subset_union_segments {E : Type*} [AddCommGroup E] [Module ℝ E] {n : ℕ}
    (a : Fin (n + 1) → ℝ) (g : OnePoint ℝ → E)
    (B : ℝ → E) (P : Fin (n + 1) → E) (V : E) (hinfty : g ∞ = V) (hcoe : ∀ x : ℝ, g x = B x)
    (hbounded : ∀ i : Fin n,
      B '' Icc (a i.castSucc) (a i.succ) = segment ℝ (P i.castSucc) (P i.succ))
    (hright : B '' Ici (a (Fin.last n)) = segment ℝ (P (Fin.last n)) V \ {V})
    (hleft : B '' Iic (a 0) = segment ℝ (P 0) V \ {V}) :
    Set.range g ⊆ (⋃ i : Fin n, segment ℝ (P i.castSucc) (P i.succ)) ∪
      segment ℝ (P (Fin.last n)) V ∪ segment ℝ V (P 0) := by
  rintro _ ⟨x, rfl⟩
  induction x using OnePoint.rec with
  | infty =>
      rw [hinfty]
      exact Or.inr (left_mem_segment ℝ _ _)
  | coe x =>
      rw [hcoe]
      by_cases hxleft : x ≤ a 0
      · have himage : B x ∈ B '' Iic (a 0) := ⟨x, hxleft, rfl⟩
        rw [hleft] at himage
        exact Or.inr (segment_symm ℝ (P 0) V ▸ himage.1)
      · by_cases hxright : a (Fin.last n) ≤ x
        · have himage : B x ∈ B '' Ici (a (Fin.last n)) := ⟨x, hxright, rfl⟩
          rw [hright] at himage
          exact Or.inl (Or.inr himage.1)
        · have hn : n ≠ 0 := by
            rintro rfl
            exact hxright (lt_of_not_ge hxleft).le
          obtain ⟨i, hi⟩ := exists_mem_Icc_castSucc_succ a hn
            ⟨(lt_of_not_ge hxleft).le, (lt_of_not_ge hxright).le⟩
          have himage : B x ∈ B '' Icc (a i.castSucc) (a i.succ) := ⟨x, hi, rfl⟩
          rw [hbounded i] at himage
          exact Or.inl (Or.inl (Set.mem_iUnion.mpr ⟨i, himage⟩))

/-- Under the hypotheses of `range_subset_union_segments`, the union of the sides lies in the
range of `g`, the vertex at infinity being `g ∞`. -/
theorem union_segments_subset_range {E : Type*} [AddCommGroup E] [Module ℝ E] {n : ℕ}
    (a : Fin (n + 1) → ℝ) (g : OnePoint ℝ → E)
    (B : ℝ → E) (P : Fin (n + 1) → E) (V : E) (hinfty : g ∞ = V) (hcoe : ∀ x : ℝ, g x = B x)
    (hbounded : ∀ i : Fin n,
      B '' Icc (a i.castSucc) (a i.succ) = segment ℝ (P i.castSucc) (P i.succ))
    (hright : B '' Ici (a (Fin.last n)) = segment ℝ (P (Fin.last n)) V \ {V})
    (hleft : B '' Iic (a 0) = segment ℝ (P 0) V \ {V}) :
    (⋃ i : Fin n, segment ℝ (P i.castSucc) (P i.succ)) ∪
      segment ℝ (P (Fin.last n)) V ∪ segment ℝ V (P 0) ⊆ Set.range g := by
  have hside {s : Set ℝ} {S : Set E} (hs : B '' s = S \ {V}) {z : E} (hz : z ∈ S) :
      z ∈ Set.range g := by
    by_cases hzeq : z = V
    · exact ⟨∞, hzeq ▸ hinfty⟩
    · obtain ⟨x, _, rfl⟩ : z ∈ B '' s := hs ▸ ⟨hz, hzeq⟩
      exact ⟨x, hcoe x⟩
  rintro z ((hz | hzright) | hzleft)
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
    obtain ⟨x, _, rfl⟩ : z ∈ B '' Icc (a i.castSucc) (a i.succ) := (hbounded i).symm ▸ hi
    exact ⟨x, hcoe x⟩
  · exact hside hright hzright
  · exact hside hleft (segment_symm ℝ V (P 0) ▸ hzleft)

end TauCeti
