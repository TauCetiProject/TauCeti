/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Polygon.ClosingSide
public import TauCeti.Analysis.Complex.PlaneSeparation.Segment

/-!
# Separating nonconvex Schwarz--Christoffel sides from the closing sides

The total turning exponent `-2` puts the first finite vertex, the last finite vertex, and the
vertex at infinity on one horizontal line. If every intermediate vertex lies strictly above this
line, a bounded polygon side can meet either closing side only at their common finite endpoint.
This condition allows reentrant corners: the bounded sides need not have monotone directions.

Together with a check that nonadjacent bounded sides do not meet, this gives a finite geometric
criterion for simplicity of the compactified boundary and hence for the primitive to map the
upper half-plane bijectively onto the complementary component containing its base-point image.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
-/

public section

noncomputable section

open Complex Set UpperHalfPlane
open scoped ComplexOrder

namespace TauCeti

variable {n : ℕ}

/-- If all intermediate vertices are strictly above the horizontal closing line, a bounded
side meets the left closing side only at the first finite vertex. -/
theorem schwarzChristoffelPolygon_bounded_edgeSet_last_eq_first_vertex_of_heights
    (a e : Fin (n + 2) → ℝ) (z₀ : UpperHalfPlane) (ha : StrictMono a)
    (he : ∀ k, -1 < e k) (hsum : ∑ k, e k = -2)
    (hheight : ∀ k : Fin (n + 2), k ≠ 0 → k ≠ Fin.last (n + 1) →
      (schwarzChristoffelVertex a e z₀ 0).im < (schwarzChristoffelVertex a e z₀ k).im)
    (i : Fin (n + 1)) (z : ℂ)
    (hzi : z ∈ (schwarzChristoffelPolygon a e z₀).edgeSet ℝ i.castSucc.castSucc)
    (hzleft : z ∈ (schwarzChristoffelPolygon a e z₀).edgeSet ℝ (Fin.last (n + 2))) :
    z = schwarzChristoffelVertex a e z₀ 0 := by
  let V := schwarzChristoffelVertex a e z₀
  let Vinf := schwarzChristoffelVertexAtInfinity a e z₀
  have hn : 0 < n := by
    by_contra h
    have hn0 : n = 0 := by omega
    subst n
    have hs : e 0 + e 1 = -2 := by simpa [Fin.sum_univ_succ] using hsum
    linarith [he 0, he 1]
  obtain ⟨hr, hl⟩ :=
    schwarzChristoffelVertex_last_lt_vertexAtInfinity_lt_vertex_zero a e z₀ ha he hsum
  have hline : ((1 : ℂ) * (V 0 - Vinf)).im = 0 := by
    simp [V, Vinf, Complex.sub_im, (Complex.lt_def.mp hl).2]
  rw [schwarzChristoffelPolygon_edgeSet_castSucc_castSucc] at hzi
  rw [schwarzChristoffelPolygon_edgeSet_last] at hzleft
  by_cases hi0 : i = 0
  · have hsucc : i.succ ≠ Fin.last (n + 1) := by
      rw [hi0, Ne, Fin.ext_iff]
      simp only [Fin.val_succ, Fin.val_zero, Fin.val_last]
      omega
    have hh : 0 < ((1 : ℂ) * (V i.succ - Vinf)).im := by
      simpa [V, Vinf, Complex.sub_im, (Complex.lt_def.mp hl).2] using
        hheight i.succ (Fin.succ_ne_zero i) hsucc
    have hstart : ((1 : ℂ) * (V i.castSucc - Vinf)).im = 0 := by
      simpa [hi0, V] using hline
    have hz := eq_left_of_mem_segment_of_im_mul_sub_pos 1 Vinf (V 0)
      (V i.castSucc) (V i.succ) z hline hstart hh hzleft hzi
    simpa [hi0, V] using hz
  · by_cases hilast : i.succ = Fin.last (n + 1)
    · have hstart : i.castSucc ≠ (0 : Fin (n + 2)) := by
        intro h
        apply hi0
        apply Fin.ext
        simpa only [Fin.val_castSucc, Fin.val_zero] using (congrArg Fin.val h)
      have hh : 0 < ((1 : ℂ) * (V i.castSucc - Vinf)).im := by
        simpa [V, Vinf, Complex.sub_im, (Complex.lt_def.mp hl).2] using
          hheight i.castSucc hstart (Fin.castSucc_lt_last i).ne
      have hend : ((1 : ℂ) * (V i.succ - Vinf)).im = 0 := by
        simp [hilast, V, Vinf, Complex.sub_im, (Complex.lt_def.mp hr).2]
      have hzi' : z ∈ segment ℝ (V i.succ) (V i.castSucc) := by
        rwa [segment_symm]
      have hz := eq_left_of_mem_segment_of_im_mul_sub_pos 1 Vinf (V 0)
        (V i.succ) (V i.castSucc) z hline hend hh hzleft hzi'
      have hzge := (segment_subset_Icc hl.le hzleft).1
      exact ((not_le_of_gt hr) (by simpa [hilast, V, Vinf, hz] using hzge)).elim
    · have hstart : i.castSucc ≠ (0 : Fin (n + 2)) := by
        intro h
        apply hi0
        apply Fin.ext
        simpa only [Fin.val_castSucc, Fin.val_zero] using (congrArg Fin.val h)
      have hh₁ : 0 < ((1 : ℂ) * (V i.castSucc - Vinf)).im := by
        simpa [V, Vinf, Complex.sub_im, (Complex.lt_def.mp hl).2] using
          hheight i.castSucc hstart (Fin.castSucc_lt_last i).ne
      have hh₂ : 0 < ((1 : ℂ) * (V i.succ - Vinf)).im := by
        simpa [V, Vinf, Complex.sub_im, (Complex.lt_def.mp hl).2] using
          hheight i.succ (Fin.succ_ne_zero i) hilast
      exact (Set.disjoint_left.mp
        (disjoint_segment_of_im_mul_sub_pos 1 Vinf (V 0)
          (V i.castSucc) (V i.succ) hline hh₁ hh₂) hzleft hzi).elim

/-- If all intermediate vertices are strictly above the horizontal closing line, a bounded
side meets the right closing side only at the last finite vertex. -/
theorem schwarzChristoffelPolygon_bounded_edgeSet_last_prevertex_eq_last_vertex_of_heights
    (a e : Fin (n + 2) → ℝ) (z₀ : UpperHalfPlane) (ha : StrictMono a)
    (he : ∀ k, -1 < e k) (hsum : ∑ k, e k = -2)
    (hheight : ∀ k : Fin (n + 2), k ≠ 0 → k ≠ Fin.last (n + 1) →
      (schwarzChristoffelVertex a e z₀ 0).im < (schwarzChristoffelVertex a e z₀ k).im)
    (i : Fin (n + 1)) (z : ℂ)
    (hzi : z ∈ (schwarzChristoffelPolygon a e z₀).edgeSet ℝ i.castSucc.castSucc)
    (hzright : z ∈ (schwarzChristoffelPolygon a e z₀).edgeSet ℝ
      (Fin.last (n + 1)).castSucc) :
    z = schwarzChristoffelVertex a e z₀ (Fin.last (n + 1)) := by
  let V := schwarzChristoffelVertex a e z₀
  let Vinf := schwarzChristoffelVertexAtInfinity a e z₀
  have hn : 0 < n := by
    by_contra h
    have hn0 : n = 0 := by omega
    subst n
    have hs : e 0 + e 1 = -2 := by simpa [Fin.sum_univ_succ] using hsum
    linarith [he 0, he 1]
  obtain ⟨hr, hl⟩ :=
    schwarzChristoffelVertex_last_lt_vertexAtInfinity_lt_vertex_zero a e z₀ ha he hsum
  have hbase : (V (Fin.last (n + 1))).im = (V 0).im :=
    (Complex.lt_def.mp hr).2.trans (Complex.lt_def.mp hl).2
  have hline : ((1 : ℂ) * (Vinf - V (Fin.last (n + 1)))).im = 0 := by
    simp [V, Vinf, Complex.sub_im, (Complex.lt_def.mp hr).2]
  rw [schwarzChristoffelPolygon_edgeSet_castSucc_castSucc] at hzi
  rw [schwarzChristoffelPolygon_edgeSet_last_prevertex] at hzright
  by_cases hi0 : i = 0
  · have hsucc : i.succ ≠ Fin.last (n + 1) := by
      rw [hi0, Ne, Fin.ext_iff]
      simp only [Fin.val_succ, Fin.val_zero, Fin.val_last]
      omega
    have hh : 0 < ((1 : ℂ) * (V i.succ - V (Fin.last (n + 1)))).im := by
      simpa [V, Complex.sub_im, hbase] using
        hheight i.succ (Fin.succ_ne_zero i) hsucc
    have hstart : ((1 : ℂ) * (V i.castSucc - V (Fin.last (n + 1)))).im = 0 := by
      simp [hi0, V, Complex.sub_im, hbase]
    have hz := eq_left_of_mem_segment_of_im_mul_sub_pos 1
      (V (Fin.last (n + 1))) Vinf (V i.castSucc) (V i.succ) z
      hline hstart hh hzright hzi
    have hzle := (segment_subset_Icc hr.le hzright).2
    exact ((not_le_of_gt hl) (by simpa [hi0, V, Vinf, hz] using hzle)).elim
  · by_cases hilast : i.succ = Fin.last (n + 1)
    · have hstart : i.castSucc ≠ (0 : Fin (n + 2)) := by
        intro h
        apply hi0
        apply Fin.ext
        simpa only [Fin.val_castSucc, Fin.val_zero] using (congrArg Fin.val h)
      have hh : 0 < ((1 : ℂ) * (V i.castSucc - V (Fin.last (n + 1)))).im := by
        simpa [V, Complex.sub_im, hbase] using
          hheight i.castSucc hstart (Fin.castSucc_lt_last i).ne
      have hend : ((1 : ℂ) * (V i.succ - V (Fin.last (n + 1)))).im = 0 := by
        simp [hilast]
      have hzi' : z ∈ segment ℝ (V i.succ) (V i.castSucc) := by
        rwa [segment_symm]
      have hz := eq_left_of_mem_segment_of_im_mul_sub_pos 1
        (V (Fin.last (n + 1))) Vinf (V i.succ) (V i.castSucc) z
        hline hend hh hzright hzi'
      simpa [hilast, V] using hz
    · have hstart : i.castSucc ≠ (0 : Fin (n + 2)) := by
        intro h
        apply hi0
        apply Fin.ext
        simpa only [Fin.val_castSucc, Fin.val_zero] using (congrArg Fin.val h)
      have hh₁ : 0 < ((1 : ℂ) * (V i.castSucc - V (Fin.last (n + 1)))).im := by
        simpa [V, Complex.sub_im, hbase] using
          hheight i.castSucc hstart (Fin.castSucc_lt_last i).ne
      have hh₂ : 0 < ((1 : ℂ) * (V i.succ - V (Fin.last (n + 1)))).im := by
        simpa [V, Complex.sub_im, hbase] using
          hheight i.succ (Fin.succ_ne_zero i) hilast
      exact (Set.disjoint_left.mp
        (disjoint_segment_of_im_mul_sub_pos 1 (V (Fin.last (n + 1))) Vinf
          (V i.castSucc) (V i.succ) hline hh₁ hh₂) hzright hzi).elim

end TauCeti
