/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Compactification
public import TauCeti.Data.Fin.Basic
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Polygon.Basic
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.UnboundedEdge

/-!
# The Schwarz--Christoffel compactified boundary is polygonal

For a nondecreasing finite family of prevertices, the real projective line splits into the
two unbounded intervals and the intervals between consecutive prevertices.  The
Schwarz--Christoffel boundary map carries each finite interval onto its bounded side.  The real
points in the two unbounded intervals trace the two sides incident to the common vertex at infinity
with that vertex omitted; compactification supplies the omitted vertex.

Consequently the range of the compactified boundary map is exactly the boundary of the packaged
polygon.  This identification does not require the polygon to be simple; proving that distinct
nonadjacent sides do not meet is the separate global injectivity problem.

## Main result

* `TauCeti.range_schwarzChristoffelCompactifiedBoundary` -- the compactified boundary map traces
  exactly the boundary of `schwarzChristoffelPolygon`.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
-/

public section

noncomputable section

open Complex Set UpperHalfPlane
open scoped OnePoint

namespace TauCeti

variable {n : ℕ}

/-- Let `g` be a map from the projective line to `ℂ` with `g ∞ = V` that agrees with `B` on the
reals.  If `B` carries each interval between consecutive `a i` onto the side between consecutive
vertices `P`, and the two unbounded intervals onto the two sides at `V` with `V` omitted, then the
range of `g` lies in the union of the sides. -/
private lemma range_subset_union_segments {n : ℕ} (a : Fin (n + 1) → ℝ) (g : OnePoint ℝ → ℂ)
    (B : ℝ → ℂ) (P : Fin (n + 1) → ℂ) (V : ℂ) (hinfty : g ∞ = V) (hcoe : ∀ x : ℝ, g x = B x)
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
private lemma union_segments_subset_range {n : ℕ} (a : Fin (n + 1) → ℝ) (g : OnePoint ℝ → ℂ)
    (B : ℝ → ℂ) (P : Fin (n + 1) → ℂ) (V : ℂ) (hinfty : g ∞ = V) (hcoe : ∀ x : ℝ, g x = B x)
    (hbounded : ∀ i : Fin n,
      B '' Icc (a i.castSucc) (a i.succ) = segment ℝ (P i.castSucc) (P i.succ))
    (hright : B '' Ici (a (Fin.last n)) = segment ℝ (P (Fin.last n)) V \ {V})
    (hleft : B '' Iic (a 0) = segment ℝ (P 0) V \ {V}) :
    (⋃ i : Fin n, segment ℝ (P i.castSucc) (P i.succ)) ∪
      segment ℝ (P (Fin.last n)) V ∪ segment ℝ V (P 0) ⊆ Set.range g := by
  have hside {s : Set ℝ} {S : Set ℂ} (hs : B '' s = S \ {V}) {z : ℂ} (hz : z ∈ S) :
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


/-- **The compactified Schwarz--Christoffel boundary traces the polygon boundary.**  For ordered
prevertices, integrability at every finite prevertex and decay at infinity make each
closed finite interval map onto its corresponding bounded side.  Each unbounded interval traces
its side with the common vertex at infinity omitted, and the compactified point supplies that
vertex.  Their union is the complete boundary of `schwarzChristoffelPolygon`.

No simplicity hypothesis is needed: this is an equality of ranges even when nonadjacent polygon
sides intersect. -/
theorem range_schwarzChristoffelCompactifiedBoundary (a e : Fin (n + 1) → ℝ)
    (z₀ : UpperHalfPlane) (ha : Monotone a)
    (hfinite : ∀ j, -1 < ∑ i with a i = a j, e i) (hinfty : ∑ i, e i < -1) :
    Set.range (schwarzChristoffelCompactifiedBoundary a e z₀) =
      (schwarzChristoffelPolygon a e z₀).boundary ℝ := by
  have hfinite' (i : Fin n) : ∀ j, e j ≠ 0 → a j ∉ Ioo (a i.castSucc) (a i.succ) :=
    fun j _ ↦ not_mem_Ioo_castSucc_succ a ha i j
  have hb := fun i : Fin n ↦ schwarzChristoffelBoundary_image_Icc_prevertex a e z₀
    (ha i.castSucc_le_succ) (hfinite' i) (hfinite i.castSucc) (hfinite i.succ)
  have hr := schwarzChristoffelBoundary_image_Ici_prevertex a e z₀ (Fin.last n)
    (hfinite (Fin.last n)) (fun i _ ↦ ha i.le_last) hinfty
  have hl := schwarzChristoffelBoundary_image_Iic_prevertex a e z₀ 0
    (hfinite 0) (fun i _ ↦ ha i.zero_le) hinfty
  rw [schwarzChristoffelPolygon_boundary]
  exact (range_subset_union_segments a _ _ _ _
    (schwarzChristoffelCompactifiedBoundary_infty a e z₀)
    (schwarzChristoffelCompactifiedBoundary_coe a e z₀) hb hr hl).antisymm
    (union_segments_subset_range a _ _ _ _
      (schwarzChristoffelCompactifiedBoundary_infty a e z₀)
      (schwarzChristoffelCompactifiedBoundary_coe a e z₀) hb hr hl)

end TauCeti
