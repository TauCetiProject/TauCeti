/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.SimplicialComplex.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import TauCeti.Analysis.Convex.SimplicialComplex.Subdivision
import TauCeti.Analysis.Convex.Intrinsic
import TauCeti.Analysis.Convex.SimplicialComplex.Carrier
import TauCeti.Topology.LocallyFinite.Basic

/-!
# Common subdivisions of geometric simplicial complexes

A geometric simplicial complex `K'` is a **subdivision** of `K`
(`Geometry.SimplicialComplex.IsSubdivision K' K`, defined in
`TauCeti.Analysis.Convex.SimplicialComplex.Subdivision`) when it has the same underlying space
and each of its simplices lies in a simplex of `K`. This file proves that two locally finite
triangulations of the same polyhedron have a common subdivision
(`Geometry.SimplicialComplex.exists_isSubdivision_isSubdivision`), the basic comparison theorem of
piecewise-linear topology. More generally, for any two locally finite complexes `K` and `L` in a
finite-dimensional real normed space, the intersection `|K| ∩ |L|` of their underlying spaces is
triangulated by a locally finite complex each of whose simplices lies in a simplex of `K` and in a
simplex of `L` (`Geometry.SimplicialComplex.exists_space_eq_inter`).

The proof cuts `|K| ∩ |L|` into the convex cells `σ ∩ τ`, for the simplices `σ` of `K` and `τ`
of `L` whose open simplices meet. The intrinsic interior of such a cell is the intersection of the
two open simplices (`TauCeti.intrinsicInterior_inter`), so distinct cells have disjoint intrinsic
interiors, because the open simplices of a complex are disjoint
(`Geometry.SimplicialComplex.eq_of_mem_intrinsicInterior`). A point of the intrinsic frontier of
`σ ∩ τ` lies in the open simplices of faces `σ'` of `σ` and `τ'` of `τ`
(`Geometry.SimplicialComplex.exists_mem_faces_subset_mem_intrinsicInterior`), so in the strictly
smaller cell `σ' ∩ τ'`. These are the hypotheses under which a locally finite family of compact
convex cells has a simplicial subdivision (`Geometry.SimplicialComplex.exists_subdivision`).

## Main results

* `Geometry.SimplicialComplex.exists_space_eq_inter`: a triangulation of `|K| ∩ |L|` whose
  simplices lie in simplices of both `K` and `L`.
* `Geometry.SimplicialComplex.exists_isSubdivision_isSubdivision`: two locally finite
  triangulations of the same polyhedron have a common locally finite subdivision.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapter 2 (subdivisions; any two triangulations of a polyhedron have a common subdivision).
* J. F. P. Hudson, *Piecewise Linear Topology*, Benjamin (1969), Chapter I (cell complexes and
  their simplicial subdivisions).
* R. T. Rockafellar, *Convex Analysis*, Princeton (1970), Theorem 6.5 (relative interiors of
  intersections).
-/

public section

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {K L : SimplicialComplex ℝ E}

/-- **Triangulating the intersection of two polyhedra.** For locally finite geometric simplicial
complexes `K` and `L` in a finite-dimensional real normed space, there is a locally finite complex
`M` with underlying space `|K| ∩ |L|`, each of whose simplices lies both in a simplex of `K` and
in a simplex of `L`. -/
theorem exists_space_eq_inter (hK : LocallyFinite fun s : K.faces => convexHull ℝ (s : Set E))
    (hL : LocallyFinite fun t : L.faces => convexHull ℝ (t : Set E)) :
    ∃ M : SimplicialComplex ℝ E, M.space = K.space ∩ L.space ∧
      (∀ s ∈ M.faces, (∃ t ∈ K.faces, convexHull ℝ (s : Set E) ⊆ convexHull ℝ (t : Set E)) ∧
        ∃ t ∈ L.faces, convexHull ℝ (s : Set E) ⊆ convexHull ℝ (t : Set E)) ∧
      LocallyFinite fun s : M.faces => convexHull ℝ (s : Set E) := by
  -- The cells: `σ ∩ τ` for simplices `σ` of `K` and `τ` of `L` whose open simplices meet.
  let ι := {p : K.faces × L.faces // (intrinsicInterior ℝ (convexHull ℝ (p.1.1 : Set E)) ∩
    intrinsicInterior ℝ (convexHull ℝ (p.2.1 : Set E))).Nonempty}
  let P : ι → Set E := fun p => convexHull ℝ (p.1.1.1 : Set E) ∩ convexHull ℝ (p.1.2.1 : Set E)
  have hPv : ∀ p, Convex ℝ (P p) := fun p => (convex_convexHull ℝ _).inter (convex_convexHull ℝ _)
  have hPc : ∀ p, IsCompact (P p) := fun p =>
    (p.1.1.1.finite_toSet.isCompact_convexHull (𝕜 := ℝ)).inter_right
      (p.1.2.1.finite_toSet.isCompact_convexHull (𝕜 := ℝ)).isClosed
  have hri : ∀ p, intrinsicInterior ℝ (P p) =
      intrinsicInterior ℝ (convexHull ℝ (p.1.1.1 : Set E)) ∩
        intrinsicInterior ℝ (convexHull ℝ (p.1.2.1 : Set E)) := fun p =>
    TauCeti.intrinsicInterior_inter (convex_convexHull ℝ _) (convex_convexHull ℝ _) p.2
  -- Every point of `|K| ∩ |L|` lies in the intrinsic interior of a cell inside any given pair of
  -- simplices containing it.
  have hcell : ∀ ⦃x : E⦄ ⦃σ τ : Finset E⦄ (hσ : σ ∈ K.faces) (hτ : τ ∈ L.faces),
      x ∈ convexHull ℝ (σ : Set E) → x ∈ convexHull ℝ (τ : Set E) →
      ∃ q : ι, x ∈ intrinsicInterior ℝ (P q) ∧
        P q ⊆ convexHull ℝ (σ : Set E) ∩ convexHull ℝ (τ : Set E) := by
    intro x σ τ hσ hτ hxσ hxτ
    obtain ⟨σ', hσ', hσσ', hxσ'⟩ := exists_mem_faces_subset_mem_intrinsicInterior hσ hxσ
    obtain ⟨τ', hτ', hττ', hxτ'⟩ := exists_mem_faces_subset_mem_intrinsicInterior hτ hxτ
    let q : ι := ⟨(⟨σ', hσ'⟩, ⟨τ', hτ'⟩), x, hxσ', hxτ'⟩
    exact ⟨q, (hri q).symm ▸ ⟨hxσ', hxτ'⟩, inter_subset_inter
      (convexHull_mono (Finset.coe_subset.2 hσσ')) (convexHull_mono (Finset.coe_subset.2 hττ'))⟩
  have hPlf : LocallyFinite P := (hK.inter hL).comp_injective Subtype.val_injective
  have hdisj : Pairwise fun p q : ι => Disjoint (intrinsicInterior ℝ (P p))
      (intrinsicInterior ℝ (P q)) := by
    intro p q hpq
    refine Set.disjoint_left.2 fun x hxp hxq => hpq ?_
    rw [hri] at hxp hxq
    exact Subtype.ext (Prod.ext
      (Subtype.ext (eq_of_mem_intrinsicInterior p.1.1.2 q.1.1.2 hxp.1 hxq.1))
      (Subtype.ext (eq_of_mem_intrinsicInterior p.1.2.2 q.1.2.2 hxp.2 hxq.2)))
  have hfr := fun p => TauCeti.intrinsicFrontier_subset_iUnion_of_exists_mem_intrinsicInterior p
    (hPc p).isClosed fun x hx => hcell p.1.1.2 p.1.2.2 hx.1 hx.2
  obtain ⟨M, hMs, -, hMP, hMlf⟩ := exists_subdivision P hPc hPv (fun q => q.2.some)
    (fun q => (hri q).symm ▸ q.2.some_mem) hPlf hdisj hfr
  refine ⟨M, ?_, fun s hs => ?_, hMlf⟩
  · rw [hMs]
    ext x
    refine ⟨fun hx => ?_, fun ⟨hxK, hxL⟩ => ?_⟩
    · obtain ⟨p, hxp⟩ := mem_iUnion.1 hx
      exact ⟨mem_space_iff.2 ⟨_, p.1.1.2, hxp.1⟩, mem_space_iff.2 ⟨_, p.1.2.2, hxp.2⟩⟩
    · obtain ⟨σ, hσ, hxσ⟩ := mem_space_iff.1 hxK
      obtain ⟨τ, hτ, hxτ⟩ := mem_space_iff.1 hxL
      obtain ⟨q, hxq, -⟩ := hcell hσ hτ hxσ hxτ
      exact mem_iUnion.2 ⟨q, intrinsicInterior_subset hxq⟩
  · obtain ⟨p, -, hsp⟩ := hMP s hs
    have hconv : convexHull ℝ (s : Set E) ⊆ P p := convexHull_min hsp (hPv p)
    exact ⟨⟨_, p.1.1.2, hconv.trans inter_subset_left⟩,
      ⟨_, p.1.2.2, hconv.trans inter_subset_right⟩⟩

/-- **Common subdivision.** Two locally finite geometric simplicial complexes in a
finite-dimensional real normed space with the same underlying space have a common locally finite
subdivision. -/
theorem exists_isSubdivision_isSubdivision
    (hK : LocallyFinite fun s : K.faces => convexHull ℝ (s : Set E))
    (hL : LocallyFinite fun t : L.faces => convexHull ℝ (t : Set E)) (h : K.space = L.space) :
    ∃ M : SimplicialComplex ℝ E, M.IsSubdivision K ∧ M.IsSubdivision L ∧
      LocallyFinite fun s : M.faces => convexHull ℝ (s : Set E) := by
  obtain ⟨M, hM, hMKL, hMlf⟩ := exists_space_eq_inter hK hL
  exact ⟨M, ⟨by rw [hM, ← h, inter_self], fun s hs => (hMKL s hs).1⟩,
    ⟨by rw [hM, h, inter_self], fun s hs => (hMKL s hs).2⟩, hMlf⟩

end Geometry.SimplicialComplex
