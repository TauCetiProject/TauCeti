/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.SimplicialComplex.Basic
public import TauCeti.Analysis.Normed.Affine.Interpolation
import Mathlib.Analysis.Convex.Topology
import Mathlib.Data.Set.UnionLift
import Mathlib.Topology.LocallyFinite

/-!
# Interpolation of vertex values on geometric simplicial complexes

Values prescribed at the vertices of a locally finite geometric simplicial complex extend to a
continuous function on its support which is affine on each closed simplex. The extension is unique
on the support.

The local affine maps are allowed to be defined on the whole ambient space, but only their
restrictions to the simplices are used: no compatibility away from those simplices is required.
The theorem includes the empty complex and zero-dimensional faces.

## References

* C. Rourke and B. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapter 1, for interpolation on simplices.
* S. Łojasiewicz, *Triangulation of semi-analytic sets*, Ann. Scuola Norm. Sup. Pisa (3) 18
  (1964), 449–474, §4, step IV, for the rectilinear sections with prescribed vertex heights.
-/

public section

open Set

namespace Geometry.SimplicialComplex

section Uniqueness

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {K : SimplicialComplex ℝ E} {f g : E → F}

/-- Two functions affine on each simplex and equal at the vertices agree on the whole support.
No continuity or local finiteness hypothesis is needed for uniqueness. -/
theorem eqOn_of_simplexwise_affine
    (hf : ∀ s ∈ K.faces, ∃ A : E →ᵃ[ℝ] F, EqOn f A (convexHull ℝ (s : Set E)))
    (hg : ∀ s ∈ K.faces, ∃ A : E →ᵃ[ℝ] F, EqOn g A (convexHull ℝ (s : Set E)))
    (hfg : EqOn f g K.vertices) : EqOn f g K.space := by
  intro x hx
  obtain ⟨s, hs, hxs⟩ := mem_space_iff.1 hx
  obtain ⟨A, hA⟩ := hf s hs
  obtain ⟨B, hB⟩ := hg s hs
  have hAB : EqOn A B (s : Set E) := by
    intro v hv
    have hvs := subset_convexHull ℝ (s : Set E) hv
    have hvK : v ∈ K.vertices :=
      K.down_closed hs (Finset.singleton_subset_iff.2 hv) (Finset.singleton_nonempty v)
    exact (hA hvs).symm.trans ((hfg hvK).trans (hB hvs))
  exact (hA hxs).trans ((AffineMap.eqOn_affineSpan hAB
    (convexHull_subset_affineSpan (s : Set E) hxs)).trans (hB hxs).symm)

end Uniqueness

section Existence

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F]

/-- Prescribed vertex values extend to a continuous, simplexwise-affine function on the support
of a locally finite geometric simplicial complex. Each local affine map interpolates precisely
the prescribed values on its vertices. Values of the extension outside the support are immaterial.
-/
theorem exists_continuousOn_simplexwise_affine (K : SimplicialComplex ℝ E)
    (hK : LocallyFinite fun s : K.faces => convexHull ℝ (s : Set E)) (h : E → F) :
    ∃ f : E → F, ContinuousOn f K.space ∧ EqOn f h K.vertices ∧
      ∀ s ∈ K.faces, ∃ A : E →ᴬ[ℝ] F,
        EqOn A h (s : Set E) ∧ EqOn f A (convexHull ℝ (s : Set E)) := by
  classical
  choose A hA using fun s : K.faces => (K.indep s.2).exists_continuousAffineMap_eqOn h
  have hagree (s t : K.faces) (x : E)
      (hxs : x ∈ convexHull ℝ (s : Set E)) (hxt : x ∈ convexHull ℝ (t : Set E)) :
      A s x = A t x := by
    have heq : EqOn (A s).toAffineMap (A t).toAffineMap ((s : Set E) ∩ t) :=
      fun v hv => (hA s hv.1).trans (hA t hv.2).symm
    exact AffineMap.eqOn_affineSpan heq
      (convexHull_subset_affineSpan _ (K.inter_subset_convexHull s.2 t.2 ⟨hxs, hxt⟩))
  let H : K.space → F := iUnionLift
    (fun s : K.faces => convexHull ℝ (s : Set E)) (fun s x => A s x)
    (fun s t x hs ht => hagree s t x hs ht) K.space (by
      intro x hx
      obtain ⟨s, hs, hxs⟩ := mem_space_iff.1 hx
      exact mem_iUnion.2 ⟨⟨s, hs⟩, hxs⟩)
  let f : E → F := fun x => if hx : x ∈ K.space then H ⟨x, hx⟩ else 0
  have hf (s : K.faces) : EqOn f (A s) (convexHull ℝ (s : Set E)) := by
    intro x hx
    have hxK := K.convexHull_subset_space s.2 hx
    simp only [f, hxK, ↓reduceDIte]
    exact iUnionLift_of_mem _ hx
  refine ⟨f, ?_, ?_, fun s hs => ⟨A ⟨s, hs⟩, hA ⟨s, hs⟩, hf ⟨s, hs⟩⟩⟩
  · have hspace : K.space = ⋃ s : K.faces, convexHull ℝ (s : Set E) := by
      ext x
      simp only [mem_space_iff, mem_iUnion, Subtype.exists, exists_prop]
    rw [hspace]
    exact hK.continuousOn_iUnion
      (fun s => (s.1.finite_toSet.isCompact_convexHull (𝕜 := ℝ)).isClosed)
      (fun s => (A s).continuous.continuousOn.congr (hf s))
  · intro v hv
    have hvs : v ∈ convexHull ℝ (({v} : Finset E) : Set E) := by simp
    exact (hf ⟨{v}, hv⟩ hvs).trans (hA ⟨{v}, hv⟩ (by simp))

end Existence

end Geometry.SimplicialComplex
