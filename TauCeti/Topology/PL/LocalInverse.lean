/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.PL.Map
public import Mathlib.Analysis.Normed.Module.FiniteDimension
import TauCeti.Analysis.Convex.Combination
import TauCeti.Analysis.Convex.SimplicialComplex.Arrangement
import TauCeti.Analysis.Convex.SimplicialComplex.Carrier
import TauCeti.Analysis.Convex.SimplicialComplex.Neighborhood
import TauCeti.Topology.PL.Inverse

/-!
# Local inverses of piecewise-linear maps

A local inverse of a piecewise-linear map is piecewise linear. Let `f : E → F` be piecewise
linear within a convex polyhedron `P` at a point `g a`, and let `g` be continuous within `t` at
`a`, mapping `t` into `P` near `a`, with `f ∘ g = id` near `a` in `t` and `g ∘ f = id` near `g a`
in `P`. Then `g` is piecewise linear within `t` at `a`
(`TauCeti.IsPLWithinAt.of_local_left_inverse`). The polyhedron `P` is typically the range of a
model with corners: the whole space, or a half-space.

This is the local statement behind the fact that a PL homeomorphism of PL manifolds has a PL
inverse, `TauCeti.IsPLMap.symm` in `TauCeti.Geometry.Manifold.PLGroupoid.Inverse`.

The local inverse theorem rests on a local triangulation of PL maps. Near a point, a map PL
within `P` agrees with an affine map on each of finitely many simplices contained in `P`, which
cover `P` near the point (`TauCeti.IsPLWithinAt.exists_simplex_cover`). These simplices come from
subdividing a small simplex around the point along `P` and the cells of the map. For a local
inverse, the map is moreover injective on each simplex, so it keeps their vertices affinely
independent, and the inverse criterion for simplexwise affine maps,
`TauCeti.isPiecewiseAffineOn_inverse_of_finite_simplex_cover`, makes `g` piecewise affine on the
image of the cover, a neighbourhood of `a` in `t` by continuity of `g`.

Reference: C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer
(1972), Chapter 1 (PL maps and their inverses) and Chapter 2 (triangulating PL maps).
-/

public section

open Set Filter Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {P : Set E} {x : E}

/-- **Simplexwise affine germs.** Let `f` be piecewise linear within a convex polyhedron `P` at
`x`. Then near `x`, inside any prescribed neighbourhood `O`, the polyhedron `P` is covered by
finitely many simplices contained in `P`, on each of which `f` agrees with a continuous affine
map. -/
theorem IsPLWithinAt.exists_simplex_cover {G : Type*} [AddCommGroup G] [Module ℝ G]
    [TopologicalSpace G] {f : E → G} (hP : IsConvexPolyhedron P)
    (hf : IsPLWithinAt f P x) {O : Set E} (hO : O ∈ 𝓝 x) :
    ∃ T : Set (Finset E), T.Finite ∧ ⋃ s ∈ T, convexHull ℝ (s : Set E) ∈ 𝓝[P] x ∧
      ∀ s ∈ T, AffineIndependent ℝ ((↑) : ↥(s : Set E) → E) ∧
        convexHull ℝ (s : Set E) ⊆ P ∩ O ∧
          ∃ A : E →ᴬ[ℝ] G, EqOn f A (convexHull ℝ (s : Set E)) := by
  classical
  obtain ⟨V, -, hV, hpa⟩ := isPLWithinAt_iff.1 hf
  obtain ⟨n, C, A, hC, hcov, heq⟩ := isPiecewiseAffineOn_iff.1 hpa
  -- A finite complex `K` around `x` whose part in `P` lies in `O` and in the domain `V` of the
  -- decomposition of `f`.
  obtain ⟨U, hU, hUsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 (inter_mem hV
    (mem_nhdsWithin_of_mem_nhds hO))
  obtain ⟨K, hKfin, hKnhds, hKU⟩ :=
    Geometry.SimplicialComplex.exists_finite_space_mem_nhds_subset hU
  have hPK {z : E} (hz : z ∈ P) (hzK : z ∈ K.space) : z ∈ V ∧ z ∈ O := hUsub ⟨hKU hzK, hz⟩
  -- Subdivide `K` along `P` and the cells of `f`, and keep the simplices lying in `P`.
  obtain ⟨K', hK'K, hK'fin, hK'sub⟩ :=
    Geometry.SimplicialComplex.exists_isSubdivision_convexHull_subset_of_inter_nonempty hKfin
      (C := fun o : Option (Fin n) => o.elim P C) (Option.rec hP hC)
  have hK'space {s : Finset E} (hs : s ∈ K'.faces) : convexHull ℝ (s : Set E) ⊆ K.space :=
    hK'K.space_eq ▸ Geometry.SimplicialComplex.convexHull_subset_space hs
  refine ⟨{s | s ∈ K'.faces ∧ convexHull ℝ (s : Set E) ⊆ P},
    hK'fin.subset fun _ ⟨hs, _⟩ => hs, ?_, fun s ⟨hs, hsP⟩ => ?_⟩
  · -- The kept simplices cover the part of `P` in `|K|`.
    refine mem_of_superset (inter_mem_nhdsWithin P hKnhds) fun z ⟨hzP, hzK⟩ => ?_
    obtain ⟨s, ⟨hs, hzs⟩, -⟩ :=
      Geometry.SimplicialComplex.existsUnique_mem_intrinsicInterior (hK'K.space_eq ▸ hzK)
    exact mem_biUnion (x := s) ⟨hs, hK'sub s hs none ⟨z, hzs, hzP⟩⟩ (intrinsicInterior_subset hzs)
  · refine ⟨K'.indep hs, fun z hz => ⟨hsP hz, (hPK (hsP hz) (hK'space hs hz)).2⟩, ?_⟩
    -- A point of the open simplex lies in some cell `C j`; then the whole simplex does.
    obtain ⟨p, hp⟩ := ((Finset.coe_nonempty.2 (K'.nonempty_of_mem_faces hs)).convexHull
      (𝕜 := ℝ)).intrinsicInterior (convex_convexHull ℝ _)
    have hpK := hPK (hsP (intrinsicInterior_subset hp)) (hK'space hs (intrinsicInterior_subset hp))
    obtain ⟨j, hj⟩ := mem_iUnion.1 (hcov hpK.1)
    have hsC : convexHull ℝ (s : Set E) ⊆ C j := hK'sub s hs (some j) ⟨p, hp, hj⟩
    exact ⟨A j, fun z hz => heq j ⟨(hPK (hsP hz) (hK'space hs hz)).1, hsC hz⟩⟩

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {f : E → F} {g : F → E} {t : Set F} {a : F}

/-- **A local inverse of a PL map is PL.** Let `f` be piecewise linear within a convex
polyhedron `P` at `g a`, and let `g` be continuous within `t` at `a ∈ t`. If near `a` in `t` the
map `g` takes values in `P` and is a right inverse of `f`, and near `g a` in `P` it is a left
inverse of `f`, then `g` is piecewise linear within `t` at `a`. -/
theorem IsPLWithinAt.of_local_left_inverse (hP : IsConvexPolyhedron P)
    (hf : IsPLWithinAt f P (g a)) (hg : ContinuousWithinAt g t a) (ha : a ∈ t)
    (hfg : ∀ᶠ y in 𝓝[t] a, g y ∈ P ∧ f (g y) = y) (hgf : ∀ᶠ z in 𝓝[P] (g a), g (f z) = z) :
    IsPLWithinAt g t a := by
  obtain ⟨hgaP, hfga⟩ := hfg.self_of_nhdsWithin ha
  obtain ⟨O, hO, hOsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hgf
  obtain ⟨T, hTfin, hTnhds, hT⟩ := hf.exists_simplex_cover hP hO
  choose hind hsub A hA using hT
  have : Finite T := hTfin.to_subtype
  have hgf' {s : T} {z : E} (hz : z ∈ convexHull ℝ (s.1 : Set E)) : g (f z) = z :=
    hOsub ⟨(hsub s.1 s.2 hz).2, (hsub s.1 s.2 hz).1⟩
  -- `f` is affine and injective on each simplex, so it keeps its vertices affinely independent.
  have hindT (s : T) : AffineIndependent ℝ ((↑) : (A s.1 s.2 '' (s.1 : Set E)) → F) := by
    have hinj : InjOn (A s.1 s.2) (convexHull ℝ (range ((↑) : (s.1 : Set E) → E))) := by
      rw [Subtype.range_coe]
      intro z hz w hw hzw
      rw [← hgf' hz, ← hgf' hw, hA s.1 s.2 hz, hA s.1 s.2 hw, hzw]
    have hrange : range ((A s.1 s.2).toAffineMap ∘ ((↑) : (s.1 : Set E) → E)) =
        A s.1 s.2 '' (s.1 : Set E) := by
      rw [range_comp, Subtype.range_coe]
      rfl
    exact ((hind s.1 s.2).map_of_injOn_convexHull (A s.1 s.2).toAffineMap hinj).range.mono
      hrange.ge
  have hpiece := isPiecewiseAffineOn_inverse_of_finite_simplex_cover (fun s : T => (s.1 : Set E))
    (fun s => A s.1 s.2) (fun s => hA s.1 s.2) hindT fun z hz => by
      obtain ⟨s, hs⟩ := mem_iUnion.1 hz
      exact hgf' hs
  rw [← biUnion_eq_iUnion T fun s _ => convexHull ℝ (s : Set E)] at hpiece
  -- The image of the cover is a neighbourhood of `a` in `t`, since `g` maps `t` into `P`.
  have hg' : Tendsto g (𝓝[t] a) (𝓝[P] (g a)) :=
    tendsto_nhdsWithin_iff.2 ⟨hg, hfg.mono fun _ h => h.1⟩
  refine isPLWithinAt_iff.2 ⟨f '' ⋃ s ∈ T, convexHull ℝ (s : Set E),
    ⟨g a, mem_of_mem_nhdsWithin hgaP hTnhds, hfga⟩, ?_, hpiece⟩
  filter_upwards [hfg, hg' hTnhds] with y hy hyT
  exact ⟨g y, hyT, hy.2⟩

end TauCeti
