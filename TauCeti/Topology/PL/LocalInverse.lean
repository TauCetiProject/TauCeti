/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.PL.Map
public import Mathlib.Analysis.Normed.Module.FiniteDimension
import TauCeti.Analysis.Convex.Combination
import TauCeti.Topology.PL.Inverse
import TauCeti.Topology.PL.Simplicial

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
cover `P` near the point (`TauCeti.IsPLWithinAt.exists_simplex_cover` in
`TauCeti.Topology.PL.Simplicial`). For a local inverse, the map is moreover injective on each
simplex, so it keeps their vertices affinely independent, and the inverse criterion for
simplexwise affine maps, `TauCeti.isPiecewiseAffineOn_inverse_of_finite_simplex_cover`, makes `g`
piecewise affine on the image of the cover, a neighbourhood of `a` in `t` by continuity of `g`.

Reference: C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer
(1972), Chapter 1 (PL maps and their inverses) and Chapter 2 (triangulating PL maps).
-/

public section

open Set Filter Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {P : Set E} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
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
      rw [range_comp, Subtype.range_coe, ContinuousAffineMap.coe_toAffineMap]
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
