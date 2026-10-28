/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Preorder.Chain
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Basic

/-!
# Edgewise subdivision of ordered simplicial complexes

The `k`-th *edgewise subdivision* of a simplicial complex `K` whose vertices are linearly ordered
cuts every simplex of `K` into small simplices by the hyperplanes on which a sum of barycentric
coordinates at consecutive vertices, for the vertex order, is a multiple of `1 / k`. Its vertices
are the points whose barycentric coordinates are multiples of `1 / k`. Such a point is an average
of `k` vertices of `K`, which we record as a monotone `k`-tuple `u` of vertices; its coordinate at
a vertex `v` is the number of entries `u l = v`, divided by `k`.

A nonempty finite set of such tuples spans a simplex when the tuples have all their entries in a
common face of `K`, form a chain `u⁰ ≤ u¹ ≤ ⋯ ≤ uᵐ` for the coordinatewise order, and interleave:
`u⁰ 0 ≤ u¹ 0 ≤ ⋯ ≤ uᵐ 0 ≤ u⁰ 1 ≤ u¹ 1 ≤ ⋯ ≤ uᵐ (k - 1)`. Given the chain condition, the
interleaving says exactly that every entry of every tuple is at most every later entry of every
tuple of the face. This is Segal's edgewise subdivision; on a single simplex it is Freudenthal's
triangulation. The face condition only involves the vertex order of `K`, which restricts to every
face, so the subdivisions of the simplices of `K` fit together along their common faces.

Unlike iterated barycentric subdivisions, whose simplices become arbitrarily thin, all simplices
of the edgewise subdivisions of a simplex fall into finitely many shapes up to translation and
scaling by `1 / k`; their uniform fatness is proved in
`TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Edgewise.Fatness`. This is what
Whitehead's secant approximation of smooth triangulations needs from a subdivision.

Identifying the realization of the edgewise subdivision with the realization of `K` is not done
here.

## Main definitions

* `PreAbstractSimplicialComplex.EdgewiseVertex K k`: the monotone `k`-tuples of vertices of `K`
  whose entries span a face of `K`.
* `PreAbstractSimplicialComplex.edgewiseSubdivision K k`: the `k`-th edgewise subdivision.
* `TauCeti.edgewisePoint u`: the point, in barycentric coordinates, at which the subdivision
  places the vertex `u`.

## Main results

* `PreAbstractSimplicialComplex.mem_edgewiseSubdivision_iff`: the face criterion.
* `PreAbstractSimplicialComplex.le_or_le_of_mem_edgewiseSubdivision` and
  `PreAbstractSimplicialComplex.le_of_lt_of_mem_edgewiseSubdivision`: the vertices of a face are
  comparable and interleave.
* `TauCeti.support_edgewisePoint`: the point of a tuple is supported on its entries.
* `TauCeti.edgewisePoint_mem_convexHull`: a tuple with entries in `σ` is placed in the closed
  simplex spanned by `σ`.

## References

* H. Freudenthal, *Simplizialzerlegungen von beschränkter Flachheit*, Ann. of Math. 43 (1942),
  580–582.
* G. Segal, *Configuration-spaces and iterated loop-spaces*, Invent. Math. 21 (1973), 213–221,
  Appendix 1.
* H. Edelsbrunner, D. R. Grayson, *Edgewise subdivision of a simplex*, Discrete Comput. Geom. 24
  (2000), 707–719.
-/

public section

open Finset

namespace PreAbstractSimplicialComplex

variable {ι : Type*} [LinearOrder ι]

/-- The vertices of the `k`-th edgewise subdivision of `K`: the monotone `k`-tuples of vertices of
`K` whose entries form a face of `K`. The tuple `u` stands for the average of the vertices
`u 0, …, u (k - 1)`. -/
abbrev EdgewiseVertex (K : PreAbstractSimplicialComplex ι) (k : ℕ) : Type _ :=
  {u : Fin k → ι // Monotone u ∧ univ.image u ∈ K}

/-- The `k`-th **edgewise subdivision** of `K`. A nonempty finite set of vertices is a face when
the entries of its tuples together form a face of `K`, it is a chain for the coordinatewise
order, and every entry of every tuple is at most every later entry of every tuple. -/
def edgewiseSubdivision (K : PreAbstractSimplicialComplex ι) (k : ℕ) :
    AbstractSimplicialComplex (K.EdgewiseVertex k) where
  faces := {ρ | ρ.Nonempty ∧ ρ.biUnion (fun u => univ.image u.1) ∈ K ∧
    IsChain (· ≤ ·) (ρ : Set (K.EdgewiseVertex k)) ∧
    ∀ u ∈ ρ, ∀ w ∈ ρ, ∀ j j' : Fin k, j < j' → u.1 j ≤ w.1 j'}
  isRelLowerSet_faces := by
    rintro ρ ⟨hne, hK, hchain, hcross⟩
    refine ⟨hne, fun τ hτρ hτ => ⟨hτ, ?_, hchain.mono (coe_subset.mpr hτρ),
      fun u hu w hw => hcross u (hτρ hu) w (hτρ hw)⟩⟩
    -- The entries of any vertex of `τ` already form a nonempty face of `K`.
    obtain ⟨u, hu⟩ := hτ
    refine (K.isRelLowerSet_faces hK).2 (biUnion_subset_biUnion_of_subset_left _ hτρ) ?_
    exact ((K.isRelLowerSet_faces u.2.2).1).mono (subset_biUnion_of_mem _ hu)
  singleton_mem u := by
    refine ⟨singleton_nonempty u, by simpa using u.2.2, Set.Subsingleton.isChain (by simp),
      ?_⟩
    simp only [mem_singleton]
    intro a ha b hb j j' hjj'
    rw [ha, hb]
    exact u.2.1 hjj'.le

variable {K : PreAbstractSimplicialComplex ι} {k : ℕ} {ρ : Finset (K.EdgewiseVertex k)}
  {u w : K.EdgewiseVertex k}

/-- A finite set of vertices is a face of the edgewise subdivision exactly when it is nonempty,
the entries of its tuples form a face of `K`, it is a chain for the coordinatewise order, and
every entry of every tuple is at most every later entry of every tuple. -/
@[simp]
theorem mem_edgewiseSubdivision_iff :
    ρ ∈ K.edgewiseSubdivision k ↔ ρ.Nonempty ∧ ρ.biUnion (fun u => univ.image u.1) ∈ K ∧
      IsChain (· ≤ ·) (ρ : Set (K.EdgewiseVertex k)) ∧
      ∀ u ∈ ρ, ∀ w ∈ ρ, ∀ j j' : Fin k, j < j' → u.1 j ≤ w.1 j' :=
  Iff.rfl

/-- The entries of the vertices of a face of the edgewise subdivision form a face of `K`. -/
theorem biUnion_image_mem_of_mem_edgewiseSubdivision (hρ : ρ ∈ K.edgewiseSubdivision k) :
    ρ.biUnion (fun u => univ.image u.1) ∈ K :=
  (mem_edgewiseSubdivision_iff.mp hρ).2.1

/-- Two vertices of a face of the edgewise subdivision are comparable coordinatewise. -/
theorem le_or_le_of_mem_edgewiseSubdivision (hρ : ρ ∈ K.edgewiseSubdivision k) (hu : u ∈ ρ)
    (hw : w ∈ ρ) : u ≤ w ∨ w ≤ u :=
  (mem_edgewiseSubdivision_iff.mp hρ).2.2.1.total (mem_coe.mpr hu) (mem_coe.mpr hw)

/-- In a face of the edgewise subdivision, every entry of every vertex is at most every later
entry of every vertex. -/
theorem le_of_lt_of_mem_edgewiseSubdivision (hρ : ρ ∈ K.edgewiseSubdivision k) (hu : u ∈ ρ)
    (hw : w ∈ ρ) {j j' : Fin k} (hjj' : j < j') : u.1 j ≤ w.1 j' :=
  (mem_edgewiseSubdivision_iff.mp hρ).2.2.2 u hu w hw j j' hjj'

end PreAbstractSimplicialComplex

namespace TauCeti

variable {ι : Type*} {k : ℕ}

/-- The point at which the edgewise subdivision places the tuple `u : Fin k → ι`: the average of
the vertices `u 0, …, u (k - 1)`, in barycentric coordinates. Its coordinate at `i` is the number
of entries `u l = i`, divided by `k`. -/
noncomputable def edgewisePoint (u : Fin k → ι) : ι →₀ ℝ :=
  (k : ℝ)⁻¹ • ∑ l, Finsupp.single (u l) 1

/-- The coordinate of `edgewisePoint u` at `i` is the proportion of entries of `u` equal to
`i`. -/
theorem edgewisePoint_apply [DecidableEq ι] (u : Fin k → ι) (i : ι) :
    edgewisePoint u i = (k : ℝ)⁻¹ * #{l | u l = i} := by
  simp [edgewisePoint, Finsupp.single_apply]

/-- The coordinates of `edgewisePoint u` that are nonzero are those at the entries of `u`. -/
@[simp]
theorem support_edgewisePoint [DecidableEq ι] (u : Fin k → ι) :
    (edgewisePoint u).support = univ.image u := by
  ext i
  rw [Finsupp.mem_support_iff, edgewisePoint_apply, mem_image]
  simp only [mem_univ, true_and]
  constructor
  · intro h
    by_contra! hi
    simp [hi] at h
  · rintro ⟨l, rfl⟩
    have hk : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Fin.pos l).ne'
    exact mul_ne_zero (inv_ne_zero hk)
      (Nat.cast_ne_zero.mpr (card_ne_zero.mpr ⟨l, mem_filter.mpr ⟨mem_univ l, rfl⟩⟩))

/-- A tuple of positive length with entries in `σ` is placed in the closed simplex spanned by
`σ`. -/
theorem edgewisePoint_mem_convexHull (hk : k ≠ 0) {u : Fin k → ι} {σ : Finset ι}
    (hu : ∀ l, u l ∈ σ) :
    edgewisePoint u ∈ convexHull ℝ ((fun v => Finsupp.single v (1 : ℝ)) '' (σ : Set ι)) := by
  rw [edgewisePoint, Finset.smul_sum]
  refine (convex_convexHull ℝ _).sum_mem (fun _ _ => by positivity) ?_
    fun l _ => subset_convexHull ℝ _ (Set.mem_image_of_mem _ (mem_coe.mpr (hu l)))
  simp [hk]

end TauCeti
