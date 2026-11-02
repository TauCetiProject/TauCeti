/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Convex.Intrinsic
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import TauCeti.Analysis.Convex.Intrinsic

/-!
# Open simplices

The *open simplex* spanned by an affinely independent finite family `p` of points of a
finite-dimensional real normed space is the intrinsic interior of its convex hull. This file
identifies it with the set of affine combinations of `p` with all weights positive
(`AffineIndependent.mem_intrinsicInterior_convexHull_iff`), and shows that a proper face misses
it: a point of the open simplex lying in the convex hull of `p '' s` forces `s` to contain every
index (`AffineIndependent.eq_univ_of_mem_intrinsicInterior_convexHull`).

So the open simplices of the faces of a simplex partition it, which is what makes the open
simplices of a geometric simplicial complex disjoint
(`Geometry.SimplicialComplex.eq_of_mem_intrinsicInterior`).

The proofs read the weights through barycentric coordinates: extending `p` to an affine basis of
the whole space (Mathlib's `exists_subset_affineIndependent_affineSpan_eq_top`) gives continuous
affine functions which read off the weight of each point of `p` in every affine combination.

## Main results

* `AffineIndependent.mem_intrinsicInterior_convexHull_iff`: the intrinsic interior of the convex
  hull of an affinely independent finite family consists of its affine combinations with positive
  weights.
* `AffineIndependent.eq_univ_of_mem_intrinsicInterior_convexHull`: a proper face of a simplex
  misses its intrinsic interior.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton (1970), Theorem 6.9 (the relative interior of a
  convex hull).
* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapter 2 (open simplices).
-/

public section

open Set Finset Filter Topology

section AffineIndependent

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {p : ι → E}

/-- Continuous barycentric coordinates of an affinely independent family: continuous affine
functions on the whole space which read off the weights of every affine combination of the
family, and so take the value `1` at the corresponding point and `0` at the others. -/
private theorem AffineIndependent.exists_coord (hp : AffineIndependent ℝ p) :
    ∃ f : ι → E →ᵃ[ℝ] ℝ, (∀ i, Continuous (f i)) ∧ (∀ w : ι → ℝ, ∑ j, w j = 1 → ∀ i,
      f i (Finset.univ.affineCombination ℝ p w) = w i) ∧ (∀ i, f i (p i) = 1) ∧
      ∀ i j, i ≠ j → f i (p j) = 0 := by
  classical
  obtain ⟨t, hst, hti, hts⟩ := exists_subset_affineIndependent_affineSpan_eq_top
    (hp.range (k := ℝ))
  -- The points of `t` form an affine basis of the space, whose coordinates are the `f i`.
  let b : AffineBasis t ℝ E := ⟨fun q => q, hti, by simpa using hts⟩
  have hcoord : ∀ i j, b.coord ⟨p i, hst (mem_range_self i)⟩ (p j) = if i = j then 1 else 0 :=
    fun i j => by
      -- `b` is the inclusion of `t`, so the basis point at `p j` is `p j` by definition.
      rw [show p j = b ⟨p j, hst (mem_range_self j)⟩ from rfl, b.coord_apply]
      simp [hp.injective.eq_iff]
  refine ⟨fun i => b.coord ⟨p i, hst (mem_range_self i)⟩,
    fun i => continuous_barycentric_coord b _, fun w hw i => ?_, fun i => by simp [hcoord],
    fun i j hij => by simp [hcoord, hij]⟩
  rw [Finset.map_affineCombination _ _ _ hw,
    Finset.affineCombination_eq_linear_combination _ _ _ hw]
  simp [hcoord]

omit [Fintype ι] [FiniteDimensional ℝ E] in
/-- An affine function taking the value `1` at `p i` and `0` at the other points of the family is
nonnegative on the convex hull of the family. -/
private theorem convexHull_subset_coord_nonneg (f : E →ᵃ[ℝ] ℝ) {i : ι} (hfi : f (p i) = 1)
    (hf : ∀ j, i ≠ j → f (p j) = 0) : convexHull ℝ (range p) ⊆ {x | 0 ≤ f x} := by
  refine convexHull_min ?_ ((convex_Ici 0).affine_preimage f)
  rintro _ ⟨j, rfl⟩
  rcases eq_or_ne i j with rfl | hij
  · simp [hfi]
  · simp [hf j hij]

/-- **The open simplex.** A point lies in the intrinsic interior of the convex hull of an affinely
independent finite family exactly when it is an affine combination of the family with all weights
positive. -/
theorem AffineIndependent.mem_intrinsicInterior_convexHull_iff (hp : AffineIndependent ℝ p)
    {x : E} : x ∈ intrinsicInterior ℝ (convexHull ℝ (range p)) ↔
      ∃ w : ι → ℝ, (∀ i, 0 < w i) ∧ ∑ i, w i = 1 ∧ Finset.univ.affineCombination ℝ p w = x := by
  obtain ⟨f, hfc, hf, hfi, hfj⟩ := hp.exists_coord
  rw [TauCeti.mem_intrinsicInterior_iff_eventually, affineSpan_convexHull]
  constructor
  · rintro ⟨hx, hev⟩
    obtain ⟨w, hw, rfl⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hx
    refine ⟨w, fun i => ?_, hw, rfl⟩
    set x := Finset.univ.affineCombination ℝ p w
    have hnn := convexHull_subset_coord_nonneg (f i) (hfi i) (hfj i)
    have hx0 : 0 ≤ w i := hf w hw i ▸ hnn (hev.self_of_nhds hx)
    refine hx0.lt_of_ne fun hwi => ?_
    -- Moving from `x` slightly away from `p i` stays in the convex hull, where `f i ≥ 0`, but
    -- makes the weight of `p i` negative.
    have hcont : Tendsto (fun ε : ℝ => AffineMap.lineMap x (p i) ε) (𝓝 0) (𝓝 x) := by
      simpa using (AffineMap.lineMap_continuous (R := ℝ) (p := x) (q := p i)).tendsto (0 : ℝ)
    obtain ⟨ε, hε, hεneg⟩ := (((hcont.eventually hev).filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin (s := Iio 0))).exists
    have hmem : 0 ≤ f i (AffineMap.lineMap x (p i) ε) :=
      hnn (hε (AffineMap.lineMap_mem _ hx (subset_affineSpan _ _ (mem_range_self i))))
    have hfx : f i x = 0 := (hf w hw i).trans hwi.symm
    rw [AffineMap.apply_lineMap, hfx, hfi i, AffineMap.lineMap_apply_ring'] at hmem
    linarith [mem_Iio.1 hεneg]
  · rintro ⟨w, hw₀, hw₁, rfl⟩
    refine ⟨affineCombination_mem_affineSpan hw₁ p, ?_⟩
    have hev : ∀ᶠ y in 𝓝 (Finset.univ.affineCombination ℝ p w), ∀ i, 0 < f i y :=
      Filter.eventually_all.2 fun i => (hfc i).continuousAt.eventually
        (lt_mem_nhds (by rw [hf w hw₁ i]; exact hw₀ i))
    filter_upwards [hev] with y hy hyA
    obtain ⟨v, hv, rfl⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hyA
    exact affineCombination_mem_convexHull (fun i _ => (hf v hv i ▸ hy i).le) hv

omit [Fintype ι] in
/-- **A proper face misses the open simplex.** If a point of the intrinsic interior of the convex
hull of an affinely independent finite family lies in the convex hull of the points indexed by
`s`, then `s` contains every index. -/
theorem AffineIndependent.eq_univ_of_mem_intrinsicInterior_convexHull [Finite ι]
    (hp : AffineIndependent ℝ p) {x : E} (hx : x ∈ intrinsicInterior ℝ (convexHull ℝ (range p)))
    {s : Set ι} (hs : x ∈ convexHull ℝ (p '' s)) : s = univ := by
  cases nonempty_fintype ι
  obtain ⟨f, -, hf, -, hfj⟩ := hp.exists_coord
  obtain ⟨w, hw₀, hw₁, rfl⟩ := hp.mem_intrinsicInterior_convexHull_iff.1 hx
  refine eq_univ_of_forall fun i => by_contra fun hi => (hw₀ i).ne' ?_
  -- The weight of `p i` vanishes on the convex hull of the other points.
  have hsub : convexHull ℝ (p '' s) ⊆ {y | f i y = 0} :=
    convexHull_min (by rintro _ ⟨j, hj, rfl⟩; exact hfj i j fun hij => hi (hij ▸ hj))
      ((convex_singleton 0).affine_preimage (f i))
  simpa [hf w hw₁ i] using hsub hs

end AffineIndependent
