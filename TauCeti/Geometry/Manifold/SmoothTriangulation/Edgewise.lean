/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Filter.AtTopBot.Basic
public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Edgewise.Basic
public import TauCeti.Geometry.Manifold.SmoothTriangulation.Basic

import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Edgewise.Fatness
import TauCeti.Geometry.Manifold.SmoothTriangulation.Secant

/-!
# Secant maps on edgewise subdivisions

Whitehead's and Munkres' proofs that a smooth manifold has an essentially unique smooth
triangulation (Munkres, Theorems 10.5 and 10.6) replace a smooth triangulation, simplex by simplex,
by its secant map on a fine subdivision, and need that secant map to be non-degenerate on every
simplex of the subdivision at once. The uniform secant approximation
`TauCeti.IsSimplexImmersion.exists_pos_forall_isSimplexImmersion_sum_smul` gives this on simplices
which are small and uniformly fat; iterated barycentric subdivisions are small but not uniformly
fat. The edgewise subdivisions are both: their simplices have mesh `1 / k` and fatness bounded
below independently of `k`.

This file combines the two. Let `g` be a `C¹` immersion of the closed simplex on `σ` into a
normed space. For all sufficiently large `k`, on every face `ρ` of the `k`-th edgewise subdivision
of any complex whose vertices have their entries in `σ`, the secant map of `g`, the map that is
linear in barycentric coordinates on `ρ` and sends each vertex `a` of `ρ` to `g` at the point
`edgewisePoint a`, is again an immersion.

## Main results

* `TauCeti.IsSimplexImmersion.eventually_isSimplexImmersion_edgewiseSubdivision`: the secant map
  of a `C¹` immersion of a simplex is an immersion on every face of all sufficiently fine edgewise
  subdivisions of that simplex.

## References

* J. H. C. Whitehead, *On C¹-complexes*, Ann. of Math. 41 (1940), 809–824.
* J. Munkres, *Elementary Differential Topology*, Annals of Math. Studies 54 (1966), Chapter II,
  Section 9 (secant approximations) and Theorems 10.5–10.6.
* H. Freudenthal, *Simplizialzerlegungen von beschränkter Flachheit*, Ann. of Math. 43 (1942),
  580–582.
-/

public section

open Finset AbstractSimplicialComplex PreAbstractSimplicialComplex Filter
open scoped Manifold ContDiff

namespace TauCeti.IsSimplexImmersion

variable {ι : Type*} [LinearOrder ι] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {n : WithTop ℕ∞} {σ : Finset ι} {g : StandardSimplex σ → E}

/-- **Secant approximation on edgewise subdivisions.** Let `g` be a `Cⁿ` immersion of the closed
simplex on `σ` into a normed space, with `1 ≤ n`, and let `K` be a simplicial complex on the same
ordered vertex set. For all sufficiently large `k`, for every face `ρ` of the `k`-th edgewise
subdivision of `K` whose vertices `a` are placed at points `p a` of the simplex on `σ`, the secant
map of `g` on `ρ`, the map of `ρ` that is linear in barycentric coordinates and sends each vertex
`a` to `g (p a)`, is a `Cᵐ` immersion of `ρ` for every `m`. -/
theorem eventually_isSimplexImmersion_edgewiseSubdivision (h : IsSimplexImmersion 𝓘(ℝ, E) n g)
    (hn : 1 ≤ n) (K : PreAbstractSimplicialComplex ι) :
    ∀ᶠ k in atTop, ∀ ρ ∈ K.edgewiseSubdivision k, ∀ p : ρ → StandardSimplex σ,
      (∀ a, (p a : ι →₀ ℝ) = edgewisePoint a.1.1) → ∀ m : WithTop ℕ∞,
        IsSimplexImmersion 𝓘(ℝ, E) m fun x : StandardSimplex ρ => ∑ a : ρ, x.1 a • g (p a) := by
  rcases σ.eq_empty_or_nonempty with rfl | hσ
  · -- The simplex on no vertices is empty, so there are no such faces.
    refine Eventually.of_forall fun k ρ hρ p _ => ?_
    obtain ⟨a, ha⟩ := (mem_edgewiseSubdivision_iff.mp hρ).1
    have hmem := (p ⟨a, ha⟩).2
    simp at hmem
  obtain ⟨δ, hδ, hsecant⟩ :=
    h.exists_pos_forall_isSimplexImmersion_sum_smul hn (t := ((2 : ℝ) * #σ ^ 2)⁻¹)
      (by positivity)
  obtain ⟨N, hN⟩ := exists_nat_gt δ⁻¹
  filter_upwards [eventually_ge_atTop N] with k hk ρ hρ p hp m
  -- The mesh `1 / k` of the subdivision is below `δ`.
  have hkδ : δ⁻¹ < k := hN.trans_le (Nat.cast_le.mpr hk)
  have hk0 : (0 : ℝ) < k := (inv_pos.mpr hδ).trans hkδ
  -- The vertices of `ρ` have their entries in `σ`, since their points lie in the simplex on `σ`.
  have hρσ : ∀ u ∈ ρ, ∀ l, u.1 l ∈ σ := fun u hu l => by
    have hsupp := StandardSimplex.support_subset (p ⟨u, hu⟩)
    rw [hp, support_edgewisePoint] at hsupp
    exact hsupp (mem_image_of_mem _ (mem_univ l))
  refine hsecant p k⁻¹ (inv_pos.mpr hk0) (inv_lt_of_inv_lt₀ hδ hkδ) (fun a b => ?_)
    (fun v hv => ?_) m
  · simpa only [hp] using norm_edgewisePoint_sub_edgewisePoint_le hρ a.2 b.2 σ
  · simpa only [hp] using mul_sum_abs_le_norm_sum_smul_edgewisePoint hρ hρσ v hv

end TauCeti.IsSimplexImmersion
