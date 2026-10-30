/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Filter.AtTopBot.Basic
public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Edgewise.Homeomorph
public import TauCeti.Geometry.Manifold.SmoothTriangulation.Basic

import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Edgewise.Fatness
import TauCeti.Geometry.Manifold.SmoothTriangulation.Secant

/-!
# Smooth triangulations and secant maps on edgewise subdivisions

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

It also shows that a smooth triangulation `f : |K| ≃ₜ M` stays a smooth triangulation after
edgewise subdivision: composing `f` with the canonical homeomorphism from the realization of the
`k`-th edgewise subdivision onto `|K|` gives a smooth triangulation of `M` of the same class. On
a simplex of the subdivision that homeomorphism is linear in barycentric coordinates, and it is
injective on the directions of the simplex because the simplices of the subdivision are uniformly
fat.

## Main results

* `TauCeti.IsSimplexImmersion.eventually_isSimplexImmersion_edgewiseSubdivision`: the secant map
  of a `C¹` immersion of a simplex is an immersion on every face of all sufficiently fine edgewise
  subdivisions of that simplex.
* `TauCeti.IsSmoothTriangulation.edgewiseSubdivisionRealizationHomeomorph_trans`: the edgewise
  subdivisions of a smooth triangulation are smooth triangulations of the same class.

## References

* J. H. C. Whitehead, *On C¹-complexes*, Ann. of Math. 41 (1940), 809–824.
* J. Munkres, *Elementary Differential Topology*, Annals of Math. Studies 54 (1966), Chapter II,
  Section 9 (secant approximations) and Theorems 10.5–10.6.
* H. Freudenthal, *Simplizialzerlegungen von beschränkter Flachheit*, Ann. of Math. 43 (1942),
  580–582.
-/

public section

open Finset AbstractSimplicialComplex PreAbstractSimplicialComplex Filter TauCeti.SetLike
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

namespace TauCeti.IsSmoothTriangulation

variable {ι : Type*} [LinearOrder ι]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {n : WithTop ℕ∞} {k : ℕ}

/-- The `k`-th edgewise subdivision of a `Cⁿ` triangulation of `M` is a `Cⁿ` triangulation of
`M`, for `k ≠ 0`: composing it with the canonical homeomorphism from the realization of the
edgewise subdivision gives a smooth triangulation. -/
theorem edgewiseSubdivisionRealizationHomeomorph_trans {K : AbstractSimplicialComplex ι}
    {f : Realization K ≃ₜ M} (h : IsSmoothTriangulation I n f) (hk : k ≠ 0) :
    IsSmoothTriangulation I n ((edgewiseSubdivisionRealizationHomeomorph K hk).trans f) := by
  refine isSmoothTriangulation_iff.mpr fun ρ => ?_
  -- The canonical homeomorphism maps the simplex `ρ` into the face `σ` of `K` spanned by the
  -- entries of its vertices.
  let σ : Face K := ⟨_, biUnion_image_mem_of_mem_edgewiseSubdivision ρ.2⟩
  have hρσ : ∀ u ∈ ρ.1, ∀ l, u.1 l ∈ σ.1 := fun u hu l =>
    mem_biUnion.mpr ⟨u, hu, mem_image_of_mem _ (mem_univ l)⟩
  have hfactor : (edgewiseSubdivisionRealizationHomeomorph K hk).trans f ∘ faceInclusion _ ρ =
      (f ∘ faceInclusion K σ) ∘ edgewiseSubdivisionFaceMap hρσ := by
    funext x
    simp only [Function.comp_apply, Homeomorph.trans_apply,
      edgewiseSubdivisionRealizationHomeomorph_apply]
    exact congrArg f
      (congrFun (edgewiseSubdivisionRealizationMap_comp_faceInclusion ρ σ hρσ) x)
  rw [hfactor]
  -- In barycentric coordinates, the face map is the linear map sending the vertex `u` of `ρ` to
  -- `edgewisePoint u`.
  refine (isSmoothTriangulation_iff.mp h σ).comp_linear (Fintype.linearCombination ℝ
    fun (a : ρ.1) (b : σ.1) => edgewisePoint a.1.1 b) (fun x => funext fun b => ?_)
    (fun v hv hv0 => ?_)
  · simp only [Fintype.linearCombination_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [edgewiseSubdivisionFaceMap_apply]
    exact (Finset.sum_coe_sort ρ.1 fun u => x.1 u * edgewisePoint u.1 b).symm
  · -- A linear relation among the vertices of `ρ` is trivial, by the uniform fatness of the
    -- edgewise subdivision.
    have hσ : 0 < #σ.1 := card_pos.mpr (by simpa using K.isRelLowerSet_faces.prop_of_mem σ.2)
    have hfat := mul_sum_abs_le_norm_sum_smul_edgewisePoint ρ.2 hρσ v hv
    rw [← Fintype.linearCombination_apply, hv0, norm_zero] at hfat
    have hsum : ∑ a, |v a| = 0 := le_antisymm
      (nonpos_of_mul_nonpos_right hfat (by positivity)) (sum_nonneg fun a _ => abs_nonneg _)
    funext a
    exact abs_eq_zero.mp ((sum_eq_zero_iff_of_nonneg fun a _ => abs_nonneg _).mp hsum a
      (mem_univ a))

end TauCeti.IsSmoothTriangulation
