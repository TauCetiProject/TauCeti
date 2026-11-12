/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothTriangulation.Secant
public import TauCeti.Analysis.Calculus.FDeriv.Antilipschitz
import TauCeti.Analysis.Convex.SecantEstimate
import TauCeti.Analysis.Convex.StdSimplex

/-!
# Separation bounds for embedded smooth simplices

An injective `C¹` immersion of a closed simplex has a positive uniform lower bound on chords,
measured in its barycentric coordinates. This is stronger than the non-degeneracy of individual
secants: it controls pairs anywhere in the original simplex, including different subdivided
faces. Such a bound is the quantitative input for keeping secant perturbations injective.

The argument uses derivatives only on directions of coordinate sum zero. It does not require
an extension which is an immersion on the ambient barycentric-coordinate space.
`exists_antilipschitzWith` states the separation bound on the barycentric-coordinate image,
using `Finset.standardSimplexCoordinatesHomeomorph`. Mathlib's
`AntilipschitzWith.add_sub_lipschitzWith` then preserves a quantitative separation bound under
any Lipschitz error smaller than the inverse antilipschitz constant; its `.injective` consequence
rules out collisions. No differentiability of the perturbation is required.

## References

* J. Munkres, *Elementary Differential Topology*, Chapter II, §9 (secant approximations)
  and Theorems 10.5–10.6 (smooth triangulations).
* J. H. C. Whitehead, *On C¹-complexes*, Ann. of Math. 41 (1940), 809–824.
-/

public section

open Set AbstractSimplicialComplex
open scoped Manifold ContDiff

namespace TauCeti.IsSimplexImmersion

/-- An injective immersion of a closed simplex of class at least `C¹` is antilipschitz in
barycentric coordinates, including on the boundary. -/
theorem exists_antilipschitzWith
    {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {σ : Finset ι}
    {n : WithTop ℕ∞} {g : StandardSimplex σ → E}
    (h : IsSimplexImmersion 𝓘(ℝ, E) n g) (hn : 1 ≤ n) (hg : Function.Injective g) :
    ∃ K > 0, AntilipschitzWith K (g ∘ (Finset.standardSimplexCoordinatesHomeomorph σ).symm) := by
  classical
  obtain ⟨F, F', hFg, hFd, hFc, hinj⟩ := h.exists_continuousOn_hasFDerivWithinAt hn
  let S := range fun t : Convexity.StdSimplex ℝ σ => ⇑t.weights
  have hS : IsCompact S := isCompact_range
    (Convexity.StdSimplex.isClosedEmbedding_toFun_comp_weights (R := ℝ) σ).continuous
  have hFinj : InjOn F S := by
    intro u hu v hv huv
    have hScoords : S = range (fun x : StandardSimplex σ => fun a : σ => x.1 a) :=
      (Finset.range_standardSimplex_coordinates σ).symm
    rw [hScoords] at hu hv
    obtain ⟨x, rfl⟩ := hu
    obtain ⟨y, rfl⟩ := hv
    rw [hFg, hFg] at huv
    exact congrArg (fun x : StandardSimplex σ => fun a : σ => x.1 a) (hg huv)
  obtain ⟨c, hc, hbound⟩ := hS.exists_pos_mul_sum_abs_le_norm hFc hinj
  have hbound' : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, c * ‖y - z‖ ≤ ‖F' x (y - z)‖ := by
    intro x hx y hy z hz
    have hsum : ∑ a, (y - z) a = 0 := by
      obtain ⟨t, rfl⟩ := hy
      obtain ⟨u, rfl⟩ := hz
      simp only [Pi.sub_apply, Finset.sum_sub_distrib, Convexity.StdSimplex.total_of_fintype,
        sub_self]
    exact (mul_le_mul_of_nonneg_left
      ((pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun a _ => abs_nonneg ((y - z) a))).mpr
        fun a => Finset.single_le_sum (fun i _ => abs_nonneg ((y - z) i)) (Finset.mem_univ a))
      hc.le).trans (by
        simpa only [Real.norm_eq_abs] using hbound x hx (y - z) hsum)
  obtain ⟨K, hKpos, hK⟩ := hS.exists_antilipschitzWith_of_hasFDerivWithinAt
    (Convexity.StdSimplex.convex_range_toFun_comp_weights ℝ σ) hFd hFc hFinj hc hbound'
  refine ⟨K, hKpos, ?_⟩
  have hEq : S.domRestrict F = g ∘ (Finset.standardSimplexCoordinatesHomeomorph σ).symm := by
    funext u
    obtain ⟨x, rfl⟩ := (Finset.standardSimplexCoordinatesHomeomorph σ).surjective u
    simp only [Set.domRestrict_apply, Finset.standardSimplexCoordinatesHomeomorph_val,
      Function.comp_apply, Homeomorph.symm_apply_apply, hFg]
  rwa [hEq] at hK

end TauCeti.IsSimplexImmersion
