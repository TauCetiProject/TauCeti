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
`exists_pos_forall_injective_of_norm_sub_sub_le` supplies the resulting injectivity
stability: any perturbation with sufficiently small Lipschitz error in these coordinates
remains injective. No differentiability of the perturbation is required.

## References

* J. Munkres, *Elementary Differential Topology*, Chapter II, §9 (secant approximations)
  and Theorems 10.5–10.6 (smooth triangulations).
* J. H. C. Whitehead, *On C¹-complexes*, Ann. of Math. 41 (1940), 809–824.
-/

public section

open Set AbstractSimplicialComplex
open scoped Manifold ContDiff

namespace TauCeti.IsSimplexImmersion

/-- An injective immersion of a closed simplex of class at least `C¹` is bounded below on all
chords in barycentric coordinates, including pairs on the boundary. -/
theorem exists_pos_mul_norm_sub_le
    {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {σ : Finset ι}
    {n : WithTop ℕ∞} {g : StandardSimplex σ → E}
    (h : IsSimplexImmersion 𝓘(ℝ, E) n g) (hn : 1 ≤ n) (hg : Function.Injective g) :
    ∃ b > 0, ∀ x y : StandardSimplex σ,
      b * ‖(fun a : σ => x.1 a) - fun a : σ => y.1 a‖ ≤ ‖g x - g y‖ := by
  classical
  obtain ⟨F, F', hFg, hFd, hFc, hinj⟩ := h.exists_continuousOn_hasFDerivWithinAt hn
  let S := range fun t : Convexity.StdSimplex ℝ σ => ⇑t.weights
  have hS : IsCompact S := isCompact_range
    (Convexity.StdSimplex.isClosedEmbedding_toFun_comp_weights (R := ℝ) σ).continuous
  have hcoords (x : StandardSimplex σ) : (fun a : σ => x.1 a) ∈ S :=
    ⟨Finset.standardSimplexHomeomorph σ x,
      funext fun a => Finset.standardSimplexHomeomorph_weights σ x a⟩
  have hpoint : ∀ y ∈ S, ∃ x : StandardSimplex σ, (fun a : σ => x.1 a) = y := by
    rintro _ ⟨t, rfl⟩
    refine ⟨(Finset.standardSimplexHomeomorph σ).symm t, ?_⟩
    funext a
    simpa only [Homeomorph.apply_symm_apply] using
      (Finset.standardSimplexHomeomorph_weights σ
        ((Finset.standardSimplexHomeomorph σ).symm t) a).symm
  have hFinj : InjOn F S := by
    intro u hu v hv huv
    obtain ⟨x, rfl⟩ := hpoint u hu
    obtain ⟨y, rfl⟩ := hpoint v hv
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
  obtain ⟨b, hb, hchord⟩ := hS.exists_pos_mul_norm_sub_le_of_hasFDerivWithinAt
    (Convexity.StdSimplex.convex_range_toFun_comp_weights ℝ σ) hFd hFc hFinj hc hbound'
  exact ⟨b, hb, fun x y => by simpa only [hFg] using hchord _ (hcoords x) _ (hcoords y)⟩

/-- An embedded `C¹` simplex stays injective under every perturbation with sufficiently small
Lipschitz error in barycentric coordinates. In particular, the bound controls collisions between
different subdivided faces, not just injectivity on each face separately. -/
theorem exists_pos_forall_injective_of_norm_sub_sub_le
    {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {σ : Finset ι}
    {n : WithTop ℕ∞} {g : StandardSimplex σ → E}
    (h : IsSimplexImmersion 𝓘(ℝ, E) n g) (hn : 1 ≤ n) (hg : Function.Injective g) :
    ∃ ε > 0, ∀ f : StandardSimplex σ → E,
      (∀ x y, ‖(f x - g x) - (f y - g y)‖ ≤
        ε * ‖(fun a : σ => x.1 a) - fun a : σ => y.1 a‖) → Function.Injective f := by
  obtain ⟨b, hb, hbound⟩ := h.exists_pos_mul_norm_sub_le hn hg
  refine ⟨b / 2, half_pos hb, fun f hf x y hxy => hg ?_⟩
  have hlower := hbound x y
  have herror := hf x y
  have heq : (f x - g x) - (f y - g y) = -(g x - g y) := by rw [hxy]; abel
  rw [heq, norm_neg] at herror
  have hzero : ‖(fun a : σ => x.1 a) - fun a : σ => y.1 a‖ = 0 := by
    nlinarith [norm_nonneg ((fun a : σ => x.1 a) - fun a : σ => y.1 a)]
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm (by simpa [hzero] using herror)
    (norm_nonneg _)))

end TauCeti.IsSimplexImmersion
