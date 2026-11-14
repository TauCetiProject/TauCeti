/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Convex.StdSimplex
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Basic
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Data.Fintype.Order
import TauCeti.Analysis.Convex.StdSimplex
import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Coordinates
import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Finite
import TauCeti.AlgebraicTopology.SimplicialComplex.Simplex.Realization

/-!
# Lipschitz bounds for simplexwise `C¹` maps on finite polyhedra

A map of the realization of a complex on a finite vertex type which is `C¹` on every closed
simplex is Lipschitz in barycentric coordinates, also between points of different simplices.
On each closed simplex this is Mathlib's `ContDiffOn.exists_lipschitzOnWith`. Two nearby points
of different closed simplices pass through a common point given by
`AbstractSimplicialComplex.exists_mem_inter_range_standardSimplex_coe`, and distant pairs are
handled by boundedness on the compact realization.

## Main results

* `TauCeti.exists_norm_sub_le_mul_norm_sub_of_contDiffOn`: a map of a complex on a finite vertex
  type which is `C¹` on every closed simplex is Lipschitz in barycentric coordinates.

## References

* J. Munkres, *Elementary Differential Topology*, Chapter II, Section 9.
-/

public section

open Set AbstractSimplicialComplex TauCeti.SetLike

namespace TauCeti

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K : AbstractSimplicialComplex ι} {f : Realization K → E}

/-- A map of the realization of a complex on a finite vertex type which is `C¹` on every closed
simplex is Lipschitz in barycentric coordinates, also between points of different simplices.
Being `C¹` on a closed simplex means being, in barycentric coordinates, the restriction of a map
which is `C¹` within the standard simplex. -/
theorem exists_norm_sub_le_mul_norm_sub_of_contDiffOn
    (hf : ∀ σ : Face K, ∃ F : (σ.1 → ℝ) → E,
      (∀ x : StandardSimplex σ.1, F (fun a => x.1 a) = f (faceInclusion K σ x)) ∧
        ContDiffOn ℝ 1 F (range fun t : Convexity.StdSimplex ℝ σ.1 => ⇑t.weights)) :
    ∃ C, ∀ x y : Realization K, ‖f x - f y‖ ≤ C * ‖(x.1 : ι → ℝ) - y.1‖ := by
  have : Finite (Face K) := (Set.toFinite K.faces).to_subtype
  -- On each closed simplex, `f` is Lipschitz, since it is `C¹` on a compact convex set.
  have hface (σ : Face K) : ∃ L : NNReal, ∀ x y : StandardSimplex σ.1,
      ‖f (faceInclusion K σ x) - f (faceInclusion K σ y)‖ ≤ L * ‖(x.1 : ι → ℝ) - y.1‖ := by
    obtain ⟨F, hFf, hF⟩ := hf σ
    obtain ⟨L, hL⟩ := hF.exists_lipschitzOnWith one_ne_zero
      (Convexity.StdSimplex.convex_range_toFun_comp_weights ℝ σ.1)
      (isCompact_range
        (Convexity.StdSimplex.isClosedEmbedding_toFun_comp_weights (R := ℝ) σ.1).continuous)
    refine ⟨L, fun x y => ?_⟩
    have hmem (z : StandardSimplex σ.1) :
        (fun a : σ.1 => z.1 a) ∈ range fun t : Convexity.StdSimplex ℝ σ.1 => ⇑t.weights := by
      rw [← Finset.range_standardSimplex_coordinates]
      exact mem_range_self z
    have hxy := hL.dist_le_mul _ (hmem x) _ (hmem y)
    rw [dist_eq_norm, dist_eq_norm, hFf, hFf] at hxy
    refine hxy.trans (mul_le_mul_of_nonneg_left ?_ L.2)
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
    exact norm_le_pi_norm ((x.1 : ι → ℝ) - (y.1 : ι → ℝ)) i.1
  choose L hL using hface
  obtain ⟨L₀, hL₀⟩ := Finite.exists_le L
  have hface₀ (σ : Face K) (x y : StandardSimplex σ.1) :
      ‖f (faceInclusion K σ x) - f (faceInclusion K σ y)‖ ≤ L₀ * ‖(x.1 : ι → ℝ) - y.1‖ :=
    (hL σ x y).trans (mul_le_mul_of_nonneg_right (NNReal.coe_le_coe.2 (hL₀ σ)) (norm_nonneg _))
  -- `f` is continuous on the compact space `|K|`, hence bounded.
  have hfc : Continuous f := continuous_iff_faceInclusion.2 fun σ => by
    obtain ⟨F, hFg, hF⟩ := hf σ
    exact Finset.continuous_of_continuousOn_coordinates hFg hF.continuousOn
  obtain ⟨B, hB⟩ := (isCompact_range hfc).isBounded.exists_norm_le
  set N : ℝ := (Fintype.card ι : ℝ)
  have hN : 0 ≤ N := Nat.cast_nonneg _
  refine ⟨(2 * N + 1) * L₀ + 2 * N * B, fun x y => ?_⟩
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB _ (mem_range_self x))
  -- Every point is the image of a point of the closed simplex spanned by its carrier.
  have hpt (x : Realization K) :
      faceInclusion K (carrier K x) ⟨x.1, mem_convexHull_carrier K x⟩ = x :=
    Subtype.ext (faceInclusion_val _ _ _)
  have hmem (x : Realization K) :
      (x.1 : ι → ℝ) ∈ range fun t : StandardSimplex (carrier K x).1 => (t.1 : ι → ℝ) :=
    ⟨⟨_, mem_convexHull_carrier K x⟩, rfl⟩
  have hd := norm_nonneg ((x.1 : ι → ℝ) - y.1)
  by_cases hnear : N * ‖(x.1 : ι → ℝ) - y.1‖ < 1
  · -- Nearby points: pass through a common point `z` of the two closed simplices.
    obtain ⟨z, ⟨⟨t, ht⟩, ⟨t', ht'⟩⟩, -, -, hyz, -⟩ :=
      exists_mem_inter_range_standardSimplex_coe (hmem x) (hmem y) hnear
    dsimp only at ht ht'
    have htt' : faceInclusion K (carrier K x) t = faceInclusion K (carrier K y) t' := by
      refine Subtype.ext ?_
      rw [faceInclusion_val, faceInclusion_val]
      exact DFunLike.coe_injective (ht.trans ht'.symm)
    have hx := hface₀ _ ⟨x.1, mem_convexHull_carrier K x⟩ t
    have hy := hface₀ _ t' ⟨y.1, mem_convexHull_carrier K y⟩
    rw [hpt, ht] at hx
    rw [hpt, ht', ← htt'] at hy
    dsimp only at hx hy
    have hxz : ‖(x.1 : ι → ℝ) - z‖ ≤ ‖(x.1 : ι → ℝ) - y.1‖ + ‖(y.1 : ι → ℝ) - z‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    have hzy : ‖z - (y.1 : ι → ℝ)‖ = ‖(y.1 : ι → ℝ) - z‖ := norm_sub_rev _ _
    have hL0 : (0 : ℝ) ≤ L₀ := L₀.2
    calc ‖f x - f y‖
        ≤ ‖f x - f (faceInclusion K (carrier K x) t)‖ +
          ‖f (faceInclusion K (carrier K x) t) - f y‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ L₀ * (‖(x.1 : ι → ℝ) - y.1‖ + 2 * ‖(y.1 : ι → ℝ) - z‖) := by nlinarith
      _ ≤ L₀ * ((2 * N + 1) * ‖(x.1 : ι → ℝ) - y.1‖) := by gcongr; nlinarith
      _ ≤ ((2 * N + 1) * L₀ + 2 * N * B) * ‖(x.1 : ι → ℝ) - y.1‖ := by
        nlinarith [mul_nonneg (mul_nonneg hN hB0) hd]
  · -- Distant points: both values are bounded by `B`.
    have : 1 ≤ N * ‖(x.1 : ι → ℝ) - y.1‖ := not_lt.mp hnear
    calc ‖f x - f y‖ ≤ ‖f x‖ + ‖f y‖ := norm_sub_le _ _
      _ ≤ 2 * B := by linarith [hB _ (mem_range_self x), hB _ (mem_range_self y)]
      _ ≤ ((2 * N + 1) * L₀ + 2 * N * B) * ‖(x.1 : ι → ℝ) - y.1‖ := by
        have hL0 : (0 : ℝ) ≤ L₀ := L₀.2
        nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * N + 1) hL0) hd]

end TauCeti
