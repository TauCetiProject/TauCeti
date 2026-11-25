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
import TauCeti.Analysis.Convex.StdSimplex.Faces
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
    (hf : ∀ σ : Face K, ∃ F : (σ.val → ℝ) → E,
      (∀ x : StandardSimplex σ.val, F (fun a => x.val a) = f (faceInclusion K σ x)) ∧
        ContDiffOn ℝ 1 F (range fun t : Convexity.StdSimplex ℝ σ.val => ⇑t.weights)) :
    ∃ C, ∀ x y : Realization K, ‖f x - f y‖ ≤ C * ‖(x.val : ι → ℝ) - y.val‖ := by
  have : Finite (Face K) := (Set.toFinite K.faces).to_subtype
  -- On each closed simplex, `f` is Lipschitz, since it is `C¹` on a compact convex set.
  have hface (σ : Face K) : ∃ L : NNReal, ∀ x y : StandardSimplex σ.val,
      ‖f (faceInclusion K σ x) - f (faceInclusion K σ y)‖ ≤ L * ‖(x.val : ι → ℝ) - y.val‖ := by
    obtain ⟨F, hFf, hF⟩ := hf σ
    obtain ⟨L, hL⟩ := hF.exists_lipschitzOnWith one_ne_zero
      (Convexity.StdSimplex.convex_range_toFun_comp_weights ℝ σ.val)
      (isCompact_range
        (Convexity.StdSimplex.isClosedEmbedding_toFun_comp_weights (R := ℝ) σ.val).continuous)
    refine ⟨L, fun x y => ?_⟩
    have hmem (z : StandardSimplex σ.val) :
        (fun a : σ.val => z.val a) ∈ range fun t : Convexity.StdSimplex ℝ σ.val => ⇑t.weights := by
      rw [← Finset.range_standardSimplex_coordinates]
      exact mem_range_self z
    have hxy := hL.dist_le_mul _ (hmem x) _ (hmem y)
    rw [dist_eq_norm, dist_eq_norm, hFf, hFf] at hxy
    refine hxy.trans (mul_le_mul_of_nonneg_left ?_ L.property)
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
    exact norm_le_pi_norm ((x.val : ι → ℝ) - (y.val : ι → ℝ)) i.val
  choose L hL using hface
  obtain ⟨L₀, hL₀⟩ := Finite.exists_le L
  have hface₀ (σ : Face K) (x y : StandardSimplex σ.val) :
      ‖f (faceInclusion K σ x) - f (faceInclusion K σ y)‖ ≤ L₀ * ‖(x.val : ι → ℝ) - y.val‖ :=
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
      faceInclusion K (carrier K x) ⟨x.val, mem_convexHull_carrier K x⟩ = x :=
    faceInclusion_mk_val K (carrier K x) x (mem_convexHull_carrier K x)
  have hmem (x : Realization K) :
      (x.val : ι → ℝ) ∈ range fun t : StandardSimplex (carrier K x).val => (t.val : ι → ℝ) :=
    ⟨⟨_, mem_convexHull_carrier K x⟩, rfl⟩
  have hd := norm_nonneg ((x.val : ι → ℝ) - y.val)
  by_cases hnear : N * ‖(x.val : ι → ℝ) - y.val‖ < 1
  · -- Nearby points: pass through a common point `z` of the two closed simplices.
    obtain ⟨z, ⟨⟨t, ht⟩, ⟨t', ht'⟩⟩, -, -, hyz, -⟩ :=
      exists_mem_inter_range_standardSimplex_coe (hmem x) (hmem y) hnear
    dsimp only at ht ht'
    have htt' : faceInclusion K (carrier K x) t = faceInclusion K (carrier K y) t' := by
      refine Subtype.ext ?_
      rw [faceInclusion_val, faceInclusion_val]
      exact DFunLike.coe_injective (ht.trans ht'.symm)
    have hx := hface₀ _ ⟨x.val, mem_convexHull_carrier K x⟩ t
    have hy := hface₀ _ t' ⟨y.val, mem_convexHull_carrier K y⟩
    rw [hpt, ht] at hx
    rw [hpt, ht', ← htt'] at hy
    dsimp only at hx hy
    have hxz : ‖(x.val : ι → ℝ) - z‖ ≤ ‖(x.val : ι → ℝ) - y.val‖ + ‖(y.val : ι → ℝ) - z‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    have hzy : ‖z - (y.val : ι → ℝ)‖ = ‖(y.val : ι → ℝ) - z‖ := norm_sub_rev _ _
    have hL0 : (0 : ℝ) ≤ L₀ := L₀.property
    calc ‖f x - f y‖
        ≤ ‖f x - f (faceInclusion K (carrier K x) t)‖ +
          ‖f (faceInclusion K (carrier K x) t) - f y‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ L₀ * (‖(x.val : ι → ℝ) - y.val‖ + 2 * ‖(y.val : ι → ℝ) - z‖) := by nlinarith
      _ ≤ L₀ * ((2 * N + 1) * ‖(x.val : ι → ℝ) - y.val‖) := by gcongr; nlinarith
      _ ≤ ((2 * N + 1) * L₀ + 2 * N * B) * ‖(x.val : ι → ℝ) - y.val‖ := by
        nlinarith [mul_nonneg (mul_nonneg hN hB0) hd]
  · -- Distant points: both values are bounded by `B`.
    have : 1 ≤ N * ‖(x.val : ι → ℝ) - y.val‖ := not_lt.mp hnear
    calc ‖f x - f y‖ ≤ ‖f x‖ + ‖f y‖ := norm_sub_le _ _
      _ ≤ 2 * B := by linarith [hB _ (mem_range_self x), hB _ (mem_range_self y)]
      _ ≤ ((2 * N + 1) * L₀ + 2 * N * B) * ‖(x.val : ι → ℝ) - y.val‖ := by
        have hL0 : (0 : ℝ) ≤ L₀ := L₀.property
        nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * N + 1) hL0) hd]

end TauCeti
