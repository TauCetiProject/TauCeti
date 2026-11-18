/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giada Franz, The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Ellipticity.Basic

/-!
# Uniform ellipticity on compact sets

A coefficient field `a : X → Matrix n n ℝ` that is continuous on a compact set `K` and positive
definite at every point of `K` is uniformly elliptic on `K`
(`TauCeti.PDE.exists_uniformlyEllipticOn_of_isCompact`). The lower constant is a positive uniform
lower bound for the continuous function `(x, ξ) ↦ ξ ⬝ a(x) ξ` on the compact set `K × S`, with `S`
the unit sphere. The upper constant bounds the operator norms of the bilinear forms of `a(x)`,
which vary continuously on `K`. No nonemptiness assumption on `K × S` is needed.

This is how a smooth coefficient field, such as a Riemannian metric read in a chart, gives a
uniformly elliptic operator on every open set with compact closure in its domain.

Adapted from Giada Franz's formalization in
[`ColdingMinicozziTheory`](https://github.com/riccardobrasca/ColdingMinicozziTheory), module
`ForTauCeti/Analysis/PDE/Ellipticity/Compact.lean`, revision
`6b89bc4abbf989319947d24d776114611027f224`.
-/

public section

open Matrix Metric Set

namespace TauCeti

namespace PDE

variable {X : Type*} [TopologicalSpace X] {n : Type*} [Fintype n] [DecidableEq n]

/-- **Pointwise positivity on a compact set is uniform ellipticity.** A coefficient field that is
continuous on a compact set `K`, and positive definite at every point of `K`, is uniformly
elliptic on `K`. -/
theorem exists_uniformlyEllipticOn_of_isCompact {K : Set X} (hK : IsCompact K)
    {a : X → Matrix n n ℝ} (ha : ContinuousOn a K)
    (hpos : ∀ x ∈ K, ∀ ξ : EuclideanSpace ℝ n, ξ ≠ 0 → 0 < ξ ⬝ᵥ (a x *ᵥ ξ)) :
    ∃ lam Lam, UniformlyEllipticOn K a lam Lam := by
  have hB : ContinuousOn (fun x ↦ matrixBilinearForm (a x)) K :=
    continuous_matrixBilinearForm.comp_continuousOn ha
  set S := K ×ˢ sphere (0 : EuclideanSpace ℝ n) 1
  have hq : ContinuousOn (fun y : X × EuclideanSpace ℝ n ↦ matrixBilinearForm (a y.1) y.2 y.2)
      S :=
    ((hB.comp continuousOn_fst fun _ hy ↦ (mem_prod.1 hy).1).clm_apply
      continuousOn_snd).clm_apply continuousOn_snd
  obtain ⟨lam, hlam, hlamq⟩ := (hK.prod (isCompact_sphere 0 1)).exists_forall_le' hq
    (a := 0) fun y hy ↦ by
      rw [matrixBilinearForm_apply]
      refine hpos y.1 hy.1 y.2 fun h ↦ ?_
      have h1 := hy.2
      rw [h, mem_sphere_zero_iff_norm, norm_zero] at h1
      exact zero_ne_one h1
  have hlower (x : X) (hx : x ∈ K) (ξ : EuclideanSpace ℝ n) :
      lam * ‖ξ‖ ^ 2 ≤ (a x).toQuadraticForm' ξ := by
    rw [← matrixBilinearForm_self]
    rcases eq_or_ne ξ 0 with rfl | hξ
    · simp
    have hξ' : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
    have h := hlamq (x, ‖ξ‖⁻¹ • ξ) ⟨hx, by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hξ'.ne']⟩
    simp only [map_smul, smul_apply, smul_eq_mul] at h
    have hsq : ‖ξ‖ ^ 2 * (‖ξ‖⁻¹ * (‖ξ‖⁻¹ * matrixBilinearForm (a x) ξ ξ)) =
        matrixBilinearForm (a x) ξ ξ := by
      field_simp
    rw [← hsq]
    nlinarith [sq_nonneg ‖ξ‖]
  have hsum : ContinuousOn (fun x ↦ ∑ i, ∑ j, |a x i j|) K :=
    continuousOn_finsetSum _ fun i _ ↦ continuousOn_finsetSum _ fun j _ ↦
      ((continuous_id.matrix_elem i j).comp_continuousOn ha).abs
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hsum
  refine ⟨lam, max lam C, UniformlyEllipticOn.of_bounds hlam (le_max_left _ _)
    (fun x hx ξ ↦ hlower x hx ξ) fun x hx η ξ ↦ ?_⟩
  rw [← matrixBilinearForm_apply, ← Real.norm_eq_abs]
  exact (matrixBilinearForm (a x)).le_of_opNorm₂_le_of_le
    (((norm_matrixBilinearForm_le_sum_abs _).trans ((le_abs_self _).trans (hC x hx))).trans
      (le_max_right _ _)) le_rfl le_rfl

end PDE

end TauCeti
