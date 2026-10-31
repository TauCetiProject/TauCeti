/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import TauCeti.Analysis.Normed.Module.CoveringNumber

/-!
# Operator norms and sphere nets

Finite nets on the unit spheres of real inner product spaces reduce an operator norm to finitely
many bilinear evaluations. For two nets of radius `η < 1 / 2`, the loss is the factor
`(1 - 2η)⁻¹`, which is `2` when `η = 1 / 4`.
-/

public section

open Metric

namespace ContinuousLinearMap

/-- A bilinear `η`-net bound for the operator norm. If `Nₙ` and `Nₚ` cover the unit spheres in
the domain and codomain with radius `η < 1 / 2`, then the operator norm is at most
`(1 - 2η)⁻¹` times the largest absolute bilinear evaluation on the two nets. In particular,
`η = 1 / 4` gives the factor `2`. -/
theorem opNorm_le_of_isCover_sphere {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [Nontrivial E] [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [Nontrivial F] (T : E →L[ℝ] F) {η : NNReal}
    (hη : η < (1 / 2 : NNReal)) (Nₙ : Finset E) (Nₚ : Finset F)
    (hNₙ : (Nₙ : Set E) ⊆ sphere (0 : E) 1) (hNₚ : (Nₚ : Set F) ⊆ sphere (0 : F) 1)
    (hcoverₙ : IsCover η (sphere (0 : E) 1) (Nₙ : Set E))
    (hcoverₚ : IsCover η (sphere (0 : F) 1) (Nₚ : Set F)) :
    ‖T‖ ≤ (1 - 2 * (η : ℝ))⁻¹ *
      Nₙ.sup' (hcoverₙ.nonempty (NormedSpace.sphere_nonempty.mpr (by norm_num)))
        (fun u => Nₚ.sup' (hcoverₚ.nonempty (NormedSpace.sphere_nonempty.mpr (by norm_num)))
          (fun v => abs (Inner.inner ℝ v (T u)))) := by
  have hη0 : 0 ≤ (η : ℝ) := η.coe_nonneg
  have hηreal : (η : ℝ) < 1 / 2 := by exact_mod_cast hη
  have hden : 0 < 1 - 2 * (η : ℝ) := by nlinarith
  have hNₙ_nonempty : Nₙ.Nonempty := by
    exact hcoverₙ.nonempty (NormedSpace.sphere_nonempty.mpr (by norm_num))
  have hNₚ_nonempty : Nₚ.Nonempty := by
    exact hcoverₚ.nonempty (NormedSpace.sphere_nonempty.mpr (by norm_num))
  let M := Nₙ.sup' hNₙ_nonempty
    (fun u => Nₚ.sup' hNₚ_nonempty (fun v => abs (Inner.inner ℝ v (T u))))
  have hM_nonneg : 0 ≤ M := by
    rcases hNₙ_nonempty with ⟨u, hu⟩
    have hinner_nonneg :
        0 ≤ Nₚ.sup' hNₚ_nonempty (fun v => abs (Inner.inner ℝ v (T u))) := by
      rcases hNₚ_nonempty with ⟨v, hv⟩
      exact (abs_nonneg _).trans
        (Finset.le_sup' (f := fun v => abs (Inner.inner ℝ v (T u))) hv)
    dsimp [M]
    exact hinner_nonneg.trans
      (Finset.le_sup' (f := fun u => Nₚ.sup' hNₚ_nonempty
        (fun v => abs (Inner.inner ℝ v (T u)))) hu)
  have hunit : ∀ x : E, ‖x‖ = 1 → ‖T x‖ ≤ M + 2 * (η : ℝ) * ‖T‖ := by
    intro x hx
    have hxSphere : x ∈ sphere (0 : E) 1 := by
      rwa [mem_sphere_zero_iff_norm]
    have hcoverUnion : sphere (0 : E) 1 ⊆
        ⋃ u ∈ (Nₙ : Set E), closedBall u η :=
      hcoverₙ.subset_iUnion_closedBall
    have hxCover : ∃ u : E, u ∈ (Nₙ : Set E) ∧ x ∈ closedBall u η := by
      simpa only [Set.mem_iUnion, exists_prop] using hcoverUnion hxSphere
    rcases hxCover with ⟨u, hu, hxu⟩
    have hxu' : ‖x - u‖ ≤ (η : ℝ) := by
      simpa only [Metric.mem_closedBall, dist_eq_norm] using hxu
    have hunorm : ‖u‖ = 1 := mem_sphere_zero_iff_norm.mp (hNₙ hu)
    by_cases hTx : T x = 0
    · rw [hTx]
      have : 0 ≤ M + 2 * (η : ℝ) * ‖T‖ := by positivity
      simpa using this
    · let y : F := ‖T x‖⁻¹ • T x
      have hynorm : ‖y‖ = 1 := by
        have hnormpos : 0 < ‖T x‖ := norm_pos_iff.mpr hTx
        calc
          ‖y‖ = ‖‖T x‖⁻¹ • T x‖ := by rfl
          _ = ‖‖T x‖⁻¹‖ * ‖T x‖ := norm_smul _ _
          _ = ‖T x‖⁻¹ * ‖T x‖ := by
            rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
          _ = 1 := inv_mul_cancel₀ (ne_of_gt hnormpos)
      have hinner : Inner.inner ℝ y (T x) = ‖T x‖ := by
        rw [show y = ‖T x‖⁻¹ • T x by rfl, real_inner_smul_self_left]
        have hnormpos : 0 < ‖T x‖ := norm_pos_iff.mpr hTx
        field_simp
      have hySphere : y ∈ sphere (0 : F) 1 := by rwa [mem_sphere_zero_iff_norm]
      have hcoverUnionₚ : sphere (0 : F) 1 ⊆
          ⋃ v ∈ (Nₚ : Set F), closedBall v η :=
        hcoverₚ.subset_iUnion_closedBall
      have hyCover : ∃ v : F, v ∈ (Nₚ : Set F) ∧ y ∈ closedBall v η := by
        simpa only [Set.mem_iUnion, exists_prop] using hcoverUnionₚ hySphere
      rcases hyCover with ⟨v, hv, hyv⟩
      have hyv' : ‖y - v‖ ≤ (η : ℝ) := by
        simpa only [Metric.mem_closedBall, dist_eq_norm] using hyv
      have hvnorm : ‖v‖ = 1 := mem_sphere_zero_iff_norm.mp (hNₚ hv)
      have hsample : abs (Inner.inner ℝ v (T u)) ≤ M := by
        dsimp [M]
        exact (Finset.le_sup' (f := fun v => abs (Inner.inner ℝ v (T u))) hv).trans
          (Finset.le_sup' (f := fun u => Nₚ.sup' hNₚ_nonempty
            (fun v => abs (Inner.inner ℝ v (T u)))) hu)
      have hdecomp :
          Inner.inner ℝ y (T x) - Inner.inner ℝ v (T u) =
            Inner.inner ℝ (y - v) (T x) + Inner.inner ℝ v (T (x - u)) := by
        simp only [inner_sub_left, inner_sub_right, map_sub]
        ring
      have herror :
          abs (Inner.inner ℝ y (T x) - Inner.inner ℝ v (T u)) ≤ 2 * (η : ℝ) * ‖T‖ := by
        rw [hdecomp]
        calc
          abs (Inner.inner ℝ (y - v) (T x) + Inner.inner ℝ v (T (x - u)))
              ≤ abs (Inner.inner ℝ (y - v) (T x)) + abs (Inner.inner ℝ v (T (x - u))) :=
                abs_add_le _ _
          _ ≤ ‖y - v‖ * ‖T x‖ + ‖v‖ * ‖T (x - u)‖ :=
            add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)
          _ ≤ (η : ℝ) * ‖T‖ + 1 * (‖T‖ * (η : ℝ)) := by
            have hTxle : ‖T x‖ ≤ ‖T‖ := by simpa [hx] using T.le_opNorm x
            have hTdiff : ‖T (x - u)‖ ≤ ‖T‖ * (η : ℝ) := by
              exact (T.le_opNorm (x - u)).trans
                (mul_le_mul_of_nonneg_left hxu' T.opNorm_nonneg)
            rw [hvnorm]
            exact add_le_add
              (mul_le_mul_of_nonneg hyv' hTxle (norm_nonneg _) (norm_nonneg _))
              (mul_le_mul_of_nonneg_left hTdiff (by norm_num))
          _ = 2 * (η : ℝ) * ‖T‖ := by ring
      calc
        ‖T x‖ = abs (Inner.inner ℝ y (T x)) := by rw [hinner, abs_of_nonneg (norm_nonneg _)]
        _ ≤ abs (Inner.inner ℝ v (T u)) +
          abs (Inner.inner ℝ y (T x) - Inner.inner ℝ v (T u)) := by
          calc
            abs (Inner.inner ℝ y (T x)) =
                abs ((Inner.inner ℝ y (T x) - Inner.inner ℝ v (T u)) +
                  Inner.inner ℝ v (T u)) := by ring_nf
            _ ≤ _ := by
              simpa [add_comm] using
                (abs_add_le (Inner.inner ℝ y (T x) - Inner.inner ℝ v (T u))
                  (Inner.inner ℝ v (T u)))
        _ ≤ M + 2 * (η : ℝ) * ‖T‖ := add_le_add hsample herror
  have hnorm : ‖T‖ ≤ M + 2 * (η : ℝ) * ‖T‖ :=
    ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity) hunit
  have hsolve : (1 - 2 * (η : ℝ)) * ‖T‖ ≤ M := by
    nlinarith [hnorm]
  calc
    ‖T‖ = (1 - 2 * (η : ℝ))⁻¹ * ((1 - 2 * (η : ℝ)) * ‖T‖) := by
      field_simp
    _ ≤ (1 - 2 * (η : ℝ))⁻¹ * M :=
      mul_le_mul_of_nonneg_left hsolve (inv_nonneg.mpr hden.le)

end ContinuousLinearMap
