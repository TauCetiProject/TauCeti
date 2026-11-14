/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Schoenflies.Disc
public import TauCeti.Analysis.InnerProductSpace.Hemisphere
import TauCeti.Analysis.Normed.Module.Ball.Radial.Extension

/-!
# Simultaneous Schoenflies straightening

For `m ≥ 2`, a bicollared `Sᵐ⁻¹` in `Sᵐ` can be carried to the equator by one ambient
homeomorphism (`TauCeti.IsBicollar.exists_homeomorph_eq_equatorInclusion`). The source is the
unit sphere of a real normed space `E`, and the ambient sphere is that of a real inner product
space `F` with `dim F = dim E + 1`. The boundary identification with the equator is prescribed
by a homeomorphism from the source sphere to the unit sphere of the orthogonal complement of
a pole, followed by `TauCeti.equatorInclusion`.

The same ambient homeomorphism carries the closures of both complementary domains to the
standard closed hemispheres. This simultaneous conclusion identifies the embedded sphere
and its two sides as one standard pair, rather than identifying each complementary closure
with a ball separately as in
`TauCeti.IsBicollar.exists_homeomorph_closure_connectedComponentIn_compl_range`.
For abstract pairs of discs, see
`TauCeti.exists_homeomorph_sphere_of_union_closedBall_orthogonal`.

## References

* M. Brown, *A proof of the generalized Schoenflies theorem*, Bull. Amer. Math. Soc. 66
  (1960), 74–76, Theorem 5.
-/

public section

open Function Metric Module Set
open scoped RealInnerProductSpace

namespace TauCeti.IsBicollar

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {σ : sphere (0 : E) 1 → sphere (0 : F) 1}
  {b : sphere (0 : E) 1 × ℝ → sphere (0 : F) 1}

/-- **Simultaneous Schoenflies theorem.** A bicollared `Sᵐ⁻¹` in `Sᵐ`, for `m ≥ 2`, admits
an ambient homeomorphism carrying the closures of the complementary domains containing the
positive and negative sides of the bicollar onto the closed hemispheres around `p` and `-p`.
Its boundary values satisfy `h (σ x) = equatorInclusion (p : F) (e x)` for the prescribed
homeomorphism `e` of unit spheres. The same hemisphere characterizations hold at every point
of each side of the bicollar. -/
theorem exists_homeomorph_eq_equatorInclusion
    (hb : IsBicollar σ b) (hEF : finrank ℝ F = finrank ℝ E + 1)
    (hE : 1 < finrank ℝ E) (p : sphere (0 : F) 1)
    (e : sphere (0 : E) 1 ≃ₜ sphere (0 : (ℝ ∙ (p : F))ᗮ) 1) :
    ∃ h : sphere (0 : F) 1 ≃ₜ sphere (0 : F) 1,
      (∀ x, h (σ x) = equatorInclusion (p : F) (e x)) ∧
      (∀ (x : sphere (0 : E) 1) {t : ℝ}, 0 < t → ∀ y, 0 ≤ ⟪(h y : F), (p : F)⟫ ↔
        y ∈ closure (connectedComponentIn (range σ)ᶜ (b (x, t)))) ∧
      (∀ (x : sphere (0 : E) 1) {t : ℝ}, t < 0 → ∀ y, ⟪(h y : F), (p : F)⟫ ≤ 0 ↔
        y ∈ closure (connectedComponentIn (range σ)ᶜ (b (x, t)))) := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  obtain ⟨x₀⟩ : Nonempty (sphere (0 : E) 1) :=
    (NormedSpace.sphere_nonempty.2 zero_le_one).to_subtype
  let B : closedBall (0 : E) 1 ≃ₜ closedBall (0 : (ℝ ∙ (p : F))ᗮ) 1 :=
    e.radialExtension.subtype fun z ↦ by simp
  -- The complementary domains are the two sides of the bicollar.
  obtain ⟨U, V, -, -, hUV, hcompl, -, -, hpos, hneg, hUc, hVc⟩ :=
    hb.exists_connectedComponentIn_eq hEF hE
  have hu : b (x₀, 1) ∈ U := hpos ⟨mem_univ _, by norm_num⟩
  have hv : b (x₀, -1) ∈ V := hneg ⟨mem_univ _, by norm_num⟩
  have huσ : b (x₀, 1) ∉ range σ := hcompl.ge (Or.inl hu)
  have hvσ : b (x₀, -1) ∉ range σ := hcompl.ge (Or.inr hv)
  let A := closure (connectedComponentIn (range σ)ᶜ (b (x₀, 1)))
  let C := closure (connectedComponentIn (range σ)ᶜ (b (x₀, -1)))
  have hA : A = U ∪ range σ := by
    dsimp only [A]
    rw [hb.closure_connectedComponentIn_compl_range hEF hE huσ, hUc _ hu]
  have hC : C = V ∪ range σ := by
    dsimp only [C]
    rw [hb.closure_connectedComponentIn_compl_range hEF hE hvσ, hVc _ hv]
  have hAC : A ∪ C = univ := by
    rw [hA, hC, ← union_union_distrib_right, ← hcompl, compl_union_self]
  have hinter : A ∩ C = range σ := by
    rw [hA, hC, ← inter_union_distrib_right, hUV.inter_eq, empty_union]
  -- Brown supplies discs with the same parametrization on their common boundary.
  obtain ⟨eA, heA, hnA⟩ := hb.exists_homeomorph_closure_connectedComponentIn_compl_range
    hEF hE huσ
  obtain ⟨eC, -, hnC⟩ := hb.exists_homeomorph_closure_connectedComponentIn_compl_range
    hEF hE hvσ
  have hB (z : closedBall (0 : E) 1) : ‖(B z : (ℝ ∙ (p : F))ᗮ)‖ = 1 ↔ ‖(z : E)‖ = 1 := by
    simp [B]
  -- Glue both discs at once, retaining the coordinates of the positive disc.
  obtain ⟨h, hhA, hhpos, hhneg⟩ := exists_homeomorph_sphere_of_union_closedBall_orthogonal p
    isClosed_closure isClosed_closure hAC (eA.trans B) (eC.trans B)
    (fun z ↦ by
      rw [Homeomorph.trans_apply, hB, ← mem_sphere_zero_iff_norm, hnA]
      simpa only [mem_inter_iff, A, C, z.2, true_and] using Set.ext_iff.1 hinter z)
    (fun z ↦ by
      rw [Homeomorph.trans_apply, hB, ← mem_sphere_zero_iff_norm, hnC]
      simpa only [mem_inter_iff, A, C, z.2, and_true] using Set.ext_iff.1 hinter z)
  refine ⟨h, ?_, ?_, ?_⟩
  · intro x
    have hxA : σ x ∈ A := (hA ▸ Or.inr (mem_range_self x))
    rw [hhA ⟨σ x, hxA⟩]
    have he : (B (eA ⟨σ x, hxA⟩) : (ℝ ∙ (p : F))ᗮ) = e x := by
      simpa only [B, Homeomorph.subtype_apply_coe, heA ⟨σ x, hxA⟩ x rfl] using
        e.radialExtension_coe_sphere x
    apply Subtype.ext
    simp [Homeomorph.trans_apply, coe_hemisphereHomeomorph_symm_apply,
      coe_equatorInclusion_apply, he, norm_eq_of_mem_sphere]
  · intro x t ht y
    rw [hhpos, hUc _ hu, hUc _ (hpos (x := (x, t)) ⟨mem_univ x, mem_Ioi.2 ht⟩)]
  · intro x t ht y
    rw [hhneg, hVc _ hv, hVc _ (hneg (x := (x, t)) ⟨mem_univ x, mem_Iio.2 ht⟩)]

end TauCeti.IsBicollar
