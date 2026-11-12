/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Schoenflies.Disc
public import TauCeti.Analysis.InnerProductSpace.Hemisphere
public import TauCeti.Analysis.Normed.Module.Ball.Homeomorph

/-!
# Simultaneous Schoenflies straightening

For `m ≥ 2`, a bicollared `Sᵐ⁻¹` in `Sᵐ` can be carried to the equator by one ambient
homeomorphism. The same homeomorphism carries the closures of its two complementary
domains to the two standard closed hemispheres. It respects the given parametrization
of the embedded sphere, after the radial identification of equal-dimensional unit spheres.

The individual parametrized discs are supplied by
`TauCeti.IsBicollar.exists_homeomorph_closure_connectedComponentIn_compl_range`.
The simultaneous identification uses the hemisphere gluing theorem
`TauCeti.exists_homeomorph_sphere_of_union_closedBall_orthogonal`, which preserves the
coordinates on the first disc. No compatibility of independently chosen disc interiors
is required: their common boundary parametrization fixes the seam.

## References

* M. Brown, *A proof of the generalized Schoenflies theorem*, Bull. Amer. Math. Soc. 66
  (1960), 74–76, Theorem 5.
-/

public section

open Function Metric Module Set
open scoped RealInnerProductSpace

namespace TauCeti.IsBicollar

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]
  {σ : sphere (0 : E) 1 → sphere (0 : F) 1}
  {b : sphere (0 : E) 1 × ℝ → sphere (0 : F) 1}

/-- **Simultaneous Schoenflies theorem.** A bicollared `Sᵐ⁻¹` in `Sᵐ`, for `m ≥ 2`, is the
equator of a standard hemisphere decomposition, by one ambient homeomorphism. The positive
and negative sides of the bicollar go to the corresponding hemispheres around any prescribed
pole `p`. On the embedded sphere this homeomorphism is the prescribed parametrization, read
through the radial identification with the unit sphere of the orthogonal complement of `p`.
The point `x₀` selects a point on each side, without imposing any further condition on it. -/
theorem exists_homeomorph_eq_equatorInclusion
    (hb : IsBicollar σ b) (hEF : finrank ℝ F = finrank ℝ E + 1)
    (hE : 1 < finrank ℝ E) (x₀ : sphere (0 : E) 1) (p : sphere (0 : F) 1) :
    let hdim : finrank ℝ E = finrank ℝ (ℝ ∙ (p : F))ᗮ := by
      have : Fact (finrank ℝ F = finrank ℝ E + 1) := ⟨hEF⟩
      exact (Submodule.finrank_orthogonal_span_singleton (ne_zero_of_mem_unit_sphere p)).symm
    ∃ h : sphere (0 : F) 1 ≃ₜ sphere (0 : F) 1,
      (∀ x, h (σ x) = equatorInclusion (p : F) (sphereHomeomorphOfFinrankEq hdim x)) ∧
      (∀ y, 0 ≤ ⟪(h y : F), (p : F)⟫ ↔
        y ∈ closure (connectedComponentIn (range σ)ᶜ (b (x₀, 1)))) ∧
      (∀ y, ⟪(h y : F), (p : F)⟫ ≤ 0 ↔
        y ∈ closure (connectedComponentIn (range σ)ᶜ (b (x₀, -1)))) := by
  have : Fact (finrank ℝ F = finrank ℝ E + 1) := ⟨hEF⟩
  have hdim : finrank ℝ E = finrank ℝ (ℝ ∙ (p : F))ᗮ :=
    (Submodule.finrank_orthogonal_span_singleton (ne_zero_of_mem_unit_sphere p)).symm
  let B := closedBallHomeomorphOfFinrankEq hdim
  -- The complementary domains are the two sides of the bicollar.
  obtain ⟨U, V, -, -, hUV, hcompl, hpos, hneg, hUc, hVc⟩ :=
    hb.exists_connectedComponentIn_eq hEF hE
  have hu : b (x₀, 1) ∈ U := hpos ⟨mem_univ _, by norm_num⟩
  have hv : b (x₀, -1) ∈ V := hneg ⟨mem_univ _, by norm_num⟩
  have huσ : b (x₀, 1) ∉ range σ := by
    intro h
    have hm : (x₀, (1 : ℝ)) ∈ b ⁻¹' range σ := h
    rw [hb.preimage_range] at hm
    norm_num at hm
  have hvσ : b (x₀, -1) ∉ range σ := by
    intro h
    have hm : (x₀, (-1 : ℝ)) ∈ b ⁻¹' range σ := h
    rw [hb.preimage_range] at hm
    norm_num at hm
  let A := closure (connectedComponentIn (range σ)ᶜ (b (x₀, 1)))
  let C := closure (connectedComponentIn (range σ)ᶜ (b (x₀, -1)))
  have hA : A = U ∪ range σ := by
    dsimp only [A]
    rw [hb.closure_connectedComponentIn_compl_range hEF hE huσ, hUc _ hu]
  have hC : C = V ∪ range σ := by
    dsimp only [C]
    rw [hb.closure_connectedComponentIn_compl_range hEF hE hvσ, hVc _ hv]
  have hAC : A ∪ C = univ := by
    rw [hA, hC]
    ext y
    have hy : y ∉ range σ ↔ y ∈ U ∨ y ∈ V := Set.ext_iff.1 hcompl y
    simp only [mem_union, mem_range, mem_univ, iff_true] at *
    tauto
  have hinter (y : sphere (0 : F) 1) : y ∈ A ∧ y ∈ C ↔ y ∈ range σ := by
    rw [hA, hC]
    have hd := disjoint_left.1 hUV
    simp only [mem_union]
    constructor
    · rintro ⟨hy | hy, hz | hz⟩
      · exact (hd hy hz).elim
      all_goals assumption
    · exact fun hy ↦ ⟨Or.inr hy, Or.inr hy⟩
  -- Brown supplies discs with the same parametrization on their common boundary.
  obtain ⟨eA, heA, hnA⟩ := hb.exists_homeomorph_closure_connectedComponentIn_compl_range
    hEF hE huσ
  obtain ⟨eC, -, hnC⟩ := hb.exists_homeomorph_closure_connectedComponentIn_compl_range
    hEF hE hvσ
  have hB (z : closedBall (0 : E) 1) : ‖(B z : (ℝ ∙ (p : F))ᗮ)‖ = 1 ↔ ‖(z : E)‖ = 1 := by
    simp only [B, coe_closedBallHomeomorphOfFinrankEq_apply,
      ContinuousLinearEquiv.norm_unitBallHomeomorph_eq_one_iff]
  -- Glue both discs at once, retaining the coordinates of the positive disc.
  obtain ⟨h, hhA, hhpos, hhneg⟩ := exists_homeomorph_sphere_of_union_closedBall_orthogonal p
    isClosed_closure isClosed_closure hAC (eA.trans B) (eC.trans B)
    (fun z ↦ by
      rw [Homeomorph.trans_apply, hB, ← mem_sphere_zero_iff_norm, hnA]
      exact ⟨fun hz ↦ (hinter z).1 ⟨z.2, hz⟩,
        fun hz ↦ ((hinter z).2 hz).2⟩)
    (fun z ↦ by
      rw [Homeomorph.trans_apply, hB, ← mem_sphere_zero_iff_norm, hnC]
      exact ⟨fun hz ↦ (hinter z).1 ⟨hz, z.2⟩,
        fun hz ↦ ((hinter z).2 hz).1⟩)
  refine ⟨h, fun x ↦ ?_, hhpos, hhneg⟩
  have hxA : σ x ∈ A := (hA ▸ Or.inr (mem_range_self x))
  rw [hhA ⟨σ x, hxA⟩]
  have he : eA ⟨σ x, hxA⟩ = ⟨(x : E), sphere_subset_closedBall x.2⟩ :=
    Subtype.ext (heA _ x rfl)
  have hnorm : ‖(B (eA ⟨σ x, hxA⟩) : (ℝ ∙ (p : F))ᗮ)‖ = 1 :=
    (hB _).2 (by rw [he]; exact norm_eq_of_mem_sphere x)
  apply Subtype.ext
  simp only [Homeomorph.trans_apply, coe_hemisphereHomeomorph_symm_apply,
    coe_equatorInclusion_apply]
  rw [hnorm]
  simp only [one_pow, sub_self, Real.sqrt_zero, zero_smul, add_zero, he, B,
    coe_closedBallHomeomorphOfFinrankEq_apply, coe_sphereHomeomorphOfFinrankEq_apply]

end TauCeti.IsBicollar
