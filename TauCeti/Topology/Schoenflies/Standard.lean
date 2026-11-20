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

A bicollared `Sᵐ⁻¹` in `Sᵐ`, in any dimension `m ≥ 0`, can be carried to the equator by one ambient
homeomorphism (`TauCeti.IsBicollar.exists_homeomorph_sphere_eq_equatorInclusion`), sending the
closure of a chosen complementary domain onto the closed hemisphere around a pole `p`. The source
is the unit sphere of a real normed space `E`, and the ambient sphere is that of a real inner
product space `F` with `dim F = dim E + 1`. The boundary identification with the equator is
prescribed by a homeomorphism from the source sphere to the unit sphere of the orthogonal
complement of `p`, followed by `TauCeti.equatorInclusion`.

For `m ≥ 2`, the positive and negative sides of the bicollar lie in the two complementary domains,
so the same ambient homeomorphism carries the closures of the positive-side and negative-side
complementary domains onto the closed hemispheres around `p` and `-p`
(`TauCeti.IsBicollar.exists_homeomorph_eq_equatorInclusion`). This simultaneous conclusion
identifies the embedded sphere and its two sides as one standard pair, rather than identifying each
complementary closure with a ball separately as in
`TauCeti.IsBicollar.exists_homeomorph_closure_connectedComponentIn_compl_range`.
For abstract pairs of discs, see
`TauCeti.exists_homeomorph_sphere_of_union_closedBall_orthogonal`.

## Main results

* `TauCeti.IsBicollar.exists_homeomorph_sphere_eq_equatorInclusion`: ambient equatorial
  straightening in every dimension `m ≥ 0`, sending a chosen complementary closure onto the closed
  positive hemisphere.
* `TauCeti.IsBicollar.exists_homeomorph_eq_equatorInclusion`: for `m ≥ 2`, simultaneous ambient
  straightening sending the positive and negative bicollar-side complementary closures onto the
  closed hemispheres around `p` and `-p`.

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

/-- **Ambient equatorial straightening in all dimensions (`m ≥ 0`).** In a real inner product space
`F` with `finrank ℝ F = finrank ℝ E + 1`, for any pole `p : sphere (0 : F) 1`, any homeomorphism
`e : S(E) ≃ₜ S((ℝ ∙ p)ᗮ)`, and any chosen exterior point `y ∉ range σ`, there is an ambient
homeomorphism `h : S(F) ≃ₜ S(F)` straightening `σ` to `equatorInclusion (p : F) ∘ e` and carrying
`closure (connectedComponentIn (range σ)ᶜ y)` onto the closed hemisphere `{z | 0 ≤ ⟪z, p⟫}` (and
the opposite complementary domain onto `{z | ⟪z, p⟫ < 0}`). -/
theorem exists_homeomorph_sphere_eq_equatorInclusion
    (hb : IsBicollar σ b) (hEF : finrank ℝ F = finrank ℝ E + 1)
    (p : sphere (0 : F) 1) (e : sphere (0 : E) 1 ≃ₜ sphere (0 : (ℝ ∙ (p : F))ᗮ) 1)
    {y : sphere (0 : F) 1} (hy : y ∉ range σ) :
    ∃ h : sphere (0 : F) 1 ≃ₜ sphere (0 : F) 1,
      (∀ x, h (σ x) = equatorInclusion (p : F) (e x)) ∧
      (∀ z, 0 ≤ ⟪(h z : F), (p : F)⟫ ↔
        z ∈ closure (connectedComponentIn (range σ)ᶜ y)) ∧
      (∀ z, ⟪(h z : F), (p : F)⟫ < 0 ↔
        z ∉ closure (connectedComponentIn (range σ)ᶜ y)) := by
  obtain ⟨w, hw, hUV, hcompl⟩ :=
    exists_connectedComponentIn_compl_range_sphere_eq_union hEF hb.continuous hb.injective hy
  let U := connectedComponentIn (range σ)ᶜ y
  let V := connectedComponentIn (range σ)ᶜ w
  let A := closure U
  let C := closure V
  have hA : A = U ∪ range σ := hb.closure_connectedComponentIn_compl_range hEF hy
  have hC : C = V ∪ range σ := hb.closure_connectedComponentIn_compl_range hEF hw
  have hAC : A ∪ C = univ := by
    rw [hA, hC, ← union_union_distrib_right, ← hcompl, compl_union_self]
  have hinter : A ∩ C = range σ := by
    rw [hA, hC, ← inter_union_distrib_right, hUV.inter_eq, empty_union]
  let B : closedBall (0 : E) 1 ≃ₜ closedBall (0 : (ℝ ∙ (p : F))ᗮ) 1 :=
    e.radialExtension.subtype fun z ↦ by simp
  have hB (z : closedBall (0 : E) 1) : ‖(B z : (ℝ ∙ (p : F))ᗮ)‖ = 1 ↔ ‖(z : E)‖ = 1 := by
    simp [B]
  obtain ⟨eA, heA, hnA⟩ :=
    hb.exists_homeomorph_closure_connectedComponentIn_compl_range hEF hy
  obtain ⟨eC, -, hnC⟩ :=
    hb.exists_homeomorph_closure_connectedComponentIn_compl_range hEF hw
  obtain ⟨h, hhA, hhpos, -⟩ := exists_homeomorph_sphere_of_union_closedBall_orthogonal p
    isClosed_closure isClosed_closure hAC (eA.trans B) (eC.trans B)
    (fun z ↦ by
      rw [Homeomorph.trans_apply, hB, ← mem_sphere_zero_iff_norm, hnA]
      simpa only [mem_inter_iff, A, C, z.property, true_and] using Set.ext_iff.1 hinter z)
    (fun z ↦ by
      rw [Homeomorph.trans_apply, hB, ← mem_sphere_zero_iff_norm, hnC]
      simpa only [mem_inter_iff, A, C, z.property, and_true] using Set.ext_iff.1 hinter z)
  refine ⟨h, fun x ↦ ?_, hhpos, fun z ↦ not_le.symm.trans (hhpos z).not⟩
  have hxA : σ x ∈ A := hA ▸ Or.inr (mem_range_self x)
  rw [hhA ⟨σ x, hxA⟩]
  have he : (B (eA ⟨σ x, hxA⟩) : (ℝ ∙ (p : F))ᗮ) = e x := by
    simpa only [B, Homeomorph.subtype_apply_coe, heA ⟨σ x, hxA⟩ x rfl] using
      e.radialExtension_coe_sphere x
  apply Subtype.ext
  simp [Homeomorph.trans_apply, coe_hemisphereHomeomorph_symm_apply,
    coe_equatorInclusion_apply, he, norm_eq_of_mem_sphere]

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
  obtain ⟨U, V, -, -, hUV, hcompl, -, -, hpos, hneg, hUc, hVc⟩ :=
    hb.exists_connectedComponentIn_eq hEF hE
  have hu : b (x₀, 1) ∈ U := hpos ⟨mem_univ _, by norm_num⟩
  have huσ : b (x₀, 1) ∉ range σ := hcompl.ge (Or.inl hu)
  obtain ⟨h, hhσ, hhpos, hhneg⟩ :=
    hb.exists_homeomorph_sphere_eq_equatorInclusion hEF p e huσ
  have hUcl : closure U = U ∪ range σ := by
    rw [← hUc _ hu, hb.closure_connectedComponentIn_compl_range hEF huσ, hUc _ hu]
  have hheq (z : sphere (0 : F) 1) : ⟪(h z : F), (p : F)⟫ = 0 ↔ z ∈ range σ := by
    have hmem : h z ∈ range (equatorInclusion (p : F)) ↔ ⟪(h z : F), (p : F)⟫ = 0 := by
      rw [range_equatorInclusion, mem_inter_iff, mem_ofPred_eq, mem_ofPred_eq,
        inner_neg_right, neg_nonneg, ← le_antisymm_iff, eq_comm]
    rw [← hmem]
    exact ⟨fun ⟨u, hu'⟩ ↦ ⟨e.symm u, h.injective (by simp [hhσ, hu'])⟩,
      fun ⟨x, hx⟩ ↦ ⟨e x, hx ▸ (hhσ x).symm⟩⟩
  refine ⟨h, hhσ, fun x t ht y ↦ ?_, fun x t ht y ↦ ?_⟩
  · rw [hhpos, hUc _ hu, hUc _ (hpos (x := (x, t)) ⟨mem_univ x, mem_Ioi.2 ht⟩)]
  · have hyt : b (x, t) ∈ V := hneg ⟨mem_univ x, mem_Iio.2 ht⟩
    have hytσ : b (x, t) ∉ range σ := hcompl.ge (Or.inr hyt)
    rw [hb.closure_connectedComponentIn_compl_range hEF hytσ, hVc _ hyt,
      le_iff_lt_or_eq, hhneg, hheq, hUc _ hu, hUcl]
    simp only [mem_union, not_or]
    exact ⟨fun h ↦ h.elim (fun ⟨hyU, hyσ⟩ ↦ Or.inl ((hcompl.subset (mem_compl hyσ)).resolve_left
        hyU)) Or.inr,
      fun h ↦ h.elim (fun hyV ↦ Or.inl ⟨hUV.notMem_of_mem_right hyV, hcompl.ge (Or.inr hyV)⟩)
        Or.inr⟩

end TauCeti.IsBicollar
