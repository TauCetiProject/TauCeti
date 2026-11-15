/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Schoenflies.Disc
public import TauCeti.Analysis.InnerProductSpace.Hemisphere
import TauCeti.Analysis.Normed.Module.Ball.Radial.Extension
import TauCeti.Topology.ConnectedComponents
import TauCeti.Topology.Homeomorph.ClosedBall

/-!
# Simultaneous Schoenflies straightening

In every dimension (`dim F = dim E + 1`), a bicollared sphere in `S(F)` can be carried to the
equator by one ambient homeomorphism sending any chosen pair of points `u, v` in distinct
complementary components into the standard hemispheres around `p` and `-p`, with `h u = p`
(`TauCeti.IsBicollar.exists_homeomorph_eq_equatorInclusion_of_connectedComponentIn_ne`). For
`m ≥ 2` (`1 < finrank ℝ E`), the positive and negative sides of the bicollar select those two
complementary components canonically (`TauCeti.IsBicollar.exists_homeomorph_eq_equatorInclusion`).
The source is the unit sphere of a real normed space `E`, and the ambient sphere is that of a real
inner product space `F` with `dim F = dim E + 1`. The boundary identification with the equator is
prescribed by a homeomorphism from the source sphere to the unit sphere of the orthogonal
complement of a pole, followed by `TauCeti.equatorInclusion`.

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

private theorem exists_recentered_closedBall_homeomorph {X H : Type*} [TopologicalSpace X]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H] (d : X ≃ₜ closedBall (0 : H) 1)
    {z₀ : X} (hz₀ : ‖(d z₀ : H)‖ ≠ 1) :
    ∃ d' : X ≃ₜ closedBall (0 : H) 1,
      d' z₀ = ⟨0, mem_closedBall_self zero_le_one⟩ ∧
      (∀ z : X, ‖(d z : H)‖ = 1 → d' z = d z) ∧
      ∀ z : X, ‖(d' z : H)‖ = 1 ↔ ‖(d z : H)‖ = 1 := by
  have hq : ‖(d z₀ : H)‖ < 1 := lt_of_le_of_ne (mem_closedBall_zero_iff.1 (d z₀).2) hz₀
  let d' := d.trans (Homeomorph.shiftClosedBallZero hq).symm
  refine ⟨d', ?_, fun z hz ↦ ?_, fun z ↦ ?_⟩
  · exact (Homeomorph.shiftClosedBallZero hq).symm_apply_eq.2
      (Homeomorph.shiftClosedBallZero_zero hq).symm
  · exact (Homeomorph.shiftClosedBallZero hq).symm_apply_eq.2
      (Homeomorph.shiftClosedBallZero_of_norm_eq_one hq hz).symm
  · have hsymm : d z = Homeomorph.shiftClosedBallZero hq (d' z) := by simp [d']
    rw [hsymm, Homeomorph.coe_shiftClosedBallZero_apply, Homeomorph.norm_shiftBallZero_eq_one_iff]

/-- **Simultaneous Schoenflies theorem for distinct complementary components.** Let `σ` be a
bicollared sphere in `S(F)` in any dimension `dim F = dim E + 1`, and let `u` and `v` lie in
distinct connected components of `(range σ)ᶜ`. For any pole `p` of `F` and homeomorphism `e` of
unit spheres, there is an ambient self-homeomorphism `h` of `S(F)` satisfying `h u = p`,
`h (σ x) = equatorInclusion (p : F) (e x)`, and carrying the closures of the complementary
components of `u` and `v` onto the closed hemispheres around `p` and `-p`. -/
theorem exists_homeomorph_eq_equatorInclusion_of_connectedComponentIn_ne
    (hb : IsBicollar σ b) (hEF : finrank ℝ F = finrank ℝ E + 1)
    (p : sphere (0 : F) 1) (e : sphere (0 : E) 1 ≃ₜ sphere (0 : (ℝ ∙ (p : F))ᗮ) 1)
    {u v : sphere (0 : F) 1} (hu : u ∉ range σ) (hv : v ∉ range σ)
    (huv : connectedComponentIn (range σ)ᶜ u ≠ connectedComponentIn (range σ)ᶜ v) :
    ∃ h : sphere (0 : F) 1 ≃ₜ sphere (0 : F) 1,
      h u = p ∧
      (∀ x, h (σ x) = equatorInclusion (p : F) (e x)) ∧
      (∀ y, 0 ≤ ⟪(h y : F), (p : F)⟫ ↔ y ∈ closure (connectedComponentIn (range σ)ᶜ u)) ∧
      (∀ y, ⟪(h y : F), (p : F)⟫ ≤ 0 ↔ y ∈ closure (connectedComponentIn (range σ)ᶜ v)) := by
  have : FiniteDimensional ℝ F := .of_finrank_pos (by omega)
  let B : closedBall (0 : E) 1 ≃ₜ closedBall (0 : (ℝ ∙ (p : F))ᗮ) 1 :=
    e.radialExtension.subtype fun z ↦ by simp
  let U := connectedComponentIn (range σ)ᶜ u
  let V := connectedComponentIn (range σ)ᶜ v
  have hcompl : (range σ)ᶜ = U ∪ V :=
    (connectedComponentIn_union_eq_of_natCard_eq_two
      (natCard_connectedComponents_sphere_compl_range_eq_two hEF hb.continuous hb.injective)
      hu hv huv).symm
  let A := closure U
  let C := closure V
  have hA : A = U ∪ range σ := hb.closure_connectedComponentIn_compl_range hEF hu
  have hC : C = V ∪ range σ := hb.closure_connectedComponentIn_compl_range hEF hv
  have hAC : A ∪ C = univ := by
    rw [hA, hC, ← union_union_distrib_right, ← hcompl, compl_union_self]
  have hinter : A ∩ C = range σ := by
    rw [hA, hC, ← inter_union_distrib_right, (disjoint_connectedComponentIn_of_ne huv).inter_eq,
      empty_union]
  obtain ⟨eA, heA, hnA⟩ := hb.exists_homeomorph_closure_connectedComponentIn_compl_range hEF hu
  obtain ⟨eC, -, hnC⟩ := hb.exists_homeomorph_closure_connectedComponentIn_compl_range hEF hv
  have hB (z : closedBall (0 : E) 1) : ‖(B z : (ℝ ∙ (p : F))ᗮ)‖ = 1 ↔ ‖(z : E)‖ = 1 := by simp [B]
  have huA : u ∈ A := subset_closure (mem_connectedComponentIn hu)
  have hu1 : ‖((eA.trans B) ⟨u, huA⟩ : (ℝ ∙ (p : F))ᗮ)‖ ≠ 1 := fun h1 ↦ hu <| by
    rwa [Homeomorph.trans_apply, hB, ← mem_sphere_zero_iff_norm, hnA] at h1
  obtain ⟨eA', hq0, hfix, heA'⟩ := exists_recentered_closedBall_homeomorph (eA.trans B) hu1
  obtain ⟨h, hhA, hhpos, hhneg⟩ := exists_homeomorph_sphere_of_union_closedBall_orthogonal p
    isClosed_closure isClosed_closure hAC eA' (eC.trans B)
    (fun z ↦ by
      rw [heA', Homeomorph.trans_apply, hB, ← mem_sphere_zero_iff_norm, hnA]
      simpa only [mem_inter_iff, A, C, z.2, true_and] using Set.ext_iff.1 hinter z)
    (fun z ↦ by
      rw [Homeomorph.trans_apply, hB, ← mem_sphere_zero_iff_norm, hnC]
      simpa only [mem_inter_iff, A, C, z.2, and_true] using Set.ext_iff.1 hinter z)
  refine ⟨h, ?_, fun x ↦ ?_, hhpos, hhneg⟩
  · rw [hhA ⟨u, huA⟩, hq0]
    exact Subtype.ext (by simp [coe_hemisphereHomeomorph_symm_apply])
  · have hxA : σ x ∈ A := hA ▸ Or.inr (mem_range_self x)
    have he : (B (eA ⟨σ x, hxA⟩) : (ℝ ∙ (p : F))ᗮ) = e x := by
      simpa only [B, Homeomorph.subtype_apply_coe, heA ⟨σ x, hxA⟩ x rfl] using
        e.radialExtension_coe_sphere x
    have hfixx : eA' ⟨σ x, hxA⟩ = B (eA ⟨σ x, hxA⟩) :=
      hfix ⟨σ x, hxA⟩ (by rw [Homeomorph.trans_apply, he]; exact norm_eq_of_mem_sphere (e x))
    rw [hhA ⟨σ x, hxA⟩, hfixx]
    exact Subtype.ext (by simp [coe_hemisphereHomeomorph_symm_apply, coe_equatorInclusion_apply, he,
      norm_eq_of_mem_sphere])

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
  have hv : b (x₀, -1) ∈ V := hneg ⟨mem_univ _, by norm_num⟩
  have huσ : b (x₀, 1) ∉ range σ := hcompl.ge (Or.inl hu)
  have hvσ : b (x₀, -1) ∉ range σ := hcompl.ge (Or.inr hv)
  have huv : connectedComponentIn (range σ)ᶜ (b (x₀, 1)) ≠
      connectedComponentIn (range σ)ᶜ (b (x₀, -1)) := by
    rw [hUc _ hu, hVc _ hv]
    exact fun heq ↦ disjoint_left.1 hUV hu (heq ▸ hu)
  obtain ⟨h, -, hhσ, hhpos, hhneg⟩ :=
    hb.exists_homeomorph_eq_equatorInclusion_of_connectedComponentIn_ne hEF p e huσ hvσ huv
  refine ⟨h, hhσ, fun x t ht y ↦ ?_, fun x t ht y ↦ ?_⟩
  · rw [hhpos, hUc _ hu, hUc _ (hpos (x := (x, t)) ⟨mem_univ x, mem_Ioi.2 ht⟩)]
  · rw [hhneg, hVc _ hv, hVc _ (hneg (x := (x, t)) ⟨mem_univ x, mem_Iio.2 ht⟩)]

end TauCeti.IsBicollar
