/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import TauCeti.Topology.Schoenflies.Components
import Mathlib.Geometry.Manifold.Instances.Sphere
import TauCeti.Analysis.Normed.Module.Ball.Homeomorph
import TauCeti.Analysis.Normed.Module.Ball.Radial.Cone
import TauCeti.Topology.CellularSet.TwoInverseSets
import TauCeti.Topology.Schoenflies.Collapse
import TauCeti.Topology.Schoenflies.Hemisphere

/-!
# The generalized Schoenflies theorem

Let `σ : Sᵐ⁻¹ → Sᵐ` be a map of the unit sphere of a real normed space `E` of dimension `m ≥ 2`
into the unit sphere of a real inner product space of dimension `m + 1`, with a bicollar
`b : Sᵐ⁻¹ × ℝ → Sᵐ` (`TauCeti.IsBicollar`). Then the closure of each of the two complementary
domains of the image of `σ` is a closed `m`-cell bounded by that image: it is homeomorphic to the
closed unit ball of `E` by a homeomorphism whose inverse restricts to `σ` on the unit sphere of `E`
(`TauCeti.IsBicollar.exists_homeomorph_closure_connectedComponentIn`). This is M. Brown's
generalized Schoenflies theorem. Brown's bicollaring theorem (`TauCeti.brownBicollaring`)
supplies such a bicollar for locally flat spheres, which therefore bound a closed ball on each side.
The bicollar cannot be dropped: the Alexander horned sphere bounds a ball on only one side.

The proof is Brown's. Choose a pole `p` and Brown's collapse `g : Sᵐ → Sᵐ`
(`TauCeti.IsBicollar.exists_collapse`), the latitude map `b (x, t) ↦ √(1 - t²) • e x + t • p` on
the closed collar, for a homeomorphism `e` of `Sᵐ⁻¹` with the equator orthogonal to `p`. It sends
the two pieces outside the open collar to the poles `±p` and is injective elsewhere. Both of its
inverse sets are cellular, by Brown's theorem on two inverse sets
(`TauCeti.isCellularSet_preimage_singleton_of_injOn`). The closure of the complementary domain
containing the positive side of the collar is the preimage under `g` of the closed hemisphere
`{0 ≤ ⟪y, p⟫}` (`TauCeti.IsBicollar.closure_setOf_pos`), which collapsing `g⁻¹(p)` identifies with
the closed hemisphere, hence with a closed ball, by a homeomorphism agreeing with `g` over the
equator (`TauCeti.IsCellularSet.exists_homeomorph_preimage_hemisphere`). The other domain is
treated in the same way after reversing the bicollar.

## Main results

* `TauCeti.IsBicollar.exists_homeomorph_closure_connectedComponentIn`: **the generalized
  Schoenflies theorem** for bicollared spheres `Sᵐ⁻¹ ⊆ Sᵐ`, `m ≥ 2`.

## References

* M. Brown, *A proof of the generalized Schoenflies theorem*, Bull. Amer. Math. Soc. 66 (1960),
  74–76, Theorem 5.
-/

public section

open Function Metric Module Set Topology
open scoped RealInnerProductSpace

namespace TauCeti

namespace IsBicollar

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] {σ : sphere (0 : E) 1 → sphere (0 : F) 1}
  {b : sphere (0 : E) 1 × ℝ → sphere (0 : F) 1}

/-- The generalized Schoenflies theorem for a complementary domain not containing the point
`b (x₀, -1)` of the negative side of the bicollar. -/
private theorem exists_homeomorph_closure_connectedComponentIn_of_notMem (hb : IsBicollar σ b)
    (hEF : finrank ℝ F = finrank ℝ E + 1) (hE : 1 < finrank ℝ E) (x₀ : sphere (0 : E) 1)
    {y : sphere (0 : F) 1} (hy : y ∉ range σ)
    (hy' : b (x₀, -1) ∉ connectedComponentIn (range σ)ᶜ y) :
    ∃ h : closure (connectedComponentIn (range σ)ᶜ y) ≃ₜ closedBall (0 : E) 1,
      ∀ x : sphere (0 : E) 1,
        (h.symm ⟨x, sphere_subset_closedBall x.2⟩ : sphere (0 : F) 1) = σ x := by
  have : FiniteDimensional ℝ E := .of_finrank_pos (by omega)
  have : FiniteDimensional ℝ F := .of_finrank_pos (by omega)
  have : Fact (finrank ℝ F = finrank ℝ E + 1) := ⟨hEF⟩
  -- Brown's collapse `g` onto the poles `±p`, with the equator identified with `Sᵐ⁻¹` by `e`.
  set p := σ x₀
  have hpp : ⟪(p : F), (p : F)⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere p, one_pow]
  set e := sphereHomeomorphOfFinrankEq
    (Submodule.finrank_orthogonal_span_singleton (𝕜 := ℝ) (n := finrank ℝ E)
      (ne_zero_of_mem_unit_sphere p)).symm
  obtain ⟨g, hgs, hlat, -, hφσ, hinj⟩ := hb.exists_collapse p e hEF hE
  set φ : sphere (0 : F) 1 → ℝ := fun w ↦ ⟪(g w : F), (p : F)⟫
  have hφ : Continuous φ := by fun_prop
  have hφ1 : 0 < φ (b (x₀, 1)) := by
    have h := congrArg (⟪·, (p : F)⟫) (hlat x₀ 1 ⟨by norm_num, le_rfl⟩)
    simp only [inner_add_left, inner_smul_left, hpp] at h
    simp [φ, h]
  have hφ1' : φ (b (x₀, -1)) < 0 := by
    have h := congrArg (⟪·, (p : F)⟫) (hlat x₀ (-1) ⟨le_rfl, by norm_num⟩)
    simp only [inner_add_left, inner_smul_left, hpp] at h
    simp [φ, h]
  -- The domain of `y` is the positive domain of `φ`, so its closure is the preimage of the
  -- closed hemisphere over `p`.
  have hφy : 0 < φ y := by
    rcases lt_trichotomy (φ y) 0 with h | h | h
    · refine absurd ?_ hy'
      rw [connectedComponentIn_compl_range_eq_setOf_neg hEF hb.continuous hb.injective hφ hφσ hφ1 h]
      exact hφ1'
    · exact absurd ((hφσ y).1 h) hy
    · exact h
  have hcl : closure (connectedComponentIn (range σ)ᶜ y) =
      g ⁻¹' {w | 0 ≤ ⟪(w : F), (p : F)⟫} := by
    rw [connectedComponentIn_compl_range_eq_setOf_pos hEF hb.continuous hb.injective hφ hφσ hφ1'
        hφy,
      hb.closure_setOf_pos hEF hE hφ hφσ hφy hφ1', preimage_ofPred_eq]
  -- The inverse set over `p` is cellular, so the preimage of the closed hemisphere is a closed
  -- ball.
  have hcell : IsCellularSet (EuclideanSpace ℝ (Fin (finrank ℝ E))) (g ⁻¹' {p}) :=
    isCellularSet_preimage_singleton_of_injOn (by simp; omega) (by simpa using hEF) g.continuous
      hgs hinj
  obtain ⟨h₀, hh₀, -⟩ := hcell.exists_homeomorph_preimage_hemisphere g.continuous hgs
    fun x x' hx hxx' ↦ by
      by_cases hxp : g x = p
      · exact .inr hxp
      by_cases hxn : g x = -p
      · simp [hxn] at hx
        linarith
      refine .inl (hinj ?_ ?_ hxx')
      · simp [hxp, hxn]
      · simp [← hxx', hxp, hxn]
  -- The radial extension of `e⁻¹` carries the closed ball of the equatorial hyperplane onto that
  -- of `E`, extending `e⁻¹` on the unit spheres.
  let c : closedBall (0 : (ℝ ∙ (p : F))ᗮ) 1 ≃ₜ closedBall (0 : E) 1 :=
    e.symm.sphereCone.subtype fun v ↦ by
      simp only [mem_closedBall_zero_iff, Homeomorph.norm_sphereCone_apply]
  let s : closure (connectedComponentIn (range σ)ᶜ y) ≃ₜ g ⁻¹' {w | 0 ≤ ⟪(w : F), (p : F)⟫} :=
    (Homeomorph.refl _).subtype fun w ↦ by rw [hcl, Homeomorph.refl_apply, id_eq]
  refine ⟨s.trans (h₀.trans c), fun x ↦ ?_⟩
  -- On the image of `σ`, which `g` sends to the equator by `e`, the homeomorphism inverts `σ`.
  have hσx : σ x ∈ closure (connectedComponentIn (range σ)ᶜ y) := by
    rw [hcl, mem_preimage, mem_ofPred_eq]
    exact ((hφσ _).2 ⟨x, rfl⟩).ge
  have hgσ : (g (σ x) : F) = ((e x : (ℝ ∙ (p : F))ᗮ) : F) := by
    simpa [hb.apply_zero] using hlat x 0 ⟨by norm_num, by norm_num⟩
  have key : s.trans (h₀.trans c) ⟨σ x, hσx⟩ = ⟨x, sphere_subset_closedBall x.2⟩ := by
    have hs : s ⟨σ x, hσx⟩ = ⟨σ x, hcl ▸ hσx⟩ := Subtype.ext (by simp [s])
    have h₀x : (h₀ ⟨σ x, hcl ▸ hσx⟩ : (ℝ ∙ (p : F))ᗮ) = (e x : (ℝ ∙ (p : F))ᗮ) :=
      Subtype.ext ((hh₀ _ ((hφσ _).2 ⟨x, rfl⟩)).trans hgσ)
    apply Subtype.ext
    rw [Homeomorph.trans_apply, Homeomorph.trans_apply, hs]
    simp only [c, Homeomorph.subtype_apply_coe, h₀x, Homeomorph.coe_sphereCone]
    simp
  rw [← key, Homeomorph.symm_apply_apply]

/-- **The generalized Schoenflies theorem.** Let `b` be a bicollar of a map `σ` from the unit
sphere `Sᵐ⁻¹` of a real normed space `E` of dimension `m ≥ 2` into the unit sphere `Sᵐ` of a real
inner product space of dimension `m + 1`. Then the closure of each connected component of the
complement of the image of `σ` is homeomorphic to the closed unit ball of `E`, by a homeomorphism
whose inverse restricts to `σ` on the unit sphere of `E`. -/
theorem exists_homeomorph_closure_connectedComponentIn (hb : IsBicollar σ b)
    (hEF : finrank ℝ F = finrank ℝ E + 1) (hE : 1 < finrank ℝ E) {y : sphere (0 : F) 1}
    (hy : y ∉ range σ) :
    ∃ h : closure (connectedComponentIn (range σ)ᶜ y) ≃ₜ closedBall (0 : E) 1,
      ∀ x : sphere (0 : E) 1,
        (h.symm ⟨x, sphere_subset_closedBall x.2⟩ : sphere (0 : F) 1) = σ x := by
  have : FiniteDimensional ℝ E := .of_finrank_pos (by omega)
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  obtain ⟨x₀, hx₀⟩ := (NormedSpace.sphere_nonempty (x := (0 : E)) (r := 1)).2 zero_le_one
  by_cases hy' : b (⟨x₀, hx₀⟩, -1) ∈ connectedComponentIn (range σ)ᶜ y
  · -- The domain of `y` contains the negative side of the bicollar: reverse the bicollar.
    refine hb.comp_prodMap_id_neg.exists_homeomorph_closure_connectedComponentIn_of_notMem hEF hE
      ⟨x₀, hx₀⟩ hy fun h ↦ ?_
    have hσ : b (⟨x₀, hx₀⟩, 1) ∈ (range σ)ᶜ := fun hσ ↦ by
      have h' : (⟨x₀, hx₀⟩, (1 : ℝ)) ∈ b ⁻¹' range σ := hσ
      rw [hb.preimage_range] at h'
      exact one_ne_zero (mem_singleton_iff.1 h'.2)
    have h' : b (⟨x₀, hx₀⟩, 1) ∈ connectedComponentIn (range σ)ᶜ y := by simpa using h
    rw [connectedComponentIn_eq hy'] at h'
    exact (hb.disjoint_connectedComponentIn_compl_range hEF hE ⟨x₀, hx₀⟩ ⟨x₀, hx₀⟩ one_pos
      (by norm_num : (-1 : ℝ) < 0)).ne_of_mem (mem_connectedComponentIn hσ) h' rfl
  · exact hb.exists_homeomorph_closure_connectedComponentIn_of_notMem hEF hE ⟨x₀, hx₀⟩ hy hy'

end IsBicollar

end TauCeti
