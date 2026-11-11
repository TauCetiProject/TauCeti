/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import TauCeti.Geometry.Manifold.LocallyFlat.Bicollar
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Geometry.Manifold.Instances.Sphere
import TauCeti.Analysis.Normed.Module.Ball.Homeomorph
import TauCeti.Topology.CellularSet.TwoInverseSets
import TauCeti.Topology.Schoenflies.Collapse
import TauCeti.Topology.Schoenflies.Components
import TauCeti.Topology.Schoenflies.Hemisphere

/-!
# The generalized Schoenflies theorem

Let `σ : Sᵐ⁻¹ → Sᵐ` be a map from the unit sphere of a finite-dimensional real normed space `E` of
dimension `m ≥ 2` into the unit sphere of a real inner product space of dimension `m + 1`, and let
`b : Sᵐ⁻¹ × ℝ → Sᵐ` be a bicollar of `σ` (`TauCeti.IsBicollar`). By the Jordan–Brouwer separation
theorem the image `Σ` of `σ` separates `Sᵐ` into two connected components. **M. Brown's
generalized Schoenflies theorem** says that the closure of each of them is a closed `m`-ball:
it is homeomorphic to the closed unit ball of `E` by a homeomorphism which carries `Σ` onto the
unit sphere and inverts `σ` there
(`TauCeti.IsBicollar.exists_homeomorph_closure_connectedComponentIn`).

The proof is Brown's. Fix a pole `p ∈ Sᵐ` and the map `g : Sᵐ → Sᵐ` which is a latitude map on the
closed collar `b (Sᵐ⁻¹ × [-1, 1])` and collapses the two pieces of `Sᵐ` outside the open collar to
`p` and `-p` (`TauCeti.IsBicollar.exists_collapse`). These two pieces are the only inverse sets of
`g`, so they are cellular (`TauCeti.isCellularSet_preimage_singleton_of_injOn`), and collapsing
the cellular set `g⁻¹(p)` identifies `g⁻¹{y | 0 ≤ ⟪y, p⟫}` with a closed ball
(`TauCeti.IsCellularSet.exists_homeomorph_preimage_hemisphere`). The function `y ↦ ⟪g y, p⟫`
vanishes exactly on `Σ`, so `g⁻¹{y | 0 ≤ ⟪y, p⟫}` is the closure of the component of `Sᵐ ∖ Σ`
containing the positive side of the collar (`TauCeti.IsBicollar.closure_setOf_pos`). The other
component is treated in the same way with the reversed bicollar
(`TauCeti.IsBicollar.comp_prodMap_id_neg`).

With Brown's bicollaring theorem (`TauCeti.brownBicollaring`) this shows that a locally flat
`Sᵐ⁻¹ ⊆ Sᵐ` bounds a closed ball on each side.

## Main results

* `TauCeti.IsBicollar.exists_homeomorph_closure_connectedComponentIn`: **the generalized
  Schoenflies theorem**: the closure of each complementary domain of a bicollared `Sᵐ⁻¹ ⊆ Sᵐ`,
  `m ≥ 2`, is homeomorphic to the closed unit ball by a homeomorphism inverting the given
  parametrization on the boundary.

## References

* M. Brown, *A proof of the generalized Schoenflies theorem*, Bull. Amer. Math. Soc. 66 (1960),
  74–76, Theorem 5.
-/

public section

open Function Metric Module Set Topology
open scoped RealInnerProductSpace

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] {σ : sphere (0 : E) 1 → sphere (0 : F) 1}
  {b : sphere (0 : E) 1 × ℝ → sphere (0 : F) 1}

namespace IsBicollar

/-- **The disc on the positive side of a bicollar.** There is a continuous function `φ` on `Sᵐ`
vanishing exactly on the image of `σ`, positive at `b (x₀, 1)` and negative at `b (x₀, -1)`, such
that `{φ ≥ 0}` is homeomorphic to the closed unit ball of `E` by a homeomorphism inverting `σ`. It
is `φ y = ⟪g y, p⟫` for Brown's collapse map `g`. -/
private theorem exists_homeomorph_setOf_nonneg (hEF : finrank ℝ F = finrank ℝ E + 1)
    (hE : 2 ≤ finrank ℝ E) (hb : IsBicollar σ b) (x₀ : sphere (0 : E) 1) :
    ∃ φ : sphere (0 : F) 1 → ℝ, Continuous φ ∧ (∀ y, φ y = 0 ↔ y ∈ range σ) ∧
      0 < φ (b (x₀, 1)) ∧ φ (b (x₀, -1)) < 0 ∧
      ∃ h : {y | 0 ≤ φ y} ≃ₜ closedBall (0 : E) 1,
        ∀ s (hs : 0 ≤ φ (σ s)), (h ⟨σ s, hs⟩ : E) = s := by
  have : FiniteDimensional ℝ F := Module.finite_of_finrank_pos (by omega)
  have : Fact (finrank ℝ F = finrank ℝ E + 1) := ⟨hEF⟩
  have : Nontrivial F := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  obtain ⟨p⟩ : Nonempty (sphere (0 : F) 1) :=
    (NormedSpace.sphere_nonempty.2 zero_le_one).to_subtype
  have hE' : finrank ℝ E = finrank ℝ (ℝ ∙ (p : F))ᗮ :=
    (Submodule.finrank_orthogonal_span_singleton (ne_zero_of_mem_unit_sphere p)).symm
  set e := sphereHomeomorphOfFinrankEq hE'
  obtain ⟨g, hgs, hgb, -, hgσ, hginj⟩ := hb.exists_collapse p e hEF (by omega)
  have hpp : ⟪(p : F), (p : F)⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere p, one_pow]
  -- On the closed collar, `⟪g (b (x, t)), p⟫ = t`.
  have hgbp (x : sphere (0 : E) 1) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
      ⟪(g (b (x, t)) : F), (p : F)⟫ = t := by
    rw [hgb x t ht, inner_add_left, real_inner_smul_left, real_inner_smul_left, hpp,
      Submodule.mem_orthogonal_singleton_iff_inner_left.1 (e x : (ℝ ∙ (p : F))ᗮ).2]
    ring
  -- The fibre `g⁻¹(p)` is cellular, by Brown's theorem on two inverse sets.
  have hA : IsCellularSet (EuclideanSpace ℝ (Fin (finrank ℝ E))) (g ⁻¹' {p}) :=
    isCellularSet_preimage_singleton_of_injOn (by simpa using hE) (by simpa using hEF)
      g.continuous hgs (ne_neg_of_mem_unit_sphere ℝ p) hginj
  obtain ⟨h₀, hh₀, -⟩ := hA.exists_homeomorph_preimage_hemisphere g.continuous hgs
    fun x y hx hxy ↦ by
      by_cases hxp : g x = p
      · exact .inr hxp
      have hxn : g x ≠ -p := fun h ↦ by
        rw [h, coe_neg_sphere, inner_neg_left, hpp] at hx
        linarith
      have hx' : x ∉ g ⁻¹' {p, -p} := by
        rw [mem_preimage, mem_insert_iff, mem_singleton_iff, not_or]
        exact ⟨hxp, hxn⟩
      have hy' : y ∉ g ⁻¹' {p, -p} := by
        rw [mem_preimage, ← hxy]
        exact hx'
      exact .inl (hginj hx' hy' hxy)
  refine ⟨fun y ↦ ⟪(g y : F), (p : F)⟫, by fun_prop, hgσ, ?_, ?_,
    h₀.trans (closedBallHomeomorphOfFinrankEq hE').symm, fun s hs ↦ ?_⟩
  · simp only [hgbp x₀ (by norm_num : (1 : ℝ) ∈ Icc (-1) 1), one_pos]
  · simp only [hgbp x₀ (by norm_num : (-1 : ℝ) ∈ Icc (-1) 1), neg_one_lt_zero]
  · -- On the equator `h₀` is `g`, and `g (σ s) = e s`.
    have hσ0 : ⟪(g (σ s) : F), (p : F)⟫ = 0 := (hgσ _).2 ⟨s, rfl⟩
    have hgσs : (g (σ s) : F) = ((e s : (ℝ ∙ (p : F))ᗮ) : F) := by
      rw [← hb.apply_zero, hgb s 0 (by norm_num)]
      simp
    have hball : (closedBallHomeomorphOfFinrankEq hE').symm (h₀ ⟨σ s, hs⟩) =
        ⟨s, sphere_subset_closedBall s.2⟩ := by
      rw [Homeomorph.symm_apply_eq]
      apply Subtype.ext
      apply Subtype.ext
      rw [hh₀ ⟨σ s, hs⟩ hσ0, hgσs, coe_sphereHomeomorphOfFinrankEq_apply,
        coe_closedBallHomeomorphOfFinrankEq_apply]
    rw [Homeomorph.trans_apply, hball]

variable (hEF : finrank ℝ F = finrank ℝ E + 1) (hE : 2 ≤ finrank ℝ E) (hb : IsBicollar σ b)
include hEF hE hb

/-- **The generalized Schoenflies theorem** (M. Brown). Let `b` be a bicollar of a map `σ` from
the unit sphere `Sᵐ⁻¹` of a finite-dimensional real normed space `E` of dimension `m ≥ 2` into the
unit sphere `Sᵐ` of a real inner product space of dimension `m + 1`. Then the closure of each
connected component of the complement of the image of `σ` is homeomorphic to the closed unit ball
of `E`, by a homeomorphism `h` which inverts `σ` on the boundary, `h (σ s) = s`, and sends a point
to the unit sphere exactly when it lies in the image of `σ`. -/
theorem exists_homeomorph_closure_connectedComponentIn {y : sphere (0 : F) 1}
    (hy : y ∉ range σ) :
    ∃ h : closure (connectedComponentIn (range σ)ᶜ y) ≃ₜ closedBall (0 : E) 1,
      (∀ s (hs : σ s ∈ closure (connectedComponentIn (range σ)ᶜ y)), (h ⟨σ s, hs⟩ : E) = s) ∧
      ∀ x, ‖(h x : E)‖ = 1 ↔ (x : sphere (0 : F) 1) ∈ range σ := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  obtain ⟨x₀⟩ : Nonempty (sphere (0 : E) 1) :=
    (NormedSpace.sphere_nonempty.2 zero_le_one).to_subtype
  set C := connectedComponentIn (range σ)ᶜ y with hCdef
  -- The closure of `C` is `{φ ≥ 0}` for one of the two functions given by `b` and its reversal.
  obtain ⟨φ, hφ, hφσ, hpos, hneg, h, hh⟩ : ∃ φ : sphere (0 : F) 1 → ℝ, Continuous φ ∧
      (∀ y, φ y = 0 ↔ y ∈ range σ) ∧ (∃ z, 0 < φ z) ∧ (∃ z, φ z < 0) ∧
      ∃ h : closure C ≃ₜ closedBall (0 : E) 1,
        ∀ s (hs : σ s ∈ closure C), (h ⟨σ s, hs⟩ : E) = s := by
    obtain ⟨φ, hφ, hφσ, hφ₁, hφ₂, h, hh⟩ := exists_homeomorph_setOf_nonneg hEF hE hb x₀
    rcases lt_or_gt_of_ne fun h ↦ hy ((hφσ y).1 h) with hφy | hφy
    · obtain ⟨φ', hφ', hφ'σ, hφ'₁, hφ'₂, h', hh'⟩ :=
        exists_homeomorph_setOf_nonneg hEF hE hb.comp_prodMap_id_neg x₀
      simp only [comp_apply, Prod.map_apply, id_eq, neg_neg] at hφ'₁ hφ'₂
      have hC : C = {w | 0 < φ' w} := by
        have hneg {w} (hw : φ w < 0) := connectedComponentIn_compl_range_eq_setOf_neg hEF
          hb.continuous hb.injective hφ hφσ hφ₁ hw
        rw [hCdef, hneg hφy, ← hneg hφ₂]
        exact connectedComponentIn_compl_range_eq_setOf_pos hEF hb.continuous hb.injective hφ'
          hφ'σ hφ'₂ hφ'₁
      have hcl : closure C = {w | 0 ≤ φ' w} := by
        rw [hC, hb.closure_setOf_pos hEF (by omega) hφ' hφ'σ hφ'₁ hφ'₂]
      exact ⟨φ', hφ', hφ'σ, ⟨_, hφ'₁⟩, ⟨_, hφ'₂⟩, (Homeomorph.setCongr hcl).trans h',
        fun s hs ↦ hh' s (by rw [hcl] at hs; exact hs)⟩
    · have hcl : closure C = {w | 0 ≤ φ w} := by
        rw [hCdef, connectedComponentIn_compl_range_eq_setOf_pos hEF hb.continuous hb.injective
          hφ hφσ hφ₂ hφy, hb.closure_setOf_pos hEF (by omega) hφ hφσ hφy hφ₂]
      exact ⟨φ, hφ, hφσ, ⟨_, hφ₁⟩, ⟨_, hφ₂⟩, (Homeomorph.setCongr hcl).trans h,
        fun s hs ↦ hh s (by rw [hcl] at hs; exact hs)⟩
  -- The image of `σ` is the frontier of `C`, so it lies in the closure.
  have hσC (s : sphere (0 : E) 1) : σ s ∈ closure C :=
    frontier_subset_closure ((hb.frontier_connectedComponentIn_compl_range hEF (by omega) hy).symm ▸
      mem_range_self s)
  refine ⟨h, hh, fun x ↦ ⟨fun hx ↦ ?_, ?_⟩⟩
  · set s : sphere (0 : E) 1 := ⟨h x, mem_sphere_zero_iff_norm.2 hx⟩
    have hxx : x = ⟨σ s, hσC s⟩ := h.injective (Subtype.ext (hh s (hσC s)).symm)
    exact ⟨_, congrArg Subtype.val hxx.symm⟩
  · rintro ⟨s, hs⟩
    obtain rfl : x = ⟨σ s, hσC s⟩ := Subtype.ext hs.symm
    rw [hh s (hσC s)]
    exact norm_eq_of_mem_sphere s

end IsBicollar

end TauCeti
