/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import TauCeti.Geometry.Manifold.LocallyFlat.Bicollar
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Geometry.Manifold.Instances.Sphere
import TauCeti.Analysis.Normed.Module.Ball.Homeomorph
import TauCeti.Analysis.Normed.Module.Ball.Radial.Extension
import TauCeti.Topology.CellularSet.TwoInverseSets
import TauCeti.Topology.Schoenflies.Collapse
import TauCeti.Topology.Schoenflies.Components
import TauCeti.Topology.Schoenflies.Hemisphere

/-!
# The generalized Schoenflies theorem

Let `σ : Sᵐ⁻¹ → Sᵐ` be a map from the unit sphere of a real normed space `E` of dimension
`m ≥ 2` into the unit sphere of a real inner product space of dimension `m + 1`, with a bicollar
`b : Sᵐ⁻¹ × ℝ → Sᵐ` (`TauCeti.IsBicollar`). **Brown's generalized Schoenflies theorem** states that
the closure of each of the two complementary domains of the image of `σ` is a closed `m`-cell, by
a homeomorphism onto the closed unit ball of `E` which inverts `σ` on the boundary
(`TauCeti.IsBicollar.exists_homeomorph_closure_connectedComponentIn`).

The proof is Brown's. Fix a pole `p` and identify `Sᵐ⁻¹` with the equator orthogonal to `p`. The
collapse `g : Sᵐ → Sᵐ` of the outside of the bicollar (`TauCeti.IsBicollar.exists_collapse`) is the
latitude map `b (x, t) ↦ √(1 - t²) • x + t • p` on the closed collar and sends the two pieces
outside the open collar to the poles `p` and `-p`. It is injective off these two pieces, so both
are cellular (`TauCeti.isCellularSet_preimage_singleton_of_injOn`). The function `⟪g ·, p⟫`
vanishes exactly on the image of `σ` and is `t` at `b (x, t)` for `t ∈ [-1, 1]`, so the
complementary domain containing `b (x, 1)` is the set where it is positive, and its closure is the
preimage under `g` of the closed hemisphere of `p` (`TauCeti.IsBicollar.closure_setOf_pos`). Since
the only fibre of `g` over that hemisphere with more than one point is the cellular set `g⁻¹(p)`,
this preimage is a closed disc, by a homeomorphism agreeing with `g` over the equator
(`TauCeti.IsCellularSet.exists_homeomorph_preimage_hemisphere`). The radial extension of the
identification of `Sᵐ⁻¹` with the equator (`Homeomorph.radialExtension`) carries that disc to the
closed unit ball of `E`, and the resulting homeomorphism sends `σ x = b (x, 0)` to `x`. The other
complementary domain is handled in the same way after reversing the bicollar
(`TauCeti.IsBicollar.comp_prodMap_id_neg`).

## Main results

* `TauCeti.IsBicollar.exists_homeomorph_closure_connectedComponentIn`: **the generalized
  Schoenflies theorem**.

## References

* M. Brown, *A proof of the generalized Schoenflies theorem*, Bull. Amer. Math. Soc. 66 (1960),
  74–76, Theorem 5.
-/

public section

open Function Metric Module Set Topology
open scoped RealInnerProductSpace

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] {σ : sphere (0 : E) 1 → sphere (0 : F) 1}
  {b : sphere (0 : E) 1 × ℝ → sphere (0 : F) 1}

namespace IsBicollar

/-- The positive side of a bicollar, cut out by a function. Let `b` be a bicollar of `σ`, with
`m ≥ 2`. There is a continuous function `φ` on `Sᵐ` vanishing exactly on the image of `σ`, equal to
`1` at every point `b (x, 1)` and to `-1` at every point `b (x, -1)`, together with a homeomorphism
of `{φ ≥ 0}` with the closed unit ball of `E` sending `σ x` to `x`. -/
private theorem exists_homeomorph_setOf_nonneg (hb : IsBicollar σ b)
    (hEF : finrank ℝ F = finrank ℝ E + 1) (hE : 1 < finrank ℝ E) :
    ∃ φ : sphere (0 : F) 1 → ℝ, Continuous φ ∧ (∀ w, φ w = 0 ↔ w ∈ range σ) ∧
      (∀ x, φ (b (x, 1)) = 1) ∧ (∀ x, φ (b (x, -1)) = -1) ∧
      ∃ h : {w | 0 ≤ φ w} ≃ₜ closedBall (0 : E) 1, ∀ x : sphere (0 : E) 1,
        (h.symm ⟨x, sphere_subset_closedBall x.2⟩ : sphere (0 : F) 1) = σ x := by
  have : FiniteDimensional ℝ E := .of_finrank_pos (by omega)
  have : FiniteDimensional ℝ F := .of_finrank_pos (by omega)
  have : Fact (finrank ℝ F = finrank ℝ E + 1) := ⟨hEF⟩
  have : Nontrivial F := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  obtain ⟨p⟩ : Nonempty (sphere (0 : F) 1) :=
    (NormedSpace.sphere_nonempty.2 zero_le_one).to_subtype
  have hp0 : (p : F) ≠ 0 := ne_zero_of_mem_unit_sphere p
  have hpp : ⟪(p : F), (p : F)⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere p, one_pow]
  -- The equator `(ℝ ∙ p)ᗮ` has the dimension of `E`.
  let e : sphere (0 : E) 1 ≃ₜ sphere (0 : (ℝ ∙ (p : F))ᗮ) 1 :=
    sphereHomeomorphOfFinrankEq (Submodule.finrank_orthogonal_span_singleton hp0).symm
  obtain ⟨g, hgs, hgb, -, hgσ, hginj⟩ := hb.exists_collapse p e hEF hE
  set φ : sphere (0 : F) 1 → ℝ := fun w ↦ ⟪(g w : F), (p : F)⟫
  have hφc : Continuous φ := by fun_prop
  have hφb (x : sphere (0 : E) 1) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) : φ (b (x, t)) = t := by
    have he : ⟪((e x : (ℝ ∙ (p : F))ᗮ) : F), (p : F)⟫ = 0 :=
      Submodule.mem_orthogonal_singleton_iff_inner_left.1 (e x : (ℝ ∙ (p : F))ᗮ).2
    simp only [φ, hgb x t ht, inner_add_left, inner_smul_left, he, hpp]
    simp
  -- The fibre over `p` is cellular, so the preimage of the closed hemisphere is a closed disc.
  let m := finrank ℝ E
  have hpn : p ≠ -p := fun h ↦ by
    have := congrArg (fun w : sphere (0 : F) 1 ↦ ⟪(w : F), (p : F)⟫) h
    simp only [coe_neg_sphere, inner_neg_left, hpp] at this
    norm_num at this
  have hcell : IsCellularSet (EuclideanSpace ℝ (Fin m)) (g ⁻¹' {p}) :=
    isCellularSet_preimage_singleton_of_injOn (by simpa [m] using hE.nat_succ_le)
      (by simpa [m] using hEF) g.continuous hgs hpn hginj
  obtain ⟨h₁, hh₁, -⟩ := hcell.exists_homeomorph_preimage_hemisphere g.continuous hgs
    fun x y hx hxy ↦ by
      by_cases hxp : g x ∈ ({p, -p} : Set (sphere (0 : F) 1))
      · rcases hxp with hxp | hxp
        · exact .inr hxp
        · rw [hxp, coe_neg_sphere, inner_neg_left, hpp] at hx
          norm_num at hx
      · exact .inl (hginj hxp (by simpa [← hxy] using hxp) hxy)
  -- The radial extension of `e⁻¹` carries the closed disc of the equator to that of `E`.
  let r : closedBall (0 : (ℝ ∙ (p : F))ᗮ) 1 ≃ₜ closedBall (0 : E) 1 :=
    (Homeomorph.radialExtension e.symm).subtype fun v ↦ by simp
  refine ⟨φ, hφc, fun w ↦ hgσ w, fun x ↦ hφb x (by simp), fun x ↦ hφb x (by simp),
    h₁.trans r, fun x ↦ ?_⟩
  have hσx : σ x ∈ g ⁻¹' {y | 0 ≤ ⟪(y : F), (p : F)⟫} := by
    simp [(hgσ (σ x)).2 (mem_range_self x)]
  have hgσx : (g (σ x) : F) = ((e x : (ℝ ∙ (p : F))ᗮ) : F) := by
    rw [← hb.apply_zero x, hgb x 0 (by simp)]
    simp
  have h₁x : (h₁ ⟨σ x, hσx⟩ : (ℝ ∙ (p : F))ᗮ) = (e x : (ℝ ∙ (p : F))ᗮ) :=
    Subtype.ext ((hh₁ ⟨σ x, hσx⟩ ((hgσ (σ x)).2 (mem_range_self x))).trans hgσx)
  have key : (h₁.trans r) ⟨σ x, hσx⟩ = ⟨x, sphere_subset_closedBall x.2⟩ := by
    ext1
    simp [r, h₁x]
  rw [← key, Homeomorph.symm_apply_apply]

end IsBicollar

/-- **The generalized Schoenflies theorem** (Brown). Let `σ` be a map from the unit sphere `Sᵐ⁻¹` of
a real normed space `E` of dimension `m ≥ 2` into the unit sphere `Sᵐ` of a real inner product
space of dimension `m + 1`, with a bicollar `b`. Then the closure of the complementary domain of
the image of `σ` containing any point `y` off that image is homeomorphic to the closed unit ball of
`E`, by a homeomorphism `h` with `h (σ x) = x`; in particular `h` carries the image of `σ` onto the
unit sphere of `E`. -/
theorem IsBicollar.exists_homeomorph_closure_connectedComponentIn (hb : IsBicollar σ b)
    (hEF : finrank ℝ F = finrank ℝ E + 1) (hE : 1 < finrank ℝ E) {y : sphere (0 : F) 1}
    (hy : y ∉ range σ) :
    ∃ h : closure (connectedComponentIn (range σ)ᶜ y) ≃ₜ closedBall (0 : E) 1,
      (∀ x : sphere (0 : E) 1,
        (h.symm ⟨x, sphere_subset_closedBall x.2⟩ : sphere (0 : F) 1) = σ x) ∧
      ∀ z, ‖(h z : E)‖ = 1 ↔ (z : sphere (0 : F) 1) ∈ range σ := by
  have : FiniteDimensional ℝ E := .of_finrank_pos (by omega)
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  obtain ⟨x₀⟩ : Nonempty (sphere (0 : E) 1) :=
    (NormedSpace.sphere_nonempty.2 zero_le_one).to_subtype
  -- It suffices to find a function `φ` as in `exists_homeomorph_setOf_nonneg` whose positive set
  -- is the component of `y`.
  suffices H : ∃ φ : sphere (0 : F) 1 → ℝ, Continuous φ ∧ (∀ w, φ w = 0 ↔ w ∈ range σ) ∧
      (∃ z, φ z < 0) ∧ connectedComponentIn (range σ)ᶜ y = {w | 0 < φ w} ∧
      ∃ h : {w | 0 ≤ φ w} ≃ₜ closedBall (0 : E) 1, ∀ x : sphere (0 : E) 1,
        (h.symm ⟨x, sphere_subset_closedBall x.2⟩ : sphere (0 : F) 1) = σ x by
    obtain ⟨φ, hφc, hφσ, ⟨z, hz⟩, hcomp, h, hh⟩ := H
    have hyφ : 0 < φ y := by
      have := mem_connectedComponentIn (F := (range σ)ᶜ) hy
      rwa [hcomp] at this
    have hcl : closure (connectedComponentIn (range σ)ᶜ y) = {w | 0 ≤ φ w} := by
      rw [hcomp]
      exact hb.closure_setOf_pos hEF hE hφc hφσ hyφ hz
    let h' := (Homeomorph.setCongr hcl).trans h
    have hh' (x : sphere (0 : E) 1) :
        (h'.symm ⟨x, sphere_subset_closedBall x.2⟩ : sphere (0 : F) 1) = σ x := by
      simpa [h', Homeomorph.setCongr] using hh x
    refine ⟨h', hh', fun w ↦ ⟨fun hw ↦ ?_, ?_⟩⟩
    · have := hh' ⟨h' w, mem_sphere_zero_iff_norm.2 hw⟩
      simp only [Subtype.coe_eta, Homeomorph.symm_apply_apply] at this
      exact ⟨_, this.symm⟩
    · rintro ⟨x, hx⟩
      have hw : w = h'.symm ⟨x, sphere_subset_closedBall x.2⟩ := Subtype.ext (by rw [hh', hx])
      rw [hw, Homeomorph.apply_symm_apply]
      exact norm_eq_of_mem_sphere x
  obtain ⟨φ, hφc, hφσ, hφ1, hφ1', h, hh⟩ := hb.exists_homeomorph_setOf_nonneg hEF hE
  have hφy : φ y ≠ 0 := fun h ↦ hy ((hφσ y).1 h)
  rcases hφy.lt_or_gt with hφy | hφy
  · -- On the negative side, use the reversed bicollar, whose positive side contains `y`.
    have hb' := hb.comp_prodMap_id_neg
    obtain ⟨ψ, hψc, hψσ, hψ1, hψ1', h', hh'⟩ := hb'.exists_homeomorph_setOf_nonneg hEF hE
    refine ⟨ψ, hψc, hψσ, ⟨_, (hψ1' x₀).trans_lt (by norm_num)⟩, ?_, h', hh'⟩
    have hneg := connectedComponentIn_compl_range_eq_setOf_neg hEF hb.continuous hb.injective
      hφc hφσ (z := b (x₀, 1)) (by rw [hφ1]; norm_num) hφy
    have hpos := connectedComponentIn_compl_range_eq_setOf_pos hEF hb'.continuous
      hb'.injective hψc hψσ (z := (b ∘ Prod.map id Neg.neg) (x₀, -1))
      (by rw [hψ1']; norm_num) (y := (b ∘ Prod.map id Neg.neg) (x₀, 1)) (by rw [hψ1]; norm_num)
    have hmem : (b ∘ Prod.map id Neg.neg) (x₀, 1) ∈ connectedComponentIn (range σ)ᶜ y := by
      rw [hneg]
      simp [hφ1']
    rw [connectedComponentIn_eq hmem, hpos]
  · refine ⟨φ, hφc, hφσ, ⟨_, (hφ1' x₀).trans_lt (by norm_num)⟩,
      connectedComponentIn_compl_range_eq_setOf_pos hEF hb.continuous hb.injective hφc hφσ
        (z := b (x₀, -1)) (by rw [hφ1']; norm_num) hφy, h, hh⟩

end TauCeti
