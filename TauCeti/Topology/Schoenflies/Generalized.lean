/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import TauCeti.Geometry.Manifold.LocallyFlat.Bicollar
import Mathlib.Geometry.Manifold.Instances.Sphere
import TauCeti.Analysis.Normed.Module.Ball.Homeomorph
import TauCeti.Topology.CellularSet.TwoInverseSets
import TauCeti.Topology.Schoenflies.Collapse
import TauCeti.Topology.Schoenflies.Components
import TauCeti.Topology.Schoenflies.Hemisphere

/-!
# Brown's generalized Schoenflies theorem

Let `σ : Sᵐ⁻¹ → Sᵐ` be a map of the unit sphere of a real normed space `E` of dimension `m ≥ 2`
into the unit sphere of a real inner product space of dimension `m + 1`, with a bicollar
`b : Sᵐ⁻¹ × ℝ → Sᵐ` (`TauCeti.IsBicollar`). By the Jordan–Brouwer separation theorem
(`TauCeti.natCard_connectedComponents_sphere_compl_range_eq_two`) the complement of the image `Σ`
of `σ` has exactly two connected components. **Brown's generalized Schoenflies theorem**
(`TauCeti.IsBicollar.exists_homeomorph_closure_connectedComponentIn_compl_range`) says that the
closure of each of them is homeomorphic to the closed unit ball `Dᵐ` of `E`, by a homeomorphism
which inverts `σ` on `Σ` and carries exactly `Σ` onto the boundary sphere of `Dᵐ`.

The proof is Brown's Theorem 5. Fix a pole `p` and collapse the two pieces of `Sᵐ` outside the open
collar onto `p` and `-p` by a map `g` which is the latitude map on the collar
(`TauCeti.IsBicollar.exists_collapse`). Its only inverse sets are the two collapsed pieces, which
are therefore cellular (`TauCeti.isCellularSet_preimage_singleton_of_injOn`). The closure of the
component on the positive side of the collar is the preimage under `g` of the closed hemisphere
around `p` (`TauCeti.IsBicollar.closure_setOf_pos`), and since `g⁻¹(p)` is cellular this preimage
is a closed disc (`TauCeti.IsCellularSet.exists_homeomorph_preimage_hemisphere`). The component on
the negative side is the positive side of the reversed bicollar.

The statement is false without the bicollar: one complementary domain of the Alexander horned
sphere in `S³` is not simply connected, so its closure is not a ball. The case `m = 1`, where
`Sᵐ⁻¹` is two points and no bicollar is needed, is separate.

## Main results

* `TauCeti.IsBicollar.exists_homeomorph_closure_connectedComponentIn_compl_range`: **Brown's
  generalized Schoenflies theorem** for `m ≥ 2`.

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

/-- **The closed positive side of a bicollared sphere is a disc.** For a bicollar `b` of `σ`, there
is a continuous function `φ` on `Sᵐ` vanishing exactly on the image of `σ`, positive at the points
`b (x, 1 / 2)` and negative at the points `b (x, -1 / 2)`, whose nonnegative set is homeomorphic to
the closed unit ball of `E` by a homeomorphism inverting `σ` and carrying exactly the image of `σ`
onto the boundary sphere. The function is the height `⟪g y, p⟫` of Brown's collapse `g`. -/
private theorem exists_homeomorph_setOf_nonneg (hb : IsBicollar σ b)
    (hEF : finrank ℝ F = finrank ℝ E + 1) (hE : 1 < finrank ℝ E) :
    ∃ φ : sphere (0 : F) 1 → ℝ, Continuous φ ∧ (∀ y, φ y = 0 ↔ y ∈ range σ) ∧
      (∀ x, 0 < φ (b (x, 1 / 2))) ∧ (∀ x, φ (b (x, -(1 / 2))) < 0) ∧
      ∃ h : {y | 0 ≤ φ y} ≃ₜ closedBall (0 : E) 1,
        (∀ (z : {y | 0 ≤ φ y}) x, (z : sphere (0 : F) 1) = σ x → (h z : E) = x) ∧
        ∀ z, (h z : E) ∈ sphere (0 : E) 1 ↔ (z : sphere (0 : F) 1) ∈ range σ := by
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_pos (by omega)
  have : FiniteDimensional ℝ F := Module.finite_of_finrank_pos (by omega)
  have : Nontrivial F := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  have : Fact (finrank ℝ F = finrank ℝ E + 1) := ⟨hEF⟩
  obtain ⟨p⟩ : Nonempty (sphere (0 : F) 1) :=
    (NormedSpace.sphere_nonempty.2 zero_le_one).to_subtype
  have hdim : finrank ℝ E = finrank ℝ (ℝ ∙ (p : F))ᗮ :=
    (Submodule.finrank_orthogonal_span_singleton (ne_zero_of_mem_unit_sphere p)).symm
  set e := sphereHomeomorphOfFinrankEq hdim
  set T := closedBallHomeomorphOfFinrankEq hdim
  obtain ⟨g, hgs, hgb, -, hgσ, hginj⟩ := hb.exists_collapse p e hEF hE
  have hpp : ⟪(p : F), (p : F)⟫ = 1 := by simp
  have hep (x : sphere (0 : E) 1) : ⟪((e x : (ℝ ∙ (p : F))ᗮ) : F), (p : F)⟫ = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_left.1 (e x : (ℝ ∙ (p : F))ᗮ).2
  -- The height of `g` on the collar is the collar parameter.
  have hφb (x : sphere (0 : E) 1) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
      ⟪(g (b (x, t)) : F), (p : F)⟫ = t := by
    rw [hgb x t ht, inner_add_left, real_inner_smul_left, real_inner_smul_left, hep, hpp]
    ring
  -- `g` sends the image of `σ` to the equator by `e`.
  have hgσ' (x : sphere (0 : E) 1) : (g (σ x) : F) = e x := by
    rw [← hb.apply_zero, hgb x 0 ⟨by norm_num, by norm_num⟩]
    simp
  -- The fibre of `g` over `p` is cellular.
  have hcell : IsCellularSet (EuclideanSpace ℝ (Fin (finrank ℝ E))) (g ⁻¹' {p}) :=
    isCellularSet_preimage_singleton_of_injOn (by rw [finrank_euclideanSpace_fin]; omega)
      (by rw [finrank_euclideanSpace_fin, hEF]) g.continuous hgs (a := -p) (c := p)
      (fun h ↦ by
        have := congrArg (fun v : sphere (0 : F) 1 ↦ ⟪(v : F), (p : F)⟫) h
        rw [coe_neg_sphere, inner_neg_left, hpp] at this
        norm_num at this) (by rwa [pair_comm])
  obtain ⟨h₀, h₀g, h₀S⟩ := hcell.exists_homeomorph_preimage_hemisphere g.continuous hgs
    fun x y hx hxy ↦ by
      by_cases hxp : g x ∈ ({p, -p} : Set (sphere (0 : F) 1))
      · rcases hxp with hxp | hxp
        · exact .inr hxp
        · rw [mem_singleton_iff.1 hxp, coe_neg_sphere, inner_neg_left, hpp] at hx
          norm_num at hx
      · exact .inl (hginj hxp (by rwa [mem_compl_iff, mem_preimage, ← hxy]) hxy)
  refine ⟨fun y ↦ ⟪(g y : F), (p : F)⟫, by fun_prop, hgσ, fun x ↦ ?_, fun x ↦ ?_,
    h₀.trans T.symm, fun z x hz ↦ ?_, fun z ↦ ?_⟩
  -- The goals apply the function `fun y ↦ ⟪g y, p⟫` to points; reduce these beta-redexes.
  all_goals beta_reduce
  · rw [hφb x ⟨by norm_num, by norm_num⟩]
    norm_num
  · rw [hφb x ⟨by norm_num, by norm_num⟩]
    norm_num
  · -- `h₀` agrees with `g` over the equator, where `g` is `e`, the restriction of `T`.
    have hx : (⟨x, sphere_subset_closedBall x.2⟩ : closedBall (0 : E) 1) = T.symm (h₀ z) := by
      refine T.eq_symm_apply.2 (Subtype.ext (Subtype.ext ?_))
      rw [h₀g z ((hgσ _).2 (hz ▸ mem_range_self x)), hz, hgσ' x,
        coe_closedBallHomeomorphOfFinrankEq_apply, ← coe_sphereHomeomorphOfFinrankEq_apply]
    exact congrArg Subtype.val hx.symm
  · obtain ⟨w, hw⟩ := T.surjective (h₀ z)
    calc (T.symm (h₀ z) : E) ∈ sphere (0 : E) 1 ↔ ‖(w : E)‖ = 1 := by
          rw [← hw, T.symm_apply_apply, mem_sphere_zero_iff_norm]
      _ ↔ ‖(T w : (ℝ ∙ (p : F))ᗮ)‖ = 1 := by
          rw [coe_closedBallHomeomorphOfFinrankEq_apply,
            (ContinuousLinearEquiv.ofFinrankEq hdim).norm_unitBallHomeomorph_eq_one_iff]
      _ ↔ (z : sphere (0 : F) 1) ∈ range σ := by
          rw [hw, h₀S z]
          exact hgσ z

/-- **Brown's generalized Schoenflies theorem.** Let `σ` be a map from the unit sphere `Sᵐ⁻¹` of a
real normed space `E` of dimension `m ≥ 2` into the unit sphere `Sᵐ` of a real inner product space
of dimension `m + 1`, with a bicollar `b`, and write `Σ` for its image. The closure of each
connected component of `Sᵐ ∖ Σ` is homeomorphic to the closed unit ball `Dᵐ` of `E`, by a
homeomorphism `h` which inverts `σ` on `Σ` and carries exactly `Σ` onto the boundary sphere of
`Dᵐ`. -/
theorem exists_homeomorph_closure_connectedComponentIn_compl_range (hb : IsBicollar σ b)
    (hEF : finrank ℝ F = finrank ℝ E + 1) (hE : 1 < finrank ℝ E) {y : sphere (0 : F) 1}
    (hy : y ∉ range σ) :
    ∃ h : closure (connectedComponentIn (range σ)ᶜ y) ≃ₜ closedBall (0 : E) 1,
      (∀ (z : closure (connectedComponentIn (range σ)ᶜ y)) x,
        (z : sphere (0 : F) 1) = σ x → (h z : E) = x) ∧
      ∀ z, (h z : E) ∈ sphere (0 : E) 1 ↔ (z : sphere (0 : F) 1) ∈ range σ := by
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_pos (by omega)
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  obtain ⟨x₀⟩ : Nonempty (sphere (0 : E) 1) :=
    (NormedSpace.sphere_nonempty.2 zero_le_one).to_subtype
  -- It suffices that the component of `y` is that of the positive side of some bicollar.
  suffices H : ∃ b' : sphere (0 : E) 1 × ℝ → sphere (0 : F) 1, IsBicollar σ b' ∧
      connectedComponentIn (range σ)ᶜ y = connectedComponentIn (range σ)ᶜ (b' (x₀, 1 / 2)) by
    obtain ⟨b', hb', hyb⟩ := H
    obtain ⟨φ, hφ, hφσ, hpos, hneg, h, hhσ, hhS⟩ := hb'.exists_homeomorph_setOf_nonneg hEF hE
    have hcl : closure (connectedComponentIn (range σ)ᶜ y) = {w | 0 ≤ φ w} := by
      rw [hyb, connectedComponentIn_compl_range_eq_setOf_pos hEF hb'.continuous hb'.injective hφ
        hφσ (hneg x₀) (hpos x₀), hb'.closure_setOf_pos hEF hE hφ hφσ (hpos x₀) (hneg x₀)]
    exact ⟨(Homeomorph.setCongr hcl).trans h, fun z x hz ↦ hhσ _ x hz, fun z ↦ hhS _⟩
  obtain ⟨φ, hφ, hφσ, hpos, hneg, -⟩ := hb.exists_homeomorph_setOf_nonneg hEF hE
  rcases lt_or_gt_of_ne fun h ↦ hy ((hφσ y).1 h) with hφy | hφy
  · -- On the negative side, use the reversed bicollar.
    refine ⟨b ∘ Prod.map id Neg.neg, hb.comp_prodMap_id_neg, ?_⟩
    rw [connectedComponentIn_compl_range_eq_setOf_neg hEF hb.continuous hb.injective hφ hφσ
      (hpos x₀) hφy]
    exact (connectedComponentIn_compl_range_eq_setOf_neg hEF hb.continuous hb.injective hφ hφσ
      (hpos x₀) (hneg x₀)).symm
  · refine ⟨b, hb, ?_⟩
    rw [connectedComponentIn_compl_range_eq_setOf_pos hEF hb.continuous hb.injective hφ hφσ
      (hneg x₀) hφy]
    exact (connectedComponentIn_compl_range_eq_setOf_pos hEF hb.continuous hb.injective hφ hφσ
      (hneg x₀) (hpos x₀)).symm

end IsBicollar

end TauCeti
