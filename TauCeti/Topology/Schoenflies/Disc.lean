/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Schoenflies.Components
import Mathlib.Geometry.Manifold.Instances.Sphere
import TauCeti.Analysis.Normed.Module.Ball.Homeomorph
import TauCeti.Topology.CellularSet.InverseSet
import TauCeti.Topology.Circle.Schoenflies
import TauCeti.Topology.Schoenflies.Collapse
import TauCeti.Topology.Schoenflies.Hemisphere

/-!
# Brown's generalized Schoenflies theorem

Let `σ : Sᵐ⁻¹ → Sᵐ` be a map from the unit sphere of a real normed space `E` of dimension `m` into
the unit sphere of a real normed space of dimension `m + 1`, with a bicollar
`b : Sᵐ⁻¹ × ℝ → Sᵐ` (`TauCeti.IsBicollar`), and write `Σ` for the image of `σ`. By the
Jordan–Brouwer separation theorem `Sᵐ ∖ Σ` has exactly two connected components. This file proves
that the closure of each of them is a closed disc: it is homeomorphic to the closed unit ball of
`E` by a homeomorphism which inverts `σ` on `Σ` and carries exactly `Σ` onto the boundary sphere
(`TauCeti.IsBicollar.exists_homeomorph_closure_connectedComponentIn_compl_range`).

The bicollar cannot be dropped: the Alexander horned sphere in `S³` has a complementary domain whose
closure is not a disc, and it has no bicollar.

For `m ≥ 2` the proof is M. Brown's, after identifying `Sᵐ` with the unit sphere of a Euclidean
space (`TauCeti.sphereHomeomorphOfFinrankEq`). His collapse map `g : Sᵐ → Sᵐ`
(`TauCeti.IsBicollar.exists_collapse`) is the latitude map on the closed collar and sends the two
pieces of `Sᵐ` outside the open collar to the poles `p` and `-p`; these two fibres are its only
inverse sets, so both are cellular by Brown's theorem on two inverse sets
(`TauCeti.isCellularSet_preimage_singleton_of_injOn`). The function `φ = ⟪g ·, p⟫` vanishes exactly
on `Σ`, so the two complementary domains are `{φ > 0}` and `{φ < 0}` and their closures are the
preimages under `g` of the two closed hemispheres (`TauCeti.IsBicollar.closure_setOf_pos`).
Collapsing the cellular fibre over the pole identifies such a preimage with the closed hemisphere,
hence with a ball (`TauCeti.IsCellularSet.exists_homeomorph_preimage_hemisphere`). The other
complementary domain is treated in the same way with the collar coordinate reversed.

For `m = 1` the bicollar plays no role: `Σ` is a pair of points of the circle, and the two closed
arcs between them are the closures of its two complementary domains
(`TauCeti.exists_homeomorph_closure_connectedComponentIn_compl_range_of_finrank_eq_one`). For
`m = 0` the sphere `Σ` is empty, and each complementary domain is a single point of `S⁰`.

## Main results

* `TauCeti.IsBicollar.exists_homeomorph_closure_connectedComponentIn_compl_range`: **Brown's
  generalized Schoenflies theorem**: the closure of each complementary domain of a bicollared
  sphere `Σ` in `Sᵐ` is homeomorphic to the closed unit ball of `E`, with `Σ` going to the boundary
  sphere.

## References

* M. Brown, *A proof of the generalized Schoenflies theorem*, Bull. Amer. Math. Soc. 66 (1960),
  74–76, Theorem 5.
-/

public section

namespace TauCeti

open Function Metric Module Set
open scoped RealInnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]

namespace IsBicollar

section InnerProductSpace

variable [InnerProductSpace ℝ F] {σ : sphere (0 : E) 1 → sphere (0 : F) 1}
  {b : sphere (0 : E) 1 × ℝ → sphere (0 : F) 1}

variable (hb : IsBicollar σ b) (hEF : finrank ℝ F = finrank ℝ E + 1) (hE : 1 < finrank ℝ E)
include hb hEF hE

/-- **One side of Brown's theorem.** There is a continuous function `φ` on `Sᵐ` vanishing exactly
on the image of `σ` and equal to the collar coordinate `t` at `b (x, t)` for `t ∈ [-1, 1]`, such
that the closure of the complementary domain of each point where `φ` is positive is a disc, by a
homeomorphism inverting `σ` and carrying exactly the image of `σ` to the boundary sphere. Here
`φ = ⟪g ·, p⟫` for Brown's collapse map `g`. -/
private theorem exists_homeomorph_closure_of_pos :
    ∃ φ : sphere (0 : F) 1 → ℝ, Continuous φ ∧ (∀ y, φ y = 0 ↔ y ∈ range σ) ∧
      (∀ x, ∀ t ∈ Icc (-1 : ℝ) 1, φ (b (x, t)) = t) ∧
      ∀ y, 0 < φ y → ∃ h : closure (connectedComponentIn (range σ)ᶜ y) ≃ₜ closedBall (0 : E) 1,
        (∀ (z : closure (connectedComponentIn (range σ)ᶜ y)) x,
          (z : sphere (0 : F) 1) = σ x → (h z : E) = x) ∧
        ∀ z, (h z : E) ∈ sphere (0 : E) 1 ↔ (z : sphere (0 : F) 1) ∈ range σ := by
  have : FiniteDimensional ℝ E := .of_finrank_pos (by omega)
  have : FiniteDimensional ℝ F := .of_finrank_pos (by omega)
  have : Fact (finrank ℝ F = finrank ℝ E + 1) := ⟨hEF⟩
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  have : Nontrivial F := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  obtain ⟨x₀⟩ : Nonempty (sphere (0 : E) 1) :=
    (NormedSpace.sphere_nonempty.2 zero_le_one).to_subtype
  obtain ⟨p⟩ : Nonempty (sphere (0 : F) 1) :=
    (NormedSpace.sphere_nonempty.2 zero_le_one).to_subtype
  have hpp : ⟪(p : F), (p : F)⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere p, one_pow]
  have hfin : finrank ℝ E = finrank ℝ (ℝ ∙ (p : F))ᗮ :=
    (Submodule.finrank_orthogonal_span_singleton (ne_zero_of_mem_unit_sphere p)).symm
  set e := sphereHomeomorphOfFinrankEq hfin
  set B := closedBallHomeomorphOfFinrankEq hfin
  obtain ⟨g, hgs, hlat, -, hgσ, hinj⟩ := hb.exists_collapse p e hEF hE
  set φ : sphere (0 : F) 1 → ℝ := fun y ↦ ⟪(g y : F), (p : F)⟫
  have hφ : Continuous φ := by fun_prop
  have hφb (x : sphere (0 : E) 1) (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) : φ (b (x, t)) = t := by
    simp [φ, hlat x t ht, inner_add_left, real_inner_smul_left,
      Submodule.mem_orthogonal_singleton_iff_inner_left.1 (e x : (ℝ ∙ (p : F))ᗮ).2]
  refine ⟨φ, hφ, hgσ, hφb, fun y hy ↦ ?_⟩
  -- The closure of the domain of `y` is the preimage of the closed hemisphere about `p`.
  have hz : φ (b (x₀, -1)) < 0 := by
    rw [hφb x₀ (-1) (by norm_num)]
    norm_num
  have hcl : closure (connectedComponentIn (range σ)ᶜ y) =
      g ⁻¹' {v | 0 ≤ ⟪(v : F), (p : F)⟫} := by
    rw [connectedComponentIn_compl_range_eq_setOf_pos hEF hb.continuous hb.injective hφ hgσ hz hy,
      hb.closure_setOf_pos hEF hE hφ hgσ hy hz]
    rfl
  -- The fibre of `g` over `p` is cellular, so that preimage is a disc.
  have hA : IsCellularSet (EuclideanSpace ℝ (Fin (finrank ℝ E))) (g ⁻¹' {p}) :=
    isCellularSet_preimage_singleton_of_injOn (by simp; omega) (by simp [hEF]) g.continuous hgs
      (p := -p) (ne_neg_of_mem_unit_sphere ℝ p).symm (by rwa [pair_comm])
  obtain ⟨h₁, hh₁, hh₁'⟩ := hA.exists_homeomorph_preimage_hemisphere g.continuous hgs
    fun x x' hx hxx' ↦ by
      by_cases hxp : g x = p
      · exact .inr hxp
      have hn {w : sphere (0 : F) 1} (hw : 0 ≤ ⟪(g w : F), (p : F)⟫) (hwp : g w ≠ p) :
          w ∈ (g ⁻¹' {p, -p})ᶜ := by
        simp only [mem_compl_iff, mem_preimage, mem_insert_iff, mem_singleton_iff, not_or]
        refine ⟨hwp, fun h ↦ ?_⟩
        rw [h, coe_neg_sphere, inner_neg_left, hpp] at hw
        norm_num at hw
      exact .inl (hinj (hn hx hxp) (hn (hxx' ▸ hx) (hxx' ▸ hxp)) hxx')
  refine ⟨(Homeomorph.setCongr hcl).trans (h₁.trans B.symm), fun z x hzx ↦ ?_, fun z ↦ ?_⟩
  all_goals
    -- `Homeomorph.setCongr` does not move points; Mathlib has no simp lemma for its coercion.
    have hz : ((Homeomorph.setCongr hcl z : g ⁻¹' {v | 0 ≤ ⟪(v : F), (p : F)⟫}) :
      sphere (0 : F) 1) = z := rfl
  · -- On the image of `σ`, `h₁` is `g`, which is `e` read through `σ`.
    have hgx : ((h₁ (Homeomorph.setCongr hcl z) : (ℝ ∙ (p : F))ᗮ) : F) = (e x : F) := by
      rw [hh₁ _ ((hgσ _).2 ⟨x, (hz.trans hzx).symm⟩), hz, hzx, ← hb.apply_zero,
        hlat x 0 (by norm_num)]
      simp
    have hBx : h₁ (Homeomorph.setCongr hcl z) = B ⟨x, sphere_subset_closedBall x.2⟩ :=
      Subtype.ext (Subtype.ext (by simpa [B, e] using hgx))
    simp [hBx]
  · -- `B` preserves the unit sphere, and `h₁` sends exactly the image of `σ` to it.
    have key : ‖(h₁ (Homeomorph.setCongr hcl z) : (ℝ ∙ (p : F))ᗮ)‖ = 1 ↔
        (z : sphere (0 : F) 1) ∈ range σ := (hh₁' _).trans (hz ▸ hgσ _)
    rw [mem_sphere_zero_iff_norm, ← key, Homeomorph.trans_apply, Homeomorph.trans_apply]
    obtain ⟨u, hu⟩ := B.surjective (h₁ (Homeomorph.setCongr hcl z))
    simp only [← hu, B, Homeomorph.symm_apply_apply, coe_closedBallHomeomorphOfFinrankEq_apply,
      ContinuousLinearEquiv.norm_unitBallHomeomorph_eq_one_iff]

/-- Brown's generalized Schoenflies theorem in dimension `m ≥ 2`. -/
private theorem exists_homeomorph_closure_connectedComponentIn_compl_range_of_one_lt
    {y : sphere (0 : F) 1} (hy : y ∉ range σ) :
    ∃ h : closure (connectedComponentIn (range σ)ᶜ y) ≃ₜ closedBall (0 : E) 1,
      (∀ (z : closure (connectedComponentIn (range σ)ᶜ y)) x,
        (z : sphere (0 : F) 1) = σ x → (h z : E) = x) ∧
      ∀ z, (h z : E) ∈ sphere (0 : E) 1 ↔ (z : sphere (0 : F) 1) ∈ range σ := by
  have : FiniteDimensional ℝ E := .of_finrank_pos (by omega)
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  obtain ⟨x₀⟩ : Nonempty (sphere (0 : E) 1) :=
    (NormedSpace.sphere_nonempty.2 zero_le_one).to_subtype
  have hb' := hb.comp_prodMap_id_neg
  obtain ⟨φ, hφ, hφσ, hφb, hpos⟩ := exists_homeomorph_closure_of_pos hb hEF hE
  obtain ⟨φ', hφ', hφ'σ, hφ'b, hpos'⟩ := exists_homeomorph_closure_of_pos hb' hEF hE
  have hy0 : φ y ≠ 0 := fun h ↦ hy ((hφσ y).1 h)
  rcases hy0.lt_or_gt with hy0 | hy0
  · -- `y` lies on the negative side of `b`, which is the positive side of the reversed bicollar.
    refine hpos' y ?_
    have hcc : connectedComponentIn (range σ)ᶜ y = {w | φ w < 0} :=
      connectedComponentIn_compl_range_eq_setOf_neg hEF hb.continuous hb.injective hφ hφσ
        (z := b (x₀, 1 / 2)) (by rw [hφb _ _ (by norm_num)]; norm_num) hy0
    have hmem : (b ∘ Prod.map id Neg.neg) (x₀, 1 / 2) ∈ connectedComponentIn (range σ)ᶜ y := by
      rw [hcc, mem_ofPred_eq, comp_apply, Prod.map_apply, id_eq, hφb _ _ (by norm_num)]
      norm_num
    have hcc' := connectedComponentIn_compl_range_eq_setOf_pos hEF hb'.continuous hb'.injective
      hφ' hφ'σ (z := (b ∘ Prod.map id Neg.neg) (x₀, -(1 / 2)))
      (by rw [hφ'b _ _ (by norm_num)]; norm_num) (y := (b ∘ Prod.map id Neg.neg) (x₀, 1 / 2))
      (by rw [hφ'b _ _ (by norm_num)]; norm_num)
    rw [← connectedComponentIn_eq hmem] at hcc'
    simpa using hcc'.subset (mem_connectedComponentIn hy)
  · exact hpos y hy0

end InnerProductSpace

variable [NormedSpace ℝ F] {σ : sphere (0 : E) 1 → sphere (0 : F) 1}
  {b : sphere (0 : E) 1 × ℝ → sphere (0 : F) 1}

/-- **Brown's generalized Schoenflies theorem.** Let `σ` be a map from the unit sphere `Sᵐ⁻¹` of a
real normed space `E` of dimension `m` into the unit sphere `Sᵐ` of a real normed space of dimension
`m + 1`, with a bicollar `b`. Then the closure of the connected component of each point `y ∉ Σ` in
the complement of the image `Σ` of `σ` is homeomorphic to the closed unit ball of `E`, by a
homeomorphism which inverts `σ` on `Σ` and sends exactly the points of `Σ` to the boundary sphere.
For `m = 1` the bicollar is not needed: see
`TauCeti.exists_homeomorph_closure_connectedComponentIn_compl_range_of_finrank_eq_one`. -/
theorem exists_homeomorph_closure_connectedComponentIn_compl_range
    (hb : IsBicollar σ b) (hEF : finrank ℝ F = finrank ℝ E + 1)
    {y : sphere (0 : F) 1} (hy : y ∉ range σ) :
    ∃ h : closure (connectedComponentIn (range σ)ᶜ y) ≃ₜ closedBall (0 : E) 1,
      (∀ (z : closure (connectedComponentIn (range σ)ᶜ y)) x,
        (z : sphere (0 : F) 1) = σ x → (h z : E) = x) ∧
      ∀ z, (h z : E) ∈ sphere (0 : E) 1 ↔ (z : sphere (0 : F) 1) ∈ range σ := by
  have : FiniteDimensional ℝ E := finiteDimensional_of_injective_sphere hEF hb.injective
  obtain hE | hE | hE : finrank ℝ E = 0 ∨ finrank ℝ E = 1 ∨ 1 < finrank ℝ E := by omega
  · -- `Sᵐ⁻¹` is empty, and `y` is alone in its component of the discrete sphere `S⁰`.
    have : Subsingleton E := finrank_zero_iff.1 hE
    have := discreteTopology_sphere_of_finrank_eq_one (hEF.trans (by rw [hE])) (0 : F) 1
    have hcl : closure (connectedComponentIn (range σ)ᶜ y) = {y} := by
      rw [range_eq_empty, compl_empty, connectedComponentIn_univ,
        connectedComponent_eq_singleton, closure_singleton]
    refine ⟨(Homeomorph.setCongr hcl).trans ((Homeomorph.homeomorphOfUnique _ _).trans
      (Homeomorph.setCongr (closedBall_eq_singleton_of_subsingleton zero_le_one).symm)),
      fun _ x _ ↦ isEmptyElim x, fun z ↦ ?_⟩
    simp [sphere_eq_empty_of_subsingleton]
  · exact exists_homeomorph_closure_connectedComponentIn_compl_range_of_finrank_eq_one
      hEF hE hb.injective hy
  · -- Transport `Sᵐ` to the unit sphere of a Euclidean space.
    have : FiniteDimensional ℝ F := .of_finrank_pos (by omega)
    let G := EuclideanSpace ℝ (Fin (finrank ℝ F))
    let e : sphere (0 : F) 1 ≃ₜ sphere (0 : G) 1 := sphereHomeomorphOfFinrankEq (by simp [G])
    have hy' : e y ∉ range (e ∘ σ) := by simpa [range_comp] using hy
    obtain ⟨h, hσ, hS⟩ := (hb.isOpenEmbedding_comp e.isOpenEmbedding)
      |>.exists_homeomorph_closure_connectedComponentIn_compl_range_of_one_lt
        (by simp [G, hEF]) hE hy'
    have hcl : e '' closure (connectedComponentIn (range σ)ᶜ y) =
        closure (connectedComponentIn (range (e ∘ σ))ᶜ (e y)) := by
      rw [e.image_closure, e.image_connectedComponentIn hy, e.image_compl, range_comp]
    let Ψ : closure (connectedComponentIn (range σ)ᶜ y) ≃ₜ
        closure (connectedComponentIn (range (e ∘ σ))ᶜ (e y)) :=
      e.subtype fun w ↦ by rw [← hcl, e.injective.mem_set_image]
    refine ⟨Ψ.trans h, fun z x hzx ↦ hσ (Ψ z) x ?_, fun z ↦ (hS (Ψ z)).trans ?_⟩
    · rw [Homeomorph.subtype_apply_coe, hzx, comp_apply]
    · rw [Homeomorph.subtype_apply_coe, range_comp, e.injective.mem_set_image]

end IsBicollar

end TauCeti
