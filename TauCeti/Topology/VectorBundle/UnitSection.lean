/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.VectorBundle.Riemannian
public import TauCeti.Topology.VectorBundle.Smul
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# A unit section trivializes a real line bundle

Let `E → B` be a real vector bundle of rank one with a continuous fibrewise inner product
(`IsContinuousRiemannianBundle`), and `u` a continuous section of unit vectors. Every vector `v`
over `b` is then `⟪v, u b⟫ • u b`, so

`TauCeti.VectorBundle.unitSectionHomeomorph : B × ℝ ≃ₜ TotalSpace F E`, `(b, t) ↦ t • u b`,

is a homeomorphism, with inverse `v ↦ (b, ⟪v, u b⟫)`. It sends `B × {t}` to the vectors
`t • u b` of norm `|t|` (`TauCeti.VectorBundle.norm_snd_unitSectionHomeomorph`), so it carries
`B × (-ε, ε)` onto the vectors of norm less than `ε`
(`TauCeti.VectorBundle.unitSectionHomeomorph_image_prod_Ioo`).

Continuity of the map is that of fibrewise scalar multiplication
(`TauCeti.VectorBundle.continuous_smul`), and continuity of the inverse is that of the inner
product of two continuous maps into the bundle (`Continuous.inner_bundle`).
-/

public section

open Bundle Module Set

namespace TauCeti.VectorBundle

variable {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ b, NormedAddCommGroup (E b)] [∀ b, InnerProductSpace ℝ (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E] [IsContinuousRiemannianBundle F E]
  {u : ∀ b, E b}

omit [IsContinuousRiemannianBundle F E] in
variable (F) in
/-- In a real vector bundle of rank one, every vector is its inner product with a unit vector of
the same fibre times that unit vector. -/
theorem inner_smul_eq_of_finrank_eq_one (hF : finrank ℝ F = 1) {b : B} {w : E b}
    (hw : ‖w‖ = 1) (v : E b) : (inner ℝ v w : ℝ) • w = v := by
  have hfin : finrank ℝ (E b) = 1 :=
    ((trivializationAt F E b).linearEquivAt ℝ b
      (mem_baseSet_trivializationAt F E b)).finrank_eq.trans hF
  have hw0 : w ≠ 0 := by
    rintro rfl
    simp at hw
  obtain ⟨c, rfl⟩ := (finrank_eq_one_iff_of_ne_zero' w hw0).mp hfin v
  rw [real_inner_smul_left, real_inner_self_eq_norm_sq, hw, one_pow, mul_one]

variable (F E) in
/-- **A unit section trivializes a real line bundle.** For a continuous section `u` of unit
vectors of a real vector bundle of rank one with a continuous fibrewise inner product, the map
`(b, t) ↦ t • u b` is a homeomorphism `B × ℝ ≃ₜ TotalSpace F E`, with inverse
`v ↦ (b, ⟪v, u b⟫)`. -/
noncomputable def unitSectionHomeomorph (hF : finrank ℝ F = 1)
    (hu : Continuous fun b ↦ TotalSpace.mk' F b (u b)) (hu1 : ∀ b, ‖u b‖ = 1) :
    B × ℝ ≃ₜ TotalSpace F E where
  toFun p := TotalSpace.mk' F p.1 (p.2 • u p.1)
  invFun p := (p.proj, inner ℝ p.snd (u p.proj))
  left_inv p := by
    simp only [real_inner_smul_left, real_inner_self_eq_norm_sq, hu1, one_pow, mul_one]
  right_inv p := by
    simp only [inner_smul_eq_of_finrank_eq_one F hF (hu1 p.proj)]
  continuous_toFun :=
    (continuous_smul ℝ F E).comp (continuous_snd.prodMk (hu.comp continuous_fst))
  continuous_invFun :=
    (FiberBundle.continuous_proj F E).prodMk
      (Continuous.inner_bundle (b := TotalSpace.proj) (v := fun p ↦ p.snd)
        (w := fun p ↦ u p.proj) continuous_id (hu.comp (FiberBundle.continuous_proj F E)))

variable (hF : finrank ℝ F = 1) (hu : Continuous fun b ↦ TotalSpace.mk' F b (u b))
  (hu1 : ∀ b, ‖u b‖ = 1)

@[simp]
theorem unitSectionHomeomorph_apply (p : B × ℝ) :
    unitSectionHomeomorph F E hF hu hu1 p = TotalSpace.mk' F p.1 (p.2 • u p.1) :=
  (rfl)

@[simp]
theorem unitSectionHomeomorph_symm_apply (p : TotalSpace F E) :
    (unitSectionHomeomorph F E hF hu hu1).symm p = (p.proj, inner ℝ p.snd (u p.proj)) :=
  (rfl)

/-- The vector `t • u b` has norm `|t|`. -/
theorem norm_snd_unitSectionHomeomorph (p : B × ℝ) :
    ‖(unitSectionHomeomorph F E hF hu hu1 p).snd‖ = |p.2| := by
  rw [unitSectionHomeomorph_apply]
  exact (norm_smul p.2 (u p.1)).trans (by rw [hu1, mul_one, Real.norm_eq_abs])

/-- The unit section trivialization carries `B × (-ε, ε)` onto the vectors of norm less than `ε`.
-/
theorem unitSectionHomeomorph_image_prod_Ioo (ε : ℝ) :
    unitSectionHomeomorph F E hF hu hu1 '' (univ ×ˢ Ioo (-ε) ε) = {p | ‖p.snd‖ < ε} := by
  ext p
  obtain ⟨q, rfl⟩ := (unitSectionHomeomorph F E hF hu hu1).surjective p
  simp only [(unitSectionHomeomorph F E hF hu hu1).injective.mem_set_image, mem_ofPred_eq,
    norm_snd_unitSectionHomeomorph, mem_prod, mem_univ, true_and, mem_Ioo, abs_lt]

end TauCeti.VectorBundle
