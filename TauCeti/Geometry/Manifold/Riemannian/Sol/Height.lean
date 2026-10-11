/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Sol.Curvature
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Curvature
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Order.IntermediateValue
-- The global coordinate calculation uses Sol's inherited model-space chart.
import all TauCeti.Geometry.Manifold.Riemannian.Sol.Basic

/-!
# Height rigidity of isometries of Sol

Every Riemannian isometry of Sol carries the height function to either `z + c` or
`-z + c`. The sign is constant over the whole space. In particular, isometries carry
horizontal planes to horizontal planes. This is the first constraint on arbitrary
isometries needed to identify the full isometry group from translations and the
eight dihedral isometries.

The Ricci tensor `-2 dz ⊗ dz` determines the height differential up to sign.
Continuity and connectedness fix that sign globally; equality of derivatives then
determines the height function up to its value at the identity.

## References

* P. Scott, *The geometries of 3-manifolds*, Bull. London Math. Soc. 15 (1983),
  401–487, Section 4, pp. 470–471 (Sol and its isometry group).
* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 7
  (invariance of Ricci curvature under isometries).
-/

public section

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff

namespace TauCeti.Sol

local notation "P" => ℝ × ℝ × ℝ
local notation "J" => 𝓘(ℝ, P)

-- Compute in the actual global coordinate diffeomorphism, without putting an
-- auxiliary normed-space structure on Sol.
private def coordinateMap (Φ : Isom J Sol) : P → P :=
  (toProd ∘ Φ) ∘ toProd.symm

private theorem height_derivative_mul (Φ : Isom J Sol) (p : P) (u v : P) :
    (fderiv ℝ (coordinateMap Φ) p u).2.2 * (fderiv ℝ (coordinateMap Φ) p v).2.2 =
      u.2.2 * v.2.2 := by
  simp only [coordinateMap]
  have h := Φ.ricciTensor_mfderiv (toProd.symm p)
    ((tangentSpaceCastModel J (toProd.symm p)).symm u)
    ((tangentSpaceCastModel J (toProd.symm p)).symm v)
  rw [ricciTensor_eq, ricciTensor_eq] at h
  rw [← fderiv_toProd_isometry_apply, ← fderiv_toProd_isometry_apply] at h
  simp only [ContinuousLinearEquiv.apply_symm_apply, Equiv.apply_symm_apply] at h
  linarith

private theorem height_derivative_sign (Φ : Isom J Sol) (p : P) :
    (fderiv ℝ (coordinateMap Φ) p (0, 0, 1)).2.2 = 1 ∨
      (fderiv ℝ (coordinateMap Φ) p (0, 0, 1)).2.2 = -1 := by
  have h := height_derivative_mul Φ p (0, 0, 1) (0, 0, 1)
  dsimp only at h
  have hsq : (fderiv ℝ (coordinateMap Φ) p (0, 0, 1)).2.2 ^ 2 = 1 := by nlinarith [h]
  rcases sq_eq_one_iff.mp hsq with h | h
  · exact Or.inl h
  · exact Or.inr h

private theorem height_derivative_sign_constant (Φ : Isom J Sol) (p : P) :
    (fderiv ℝ (coordinateMap Φ) p (0, 0, 1)).2.2 =
      (fderiv ℝ (coordinateMap Φ) 0 (0, 0, 1)).2.2 := by
  let a : P → ℝ := fun p => (fderiv ℝ (coordinateMap Φ) p (0, 0, 1)).2.2
  have ha : Continuous a :=
    (((contDiff_toProd_isometry Φ).continuous_fderiv_apply (by simp)).comp
      (continuous_id.prodMk continuous_const)).snd.snd
  have hz : ∀ p, a p ≠ 0 := fun p => by
    rcases height_derivative_sign Φ p with h | h <;> simp [a, h]
  rcases height_derivative_sign Φ p with hp | hp <;>
    rcases height_derivative_sign Φ 0 with h0 | h0
  · exact hp.trans h0.symm
  · obtain ⟨q, hq⟩ := intermediate_value_univ 0 p ha
      (by simp [a, hp, h0] : (0 : ℝ) ∈ Icc (a 0) (a p))
    exact (hz q hq).elim
  · obtain ⟨q, hq⟩ := intermediate_value_univ p 0 ha
      (by simp [a, hp, h0] : (0 : ℝ) ∈ Icc (a p) (a 0))
    exact (hz q hq).elim
  · exact hp.trans h0.symm

/-- The height component of the differential of a Sol isometry is `ε dz`, for one
sign `ε = ±1` independent of the base point. -/
theorem exists_mfderiv_height_eq (Φ : Isom J Sol) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ ∀ (p : Sol) (u : TangentSpace J p),
      (tangentSpaceCastModel J (Φ p) (mfderiv J J Φ p u)).2.2 =
        ε * (tangentSpaceCastModel J p u).2.2 := by
  refine ⟨(fderiv ℝ (coordinateMap Φ) 0 (0, 0, 1)).2.2, height_derivative_sign Φ 0, ?_⟩
  intro p u
  have h := height_derivative_mul Φ (toProd p) (tangentSpaceCastModel J p u) (0, 0, 1)
  rw [height_derivative_sign_constant Φ (toProd p)] at h
  simp only [coordinateMap] at h
  rw [fderiv_toProd_isometry_apply] at h
  have hs := height_derivative_sign Φ 0
  simp only [coordinateMap] at hs ⊢
  rcases hs with hs | hs <;> rw [hs] at h ⊢ <;> linarith

/-- Every Sol isometry either preserves or reverses height, up to the height of its
image of the identity. The same sign applies to every point. -/
theorem exists_height_eq (Φ : Isom J Sol) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ ∀ p : Sol, (Φ p).z = ε * p.z + (Φ 1).z := by
  obtain ⟨ε, hε, hd⟩ := exists_mfderiv_height_eq Φ
  have hfc : ContDiff ℝ ∞ (coordinateMap Φ) := contDiff_toProd_isometry Φ
  have hf : Differentiable ℝ (fun p : P => (coordinateMap Φ p).2.2) :=
    hfc.differentiable (by simp) |>.snd.snd
  have hg : Differentiable ℝ (fun p : P => ε * p.2.2 + (Φ 1).z) := by fun_prop
  have heq := eq_of_fderiv_eq hf hg (fun p => by
    apply ContinuousLinearMap.ext
    intro u
    have h := hd (toProd.symm p) ((tangentSpaceCastModel J (toProd.symm p)).symm u)
    rw [← fderiv_toProd_isometry_apply] at h
    simp only [ContinuousLinearEquiv.apply_symm_apply, Equiv.apply_symm_apply] at h
    rw [fderiv.snd (hfc.differentiable (by simp) p).snd,
      fderiv.snd (hfc.differentiable (by simp) p),
      fderiv_add_const, fderiv_const_mul (differentiable_snd.snd p) ε,
      fderiv.snd differentiable_snd.differentiableAt, fderiv_snd]
    exact h)
    (toProd 1) (by simp [coordinateMap])
  refine ⟨ε, hε, fun p => ?_⟩
  simpa only [coordinateMap, Function.comp_apply, Equiv.symm_apply_apply,
    snd_snd_toProd] using congrFun heq (toProd p)

end TauCeti.Sol
