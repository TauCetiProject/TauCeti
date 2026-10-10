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

private theorem contDiff_isometry (Φ : Isom J Sol) : ContDiff ℝ ∞ (coordinateMap Φ) := by
  simpa only [coordinateMap, Diffeomorph.coe_trans, coe_toProdDiffeomorph,
    coe_toProdDiffeomorph_symm, RiemannianIsometry.coe_toDiffeomorph] using
    (toProdDiffeomorph.symm.trans (Φ.toDiffeomorph.trans toProdDiffeomorph)).contMDiff.contDiff

private theorem coordinate_derivative (Φ : Isom J Sol) (p : Sol)
    (u : TangentSpace J p) :
    fderiv ℝ (coordinateMap Φ) (toProd p) (tangentSpaceCastModel J p u) =
      tangentSpaceCastModel J (Φ p) (mfderiv J J Φ p u) := by
  have hf : MDifferentiable J J toProd := by
    simpa only [coe_toProdDiffeomorph] using toProdDiffeomorph.mdifferentiable (by simp)
  have hg : MDifferentiable J J toProd.symm := by
    simpa only [coe_toProdDiffeomorph_symm] using toProdDiffeomorph.symm.mdifferentiable (by simp)
  have hm := ((contDiff_isometry Φ).differentiable (by simp)
    (toProd p)).hasFDerivAt.hasMFDerivAt.mfderiv
  rw [← hm]
  -- The derivative between coordinate spaces has canonical tangent identifications.
  -- Insert them before rewriting, so no rewrite relies on their underlying types.
  change tangentSpaceCastModel J (coordinateMap Φ (toProd p))
    (mfderiv J J (coordinateMap Φ) (toProd p)
      ((tangentSpaceCastModel J (toProd p)).symm (tangentSpaceCastModel J p u))) = _
  unfold coordinateMap
  -- Apply the chain rule to tangent vectors before simplifying the intermediate
  -- base points; this keeps the dependent tangent-space types aligned.
  rw [mfderiv_comp_apply (toProd p) (hf.comp Φ.mdifferentiable _) (hg _),
    mfderiv_comp_apply (toProd.symm (toProd p)) (hf _) (Φ.mdifferentiableAt _)]
  rw [mfderiv_toProd_apply]
  -- The outer coordinate-space cast is the identity on its model vector.
  change tangentSpaceCastModel J (Φ p)
    (mfderiv J J Φ p
      (mfderiv J J toProd.symm (toProd p)
        ((tangentSpaceCastModel J (toProd p)).symm (tangentSpaceCastModel J p u)))) = _
  have hu : mfderiv J J toProd.symm (toProd p)
      ((tangentSpaceCastModel J (toProd p)).symm (tangentSpaceCastModel J p u)) = u :=
    by
      have h := toProdDiffeomorph.mfderiv_symm_apply_mfderiv_apply (by simp) p u
      rw [coe_toProdDiffeomorph_symm, coe_toProdDiffeomorph, mfderiv_toProd_apply] at h
      exact h
  exact congrArg (fun v => tangentSpaceCastModel J (Φ p) (mfderiv J J Φ p v)) hu

private theorem height_derivative_mul (Φ : Isom J Sol) (p : P) (u v : P) :
    (fderiv ℝ (coordinateMap Φ) p u).2.2 * (fderiv ℝ (coordinateMap Φ) p v).2.2 =
      u.2.2 * v.2.2 := by
  have h := Φ.ricciTensor_mfderiv (toProd.symm p)
    ((tangentSpaceCastModel J (toProd.symm p)).symm u)
    ((tangentSpaceCastModel J (toProd.symm p)).symm v)
  rw [ricciTensor_eq, ricciTensor_eq] at h
  rw [← coordinate_derivative, ← coordinate_derivative] at h
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
    (((contDiff_isometry Φ).continuous_fderiv_apply (by simp)).comp
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
  rw [height_derivative_sign_constant Φ (toProd p), coordinate_derivative] at h
  have hs := height_derivative_sign Φ 0
  dsimp only at h
  rcases hs with hs | hs <;> rw [hs] at h ⊢ <;> linarith

/-- Every Sol isometry either preserves or reverses height, up to the height of its
image of the identity. The same sign applies to every point. -/
theorem exists_height_eq (Φ : Isom J Sol) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ ∀ p : Sol, (Φ p).z = ε * p.z + (Φ 1).z := by
  obtain ⟨ε, hε, hd⟩ := exists_mfderiv_height_eq Φ
  have hf : Differentiable ℝ (fun p : P => (coordinateMap Φ p).2.2) :=
    (contDiff_isometry Φ).differentiable (by simp) |>.snd.snd
  have hg : Differentiable ℝ (fun p : P => ε * p.2.2 + (Φ 1).z) := by fun_prop
  have heq := eq_of_fderiv_eq hf hg (fun p => by
    apply ContinuousLinearMap.ext
    intro u
    have h := hd (toProd.symm p) ((tangentSpaceCastModel J (toProd.symm p)).symm u)
    rw [← coordinate_derivative] at h
    simp only [ContinuousLinearEquiv.apply_symm_apply, Equiv.apply_symm_apply] at h
    rw [fderiv.snd ((contDiff_isometry Φ).differentiable (by simp) p).snd,
      fderiv.snd ((contDiff_isometry Φ).differentiable (by simp) p),
      fderiv_add_const, fderiv_const_mul (differentiable_snd.snd p) ε,
      fderiv.snd differentiable_snd.differentiableAt, fderiv_snd]
    exact h)
    (toProd 1) (by simp [coordinateMap])
  refine ⟨ε, hε, fun p => ?_⟩
  simpa only [coordinateMap, Function.comp_apply, Equiv.symm_apply_apply,
    snd_snd_toProd] using congrFun heq (toProd p)

end TauCeti.Sol
