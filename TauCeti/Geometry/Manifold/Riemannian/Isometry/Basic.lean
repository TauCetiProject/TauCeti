/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.Riemannian.Basic
public import Mathlib.Geometry.Manifold.Riemannian.PathELength

/-!
# Smooth Riemannian isometries

A smooth Riemannian isometry is a diffeomorphism whose differential preserves the inner product
on each tangent space. The inverse and composite are again smooth Riemannian isometries. This
is the natural map for transporting the Levi-Civita connection and geodesics.

The pointwise condition says that the pullback of the metric on the target is the metric on the
source; see J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Chapter 2. Isometries
preserve tangent-vector norms and the Riemannian length `pathELength` of every curve.
-/

public section

open Bundle Manifold
open scoped ContDiff ENNReal Manifold

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]

/-- An infinitely differentiable equivalence that preserves the Riemannian inner product of
tangent vectors. Smoothness of the inverse is part of the underlying diffeomorphism. -/
structure RiemannianIsometry (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ F H')
    (M : Type*) (N : Type*) [TopologicalSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [TopologicalSpace N] [ChartedSpace H' N]
    [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
    extends Diffeomorph I J M N ∞ where
  inner_mfderiv' : ∀ x (v w : TangentSpace I x),
    inner ℝ (mfderiv I J toDiffeomorph x v) (mfderiv I J toDiffeomorph x w) =
      inner ℝ v w

namespace RiemannianIsometry

instance : EquivLike (RiemannianIsometry I J M N) M N where
  coe Φ := Φ.toDiffeomorph
  inv Φ := Φ.toDiffeomorph.symm
  left_inv Φ := Φ.toDiffeomorph.left_inv
  right_inv Φ := Φ.toDiffeomorph.right_inv
  coe_injective' Φ Ψ h := by
    cases Φ
    cases Ψ
    simp_all

@[ext]
theorem ext {Φ Ψ : RiemannianIsometry I J M N}
    (h : ∀ x, Φ x = Ψ x) : Φ = Ψ := DFunLike.coe_injective (funext h)

@[simp]
theorem coe_toDiffeomorph (Φ : RiemannianIsometry I J M N) :
    ⇑Φ.toDiffeomorph = Φ := rfl

/-- The differential of a Riemannian isometry preserves inner products. -/
@[simp]
theorem inner_mfderiv (Φ : RiemannianIsometry I J M N)
    (x : M) (v w : TangentSpace I x) :
    inner ℝ (mfderiv I J Φ x v) (mfderiv I J Φ x w) = inner ℝ v w := by
  simpa only [coe_toDiffeomorph] using Φ.inner_mfderiv' x v w

/-- The differential of a Riemannian isometry preserves tangent-vector norms. -/
@[simp]
theorem norm_mfderiv (Φ : RiemannianIsometry I J M N)
    (x : M) (v : TangentSpace I x) : ‖mfderiv I J Φ x v‖ = ‖v‖ := by
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner]
  exact congrArg Real.sqrt (Φ.inner_mfderiv x v v)

/-- The differential of a Riemannian isometry preserves extended tangent-vector norms. -/
@[simp]
theorem enorm_mfderiv (Φ : RiemannianIsometry I J M N)
    (x : M) (v : TangentSpace I x) : ‖mfderiv I J Φ x v‖ₑ = ‖v‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, Φ.norm_mfderiv]

/-- A smooth Riemannian isometry is differentiable everywhere. -/
protected theorem mdifferentiable (Φ : RiemannianIsometry I J M N) :
    MDifferentiable I J Φ := Φ.toDiffeomorph.mdifferentiable (by simp)

/-- A smooth Riemannian isometry is differentiable at each point. -/
protected theorem mdifferentiableAt (Φ : RiemannianIsometry I J M N) (x : M) :
    MDifferentiableAt I J Φ x := Φ.mdifferentiable x

/-- The identity diffeomorphism is a Riemannian isometry. -/
protected def refl (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)] :
    RiemannianIsometry I I M M where
  toDiffeomorph := Diffeomorph.refl I M ∞
  inner_mfderiv' := by
    intro x v w
    rw [Diffeomorph.coe_refl, mfderiv_id]
    rfl

@[simp]
theorem refl_apply (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)] (x : M) :
    RiemannianIsometry.refl I M x = x := by rfl

/-- The inverse of a smooth Riemannian isometry. -/
protected def symm (Φ : RiemannianIsometry I J M N) :
    RiemannianIsometry J I N M where
  toDiffeomorph := Φ.toDiffeomorph.symm
  inner_mfderiv' := by
    intro y v w
    obtain ⟨x, rfl⟩ : ∃ x : M, Φ.toDiffeomorph x = y :=
      ⟨Φ.toDiffeomorph.symm y, Φ.toDiffeomorph.apply_symm_apply y⟩
    have hx : Φ.toDiffeomorph.symm (Φ.toDiffeomorph x) = x :=
      Φ.toDiffeomorph.symm_apply_apply x
    have h := Φ.inner_mfderiv' x
      (mfderiv J I Φ.toDiffeomorph.symm (Φ.toDiffeomorph x) v)
      (mfderiv J I Φ.toDiffeomorph.symm (Φ.toDiffeomorph x) w)
    rw [hx]
    rw [Diffeomorph.mfderiv_apply_mfderiv_symm_apply Φ.toDiffeomorph
        (by simp) x v,
      Diffeomorph.mfderiv_apply_mfderiv_symm_apply Φ.toDiffeomorph
        (by simp) x w] at h
    exact h.symm

@[simp]
theorem symm_apply_apply (Φ : RiemannianIsometry I J M N)
    (x : M) : Φ.symm (Φ x) = x := Φ.toDiffeomorph.symm_apply_apply x

@[simp]
theorem apply_symm_apply (Φ : RiemannianIsometry I J M N)
    (y : N) : Φ (Φ.symm y) = y := Φ.toDiffeomorph.apply_symm_apply y

@[simp]
theorem symm_symm (Φ : RiemannianIsometry I J M N) :
    Φ.symm.symm = Φ := by
  ext x
  rfl

/-- The inverse of the identity isometry is the identity isometry. -/
@[simp]
theorem symm_refl (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)] :
    (RiemannianIsometry.refl I M).symm = RiemannianIsometry.refl I M := by
  ext x
  rfl

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  {H'' : Type*} [TopologicalSpace H''] {K : ModelWithCorners ℝ G H''}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H'' P]
  [RiemannianBundle (fun z : P ↦ TangentSpace K z)]

/-- The composite of two smooth Riemannian isometries. -/
protected def trans (Φ : RiemannianIsometry I J M N)
    (Ψ : RiemannianIsometry J K N P) :
    RiemannianIsometry I K M P where
  toDiffeomorph := Φ.toDiffeomorph.trans Ψ.toDiffeomorph
  inner_mfderiv' := by
    intro x v w
    have hv := mfderiv_comp_apply x
      (Ψ.mdifferentiableAt (Φ x)) (Φ.mdifferentiableAt x) v
    have hw := mfderiv_comp_apply x
      (Ψ.mdifferentiableAt (Φ x)) (Φ.mdifferentiableAt x) w
    rw [Diffeomorph.coe_trans, coe_toDiffeomorph, coe_toDiffeomorph, hv, hw]
    exact (Ψ.inner_mfderiv (Φ x) (mfderiv I J Φ x v)
      (mfderiv I J Φ x w)).trans (Φ.inner_mfderiv x v w)

@[simp]
theorem trans_apply (Φ : RiemannianIsometry I J M N)
    (Ψ : RiemannianIsometry J K N P) (x : M) :
    (Φ.trans Ψ) x = Ψ (Φ x) := by rfl

/-- The inverse of a composite is the composite of the inverses in reverse order. -/
@[simp]
theorem symm_trans (Φ : RiemannianIsometry I J M N)
    (Ψ : RiemannianIsometry J K N P) :
    (Φ.trans Ψ).symm = Ψ.symm.trans Φ.symm := by
  ext x
  rfl

@[simp]
theorem refl_trans (Φ : RiemannianIsometry I J M N) :
    (RiemannianIsometry.refl I M).trans Φ = Φ := by
  ext x
  simp

@[simp]
theorem trans_refl (Φ : RiemannianIsometry I J M N) :
    Φ.trans (RiemannianIsometry.refl J N) = Φ := by
  ext x
  simp

@[simp]
theorem self_trans_symm (Φ : RiemannianIsometry I J M N) :
    Φ.trans Φ.symm = RiemannianIsometry.refl I M := by
  ext x
  simp

@[simp]
theorem symm_trans_self (Φ : RiemannianIsometry I J M N) :
    Φ.symm.trans Φ = RiemannianIsometry.refl J N := by
  ext x
  simp

theorem trans_assoc (Φ : RiemannianIsometry I J M N)
    (Ψ : RiemannianIsometry J K N P)
    {L : Type*} [NormedAddCommGroup L] [NormedSpace ℝ L]
    {H''' : Type*} [TopologicalSpace H'''] {K' : ModelWithCorners ℝ L H'''}
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace H''' Q]
    [RiemannianBundle (fun z : Q ↦ TangentSpace K' z)]
    (Θ : RiemannianIsometry K K' P Q) :
    (Φ.trans Ψ).trans Θ = Φ.trans (Ψ.trans Θ) := by
  ext x
  simp

/-- A smooth Riemannian isometry preserves the Riemannian length of any curve. -/
@[simp]
theorem pathELength_comp (Φ : RiemannianIsometry I J M N)
    {γ : ℝ → M} {a b : ℝ} :
    Manifold.pathELength J (Φ ∘ γ) a b = Manifold.pathELength I γ a b := by
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Ioo,
    Manifold.pathELength_eq_lintegral_mfderiv_Ioo]
  apply MeasureTheory.setLIntegral_congr_fun measurableSet_Ioo
  intro t ht
  dsimp only
  -- The length expression coerces `Φ` directly, while the chain rule uses its diffeomorphism.
  change ‖mfderiv 𝓘(ℝ, ℝ) J ((Φ : M → N) ∘ γ) t (1 : ℝ)‖ₑ =
    ‖mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)‖ₑ
  by_cases hγ : MDiffAt γ t
  · have hder : mfderiv 𝓘(ℝ, ℝ) J ((Φ : M → N) ∘ γ) t (1 : ℝ) =
        mfderiv I J Φ.toDiffeomorph (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1) :=
      mfderiv_comp_apply t (Φ.mdifferentiableAt (γ t)) hγ 1
    rw [hder, coe_toDiffeomorph, Φ.enorm_mfderiv]
    -- The remaining tangent norm is the same expression on both sides.
    rfl
  · have hcomp : ¬MDiffAt ((Φ : M → N) ∘ γ) t := by
      exact mt (Diffeomorph.mdifferentiableAt_comp_iff Φ.toDiffeomorph
        (by simp)).1 hγ
    rw [mfderiv_zero_of_not_mdifferentiableAt hγ,
      mfderiv_zero_of_not_mdifferentiableAt hcomp]
    have hzero : ‖(0 : TangentSpace J (Φ (γ t)))‖ₑ =
        ‖(0 : TangentSpace I (γ t))‖ₑ := by simp
    exact hzero

end RiemannianIsometry

end TauCeti

end
