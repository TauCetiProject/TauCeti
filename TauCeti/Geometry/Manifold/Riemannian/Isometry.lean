/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.Riemannian.Basic
public import Mathlib.Geometry.Manifold.Riemannian.PathELength

/-!
# Smooth Riemannian isometries

A smooth Riemannian isometry is a diffeomorphism whose differential preserves the inner product
on each tangent space. The inverse and composite are again smooth Riemannian isometries. This
is the natural map for transporting the Levi-Civita connection and geodesics.

The definition uses the same pointwise tangent-space condition as the invariance of Riemannian
volume. See J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Chapter 2.
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
structure RiemannianIsometry extends Diffeomorph I J M N ∞ where
  inner_mfderiv : ∀ x (v w : TangentSpace I x),
    inner ℝ (mfderiv I J toDiffeomorph x v) (mfderiv I J toDiffeomorph x w) =
      inner ℝ v w

namespace RiemannianIsometry

instance : EquivLike (RiemannianIsometry (I := I) (J := J) (M := M) (N := N)) M N where
  coe Φ := Φ.toDiffeomorph
  inv Φ := Φ.toDiffeomorph.symm
  left_inv Φ := Φ.toDiffeomorph.left_inv
  right_inv Φ := Φ.toDiffeomorph.right_inv
  coe_injective' Φ Ψ h := by
    cases Φ
    cases Ψ
    simp_all

@[ext]
theorem ext {Φ Ψ : RiemannianIsometry (I := I) (J := J) (M := M) (N := N)}
    (h : ∀ x, Φ x = Ψ x) : Φ = Ψ := DFunLike.coe_injective (funext h)

@[simp]
theorem coe_toDiffeomorph (Φ : RiemannianIsometry (I := I) (J := J) (M := M) (N := N)) :
    ⇑Φ.toDiffeomorph = Φ := rfl

/-- The differential of a Riemannian isometry preserves inner products. -/
@[simp]
theorem inner_mfderiv_apply (Φ : RiemannianIsometry (I := I) (J := J) (M := M) (N := N))
    (x : M) (v w : TangentSpace I x) :
    inner ℝ (mfderiv I J Φ x v) (mfderiv I J Φ x w) = inner ℝ v w := by
  simpa only [coe_toDiffeomorph] using Φ.inner_mfderiv x v w

/-- The differential of a Riemannian isometry preserves tangent-vector norms. -/
@[simp]
theorem norm_mfderiv (Φ : RiemannianIsometry (I := I) (J := J) (M := M) (N := N))
    (x : M) (v : TangentSpace I x) : ‖mfderiv I J Φ x v‖ = ‖v‖ := by
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner]
  exact congrArg Real.sqrt (by simpa only [coe_toDiffeomorph] using Φ.inner_mfderiv x v v)

/-- The identity diffeomorphism is a Riemannian isometry. -/
protected def refl (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)] :
    RiemannianIsometry (I := I) (J := I) (M := M) (N := M) where
  toDiffeomorph := Diffeomorph.refl I M ∞
  inner_mfderiv := by
    intro x v w
    rw [Diffeomorph.coe_refl, mfderiv_id]
    rfl

@[simp]
theorem refl_apply (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)] (x : M) :
    RiemannianIsometry.refl I M x = x := by rfl

/-- The inverse of a smooth Riemannian isometry. -/
protected def symm (Φ : RiemannianIsometry (I := I) (J := J) (M := M) (N := N)) :
    RiemannianIsometry (I := J) (J := I) (M := N) (N := M) where
  toDiffeomorph := Φ.toDiffeomorph.symm
  inner_mfderiv := by
    intro y v w
    obtain ⟨x, rfl⟩ : ∃ x : M, Φ.toDiffeomorph x = y :=
      ⟨Φ.toDiffeomorph.symm y, Φ.toDiffeomorph.apply_symm_apply y⟩
    have hx : Φ.toDiffeomorph.symm (Φ.toDiffeomorph x) = x :=
      Φ.toDiffeomorph.symm_apply_apply x
    have hcomp (u : TangentSpace J (Φ.toDiffeomorph x)) :
        mfderiv I J Φ.toDiffeomorph x
          (mfderiv J I Φ.toDiffeomorph.symm (Φ.toDiffeomorph x) u) = u := by
      have hid : Φ.toDiffeomorph ∘ Φ.toDiffeomorph.symm = id :=
        funext Φ.toDiffeomorph.apply_symm_apply
      have hder : mfderiv J J (Φ.toDiffeomorph ∘ Φ.toDiffeomorph.symm)
          (Φ.toDiffeomorph x) u =
          mfderiv I J Φ.toDiffeomorph (Φ.toDiffeomorph.symm (Φ.toDiffeomorph x))
            (mfderiv J I Φ.toDiffeomorph.symm (Φ.toDiffeomorph x) u) :=
        mfderiv_comp_apply (Φ.toDiffeomorph x)
          (Φ.toDiffeomorph.contMDiffAt.mdifferentiableAt (by simp))
          (Φ.toDiffeomorph.symm.contMDiffAt.mdifferentiableAt (by simp)) u
      rw [hid, mfderiv_id] at hder
      rw [hx] at hder
      convert hder.symm using 1 <;> simp only [id_eq, ContinuousLinearMap.id_apply]
    have h := Φ.inner_mfderiv x
      (mfderiv J I Φ.toDiffeomorph.symm (Φ.toDiffeomorph x) v)
      (mfderiv J I Φ.toDiffeomorph.symm (Φ.toDiffeomorph x) w)
    rw [hx]
    rw [hcomp v, hcomp w] at h
    exact h.symm

@[simp]
theorem symm_apply_apply (Φ : RiemannianIsometry (I := I) (J := J) (M := M) (N := N))
    (x : M) : Φ.symm (Φ x) = x := Φ.toDiffeomorph.symm_apply_apply x

@[simp]
theorem apply_symm_apply (Φ : RiemannianIsometry (I := I) (J := J) (M := M) (N := N))
    (y : N) : Φ (Φ.symm y) = y := Φ.toDiffeomorph.apply_symm_apply y

@[simp]
theorem symm_symm (Φ : RiemannianIsometry (I := I) (J := J) (M := M) (N := N)) :
    Φ.symm.symm = Φ := by
  ext x
  rfl

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  {H'' : Type*} [TopologicalSpace H''] {K : ModelWithCorners ℝ G H''}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H'' P]
  [RiemannianBundle (fun z : P ↦ TangentSpace K z)]

/-- The composite of two smooth Riemannian isometries. -/
protected def trans (Φ : RiemannianIsometry (I := I) (J := J) (M := M) (N := N))
    (Ψ : RiemannianIsometry (I := J) (J := K) (M := N) (N := P)) :
    RiemannianIsometry (I := I) (J := K) (M := M) (N := P) where
  toDiffeomorph := Φ.toDiffeomorph.trans Ψ.toDiffeomorph
  inner_mfderiv := by
    intro x v w
    have hv := mfderiv_comp_apply x
      (Ψ.toDiffeomorph.contMDiffAt.mdifferentiableAt (by simp))
      (Φ.toDiffeomorph.contMDiffAt.mdifferentiableAt (by simp)) v
    have hw := mfderiv_comp_apply x
      (Ψ.toDiffeomorph.contMDiffAt.mdifferentiableAt (by simp))
      (Φ.toDiffeomorph.contMDiffAt.mdifferentiableAt (by simp)) w
    rw [Diffeomorph.coe_trans, hv, hw]
    exact (Ψ.inner_mfderiv (Φ x) (mfderiv I J Φ.toDiffeomorph x v)
      (mfderiv I J Φ.toDiffeomorph x w)).trans (Φ.inner_mfderiv x v w)

@[simp]
theorem trans_apply (Φ : RiemannianIsometry (I := I) (J := J) (M := M) (N := N))
    (Ψ : RiemannianIsometry (I := J) (J := K) (M := N) (N := P)) (x : M) :
    (Φ.trans Ψ) x = Ψ (Φ x) := by rfl

@[simp]
theorem refl_trans (Φ : RiemannianIsometry (I := I) (J := J) (M := M) (N := N)) :
    (RiemannianIsometry.refl I M).trans Φ = Φ := by
  ext x
  simp

@[simp]
theorem trans_refl (Φ : RiemannianIsometry (I := I) (J := J) (M := M) (N := N)) :
    Φ.trans (RiemannianIsometry.refl J N) = Φ := by
  ext x
  simp

@[simp]
theorem trans_symm (Φ : RiemannianIsometry (I := I) (J := J) (M := M) (N := N)) :
    Φ.trans Φ.symm = RiemannianIsometry.refl I M := by
  ext x
  simp

@[simp]
theorem symm_trans (Φ : RiemannianIsometry (I := I) (J := J) (M := M) (N := N)) :
    Φ.symm.trans Φ = RiemannianIsometry.refl J N := by
  ext x
  simp

theorem trans_assoc (Φ : RiemannianIsometry (I := I) (J := J) (M := M) (N := N))
    (Ψ : RiemannianIsometry (I := J) (J := K) (M := N) (N := P))
    {L : Type*} [NormedAddCommGroup L] [NormedSpace ℝ L]
    {H''' : Type*} [TopologicalSpace H'''] {K' : ModelWithCorners ℝ L H'''}
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace H''' Q]
    [RiemannianBundle (fun z : Q ↦ TangentSpace K' z)]
    (Θ : RiemannianIsometry (I := K) (J := K') (M := P) (N := Q)) :
    (Φ.trans Ψ).trans Θ = Φ.trans (Ψ.trans Θ) := by
  ext x
  simp

/-- A smooth Riemannian isometry preserves the Riemannian length of any curve. -/
@[simp]
theorem pathELength_comp (Φ : RiemannianIsometry (I := I) (J := J) (M := M) (N := N))
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
      mfderiv_comp_apply t (Φ.toDiffeomorph.mdifferentiable (by simp) (γ t)) hγ 1
    rw [hder, coe_toDiffeomorph]
    rw [← ofReal_norm, ← ofReal_norm,
      Φ.norm_mfderiv (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1)]
    rfl
  · have hcomp : ¬MDiffAt ((Φ : M → N) ∘ γ) t := by
      intro hc
      have h := (Φ.toDiffeomorph.symm.mdifferentiable (by simp) ((Φ : M → N) (γ t))).comp t hc
      have heq : Φ.toDiffeomorph.symm ∘ ((Φ : M → N) ∘ γ) = γ := by
        funext s
        exact Φ.toDiffeomorph.symm_apply_apply (γ s)
      rw [heq] at h
      exact hγ h
    rw [mfderiv_zero_of_not_mdifferentiableAt hγ,
      mfderiv_zero_of_not_mdifferentiableAt hcomp]
    change ‖(0 : TangentSpace J (Φ (γ t)))‖ₑ = ‖(0 : TangentSpace I (γ t))‖ₑ
    simp

end RiemannianIsometry

end TauCeti

end
