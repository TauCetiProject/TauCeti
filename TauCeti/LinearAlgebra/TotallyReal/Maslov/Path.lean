/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TotallyReal.Maslov.Index

/-!
# Relative Maslov index of paths of totally real subspaces

For two paths of maximal totally real subspaces with the same endpoints, the quotient of their
Maslov phase paths is a loop in the circle. Its degree is an integer measuring the relative
homotopy class detected by their Maslov phases. This defines the relative path comparison index;
the crossing-form index for a single path is a further construction.

The Maslov phase and its loop degree follow McDuff--Salamon, *J-holomorphic Curves and Symplectic
Topology*, 2nd ed., Appendix C.3. The relative path viewpoint is the comparison form of the
Robbin--Salamon Maslov index.
-/

public section

open Module Real
open scoped ComplexConjugate unitInterval

namespace TauCeti

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A path of maximal totally real subspaces, given by a continuous family of complex-linear
changes of frame applied to one maximal totally real subspace. -/
structure TotallyRealPath where
  /-- The subspace at time `t`. -/
  toFun : I → Submodule ℝ E
  /-- The path is given by a continuous family of complex-linear automorphisms. -/
  exists_frame : ∃ L₀ : Submodule ℝ E,
    IsMaximalTotallyReal ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) L₀ ∧
    ∃ A : I → E ≃L[ℂ] E, Continuous (fun t => (A t : E →L[ℂ] E)) ∧
      ∀ t, toFun t = L₀.map (((A t).toLinearEquiv : E →ₗ[ℂ] E).restrictScalars ℝ)

namespace TotallyRealPath

variable {E}

attribute [coe] toFun

instance : CoeFun (TotallyRealPath E) fun _ => I → Submodule ℝ E := ⟨toFun⟩

@[ext]
theorem ext {Λ Λ' : TotallyRealPath E} (h : ∀ t, Λ t = Λ' t) : Λ = Λ' := by
  cases Λ
  cases Λ'
  congr
  exact funext h

/-- Every subspace along a path of maximal totally real subspaces is maximal totally real. -/
theorem isMaximalTotallyReal (Λ : TotallyRealPath E) (t : I) :
    IsMaximalTotallyReal ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) (Λ t) := by
  obtain ⟨L₀, hL₀, A, -, hA⟩ := Λ.exists_frame
  rw [hA t]
  exact hL₀.map_linearEquiv (A t).toLinearEquiv

variable [FiniteDimensional ℂ E]

/-- The Maslov phase along a path, relative to a fixed maximal totally real subspace, is
continuous. -/
theorem continuous_maslovPhase (Λ : TotallyRealPath E) {L₀ : Submodule ℝ E}
    (hL₀ : IsMaximalTotallyReal ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) L₀) :
    Continuous fun t => hL₀.maslovPhase (Λ.isMaximalTotallyReal t) := by
  obtain ⟨L₁, hL₁, A, hAc, hA⟩ := Λ.exists_frame
  have hphase (t : I) : hL₀.maslovPhase (Λ.isMaximalTotallyReal t) =
      hL₀.maslovPhase hL₁ * (LinearMap.det ((A t).toLinearEquiv : E →ₗ[ℂ] E) /
        conj (LinearMap.det ((A t).toLinearEquiv : E →ₗ[ℂ] E))) := by
    rw [← hL₀.maslovPhase_mul_maslovPhase hL₁ (Λ.isMaximalTotallyReal t),
      hL₁.maslovPhase_congr (Λ.isMaximalTotallyReal t)
        (hL₁.map_linearEquiv (A t).toLinearEquiv) (hA t),
      IsMaximalTotallyReal.maslovPhase_map]
  simp_rw [hphase]
  exact continuous_const.mul (continuous_det_div_conj A hAc)

/-- The path of Maslov phases of `Λ` relative to a maximal totally real reference, as a continuous
map to the circle. -/
noncomputable def maslovPhasePath (Λ : TotallyRealPath E) {L₀ : Submodule ℝ E}
    (hL₀ : IsMaximalTotallyReal ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) L₀) :
    C(I, Circle) where
  toFun t := ⟨hL₀.maslovPhase (Λ.isMaximalTotallyReal t),
    mem_sphere_zero_iff_norm.2 (IsMaximalTotallyReal.norm_maslovPhase _ _)⟩
  continuous_toFun := (Λ.continuous_maslovPhase hL₀).subtype_mk _

@[simp]
theorem maslovPhasePath_apply (Λ : TotallyRealPath E) {L₀ : Submodule ℝ E}
    (hL₀ : IsMaximalTotallyReal ((LinearMap.lsmul ℂ E Complex.I).restrictScalars ℝ) L₀)
    (t : I) :
    ((Λ.maslovPhasePath hL₀ t : Circle) : ℂ) = hL₀.maslovPhase (Λ.isMaximalTotallyReal t) := by
  -- Expose the stored complex phase through the coercion from the circle subtype.
  change (hL₀.maslovPhase (Λ.isMaximalTotallyReal t) : ℂ) = _
  rfl

/-- The loop of relative Maslov phases of two paths with the same endpoints. -/
noncomputable def relativeMaslovPhasePath (Λ Γ : TotallyRealPath E)
    (h₀ : Λ 0 = Γ 0) (h₁ : Λ 1 = Γ 1) :
    Path ((Λ.maslovPhasePath (Λ.isMaximalTotallyReal 0) 0) *
      (Γ.maslovPhasePath (Λ.isMaximalTotallyReal 0) 0)⁻¹)
      ((Λ.maslovPhasePath (Λ.isMaximalTotallyReal 0) 0) *
      (Γ.maslovPhasePath (Λ.isMaximalTotallyReal 0) 0)⁻¹) := by
  let L₀ := Λ 0
  let hL₀ := Λ.isMaximalTotallyReal 0
  let α := Λ.maslovPhasePath hL₀
  let β := Γ.maslovPhasePath hL₀
  let γ : Path (α 0 * (β 0)⁻¹) (α 0 * (β 0)⁻¹) :=
    { toFun := fun t => α t * (β t)⁻¹
      continuous_toFun := α.continuous.mul β.continuous.inv
      source' := rfl
      target' := by
        have hα : α 1 = β 1 := by
          apply Circle.ext
          rw [maslovPhasePath_apply, maslovPhasePath_apply]
          exact hL₀.maslovPhase_congr _ _ h₁
        have hβ : α 0 = β 0 := by
          apply Circle.ext
          rw [maslovPhasePath_apply, maslovPhasePath_apply]
          exact hL₀.maslovPhase_congr _ _ h₀
        rw [hα, hβ]
        simp }
  exact γ

@[simp]
theorem relativeMaslovPhasePath_apply (Λ Γ : TotallyRealPath E)
    (h₀ : Λ 0 = Γ 0) (h₁ : Λ 1 = Γ 1) (t : I) :
    Λ.relativeMaslovPhasePath Γ h₀ h₁ t =
      (Λ.maslovPhasePath (Λ.isMaximalTotallyReal 0) t) *
        (Γ.maslovPhasePath (Λ.isMaximalTotallyReal 0) t)⁻¹ := by
  simp [relativeMaslovPhasePath]

/-- The relative Maslov index of two paths with the same endpoints is the degree of the loop
formed by dividing their Maslov phase paths. -/
noncomputable def relativeMaslovIndex (Λ Γ : TotallyRealPath E)
    (h₀ : Λ 0 = Γ 0) (h₁ : Λ 1 = Γ 1) : ℤ :=
  Circle.degree (Λ.relativeMaslovPhasePath Γ h₀ h₁)

/-- The relative Maslov index is the degree of the relative phase loop. -/
theorem relativeMaslovIndex_def (Λ Γ : TotallyRealPath E)
    (h₀ : Λ 0 = Γ 0) (h₁ : Λ 1 = Γ 1) :
    relativeMaslovIndex Λ Γ h₀ h₁ = Circle.degree (Λ.relativeMaslovPhasePath Γ h₀ h₁) := by
  rw [relativeMaslovIndex]

/-- Comparing a path with itself gives relative Maslov index zero. -/
@[simp]
theorem relativeMaslovIndex_self (Λ : TotallyRealPath E) :
    relativeMaslovIndex Λ Λ rfl rfl = 0 := by
  rw [relativeMaslovIndex, relativeMaslovPhasePath_self]
  exact Circle.degree_refl _
where
  relativeMaslovPhasePath_self (Λ : TotallyRealPath E) :
      Λ.relativeMaslovPhasePath Λ rfl rfl = Path.refl _ := by
    apply Path.ext
    ext t
    simp [relativeMaslovPhasePath]

/-- Compute the relative Maslov index from continuous angle lifts of the two Maslov phase paths.
If the change in the difference of the angles is `2π n`, the relative index is `n`. -/
theorem relativeMaslovIndex_eq_of_angle_lifts (Λ Γ : TotallyRealPath E)
    (h₀ : Λ 0 = Γ 0) (h₁ : Λ 1 = Γ 1) {θΛ θΓ : I → ℝ}
    (hθΛ : Continuous θΛ) (hθΓ : Continuous θΓ)
    (hΛ : ∀ t, Circle.exp (θΛ t) =
      Λ.maslovPhasePath (Λ.isMaximalTotallyReal 0) t)
    (hΓ : ∀ t, Circle.exp (θΓ t) =
      Γ.maslovPhasePath (Λ.isMaximalTotallyReal 0) t)
    {n : ℤ}
    (hangle : (θΛ 1 - θΓ 1) - (θΛ 0 - θΓ 0) = n * (2 * π)) :
    relativeMaslovIndex Λ Γ h₀ h₁ = n := by
  let γ := Λ.relativeMaslovPhasePath Γ h₀ h₁
  have hθ : Continuous fun t => θΛ t - θΓ t := hθΛ.sub hθΓ
  have hθγ (t : I) : Circle.exp (θΛ t - θΓ t) = γ t := by
    rw [relativeMaslovPhasePath_apply]
    rw [sub_eq_add_neg, Circle.exp_add, Circle.exp_neg, hΛ t, hΓ t]
  rw [relativeMaslovIndex]
  exact Circle.degree_eq_of_sub_eq γ hθ hθγ hangle

end TotallyRealPath

end TauCeti
