/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Smooth.Bundle
import TauCeti.Geometry.Manifold.VectorBundle.Hom

/-!
# Regularity of wedge products of differential forms

The paired wedge of two fixed-coefficient forms of class `C^n` is again of class `C^n`, for
every continuous bilinear pairing of the coefficient spaces. These results specialize the
bundle-valued smooth wedge to trivial coefficient bundles and a constant pairing. The constant
pairing defines a smooth section of the bundle of bilinear maps.

The relative statements use no derivative, so they hold within arbitrary subsets and at
boundary and corner points. In particular smooth forms are closed under the paired wedge, and
`TauCeti.SmoothForm.wedgeWith` and `TauCeti.SmoothForm.wedge` bundle the product as a bilinear
map on smooth forms; these supply the product on de Rham cohomology.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 14.
-/

public section

noncomputable section

open Bundle
open scoped ContDiff Manifold

namespace TauCeti

variable {E H M F₁ F₂ F₃ : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H}
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  [NormedAddCommGroup F₃] [NormedSpace ℝ F₃]
  [IsManifold I 1 M] {k l : ℕ} {n : WithTop ℕ∞} {s : Set M} {x : M}

/-- The paired wedge of two `C^n` sections of the alternating bundle is a `C^n` section,
within an arbitrary subset. -/
theorem _root_.ContMDiffWithinAt.wedgeWith_form
    {φ : RoughForm I M F₁ k} {ψ : RoughForm I M F₂ l}
    (hφ : ContMDiffWithinAt I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F₁)) n
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F₁) y (φ y)) s x)
    (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (hψ : ContMDiffWithinAt I (I.prod 𝓘(ℝ, E [⋀^Fin l]→L[ℝ] F₂)) n
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin l]→L[ℝ] F₂) y (ψ y)) s x) :
    ContMDiffWithinAt I (I.prod 𝓘(ℝ, E [⋀^Fin (k + l)]→L[ℝ] F₃)) n
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin (k + l)]→L[ℝ] F₃) y (φ.wedgeWith μ ψ y)) s x := by
  simpa only [bundleWedgeWith_trivial] using
    ContMDiffWithinAt.bundleWedgeWith_form (fun _ ↦ μ.continuous₂)
      ((contMDiff_const_bundlePairing μ x).contMDiffWithinAt) hφ hψ

/-- The paired wedge of two `C^n` sections of the alternating bundle is a `C^n` section on an
arbitrary subset. -/
theorem _root_.ContMDiffOn.wedgeWith_form
    {φ : RoughForm I M F₁ k} {ψ : RoughForm I M F₂ l}
    (hφ : ContMDiffOn I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F₁)) n
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F₁) y (φ y)) s)
    (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (hψ : ContMDiffOn I (I.prod 𝓘(ℝ, E [⋀^Fin l]→L[ℝ] F₂)) n
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin l]→L[ℝ] F₂) y (ψ y)) s) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E [⋀^Fin (k + l)]→L[ℝ] F₃)) n
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin (k + l)]→L[ℝ] F₃) y (φ.wedgeWith μ ψ y)) s :=
  fun x hx ↦ (hφ x hx).wedgeWith_form μ (hψ x hx)

/-- The paired wedge of two sections of the alternating bundle that are `C^n` at a point is
`C^n` at that point. -/
theorem _root_.ContMDiffAt.wedgeWith_form
    {φ : RoughForm I M F₁ k} {ψ : RoughForm I M F₂ l}
    (hφ : ContMDiffAt I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F₁)) n
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F₁) y (φ y)) x)
    (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (hψ : ContMDiffAt I (I.prod 𝓘(ℝ, E [⋀^Fin l]→L[ℝ] F₂)) n
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin l]→L[ℝ] F₂) y (ψ y)) x) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E [⋀^Fin (k + l)]→L[ℝ] F₃)) n
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin (k + l)]→L[ℝ] F₃) y (φ.wedgeWith μ ψ y)) x :=
  ContMDiffWithinAt.wedgeWith_form hφ μ hψ

/-- The paired wedge of two fixed-coefficient forms of class `C^n` is of class `C^n`. -/
theorem IsSmoothForm.wedgeWith (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃) {φ : RoughForm I M F₁ k}
    {ψ : RoughForm I M F₂ l} (hφ : IsSmoothForm I n φ) (hψ : IsSmoothForm I n ψ) :
    IsSmoothForm I n (φ.wedgeWith μ ψ) := by
  rw [isSmoothForm_def] at hφ hψ ⊢
  simpa only [isSmoothBundleForm_def, bundleWedgeWith_trivial] using
    IsSmoothBundleForm.bundleWedgeWith (fun _ ↦ μ.continuous₂) (contMDiff_const_bundlePairing μ)
      ((isSmoothBundleForm_def n φ).mpr hφ) ((isSmoothBundleForm_def n ψ).mpr hψ)

/-- The real wedge of two real-valued forms of class `C^n` is of class `C^n`. -/
theorem IsSmoothForm.wedge {φ : RoughForm I M ℝ k} {ψ : RoughForm I M ℝ l}
    (hφ : IsSmoothForm I n φ) (hψ : IsSmoothForm I n ψ) : IsSmoothForm I n (φ.wedge ψ) := by
  rw [RoughForm.wedge_def]
  exact hφ.wedgeWith (ContinuousLinearMap.mul ℝ ℝ) hψ

/-- Smooth fixed-coefficient forms are closed under the paired wedge, for every continuous
bilinear pairing of the coefficient spaces. -/
theorem smoothForms_wedgeWith_mem (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃) (φ : SmoothForm I M F₁ k)
    (ψ : SmoothForm I M F₂ l) :
    RoughForm.wedgeWith μ (φ : RoughForm I M F₁ k) (ψ : RoughForm I M F₂ l) ∈
      smoothForms I M F₃ (k + l) := by
  apply mem_smoothForms.mpr
  simpa only [bundleWedgeWith_trivial] using
    IsSmoothBundleForm.bundleWedgeWith (fun _ ↦ μ.continuous₂)
      (contMDiff_const_bundlePairing μ) φ.isSmoothBundleForm ψ.isSmoothBundleForm

/-- Smooth real-valued forms are closed under the real wedge. -/
theorem smoothForms_wedge_mem (φ : SmoothForm I M ℝ k) (ψ : SmoothForm I M ℝ l) :
    RoughForm.wedge (φ : RoughForm I M ℝ k) (ψ : RoughForm I M ℝ l) ∈
      smoothForms I M ℝ (k + l) := by
  rw [RoughForm.wedge_def]
  exact smoothForms_wedgeWith_mem (ContinuousLinearMap.mul ℝ ℝ) φ ψ

namespace SmoothForm

/-- The paired wedge of smooth fixed-coefficient forms, as a bilinear map. -/
def wedgeWith (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃) :
    SmoothForm I M F₁ k →ₗ[ℝ] SmoothForm I M F₂ l →ₗ[ℝ] SmoothForm I M F₃ (k + l) :=
  LinearMap.mk₂ ℝ (fun φ ψ ↦ ⟨_, smoothForms_wedgeWith_mem μ φ ψ⟩)
    (fun φ φ' ψ ↦ Subtype.ext <| by
      simp only [Submodule.coe_add, RoughForm.wedgeWith_add_left])
    (fun c φ ψ ↦ Subtype.ext <| by
      simp only [Submodule.coe_smul, RoughForm.wedgeWith_smul_left])
    (fun φ ψ ψ' ↦ Subtype.ext <| by
      simp only [Submodule.coe_add, RoughForm.wedgeWith_add_right])
    (fun c φ ψ ↦ Subtype.ext <| by
      simp only [Submodule.coe_smul, RoughForm.wedgeWith_smul_right])

/-- The underlying rough form of the smooth paired wedge is the rough paired wedge. -/
@[simp]
theorem coe_wedgeWith (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃) (φ : SmoothForm I M F₁ k)
    (ψ : SmoothForm I M F₂ l) :
    (wedgeWith μ φ ψ : RoughForm I M F₃ (k + l)) =
      RoughForm.wedgeWith μ (φ : RoughForm I M F₁ k) (ψ : RoughForm I M F₂ l) := by
  rw [wedgeWith, LinearMap.mk₂_apply]

/-- Evaluation of the smooth fixed-coefficient paired wedge. -/
theorem wedgeWith_apply (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃) (φ : SmoothForm I M F₁ k)
    (ψ : SmoothForm I M F₂ l) (x : M) (v : Fin (k + l) → TangentSpace I x) :
    (wedgeWith μ φ ψ).1 x v =
      (((k.factorial : ℝ) * (l.factorial : ℝ))⁻¹) •
        ∑ σ : Equiv.Perm (Fin (k + l)), Equiv.Perm.sign σ •
          μ (φ.1 x (fun i ↦ v (σ (Fin.castAdd l i))))
            (ψ.1 x (fun j ↦ v (σ (Fin.natAdd k j)))) := by
  rw [coe_wedgeWith, RoughForm.wedgeWith_apply]

/-- Pairing a smooth form with a degree-zero form pairs its value with the function value. -/
@[simp]
theorem wedgeWith_apply_zero_right (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (φ : SmoothForm I M F₁ k) (ψ : SmoothForm I M F₂ 0)
    (x : M) (v : Fin k → TangentSpace I x) :
    (wedgeWith μ φ ψ).1 x v = μ (φ.1 x v) (ψ.1 x 0) := by
  rw [coe_wedgeWith]
  exact RoughForm.wedgeWith_apply_zero_right μ φ.1 ψ.1 x v

/-- Evaluation of the smooth paired wedge on two one-forms. -/
theorem wedgeWith_apply_one_one (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (φ : SmoothForm I M F₁ 1) (ψ : SmoothForm I M F₂ 1) (x : M)
    (v w : TangentSpace I x) :
    (wedgeWith μ φ ψ).1 x ![v, w] =
      μ (φ.1 x ![v]) (ψ.1 x ![w]) - μ (φ.1 x ![w]) (ψ.1 x ![v]) := by
  rw [coe_wedgeWith, RoughForm.wedgeWith_apply_one_one]

/-- The real wedge of smooth real-valued forms, as a bilinear map. -/
def wedge : SmoothForm I M ℝ k →ₗ[ℝ] SmoothForm I M ℝ l →ₗ[ℝ] SmoothForm I M ℝ (k + l) :=
  wedgeWith (ContinuousLinearMap.mul ℝ ℝ)

/-- The smooth real wedge specializes the paired wedge to multiplication. -/
theorem wedge_def (φ : SmoothForm I M ℝ k) (ψ : SmoothForm I M ℝ l) :
    wedge φ ψ = wedgeWith (ContinuousLinearMap.mul ℝ ℝ) φ ψ := by
  rw [wedge]

/-- The underlying rough form of the smooth real wedge is the rough real wedge. -/
@[simp]
theorem coe_wedge (φ : SmoothForm I M ℝ k) (ψ : SmoothForm I M ℝ l) :
    (wedge φ ψ : RoughForm I M ℝ (k + l)) =
      RoughForm.wedge (φ : RoughForm I M ℝ k) (ψ : RoughForm I M ℝ l) := by
  rw [wedge, coe_wedgeWith, RoughForm.wedge_def]

/-- Evaluation of the smooth real-valued wedge in every degree. -/
theorem wedge_apply (φ : SmoothForm I M ℝ k) (ψ : SmoothForm I M ℝ l)
    (x : M) (v : Fin (k + l) → TangentSpace I x) :
    (wedge φ ψ).1 x v =
      (((k.factorial : ℝ) * (l.factorial : ℝ))⁻¹) •
        ∑ σ : Equiv.Perm (Fin (k + l)), Equiv.Perm.sign σ •
          (φ.1 x (fun i ↦ v (σ (Fin.castAdd l i))) *
            ψ.1 x (fun j ↦ v (σ (Fin.natAdd k j)))) := by
  rw [coe_wedge, RoughForm.wedge_apply]

/-- Wedging a smooth real-valued form with a degree-zero form multiplies its value by the
function value. -/
@[simp]
theorem wedge_apply_zero_right (φ : SmoothForm I M ℝ k) (ψ : SmoothForm I M ℝ 0)
    (x : M) (v : Fin k → TangentSpace I x) :
    (wedge φ ψ).1 x v = φ.1 x v * ψ.1 x 0 := by
  rw [coe_wedge, RoughForm.wedge_apply_zero_right]

/-- The smooth real-valued wedge of two one-forms evaluates as a determinant. -/
theorem wedge_apply_one_one (φ : SmoothForm I M ℝ 1) (ψ : SmoothForm I M ℝ 1) (x : M)
    (v w : TangentSpace I x) :
    (wedge φ ψ).1 x ![v, w] =
      φ.1 x ![v] * ψ.1 x ![w] - φ.1 x ![w] * ψ.1 x ![v] := by
  rw [coe_wedge, RoughForm.wedge_apply_one_one]

/-- Swapping smooth paired forms flips the coefficient pairing and contributes the graded sign. -/
theorem wedgeWith_flip (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (φ : SmoothForm I M F₁ k) (ψ : SmoothForm I M F₂ l) (x : M)
    (v : Fin (k + l) → TangentSpace I x) :
    (wedgeWith μ φ ψ).1 x v =
      (-1 : ℝ) ^ (k * l) •
        (wedgeWith μ.flip ψ φ).1 x (v ∘ Fin.cast (Nat.add_comm l k)) := by
  simpa only [coe_wedgeWith] using
    RoughForm.wedgeWith_flip μ (φ : RoughForm I M F₁ k) (ψ : RoughForm I M F₂ l) x v

/-- A symmetric coefficient pairing makes the smooth paired wedge graded-commutative. -/
theorem wedgeWith_comm (μ : F₁ →L[ℝ] F₁ →L[ℝ] F₃)
    (hμ : ∀ a b, μ a b = μ b a) (φ : SmoothForm I M F₁ k) (ψ : SmoothForm I M F₁ l)
    (x : M) (v : Fin (k + l) → TangentSpace I x) :
    (wedgeWith μ φ ψ).1 x v =
      (-1 : ℝ) ^ (k * l) •
        (wedgeWith μ ψ φ).1 x (v ∘ Fin.cast (Nat.add_comm l k)) := by
  simpa only [coe_wedgeWith] using
    RoughForm.wedgeWith_comm μ hμ (φ : RoughForm I M F₁ k) (ψ : RoughForm I M F₁ l) x v

/-- Real-valued smooth forms commute with the usual graded sign. -/
theorem wedge_comm (φ : SmoothForm I M ℝ k) (ψ : SmoothForm I M ℝ l) (x : M)
    (v : Fin (k + l) → TangentSpace I x) :
    (wedge φ ψ).1 x v =
      (-1 : ℝ) ^ (k * l) • (wedge ψ φ).1 x (v ∘ Fin.cast (Nat.add_comm l k)) := by
  simpa only [wedge, coe_wedgeWith, RoughForm.wedge_def] using
    RoughForm.wedge_comm (φ : RoughForm I M ℝ k) (ψ : RoughForm I M ℝ l) x v

end SmoothForm

end TauCeti
