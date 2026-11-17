/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Flow
public import TauCeti.Geometry.Manifold.Flow.Eulerian

/-!
# Lie derivatives of differential forms along smooth isotopies

Let `φ_t`, `t ∈ ℝ`, be a family of diffeomorphisms of a boundaryless manifold `M`, such that
`(t, x) ↦ φ_t x` and `(t, y) ↦ φ_t⁻¹ y` are jointly `C²`, and let
`X_t = (∂_t φ_t) ∘ φ_t⁻¹` be its Eulerian velocity field (`TauCeti.eulerianField`). For a
differential form `α`, the pullbacks `φ_t^* α` at a point `x` form a curve in the alternating maps
on `T_x M`, and its velocity is the pullback of the Lie derivative along the current field:

`d/dt (φ_t^* α)ₓ = (φ_t^* L_{X_t} α)ₓ`

(`TauCeti.hasDerivAt_mpullback_eulerianField`). Consequently the pullback `φ_t^* α` is independent
of `t` exactly when `L_{X_t} α = 0` for every `t`
(`TauCeti.forall_mpullback_eq_iff_forall_mlieDerivForm_eulerianField_eq_zero`). For a closed form
`β`, Cartan's formula turns this into the condition that every contraction `ι_{X_t} β` is closed
(`TauCeti.forall_mpullback_eq_iff_forall_mextDeriv_interior_eulerianField_eq_zero`).

For a symplectic form `ω` and an isotopy starting at the identity, this says that the isotopy
consists of symplectomorphisms exactly when its velocity one-forms `ι_{X_t} ω` are all closed
(`TauCeti.mextDeriv_interior_eulerianField_eq_zero` is the forward direction). These closed
one-forms are the integrands of the flux of a symplectic isotopy.

The proof does not use the time-dependent flow of `X`: at the base time `t`, the family
`u ↦ φ_u ∘ φ_t⁻¹` is the identity and moves with velocity `X_t`, so
`TauCeti.hasDerivAt_mpullback_of_eq_id` applies to it directly.

## References

* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford University
  Press, 2017, Chapter 3 (symplectic isotopies and the closed one-forms `ι_{X_t} ω`) and
  Chapter 10 (the flux homomorphism).
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 22
  (derivatives of pullbacks along time-dependent families).
-/

public section

noncomputable section

open Set Filter Bundle ContinuousAlternatingMap
open scoped Manifold Topology ContDiff

namespace TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ} {φ : ℝ → M ≃ M}

variable (hφ : ContMDiff (𝓘(ℝ, ℝ).prod I) I 2 (fun p : ℝ × M ↦ φ p.1 p.2))
  (hφ' : ContMDiff (𝓘(ℝ, ℝ).prod I) I 2 (fun p : ℝ × M ↦ (φ p.1).symm p.2))
include hφ hφ'

/-- **The Lie derivative is the velocity of pulled-back forms at the base time.** For a form `α`
differentiable at `y`, the pullbacks by the maps `φ_u ∘ φ_t⁻¹` satisfy
`d/du|_{u = t} ((φ_u ∘ φ_t⁻¹)^* α)_y = (L_{X_t} α)_y`. -/
theorem hasDerivAt_mpullback_eulerianField_self {α : RoughForm I M F k} (t : ℝ) (y : M)
    (hα : MDifferentiableAt I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F))
      (fun z ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) z (α z)) y) :
    HasDerivAt (F := E [⋀^Fin k]→L[ℝ] F)
      (fun u ↦ mpullback I I (fun x ↦ φ u ((φ t).symm x)) α y)
      (mlieDerivForm (eulerianField I φ t) α y) t :=
  (PullbackAction.roughForm I M F k).hasDerivAt_eulerianField_self hφ hφ' (s := fun _ ↦ α) t y
    (fun hid hsmooth hvel ↦ hasDerivAt_mpullback_of_eq_id y hid hsmooth hvel hα)

/-- **Lie derivatives along isotopies.** For a form `α` differentiable at `φ_t x`, the pullbacks
`(φ_u^* α)ₓ` have velocity `(φ_t^* L_{X_t} α)ₓ` at time `t`, where `X` is the Eulerian velocity
field of the family. -/
theorem hasDerivAt_mpullback_eulerianField {α : RoughForm I M F k} (t : ℝ) (x : M)
    (hα : MDifferentiableAt I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F))
      (fun z ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) z (α z)) (φ t x)) :
    HasDerivAt (F := E [⋀^Fin k]→L[ℝ] F)
      (fun u ↦ mpullback I I (φ u) α x)
      (mpullback I I (φ t) (mlieDerivForm (eulerianField I φ t) α) x) t :=
  (PullbackAction.roughForm I M F k).hasDerivAt_eulerianField hφ hφ' (s := fun _ ↦ α) t x
    (hasDerivAt_mpullback_eulerianField_self hφ hφ' t _ hα)

/-- **Invariance of forms under isotopies.** For a differentiable form `α`, the pullback `φ_t^* α`
is independent of `t` exactly when its Lie derivative along the Eulerian velocity field of the
family vanishes at every time. -/
theorem forall_mpullback_eq_iff_forall_mlieDerivForm_eulerianField_eq_zero
    {α : RoughForm I M F k}
    (hα : MDifferentiable I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F))
      (fun z ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) z (α z))) :
    (∀ s t, mpullback I I (φ s) α = mpullback I I (φ t) α) ↔
      ∀ t, mlieDerivForm (eulerianField I φ t) α = 0 :=
  (PullbackAction.roughForm I M F k).forall_pull_eulerianField_eq_iff hφ hφ'
    (L := fun V ↦ mlieDerivForm V α)
    (fun t y ↦ hasDerivAt_mpullback_eulerianField_self hφ hφ' t y (hα y))

/-- If every map of the family preserves a differentiable form `α`, then `L_{X_t} α = 0` for the
Eulerian velocity field `X` of the family. -/
theorem mlieDerivForm_eulerianField_eq_zero {α : RoughForm I M F k}
    (hα : MDifferentiable I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F))
      (fun z ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) z (α z)))
    (h : ∀ t, mpullback I I (φ t) α = α) (t : ℝ) :
    mlieDerivForm (eulerianField I φ t) α = 0 :=
  (forall_mpullback_eq_iff_forall_mlieDerivForm_eulerianField_eq_zero hφ hφ' hα).1
    (fun s u ↦ by rw [h s, h u]) t

/-- **Isotopies preserving a closed form.** For a differentiable closed form `β`, the pullback
`φ_t^* β` is independent of `t` exactly when every contraction `ι_{X_t} β` with the Eulerian
velocity field is closed. For a symplectic form and an isotopy starting at the identity: the
isotopy consists of symplectomorphisms exactly when its velocity one-forms are closed. -/
theorem forall_mpullback_eq_iff_forall_mextDeriv_interior_eulerianField_eq_zero
    {β : RoughForm I M F (k + 1)}
    (hβ : MDifferentiable I (I.prod 𝓘(ℝ, E [⋀^Fin (k + 1)]→L[ℝ] F))
      (fun z ↦ TotalSpace.mk' (E [⋀^Fin (k + 1)]→L[ℝ] F) z (β z)))
    (hdβ : mextDeriv β = 0) :
    (∀ s t, mpullback I I (φ s) β = mpullback I I (φ t) β) ↔
      ∀ t, mextDeriv (RoughForm.interior (eulerianField I φ t) β) = 0 := by
  rw [forall_mpullback_eq_iff_forall_mlieDerivForm_eulerianField_eq_zero hφ hφ' hβ]
  refine forall_congr' fun t ↦ ?_
  -- The slice `X_t` of the jointly `C¹` Eulerian field is a differentiable vector field.
  have hX : MDifferentiable I I.tangent
      (fun y ↦ (⟨y, eulerianField I φ t y⟩ : TangentBundle I M)) :=
    ((contMDiff_eulerianField (m := 1) (n := 2) (by norm_num) hφ (hφ'.of_le one_le_two)).comp
      ((contMDiff_const (c := t)).prodMk contMDiff_id)).mdifferentiable one_ne_zero
  rw [mlieDerivForm_eq_mextDeriv_interior hβ hX hdβ]

/-- **The velocity one-forms of a symplectic isotopy are closed.** If every map of the family
preserves a differentiable closed form `β`, then every contraction `ι_{X_t} β` with the Eulerian
velocity field is closed. -/
theorem mextDeriv_interior_eulerianField_eq_zero {β : RoughForm I M F (k + 1)}
    (hβ : MDifferentiable I (I.prod 𝓘(ℝ, E [⋀^Fin (k + 1)]→L[ℝ] F))
      (fun z ↦ TotalSpace.mk' (E [⋀^Fin (k + 1)]→L[ℝ] F) z (β z)))
    (hdβ : mextDeriv β = 0) (h : ∀ t, mpullback I I (φ t) β = β) (t : ℝ) :
    mextDeriv (RoughForm.interior (eulerianField I φ t) β) = 0 :=
  (forall_mpullback_eq_iff_forall_mextDeriv_interior_eulerianField_eq_zero hφ hφ' hβ hdβ).1
    (fun s u ↦ by rw [h s, h u]) t

end TauCeti
