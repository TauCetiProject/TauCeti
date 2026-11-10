/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Flow
public import TauCeti.Geometry.Manifold.Flow.Eulerian

/-!
# Forms moved by an isotopy

Let `φ : ℝ → (M ≃ₘ^n M)`, `2 ≤ n`, be a family of diffeomorphisms of a manifold which is jointly
`C²` in time and space, with Eulerian velocity field `X_t = (∂_t φ_t) ∘ φ_t⁻¹`
(`TauCeti.eulerianVelocity`). The Eulerian field controls how pulled-back forms move. For a form
`α`,

`d/dt (φ_t^* α) = φ_t^* L_{X_t} α`

(`TauCeti.hasDerivAt_mpullback_eulerianVelocity`): the family `u ↦ φ_u ∘ φ_t⁻¹` is the identity at
time `t` and moves with velocity `X_t` there, so its pullbacks have velocity `L_{X_t} α` at `t`
(`TauCeti.hasDerivAt_mpullback_of_eq_id`), and pulling back by `φ_t` gives the formula. No flow,
completeness or compactness is involved, since `φ` is given. Hence the pullbacks `φ_t^* α` do not
depend on `t` exactly when `L_{X_t} α = 0` for every `t`
(`TauCeti.forall_mpullback_eq_mpullback_iff_mlieDerivForm_eulerianVelocity_eq_zero`). For a closed
form `β`, Cartan's formula turns this into closedness of the contractions `ι_{X_t} β`
(`TauCeti.forall_mpullback_eq_self_iff_mextDeriv_interior_eulerianVelocity_eq_zero`). For a
symplectic form `ω` and an isotopy starting at the identity, this says that `φ` is a symplectic
isotopy exactly when the one-forms `ι_{X_t} ω` are all closed. These closed one-forms are the
input to the flux of a symplectic isotopy.

The time-dependent flows of `TauCeti.Geometry.Manifold.DifferentialForm.Flow.TimeDependent` are
such families, with Eulerian field the generating time-dependent vector field.

## Main results

* `TauCeti.hasDerivAt_mpullback_eulerianVelocity`: `d/dt (φ_t^* α) = φ_t^* L_{X_t} α`.
* `TauCeti.forall_mpullback_eq_mpullback_iff_mlieDerivForm_eulerianVelocity_eq_zero`: the
  pullbacks are constant in time exactly when the Lie derivatives vanish.
* `TauCeti.forall_mpullback_eq_self_iff_mextDeriv_interior_eulerianVelocity_eq_zero`: an isotopy
  starting at a map preserving a closed form `β` preserves `β` at all times exactly when every
  contraction `ι_{X_t} β` is closed.

## References

* Dusa McDuff and Dietmar Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Chapter 3 (symplectic isotopies and their generating vector fields) and Chapter 10 (the flux
  homomorphism).
-/

public section

noncomputable section

open Set Filter Bundle ContinuousAlternatingMap
open scoped Manifold Topology ContDiff

namespace TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}
  {n : ℕ∞ω} {φ : ℝ → M ≃ₘ^n⟮I, I⟯ M}

/-- **Pullbacks along an isotopy move with the Lie derivative along its Eulerian field.** For a
jointly `C²` family `φ` of `C^n` diffeomorphisms, `2 ≤ n`, and a form `α` differentiable at
`φ_t x`, the pullbacks `(φ_u^* α)ₓ` have velocity `(φ_t^* L_{X_t} α)ₓ` at time `t`, where `X_t` is
the Eulerian field. -/
theorem hasDerivAt_mpullback_eulerianVelocity (hn : 2 ≤ n)
    (hφ : ContMDiff (𝓘(ℝ, ℝ).prod I) I 2 fun p : ℝ × M ↦ φ p.1 p.2) {α : RoughForm I M F k}
    (t : ℝ) (x : M)
    (hα : MDifferentiableAt I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F))
      (fun z ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) z (α z)) (φ t x)) :
    HasDerivAt (F := E [⋀^Fin k]→L[ℝ] F) (fun u ↦ mpullback I I (φ u) α x)
      (mpullback I I (φ t) (mlieDerivForm (eulerianVelocity φ t) α) x) t := by
  have hn₀ : n ≠ 0 := by
    rintro rfl
    simp at hn
  have hφ₁ : MDifferentiable (𝓘(ℝ, ℝ).prod I) I fun p : ℝ × M ↦ φ p.1 p.2 :=
    hφ.mdifferentiable two_ne_zero
  -- The family `u ↦ φ_u ∘ φ_t⁻¹` is the identity at time `t` and moves with velocity `X_t`.
  set ψ : ℝ → M → M := fun u z ↦ φ u ((φ t).symm z) with hψ
  have hd := hasDerivAt_mpullback_of_eq_id (ψ := ψ) (V := eulerianVelocity φ t) (φ t x)
    (Eventually.of_forall fun z ↦ (φ t).apply_symm_apply z)
    (hφ.comp (contMDiff_fst.prodMk (((φ t).symm.contMDiff.of_le hn).comp
      contMDiff_snd))).contMDiffAt
    (Eventually.of_forall fun z ↦ hasMFDerivAt_eulerianVelocity
      ((hφ₁ (t, (φ t).symm z)).comp t (mdifferentiableAt_id.prodMk mdifferentiableAt_const))) hα
  set L : E →L[ℝ] E := mfderiv I I (φ t) x
  -- Since `φ_u = ψ_u ∘ φ_t`, the pullback by `φ_u` at `x` is the pullback by `ψ_u` at `φ_t x`,
  -- precomposed with `dφ_t`.
  have hshift (u : ℝ) : mpullback I I (φ u) α x =
      compContinuousLinearMapCLM (ι := Fin k) (F := F) L (mpullback I I (ψ u) α (φ t x)) := by
    have hcomp : (φ u : M → M) = ψ u ∘ φ t := funext fun z ↦ by simp [hψ]
    rw [hcomp, mpullback_comp_at (g := ψ u) (((φ t).mdifferentiable hn₀) x)
      ((((φ u).mdifferentiable hn₀) _).comp _ (((φ t).symm.mdifferentiable hn₀) _))]
    exact mpullback_apply_eq_compContinuousLinearMap _ _ _
  have h := (compContinuousLinearMapCLM (ι := Fin k) (F := F) L).hasFDerivAt.comp_hasDerivAt t hd
  refine (h.congr_of_eventuallyEq (Eventually.of_forall fun u ↦ hshift u)).congr_deriv ?_
  exact (mpullback_apply_eq_compContinuousLinearMap _ _ _).symm

/-- **Forms moved by an isotopy.** For a jointly `C²` family `φ` of `C^n` diffeomorphisms,
`2 ≤ n`, and a differentiable form `α`, the pullbacks `φ_t^* α` do not depend on `t` exactly when
the Lie derivative of `α` along the Eulerian field `X_t` vanishes at every time `t`. -/
theorem forall_mpullback_eq_mpullback_iff_mlieDerivForm_eulerianVelocity_eq_zero (hn : 2 ≤ n)
    (hφ : ContMDiff (𝓘(ℝ, ℝ).prod I) I 2 fun p : ℝ × M ↦ φ p.1 p.2) {α : RoughForm I M F k}
    (hα : MDifferentiable I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F))
      (fun z ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) z (α z))) :
    (∀ s t, mpullback I I (φ s) α = mpullback I I (φ t) α) ↔
      ∀ t, mlieDerivForm (eulerianVelocity φ t) α = 0 := by
  constructor
  · -- The pullbacks are constant, so their velocity `φ_t^* L_{X_t} α` vanishes; pullback by the
    -- diffeomorphism `φ_t` is injective.
    intro h t
    refine mpullback_injective_of_surjective (I := I) (I' := I) (f := (φ t : M → M))
      (φ t).surjective
      (fun x ↦ by
        rw [← Diffeomorph.mfderivToContinuousLinearEquiv_coe (φ t) (by rintro rfl; simp at hn)]
        exact ContinuousLinearEquiv.surjective _) ?_
    rw [mpullback_zero]
    funext x
    have hd := hasDerivAt_mpullback_eulerianVelocity hn hφ t x (hα _)
    have hconst : (fun u ↦ mpullback I I (φ u) α x) = fun _ ↦ mpullback I I (φ t) α x :=
      funext fun u ↦ congrFun (h u t) x
    rw [hconst] at hd
    exact hd.unique (hasDerivAt_const (F := E [⋀^Fin k]→L[ℝ] F) t _)
  · -- With vanishing Lie derivatives, the pullbacks at each point have zero velocity.
    intro h s t
    funext x
    set P : ℝ → E [⋀^Fin k]→L[ℝ] F := fun u ↦ mpullback I I (φ u) α x
    have hderiv (u : ℝ) : HasDerivAt P 0 u := by
      have hd := hasDerivAt_mpullback_eulerianVelocity hn hφ u x (hα _)
      rwa [h u, mpullback_zero] at hd
    exact is_const_of_deriv_eq_zero (fun u ↦ (hderiv u).differentiableAt)
      (fun u ↦ (hderiv u).deriv) s t

/-- **Isotopies preserving a closed form.** Let `φ` be a jointly `C²` family of `C^n`
diffeomorphisms, `2 ≤ n`, with `φ_{t₀}^* β = β` for one time `t₀`, and `β` a closed form. Then
`φ_t^* β = β` for every `t` exactly when every contraction `ι_{X_t} β` with the Eulerian field is
closed, by Cartan's formula
`L_{X_t} β = d(ι_{X_t} β)`. For a symplectic form and an isotopy starting at the identity, this
characterizes symplectic isotopies by the closedness of the one-forms `ι_{X_t} ω`. -/
theorem forall_mpullback_eq_self_iff_mextDeriv_interior_eulerianVelocity_eq_zero
    (hn : 2 ≤ n) (hφ : ContMDiff (𝓘(ℝ, ℝ).prod I) I 2 fun p : ℝ × M ↦ φ p.1 p.2)
    {β : SmoothForm I M F (k + 1)} (hβ : β.IsClosed) {t₀ : ℝ}
    (h₀ : mpullback (F := F) I I (φ t₀) β.1 = β.1) :
    (∀ t, mpullback (F := F) I I (φ t) β.1 = β.1) ↔
      ∀ t, mextDeriv (RoughForm.interior (eulerianVelocity φ t) β.1) = 0 := by
  have hcartan (t : ℝ) : mlieDerivForm (eulerianVelocity φ t) β.1 =
      mextDeriv (RoughForm.interior (eulerianVelocity φ t) β.1) :=
    SmoothForm.mlieDerivForm_eq_mextDeriv_interior
      ((contMDiff_eulerianVelocity (m := 1) hφ le_rfl (one_le_two.trans hn) t).mdifferentiable
        one_ne_zero) hβ
  simp only [← hcartan]
  rw [← forall_mpullback_eq_mpullback_iff_mlieDerivForm_eulerianVelocity_eq_zero hn hφ
    β.mdifferentiable]
  exact ⟨fun h s t ↦ by rw [h s, h t], fun h t ↦ by rw [h t t₀, h₀]⟩

end TauCeti
