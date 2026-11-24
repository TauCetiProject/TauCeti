/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.ActionAngle.Basic
public import TauCeti.Geometry.Symplectic.Hamiltonian.Manifold

import Mathlib.Analysis.Calculus.Deriv.Prod
import TauCeti.Geometry.Manifold.MFDeriv.Curve
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Hamiltonian vector fields in action–angle coordinates

Let `p > 0` and let `Tⁿ = ι → AddCircle p`. A covector `ξ` of the torus over `[θ]` has
**actions** `I_j = ξ(e_j)` (`TauCeti.CotangentBundle.torusActions`), and in the action–angle
coordinates `κ(θ, I) = ∑ j, I_j dθ_j` (`TauCeti.CotangentBundle.actionAngleCover`) the canonical
symplectic form of `T*Tⁿ` is `ω = ∑ j, dθ_j ∧ dI_j`. The action map is smooth, since its composite
with the surjective local diffeomorphism `κ` is the projection `(θ, I) ↦ I`.

A Hamiltonian that depends on the actions alone, `H = h(I)`, therefore has the Hamiltonian vector
field (for the convention `ι_{X_H} ω = dH`)

`X_H = ∑ j, (∂h / ∂I_j) ∂θ_j`

(`TauCeti.CotangentBundle.hamiltonianVectorField_comp_torusActions_actionAngleCover`): it moves the
angles with the constant frequencies `∂h / ∂I_j` and fixes the actions. Its integral curves are the
linear motions `t ↦ κ(θ + t ∇h(I), I)` on the invariant tori of constant action
(`TauCeti.CotangentBundle.isMIntegralCurve_actionAngleCover_add_smul`); in particular the flow of
`X_H` is complete. Only differentiability of `h` at the actions in question is needed.

The same formula holds in every action–angle chart. If a map `Φ` from a manifold with a
nondegenerate two-form `σ` to `T*Tⁿ` is a local diffeomorphism at `y`, preserves the symplectic
forms there, and a function `f` agrees near `y` with `h ∘ torusActions ∘ Φ`, then the differential
of `Φ` carries the Hamiltonian vector field of `f` at `y` to `∑ j, (∂h / ∂I_j) ∂θ_j`
(`TauCeti.CotangentBundle.mfderiv_hamiltonianVectorField_eq_mfderiv_actionAngleCover`). This is the
form in which the Liouville–Arnold theorem describes the motion of an integrable system near a
compact regular level.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Sections 49–50 (the equations of motion in action–angle
  variables).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 18.4.
-/

public section

noncomputable section

open Bundle Function Filter
open scoped Manifold ContDiff Topology

namespace TauCeti

namespace CotangentBundle

variable (p : ℝ) [Fact (0 < p)] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Hamiltonian vector fields of functions of the actions -/

/-- The value of `d(h ∘ I)` on the image of a tangent vector `u` under the differential of the
action–angle covering map: the derivative of `h` in the action component of `u`. -/
private theorem mvfderiv_comp_torusActions_mfderiv_actionAngleCover {h : (ι → ℝ) → ℝ}
    {x : (ι → ℝ) × (ι → ℝ)} (hh : DifferentiableAt ℝ h x.2)
    (u : TangentSpace 𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) x) :
    mvfderiv ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
        (h ∘ torusActions p) (actionAngleCover p x)
        (mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
          ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
          (actionAngleCover p) x u) =
      fderiv ℝ h x.2 u.2 := by
  have hκ := (contMDiff_actionAngleCover (ι := ι) p x).mdifferentiableAt (by simp)
  have hH := mdifferentiableAt_comp_torusActions p (z := actionAngleCover p x)
    ((torusActions_actionAngleCover p x).symm ▸ hh)
  rw [← mvfderiv_comp_apply x hH hκ u, comp_assoc, torusActions_comp_actionAngleCover,
    mvfderiv_eq_fderiv_apply, (hh.hasFDerivAt.comp x hasFDerivAt_snd).fderiv]
  -- The tangent space of the model `ℝ^ι × ℝ^ι` is that space itself, so `u` is its own pair of
  -- coordinates and `(dh ∘ snd) u` is `dh (u.2)`; the generic rewrites cannot see through it.
  exact ContinuousLinearMap.comp_apply _ _ _

/-- **Hamilton's equations in action–angle coordinates.** For a Hamiltonian `H = h(I)` that depends
on the actions alone, the Hamiltonian vector field at `κ(θ, I)` is
`∑ j, (∂h / ∂I_j) ∂θ_j`: it moves the angles with the frequencies `∂h / ∂I_j` and fixes the
actions. -/
theorem hamiltonianVectorField_comp_torusActions_actionAngleCover {h : (ι → ℝ) → ℝ}
    {x : (ι → ℝ) × (ι → ℝ)} (hh : DifferentiableAt ℝ h x.2) :
    (symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p)).hamiltonianVectorField
        (h ∘ torusActions p) (actionAngleCover p x) =
      mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
        ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
        (actionAngleCover p) x (fun j ↦ fderiv ℝ h x.2 (Pi.single j 1), 0) := by
  have hω := (isSymplectic_symplecticForm (I := ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
    (M := ι → AddCircle p)).isNondegenerate
  have hsurj := ((isLocalDiffeomorph_actionAngleCover (ι := ι) p x).isInvertible_mfderiv
    (by simp)).surjective
  -- Both vectors have the same contraction with `ω`, which is nondegenerate.
  refine (hω.isInvertible_flat _).injective (ContinuousLinearMap.ext fun w ↦ ?_)
  obtain ⟨u, rfl⟩ := hsurj w
  rw [hω.flat_hamiltonianVectorField, SmoothTwoForm.flat_apply]
  refine (mvfderiv_comp_torusActions_mfderiv_actionAngleCover p hh u).trans
    (Eq.trans ?_ (eval₂_symplecticForm_mfderiv_actionAngleCover p x _ u).symm)
  -- `dh(u₂) = ∑ j, (∂h / ∂I_j) u₂ⱼ`, by expanding `u₂` in the standard basis.
  refine (LinearMap.pi_apply_eq_sum_univ (fderiv ℝ h x.2 : (ι → ℝ) →ₗ[ℝ] ℝ) _).trans
    (Finset.sum_congr rfl fun j _ ↦ ?_)
  have hj : (fun k ↦ if j = k then (1 : ℝ) else 0) = Pi.single j 1 :=
    funext fun k ↦ by simp [Pi.single_apply, eq_comm]
  simp [hj, mul_comm]

/-- **The motions of a Hamiltonian of the actions are linear on the invariant tori.** For
`H = h(I)`, the curve `t ↦ κ(θ + t ∇h(I), I)`, which keeps the actions `I` and turns the angles
with the constant frequencies `∂h / ∂I_j`, is an integral curve of the Hamiltonian vector field
of `H`. -/
theorem isMIntegralCurve_actionAngleCover_add_smul {h : (ι → ℝ) → ℝ} (θ I : ι → ℝ)
    (hh : DifferentiableAt ℝ h I) :
    IsMIntegralCurve
      (fun t ↦ actionAngleCover p (θ + t • fun j ↦ fderiv ℝ h I (Pi.single j 1), I))
      ((symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
        (ι → AddCircle p)).hamiltonianVectorField (h ∘ torusActions p)) := by
  rw [Manifold.isMIntegralCurve_iff_curveVelocity_eq]
  intro t
  set a : ι → ℝ := fun j ↦ fderiv ℝ h I (Pi.single j 1)
  have hline : HasDerivAt (fun t : ℝ ↦ (θ + t • a, I)) (a, 0) t := by
    simpa using HasDerivAt.prodMk (((hasDerivAt_id t).smul_const a).const_add θ)
      (hasDerivAt_const t I)
  have hκ := (contMDiff_actionAngleCover (ι := ι) p (θ + t • a, I)).mdifferentiableAt (by simp)
  refine ⟨hκ.comp t hline.differentiableAt.mdifferentiableAt, ?_⟩
  -- The velocity of `κ` along the line is `dκ (∇h(I), 0)`, which is `X_H` there.
  exact (hκ.curveVelocity_comp_mfderiv hline).trans
    (hamiltonianVectorField_comp_torusActions_actionAngleCover (x := (θ + t • a, I)) p hh).symm

/-- **The Hamiltonian vector field of a function of the actions is complete.** Through a
covector `z` of the torus, at whose actions `h` is differentiable, passes an integral curve
defined for all times. -/
theorem exists_isMIntegralCurve_hamiltonianVectorField_comp_torusActions {h : (ι → ℝ) → ℝ}
    {z : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p)}
    (hh : DifferentiableAt ℝ h (torusActions p z)) :
    ∃ γ : ℝ → CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p),
      γ 0 = z ∧ IsMIntegralCurve γ
        ((symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
          (ι → AddCircle p)).hamiltonianVectorField (h ∘ torusActions p)) := by
  obtain ⟨⟨θ, I⟩, rfl⟩ := surjective_actionAngleCover (ι := ι) p z
  rw [torusActions_actionAngleCover] at hh
  exact ⟨_, by simp, isMIntegralCurve_actionAngleCover_add_smul p θ I hh⟩

/-! ### Action–angle charts -/

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {σ : SmoothTwoForm I M}

/-- **Hamilton's equations in an action–angle chart.** Let `Φ` map a manifold with a
nondegenerate two-form `σ` into the cotangent bundle of the torus, be a local diffeomorphism at
`y` and carry `σ` at `y` to the canonical form `ω`. If `f` agrees near `y` with a function `h` of
the actions of `Φ`, then the differential of `Φ` carries the Hamiltonian vector field of `f` at `y`
to `∑ j, (∂h / ∂I_j) ∂θ_j` at `Φ y = κ(θ, I)`. -/
theorem mfderiv_hamiltonianVectorField_eq_mfderiv_actionAngleCover (hσ : σ.IsNondegenerate)
    {Φ : M → CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p)} {y : M}
    (hΦ : IsLocalDiffeomorphAt I
      ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) ∞ Φ y)
    (hΦσ : ∀ v w : TangentSpace I y,
      SmoothBundleForm.eval₂
          (symplecticForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p)) (Φ y)
          (mfderiv I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
            Φ y v)
          (mfderiv I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
            Φ y w) =
        SmoothBundleForm.eval₂ σ y v w)
    {f : M → ℝ} {h : (ι → ℝ) → ℝ} (hf : f =ᶠ[𝓝 y] h ∘ torusActions p ∘ Φ)
    {x : (ι → ℝ) × (ι → ℝ)} (hx : actionAngleCover p x = Φ y) (hh : DifferentiableAt ℝ h x.2) :
    mfderiv I ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) Φ y
        (σ.hamiltonianVectorField f y) =
      mfderiv 𝓘(ℝ, (ι → ℝ) × (ι → ℝ))
        ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ))
        (actionAngleCover p) x (fun j ↦ fderiv ℝ h x.2 (Pi.single j 1), 0) := by
  have hω := (isSymplectic_symplecticForm (I := ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
    (M := ι → AddCircle p)).isNondegenerate
  have hH := mdifferentiableAt_comp_torusActions p (z := Φ y)
    (by rwa [← hx, torusActions_actionAngleCover])
  rw [← hamiltonianVectorField_comp_torusActions_actionAngleCover p hh, hx]
  -- `dΦ_y` is a linear symplectic isomorphism carrying `df_y` to `d(h ∘ I)` at `Φ y`.
  refine hσ.map_hamiltonianVectorField_of_eval₂ hω
    ((hΦ.isInvertible_mfderiv (by simp)).surjective _) hΦσ fun u ↦ ?_
  rw [hf.mvfderiv_eq, ← comp_assoc, mvfderiv_comp_apply y hH (hΦ.mdifferentiableAt (by simp))]

end CotangentBundle

end TauCeti
