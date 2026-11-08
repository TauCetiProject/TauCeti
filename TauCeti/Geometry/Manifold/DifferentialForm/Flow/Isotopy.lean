/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Flow
public import TauCeti.Geometry.Manifold.MFDeriv.Curve
import TauCeti.Geometry.Manifold.MFDeriv.Parametric.Basic

/-!
# Eulerian velocity fields of isotopies and the forms they move

Let `φ : ℝ → (M ≃ₘ M)` be a family of diffeomorphisms of a manifold which is jointly smooth in
time and space. Its **Eulerian velocity field** at time `t` is the vector field

`X_t = (∂_t φ_t) ∘ φ_t⁻¹`, that is `X_t (φ_t x) = d/du|_{u = t} φ_u x`

(`TauCeti.eulerianVelocity`). Unlike the velocity `u ↦ ∂_u φ_u x` of the individual trajectories,
it is a vector field on `M` at each time, and the trajectories `u ↦ φ_u x` are integral curves of
the time-dependent field `X` (`TauCeti.hasMFDerivAt_eulerianVelocity`). For every time `t`, `X_t`
is `C^m` when `φ` is jointly `C^(m + 1)` (`TauCeti.contMDiff_eulerianVelocity`).

The Eulerian field controls how pulled-back forms move. For a form `α`,

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

The Eulerian field of the pointwise composite `(φ ψ)_t = φ_t ∘ ψ_t` of two isotopies is

`X_{φ ψ, t} = X_{φ, t} + (φ_t)_* X_{ψ, t}`

(`TauCeti.eulerianVelocity_trans`), where the pushforward is evaluated at `y` as
`(dφ_t) X_{ψ, t} (φ_t⁻¹ y)`. This pointwise product is not the concatenation of paths. Two
consequences follow from it, since a constant family has zero Eulerian field: the inverse family
`φ_t⁻¹` has Eulerian field `-(φ_t⁻¹)_* X_{φ, t}` (`TauCeti.eulerianVelocity_symm`), and the
conjugate family `g⁻¹ ∘ φ_t ∘ g` by a fixed diffeomorphism `g` has Eulerian field `g^* X_{φ, t}`
(`TauCeti.eulerianVelocity_conj`).

## Main definitions

* `TauCeti.eulerianVelocity φ t`: the Eulerian velocity field `(∂_t φ_t) ∘ φ_t⁻¹`.

## Main results

* `TauCeti.hasMFDerivAt_eulerianVelocity`: the trajectories of `φ` are integral curves of its
  Eulerian field.
* `TauCeti.contMDiff_eulerianVelocity`: the Eulerian field at each time is `C^m` when `φ` is
  jointly `C^(m + 1)`.
* `TauCeti.eulerianVelocity_trans`: the product formula for the Eulerian field of a composite.
* `TauCeti.eulerianVelocity_symm`, `TauCeti.eulerianVelocity_conj`: the Eulerian fields of the
  inverse and of a conjugate isotopy.
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

open TauCeti.Manifold (curveVelocity hasMFDerivAt_curveVelocity)

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}
  {φ ψ : ℝ → M ≃ₘ⟮I, I⟯ M}

/-! ### The Eulerian velocity field -/

/-- The **Eulerian velocity field** `X_t = (∂_t φ_t) ∘ φ_t⁻¹` of a family `φ` of diffeomorphisms
at time `t`: at `y`, it is the velocity at time `t` of the trajectory `u ↦ φ_u (φ_t⁻¹ y)` through
`y`. -/
def eulerianVelocity (φ : ℝ → M ≃ₘ⟮I, I⟯ M) (t : ℝ) (y : M) : TangentSpace I y :=
  curveVelocity I (fun u ↦ φ u ((φ t).symm y)) t

/-- At the point `φ_t x`, the Eulerian field is the velocity of the trajectory of `x`. -/
theorem eulerianVelocity_apply_apply (t : ℝ) (x : M) :
    eulerianVelocity φ t (φ t x) = curveVelocity I (fun u ↦ φ u x) t := by
  rw [eulerianVelocity, Diffeomorph.symm_apply_apply]

/-- The Eulerian field at `y` is the velocity of the trajectory of `φ_t⁻¹ y`. This restates the
definition, whose body is not exposed across the module boundary. -/
theorem eulerianVelocity_apply (t : ℝ) (y : M) :
    eulerianVelocity φ t y = curveVelocity I (fun u ↦ φ u ((φ t).symm y)) t :=
  (rfl)

/-- A constant family of diffeomorphisms has zero Eulerian field. -/
@[simp]
theorem eulerianVelocity_const (f : M ≃ₘ⟮I, I⟯ M) (t : ℝ) :
    eulerianVelocity (fun _ ↦ f) t = 0 := by
  funext y
  exact TauCeti.Manifold.curveVelocity_const _

/-- **The trajectories of an isotopy are integral curves of its Eulerian field.** If the trajectory
`u ↦ φ_u x` is differentiable at `t`, its velocity there is `X_t (φ_t x)`. -/
theorem hasMFDerivAt_eulerianVelocity {t : ℝ} {x : M}
    (hφ : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun u ↦ φ u x) t) :
    HasMFDerivAt 𝓘(ℝ, ℝ) I (fun u ↦ φ u x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (eulerianVelocity φ t (φ t x))) := by
  rw [eulerianVelocity_apply_apply]
  exact hasMFDerivAt_curveVelocity hφ

/-- **The Eulerian field of a composite isotopy.** For jointly differentiable families `φ` and
`ψ`, the Eulerian field of the pointwise composite `(φ ψ)_t = φ_t ∘ ψ_t` is
`X_{φ ψ} = X_φ + (φ_t)_* X_ψ`. It is stated at the point `φ_t (ψ_t z)`, where the pushforward of
`X_ψ` is the differential of `φ_t` at `ψ_t z` applied to `X_ψ (ψ_t z)`. -/
theorem eulerianVelocity_trans
    (hφ : MDifferentiable (𝓘(ℝ, ℝ).prod I) I fun p : ℝ × M ↦ φ p.1 p.2)
    (hψ : MDifferentiable (𝓘(ℝ, ℝ).prod I) I fun p : ℝ × M ↦ ψ p.1 p.2) (t : ℝ) (z : M) :
    eulerianVelocity (fun u ↦ (ψ u).trans (φ u)) t (φ t (ψ t z)) =
      eulerianVelocity φ t (φ t (ψ t z)) +
        mfderiv I I (φ t) (ψ t z) (eulerianVelocity ψ t (ψ t z)) := by
  have hψz : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun u ↦ ψ u z) t :=
    (hψ (t, z)).comp t (mdifferentiableAt_id.prodMk mdifferentiableAt_const)
  set v : E := curveVelocity I (fun u ↦ ψ u z) t
  set D := mfderiv (𝓘(ℝ, ℝ).prod I) I (fun p : ℝ × M ↦ φ p.1 p.2) (t, ψ t z)
  -- The trajectory `u ↦ φ_u (ψ_u z)` is the family `φ` read along `u ↦ (u, ψ_u z)`, whose
  -- velocity is `(1, v)`.
  have hcomp : curveVelocity I (fun u ↦ φ u (ψ u z)) t = D ((1 : ℝ), v) := by
    have hd := (hφ (t, ψ t z)).hasMFDerivAt.comp t
      ((hasMFDerivAt_id (I := 𝓘(ℝ, ℝ)) t).prodMk (hasMFDerivAt_curveVelocity hψz))
    rw [TauCeti.Manifold.curveVelocity_apply,
      show (fun u ↦ φ u (ψ u z)) = (fun p : ℝ × M ↦ φ p.1 p.2) ∘ fun u ↦ (id u, ψ u z) from rfl,
      hd.mfderiv]
    -- The derivative of `u ↦ (u, ψ_u z)` sends `1` to `(1, v)`; the tangent spaces involved are
    -- the model spaces only up to unfolding.
    change D ((1 : ℝ), (1 : ℝ) • v) = D ((1 : ℝ), v)
    rw [one_smul]
  -- The total derivative of the family splits into its partial derivatives in time and space.
  have hsplit : D ((1 : ℝ), v) =
      mfderiv 𝓘(ℝ, ℝ) I (fun u ↦ φ u (ψ t z)) t (1 : ℝ) + mfderiv I I (φ t) (ψ t z) v :=
    mfderiv_prod_eq_add_apply (hφ _)
  have htrans := eulerianVelocity_apply_apply (φ := fun u ↦ (ψ u).trans (φ u)) t z
  simp only [Diffeomorph.coe_trans, Function.comp_apply] at htrans
  rw [htrans, hcomp, hsplit, ← TauCeti.Manifold.curveVelocity_apply, eulerianVelocity_apply_apply,
    eulerianVelocity_apply_apply]

/-- **The Eulerian field of the inverse isotopy.** If `φ` and the family of inverses `φ_t⁻¹` are
jointly differentiable, the Eulerian field of the inverse family is `-(φ_t⁻¹)_* X_{φ, t}`: at
`φ_t⁻¹ y` it is the differential of `φ_t⁻¹` at `y` applied to `-X_{φ, t} y`. -/
theorem eulerianVelocity_symm
    (hφ : MDifferentiable (𝓘(ℝ, ℝ).prod I) I fun p : ℝ × M ↦ φ p.1 p.2)
    (hφ' : MDifferentiable (𝓘(ℝ, ℝ).prod I) I fun p : ℝ × M ↦ (φ p.1).symm p.2) (t : ℝ) (y : M) :
    eulerianVelocity (fun u ↦ (φ u).symm) t ((φ t).symm y) =
      -mfderiv I I (φ t).symm y (eulerianVelocity φ t y) := by
  -- The composite `φ_u⁻¹ ∘ φ_u` is the identity, whose Eulerian field vanishes.
  have h := eulerianVelocity_trans (φ := fun u ↦ (φ u).symm) (ψ := φ) hφ' hφ t ((φ t).symm y)
  simp only [Diffeomorph.self_trans_symm, eulerianVelocity_const, Pi.zero_apply] at h
  rw [Diffeomorph.apply_symm_apply] at h
  exact eq_neg_of_add_eq_zero_left h.symm

/-- **The Eulerian field of a conjugate isotopy.** For a jointly differentiable family `φ` and a
diffeomorphism `g`, the Eulerian field of the conjugate family `g⁻¹ ∘ φ_t ∘ g` is the pullback
`g^* X_{φ, t}`: at `g⁻¹ (φ_t (g z))` it is the differential of `g⁻¹` applied to
`X_{φ, t} (φ_t (g z))`. -/
theorem eulerianVelocity_conj
    (hφ : MDifferentiable (𝓘(ℝ, ℝ).prod I) I fun p : ℝ × M ↦ φ p.1 p.2)
    (g : M ≃ₘ⟮I, I⟯ M) (t : ℝ) (z : M) :
    eulerianVelocity (fun u ↦ (g.trans (φ u)).trans g.symm) t (g.symm (φ t (g z))) =
      mfderiv I I g.symm (φ t (g z)) (eulerianVelocity φ t (φ t (g z))) := by
  have hg : MDifferentiable (𝓘(ℝ, ℝ).prod I) I fun p : ℝ × M ↦ g p.2 :=
    (g.mdifferentiable (by simp)).comp mdifferentiable_snd
  have hg' : MDifferentiable (𝓘(ℝ, ℝ).prod I) I fun p : ℝ × M ↦ g.symm p.2 :=
    (g.symm.mdifferentiable (by simp)).comp mdifferentiable_snd
  have hφg : MDifferentiable (𝓘(ℝ, ℝ).prod I) I fun p : ℝ × M ↦ (g.trans (φ p.1)) p.2 :=
    hφ.comp (mdifferentiable_fst.prodMk hg)
  -- First `X_{φ ∘ g} = X_φ`, since the constant family `g` has zero Eulerian field.
  have h₁ := eulerianVelocity_trans (φ := φ) (ψ := fun _ ↦ g) hφ hg t z
  simp only [eulerianVelocity_const, Pi.zero_apply, _root_.map_zero] at h₁
  -- Then `X_{g⁻¹ ∘ (φ ∘ g)} = (g⁻¹)_* X_{φ ∘ g}`, since `g⁻¹` is constant too.
  have h₂ := eulerianVelocity_trans (φ := fun _ ↦ g.symm) (ψ := fun u ↦ g.trans (φ u)) hg' hφg t z
  simp only [eulerianVelocity_const, Pi.zero_apply, Diffeomorph.coe_trans,
    Function.comp_apply] at h₂ h₁
  have h₁' : eulerianVelocity (fun u ↦ g.trans (φ u)) t (φ t (g z)) =
      eulerianVelocity φ t (φ t (g z)) := by
    rw [h₁]
    exact add_zero _
  rw [h₂, h₁']
  exact zero_add _

variable [IsManifold I 1 M]

/-- **Regularity of the Eulerian field.** If the family `φ` is jointly `C^n`, its Eulerian field at
each time is a `C^m` vector field for every `m` with `m + 1 ≤ n`. -/
theorem contMDiff_eulerianVelocity {m : ℕ∞} {n : WithTop ℕ∞}
    (hφ : ContMDiff (𝓘(ℝ, ℝ).prod I) I n fun p : ℝ × M ↦ φ p.1 p.2) (hmn : m + 1 ≤ n) (t : ℝ) :
    ContMDiff I I.tangent m fun y ↦ (⟨y, eulerianVelocity φ t y⟩ : TangentBundle I M) := by
  have hn : n ≠ 0 := by
    rintro rfl
    exact absurd hmn (by simp)
  have hvel := TauCeti.Manifold.contMDiff_mfderiv_apply_one_zero hφ hmn
  -- The section is the velocity of the family read along `y ↦ (t, φ_t⁻¹ y)`.
  have hsec : (fun y ↦ (⟨y, eulerianVelocity φ t y⟩ : TangentBundle I M)) =
      (fun q : ℝ × M ↦ TotalSpace.mk' E (φ q.1 q.2)
        (mfderiv (𝓘(ℝ, ℝ).prod I) I (fun p : ℝ × M ↦ φ p.1 p.2) q ((1 : ℝ), (0 : E)))) ∘
        fun y ↦ (t, (φ t).symm y) := by
    funext y
    have hd := (hφ.mdifferentiable hn) (t, (φ t).symm y)
    -- The time-direction partial derivative of the family is the velocity of the trajectory.
    have hsplit : mfderiv (𝓘(ℝ, ℝ).prod I) I (fun p : ℝ × M ↦ φ p.1 p.2) (t, (φ t).symm y)
        ((1 : ℝ), (0 : E)) = mfderiv 𝓘(ℝ, ℝ) I (fun u ↦ φ u ((φ t).symm y)) t (1 : ℝ) +
          mfderiv I I (φ t) ((φ t).symm y) 0 :=
      mfderiv_prod_eq_add_apply hd
    rw [Function.comp_apply, hsplit, _root_.map_zero, add_zero,
      ← TauCeti.Manifold.curveVelocity_apply, ← eulerianVelocity_apply]
    exact congrArg (fun z ↦ TotalSpace.mk' E z (eulerianVelocity φ t y))
      ((φ t).apply_symm_apply y).symm
  rw [hsec]
  exact hvel.comp (contMDiff_const.prodMk ((φ t).symm.contMDiff.of_le (by exact_mod_cast le_top)))

/-! ### Pulled-back forms -/

section Pullback

variable [I.Boundaryless] [IsManifold I 2 M]

/-- **Pullbacks along an isotopy move with the Lie derivative along its Eulerian field.** For a
jointly `C²` family `φ` of diffeomorphisms and a form `α` differentiable at `φ_t x`, the pullbacks
`(φ_u^* α)ₓ` have velocity `(φ_t^* L_{X_t} α)ₓ` at time `t`, where `X_t` is the Eulerian field. -/
theorem hasDerivAt_mpullback_eulerianVelocity
    (hφ : ContMDiff (𝓘(ℝ, ℝ).prod I) I 2 fun p : ℝ × M ↦ φ p.1 p.2) {α : RoughForm I M F k}
    (t : ℝ) (x : M)
    (hα : MDifferentiableAt I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F))
      (fun z ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) z (α z)) (φ t x)) :
    HasDerivAt (F := E [⋀^Fin k]→L[ℝ] F) (fun u ↦ mpullback I I (φ u) α x)
      (mpullback I I (φ t) (mlieDerivForm (eulerianVelocity φ t) α) x) t := by
  have hφ₁ : MDifferentiable (𝓘(ℝ, ℝ).prod I) I fun p : ℝ × M ↦ φ p.1 p.2 :=
    hφ.mdifferentiable two_ne_zero
  -- The family `u ↦ φ_u ∘ φ_t⁻¹` is the identity at time `t` and moves with velocity `X_t`.
  set ψ : ℝ → M → M := fun u z ↦ φ u ((φ t).symm z) with hψ
  have hd := hasDerivAt_mpullback_of_eq_id (ψ := ψ) (V := eulerianVelocity φ t) (φ t x)
    (Eventually.of_forall fun z ↦ (φ t).apply_symm_apply z)
    (hφ.comp (contMDiff_fst.prodMk (((φ t).symm.contMDiff.of_le
      (by norm_cast)).comp contMDiff_snd))).contMDiffAt
    (Eventually.of_forall fun z ↦ hasMFDerivAt_eulerianVelocity
      ((hφ₁ (t, (φ t).symm z)).comp t (mdifferentiableAt_id.prodMk mdifferentiableAt_const))) hα
  set L : E →L[ℝ] E := mfderiv I I (φ t) x
  -- Since `φ_u = ψ_u ∘ φ_t`, the pullback by `φ_u` at `x` is the pullback by `ψ_u` at `φ_t x`,
  -- precomposed with `dφ_t`.
  have hshift (u : ℝ) : mpullback I I (φ u) α x =
      compContinuousLinearMapCLM (ι := Fin k) (F := F) L (mpullback I I (ψ u) α (φ t x)) := by
    have hcomp : (φ u : M → M) = ψ u ∘ φ t := funext fun z ↦ by simp [hψ]
    rw [hcomp, mpullback_comp_at (g := ψ u) (((φ t).mdifferentiable (by simp)) x)
      ((((φ u).mdifferentiable (by simp)) _).comp _ (((φ t).symm.mdifferentiable (by simp)) _))]
    ext v
    -- As in `TauCeti.hasDerivAt_mpullback_timeDependentFlowOf`, the pulled-back form takes values
    -- on tangent spaces, which are `E` only up to unfolding.
    rw [mpullback_apply]
    rfl
  have h := (compContinuousLinearMapCLM (ι := Fin k) (F := F) L).hasFDerivAt.comp_hasDerivAt t hd
  refine (h.congr_of_eventuallyEq (Eventually.of_forall fun u ↦ hshift u)).congr_deriv ?_
  ext v
  exact (mpullback_apply (φ t) (mlieDerivForm (eulerianVelocity φ t) α) x v).symm

/-- **Forms moved by an isotopy.** For a jointly `C²` family `φ` of diffeomorphisms and a
differentiable form `α`, the pullbacks `φ_t^* α` do not depend on `t` exactly when the Lie
derivative of `α` along the Eulerian field `X_t` vanishes at every time `t`. -/
theorem forall_mpullback_eq_mpullback_iff_mlieDerivForm_eulerianVelocity_eq_zero
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
        rw [← Diffeomorph.mfderivToContinuousLinearEquiv_coe (φ t) (by simp)]
        exact ContinuousLinearEquiv.surjective _) ?_
    rw [mpullback_zero]
    funext x
    have hd := hasDerivAt_mpullback_eulerianVelocity hφ t x (hα _)
    have hconst : (fun u ↦ mpullback I I (φ u) α x) = fun _ ↦ mpullback I I (φ t) α x :=
      funext fun u ↦ congrFun (h u t) x
    rw [hconst] at hd
    exact hd.unique (hasDerivAt_const (F := E [⋀^Fin k]→L[ℝ] F) t _)
  · -- With vanishing Lie derivatives, the pullbacks at each point have zero velocity.
    intro h s t
    funext x
    set P : ℝ → E [⋀^Fin k]→L[ℝ] F := fun u ↦ mpullback I I (φ u) α x
    have hderiv (u : ℝ) : HasDerivAt P 0 u := by
      have hd := hasDerivAt_mpullback_eulerianVelocity hφ u x (hα _)
      rwa [h u, mpullback_zero] at hd
    exact is_const_of_deriv_eq_zero (fun u ↦ (hderiv u).differentiableAt)
      (fun u ↦ (hderiv u).deriv) s t

/-- **Isotopies preserving a closed form.** Let `φ` be a jointly `C²` family of diffeomorphisms
with `φ_{t₀}^* β = β` for one time `t₀`, and `β` a closed form. Then `φ_t^* β = β` for every `t`
exactly when every contraction `ι_{X_t} β` with the Eulerian field is closed, by Cartan's formula
`L_{X_t} β = d(ι_{X_t} β)`. For a symplectic form and an isotopy starting at the identity, this
characterizes symplectic isotopies by the closedness of the one-forms `ι_{X_t} ω`. -/
theorem forall_mpullback_eq_self_iff_mextDeriv_interior_eulerianVelocity_eq_zero
    (hφ : ContMDiff (𝓘(ℝ, ℝ).prod I) I 2 fun p : ℝ × M ↦ φ p.1 p.2)
    {β : SmoothForm I M F (k + 1)} (hβ : β.IsClosed) {t₀ : ℝ}
    (h₀ : mpullback (F := F) I I (φ t₀) β.1 = β.1) :
    (∀ t, mpullback (F := F) I I (φ t) β.1 = β.1) ↔
      ∀ t, mextDeriv (RoughForm.interior (eulerianVelocity φ t) β.1) = 0 := by
  have hcartan (t : ℝ) : mlieDerivForm (eulerianVelocity φ t) β.1 =
      mextDeriv (RoughForm.interior (eulerianVelocity φ t) β.1) :=
    SmoothForm.mlieDerivForm_eq_mextDeriv_interior
      ((contMDiff_eulerianVelocity (m := 1) hφ le_rfl t).mdifferentiable one_ne_zero) hβ
  simp only [← hcartan]
  rw [← forall_mpullback_eq_mpullback_iff_mlieDerivForm_eulerianVelocity_eq_zero hφ
    β.mdifferentiable]
  exact ⟨fun h s t ↦ by rw [h s, h t], fun h t ↦ by rw [h t t₀, h₀]⟩

end Pullback

end TauCeti
