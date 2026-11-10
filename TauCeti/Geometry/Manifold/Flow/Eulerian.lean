/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.VectorField.Pullback
public import TauCeti.Geometry.Manifold.MFDeriv.Curve
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import TauCeti.Geometry.Manifold.MFDeriv.Parametric.Basic

/-!
# Eulerian velocity fields of isotopies

Let `φ : ℝ → (M ≃ₘ^n M)` be a family of diffeomorphisms of a manifold. Its **Eulerian velocity
field** at time `t` is the vector field

`X_t = (∂_t φ_t) ∘ φ_t⁻¹`, that is `X_t (φ_t x) = d/du|_{u = t} φ_u x`

(`TauCeti.eulerianVelocity`). Unlike the velocity `u ↦ ∂_u φ_u x` of the individual trajectories,
it is a vector field on `M` at each time, and the trajectories `u ↦ φ_u x` are integral curves of
the time-dependent field `X` (`TauCeti.hasMFDerivAt_eulerianVelocity`). For every time `t`, `X_t`
is `C^m` when `φ` is jointly `C^(m + 1)` and its slices are `C^m` diffeomorphisms
(`TauCeti.contMDiff_eulerianVelocity`).

The Eulerian field of the pointwise composite `(φ ψ)_t = φ_t ∘ ψ_t` of two isotopies is

`X_{φ ψ, t} = X_{φ, t} + (φ_t)_* X_{ψ, t}`

(`TauCeti.eulerianVelocity_trans`), where the pushforward `(φ_t)_* X_{ψ, t}` is Mathlib's
pullback `VectorField.mpullback` by `φ_t⁻¹`; at `φ_t x` it is `(dφ_t)_x X_{ψ, t} x`
(`Diffeomorph.mpullback_symm_apply_eq_mfderiv`). This pointwise product is not the concatenation
of paths. Two consequences follow from it, since a constant family has zero Eulerian field: the
inverse family `φ_t⁻¹` has Eulerian field `-(φ_t⁻¹)_* X_{φ, t}` (`TauCeti.eulerianVelocity_symm`),
and the conjugate family `g⁻¹ ∘ φ_t ∘ g` by a fixed diffeomorphism `g` has Eulerian field
`g^* X_{φ, t}` (`TauCeti.eulerianVelocity_conj`). These identities need differentiability only at
the points involved.

The slices of a `TauCeti.Diffeotopy`, read along any reparametrization `ℝ → I` of time, are such a
family, and `TauCeti.Diffeotopy.timeSlice_trans` and `TauCeti.Diffeotopy.timeSlice_symm` rewrite
the slices of `Diffeotopy.trans ψ φ` and `Diffeotopy.symm φ` into the pointwise composite and
inverse used here.

## Main definitions

* `TauCeti.eulerianVelocity φ t`: the Eulerian velocity field `(∂_t φ_t) ∘ φ_t⁻¹`.

## Main results

* `TauCeti.hasMFDerivAt_eulerianVelocity`: the trajectories of `φ` are integral curves of its
  Eulerian field.
* `TauCeti.contMDiff_eulerianVelocity`: the Eulerian field at each time is `C^m` when `φ` is
  jointly `C^(m + 1)`.
* `Diffeomorph.mpullback_symm_apply_eq_mfderiv`: pulling a vector field back by the inverse of a
  diffeomorphism pushes it forward.
* `TauCeti.eulerianVelocity_trans`: the product formula for the Eulerian field of a composite.
* `TauCeti.eulerianVelocity_symm`, `TauCeti.eulerianVelocity_conj`: the Eulerian fields of the
  inverse and of a conjugate isotopy.

## References

* Dusa McDuff and Dietmar Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Chapter 3 (symplectic isotopies and their generating vector fields) and Chapter 10 (the flux
  homomorphism).
-/

public section

noncomputable section

open Set Bundle
open scoped Manifold ContDiff

namespace TauCeti

open TauCeti.Manifold (curveVelocity hasMFDerivAt_curveVelocity)

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}
  {φ ψ : ℝ → M ≃ₘ^n⟮I, I⟯ M}

/-- The **Eulerian velocity field** `X_t = (∂_t φ_t) ∘ φ_t⁻¹` of a family `φ` of diffeomorphisms
at time `t`: at `y`, it is the velocity at time `t` of the trajectory `u ↦ φ_u (φ_t⁻¹ y)` through
`y`. -/
def eulerianVelocity (φ : ℝ → M ≃ₘ^n⟮I, I⟯ M) (t : ℝ) (y : M) : TangentSpace I y :=
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
theorem eulerianVelocity_const (f : M ≃ₘ^n⟮I, I⟯ M) (t : ℝ) :
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

/-- The pullback of a vector field `V` by the inverse of a `C^n` diffeomorphism `f`, `n ≠ 0`, is its
pushforward by `f`: at `f x` it is `df_x (V x)`. -/
theorem _root_.Diffeomorph.mpullback_symm_apply_eq_mfderiv {E' H' M' : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
    [TopologicalSpace M'] [ChartedSpace H' M'] (f : M ≃ₘ^n⟮I, I'⟯ M') (hn : n ≠ 0)
    (V : Π x : M, TangentSpace I x) (x : M) :
    VectorField.mpullback I' I f.symm V (f x) = mfderiv I I' f x (V x) := by
  -- By the chain rule, `d(f⁻¹)_{f x}` sends `df_x v` back to `v`.
  have hchain (v : TangentSpace I x) : mfderiv I' I f.symm (f x) (mfderiv I I' f x v) = v := by
    have h := mfderiv_comp x (f.symm.mdifferentiable hn (f x)) (f.mdifferentiable hn x)
    rw [show (f.symm ∘ f : M → M) = id from funext f.symm_apply_apply, mfderiv_id] at h
    exact (congrArg (fun L ↦ L v) h).symm
  have key := (f.symm.isInvertible_mfderiv hn (x := f x)).inverse_apply_self
    (mfderiv I I' f x (V x))
  rw [hchain] at key
  rw [VectorField.mpullback_apply]
  convert key using 3
  rw [f.symm_apply_apply]

/-- **The Eulerian field of a composite isotopy.** The Eulerian field of the pointwise composite
`(φ ψ)_t = φ_t ∘ ψ_t` is `X_{φ ψ} = X_φ + (φ_t)_* X_ψ`, where the pushforward `(φ_t)_* X_ψ` is the
pullback by `φ_t⁻¹`. It suffices that `φ` is jointly differentiable at `(t, φ_t⁻¹ y)` and that the
trajectory of `ψ` through `(φ_t ∘ ψ_t)⁻¹ y` is differentiable at `t`. -/
theorem eulerianVelocity_trans (hn : n ≠ 0) {t : ℝ} {y : M}
    (hφ : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) I (fun p : ℝ × M ↦ φ p.1 p.2) (t, (φ t).symm y))
    (hψ : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun u ↦ ψ u ((ψ t).symm ((φ t).symm y))) t) :
    eulerianVelocity (fun u ↦ (ψ u).trans (φ u)) t y =
      eulerianVelocity φ t y + VectorField.mpullback I I (φ t).symm (eulerianVelocity ψ t) y := by
  -- Write `y = φ_t (ψ_t z)`.
  obtain ⟨z, rfl⟩ : ∃ z, φ t (ψ t z) = y := ⟨(ψ t).symm ((φ t).symm y), by simp⟩
  simp only [Diffeomorph.symm_apply_apply] at hφ hψ
  rw [(φ t).mpullback_symm_apply_eq_mfderiv hn]
  set v : E := curveVelocity I (fun u ↦ ψ u z) t
  set D := mfderiv (𝓘(ℝ, ℝ).prod I) I (fun p : ℝ × M ↦ φ p.1 p.2) (t, ψ t z)
  -- The trajectory `u ↦ φ_u (ψ_u z)` is the family `φ` read along `u ↦ (u, ψ_u z)`, whose
  -- velocity is `(1, v)`.
  have hcomp : curveVelocity I (fun u ↦ φ u (ψ u z)) t = D ((1 : ℝ), v) := by
    have hd := hφ.hasMFDerivAt.comp t
      ((hasMFDerivAt_id (I := 𝓘(ℝ, ℝ)) t).prodMk (hasMFDerivAt_curveVelocity hψ))
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
    mfderiv_prod_eq_add_apply hφ
  have htrans := eulerianVelocity_apply_apply (φ := fun u ↦ (ψ u).trans (φ u)) t z
  simp only [Diffeomorph.coe_trans, Function.comp_apply] at htrans
  rw [htrans, hcomp, hsplit, ← TauCeti.Manifold.curveVelocity_apply, eulerianVelocity_apply_apply,
    eulerianVelocity_apply_apply]

/-- **The Eulerian field of the inverse isotopy.** The Eulerian field of the inverse family
`φ_t⁻¹` is `-(φ_t⁻¹)_* X_{φ, t}`, the pullback of `-X_{φ, t}` by `φ_t`. It suffices that the
trajectory of `x` under `φ` is differentiable at `t` and that the family of inverses is jointly
differentiable at `(t, φ_t x)`. -/
theorem eulerianVelocity_symm (hn : n ≠ 0) {t : ℝ} {x : M}
    (hφ : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun u ↦ φ u x) t)
    (hφ' : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) I (fun p : ℝ × M ↦ (φ p.1).symm p.2) (t, φ t x)) :
    eulerianVelocity (fun u ↦ (φ u).symm) t x =
      -VectorField.mpullback I I (φ t) (eulerianVelocity φ t) x := by
  have hss : (φ t).symm.symm = φ t := Diffeomorph.ext fun _ ↦ rfl
  -- The composite `φ_u⁻¹ ∘ φ_u` is the identity, whose Eulerian field vanishes.
  have h := eulerianVelocity_trans (φ := fun u ↦ (φ u).symm) (ψ := φ) hn (t := t) (y := x)
    (by simpa only [hss] using hφ') (by simpa only [hss, Diffeomorph.symm_apply_apply] using hφ)
  simp only [Diffeomorph.self_trans_symm, eulerianVelocity_const, Pi.zero_apply, hss] at h
  exact eq_neg_of_add_eq_zero_left h.symm

/-- **The Eulerian field of a conjugate isotopy.** For a diffeomorphism `g`, the Eulerian field of
the conjugate family `g⁻¹ ∘ φ_t ∘ g` is the pullback `g^* X_{φ, t}`. It suffices that the
trajectory of `φ` through `φ_t⁻¹ (g y)` is differentiable at `t`. -/
theorem eulerianVelocity_conj (hn : n ≠ 0) (g : M ≃ₘ^n⟮I, I⟯ M) {t : ℝ} {y : M}
    (hφ : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun u ↦ φ u ((φ t).symm (g y))) t) :
    eulerianVelocity (fun u ↦ (g.trans (φ u)).trans g.symm) t y =
      VectorField.mpullback I I g (eulerianVelocity φ t) y := by
  have hss : g.symm.symm = g := Diffeomorph.ext fun _ ↦ rfl
  -- First `X_{φ ∘ g} = X_φ`, since `φ_u ∘ g ∘ (φ_t ∘ g)⁻¹ = φ_u ∘ φ_t⁻¹`.
  have h₁ : eulerianVelocity (fun u ↦ g.trans (φ u)) t = eulerianVelocity φ t := by
    funext w
    simp only [eulerianVelocity_apply, Diffeomorph.coe_trans, Diffeomorph.symm_trans',
      Function.comp_apply]
    rw [g.apply_symm_apply]
  -- Then `X_{g⁻¹ ∘ (φ ∘ g)} = (g⁻¹)_* X_{φ ∘ g}`, since `g⁻¹` is constant.
  have h₂ := eulerianVelocity_trans (φ := fun _ ↦ g.symm) (ψ := fun u ↦ g.trans (φ u)) hn
    (t := t) (y := y) ((g.symm.mdifferentiable hn _).comp _ mdifferentiableAt_snd)
    (by simpa only [hss, Diffeomorph.coe_trans, Diffeomorph.symm_trans', Function.comp_apply,
      Diffeomorph.apply_symm_apply] using hφ)
  simp only [eulerianVelocity_const, Pi.zero_apply, hss, zero_add] at h₂
  rw [h₂, h₁]

variable [IsManifold I 1 M]

/-- **Regularity of the Eulerian field.** If the family `φ` is jointly `C^r` and its slices are
`C^n` diffeomorphisms, its Eulerian field at each time is a `C^m` vector field for every `m` with
`m + 1 ≤ r` and `m ≤ n`. -/
theorem contMDiff_eulerianVelocity {m : ℕ∞} {r : ℕ∞ω}
    (hφ : ContMDiff (𝓘(ℝ, ℝ).prod I) I r fun p : ℝ × M ↦ φ p.1 p.2) (hmr : m + 1 ≤ r)
    (hmn : (m : ℕ∞ω) ≤ n) (t : ℝ) :
    ContMDiff I I.tangent m fun y ↦ (⟨y, eulerianVelocity φ t y⟩ : TangentBundle I M) := by
  have hr : r ≠ 0 := by
    rintro rfl
    exact absurd hmr (by simp)
  have hvel := TauCeti.Manifold.contMDiff_mfderiv_apply_one_zero hφ hmr
  -- The section is the velocity of the family read along `y ↦ (t, φ_t⁻¹ y)`.
  have hsec : (fun y ↦ (⟨y, eulerianVelocity φ t y⟩ : TangentBundle I M)) =
      (fun q : ℝ × M ↦ TotalSpace.mk' E (φ q.1 q.2)
        (mfderiv (𝓘(ℝ, ℝ).prod I) I (fun p : ℝ × M ↦ φ p.1 p.2) q ((1 : ℝ), (0 : E)))) ∘
        fun y ↦ (t, (φ t).symm y) := by
    funext y
    have hd := (hφ.mdifferentiable hr) (t, (φ t).symm y)
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
  exact hvel.comp (contMDiff_const.prodMk ((φ t).symm.contMDiff.of_le hmn))

end TauCeti
