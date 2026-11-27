/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.ActionAngle.Basic
public import TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce.Polar

import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition
import TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce.Coordinates
import TauCeti.LinearAlgebra.Determinant.Basic

/-!
# The punctured plane as a neighbourhood of the zero section of `T*S¹`

Let `V` be a real inner product plane with an orthonormal basis `b`, so that `(V, dx ∧ dy)` is the
standard symplectic plane in the coordinates `(x, y)` of `b`, and let `S¹ = ℝ / 2πℤ`, read as the
one-dimensional torus `Fin 1 → AddCircle (2 * π)`, whose cotangent bundle carries the global
action–angle coordinates `(θ, I)` of `TauCeti.CotangentBundle.actionAngleCover`, with canonical
form `ω = dθ ∧ dI`. For a radial profile `h : ℝ → ℝ`, this file studies the map

`Φ_h : V → T*S¹`, `q ↦ h(‖q‖) dθ` at the polar angle `θ(q)`

(`TauCeti.CotangentBundle.polarCovector`): in polar coordinates `q = r e_r(θ)` it is
`(r, θ) ↦ (θ, I = h(r))`. Its actions are `h(‖q‖)`, so the circle `‖q‖ = c` goes to the zero
section exactly when `h(c) = 0`, each point to the zero covector over its own angle.

Away from the origin, `Φ_h` pulls the canonical form back to a multiple of the area form:

`Φ_h^* (dθ ∧ dI) = -(h'(r) / r) dx ∧ dy`,  `r = ‖q‖`

(`TauCeti.CotangentBundle.eval₂_symplecticForm_mfderiv_polarCovector`). Indeed
`dx ∧ dy = r dr ∧ dθ` while `dθ ∧ d(h(r)) = -h'(r) dr ∧ dθ`. Hence `Φ_h` is symplectic on the
punctured plane exactly when `h'(r) = -r` for every `r > 0`
(`TauCeti.CotangentBundle.forall_eval₂_symplecticForm_mfderiv_polarCovector_eq_det_iff`).

For `h(r) = (1 - r²) / 2` this holds: the map `(r, θ) ↦ (θ, (1 - r²) / 2)` is symplectic and sends
the unit circle, a Lagrangian curve of the plane, to the zero section
(`TauCeti.CotangentBundle.eval₂_symplecticForm_mfderiv_polarCovector_one_sub_sq_div_two`). It is
injective on the punctured plane, a local diffeomorphism there, and its image is the set
`{I < 1 / 2}` of covectors with action less than `1 / 2`, which contains the zero section
(`TauCeti.CotangentBundle.injOn_polarCovector_one_sub_sq_div_two`,
`TauCeti.CotangentBundle.isLocalDiffeomorphAt_polarCovector_one_sub_sq_div_two`,
`TauCeti.CotangentBundle.polarCovector_one_sub_sq_div_two_image_compl_zero`). So it identifies the
punctured plane, a neighbourhood of the unit circle, symplectically with a neighbourhood of the
zero section of `T*S¹`, sending each point of the circle to the zero covector over its angle: an
explicit instance of Weinstein's Lagrangian neighbourhood theorem.

The profile `h(r) = 1 - r` also sends the unit circle to the zero section, and it agrees with
`(1 - r²) / 2` to first order at `r = 1`. But it pulls `dθ ∧ dI` back to `(1 / r) dx ∧ dy`
(`TauCeti.CotangentBundle.eval₂_symplecticForm_mfderiv_polarCovector_one_sub`), so it is symplectic
only along the circle.

## Main definitions

* `TauCeti.CotangentBundle.polarCovector b h`: the covector `h(‖q‖) dθ` over the polar angle of `q`.

## Main results

* `TauCeti.CotangentBundle.polarCovector_smul_polarRadialUnit`: in polar coordinates `Φ_h` is
  `(r, θ) ↦ (θ, h(r))`.
* `TauCeti.CotangentBundle.polarCovector_eq_zeroSection_iff`: `Φ_h` sends the circle `‖q‖ = c`
  to the zero section exactly when `h(c) = 0`.
* `TauCeti.CotangentBundle.eval₂_symplecticForm_mfderiv_polarCovector`:
  `Φ_h^* (dθ ∧ dI) = -(h'(r) / r) dx ∧ dy` on the punctured plane.
* `TauCeti.CotangentBundle.forall_eval₂_symplecticForm_mfderiv_polarCovector_eq_det_iff`: `Φ_h` is
  symplectic on the punctured plane exactly when `h'(r) = -r` for `r > 0`.
* `TauCeti.CotangentBundle.contMDiffAt_polarCovector`,
  `TauCeti.CotangentBundle.isLocalDiffeomorphAt_polarCovector`,
  `TauCeti.CotangentBundle.injOn_polarCovector`,
  `TauCeti.CotangentBundle.polarCovector_image_compl_zero`: smoothness, local diffeomorphism where
  `h' ≠ 0`, injectivity for `h` injective on `(0, ∞)`, and the image of the punctured plane.
* `TauCeti.CotangentBundle.eval₂_symplecticForm_mfderiv_polarCovector_one_sub_sq_div_two`,
  `TauCeti.CotangentBundle.isLocalDiffeomorphAt_polarCovector_one_sub_sq_div_two`,
  `TauCeti.CotangentBundle.injOn_polarCovector_one_sub_sq_div_two`,
  `TauCeti.CotangentBundle.polarCovector_one_sub_sq_div_two_image_compl_zero`: the profile
  `(1 - r²) / 2` identifies the punctured plane symplectically with `{I < 1 / 2}` in `T*S¹`.
* `TauCeti.CotangentBundle.eval₂_symplecticForm_mfderiv_polarCovector_one_sub`: the profile
  `1 - r` gives `(1 / r) dx ∧ dy`.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Theorem 9.3 (Weinstein's Lagrangian neighbourhood theorem).
-/

public section

noncomputable section

open Bundle Function Real Set
open scoped Manifold ContDiff InnerProductSpace

namespace TauCeti

namespace CotangentBundle

/-- The circle of angles has positive period `2π`. -/
local instance polarCovectorTwoPiPos : Fact (0 < 2 * π) := ⟨two_pi_pos⟩

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (b : OrthonormalBasis (Fin 2) ℝ V)

/-- The covector `h(‖q‖) dθ` of the circle `S¹ = Fin 1 → AddCircle (2 * π)`, over the polar angle
of `q` in the frame `(b₀, b₁)`: in polar coordinates `q = r e_r(θ)` it is the covector with angle
`θ` and action `I = h(r)`. -/
def polarCovector (h : ℝ → ℝ) (q : V) :
    CotangentBundle (ModelWithCorners.pi fun _ : Fin 1 ↦ 𝓘(ℝ)) (Fin 1 → AddCircle (2 * π)) :=
  actionAngleCover (2 * π) (fun _ ↦ (polarAngle (b 0) (b 1) q).toReal, fun _ ↦ h ‖q‖)

/-- The defining formula of `Φ_h`: the covector with angle the polar angle of `q` and action
`h(‖q‖)`. -/
theorem polarCovector_def (h : ℝ → ℝ) (q : V) :
    polarCovector b h q =
      actionAngleCover (2 * π) (fun _ ↦ (polarAngle (b 0) (b 1) q).toReal, fun _ ↦ h ‖q‖) :=
  (rfl)

/-- The covector `Φ_h(q)` evaluates a tangent vector `v` of the circle as `h(‖q‖) v`. -/
@[simp]
theorem polarCovector_snd_apply (h : ℝ → ℝ) (q : V) (v : Fin 1 → ℝ) :
    (polarCovector b h q).snd v = h ‖q‖ * v 0 := by
  rw [polarCovector_def, actionAngleCover_snd_apply, Fin.sum_univ_one]

/-- The covector `Φ_h(q)` lies over the polar angle of `q`. -/
@[simp]
theorem proj_polarCovector (h : ℝ → ℝ) (q : V) :
    (polarCovector b h q).proj =
      fun _ ↦ (((polarAngle (b 0) (b 1) q).toReal : ℝ) : AddCircle (2 * π)) := by
  rw [polarCovector, proj_actionAngleCover]

/-- **The action of `Φ_h(q)` is `h(‖q‖)`.** -/
@[simp]
theorem torusActions_polarCovector (h : ℝ → ℝ) (q : V) :
    torusActions (2 * π) (polarCovector b h q) = fun _ ↦ h ‖q‖ := by
  rw [polarCovector, torusActions_actionAngleCover]

/-- **`Φ_h` sends the circle `‖q‖ = c` to the zero section exactly when `h(c) = 0`.** The covector
`Φ_h(q)` is the zero covector over the polar angle of `q` exactly when `h(‖q‖) = 0`. -/
theorem polarCovector_eq_zeroSection_iff (h : ℝ → ℝ) (q : V) :
    polarCovector b h q =
        zeroSection ((Fin 1 → ℝ) →L[ℝ] ℝ)
          (fun y : Fin 1 → AddCircle (2 * π) ↦
            TangentSpace (ModelWithCorners.pi fun _ : Fin 1 ↦ 𝓘(ℝ)) y →L[ℝ] ℝ)
          (fun _ ↦ (((polarAngle (b 0) (b 1) q).toReal : ℝ) : AddCircle (2 * π))) ↔
      h ‖q‖ = 0 := by
  rw [zeroSection]
  constructor
  · intro hq
    have h0 := congrFun (congrArg (torusActions (2 * π)) hq) 0
    rw [torusActions_polarCovector, torusActions_apply] at h0
    exact h0.trans (zero_apply _)
  · intro hq
    refine CotangentBundle.ext (proj_polarCovector b h q) fun v ↦ ?_
    refine (actionAngleCover_snd_apply (2 * π) _ v).trans ?_
    simp only [hq, zero_mul, Finset.sum_const_zero]
    exact (zero_apply _).symm

/-! ### Polar coordinates on the real cover -/

/-- **`Φ_h` in polar coordinates.** For `r > 0`, `Φ_h(r e_r(θ))` is the covector with angle `θ`
and action `h(r)`. -/
theorem polarCovector_smul_polarRadialUnit {r : ℝ} (hr : 0 < r) (θ : ℝ) (h : ℝ → ℝ) :
    polarCovector b h (r • polarRadialUnit (b 0) (b 1) θ) =
      actionAngleCover (2 * π) (fun _ ↦ θ, fun _ ↦ h r) := by
  obtain ⟨k, hk⟩ :=
    Real.Angle.angle_eq_iff_two_pi_dvd_sub.1 (Real.Angle.coe_toReal (θ : Real.Angle))
  rw [polarCovector, b.norm_smul_polarRadialUnit hr.le, b.polarAngle_smul_polarRadialUnit hr]
  convert actionAngleCover_add_intCast_mul (2 * π) (fun _ : Fin 1 ↦ θ) (fun _ ↦ h r)
    (fun _ ↦ k) using 3
  funext i
  simp only [Pi.add_apply]
  linear_combination hk

/-! ### The pullback of the canonical form -/

/-- The covector field `Φ_h` in polar coordinates, `(r, θ) ↦ (θ, I = h(r))`. -/
private def polarActionAngle (h : ℝ → ℝ) (x : ℝ × ℝ) : (Fin 1 → ℝ) × (Fin 1 → ℝ) :=
  (fun _ ↦ x.2, fun _ ↦ h x.1)

/-- The derivative of `(r, θ) ↦ (θ, h(r))`: `(a, c) ↦ (c, h'(r) a)`. -/
private def polarActionAngleDeriv (h : ℝ → ℝ) (x : ℝ × ℝ) :
    ℝ × ℝ →L[ℝ] (Fin 1 → ℝ) × (Fin 1 → ℝ) :=
  (ContinuousLinearMap.pi fun _ : Fin 1 ↦ ContinuousLinearMap.snd ℝ ℝ ℝ).prod
    (ContinuousLinearMap.pi fun _ : Fin 1 ↦ deriv h x.1 • ContinuousLinearMap.fst ℝ ℝ ℝ)

private theorem hasFDerivAt_polarActionAngle {h : ℝ → ℝ} {x : ℝ × ℝ}
    (hh : DifferentiableAt ℝ h x.1) :
    HasFDerivAt (polarActionAngle h) (polarActionAngleDeriv h x) x := by
  refine (hasFDerivAt_pi'.2 fun _ ↦ hasFDerivAt_snd).prodMk (hasFDerivAt_pi'.2 fun _ ↦ ?_)
  exact (hh.hasDerivAt.comp_hasFDerivAt x hasFDerivAt_fst).congr_fderiv (by ext <;> simp)

/-- `Φ_h` in polar coordinates `(r, θ) ↦ r e_r` agrees with `κ ∘ polarActionAngle` near every
point with `r > 0`. -/
private theorem polarCovector_comp_smul_polarRadialUnit_eventuallyEq {x : ℝ × ℝ} (hr : 0 < x.1)
    (h : ℝ → ℝ) :
    polarCovector b h ∘ (fun x : ℝ × ℝ ↦ x.1 • polarRadialUnit (b 0) (b 1) x.2) =ᶠ[nhds x]
      actionAngleCover (2 * π) ∘ polarActionAngle h :=
  ((isOpen_lt continuous_const continuous_fst).eventually_mem hr).mono fun y hy ↦
    polarCovector_smul_polarRadialUnit b hy y.2 h

/-- `Φ_h^* (dθ ∧ dI) = -(h'(r) / r) dx ∧ dy` at a point of polar coordinates `(r, θ)`, `r > 0`,
on the images of tangent vectors under polar coordinates. -/
private theorem eval₂_symplecticForm_mfderiv_polarCovector_smul_polarRadialUnit {h : ℝ → ℝ}
    {x : ℝ × ℝ} (hr : 0 < x.1) (hh : DifferentiableAt ℝ h x.1) (a c : ℝ × ℝ) :
    SmoothBundleForm.eval₂
        (symplecticForm (ModelWithCorners.pi fun _ : Fin 1 ↦ 𝓘(ℝ)) (Fin 1 → AddCircle (2 * π)))
        (polarCovector b h (x.1 • polarRadialUnit (b 0) (b 1) x.2))
        (mfderiv 𝓘(ℝ, V) ((ModelWithCorners.pi fun _ : Fin 1 ↦ 𝓘(ℝ)).prod
          𝓘(ℝ, (Fin 1 → ℝ) →L[ℝ] ℝ)) (polarCovector b h) (x.1 • polarRadialUnit (b 0) (b 1) x.2)
          (fderiv ℝ (fun x : ℝ × ℝ ↦ x.1 • polarRadialUnit (b 0) (b 1) x.2) x a))
        (mfderiv 𝓘(ℝ, V) ((ModelWithCorners.pi fun _ : Fin 1 ↦ 𝓘(ℝ)).prod
          𝓘(ℝ, (Fin 1 → ℝ) →L[ℝ] ℝ)) (polarCovector b h) (x.1 • polarRadialUnit (b 0) (b 1) x.2)
          (fderiv ℝ (fun x : ℝ × ℝ ↦ x.1 • polarRadialUnit (b 0) (b 1) x.2) x c)) =
      -(deriv h x.1 / x.1) *
        b.toBasis.det ![fderiv ℝ (fun x : ℝ × ℝ ↦ x.1 • polarRadialUnit (b 0) (b 1) x.2) x a,
          fderiv ℝ (fun x : ℝ × ℝ ↦ x.1 • polarRadialUnit (b 0) (b 1) x.2) x c] := by
  have hP := isLocalDiffeomorphAt_smul_polarRadialUnit b hr
  have hPd := (hP.mdifferentiableAt (by simp)).differentiableAt.hasFDerivAt.hasMFDerivAt.mfderiv
  have hg := hasFDerivAt_polarActionAngle hh
  have hκ := ((contMDiff_actionAngleCover (ι := Fin 1) (2 * π)) (polarActionAngle h x))
    |>.mdifferentiableAt (by simp)
  -- The derivative of `Φ_h` along polar coordinates is that of `κ ∘ polarActionAngle`.
  have hd (e : ℝ × ℝ) :
      mfderiv 𝓘(ℝ, V) ((ModelWithCorners.pi fun _ : Fin 1 ↦ 𝓘(ℝ)).prod
          𝓘(ℝ, (Fin 1 → ℝ) →L[ℝ] ℝ)) (polarCovector b h) (x.1 • polarRadialUnit (b 0) (b 1) x.2)
          (fderiv ℝ (fun x : ℝ × ℝ ↦ x.1 • polarRadialUnit (b 0) (b 1) x.2) x e) =
        mfderiv 𝓘(ℝ, (Fin 1 → ℝ) × (Fin 1 → ℝ)) ((ModelWithCorners.pi fun _ : Fin 1 ↦ 𝓘(ℝ)).prod
          𝓘(ℝ, (Fin 1 → ℝ) →L[ℝ] ℝ)) (actionAngleCover (2 * π)) (polarActionAngle h x)
          (polarActionAngleDeriv h x e) := by
    have h1 := DFunLike.congr_fun (hP.mfderiv_comp (I' := (ModelWithCorners.pi fun _ : Fin 1 ↦
      𝓘(ℝ)).prod 𝓘(ℝ, (Fin 1 → ℝ) →L[ℝ] ℝ)) (by simp) (polarCovector b h)) e
    rw [(polarCovector_comp_smul_polarRadialUnit_eventuallyEq b hr h).mfderiv_eq,
      mfderiv_comp x hκ hg.differentiableAt.mdifferentiableAt, hg.hasMFDerivAt.mfderiv,
      hPd] at h1
    exact h1.symm
  rw [hd, hd, polarCovector_smul_polarRadialUnit b hr, ← polarActionAngle,
    det_fderiv_smul_polarRadialUnit]
  refine (eval₂_symplecticForm_mfderiv_actionAngleCover (2 * π) (polarActionAngle h x) _ _).trans
    ?_
  -- The sum has the single term `a.θ (h'(r) c.r) - c.θ (h'(r) a.r)`.
  have key : a.2 * (deriv h x.1 * c.1) - c.2 * (deriv h x.1 * a.1) =
      -(deriv h x.1 / x.1 * (x.1 * (a.1 * c.2 - c.1 * a.2))) := by
    field_simp
    ring
  simpa [polarActionAngleDeriv] using key

/-- **The pullback of the canonical form.** Away from the origin, the map `Φ_h : q ↦ h(‖q‖) dθ`
pulls the canonical form `dθ ∧ dI` of `T*S¹` back to `-(h'(r) / r) dx ∧ dy`, where `r = ‖q‖` and
`dx ∧ dy` is the area form of the basis `b`. -/
theorem eval₂_symplecticForm_mfderiv_polarCovector {h : ℝ → ℝ} {q : V} (hq : q ≠ 0)
    (hh : DifferentiableAt ℝ h ‖q‖) (u v : TangentSpace 𝓘(ℝ, V) q) :
    SmoothBundleForm.eval₂
        (symplecticForm (ModelWithCorners.pi fun _ : Fin 1 ↦ 𝓘(ℝ)) (Fin 1 → AddCircle (2 * π)))
        (polarCovector b h q)
        (mfderiv 𝓘(ℝ, V) ((ModelWithCorners.pi fun _ : Fin 1 ↦ 𝓘(ℝ)).prod
          𝓘(ℝ, (Fin 1 → ℝ) →L[ℝ] ℝ)) (polarCovector b h) q u)
        (mfderiv 𝓘(ℝ, V) ((ModelWithCorners.pi fun _ : Fin 1 ↦ 𝓘(ℝ)).prod
          𝓘(ℝ, (Fin 1 → ℝ) →L[ℝ] ℝ)) (polarCovector b h) q v) =
      -(deriv h ‖q‖ / ‖q‖) * b.toBasis.det ![u, v] := by
  -- Write `q = r e_r(θ)` in polar coordinates.
  obtain ⟨x, hr, rfl⟩ := exists_pos_smul_polarRadialUnit_eq b hq
  rw [b.norm_smul_polarRadialUnit hr.le] at hh ⊢
  -- Every tangent vector at `q` is the image of a tangent vector in polar coordinates.
  have hP := isLocalDiffeomorphAt_smul_polarRadialUnit b hr
  have hsurj := (hP.isInvertible_mfderiv (by simp)).surjective
  rw [(hP.mdifferentiableAt (by simp)).differentiableAt.hasFDerivAt.hasMFDerivAt.mfderiv] at hsurj
  obtain ⟨a, rfl⟩ := hsurj u
  obtain ⟨c, rfl⟩ := hsurj v
  exact eval₂_symplecticForm_mfderiv_polarCovector_smul_polarRadialUnit b hr hh a c

/-- **`Φ_h` is symplectic exactly when `h'(r) = -r`.** For a profile `h` differentiable on
`(0, ∞)`, the map `Φ_h` pulls the canonical form `dθ ∧ dI` of `T*S¹` back to the area form
`dx ∧ dy` of the basis `b` at every point of the punctured plane exactly when `h'(r) = -r` for every
`r > 0`. -/
theorem forall_eval₂_symplecticForm_mfderiv_polarCovector_eq_det_iff {h : ℝ → ℝ}
    (hh : ∀ r, 0 < r → DifferentiableAt ℝ h r) :
    (∀ q : V, q ≠ 0 → ∀ u v : TangentSpace 𝓘(ℝ, V) q,
      SmoothBundleForm.eval₂
          (symplecticForm (ModelWithCorners.pi fun _ : Fin 1 ↦ 𝓘(ℝ)) (Fin 1 → AddCircle (2 * π)))
          (polarCovector b h q)
          (mfderiv 𝓘(ℝ, V) ((ModelWithCorners.pi fun _ : Fin 1 ↦ 𝓘(ℝ)).prod
            𝓘(ℝ, (Fin 1 → ℝ) →L[ℝ] ℝ)) (polarCovector b h) q u)
          (mfderiv 𝓘(ℝ, V) ((ModelWithCorners.pi fun _ : Fin 1 ↦ 𝓘(ℝ)).prod
            𝓘(ℝ, (Fin 1 → ℝ) →L[ℝ] ℝ)) (polarCovector b h) q v) =
        b.toBasis.det ![u, v]) ↔
      ∀ r, 0 < r → deriv h r = -r := by
  refine ⟨fun H r hr ↦ ?_, fun H q hq u v ↦ ?_⟩
  · -- Evaluate at `q = r b₀` on the basis `(b₀, b₁)`, where `dx ∧ dy` is `1`.
    have hq : ‖r • b 0‖ = r := by rw [norm_smul, b.norm_eq_one, mul_one, norm_of_nonneg hr.le]
    have hdet : b.toBasis.det ![b 0, b 1] = 1 := by
      have hb : ![b 0, b 1] = ⇑b.toBasis := by
        ext i
        fin_cases i <;> simp
      rw [hb, Module.Basis.det_self]
    have hq0 : r • b 0 ≠ 0 := fun h0 ↦ by
      rw [h0, norm_zero] at hq
      exact hr.ne hq
    have h1 := (H (r • b 0) hq0 (b 0) (b 1)).symm.trans
      (eval₂_symplecticForm_mfderiv_polarCovector b hq0 (by rw [hq]; exact hh r hr) (b 0) (b 1))
    rw [hq, hdet] at h1
    field_simp at h1
    linarith
  · have hr : 0 < ‖q‖ := norm_pos_iff.2 hq
    rw [eval₂_symplecticForm_mfderiv_polarCovector b hq (hh _ hr), H _ hr]
    field_simp

private theorem hasDerivAt_one_sub_sq_div_two (r : ℝ) :
    HasDerivAt (fun r : ℝ ↦ (1 - r ^ 2) / 2) (-r) r := by
  convert ((hasDerivAt_pow 2 r).const_sub 1).div_const 2 using 1
  ring

/-- **The profile `(1 - r²) / 2` is symplectic.** The map `(r, θ) ↦ (θ, I = (1 - r²) / 2)` pulls
the canonical form `dθ ∧ dI` of `T*S¹` back to the area form `dx ∧ dy` of the punctured plane. It
sends the unit circle to the zero section
(`TauCeti.CotangentBundle.polarCovector_eq_zeroSection_iff`). -/
theorem eval₂_symplecticForm_mfderiv_polarCovector_one_sub_sq_div_two {q : V} (hq : q ≠ 0)
    (u v : TangentSpace 𝓘(ℝ, V) q) :
    SmoothBundleForm.eval₂
        (symplecticForm (ModelWithCorners.pi fun _ : Fin 1 ↦ 𝓘(ℝ)) (Fin 1 → AddCircle (2 * π)))
        (polarCovector b (fun r ↦ (1 - r ^ 2) / 2) q)
        (mfderiv 𝓘(ℝ, V) ((ModelWithCorners.pi fun _ : Fin 1 ↦ 𝓘(ℝ)).prod
          𝓘(ℝ, (Fin 1 → ℝ) →L[ℝ] ℝ)) (polarCovector b fun r ↦ (1 - r ^ 2) / 2) q u)
        (mfderiv 𝓘(ℝ, V) ((ModelWithCorners.pi fun _ : Fin 1 ↦ 𝓘(ℝ)).prod
          𝓘(ℝ, (Fin 1 → ℝ) →L[ℝ] ℝ)) (polarCovector b fun r ↦ (1 - r ^ 2) / 2) q v) =
      b.toBasis.det ![u, v] :=
  (forall_eval₂_symplecticForm_mfderiv_polarCovector_eq_det_iff b
    fun r _ ↦ (hasDerivAt_one_sub_sq_div_two r).differentiableAt).2
    (fun r _ ↦ (hasDerivAt_one_sub_sq_div_two r).deriv) q hq u v

/-- **The profile `1 - r` is not symplectic off the unit circle.** Like the profile
`(1 - r²) / 2`, the map `(r, θ) ↦ (θ, I = 1 - r)` sends the unit circle to the zero section, but it
pulls the canonical form `dθ ∧ dI` back to `(1 / r) dx ∧ dy`. -/
theorem eval₂_symplecticForm_mfderiv_polarCovector_one_sub {q : V} (hq : q ≠ 0)
    (u v : TangentSpace 𝓘(ℝ, V) q) :
    SmoothBundleForm.eval₂
        (symplecticForm (ModelWithCorners.pi fun _ : Fin 1 ↦ 𝓘(ℝ)) (Fin 1 → AddCircle (2 * π)))
        (polarCovector b (fun r ↦ 1 - r) q)
        (mfderiv 𝓘(ℝ, V) ((ModelWithCorners.pi fun _ : Fin 1 ↦ 𝓘(ℝ)).prod
          𝓘(ℝ, (Fin 1 → ℝ) →L[ℝ] ℝ)) (polarCovector b fun r ↦ 1 - r) q u)
        (mfderiv 𝓘(ℝ, V) ((ModelWithCorners.pi fun _ : Fin 1 ↦ 𝓘(ℝ)).prod
          𝓘(ℝ, (Fin 1 → ℝ) →L[ℝ] ℝ)) (polarCovector b fun r ↦ 1 - r) q v) =
      ‖q‖⁻¹ * b.toBasis.det ![u, v] := by
  have hd (r : ℝ) : HasDerivAt (fun r : ℝ ↦ 1 - r) (-1) r := by
    simpa using (hasDerivAt_id r).const_sub 1
  rw [eval₂_symplecticForm_mfderiv_polarCovector b hq (hd _).differentiableAt, (hd _).deriv]
  ring

/-! ### The neighbourhood of the unit circle -/

/-- **`Φ_h` is smooth off the origin** wherever the profile `h` is smooth at `‖q‖`. -/
theorem contMDiffAt_polarCovector {h : ℝ → ℝ} {q : V} (hq : q ≠ 0)
    (hh : ContDiffAt ℝ ∞ h ‖q‖) :
    ContMDiffAt 𝓘(ℝ, V) ((ModelWithCorners.pi fun _ : Fin 1 ↦ 𝓘(ℝ)).prod
      𝓘(ℝ, (Fin 1 → ℝ) →L[ℝ] ℝ)) ∞ (polarCovector b h) q := by
  obtain ⟨x, hr, rfl⟩ := exists_pos_smul_polarRadialUnit_eq b hq
  rw [b.norm_smul_polarRadialUnit hr.le] at hh
  rw [← (isLocalDiffeomorphAt_smul_polarRadialUnit b hr).contMDiffAt_comp_iff le_rfl]
  have hg : ContDiffAt ℝ ∞ (polarActionAngle h) x :=
    (contDiffAt_pi.2 fun _ ↦ contDiffAt_snd).prodMk
      (contDiffAt_pi.2 fun _ ↦ hh.comp x contDiffAt_fst)
  exact ((contMDiff_actionAngleCover (2 * π) _).comp x hg.contMDiffAt).congr_of_eventuallyEq
    (polarCovector_comp_smul_polarRadialUnit_eventuallyEq b hr h)

/-- **`Φ_h` is injective on the punctured plane when `h` is injective on `(0, ∞)`.** -/
theorem injOn_polarCovector {h : ℝ → ℝ} (hh : InjOn h (Ioi 0)) :
    InjOn (polarCovector b h) {0}ᶜ := by
  intro q hq q' hq' hqq'
  -- The actions agree and the angle lifts differ by a multiple `m 0` of `2π`.
  rw [polarCovector_def, polarCovector_def] at hqq'
  obtain ⟨hI, m, hm⟩ := (actionAngleCover_eq_actionAngleCover_iff (2 * π)).1 hqq'
  have hn : ‖q‖ = ‖q'‖ :=
    hh (norm_pos_iff.2 (mem_compl_singleton_iff.1 hq))
      (norm_pos_iff.2 (mem_compl_singleton_iff.1 hq')) (congrFun hI 0).symm
  -- So the polar angles agree.
  have hθ : ((polarAngle (b 0) (b 1) q).toReal : Real.Angle) =
      ((polarAngle (b 0) (b 1) q').toReal : Real.Angle) :=
    Real.Angle.angle_eq_iff_two_pi_dvd_sub.2 ⟨-m 0, by
      have := congrFun hm 0
      simp only [Pi.add_apply] at this
      push_cast
      linarith⟩
  rw [Real.Angle.coe_toReal, Real.Angle.coe_toReal] at hθ
  rw [← norm_smul_polarRadialUnit_of_coe_eq_polarAngle b hq (Real.Angle.coe_toReal _),
    ← norm_smul_polarRadialUnit_of_coe_eq_polarAngle b hq' (Real.Angle.coe_toReal _), hn, hθ]

/-- **`Φ_h` is a local diffeomorphism where `h' ≠ 0`.** At `q ≠ 0` with `h` smooth near `‖q‖` and
`h'(‖q‖) ≠ 0`, the pullback `-(h'(r) / r) dx ∧ dy` of `dθ ∧ dI` is nondegenerate, so the
differential of `Φ_h` is injective. -/
theorem isLocalDiffeomorphAt_polarCovector {h : ℝ → ℝ} {q : V} (hq : q ≠ 0)
    (hh : ∀ᶠ r in nhds ‖q‖, ContDiffAt ℝ ∞ h r) (hh' : deriv h ‖q‖ ≠ 0) :
    IsLocalDiffeomorphAt 𝓘(ℝ, V) ((ModelWithCorners.pi fun _ : Fin 1 ↦ 𝓘(ℝ)).prod
      𝓘(ℝ, (Fin 1 → ℝ) →L[ℝ] ℝ)) ∞ (polarCovector b h) q := by
  have : FiniteDimensional ℝ V := b.toBasis.finiteDimensional_of_finite
  -- `Φ_h` is smooth on the open set of points `q'` near `q` where `h` is smooth at `‖q'‖`.
  obtain ⟨s, hs, hqs, hsm⟩ : ∃ s : Set V, IsOpen s ∧ q ∈ s ∧ ∀ q' ∈ s, q' ≠ 0 ∧
      ContDiffAt ℝ ∞ h ‖q'‖ := by
    obtain ⟨t, hts, ht, hqt⟩ := mem_nhds_iff.1
      ((continuous_norm.continuousAt (x := q)).preimage_mem_nhds hh)
    exact ⟨t ∩ {0}ᶜ, ht.inter isOpen_compl_singleton, ⟨hqt, hq⟩,
      fun q' hq' ↦ ⟨hq'.2, hts hq'.1⟩⟩
  refine isLocalDiffeomorphAt_of_injective_mfderiv
    (fun q' hq' ↦ (contMDiffAt_polarCovector b (hsm q' hq').1 (hsm q' hq').2).contMDiffWithinAt)
    hs hqs BoundarylessManifold.isInteriorPoint (by simp)
    ((injective_iff_map_eq_zero _).2 fun u hu ↦ ?_) ?_
  · -- A vector killed by the differential pairs to zero with every vector under `dx ∧ dy`.
    have hr : ‖q‖ ≠ 0 := norm_ne_zero_iff.2 hq
    have h (v : TangentSpace 𝓘(ℝ, V) q) : b.toBasis.det ![u, v] = 0 := by
      have h1 : -(deriv h ‖q‖ / ‖q‖) * b.toBasis.det ![u, v] = 0 :=
        (eval₂_symplecticForm_mfderiv_polarCovector b hq
          (hh.self_of_nhds.differentiableAt (by simp)) u v).symm.trans (by
            rw [hu, eval₂_symplecticForm]
            exact LinearMap.map_zero₂ _ _)
      exact (mul_eq_zero.1 h1).resolve_left (by simp [hh', hr])
    exact b.toBasis.eq_zero_of_forall_det_eq_zero h
  · simp [Module.finrank_eq_card_basis b.toBasis, ContinuousLinearMap.dual_finrank_eq]

/-- **The image of the punctured plane.** `Φ_h` maps the punctured plane onto the covectors of
`T*S¹` whose action is a value of `h` on `(0, ∞)`. -/
theorem polarCovector_image_compl_zero (h : ℝ → ℝ) :
    polarCovector b h '' {0}ᶜ = {z | torusActions (2 * π) z 0 ∈ h '' Ioi 0} := by
  ext z
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨‖q‖, norm_pos_iff.2 (mem_compl_singleton_iff.1 hq), by simp⟩
  · rintro ⟨r, hr, hz⟩
    obtain ⟨⟨θ, I⟩, rfl⟩ := surjective_actionAngleCover (2 * π) z
    simp only [torusActions_actionAngleCover] at hz
    refine ⟨r • polarRadialUnit (b 0) (b 1) (θ 0), fun h0 ↦ ?_, ?_⟩
    · have := b.norm_smul_polarRadialUnit hr.le (θ 0)
      rw [mem_singleton_iff.1 h0, norm_zero] at this
      exact (ne_of_lt hr) this
    · rw [polarCovector_smul_polarRadialUnit b hr]
      congr 1
      refine Prod.ext (funext fun i ↦ ?_) (funext fun i ↦ ?_)
      · rw [Subsingleton.elim i 0]
      · rw [Subsingleton.elim i 0]
        exact hz

/-- **The profile `(1 - r²) / 2` is injective on the punctured plane.** -/
theorem injOn_polarCovector_one_sub_sq_div_two :
    InjOn (polarCovector b fun r ↦ (1 - r ^ 2) / 2) {0}ᶜ :=
  injOn_polarCovector b fun r hr r' hr' h ↦
    (sq_eq_sq₀ (le_of_lt hr) (le_of_lt hr')).1 (by linarith [h])

/-- **The profile `(1 - r²) / 2` is a local diffeomorphism on the punctured plane.** -/
theorem isLocalDiffeomorphAt_polarCovector_one_sub_sq_div_two {q : V} (hq : q ≠ 0) :
    IsLocalDiffeomorphAt 𝓘(ℝ, V) ((ModelWithCorners.pi fun _ : Fin 1 ↦ 𝓘(ℝ)).prod
      𝓘(ℝ, (Fin 1 → ℝ) →L[ℝ] ℝ)) ∞ (polarCovector b fun r ↦ (1 - r ^ 2) / 2) q :=
  isLocalDiffeomorphAt_polarCovector b hq (Filter.Eventually.of_forall fun _ ↦ by fun_prop)
    (by rw [(hasDerivAt_one_sub_sq_div_two _).deriv]; simpa using hq)

/-- **The image of the punctured plane is `{I < 1 / 2}`.** The profile `(1 - r²) / 2` maps the
punctured plane onto the covectors of `T*S¹` with action less than `1 / 2`. This set contains the
zero section, and it is open since the action map is continuous
(`TauCeti.CotangentBundle.contMDiff_torusActions`). -/
theorem polarCovector_one_sub_sq_div_two_image_compl_zero :
    (polarCovector b fun r ↦ (1 - r ^ 2) / 2) '' {0}ᶜ =
      {z | torusActions (2 * π) z 0 < 1 / 2} := by
  rw [polarCovector_image_compl_zero]
  ext z
  simp only [mem_ofPred_eq, mem_image, mem_Ioi]
  constructor
  · rintro ⟨r, hr, hz⟩
    rw [← hz]
    nlinarith
  · intro hz
    refine ⟨√(1 - 2 * torusActions (2 * π) z 0), Real.sqrt_pos.2 (by linarith), ?_⟩
    rw [Real.sq_sqrt (by linarith)]
    ring

end CotangentBundle

end TauCeti
