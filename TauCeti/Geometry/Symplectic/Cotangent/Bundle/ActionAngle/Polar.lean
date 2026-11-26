/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.ActionAngle.Basic
public import TauCeti.Geometry.Symplectic.Hamiltonian.CentralForce.Polar

import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition

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
* `TauCeti.CotangentBundle.polarCovector_eq_zero_iff`: `Φ_h` sends the circle `‖q‖ = c` to the
  zero section exactly when `h(c) = 0`.
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
theorem polarCovector_eq_zero_iff (h : ℝ → ℝ) (q : V) :
    polarCovector b h q =
        TotalSpace.mk' ((Fin 1 → ℝ) →L[ℝ] ℝ)
          (fun _ ↦ (((polarAngle (b 0) (b 1) q).toReal : ℝ) : AddCircle (2 * π))) 0 ↔
      h ‖q‖ = 0 := by
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

/-- Polar coordinates `(r, θ) ↦ r e_r(θ)` of the plane, with a real angle. -/
private def polarCover (x : ℝ × ℝ) : V :=
  x.1 • polarRadialUnit (b 0) (b 1) x.2

/-- The derivative of polar coordinates at `(r, θ)`: `(a, c) ↦ a e_r + r c e_θ`. -/
private def polarCoverDeriv (x : ℝ × ℝ) : ℝ × ℝ →L[ℝ] V :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (polarRadialUnit (b 0) (b 1) x.2) +
    x.1 • (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (polarAngularUnit (b 0) (b 1) x.2)

private theorem polarCoverDeriv_apply (x a : ℝ × ℝ) :
    polarCoverDeriv b x a =
      a.1 • polarRadialUnit (b 0) (b 1) x.2 + (x.1 * a.2) • polarAngularUnit (b 0) (b 1) x.2 := by
  simp [polarCoverDeriv, mul_smul]

private theorem hasFDerivAt_polarCover (x : ℝ × ℝ) :
    HasFDerivAt (polarCover b) (polarCoverDeriv b x) x := by
  have h := (hasFDerivAt_fst (p := x)).smul
    ((hasDerivAt_polarRadialUnit (b 0) (b 1) x.2).hasFDerivAt.comp x hasFDerivAt_snd)
  refine h.congr_fderiv ?_
  ext <;> simp [polarCoverDeriv, add_comm]

private theorem contDiff_polarCover : ContDiff ℝ ∞ (polarCover b) :=
  contDiff_fst.smul ((contDiff_polarRadialUnit (b 0) (b 1)).comp contDiff_snd)

/-- In polar coordinates, `‖r e_r(θ)‖ = r` for `r > 0`. -/
private theorem norm_polarCover {x : ℝ × ℝ} (hr : 0 < x.1) : ‖polarCover b x‖ = x.1 := by
  rw [polarCover, norm_smul, norm_polarRadialUnit (b.norm_eq_one 0) (b.norm_eq_one 1)
    (b.inner_eq_zero (by decide)), mul_one, norm_of_nonneg hr.le]

/-- The point `‖q‖ e_r(θ)`, for the polar angle `θ` of `q ≠ 0`, is `q`. -/
private theorem polarCover_norm_polarAngle {q : V} (hq : q ≠ 0) :
    polarCover b (‖q‖, (polarAngle (b 0) (b 1) q).toReal) = q := by
  simpa [polarCanonical_apply, polarCover] using
    congrArg Prod.fst (polarCanonical_polarAngle b 0 hq (Real.Angle.coe_toReal _))

/-- **`Φ_h` in polar coordinates.** For `r > 0`, `Φ_h(r e_r(θ))` is the covector with angle `θ`
and action `h(r)`. -/
theorem polarCovector_smul_polarRadialUnit {r : ℝ} (hr : 0 < r) (θ : ℝ) (h : ℝ → ℝ) :
    polarCovector b h (r • polarRadialUnit (b 0) (b 1) θ) =
      actionAngleCover (2 * π) (fun _ ↦ θ, fun _ ↦ h r) := by
  have hθ : polarAngle (b 0) (b 1) (r • polarRadialUnit (b 0) (b 1) θ) = θ := by
    simpa [polarCanonical_apply] using
      polarAngle_polarCanonical (b.norm_eq_one 0) (b.norm_eq_one 1) (b.inner_eq_zero (by decide))
        (x := ((r, 0), (θ, 0))) hr
  obtain ⟨k, hk⟩ :=
    Real.Angle.angle_eq_iff_two_pi_dvd_sub.1 (Real.Angle.coe_toReal (θ : Real.Angle))
  have hn : ‖r • polarRadialUnit (b 0) (b 1) θ‖ = r := norm_polarCover b (x := (r, θ)) hr
  rw [polarCovector, hn, hθ]
  convert actionAngleCover_add_intCast_mul (2 * π) (fun _ : Fin 1 ↦ θ) (fun _ ↦ h r)
    (fun _ ↦ k) using 3
  funext i
  simp only [Pi.add_apply]
  linear_combination hk

private theorem polarCovector_polarCover {x : ℝ × ℝ} (hr : 0 < x.1) (h : ℝ → ℝ) :
    polarCovector b h (polarCover b x) = actionAngleCover (2 * π) (fun _ ↦ x.2, fun _ ↦ h x.1) :=
  polarCovector_smul_polarRadialUnit b hr x.2 h

/-- The derivative of polar coordinates is injective away from `r = 0`. -/
private theorem injective_polarCoverDeriv {x : ℝ × ℝ} (hr : x.1 ≠ 0) :
    Injective (polarCoverDeriv b x) := by
  have hu := b.norm_eq_one 0
  have hw := b.norm_eq_one 1
  have huw : ⟪b 0, b 1⟫_ℝ = 0 := b.inner_eq_zero (by decide)
  refine (injective_iff_map_eq_zero _).2 fun a ha ↦ ?_
  rw [polarCoverDeriv_apply] at ha
  -- Pair with the orthonormal frame `(e_r, e_θ)`.
  have h1 := congrArg (fun v ↦ ⟪v, polarRadialUnit (b 0) (b 1) x.2⟫_ℝ) ha
  have h2 := congrArg (fun v ↦ ⟪v, polarAngularUnit (b 0) (b 1) x.2⟫_ℝ) ha
  simp only [inner_add_left, real_inner_smul_left, inner_polarRadialUnit_self hu hw huw,
    inner_polarAngularUnit_self hu hw huw, inner_polarRadialUnit_polarAngularUnit hu hw huw,
    inner_polarAngularUnit_polarRadialUnit hu hw huw, inner_zero_left, mul_one, mul_zero,
    add_zero, zero_add] at h1 h2
  exact Prod.ext h1 ((mul_eq_zero.1 h2).resolve_left hr)

/-- Polar coordinates are a local diffeomorphism away from `r = 0`. -/
private theorem isLocalDiffeomorphAt_polarCover {x : ℝ × ℝ} (hr : x.1 ≠ 0) :
    IsLocalDiffeomorphAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V) ∞ (polarCover b) x := by
  have : FiniteDimensional ℝ V := b.toBasis.finiteDimensional_of_finite
  refine isLocalDiffeomorphAt_of_injective_mfderiv (contDiff_polarCover b).contMDiff.contMDiffOn
    isOpen_univ (mem_univ x) BoundarylessManifold.isInteriorPoint (by simp)
    ((injective_iff_map_eq_zero _).2 fun a ha ↦ ?_) ?_
  · rw [(hasFDerivAt_polarCover b x).hasMFDerivAt.mfderiv] at ha
    exact injective_polarCoverDeriv b hr (ha.trans (map_zero _).symm)
  · rw [Module.finrank_prod, Module.finrank_self, Module.finrank_eq_card_basis b.toBasis]
    simp

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

/-- `Φ_h ∘ polarCover` agrees with `κ ∘ polarActionAngle` near every point with `r > 0`. -/
private theorem polarCovector_comp_polarCover_eventuallyEq {x : ℝ × ℝ} (hr : 0 < x.1)
    (h : ℝ → ℝ) :
    polarCovector b h ∘ polarCover b =ᶠ[nhds x] actionAngleCover (2 * π) ∘ polarActionAngle h :=
  ((isOpen_lt continuous_const continuous_fst).eventually_mem hr).mono fun _ hy ↦
    polarCovector_polarCover b hy h

/-- In polar coordinates the area form `dx ∧ dy` is `r dr ∧ dθ`. -/
private theorem det_polarCoverDeriv (x a c : ℝ × ℝ) :
    b.toBasis.det ![polarCoverDeriv b x a, polarCoverDeriv b x c] =
      x.1 * (a.1 * c.2 - c.1 * a.2) := by
  simp only [polarCoverDeriv_apply, Module.Basis.det_apply, Matrix.det_fin_two,
    Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.repr_apply_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    polarRadialUnit_apply, polarAngularUnit_apply, inner_add_right, real_inner_smul_right,
    b.inner_eq_ite]
  norm_num
  linear_combination (x.1 * (a.1 * c.2 - c.1 * a.2)) * (sin_sq_add_cos_sq x.2)

/-- `Φ_h^* (dθ ∧ dI) = -(h'(r) / r) dx ∧ dy` at a point of polar coordinates `(r, θ)`, `r > 0`,
on the images of tangent vectors under polar coordinates. -/
private theorem eval₂_symplecticForm_mfderiv_polarCovector_polarCover {h : ℝ → ℝ} {x : ℝ × ℝ}
    (hr : 0 < x.1) (hh : DifferentiableAt ℝ h x.1) (a c : ℝ × ℝ) :
    SmoothBundleForm.eval₂
        (symplecticForm (ModelWithCorners.pi fun _ : Fin 1 ↦ 𝓘(ℝ)) (Fin 1 → AddCircle (2 * π)))
        (polarCovector b h (polarCover b x))
        (mfderiv 𝓘(ℝ, V) ((ModelWithCorners.pi fun _ : Fin 1 ↦ 𝓘(ℝ)).prod
          𝓘(ℝ, (Fin 1 → ℝ) →L[ℝ] ℝ)) (polarCovector b h) (polarCover b x)
          (polarCoverDeriv b x a))
        (mfderiv 𝓘(ℝ, V) ((ModelWithCorners.pi fun _ : Fin 1 ↦ 𝓘(ℝ)).prod
          𝓘(ℝ, (Fin 1 → ℝ) →L[ℝ] ℝ)) (polarCovector b h) (polarCover b x)
          (polarCoverDeriv b x c)) =
      -(deriv h x.1 / x.1) * b.toBasis.det ![polarCoverDeriv b x a, polarCoverDeriv b x c] := by
  have hP := isLocalDiffeomorphAt_polarCover b hr.ne'
  have hg := hasFDerivAt_polarActionAngle hh
  have hκ := ((contMDiff_actionAngleCover (ι := Fin 1) (2 * π)) (polarActionAngle h x))
    |>.mdifferentiableAt (by simp)
  -- The derivative of `Φ_h` along polar coordinates is that of `κ ∘ polarActionAngle`.
  have hd (e : ℝ × ℝ) :
      mfderiv 𝓘(ℝ, V) ((ModelWithCorners.pi fun _ : Fin 1 ↦ 𝓘(ℝ)).prod
          𝓘(ℝ, (Fin 1 → ℝ) →L[ℝ] ℝ)) (polarCovector b h) (polarCover b x)
          (polarCoverDeriv b x e) =
        mfderiv 𝓘(ℝ, (Fin 1 → ℝ) × (Fin 1 → ℝ)) ((ModelWithCorners.pi fun _ : Fin 1 ↦ 𝓘(ℝ)).prod
          𝓘(ℝ, (Fin 1 → ℝ) →L[ℝ] ℝ)) (actionAngleCover (2 * π)) (polarActionAngle h x)
          (polarActionAngleDeriv h x e) := by
    have h1 := DFunLike.congr_fun (hP.mfderiv_comp (I' := (ModelWithCorners.pi fun _ : Fin 1 ↦
      𝓘(ℝ)).prod 𝓘(ℝ, (Fin 1 → ℝ) →L[ℝ] ℝ)) (by simp) (polarCovector b h)) e
    rw [(polarCovector_comp_polarCover_eventuallyEq b hr h).mfderiv_eq,
      mfderiv_comp x hκ hg.differentiableAt.mdifferentiableAt, hg.hasMFDerivAt.mfderiv,
      (hasFDerivAt_polarCover b x).hasMFDerivAt.mfderiv] at h1
    exact h1.symm
  rw [hd, hd, polarCovector_polarCover b hr, ← polarActionAngle, det_polarCoverDeriv]
  refine (eval₂_symplecticForm_mfderiv_actionAngleCover (2 * π) (polarActionAngle h x) _ _).trans
    ?_
  simp only [polarActionAngleDeriv, Finset.univ_unique, Fin.default_eq_zero,
    Finset.sum_singleton, ContinuousLinearMap.prod_apply, ContinuousLinearMap.pi_apply,
    ContinuousLinearMap.coe_snd', FunLike.coe_smul, Pi.smul_apply,
    ContinuousLinearMap.coe_fst', smul_eq_mul]
  field_simp
  ring

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
  obtain ⟨x, hr, rfl⟩ : ∃ x : ℝ × ℝ, 0 < x.1 ∧ polarCover b x = q :=
    ⟨_, norm_pos_iff.2 hq, polarCover_norm_polarAngle b hq⟩
  rw [norm_polarCover b hr] at hh ⊢
  -- Every tangent vector at `q` is the image of a tangent vector in polar coordinates.
  have hsurj :=
    ((isLocalDiffeomorphAt_polarCover b hr.ne').isInvertible_mfderiv (by simp)).surjective
  rw [(hasFDerivAt_polarCover b x).hasMFDerivAt.mfderiv] at hsurj
  obtain ⟨a, rfl⟩ := hsurj u
  obtain ⟨c, rfl⟩ := hsurj v
  exact eval₂_symplecticForm_mfderiv_polarCovector_polarCover b hr hh a c

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
sends the unit circle to the zero section (`TauCeti.CotangentBundle.polarCovector_eq_zero_iff`). -/
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
  obtain ⟨x, hr, rfl⟩ : ∃ x : ℝ × ℝ, 0 < x.1 ∧ polarCover b x = q :=
    ⟨_, norm_pos_iff.2 hq, polarCover_norm_polarAngle b hq⟩
  rw [norm_polarCover b hr] at hh
  rw [← (isLocalDiffeomorphAt_polarCover b hr.ne').contMDiffAt_comp_iff le_rfl]
  have hg : ContDiffAt ℝ ∞ (polarActionAngle h) x :=
    (contDiffAt_pi.2 fun _ ↦ contDiffAt_snd).prodMk
      (contDiffAt_pi.2 fun _ ↦ hh.comp x contDiffAt_fst)
  exact ((contMDiff_actionAngleCover (2 * π) _).comp x hg.contMDiffAt).congr_of_eventuallyEq
    (polarCovector_comp_polarCover_eventuallyEq b hr h)

/-- **`Φ_h` is injective on the punctured plane when `h` is injective on `(0, ∞)`.** -/
theorem injOn_polarCovector {h : ℝ → ℝ} (hh : InjOn h (Ioi 0)) :
    InjOn (polarCovector b h) {0}ᶜ := by
  intro q hq q' hq' hqq'
  -- The actions give `‖q‖ = ‖q'‖`.
  have hI := congrFun (congrArg (torusActions (2 * π)) hqq') 0
  simp only [torusActions_polarCovector] at hI
  have hn : ‖q‖ = ‖q'‖ :=
    hh (norm_pos_iff.2 (mem_compl_singleton_iff.1 hq))
      (norm_pos_iff.2 (mem_compl_singleton_iff.1 hq')) hI
  -- The base points give equal polar angles.
  have hθ : ((polarAngle (b 0) (b 1) q).toReal : Real.Angle) =
      ((polarAngle (b 0) (b 1) q').toReal : Real.Angle) := by
    have h := congrFun (congrArg TotalSpace.proj hqq') 0
    simp only [proj_polarCovector] at h
    exact h
  rw [Real.Angle.coe_toReal, Real.Angle.coe_toReal] at hθ
  rw [← polarCover_norm_polarAngle b hq, ← polarCover_norm_polarAngle b hq', hn, hθ]

/-- The area form is nondegenerate: a vector pairing to zero with every vector vanishes. -/
private theorem eq_zero_of_forall_det_eq_zero {u : V} (h : ∀ v : V, b.toBasis.det ![u, v] = 0) :
    u = 0 := by
  refine b.toBasis.forall_coord_eq_zero_iff.1 fun i ↦ ?_
  rw [Module.Basis.coord_apply]
  fin_cases i
  · simpa [Module.Basis.det_apply, Matrix.det_fin_two, Module.Basis.toMatrix_apply] using h (b 1)
  · simpa [Module.Basis.det_apply, Matrix.det_fin_two, Module.Basis.toMatrix_apply] using h (b 0)

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
    exact eq_zero_of_forall_det_eq_zero b h
  · rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card, Fintype.card_fin,
      ContinuousLinearMap.dual_finrank_eq, Module.finrank_fintype_fun_eq_card, Fintype.card_fin,
      Module.finrank_eq_card_basis b.toBasis]
    simp

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
    · have := norm_polarCover b (x := (r, θ 0)) hr
      rw [polarCover, mem_singleton_iff.1 h0, norm_zero] at this
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
