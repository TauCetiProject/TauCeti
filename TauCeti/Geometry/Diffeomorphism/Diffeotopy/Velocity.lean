/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Basic
public import TauCeti.Geometry.Manifold.Flow.Eulerian

/-!
# The velocity field of a diffeotopy

Let `φ_t`, `t ∈ [0, 1]`, be a diffeotopy of a manifold `M`, with motion `(x, t) ↦ φ_t x` on the
cylinder `M × [0, 1]` (`TauCeti.Diffeotopy.cylinderMap`). Its **velocity field** at time `t` is the
time-dependent vector field

`X_t = (∂ₜ φ_t) ∘ φ_t⁻¹`

(`TauCeti.Diffeotopy.velocity`): at a point `x` it is the velocity of the trajectory through
`φ_t⁻¹ x`, so that `X_t (φ_t y) = ∂ₜ φ_t y` (`TauCeti.Diffeotopy.velocity_apply`). This is the
Eulerian description of the motion, in which the field is read at the current position; the
time derivative `∂ₜ φ_t x` at the initial position `x` is its Lagrangian description. For a family
`φ : ℝ → M ≃ M` extending the diffeotopy beyond `[0, 1]`, it is the Eulerian velocity field
`TauCeti.eulerianField` of the family wherever the trajectories are differentiable
(`TauCeti.Diffeotopy.velocity_eq_eulerianField`); it is defined from the diffeotopy alone, with
one-sided time derivatives at the time ends.

On spatial tangent vectors the motion acts by the differential of the time slice,
`dΦ_(x, t) (v, 0) = dφ_t v` (`TauCeti.Diffeotopy.mfderiv_cylinderMap_inl`). Differentiating
`φ_t ∘ φ_t⁻¹ = id` in time then expresses the velocity of the inverse diffeotopy through the
velocity field: the time derivative of `φ_t⁻¹ x` is carried by `dφ_t` to `-X_t x`
(`TauCeti.Diffeotopy.mfderiv_timeSlice_mfderiv_cylinderMap_symm`), that is

`∂ₜ (φ_t⁻¹ x) = -(dφ_t)⁻¹ (X_t x)`.

## Main definitions

* `TauCeti.Diffeotopy.velocity`: the velocity field `X_t = (∂ₜ φ_t) ∘ φ_t⁻¹` of a diffeotopy.

## Main results

* `TauCeti.Diffeotopy.velocity_apply`: `X_t (φ_t y) = ∂ₜ φ_t y`.
* `TauCeti.Diffeotopy.velocity_eq_eulerianField`: comparison with the Eulerian field of an
  extension of the diffeotopy to all times.
* `TauCeti.Diffeotopy.velocity_refl`: the constant diffeotopy has zero velocity.
* `TauCeti.Diffeotopy.mfderiv_cylinderMap_inl`: the spatial derivative of the motion is the
  differential of the time slice.
* `TauCeti.Diffeotopy.mfderiv_cylinderMap_mfderiv_cylinderMap_symm`: the derivative of
  `φ_t (φ_t⁻¹ x) = x` on the cylinder.
* `TauCeti.Diffeotopy.mfderiv_timeSlice_mfderiv_cylinderMap_symm_inl`: `dφ_t ∘ d(φ_t⁻¹) = id`.
* `TauCeti.Diffeotopy.mfderiv_timeSlice_mfderiv_cylinderMap_symm`: the velocity of the inverse
  diffeotopy, `dφ_t (∂ₜ (φ_t⁻¹ x)) = -X_t x`.

## References

* Dusa McDuff and Dietmar Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford
  University Press, 2017, Section 3.1 (the vector field `X_t` of an isotopy, with
  `∂ₜ ψ_t = X_t ∘ ψ_t`).
-/

public section

noncomputable section

open unitInterval
open scoped Manifold ContDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}

namespace Diffeotopy

variable (Φ : Diffeotopy J n M)

/-- **The spatial derivative of the motion.** The motion `(x, t) ↦ φ_t x` of a diffeotopy of
positive order acts on spatial tangent vectors at `(x, t)` by the differential of the time slice
`φ_t`. -/
theorem mfderiv_cylinderMap_inl (hn : 1 ≤ n) (p : M × I) (v : E) :
    mfderiv (J.prod (𝓡∂ 1)) J Φ.cylinderMap p (v, (0 : TangentSpace (𝓡∂ 1) p.2)) =
      mfderiv J J (Φ.timeSlice p.2) p.1 v := by
  refine (mfderiv_prod_eq_add_apply (Φ.contMDiff_cylinderMap.mdifferentiableAt
    (zero_lt_one.trans_le (by exact_mod_cast hn)).ne')).trans ?_
  have hslice : (fun z ↦ Φ.cylinderMap (z, p.2)) = Φ.timeSlice p.2 :=
    funext fun z ↦ by rw [cylinderMap_apply, timeSlice_apply]
  rw [hslice]
  exact add_eq_left.2 (map_zero _)

/-- The **velocity field** `X_t = (∂ₜ φ_t) ∘ φ_t⁻¹` of a diffeotopy at time `t`: at `x` it is the
time derivative of the motion `(y, t) ↦ φ_t y` at the point `(φ_t⁻¹ x, t)`, the velocity of the
trajectory currently passing through `x`. -/
def velocity (t : I) (x : M) : TangentSpace J x :=
  mfderiv (J.prod (𝓡∂ 1)) J Φ.cylinderMap (Φ.symm (t, x), t)
    ((0 : E), (1 : TangentSpace (𝓡∂ 1) t))

/-- The velocity field unfolds to the time derivative of the motion at `(φ_t⁻¹ x, t)`. -/
theorem velocity_def (t : I) (x : M) :
    Φ.velocity t x = mfderiv (J.prod (𝓡∂ 1)) J Φ.cylinderMap (Φ.symm (t, x), t)
      ((0 : E), (1 : TangentSpace (𝓡∂ 1) t)) :=
  (rfl)

/-- **The velocity field along the motion.** At the point `φ_t y` reached from `y`, the velocity
field is the time derivative `∂ₜ φ_t y` of the trajectory of `y`. -/
theorem velocity_apply (t : I) (y : M) :
    Φ.velocity t (Φ (t, y)) = mfderiv (J.prod (𝓡∂ 1)) J Φ.cylinderMap (y, t)
      ((0 : E), (1 : TangentSpace (𝓡∂ 1) t)) := by
  have hy : Φ.symm (t, Φ (t, y)) = y := by
    rw [symm_apply]
    exact Φ.symm_apply_apply (t, y)
  rw [velocity_def, hy]

/-- **The velocity field is the Eulerian field of an extension.** Let `φ : ℝ → M ≃ M` be a family
of bijections which agrees with the diffeotopy at the times of `[0, 1]`. Where the trajectory
`u ↦ φ_u (φ_t⁻¹ x)` is differentiable at `t`, the velocity field of the diffeotopy is the Eulerian
velocity field `TauCeti.eulerianField` of the family. -/
theorem velocity_eq_eulerianField (hn : 1 ≤ n) {φ : ℝ → M ≃ M}
    (hφ : ∀ (s : I) (y : M), φ s y = Φ (s, y)) {t : I} {x : M}
    (hd : MDifferentiableAt 𝓘(ℝ, ℝ) J (fun u ↦ φ u ((φ t).symm x)) t) :
    Φ.velocity t x = eulerianField J φ t x := by
  set y := (φ t).symm x
  have hy : Φ.symm (t, x) = y := by
    have hx : Φ (t, y) = x := by
      rw [← hφ]
      exact (φ t).apply_symm_apply x
    rw [← hx, symm_apply]
    exact Φ.symm_apply_apply (t, y)
  -- Along the time direction, the motion is the trajectory `u ↦ φ_u y` restricted to `[0, 1]`.
  have htraj : (fun s : I ↦ Φ.cylinderMap (y, s)) = (fun u ↦ φ u y) ∘ Subtype.val :=
    funext fun s ↦ by rw [cylinderMap_apply, Function.comp_apply, hφ]
  have hval : MDifferentiableAt (𝓡∂ 1) 𝓘(ℝ) (Subtype.val : I → ℝ) t :=
    (contMDiff_subtypeVal_Icc (n := 1)).mdifferentiableAt one_ne_zero
  rw [velocity_def, hy, eulerianField_def, Manifold.curveVelocity_apply]
  refine (mfderiv_prod_eq_add_apply (Φ.contMDiff_cylinderMap.mdifferentiableAt
    (zero_lt_one.trans_le (by exact_mod_cast hn)).ne')).trans ?_
  refine ((congrArg (· + _) (map_zero _)).trans (zero_add _)).trans ?_
  have hcomp := mfderiv_comp_apply (t : I) hd hval (1 : TangentSpace (𝓡∂ 1) t)
  exact (congrArg (fun f : I → M ↦ (mfderiv (𝓡∂ 1) J f t (1 : TangentSpace (𝓡∂ 1) t) : E))
    htraj).trans (hcomp.trans (congrArg _ (mfderiv_subtypeVal_Icc_one t)))

/-- The constant diffeotopy has zero velocity. -/
@[simp]
theorem velocity_refl (t : I) : (refl J n M).velocity t = 0 := by
  have hcyl : (refl J n M).cylinderMap = Prod.fst := funext fun p ↦ by simp
  funext x
  rw [velocity_def, hcyl, mfderiv_fst]
  rfl

/-- **The motion followed by its inverse.** Differentiating `φ_t (φ_t⁻¹ x) = x` on the cylinder: for
a tangent vector `w = (u, s)` at `(x, t)`, the differential of the motion at `(φ_t⁻¹ x, t)` sends
the image `(d(φ⁻¹) w, s)` of `w` under the level-preserving inverse motion to `u`. -/
theorem mfderiv_cylinderMap_mfderiv_cylinderMap_symm (hn : 1 ≤ n) (p : M × I)
    (w : TangentSpace (J.prod (𝓡∂ 1)) p) :
    mfderiv (J.prod (𝓡∂ 1)) J Φ.cylinderMap (Φ.symm.cylinderMap p, p.2)
      (mfderiv (J.prod (𝓡∂ 1)) J Φ.symm.cylinderMap p w, w.2) = w.1 := by
  have hn₀ : n ≠ 0 := (zero_lt_one.trans_le (by exact_mod_cast hn)).ne'
  -- The motion of `φ_t ∘ φ_t⁻¹`, the constant diffeotopy, is the projection to `M`.
  have hcomp : Φ.cylinderMap ∘ (fun q ↦ (Φ.symm.cylinderMap q, q.2)) = Prod.fst := by
    rw [← cylinderMap_trans, symm_trans_self]
    exact funext fun q ↦ by simp
  have h := mfderiv_comp_apply p (Φ.contMDiff_cylinderMap.mdifferentiableAt hn₀)
    (Φ.symm.contMDiff_cylinderMap_prodMk_snd.mdifferentiableAt hn₀) w
  rw [hcomp, mfderiv_fst] at h
  exact (congrArg _ (Φ.symm.mfderiv_cylinderMap_prodMk_snd hn p w)).symm.trans h.symm

/-- **The spatial derivative of the inverse diffeotopy.** The differential of `φ_t` undoes the
spatial derivative `d(φ_t⁻¹)` of the inverse diffeotopy at `(x, t)`. -/
theorem mfderiv_timeSlice_mfderiv_cylinderMap_symm_inl (hn : 1 ≤ n) (t : I) (x : M) (u : E) :
    mfderiv J J (Φ.timeSlice t) (Φ.symm (t, x))
        (mfderiv (J.prod (𝓡∂ 1)) J Φ.symm.cylinderMap (x, t)
          (u, (0 : TangentSpace (𝓡∂ 1) t))) = u := by
  have hy : Φ.symm (t, x) = Φ.symm.cylinderMap (x, t) := (Φ.symm.cylinderMap_apply (x, t)).symm
  rw [hy]
  exact (Φ.mfderiv_cylinderMap_inl hn (Φ.symm.cylinderMap (x, t), t) _).symm.trans
    (Φ.mfderiv_cylinderMap_mfderiv_cylinderMap_symm hn (x, t) (u, 0))

/-- **The velocity of the inverse diffeotopy.** Differentiating `φ_t (φ_t⁻¹ x) = x` in time, the
differential of `φ_t` carries the time derivative `∂ₜ (φ_t⁻¹ x)` of the inverse diffeotopy to
minus the velocity field `X_t x`. -/
theorem mfderiv_timeSlice_mfderiv_cylinderMap_symm (hn : 1 ≤ n) (t : I) (x : M) :
    mfderiv J J (Φ.timeSlice t) (Φ.symm (t, x))
        (mfderiv (J.prod (𝓡∂ 1)) J Φ.symm.cylinderMap (x, t)
          ((0 : E), (1 : TangentSpace (𝓡∂ 1) t))) =
      -Φ.velocity t x := by
  have hy : Φ.symm (t, x) = Φ.symm.cylinderMap (x, t) := (Φ.symm.cylinderMap_apply (x, t)).symm
  rw [velocity_def, hy]
  set V : E := mfderiv (J.prod (𝓡∂ 1)) J Φ.symm.cylinderMap (x, t)
    ((0 : E), (1 : TangentSpace (𝓡∂ 1) t))
  -- `dΦ (V, ∂ₜ) = 0` at `(φ_t⁻¹ x, t)`; split `(V, ∂ₜ)` into its spatial and time parts.
  have hd := Φ.mfderiv_cylinderMap_mfderiv_cylinderMap_symm hn (x, t)
    ((0 : E), (1 : TangentSpace (𝓡∂ 1) t))
  have hsplit : ((V, (1 : TangentSpace (𝓡∂ 1) t)) : E × TangentSpace (𝓡∂ 1) t) =
      ((V, 0) : E × TangentSpace (𝓡∂ 1) t) + ((0 : E), (1 : TangentSpace (𝓡∂ 1) t)) := by
    simp
  have hsum := (map_add (mfderiv (J.prod (𝓡∂ 1)) J Φ.cylinderMap (Φ.symm.cylinderMap (x, t), t))
    ((V, 0) : E × TangentSpace (𝓡∂ 1) t) ((0 : E), (1 : TangentSpace (𝓡∂ 1) t))).symm.trans
    ((congrArg _ hsplit.symm).trans hd)
  have hinl := Φ.mfderiv_cylinderMap_inl hn (Φ.symm.cylinderMap (x, t), t) V
  exact eq_neg_of_add_eq_zero_left ((congrArg (· + _) hinl).symm.trans hsum)

end Diffeotopy

end TauCeti
