/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic

/-!
# The split torus of a hyperbolic pair

Let `Q` be a quadratic form with un-halved polar form `B = polar Q`, and let `u`, `v` be a
*hyperbolic pair*: `Q u = Q v = 0` and `B u v = 1`. For a unit `t`, the linear map

`x ↦ x + ((t - 1) * B x v) • u + ((t⁻¹ - 1) * B x u) • v`

scales `u` by `t`, scales `v` by `t⁻¹`, and fixes every vector orthogonal to both. It is an
isometry of `Q`, and `t ↦` (this map) is an injective homomorphism from `Rˣ` into the orthogonal
group: the diagonal torus `diag(t, t⁻¹)` of the hyperbolic plane spanned by `u` and `v`, extended
by the identity on its orthogonal complement, but written without choosing that complement. It is
the product of the reflections in `u + v` and in `u + t • v`, so on a finite free module it has
determinant one.

Over a normed field the vectors `t • u` are unbounded, so this torus is the standard witness that
the orthogonal group of an isotropic nondegenerate form is not compact.

## Main definitions

* `TauCeti.QuadraticMap.hyperbolicPairTorus Q hu hv huv`: the homomorphism `Rˣ →* O(Q)`
  attached to a hyperbolic pair `u`, `v`.

## Main results

* `TauCeti.QuadraticMap.hyperbolicPairTorus_apply`: the defining formula.
* `TauCeti.QuadraticMap.hyperbolicPairTorus_apply_left`,
  `TauCeti.QuadraticMap.hyperbolicPairTorus_apply_right`: the torus scales `u` by `t` and `v`
  by `t⁻¹`.
* `TauCeti.QuadraticMap.hyperbolicPairTorus_injective`: the torus is injective.
* `TauCeti.QuadraticMap.hyperbolicPairTorus_eq_reflection_mul_reflection`: the torus element `t`
  is the product of the reflections in `u + v` and in `u + t • v`.
* `TauCeti.QuadraticMap.hyperbolicPairTorus_mem_specialOrthogonalGroup`: on a finite free
  module, the torus lies in the special orthogonal group.
-/

public section

namespace TauCeti

namespace QuadraticMap

open _root_.QuadraticMap (polar polar_add_left polar_add_right polar_sub_right polar_smul_left
  polar_smul_right polar_comm polar_self)

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M) {u v : M}

/-- The underlying linear map `x ↦ x + ((t - 1) * B x v) • u + ((t⁻¹ - 1) * B x u) • v` of the
torus of a hyperbolic pair. -/
private noncomputable def hyperbolicPairTorusAux (u v : M) (t : Rˣ) : M →ₗ[R] M :=
  LinearMap.id + (((t : R) - 1) • Q.polarBilin.flip v).smulRight u +
    ((((t⁻¹ : Rˣ) : R) - 1) • Q.polarBilin.flip u).smulRight v

private theorem hyperbolicPairTorusAux_apply (t : Rˣ) (x : M) :
    hyperbolicPairTorusAux Q u v t x =
      x + (((t : R) - 1) * polar Q x v) • u + ((((t⁻¹ : Rˣ) : R) - 1) * polar Q x u) • v := by
  simp [hyperbolicPairTorusAux]

variable {Q}

private theorem polar_hyperbolicPairTorusAux_right (hv : Q v = 0)
    (huv : polar Q u v = 1) (t : Rˣ) (x : M) :
    polar Q (hyperbolicPairTorusAux Q u v t x) v = t * polar Q x v := by
  simp only [hyperbolicPairTorusAux_apply, polar_add_left, polar_smul_left, huv, polar_self, hv,
    smul_eq_mul]
  ring

private theorem polar_hyperbolicPairTorusAux_left (hu : Q u = 0)
    (huv : polar Q u v = 1) (t : Rˣ) (x : M) :
    polar Q (hyperbolicPairTorusAux Q u v t x) u = ((t⁻¹ : Rˣ) : R) * polar Q x u := by
  simp only [hyperbolicPairTorusAux_apply, polar_add_left, polar_smul_left, polar_comm Q v u,
    huv, polar_self, hu, smul_eq_mul]
  ring

private theorem hyperbolicPairTorusAux_mul (hu : Q u = 0) (hv : Q v = 0)
    (huv : polar Q u v = 1) (s t : Rˣ) (x : M) :
    hyperbolicPairTorusAux Q u v s (hyperbolicPairTorusAux Q u v t x) =
      hyperbolicPairTorusAux Q u v (s * t) x := by
  rw [hyperbolicPairTorusAux_apply Q s, polar_hyperbolicPairTorusAux_right hv huv,
    polar_hyperbolicPairTorusAux_left hu huv, hyperbolicPairTorusAux_apply,
    hyperbolicPairTorusAux_apply, mul_inv_rev, Units.val_mul, Units.val_mul]
  module

private theorem hyperbolicPairTorusAux_one (x : M) : hyperbolicPairTorusAux Q u v 1 x = x := by
  simp [hyperbolicPairTorusAux_apply]

private theorem hyperbolicPairTorusAux_comp_inv (hu : Q u = 0) (hv : Q v = 0)
    (huv : polar Q u v = 1) (t : Rˣ) :
    (hyperbolicPairTorusAux Q u v t).comp (hyperbolicPairTorusAux Q u v t⁻¹) = LinearMap.id :=
  LinearMap.ext fun x => by
    rw [LinearMap.comp_apply, hyperbolicPairTorusAux_mul hu hv huv, mul_inv_cancel,
      hyperbolicPairTorusAux_one, LinearMap.id_apply]

private theorem hyperbolicPairTorusAux_mem (hu : Q u = 0) (hv : Q v = 0)
    (huv : polar Q u v = 1) (t : Rˣ) (x : M) :
    Q (hyperbolicPairTorusAux Q u v t x) = Q x := by
  have ht : (t : R) * ((t⁻¹ : Rˣ) : R) = 1 := Units.mul_inv t
  rw [hyperbolicPairTorusAux_apply]
  simp only [QuadraticMap.map_add Q, QuadraticMap.map_smul, polar_add_left, polar_smul_left,
    polar_smul_right, hu, hv, huv, smul_eq_mul]
  linear_combination (polar Q x u * polar Q x v) * ht

variable (Q)

/-- **The split torus of a hyperbolic pair.** For isotropic vectors `u`, `v` with
`polar Q u v = 1`, the unit `t` acts by
`x ↦ x + ((t - 1) * polar Q x v) • u + ((t⁻¹ - 1) * polar Q x u) • v`: it scales `u` by `t`, `v`
by `t⁻¹`, and fixes every vector orthogonal to both. This is an injective homomorphism from `Rˣ`
into the orthogonal group of `Q`. -/
noncomputable def hyperbolicPairTorus (hu : Q u = 0) (hv : Q v = 0) (huv : polar Q u v = 1) :
    Rˣ →* orthogonalGroup Q where
  toFun t := ⟨LinearEquiv.ofLinearMap (f := hyperbolicPairTorusAux Q u v t)
      (g := hyperbolicPairTorusAux Q u v t⁻¹) (hyperbolicPairTorusAux_comp_inv hu hv huv t)
      (by simpa using hyperbolicPairTorusAux_comp_inv hu hv huv t⁻¹),
    mem_orthogonalGroup_iff.mpr (hyperbolicPairTorusAux_mem hu hv huv t)⟩
  map_one' := Subtype.ext <| LinearEquiv.ext <| hyperbolicPairTorusAux_one
  map_mul' s t := Subtype.ext <| LinearEquiv.ext fun x =>
    (hyperbolicPairTorusAux_mul hu hv huv s t x).symm

variable {Q}

/-- The torus of a hyperbolic pair acts by
`x ↦ x + ((t - 1) * polar Q x v) • u + ((t⁻¹ - 1) * polar Q x u) • v`. -/
theorem hyperbolicPairTorus_apply (hu : Q u = 0) (hv : Q v = 0) (huv : polar Q u v = 1)
    (t : Rˣ) (x : M) :
    (hyperbolicPairTorus Q hu hv huv t : M ≃ₗ[R] M) x =
      x + (((t : R) - 1) * polar Q x v) • u + ((((t⁻¹ : Rˣ) : R) - 1) * polar Q x u) • v :=
  hyperbolicPairTorusAux_apply Q t x

/-- The torus of a hyperbolic pair scales the first vector by `t`. -/
@[simp]
theorem hyperbolicPairTorus_apply_left (hu : Q u = 0) (hv : Q v = 0) (huv : polar Q u v = 1)
    (t : Rˣ) : (hyperbolicPairTorus Q hu hv huv t : M ≃ₗ[R] M) u = (t : R) • u := by
  rw [hyperbolicPairTorus_apply, huv, polar_self, hu]
  module

/-- The torus of a hyperbolic pair scales the second vector by `t⁻¹`. -/
@[simp]
theorem hyperbolicPairTorus_apply_right (hu : Q u = 0) (hv : Q v = 0) (huv : polar Q u v = 1)
    (t : Rˣ) : (hyperbolicPairTorus Q hu hv huv t : M ≃ₗ[R] M) v = ((t⁻¹ : Rˣ) : R) • v := by
  rw [hyperbolicPairTorus_apply, polar_comm Q v u, huv, polar_self, hv]
  module

/-- The torus of a hyperbolic pair fixes every vector orthogonal to both vectors of the pair. -/
@[simp]
theorem hyperbolicPairTorus_apply_of_polar_eq_zero (hu : Q u = 0) (hv : Q v = 0)
    (huv : polar Q u v = 1) (t : Rˣ) {x : M} (hxu : polar Q x u = 0) (hxv : polar Q x v = 0) :
    (hyperbolicPairTorus Q hu hv huv t : M ≃ₗ[R] M) x = x := by
  simp [hyperbolicPairTorus_apply, hxu, hxv]

/-- The torus of a hyperbolic pair is injective: `t` is recovered as `polar Q (g u) v`. -/
theorem hyperbolicPairTorus_injective (hu : Q u = 0) (hv : Q v = 0) (huv : polar Q u v = 1) :
    Function.Injective (hyperbolicPairTorus Q hu hv huv) := by
  intro s t hst
  have h := congrArg (fun g : orthogonalGroup Q => polar Q ((g : M ≃ₗ[R] M) u) v) hst
  simp only [hyperbolicPairTorus_apply_left, polar_smul_left, huv, smul_eq_mul, mul_one] at h
  exact Units.ext h

/-- The torus element `t` of a hyperbolic pair is the product of the reflections in `u + v` and
in `u + t • v`, whose norms are `1` and `t`. -/
theorem hyperbolicPairTorus_eq_reflection_mul_reflection (hu : Q u = 0) (hv : Q v = 0)
    (huv : polar Q u v = 1) (t : Rˣ) [Invertible (Q (u + v))]
    [Invertible (Q (u + (t : R) • v))] :
    (hyperbolicPairTorus Q hu hv huv t : M ≃ₗ[R] M) =
      reflection Q (u + v) * reflection Q (u + (t : R) • v) := by
  have hi₁ : ⅟(Q (u + v)) = 1 :=
    invOf_eq_right_inv (by simp [QuadraticMap.map_add Q, hu, hv, huv])
  have hi₂ : ⅟(Q (u + (t : R) • v)) = ((t⁻¹ : Rˣ) : R) :=
    invOf_eq_right_inv (by
      simp [QuadraticMap.map_add Q, QuadraticMap.map_smul, hu, hv, polar_smul_right, huv])
  have ht : (t : R) * ((t⁻¹ : Rˣ) : R) = 1 := Units.mul_inv t
  ext x
  rw [LinearEquiv.mul_apply, reflection_apply, reflection_apply, hi₁, hi₂,
    hyperbolicPairTorus_apply]
  simp only [polar_add_left, polar_add_right, polar_sub_right, polar_smul_left, polar_smul_right,
    polar_comm Q v u, polar_comm Q u x, polar_comm Q v x, polar_self, hu, hv, huv, smul_eq_mul,
    one_mul, mul_one, mul_zero, add_zero, zero_add, nsmul_eq_mul]
  match_scalars
  · ring
  · linear_combination (-(polar Q x u + t * polar Q x v)) * ht
  · linear_combination (-polar Q x v) * ht

/-- On a finite free module, the torus of a hyperbolic pair lies in the special orthogonal
group. -/
theorem hyperbolicPairTorus_mem_specialOrthogonalGroup [Module.Free R M] [Module.Finite R M]
    (hu : Q u = 0) (hv : Q v = 0) (huv : polar Q u v = 1) (t : Rˣ) :
    (hyperbolicPairTorus Q hu hv huv t : M ≃ₗ[R] M) ∈ specialOrthogonalGroup Q := by
  refine mem_specialOrthogonalGroup_iff.mpr ⟨(hyperbolicPairTorus Q hu hv huv t).2, ?_⟩
  let _ : Invertible (Q (u + v)) :=
    invertibleOne.copy _ (by simp [QuadraticMap.map_add Q, hu, hv, huv])
  let _ : Invertible (Q (u + (t : R) • v)) := t.invertible.copy _ (by
    simp [QuadraticMap.map_add Q, QuadraticMap.map_smul, hu, hv, polar_smul_right, huv])
  rw [hyperbolicPairTorus_eq_reflection_mul_reflection hu hv huv t, map_mul, det_reflection,
    det_reflection]
  norm_num

end QuadraticMap

end TauCeti
