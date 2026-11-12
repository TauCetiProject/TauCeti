/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Flow
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Submersion
public import TauCeti.Geometry.Manifold.Submersion.Basic
public import TauCeti.Geometry.Manifold.VectorField.AddCircle
public import TauCeti.Geometry.Manifold.VectorField.Prod
import TauCeti.LinearAlgebra.Alternating.Curry

/-!
# Closed forms on `S¹ × Y` annihilated by the circle direction

Let `Y` be a manifold and `X = AddCircle p × Y`, and let `∂ₛ` be the unit vector field of the
circle factor: the product field `(∂_t, 0)` of the unit field `∂_t` of the circle
(`AddCircle.timeVectorField`) and the zero field of `Y`. A closed form `α` on `X` with
`ι_{∂ₛ} α = 0` comes from `Y`: there is exactly one form `β` on `Y` with `α = pr_Y^* β`, and `β` is
closed.

The proof is Cartan's formula. Since `α` is closed, `L_{∂ₛ} α = ι_{∂ₛ} dα + d ι_{∂ₛ} α = 0`, so `α`
is invariant under the flow of `∂ₛ`, which rotates the circle factor:
`(s, y) ↦ (s + t, y)` (`AddCircle.globalFlow_prodVectorField_timeVectorField`). Its time-`t` maps
have derivative the identity, so `α` takes the same value, as an alternating map on the model
space `ℝ × E`, at all points of a circle `S¹ × {y}`
(`TauCeti.SmoothForm.apply_eq_of_snd_eq_of_interior_eq_zero`). Since `α` vanishes when one of its
arguments is `∂ₛ`, adding multiples of `∂ₛ` to its arguments does not change its value
(`AlternatingMap.map_add_smul_of_curryLeft_eq_zero`). Hence
`α_x(v) = α_{x'}(w)` whenever `x` and `x'` lie over the same point of `Y` and `v` and `w` have the
same components along `Y`: the form `α` is basic for the projection `pr_Y`
(`TauCeti.SmoothForm.isBasic_snd_of_interior_eq_zero`), and it descends along that surjective
submersion. Conversely every pullback `pr_Y^* β` is annihilated by `∂ₛ`, which `pr_Y` kills.

For a connection on a line bundle over `S¹ × Y`, applied to the curvature form `F_A`, this says that
a closed curvature form with `ι_{∂ₛ} F_A = 0` is a basic closed form, the pullback of a closed form
on `Y`. In the Seiberg–Witten theory of products `S¹ × Y`, the vanishing of `ι_{∂ₛ} F_A` is the
output of the integrated Weitzenböck identity for an unperturbed solution, and this file supplies
the step from there to a curvature form pulled back from `Y`.

## Main results

* `AddCircle.isCompleteVectorField_prodVectorField_timeVectorField`,
  `AddCircle.globalFlow_prodVectorField_timeVectorField`: the field `∂ₛ` is complete, and its flow
  rotates the circle factor.
* `TauCeti.SmoothForm.apply_eq_of_snd_eq_of_interior_eq_zero`: a closed form annihilated by `∂ₛ`
  is constant along the circles `S¹ × {y}`.
* `TauCeti.SmoothForm.isBasic_snd_of_interior_eq_zero`: such a form is basic for the projection to
  `Y`.
* `TauCeti.SmoothForm.exists_mpullback_snd_eq_iff_interior_eq_zero`: a closed form on `S¹ × Y` is
  pulled back from `Y` exactly when `∂ₛ` annihilates it.
* `TauCeti.SmoothForm.existsUnique_isClosed_and_mpullback_snd_eq`: the form on `Y` is unique and
  closed.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Theorem 14.35 (Cartan's magic formula) and Chapter 14
  (pullbacks of differential forms).
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996, §5.2.
-/

public section

noncomputable section

open Function Manifold TauCeti.Manifold
open scoped Manifold ContDiff

variable {E H Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace Y] [ChartedSpace H Y]

namespace AddCircle

variable (p : ℝ) [Fact (0 < p)]

/-- The orbits of the rotations `(s, y) ↦ (s + t, y)` of the circle factor of `AddCircle p × Y`
are the integral curves of the field `∂ₛ = (∂_t, 0)`. -/
theorem isMIntegralCurve_prodVectorField_timeVectorField (x : AddCircle p × Y) :
    IsMIntegralCurve (fun t ↦ (translationFlow p t x.1, x.2))
      (prodVectorField (timeVectorField p) (0 : (y : Y) → TangentSpace I y)) :=
  (isMIntegralCurve_translationFlow p x.1).prodMk (isMIntegralCurve_const rfl)

/-- The field `∂ₛ = (∂_t, 0)` of `AddCircle p × Y` is complete. -/
theorem isCompleteVectorField_prodVectorField_timeVectorField :
    TauCeti.IsCompleteVectorField
      (prodVectorField (timeVectorField p) (0 : (y : Y) → TangentSpace I y)) :=
  TauCeti.isCompleteVectorField_of_forall_exists_isMIntegralCurve fun x ↦
    ⟨_, by simp, isMIntegralCurve_prodVectorField_timeVectorField p x⟩

variable [IsManifold I 1 Y]

/-- The field `∂ₛ = (∂_t, 0)` of `AddCircle p × Y` is `C^n` for every `n`. -/
theorem contMDiff_prodVectorField_timeVectorField {n : ℕ∞ω} :
    ContMDiff (𝓘(ℝ).prod I) (𝓘(ℝ).prod I).tangent n
      (T% (prodVectorField (timeVectorField p) (0 : (y : Y) → TangentSpace I y))) :=
  contMDiff_prodVectorField (contMDiff_timeVectorField p)
    (Bundle.contMDiff_zeroSection ℝ (TangentSpace I))

variable [CompleteSpace E] [T2Space Y] [BoundarylessManifold I Y]

/-- The flow of the field `∂ₛ = (∂_t, 0)` of `AddCircle p × Y` rotates the circle factor:
`(s, y) ↦ (s + t, y)`. -/
theorem globalFlow_prodVectorField_timeVectorField (t : ℝ) (x : AddCircle p × Y) :
    TauCeti.globalFlow (prodVectorField (timeVectorField p) (0 : (y : Y) → TangentSpace I y))
        (contMDiff_prodVectorField_timeVectorField p)
        (isCompleteVectorField_prodVectorField_timeVectorField p) t x =
      (translationFlow p t x.1, x.2) := by
  simpa using TauCeti.globalFlow_eq_of_isMIntegralCurve
    (contMDiff_prodVectorField_timeVectorField (I := I) (Y := Y) p)
    (isCompleteVectorField_prodVectorField_timeVectorField p)
    (isMIntegralCurve_prodVectorField_timeVectorField p x) t

end AddCircle

namespace TauCeti

namespace SmoothForm

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℝ} [Fact (0 < p)] {k : ℕ}
  [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space Y] [IsManifold I ∞ Y]
  {α : SmoothForm (𝓘(ℝ).prod I) (AddCircle p × Y) F (k + 1)}

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space Y] [IsManifold I ∞ Y] in
/-- The rotation `(s, y) ↦ (s + t, y)` of the circle factor has derivative the identity. -/
private theorem mfderiv_prodMap_add_coe_id_apply (t : ℝ) (x : AddCircle p × Y)
    (v : TangentSpace (𝓘(ℝ).prod I) x) :
    mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (Prod.map (· + (t : AddCircle p)) id) x v = v := by
  have hadd : MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ) (· + (t : AddCircle p)) x.1 :=
    ((contMDiff_id (n := 1)).add contMDiff_const).mdifferentiableAt one_ne_zero
  rw [mfderiv_prodMap hadd mdifferentiableAt_id, AddCircle.mfderiv_add_right, mfderiv_id]
  -- `id.prodMap id` sends `v` to `(v.1, v.2)`, which is `v` by eta for pairs.
  rfl

/-- **A closed form annihilated by `∂ₛ` is constant along the circles.** If `α` is a closed form
on `AddCircle p × Y` with `ι_{∂ₛ} α = 0`, then `α` takes the same value at any two points over the
same point of `Y`, as an alternating map on the model space `ℝ × E` of their tangent spaces. -/
theorem apply_eq_of_snd_eq_of_interior_eq_zero (hα : α.IsClosed)
    (hι : RoughForm.interior (F := F)
      (prodVectorField (AddCircle.timeVectorField p) (0 : (y : Y) → TangentSpace I y)) α.1 = 0)
    {x x' : AddCircle p × Y} (h : x.2 = x'.2) : α.1 x = α.1 x' := by
  obtain ⟨t, ht⟩ := QuotientAddGroup.mk_surjective (x'.1 - x.1)
  -- By Cartan's formula `L_{∂ₛ} α = d ι_{∂ₛ} α = 0`, so the flow of `∂ₛ` preserves `α`.
  have hinv := mpullback_globalFlow_of_mextDeriv_interior_eq_zero
    (AddCircle.isCompleteVectorField_prodVectorField_timeVectorField p)
    (AddCircle.contMDiff_prodVectorField_timeVectorField p) hα (by rw [hι, mextDeriv_zero]) t
  -- That flow is the rotation by `t`, which carries `x` to `x'` and has derivative the identity.
  have hflow : TauCeti.globalFlow
      (prodVectorField (AddCircle.timeVectorField p) (0 : (y : Y) → TangentSpace I y))
      ((AddCircle.contMDiff_prodVectorField_timeVectorField p).of_le one_le_two)
      (AddCircle.isCompleteVectorField_prodVectorField_timeVectorField p) t =
      Prod.map (· + (t : AddCircle p)) id :=
    funext fun z ↦ by
      rw [AddCircle.globalFlow_prodVectorField_timeVectorField, AddCircle.translationFlow_apply]
      -- `Prod.map f id z` is `(f z.1, z.2)` by definition.
      rfl
  have hx' : Prod.map (· + (t : AddCircle p)) id x = x' :=
    Prod.ext (by simp [ht]) (by simpa using h)
  have hfix : α.1 x = α.1 (Prod.map (· + (t : AddCircle p)) id x) := by
    ext v
    have hv := congrFun (congrArg (fun β ↦ β x) hinv) v
    simp only [TauCeti.mpullback_apply, hflow, mfderiv_prodMap_add_coe_id_apply] at hv
    exact hv.symm
  rw [hfix, hx']

/-- **A closed form annihilated by `∂ₛ` is basic.** If `α` is a closed form on `AddCircle p × Y`
with `ι_{∂ₛ} α = 0`, then `α_x(v) = α_{x'}(w)` whenever `x` and `x'` lie over the same point of
`Y` and the components of `v` and `w` along `Y` agree. -/
theorem isBasic_snd_of_interior_eq_zero (hα : α.IsClosed)
    (hι : RoughForm.interior (F := F)
      (prodVectorField (AddCircle.timeVectorField p) (0 : (y : Y) → TangentSpace I y)) α.1 = 0) :
    RoughForm.IsBasic (V := F) I Prod.snd α.1 := by
  rw [RoughForm.isBasic_iff]
  intro x x' hx v w hvw
  rw [apply_eq_of_snd_eq_of_interior_eq_zero hα hι hx]
  set T := prodVectorField (AddCircle.timeVectorField p) (0 : (y : Y) → TangentSpace I y)
  -- The tangent spaces of `AddCircle p × Y` are the model space `ℝ × E`, where `∂ₛ = (1, 0)`;
  -- its zero vector component along `Y` is the zero of `TangentSpace I x'.2`, which `simp` does not
  -- identify with the zero of `E`.
  have hTx : T x' = ((1 : ℝ), (0 : E)) :=
    Prod.ext (by simp [T]) (by simp only [T, prodVectorField_snd, Pi.zero_apply]; rfl)
  -- Read `α_{x'}` and its arguments in the model space `ℝ × E` of the tangent spaces.
  let f : (ℝ × E) [⋀^Fin (k + 1)]→L[ℝ] F := α.1 x'
  let v' : Fin (k + 1) → ℝ × E := v
  let w' : Fin (k + 1) → ℝ × E := w
  -- The interior product of `α_{x'}` with `∂ₛ = (1, 0)` vanishes.
  have hT : f.toAlternatingMap.curryLeft ((1 : ℝ), (0 : E)) = 0 := by
    ext u
    let u' : Fin k → TangentSpace (𝓘(ℝ).prod I) x' := u
    have h := congrArg (fun β ↦ β x' u') hι
    simp only [RoughForm.interior_apply, hTx, Pi.zero_apply, ContinuousAlternatingMap.coe_zero]
      at h
    rw [AlternatingMap.curryLeft_apply_apply, zero_apply]
    exact h
  -- `v i` differs from `w i` by a multiple of `∂ₛ = (1, 0)`: the derivatives of the projection are
  -- the second projections, which agree on them, and `tangentSpaceCast` is the identity.
  have hv : v' = fun i ↦ w' i + ((v' i).1 - (w' i).1) • ((1 : ℝ), (0 : E)) := by
    funext i
    have h₂ := hvw i
    rw [mfderiv_snd, mfderiv_snd] at h₂
    have h₂' : (v' i).2 = (w' i).2 := h₂
    exact Prod.ext (by simp) (by simpa using h₂')
  change f v' = f w'
  rw [hv]
  exact AlternatingMap.map_add_smul_of_curryLeft_eq_zero hT _ _

/-- **Closed forms pulled back from `Y`.** A closed form on `AddCircle p × Y` is the pullback of a
form on `Y` along the projection exactly when it is annihilated by the field `∂ₛ` of the circle
factor. -/
theorem exists_mpullback_snd_eq_iff_interior_eq_zero (hα : α.IsClosed) :
    (∃ β : SmoothForm I Y F (k + 1), SmoothForm.mpullback Prod.snd contMDiff_snd β = α) ↔
      RoughForm.interior (F := F)
        (prodVectorField (AddCircle.timeVectorField p) (0 : (y : Y) → TangentSpace I y)) α.1 =
          0 := by
  refine ⟨?_, fun hι ↦ (isSubmersion_snd.exists_smoothForm_mpullback_eq_iff
    Prod.snd_surjective).2 (isBasic_snd_of_interior_eq_zero hα hι)⟩
  rintro ⟨β, rfl⟩
  -- The projection kills `∂ₛ`, so the pullback vanishes when its first argument is `∂ₛ`.
  ext x v
  simp only [RoughForm.interior_apply, coe_mpullback, TauCeti.mpullback_apply, mfderiv_snd]
  exact (β.1 x.2).map_coord_zero 0
    (prodVectorField_snd (AddCircle.timeVectorField p) (0 : (y : Y) → TangentSpace I y) x)

/-- **The descent to `Y`.** A closed form on `AddCircle p × Y` annihilated by the field `∂ₛ` of the
circle factor is the pullback along the projection of exactly one form on `Y`, and that form is
closed. -/
theorem existsUnique_isClosed_and_mpullback_snd_eq (hα : α.IsClosed)
    (hι : RoughForm.interior (F := F)
      (prodVectorField (AddCircle.timeVectorField p) (0 : (y : Y) → TangentSpace I y)) α.1 = 0) :
    ∃! β : SmoothForm I Y F (k + 1),
      β.IsClosed ∧ SmoothForm.mpullback Prod.snd contMDiff_snd β = α :=
  ⟨descendedForm isSubmersion_snd Prod.snd_surjective α (isBasic_snd_of_interior_eq_zero hα hι),
    ⟨isClosed_descendedForm_iff.2 hα, mpullback_descendedForm⟩,
    fun _ hβ ↦ eq_descendedForm_iff.2 hβ.2⟩

end SmoothForm

end TauCeti
