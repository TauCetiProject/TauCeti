/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IntegralCurve.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import TauCeti.Geometry.Manifold.Instances.AddCircle.Torus
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# Constant vector fields on a torus

For a finite family of positive periods `p i`, the torus `Tⁿ = ∀ i, AddCircle (p i)` is a smooth
manifold modelled on `ModelWithCorners.pi fun _ ↦ 𝓘(ℝ)`, and its tangent space at every point is
`ι → ℝ`. A real vector `v : ι → ℝ` is therefore a tangent vector at every point, and this file
makes the constant choice `x ↦ v` a smooth vector field (`TauCeti.torusConstVectorField p v`).
For unit periods and `v = Pi.single i 1` it is the coordinate field `∂_(x_i)`.

The covering map `(ι → ℝ) → Tⁿ`, `t ↦ ([t i])ᵢ`, has derivative the identity at every point, so it
sends the constant field `v` of `ι → ℝ` to the constant field `v` of the torus. Since it is a
surjective analytic local diffeomorphism, this shows that the constant field is analytic
(`TauCeti.contMDiff_torusConstVectorField`).

The integral curves of the constant field are the linear translation orbits
`t ↦ x + [t v]` (`TauCeti.isMIntegralCurve_torusConstVectorField`), the trajectories of the
translation diffeotopy `TauCeti.torusTranslationDiffeotopy`. So `v` is the generator of the
translations of the torus along `v`.

## Main definitions

* `TauCeti.torusConstVectorField p v`: the constant vector field `v` on the torus, as a smooth
  section of its tangent bundle.

## Main results

* `TauCeti.torusConstVectorField_apply`: its value at every point is `v`.
* `TauCeti.contMDiff_torusConstVectorField`: it is a `C^n` section for every `n`, including
  analytic.
* `TauCeti.isMIntegralCurve_torusConstVectorField`: its integral curves are the translation orbits
  `t ↦ x + [t v]`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapter 8 (vector fields on the torus) and Chapter 9
  (integral curves).
-/

public section

noncomputable section

open Function
open scoped Manifold ContDiff

namespace TauCeti

variable {ι : Type*} [Fintype ι] (p : ι → ℝ) [∀ i, Fact (0 < p i)] (v : ι → ℝ)

/-- The constant section `x ↦ v` of the tangent bundle of the torus `∀ i, AddCircle (p i)` is
`C^n` for every `n`, including analytic. -/
theorem contMDiff_torusConstVectorField {n : ℕ∞ω} :
    ContMDiff (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).tangent n
      (fun x ↦ (⟨x, v⟩ : TangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
        (∀ i, AddCircle (p i)))) := by
  -- The covering map `t ↦ ([t i])ᵢ` is an analytic local diffeomorphism with derivative the
  -- identity of `ι → ℝ`.
  let π : (ι → ℝ) → ∀ i, AddCircle (p i) := fun t i ↦ (t i : AddCircle (p i))
  have hπd (t : ι → ℝ) : HasMFDerivAt 𝓘(ℝ, ι → ℝ) (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) π t
      (ContinuousLinearMap.id ℝ (ι → ℝ)) :=
    (TauCeti.hasMFDerivAt_pi (M := fun i : ι ↦ AddCircle (p i)) (I := fun _ ↦ 𝓘(ℝ)) (f := π)
      fun i ↦ (AddCircle.hasMFDerivAt_coe (p i) (t i)).comp t
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i).hasMFDerivAt).congr_mfderiv <| by
      -- The product of the coordinate projections is the identity of `ι → ℝ`.
      ext w i
      rfl
  have hπs : ContMDiff 𝓘(ℝ, ι → ℝ) (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) ω π :=
    contMDiff_pi_iff.2 fun i ↦ (AddCircle.contMDiff_coe (p i) ω).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i).contMDiff
  have hπl : IsLocalDiffeomorph 𝓘(ℝ, ι → ℝ) (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) ω π :=
    isLocalDiffeomorph_of_mfderiv_eq hπs le_top fun t ↦
      ⟨ContinuousLinearEquiv.refl ℝ (ι → ℝ), (hπd t).mfderiv.symm⟩
  have hsurj : Surjective π := fun x ↦
    ⟨fun i ↦ (QuotientAddGroup.mk_surjective (x i)).choose,
      funext fun i ↦ (QuotientAddGroup.mk_surjective (x i)).choose_spec⟩
  -- Through the covering map, the field is the lifted derivative `t ↦ ([t], dπ_t v)`.
  rw [← hπl.contMDiff_comp_iff hsurj le_top]
  refine (contMDiffOn_univ.1 ((hπs.contMDiffOn (s := Set.univ)
    ).contMDiffOn_totalSpaceMk_mfderiv_apply (m := n) le_top isOpen_univ v)).congr fun t ↦ ?_
  rw [comp_apply, (hπd t).mfderiv]
  -- Both sides are `⟨π t, v⟩`, the identity map applied to `v` being `v` by definition.
  rfl

/-- The **constant vector field** `v` on the torus `∀ i, AddCircle (p i)`, a smooth section of its
tangent bundle. Each tangent space of the torus is `ι → ℝ`, read in the product charts, and the
field takes the value `v` at every point. For unit periods and `v = Pi.single i 1` it is the
coordinate field `∂_(x_i)`. -/
def torusConstVectorField :
    Cₛ^∞⟮ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ); ι → ℝ,
      TangentSpace (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (M := ∀ i, AddCircle (p i))⟯ :=
  ⟨fun _ ↦ v, contMDiff_torusConstVectorField p v⟩

/-- The constant vector field takes the value `v` at every point. -/
@[simp]
theorem torusConstVectorField_apply (x : ∀ i, AddCircle (p i)) : torusConstVectorField p v x = v :=
  (rfl)

/-- The integral curves of the constant vector field `v` are the translation orbits
`t ↦ x + [t v]`, defined for all time. -/
theorem isMIntegralCurve_torusConstVectorField (x : ∀ i, AddCircle (p i)) :
    IsMIntegralCurve (fun t : ℝ ↦ x + fun i ↦ ((t * v i : ℝ) : AddCircle (p i)))
      (torusConstVectorField p v) := fun t ↦ by
  -- Each coordinate moves along its circle with speed `v i`.
  have h (i : ι) : HasMFDerivAt 𝓘(ℝ) 𝓘(ℝ)
      (fun s : ℝ ↦ (x + fun i ↦ ((s * v i : ℝ) : AddCircle (p i))) i) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (v i)) :=
    AddCircle.hasMFDerivAt_add_coe_comp (hasDerivAt_mul_const (v i)) (x i)
  refine (TauCeti.hasMFDerivAt_pi h).congr_mfderiv ?_
  -- Both sides send the unit time vector to `v`.
  ext i
  exact (one_smul ℝ (v i)).trans (one_smul ℝ (v i)).symm

end TauCeti
