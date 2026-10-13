/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LocalFrame
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# The Christoffel map on the model space

A normed space `F` is a manifold with a single chart, and the tangent trivialization reads every
tangent space of `F` as `F` itself. In the frame of that trivialization the constant vector fields
have constant coefficients, so the flat covariant derivative of the frame kills them, and the
Christoffel map of any covariant derivative on `F` is its value on constant fields:
`Γₓ(v, u) = ∇_u v`. This turns an explicit computation of a connection on constant fields into
its Christoffel map, the input of the coordinate curvature formula of
`TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Coordinates`.

## Main results

* `TauCeti.Manifold.frameCovariantDerivative_const_model_space`: the flat covariant derivative of
  the tangent trivialization of `F` kills constant fields.
* `TauCeti.Manifold.christoffelMap_model_space`: on the model space, the Christoffel map of a
  covariant derivative is its value on constant fields.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 4, the Christoffel symbols of a connection in coordinates.
-/

public section

open Bundle Module
open scoped Manifold

noncomputable section

namespace TauCeti.Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {ι : Type*} [Fintype ι] (b : Basis ι 𝕜 F)
  {cov : (Π x : F, TangentSpace 𝓘(𝕜, F) x) →
    (Π x : F, TangentSpace 𝓘(𝕜, F) x →L[𝕜] TangentSpace 𝓘(𝕜, F) x)}

/-- The tangent trivialization of the model space reads its fibres as the model space itself:
`TangentBundle.symmL_model_space`, applied to a vector. -/
private theorem symmL_trivializationAt_model_space (x y v : F) :
    (trivializationAt F (TangentSpace 𝓘(𝕜, F)) x).symmL 𝕜 y v = v := by
  rw [TangentBundle.symmL_model_space]
  -- The identity of `F` applied to `v`, typed as a tangent vector.
  rfl

/-- The frame of the tangent trivialization of the model space differentiates a constant field
to zero: its coefficients in the frame are constant. -/
@[simp]
theorem frameCovariantDerivative_const_model_space (x₀ x v : F) :
    frameCovariantDerivative 𝓘(𝕜, F) b (trivializationAt F (TangentSpace 𝓘(𝕜, F)) x₀)
      (fun _ ↦ v : Π y : F, TangentSpace 𝓘(𝕜, F) y) x = 0 := by
  let e := trivializationAt F (TangentSpace 𝓘(𝕜, F)) x₀
  let C : Π y : F, TangentSpace 𝓘(𝕜, F) y := fun _ ↦ v
  have hbase (y : F) : y ∈ e.baseSet := by
    simp [e, TangentBundle.trivializationAt_baseSet]
  have hcoeff (i : ι) :
      (LinearMap.piApply (e.localFrameCoeff 𝓘(𝕜, F) b i)) C = fun _ ↦ b.repr v i := by
    funext y
    exact (e.localFrameCoeff_eq_coeff (I := 𝓘(𝕜, F)) (b := b) (s := C) (hbase y)).trans
      (by simp [e, C])
  -- Name the dependent constant field, so that the frame derivative is applied to it as stated.
  change frameCovariantDerivative 𝓘(𝕜, F) b e C x = 0
  ext u
  rw [frameCovariantDerivative_apply]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  -- The coefficient of the constant field is a constant function, with zero differential.
  rw [hcoeff i, mvfderiv_const]
  simp

/-- On the model space `F`, the Christoffel map of a covariant derivative of the tangent bundle,
in the tangent trivialization at `x` and any basis, is the covariant derivative of constant
fields: `Γₓ(v, u) = ∇_u v`, with the field value `v` first and the direction `u` second. -/
theorem christoffelMap_model_space [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] {x : F}
    (hcov : IsCovariantDerivativeOn F cov (trivializationAt F (TangentSpace 𝓘(𝕜, F)) x).baseSet)
    (v u : F) :
    christoffelMap b hcov x v u = cov (fun _ ↦ v) x u := by
  let e := trivializationAt F (TangentSpace 𝓘(𝕜, F)) x
  let C : Π y : F, TangentSpace 𝓘(𝕜, F) y := fun _ ↦ v
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt F (TangentSpace 𝓘(𝕜, F)) x
  have hv : MDiffAt (T% C) x :=
    mdifferentiableAt_vectorSpace_iff_differentiableAt.2 (differentiableAt_const v)
  have hc := covariantDerivative_eq_add_christoffelForm b hcov hx hv
  rw [frameCovariantDerivative_const_model_space b x x v, zero_add] at hc
  rw [christoffelMap_apply b hcov hx, symmL_trivializationAt_model_space,
    symmL_trivializationAt_model_space,
    Bundle.Trivialization.continuousLinearMapAt_apply_of_mem 𝕜 e hx]
  -- Name the constant field as in `hc`.
  change _ = cov C x u
  rw [hc]
  simp [e, C]

end TauCeti.Manifold
