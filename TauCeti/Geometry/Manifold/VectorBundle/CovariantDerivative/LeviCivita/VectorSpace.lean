/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LocalFrame
import TauCeti.Geometry.Manifold.VectorField.LieBracket
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# The Levi-Civita connection in global linear coordinates

A finite-dimensional real normed space `F` is a manifold with a single chart, and its tangent
space at every point is `F`. A Riemannian metric on `F` is then a field
`g : F → F →L[ℝ] F →L[ℝ] ℝ` of inner products, as for the left-invariant metrics of the model
geometries Nil, Sol and `SL₂ℝ~` on `ℝ³`. This file computes the Levi-Civita connection of such
a metric from the derivative of `g`, by the Christoffel formula of the first kind:

`2 g(∇_u V, w) = 2 g(DV(u), w) + (Dg(u))(V, w) + (Dg(V))(w, u) - (Dg(w))(u, V)`.

The derivative `Dg(u)` of the metric differentiates its coefficients only, with the two
arguments held fixed. For a constant field `V` the first term vanishes, so the remaining terms
are the Christoffel symbols of the first kind of `g`. A candidate vector satisfying the
right-hand side is then the value of the connection, and on the model space the Christoffel map
of a covariant derivative is its value on constant fields. Together these turn an explicit
metric on `F` into its Christoffel map, which is the input of the coordinate curvature formula of
`TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Coordinates`.

## Main results

* `TauCeti.Manifold.two_mul_leviCivitaConnection_model_space`: the Christoffel formula of the
  first kind for the Levi-Civita connection of a differentiable metric on `F`.
* `TauCeti.Manifold.leviCivitaConnection_model_space_eq_fderiv_add`: the Levi-Civita connection
  is the flat derivative plus any vector solving the Christoffel formula of the first kind.
* `TauCeti.Manifold.christoffelMap_model_space`: on the model space, the Christoffel map of a
  covariant derivative is its value on constant fields.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 5: Theorem 5.10 (the Koszul formula) and the Christoffel symbols of a metric in
  coordinates.
* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser (1992), Chapter 2, §3.
-/

public section

open Bundle CovariantDerivative Module VectorField
open scoped Manifold ContDiff

noncomputable section

namespace TauCeti.Manifold

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ### The Christoffel map on the model space -/

section ChristoffelMap

variable {ι : Type*} [Fintype ι] (b : Basis ι ℝ F) {x : F}
  {cov : (Π x : F, TangentSpace 𝓘(ℝ, F) x) →
    (Π x : F, TangentSpace 𝓘(ℝ, F) x →L[ℝ] TangentSpace 𝓘(ℝ, F) x)}

/-- The tangent trivialization of the model space reads its fibres as the model space itself:
`TangentBundle.symmL_model_space`, applied to a vector. -/
private theorem symmL_trivializationAt_model_space (x y v : F) :
    (trivializationAt F (TangentSpace 𝓘(ℝ, F)) x).symmL ℝ y v = v := by
  rw [TangentBundle.symmL_model_space]
  -- The identity of `F` applied to `v`, typed as a tangent vector.
  rfl

/-- The frame of the tangent trivialization of the model space differentiates a constant field
to zero: its coefficients in the frame are constant. -/
private theorem frameCovariantDerivative_const_model_space (x v : F) :
    frameCovariantDerivative 𝓘(ℝ, F) b (trivializationAt F (TangentSpace 𝓘(ℝ, F)) x)
      (fun _ ↦ v : Π y : F, TangentSpace 𝓘(ℝ, F) y) x = 0 := by
  let e := trivializationAt F (TangentSpace 𝓘(ℝ, F)) x
  let C : Π y : F, TangentSpace 𝓘(ℝ, F) y := fun _ ↦ v
  have hbase (y : F) : y ∈ e.baseSet := by
    simp [e, TangentBundle.trivializationAt_baseSet]
  have hcoeff (i : ι) :
      (LinearMap.piApply (e.localFrameCoeff 𝓘(ℝ, F) b i)) C = fun _ ↦ b.repr v i := by
    funext y
    exact (e.localFrameCoeff_eq_coeff (I := 𝓘(ℝ, F)) (b := b) (s := C) (hbase y)).trans
      (by simp [e, C])
  -- Name the dependent constant field, so that the frame derivative is applied to it as stated.
  change frameCovariantDerivative 𝓘(ℝ, F) b e C x = 0
  ext u
  rw [frameCovariantDerivative_apply]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  -- The coefficient of the constant field is a constant function, with zero differential.
  rw [hcoeff i, mvfderiv_const]
  simp

/-- On the model space `F`, the Christoffel map of a covariant derivative of the tangent bundle,
in the tangent trivialization at `x` and any basis, is the covariant derivative of constant
fields: `Γₓ(v, u) = ∇_u v`, with the field value `v` first and the direction `u` second. -/
theorem christoffelMap_model_space [FiniteDimensional ℝ F]
    (hcov : IsCovariantDerivativeOn F cov (trivializationAt F (TangentSpace 𝓘(ℝ, F)) x).baseSet)
    (v u : F) :
    christoffelMap b hcov x v u = cov (fun _ ↦ v) x u := by
  let e := trivializationAt F (TangentSpace 𝓘(ℝ, F)) x
  let C : Π y : F, TangentSpace 𝓘(ℝ, F) y := fun _ ↦ v
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt F (TangentSpace 𝓘(ℝ, F)) x
  have hv : MDiffAt (T% C) x :=
    mdifferentiableAt_vectorSpace_iff_differentiableAt.2 (differentiableAt_const v)
  have hc := covariantDerivative_eq_add_christoffelForm b hcov hx hv
  rw [frameCovariantDerivative_const_model_space b x v, zero_add] at hc
  rw [christoffelMap_apply b hcov hx, symmL_trivializationAt_model_space,
    symmL_trivializationAt_model_space,
    Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ e hx]
  -- Name the constant field as in `hc`.
  change _ = cov C x u
  rw [hc]
  simp [e, C]

end ChristoffelMap

/-! ### The Christoffel formula of the first kind -/

section Christoffel

/-- The derivative of `y ↦ g y (A y) (B y)` for a field `g` of bilinear forms: the product rule. -/
theorem fderiv_bilin_apply {g : F → F →L[ℝ] F →L[ℝ] ℝ} {A B : F → F} {x : F}
    (hg : DifferentiableAt ℝ g x) (hA : DifferentiableAt ℝ A x) (hB : DifferentiableAt ℝ B x)
    (u : F) :
    fderiv ℝ (fun y ↦ g y (A y) (B y)) x u =
      fderiv ℝ g x u (A x) (B x) + g x (fderiv ℝ A x u) (B x) + g x (A x) (fderiv ℝ B x u) := by
  rw [((hg.hasFDerivAt.clm_apply hA.hasFDerivAt).clm_apply hB.hasFDerivAt).fderiv]
  simp only [add_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.flip_apply]
  ring

variable [FiniteDimensional ℝ F]
  [RiemannianBundle (fun x : F ↦ TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) 1 F (fun x : F ↦ TangentSpace 𝓘(ℝ, F) x)]
  {g : F → F →L[ℝ] F →L[ℝ] ℝ} {x : F} {V : Π y : F, TangentSpace 𝓘(ℝ, F) y}

/-- **The Christoffel formula of the first kind.** If the Riemannian metric of the model space
`F` is the field of bilinear forms `g`, differentiable at `x`, then the Levi-Civita derivative of
a vector field `V` differentiable at `x` satisfies
`2 g(∇_u V, w) = 2 g(DV(u), w) + (Dg(u))(V, w) + (Dg(V))(w, u) - (Dg(w))(u, V)`.
Tangent vectors are read in the model space through `tangentSpaceCastModel`. -/
theorem two_mul_leviCivitaConnection_model_space
    (hg : ∀ y (v w : TangentSpace 𝓘(ℝ, F) y), inner ℝ v w =
      g y (tangentSpaceCastModel 𝓘(ℝ, F) y v) (tangentSpaceCastModel 𝓘(ℝ, F) y w))
    (hgx : DifferentiableAt ℝ g x) (hV : DifferentiableAt ℝ V x) (u w : F) :
    2 * g x (tangentSpaceCastModel 𝓘(ℝ, F) x
        (leviCivitaConnection 𝓘(ℝ, F) F V x ((tangentSpaceCastModel 𝓘(ℝ, F) x).symm u))) w =
      2 * g x (fderiv ℝ V x u) w + fderiv ℝ g x u (tangentSpaceCastModel 𝓘(ℝ, F) x (V x)) w +
        fderiv ℝ g x (tangentSpaceCastModel 𝓘(ℝ, F) x (V x)) w u -
        fderiv ℝ g x w u (tangentSpaceCastModel 𝓘(ℝ, F) x (V x)) := by
  -- The constant field with value `a`, as a section of the tangent bundle.
  let C (a : F) : Π y : F, TangentSpace 𝓘(ℝ, F) y :=
    fun y ↦ (tangentSpaceCastModel 𝓘(ℝ, F) y).symm a
  -- Read in the model space, the field `V` is the map `W`.
  let W : F → F := fun y ↦ tangentSpaceCastModel 𝓘(ℝ, F) y (V y)
  have hW : DifferentiableAt ℝ W x := hV
  have hWV : fderiv ℝ W x = fderiv ℝ V x := rfl
  have hC (a : F) : MDiffAt (T% (C a)) x :=
    mdifferentiableAt_vectorSpace_iff_differentiableAt.2 (differentiableAt_const a)
  have hV' : MDiffAt (T% V) x := mdifferentiableAt_vectorSpace_iff_differentiableAt.2 hV
  have hfd (f : F → ℝ) (v : TangentSpace 𝓘(ℝ, F) x) :
      mvfderiv 𝓘(ℝ, F) f x v = fderiv ℝ f x (tangentSpaceCastModel 𝓘(ℝ, F) x v) := by
    rw [mvfderiv_eq_fderiv]
    rfl
  have hinner (A B : Π y : F, TangentSpace 𝓘(ℝ, F) y) : (fun y ↦ inner ℝ (A y) (B y)) =
      fun y ↦ g y (tangentSpaceCastModel 𝓘(ℝ, F) y (A y)) (tangentSpaceCastModel 𝓘(ℝ, F) y (B y)) :=
    funext fun y ↦ hg y (A y) (B y)
  -- The three Lie brackets of the Koszul formula, read in the model space.
  have hbr₁ : tangentSpaceCastModel 𝓘(ℝ, F) x (mlieBracket 𝓘(ℝ, F) (C u) V x) =
      fderiv ℝ W x u := by
    rw [TauCeti.mlieBracket_eq_lieBracket]
    -- In the model space the bracket is `DV(u) - D(const u)(V)`.
    change fderiv ℝ W x u - fderiv ℝ (fun _ : F ↦ u) x (W x) = fderiv ℝ W x u
    simp
  have hbr₂ : tangentSpaceCastModel 𝓘(ℝ, F) x (mlieBracket 𝓘(ℝ, F) (C u) (C w) x) = 0 :=
    TauCeti.mlieBracket_const_model_space u w x
  have hbr₃ : tangentSpaceCastModel 𝓘(ℝ, F) x (mlieBracket 𝓘(ℝ, F) V (C w) x) =
      -fderiv ℝ W x w := by
    rw [TauCeti.mlieBracket_eq_lieBracket]
    -- In the model space the bracket is `D(const w)(V) - DV(w)`.
    change fderiv ℝ (fun _ : F ↦ w) x (W x) - fderiv ℝ W x w = -fderiv ℝ W x w
    simp
  have hcomm (a b : F) : g x a b = g x b a := by
    have h := hg x ((tangentSpaceCastModel 𝓘(ℝ, F) x).symm b)
      ((tangentSpaceCastModel 𝓘(ℝ, F) x).symm a)
    rw [real_inner_comm, hg] at h
    simpa using h
  have h := CovariantDerivative.two_inner_leviCivitaConnection_eq_koszul
    (X := C u) (Y := V) (Z := C w) (hC u) hV' (hC w)
  rw [koszul_apply, hinner, hinner, hinner, hfd, hfd, hfd, hg, hg, hg, hg, hbr₁, hbr₂,
    hbr₃] at h
  simp only [C, ContinuousLinearEquiv.apply_symm_apply] at h
  rw [fderiv_bilin_apply hgx hW (differentiableAt_const w),
    fderiv_bilin_apply hgx (differentiableAt_const w) (differentiableAt_const u),
    fderiv_bilin_apply hgx (differentiableAt_const u) hW] at h
  simp only [fderiv_const_apply, hWV, map_zero, zero_apply, add_zero, map_neg, neg_apply] at h
  rw [h, hcomm u]
  ring

/-- The Levi-Civita derivative `∇_u V` of a vector field `V` on the model space `F`, for a metric
given by the field of bilinear forms `g`, is the flat derivative `DV(u)` plus any vector `γ`
solving the Christoffel formula of the first kind
`2 g(γ, w) = (Dg(u))(V, w) + (Dg(V))(w, u) - (Dg(w))(u, V)` for all `w`. -/
theorem leviCivitaConnection_model_space_eq_fderiv_add
    (hg : ∀ y (v w : TangentSpace 𝓘(ℝ, F) y), inner ℝ v w =
      g y (tangentSpaceCastModel 𝓘(ℝ, F) y v) (tangentSpaceCastModel 𝓘(ℝ, F) y w))
    (hgx : DifferentiableAt ℝ g x) (hV : DifferentiableAt ℝ V x) (u γ : F)
    (hγ : ∀ w, 2 * g x γ w = fderiv ℝ g x u (tangentSpaceCastModel 𝓘(ℝ, F) x (V x)) w +
      fderiv ℝ g x (tangentSpaceCastModel 𝓘(ℝ, F) x (V x)) w u -
      fderiv ℝ g x w u (tangentSpaceCastModel 𝓘(ℝ, F) x (V x))) :
    tangentSpaceCastModel 𝓘(ℝ, F) x
        (leviCivitaConnection 𝓘(ℝ, F) F V x ((tangentSpaceCastModel 𝓘(ℝ, F) x).symm u)) =
      fderiv ℝ V x u + γ := by
  -- The metric at `x` is nondegenerate, being an inner product.
  have hnondeg (b : F) (hb : ∀ w, g x b w = 0) : b = 0 := by
    have h := hg x ((tangentSpaceCastModel 𝓘(ℝ, F) x).symm b)
      ((tangentSpaceCastModel 𝓘(ℝ, F) x).symm b)
    rw [ContinuousLinearEquiv.apply_symm_apply, hb, inner_self_eq_zero] at h
    simpa using h
  rw [← sub_eq_zero]
  refine hnondeg _ fun w ↦ ?_
  have h₁ := two_mul_leviCivitaConnection_model_space hg hgx hV u w
  have h₂ := hγ w
  simp only [map_sub, map_add, sub_apply, add_apply]
  linarith

end Christoffel

end TauCeti.Manifold
