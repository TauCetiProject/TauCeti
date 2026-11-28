/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Basic
public import Mathlib.Geometry.Manifold.Riemannian.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongMap.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Christoffel.Basic
import TauCeti.Analysis.Calculus.FDeriv.ContinuousLinearMap
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongMap.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Coordinate.ModelSpace
import TauCeti.Geometry.Manifold.VectorField.LieBracket
import TauCeti.Geometry.Manifold.VectorField.Regularity
import TauCeti.Topology.Algebra.Module.BilinearForm

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
right-hand side is then the value of the connection. Together with
`TauCeti.Manifold.christoffelMap_model_space`, which reads the Christoffel map on the model space
as the value of the connection on constant fields, these turn an explicit metric on `F` into its
Christoffel map, which is the input of the coordinate curvature formula of
`TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Coordinates`.

## Main results

* `TauCeti.Manifold.two_mul_leviCivitaConnection_model_space`: the Christoffel formula of the
  first kind for the Levi-Civita connection of a differentiable metric on `F`.
* `TauCeti.Manifold.leviCivitaConnection_model_space_eq_fderiv_add`: the Levi-Civita connection
  is the flat derivative plus any vector solving the Christoffel formula of the first kind.
* `TauCeti.Manifold.leviCivitaConnection_model_space_eq_fderiv_add_christoffelSecondKind`: the
  Levi-Civita connection is the flat derivative plus the Christoffel symbols of the second kind
  of the metric, as constructed for any nondegenerate metric in
  `TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Christoffel.Basic`.
* `TauCeti.Manifold.leviCivitaConnection_eq_fderiv_model_space`: for the standard metric, the
  Levi-Civita connection is the ordinary Fréchet derivative.
* `TauCeti.Manifold.christoffelMap_leviCivita_model_space`: the Christoffel map of the standard
  Riemannian metric vanishes.
* `TauCeti.Manifold.alongCurveWithin_leviCivitaConnection_model_space` and
  `TauCeti.Manifold.alongCurve_leviCivitaConnection_model_space`: the covariant derivative of a
  field along a curve is its ordinary derivative, within a parameter set or unrestricted.
* `TauCeti.Manifold.alongCurveWithin_add_smul_model_space` and
  `TauCeti.Manifold.alongCurve_add_smul_model_space`: the covariant derivative of an affine field.
* `TauCeti.Manifold.sectionCoord_model_space`: a field along a map into `F` is its own coordinate
  reading in every tangent trivialization of `F`.
* `TauCeti.Manifold.alongMap_leviCivitaConnection_model_space`: the covariant derivative of a
  field along a map into `F` is its ordinary derivative.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 5: Theorem 5.10 (the Koszul formula) and the Christoffel symbols of a metric in
  coordinates.
* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser (1992), Chapter 2, §3.
-/

public section

open Bundle CovariantDerivative Manifold Module Set VectorField
open scoped Manifold ContDiff

noncomputable section

namespace TauCeti.Manifold

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ### The Christoffel formula of the first kind -/

section Christoffel

variable [FiniteDimensional ℝ F]
  [RiemannianBundle (fun x : F ↦ TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) 1 F (fun x : F ↦ TangentSpace 𝓘(ℝ, F) x)]
  {g : F → F →L[ℝ] F →L[ℝ] ℝ} {x : F} {V : Π y : F, TangentSpace 𝓘(ℝ, F) y}

/-- **The Christoffel formula of the first kind.** If the Riemannian metric of the model space
`F` is the field of bilinear forms `g`, then the Levi-Civita derivative of
a vector field `V` differentiable at `x` satisfies
`2 g(∇_u V, w) = 2 g(DV(u), w) + (Dg(u))(V, w) + (Dg(V))(w, u) - (Dg(w))(u, V)`.
Tangent vectors are read in the model space through `tangentSpaceCastModel`. -/
theorem two_mul_leviCivitaConnection_model_space
    (hg : ∀ y (v w : TangentSpace 𝓘(ℝ, F) y), inner ℝ v w =
      g y (tangentSpaceCastModel 𝓘(ℝ, F) y v) (tangentSpaceCastModel 𝓘(ℝ, F) y w))
    (hV : DifferentiableAt ℝ V x) (u w : F) :
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
    -- `NormedSpace.fromTangentSpace` is `tangentSpaceCastModel` by definition.
    rfl
  have hinner (A B : Π y : F, TangentSpace 𝓘(ℝ, F) y) : (fun y ↦ inner ℝ (A y) (B y)) =
      fun y ↦ g y (tangentSpaceCastModel 𝓘(ℝ, F) y (A y)) (tangentSpaceCastModel 𝓘(ℝ, F) y (B y)) :=
    funext fun y ↦ hg y (A y) (B y)
  -- The metric coefficients are differentiable, being inner products of constant fields.
  have hgx : DifferentiableAt ℝ g x := by
    refine TauCeti.differentiableAt_clm_apply₂.2 fun a b ↦ ?_
    have h : MDiffAt (fun y ↦ inner ℝ (C a y) (C b y)) x :=
      MDifferentiableAt.inner_bundle (IB := 𝓘(ℝ, F)) (F := F)
        (E := fun y : F ↦ TangentSpace 𝓘(ℝ, F) y) (b := id) (hC a) (hC b)
    rw [hinner] at h
    simpa only [C, ContinuousLinearEquiv.apply_symm_apply] using
      mdifferentiableAt_iff_differentiableAt.1 h
  -- The three Lie brackets of the Koszul formula, read in the model space.
  have hbr₁ : tangentSpaceCastModel 𝓘(ℝ, F) x (mlieBracket 𝓘(ℝ, F) (C u) V x) =
      fderiv ℝ W x u := mlieBracket_const_left_model_space u V x
  have hbr₂ : tangentSpaceCastModel 𝓘(ℝ, F) x (mlieBracket 𝓘(ℝ, F) (C u) (C w) x) = 0 :=
    mlieBracket_const_model_space u w x
  have hbr₃ : tangentSpaceCastModel 𝓘(ℝ, F) x (mlieBracket 𝓘(ℝ, F) V (C w) x) =
      -fderiv ℝ W x w := mlieBracket_const_right_model_space V w x
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
    (hV : DifferentiableAt ℝ V x) (u γ : F)
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
  have h₁ := two_mul_leviCivitaConnection_model_space hg hV u w
  have h₂ := hγ w
  simp only [map_sub, map_add, sub_apply, add_apply]
  linarith

/-- The Levi-Civita derivative `∇_u V` of a vector field `V` on the model space `F`, for a metric
given by the field of bilinear forms `g`, is the flat derivative `DV(u)` plus the Christoffel
symbols of the second kind of `g`: `∇_u V = DV(u) + Γ(u, V)`. Thus the Christoffel symbols of a
general nondegenerate metric specialize, for a positive-definite one, to those of Mathlib's
Levi-Civita connection. -/
theorem leviCivitaConnection_model_space_eq_fderiv_add_christoffelSecondKind
    (hg : ∀ y (v w : TangentSpace 𝓘(ℝ, F) y), inner ℝ v w =
      g y (tangentSpaceCastModel 𝓘(ℝ, F) y v) (tangentSpaceCastModel 𝓘(ℝ, F) y w))
    (hV : DifferentiableAt ℝ V x) (u : F) :
    tangentSpaceCastModel 𝓘(ℝ, F) x
        (leviCivitaConnection 𝓘(ℝ, F) F V x ((tangentSpaceCastModel 𝓘(ℝ, F) x).symm u)) =
      fderiv ℝ V x u + christoffelSecondKind g x u (tangentSpaceCastModel 𝓘(ℝ, F) x (V x)) := by
  -- Read in the model space, the metric is a symmetric positive-definite bilinear form.
  have hinner (y : F) (a b : F) : g y a b = inner ℝ ((tangentSpaceCastModel 𝓘(ℝ, F) y).symm a)
      ((tangentSpaceCastModel 𝓘(ℝ, F) y).symm b) := by
    rw [hg]
    simp
  have hcomm (y a b : F) : g y a b = g y b a := by
    rw [hinner y a b, hinner y b a, real_inner_comm]
  have hsep : (g x).toBilinForm.SeparatingLeft := fun a ha ↦ by
    have h := ha a
    rw [ContinuousLinearMap.toBilinForm_apply, hinner, inner_self_eq_zero] at h
    simpa using h
  have hnd : (g x).toBilinForm.Nondegenerate :=
    LinearMap.IsRefl.nondegenerate_iff_separatingLeft
      (ContinuousLinearMap.isSymm_toBilinForm_iff.2 (hcomm x)).isRefl |>.2 hsep
  refine leviCivitaConnection_model_space_eq_fderiv_add hg hV u _ fun w ↦ ?_
  rw [apply_christoffelSecondKind hnd, christoffelFirstKind_apply,
    TauCeti.fderiv_apply_apply_comm (Filter.Eventually.of_forall (hcomm ·))
      (tangentSpaceCastModel 𝓘(ℝ, F) x (V x)) w]
  ring

/-- For the standard Riemannian metric on a finite-dimensional real inner-product space, the
Levi-Civita derivative is the ordinary Fréchet derivative. -/
theorem leviCivitaConnection_eq_fderiv_model_space
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {V : ∀ y : F, TangentSpace (modelWithCornersSelf ℝ F) y}
    {x : F} (hV : DifferentiableAt ℝ V x) (u : F) :
    tangentSpaceCastModel (modelWithCornersSelf ℝ F) x
        (leviCivitaConnection (modelWithCornersSelf ℝ F) F V x
          ((tangentSpaceCastModel (modelWithCornersSelf ℝ F) x).symm u)) =
      fderiv ℝ V x u := by
  have h := leviCivitaConnection_model_space_eq_fderiv_add
    (g := fun _ : F ↦ innerSL ℝ)
    (fun _ _ _ ↦ rfl) hV u 0 (fun w ↦ by simp)
  simpa only [add_zero] using h

end Christoffel

/-! ### Fields along a map into the model space -/

section SectionCoord

/-- For a map into the model space `F`, the coordinate reading of a field along the map in any
tangent trivialization of `F` is the field itself, as an `F`-valued map. -/
@[simp]
theorem sectionCoord_model_space {M : Type*} (f : M → F)
    (V : Π y, TangentSpace 𝓘(ℝ, F) (f y)) (a : F) :
    sectionCoord ℝ (F := F) f V a = fun y ↦ (V y : F) := by
  funext t
  rw [sectionCoord_apply, TangentBundle.continuousLinearMapAt_model_space]
  exact one_apply_eq_self (F := F →L[ℝ] F) (V t : F)

end SectionCoord

/-! ### The standard inner-product metric -/

section InnerProductSpace

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

private theorem leviCivitaConnection_const_apply (u v : F) (x : F) :
    leviCivitaConnection 𝓘(ℝ, F) F (fun _ : F ↦ v) x u = 0 := by
  let C (a : F) : ∀ y : F, TangentSpace 𝓘(ℝ, F) y := fun _ ↦ a
  -- Writing the constant sections dependently keeps all Koszul-formula terms well typed.
  change leviCivitaConnection 𝓘(ℝ, F) F (C v) x (C u x) = 0
  have hconst (a : F) :
      MDiffAt (fun y : F ↦ (TotalSpace.mk' F y (C a y) : TangentBundle 𝓘(ℝ, F) F)) x := by
    simpa only [C] using
      ((contMDiffAt_vectorSpace_iff_contDiffAt (n := (1 : ℕ∞ω))
        (V := fun _ : F ↦ a)).2 contDiffAt_const).mdifferentiableAt one_ne_zero
  -- The inner product of two constant fields is constant, so its differential vanishes.
  have hinner (a b : F) : d% (fun y : F ↦ inner ℝ (C a y) (C b y)) x = 0 :=
    mvfderiv_const (I := 𝓘(ℝ, F)) (c := inner ℝ a b)
  -- Constant fields commute, so every bracket term of the Koszul formula vanishes.
  have hbracket (a b c : F) :
      inner ℝ (C a x) (VectorField.mlieBracket 𝓘(ℝ, F) (C b) (C c) x) = 0 := by
    have h : VectorField.mlieBracket 𝓘(ℝ, F) (C b) (C c) x = 0 := by
      simpa only [C] using VectorField.mlieBracket_const_model_space b c x
    rw [h]
    exact inner_zero_right (𝕜 := ℝ) (C a x)
  let w : F := leviCivitaConnection 𝓘(ℝ, F) F (C v) x (C u x)
  -- `w` abbreviates a tangent vector represented in the model vector space.
  change w = 0
  rw [← inner_self_eq_zero (𝕜 := ℝ)]
  -- Re-expose the dependent constant section so the Koszul formula applies directly.
  change inner ℝ (leviCivitaConnection 𝓘(ℝ, F) F (C v) x (C u x)) (C w x) = 0
  rw [leviCivitaConnection_apply_inner 𝓘(ℝ, F)
    (X := C u) (Y := C v) (Z := C w) (hconst u) (hconst v) (hconst w)]
  simp [hinner, hbracket]

/-- The Levi-Civita connection of the standard Riemannian metric differentiates a constant vector
field to zero. -/
@[simp]
theorem leviCivitaConnection_const_model_space (v : F) (x : F) :
    leviCivitaConnection 𝓘(ℝ, F) F (fun _ : F ↦ v) x = 0 := by
  ext u
  simpa using leviCivitaConnection_const_apply (F := F) u v x

/-- The Christoffel map of the standard Riemannian metric on an inner-product space vanishes in
its canonical coordinates. -/
@[simp]
theorem christoffelMap_leviCivita_model_space (x : F) :
    christoffelMap (Module.finBasis ℝ F)
      ((leviCivitaConnection 𝓘(ℝ, F) F).isCovariantDerivativeOn
        (s := (trivializationAt F (TangentSpace 𝓘(ℝ, F)) x).baseSet)) x = 0 := by
  ext v u
  rw [christoffelMap_model_space, leviCivitaConnection_const_model_space]
  -- The zero map on tangent vectors, evaluated at `u`.
  rfl

/-- In an inner-product space the Levi-Civita covariant derivative along a curve is the
derivative within the parameter set. -/
@[simp]
theorem alongCurveWithin_leviCivitaConnection_model_space (γ V : ℝ → F) (s : Set ℝ) (t : ℝ) :
    alongCurveWithin (leviCivitaConnection 𝓘(ℝ, F) F) γ
      (fun r ↦ (V r : TangentSpace 𝓘(ℝ, F) (γ r))) s t = derivWithin V s t := by
  let W : ∀ r, TangentSpace 𝓘(ℝ, F) (γ r) := fun r ↦ V r
  -- Naming the field lets `rw` see it as a section of the tangent bundle along `γ`.
  change alongCurveWithin (leviCivitaConnection 𝓘(ℝ, F) F) γ W s t = _
  rw [alongCurveWithin_apply, alongCurveInChartWithin_apply]
  simp only [christoffelMap_leviCivita_model_space, zero_apply, add_zero]
  rw [sectionCoord_model_space, TangentBundle.symmL_model_space]
  rfl

/-- In an inner-product space the Levi-Civita covariant derivative along a curve is the
ordinary derivative. -/
@[simp]
theorem alongCurve_leviCivitaConnection_model_space (γ V : ℝ → F) (t : ℝ) :
    alongCurve (leviCivitaConnection 𝓘(ℝ, F) F) γ
      (fun r ↦ (V r : TangentSpace 𝓘(ℝ, F) (γ r))) t = deriv V t := by
  exact (alongCurveWithin_univ _ γ
    (fun r ↦ (V r : TangentSpace 𝓘(ℝ, F) (γ r))) t).symm.trans
      ((alongCurveWithin_leviCivitaConnection_model_space γ V univ t).trans
        (congrFun derivWithin_univ t))

/-- The covariant derivative of the affine field `t ↦ u + t • w` along any curve is `w`
within a parameter set with a unique derivative. -/
theorem alongCurveWithin_add_smul_model_space (γ : ℝ → F) {s : Set ℝ} {t : ℝ}
    (hs : UniqueDiffWithinAt ℝ s t) (u w : F) :
    alongCurveWithin (leviCivitaConnection 𝓘(ℝ, F) F) γ
      (fun r ↦ (u + r • w : TangentSpace 𝓘(ℝ, F) (γ r))) s t = w := by
  rw [alongCurveWithin_leviCivitaConnection_model_space]
  have h := (((hasDerivAt_id t).smul_const w).const_add u).hasDerivWithinAt.derivWithin hs
  rw [one_smul] at h
  exact h

/-- The covariant derivative of the affine field `t ↦ u + t • w` along any curve is `w`. -/
theorem alongCurve_add_smul_model_space (γ : ℝ → F) (u w : F) (t : ℝ) :
    alongCurve (leviCivitaConnection 𝓘(ℝ, F) F) γ
      (fun r ↦ (u + r • w : TangentSpace 𝓘(ℝ, F) (γ r))) t = w := by
  exact (alongCurveWithin_univ _ γ
    (fun r ↦ (u + r • w : TangentSpace 𝓘(ℝ, F) (γ r))) t).symm.trans
      (alongCurveWithin_add_smul_model_space γ uniqueDiffWithinAt_univ u w)

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

/-- **Covariant differentiation along a map into a Euclidean space is differentiation.** For the
flat Levi-Civita connection of a finite-dimensional inner product space `F`, the covariant
derivative of a field `V` along a map `f : M → F` is the derivative of `V`, read as an `F`-valued
map. -/
theorem alongMap_leviCivitaConnection_model_space {f : M → F}
    {V : Π y, TangentSpace 𝓘(ℝ, F) (f y)} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, F) f x)
    (hV : MDifferentiableAt I 𝓘(ℝ, F) (fun y ↦ (V y : F)) x) (v : TangentSpace I x) :
    (leviCivitaConnection 𝓘(ℝ, F) F).alongMap I f V x v =
      mfderiv I 𝓘(ℝ, F) (fun y ↦ (V y : F)) x v := by
  have hT : MDifferentiableAt I 𝓘(ℝ, F).tangent
      (fun y ↦ TotalSpace.mk' F (E := TangentSpace 𝓘(ℝ, F)) (f y) (V y)) x := by
    rw [mdifferentiableAt_totalSpace]
    exact ⟨hf, by simpa [trivializationAt_model_space_apply] using hV⟩
  rw [alongMap_apply_of_mem_baseSet _ hT (FiberBundle.mem_baseSet_trivializationAt' (f x))]
  simp only [christoffelMap_leviCivita_model_space, TangentBundle.symmL_model_space,
    sectionCoord_model_space]
  refine Eq.trans ?_ (mvfderiv_apply_eq_mfderiv_apply (I := I) (fun y ↦ (V y : F)) x v)
  -- The goal is well typed only after unfolding `TangentSpace 𝓘(ℝ, F) (f x)` to `F`, so the
  -- zero Christoffel term must be rewritten up to that unfolding.
  erw [zero_apply, add_zero]
  exact one_apply_eq_self (F := F →L[ℝ] F) _

end InnerProductSpace

end TauCeti.Manifold
