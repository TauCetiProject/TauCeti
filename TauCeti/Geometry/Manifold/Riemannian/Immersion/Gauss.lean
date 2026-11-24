/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.Immersion.SecondFundamentalForm
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Immersion
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Sectional.Basic
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric.Basic
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity
import TauCeti.Geometry.Manifold.MFDeriv.Inner
import TauCeti.Geometry.Manifold.VectorField.LieBracket
import TauCeti.Geometry.Manifold.VectorField.ModelChart
import Mathlib.Tactic.Linarith

/-!
# The Gauss curvature equation for Euclidean parametrizations

For a `C³` map `f : E → F` inducing the actual smooth Riemannian metric of its finite-dimensional
coordinate source, the native Levi-Civita curvature is determined by the existing second
fundamental form `B = TauCeti.secondFundamentalForm ℝ f x`:

`⟪R(u,v)w,z⟫ = ⟪B(u,z),B(v,w)⟫ - ⟪B(u,w),B(v,z)⟫`.

The proof differentiates the native connection Gauss formula and cancels the ambient ordinary
second derivatives. It also identifies `B` as the difference between ambient and lifted intrinsic
derivatives, and gives the sectional-curvature quotient on arbitrary tangent pairs.

The ambient inner-product space may be infinite dimensional and incomplete. The metric identity
is global, as in the native connection formula; no varying curved ambient metric or local
induced-metric extension is asserted here.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer, 2018, Chapter 8.
* The formal Gauss-equation development in
  [lean-eval-submissions](https://github.com/frenzymath/lean-eval-submissions) and
  [PoincareConjecture](https://github.com/frenzymath/PoincareConjecture).
-/

public section

open Bundle CovariantDerivative Manifold VectorField
open scoped ContDiff Manifold
noncomputable section
namespace TauCeti
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
local notation "J" => 𝓘(ℝ, E)
local notation "∇" => leviCivitaConnection J E
local notation "C" => TauCeti.constVectorField
variable [RiemannianBundle (fun x : E ↦ TangentSpace 𝓘(ℝ, E) x)]

section C1Metric

variable [IsContMDiffRiemannianBundle 𝓘(ℝ, E) 1 E (fun x : E ↦ TangentSpace 𝓘(ℝ, E) x)]
private def G (a b : E) (x : E) : TangentSpace J x := ∇ (C b) x (C a x)

private theorem inner_connection_const {f : E → F} {x : E} (hf : ContDiffAt ℝ 2 f x)
    (hg : ∀ x (u v : TangentSpace J x),
      inner ℝ u v = inner ℝ (mvfderiv J f x u) (mvfderiv J f x v))
    (u v w : E) :
    inner ℝ (G u v x) (C w x) =
      inner ℝ (fderiv ℝ (fderiv ℝ f) x u v) (fderiv ℝ f x w) := by
  have h : inner ℝ (G u v x) (C w x) =
      inner ℝ (fderiv ℝ (fun y ↦ fderiv ℝ f y v) x u) (fderiv ℝ f x w) := by
    have hconn :=
      (isLeviCivitaConnection_leviCivitaConnection (I := J)).inner_apply_eq_inner_mvfderiv
        hf.contMDiffAt hg ((contMDiff_constVectorField (n := ∞) u).mdifferentiable (by simp) x)
        ((contMDiff_constVectorField (n := ∞) v).mdifferentiable (by simp) x) (C w x)
    simp_rw [TauCeti.mvfderiv_eq_fderiv_apply] at hconn
    simpa only [G, constVectorField_apply, NormedSpace.fromTangentSpace_symm_apply] using hconn
  have hfd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt_one
  rw [fderiv_clm_apply hfd (differentiableAt_const v)] at h
  simpa using h

/-- The second fundamental form of an isometric parametrization is its ordinary second
 derivative minus the image of the intrinsic Levi-Civita derivative of constant coordinate
 fields. The source metric needs only `C¹` regularity and the parametrization only `C²` at the
 evaluation point; the metric identity concerns the actual native source metric globally. -/
theorem secondFundamentalForm_eq_fderiv_sub_leviCivitaConnection {f : E → F} {x : E}
    (hf : ContDiffAt ℝ 2 f x)
    (hg : ∀ x (u v : TangentSpace J x),
      inner ℝ u v = inner ℝ (mvfderiv J f x u) (mvfderiv J f x v))
    (u v : E) :
    secondFundamentalForm ℝ f x u v = fderiv ℝ (fderiv ℝ f) x u v -
      fderiv ℝ f x (tangentSpaceCastModel J x
        (∇ (fun y ↦ (tangentSpaceCastModel J y).symm v) x
          ((tangentSpaceCastModel J x).symm u))) := by
  -- The native evaluation law identifies the displayed tangent casts with constant fields.
  -- Its expected type expands the model-space identification `fromTangentSpace`.
  have hfield (a : E) : C a = fun y ↦ (tangentSpaceCastModel J y).symm a :=
    funext (constVectorField_apply a)
  rw [← hfield v, ← congrFun (hfield u) x]
  -- Abbreviate the connection of these constant fields by `G u v`.
  change secondFundamentalForm ℝ f x u v =
    fderiv ℝ (fderiv ℝ f) x u v - fderiv ℝ f x (tangentSpaceCastModel J x (G u v x))
  rw [TauCeti.secondFundamentalForm_apply, Submodule.starProjection_orthogonal_val]
  congr 1
  have hmem : fderiv ℝ f x (tangentSpaceCastModel J x (G u v x)) ∈
      (fderiv ℝ f x).range := ⟨tangentSpaceCastModel J x (G u v x), rfl⟩
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero hmem
  rintro _ ⟨w, rfl⟩
  rw [inner_sub_left]
  have hm := hg x (G u v x) (C w x)
  simp_rw [TauCeti.mvfderiv_eq_fderiv_apply] at hm
  -- Apply the native tangent identification explicitly, preserving the source metric.
  have hcast : tangentSpaceCastModel J x (G u v x) = G u v x :=
    NormedSpace.fromTangentSpace_apply x (G u v x)
  have hm' : inner ℝ (G u v x) (C w x) =
      inner ℝ (fderiv ℝ f x (tangentSpaceCastModel J x (G u v x))) (fderiv ℝ f x w) := by
    simpa only [hcast, constVectorField_apply, NormedSpace.fromTangentSpace_symm_apply] using hm
  exact sub_eq_zero.mpr ((inner_connection_const hf hg u v w).symm.trans hm')

private theorem inner_secondFundamentalForm_pair {f : E → F} {x : E} (hf : ContDiffAt ℝ 2 f x)
    (hg : ∀ x (u v : TangentSpace J x),
      inner ℝ u v = inner ℝ (mvfderiv J f x u) (mvfderiv J f x v))
    (a b c d : E) :
    inner ℝ (TauCeti.secondFundamentalForm ℝ f x a b)
        (TauCeti.secondFundamentalForm ℝ f x c d) =
      inner ℝ (fderiv ℝ (fderiv ℝ f) x a b) (fderiv ℝ (fderiv ℝ f) x c d) -
        inner ℝ (G a b x) (G c d x) := by
  have h (a b : E) : secondFundamentalForm ℝ f x a b =
      fderiv ℝ (fderiv ℝ f) x a b - fderiv ℝ f x (tangentSpaceCastModel J x (G a b x)) := by
    have hfield (a : E) : C a = fun y ↦ (tangentSpaceCastModel J y).symm a :=
      funext (constVectorField_apply a)
    simpa only [G, hfield] using
      secondFundamentalForm_eq_fderiv_sub_leviCivitaConnection hf hg a b
  rw [h a b, h c d]
  rw [inner_sub_left, inner_sub_right, inner_sub_right]
  have h₁ := inner_connection_const hf hg a b (tangentSpaceCastModel J x (G c d x))
  have h₂ := inner_connection_const hf hg c d (tangentSpaceCastModel J x (G a b x))
  have h₃ := hg x (G a b x) (G c d x)
  simp only [TauCeti.mvfderiv_eq_fderiv_apply] at h₃
  have h₃' : inner ℝ (G a b x) (G c d x) =
      inner ℝ (fderiv ℝ f x (tangentSpaceCastModel J x (G a b x)))
        (fderiv ℝ f x (tangentSpaceCastModel J x (G c d x))) := h₃
  simp only [constVectorField_apply, NormedSpace.fromTangentSpace,
    ContinuousLinearEquiv.symm_apply_apply] at h₁ h₂
  have h₂' : inner ℝ (fderiv ℝ f x (tangentSpaceCastModel J x (G a b x)))
      (fderiv ℝ (fderiv ℝ f) x c d) = inner ℝ (G a b x) (G c d x) := by
    calc
      _ = inner ℝ (fderiv ℝ (fderiv ℝ f) x c d)
          (fderiv ℝ f x (tangentSpaceCastModel J x (G a b x))) := real_inner_comm _ _
      _ = inner ℝ (G c d x) (G a b x) := h₂.symm
      _ = _ := real_inner_comm _ _
  linarith

end C1Metric

section SmoothMetric

variable [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : E ↦ TangentSpace 𝓘(ℝ, E) x)]

private theorem hG (a b : E) : CMDiff ∞ (T% (G a b)) :=
  ∇.contMDiff_apply (contMDiff_constVectorField a) (contMDiff_constVectorField b)

private theorem inner_connection_iterated {f : E → F} (hf : ContDiff ℝ 3 f)
    (hg : ∀ x (u v : TangentSpace J x),
      inner ℝ u v = inner ℝ (mvfderiv J f x u) (mvfderiv J f x v))
    (x u v w z : E) :
    inner ℝ (∇ (G v w) x (C u x)) (C z x) =
      inner ℝ (fderiv ℝ (fun y ↦ fderiv ℝ (fderiv ℝ f) y v w) x u)
        (fderiv ℝ f x z) +
      inner ℝ (fderiv ℝ (fderiv ℝ f) x v w) (fderiv ℝ (fderiv ℝ f) x u z) -
      inner ℝ (G v w x) (G u z x) := by
  have hdf : ContDiff ℝ 2 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hH : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ f)) := hdf.fderiv_right (by norm_num)
  have he : (fun y ↦ inner ℝ (G v w y) (C z y)) =
      fun y ↦ inner ℝ (fderiv ℝ (fderiv ℝ f) y v w) (fderiv ℝ f y z) :=
    funext fun y ↦ inner_connection_const (hf.contDiffAt.of_le (by norm_num)) hg v w z
  have hm := (isMetricCompatible_leviCivitaConnection J).mvfderiv_inner_eq (C u)
    ((hG v w).mdifferentiable (by simp) x)
    ((contMDiff_constVectorField (n := ∞) z).mdifferentiable (by simp) x)
  rw [he, TauCeti.mvfderiv_inner_apply
    (((hH.clm_apply contDiff_const).clm_apply contDiff_const).contMDiff.mdifferentiable
      (by simp) x)
    ((hdf.clm_apply contDiff_const).contMDiff.mdifferentiable (by simp) x)] at hm
  simp_rw [TauCeti.mvfderiv_eq_fderiv_apply] at hm
  have hm' : inner ℝ (fderiv ℝ (fun y ↦ fderiv ℝ (fderiv ℝ f) y v w) x u)
      (fderiv ℝ f x z) +
    inner ℝ (fderiv ℝ (fderiv ℝ f) x v w)
      (fderiv ℝ (fun y ↦ fderiv ℝ f y z) x u) =
    inner ℝ (∇ (G v w) x (C u x)) (C z x) + inner ℝ (G v w x) (G u z x) := by
    simpa only [constVectorField_apply, NormedSpace.fromTangentSpace_symm_apply, G] using hm
  rw [fderiv_clm_apply (hdf.differentiable (by simp) x) (differentiableAt_const z)] at hm'
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    fderiv_const_apply, zero_apply, map_zero, zero_add, ContinuousLinearMap.flip_apply] at hm'
  linarith

/-- The Gauss equation for a `C³` isometric parametrization into a real inner-product space.
 The source curvature is the native Levi-Civita tensor and the second fundamental form is the
 normal projection of the ordinary second derivative. The ambient space need not be finite
 dimensional or complete. -/
theorem inner_curvatureTensor_eq_secondFundamentalForm {f : E → F} (hf : ContDiff ℝ 3 f)
    (hg : ∀ x (u v : TangentSpace J x),
      inner ℝ u v = inner ℝ (mvfderiv J f x u) (mvfderiv J f x v))
    (x u v w z : E) :
    inner ℝ (∇.curvatureTensor x
      ((tangentSpaceCastModel J x).symm u) ((tangentSpaceCastModel J x).symm v)
      ((tangentSpaceCastModel J x).symm w)) ((tangentSpaceCastModel J x).symm z) =
      inner ℝ (TauCeti.secondFundamentalForm ℝ f x u z)
        (TauCeti.secondFundamentalForm ℝ f x v w) -
      inner ℝ (TauCeti.secondFundamentalForm ℝ f x u w)
        (TauCeti.secondFundamentalForm ℝ f x v z) := by
  -- The native evaluation law identifies the tensor arguments with constant fields;
  -- the expected type expands the model-space identification `fromTangentSpace`.
  have hfield (a : E) : C a x = (tangentSpaceCastModel J x).symm a :=
    constVectorField_apply a x
  rw [← hfield u, ← hfield v, ← hfield w, ← hfield z]
  have hdf : ContDiff ℝ 2 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hcomm := mvfderiv_mlieBracket
    ((hdf.clm_apply (contDiff_const (c := w))).contMDiff.contMDiffAt)
    (by simp [minSmoothness_of_isRCLikeNormedField])
    ((contMDiff_constVectorField (n := ∞) u).mdifferentiable (by simp) x)
    ((contMDiff_constVectorField (n := ∞) v).mdifferentiable (by simp) x)
  have hbr : mlieBracket J (C u) (C v) x = 0 := by
    have hc (a : E) : C a = fun _ ↦ a := by
      funext y
      exact (constVectorField_apply a y).trans (NormedSpace.fromTangentSpace_symm_apply y a)
    rw [hc u, hc v]
    exact mlieBracket_const_model_space u v x
  rw [hbr, map_zero] at hcomm
  simp_rw [TauCeti.mvfderiv_eq_fderiv_apply] at hcomm
  simp only [constVectorField_apply, NormedSpace.fromTangentSpace_symm_apply] at hcomm
  have hd (a y : E) : fderiv ℝ (fun q ↦ fderiv ℝ f q w) y a =
      fderiv ℝ (fderiv ℝ f) y a w := by
    rw [fderiv_clm_apply (hdf.differentiable (by simp) y) (differentiableAt_const w)]
    simp
  simp only [hd] at hcomm
  have hinner := congrArg (fun t ↦ inner ℝ t (fderiv ℝ f x z)) hcomm
  rw [inner_zero_left, inner_sub_left] at hinner
  rw [∇.curvatureTensor_apply x (contMDiff_constVectorField u) (contMDiff_constVectorField v)
      (contMDiff_constVectorField w), curvatureOperator_apply,
    hbr, map_zero, sub_zero, inner_sub_left]
  -- Curvature expansion contains the field `y ↦ ∇ (C w) y (C v y)`; it is precisely `G v w`.
  change inner ℝ (∇ (G v w) x (C u x)) (C z x) -
      inner ℝ (∇ (G u w) x (C v x)) (C z x) = _
  rw [inner_connection_iterated hf hg, inner_connection_iterated hf hg,
    inner_secondFundamentalForm_pair (hf.contDiffAt.of_le (by norm_num)) hg,
    inner_secondFundamentalForm_pair (hf.contDiffAt.of_le (by norm_num)) hg]
  linarith [real_inner_comm (fderiv ℝ (fderiv ℝ f) x u z)
    (fderiv ℝ (fderiv ℝ f) x v w), real_inner_comm (G u z x) (G v w x)]

/-- The sectional curvature of a `C³` isometric parametrization is the Gauss numerator divided
 by the source Gram determinant. The quotient is total, so the formula also holds on dependent
 pairs, where native sectional curvature is zero. -/
theorem sectionalCurvature_eq_secondFundamentalForm {f : E → F} (hf : ContDiff ℝ 3 f)
    (hg : ∀ x (u v : TangentSpace J x),
      inner ℝ u v = inner ℝ (mvfderiv J f x u) (mvfderiv J f x v))
    (x u v : E) :
    ∇.sectionalCurvature (isMetricCompatible_leviCivitaConnection J) x
        ((tangentSpaceCastModel J x).symm u) ((tangentSpaceCastModel J x).symm v) =
      (inner ℝ (secondFundamentalForm ℝ f x u u) (secondFundamentalForm ℝ f x v v) -
        ‖secondFundamentalForm ℝ f x u v‖ ^ 2) /
      (Matrix.gram ℝ ![(tangentSpaceCastModel J x).symm u,
        (tangentSpaceCastModel J x).symm v]).det := by
  rw [CovariantDerivative.sectionalCurvature_apply,
    inner_curvatureTensor_eq_secondFundamentalForm hf hg x u v v u,
    (hf.contDiffAt.of_le (by norm_num : (2 : ℕ∞ω) ≤ 3)).secondFundamentalForm_apply_comm v u,
    real_inner_self_eq_norm_sq]

end SmoothMetric

end TauCeti
