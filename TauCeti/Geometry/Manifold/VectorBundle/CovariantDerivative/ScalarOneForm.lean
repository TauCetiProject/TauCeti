/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.DegreeOne
public import TauCeti.Geometry.Manifold.DifferentialForm.VectorField
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric.Affine
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.Bilinear.Section
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Bilinear.SmulRight
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.AddOneForm

/-!
# Twisting a connection by a scalar one-form

Let `V` be a real vector bundle with a connection `∇`, let `J` be a field of endomorphisms of `V`
and let `θ` be a smooth real one-form. The endomorphism-valued one-form
`θ ⊗ J : (σ, v) ↦ θ(v) J σ` (`CovariantDerivative.smulRightOneForm`) gives the connection
`∇ + θ ⊗ J`, that is `(∇ + θ ⊗ J)_v σ = ∇_v σ + θ(v) J σ`, through Mathlib's
`CovariantDerivative.addOneForm`.

This is how a connection on a line bundle twists a connection on `V`. If `V` is a complex vector
bundle, regarded as a real one with `J` the multiplication by `i`, then `∇ + θ ⊗ J` is
`∇ + i θ`: changing a unitary connection on a line `L` by the imaginary one-form `i θ` changes the
tensor product connection on `V ⊗ L` in this way. For the spinor bundles of a `Spinᶜ` structure,
changing the connection on the determinant line by `i b` changes the spin connection by
`i b / 2`, the twist by `θ = b / 2`.

The main result computes the curvature of the twisted connection. If `J` is parallel for `∇`,
then

`R^(∇ + θ ⊗ J)(X, Y) σ = R^∇(X, Y) σ + dθ(X, Y) J σ`

(`CovariantDerivative.curvatureOperator_addOneForm_smulRightOneForm`): the terms quadratic in `θ`
cancel because `J` commutes with itself, and the covariant exterior derivative of `θ ⊗ J` is
`dθ ⊗ J` because `J` is parallel. For a complex line this is the additivity of curvature under
tensor products, `F_(∇ ⊗ (d + iθ)) = F_∇ + i dθ`. The identity holds at a point, under
differentiability hypotheses there only.

The twisted connection keeps the regularity of `∇` when `J` is smooth
(`CovariantDerivative.contMDiffCovariantDerivative_addOneForm_smulRightOneForm`), and it is metric
for a metric `∇` when every `J x` is skew-adjoint
(`CovariantDerivative.IsMetricCompatible.addOneForm_smulRightOneForm`), as multiplication by `i` is
for a Hermitian metric.

## Main results

* `CovariantDerivative.smulRightOneForm`: the endomorphism-valued one-form `θ ⊗ J`.
* `CovariantDerivative.curvatureOperator_addOneForm_smulRightOneForm`: the curvature of
  `∇ + θ ⊗ J` for a parallel `J`.
* `CovariantDerivative.contMDiffCovariantDerivative_addOneForm_smulRightOneForm`: smoothness of
  `∇ + θ ⊗ J`.
* `CovariantDerivative.IsMetricCompatible.addOneForm_smulRightOneForm`: metric compatibility of
  `∇ + θ ⊗ J`.

## References

* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, Vol. I, Interscience,
  1963, Chapter II, §5 (the structure equation of a connection).
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996, §3.1 and §4.1.
-/

public section

noncomputable section

open Bundle VectorField TauCeti
open scoped ContDiff Manifold

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

section Bundle

variable {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)]

/-- The **endomorphism-valued one-form `θ ⊗ J`** of a real one-form `θ` and a field `J` of
endomorphisms: `(θ ⊗ J)(σ, v) = θ(v) J σ` (`CovariantDerivative.smulRightOneForm_apply`). Adding it
to a connection `∇` gives the twisted connection `(∇ + θ ⊗ J)_v σ = ∇_v σ + θ(v) J σ`. As in
`CovariantDerivative.addOneForm`, the section value comes before the tangent vector. -/
def smulRightOneForm (θ : SmoothForm I M ℝ 1) (J : Π x : M, V x →L[ℝ] V x) :
    Π x : M, V x →L[ℝ] TangentSpace I x →L[ℝ] V x :=
  fun x ↦ (ContinuousLinearMap.smulRightL ℝ ℝ ℝ (TangentSpace I x) (V x)
    (SmoothForm.degreeOneEquiv θ x)).comp (J x)

@[simp]
theorem smulRightOneForm_apply (θ : SmoothForm I M ℝ 1) (J : Π x : M, V x →L[ℝ] V x) (x : M)
    (u : V x) (v : TangentSpace I x) :
    smulRightOneForm θ J x u v = θ.val x ![v] • J x u := by
  simp [smulRightOneForm]

/-- The twisted connection `∇ + θ ⊗ J` evaluates as `∇_v σ + θ(v) J σ`. -/
theorem addOneForm_smulRightOneForm_apply [FiberBundle F V] (cov : _root_.CovariantDerivative I F V)
    (θ : SmoothForm I M ℝ 1) (J : Π x : M, V x →L[ℝ] V x) (σ : Π x : M, V x) (x : M)
    (v : TangentSpace I x) :
    cov.addOneForm (smulRightOneForm θ J) σ x v = cov σ x v + θ.val x ![v] • J x (σ x) := by
  simp [addOneForm_apply]

/-- **Curvature of a connection twisted by a scalar one-form.** Let `J` be a field of
endomorphisms of `V` and `θ` a smooth real one-form. If `J σ` is differentiable at `x` with
`∇_v (J σ) = J ∇_v σ` there, then the curvature of `∇ + θ ⊗ J` is

`R^(∇ + θ ⊗ J)(X, Y) σ = R^∇(X, Y) σ + dθ(X, Y) J σ`

at `x`. The other hypotheses are the differentiability at `x` of the vector fields and of the
sections `∇_X σ`, `∇_Y σ`, which the outer covariant derivatives differentiate. -/
theorem curvatureOperator_addOneForm_smulRightOneForm [FiberBundle F V] [VectorBundle ℝ F V]
    (cov : _root_.CovariantDerivative I F V) (θ : SmoothForm I M ℝ 1)
    (J : Π x : M, V x →L[ℝ] V x) {X Y : Π x : M, TangentSpace I x} {σ : Π x : M, V x} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hXσ : MDiffAt (T% (fun y ↦ cov σ y (X y))) x)
    (hYσ : MDiffAt (T% (fun y ↦ cov σ y (Y y))) x)
    (hJσ : MDiffAt (T% (fun y ↦ J y (σ y))) x)
    (hJ : ∀ v, cov (fun y ↦ J y (σ y)) x v = J x (cov σ x v)) :
    curvatureOperator (cov.addOneForm (smulRightOneForm θ J)) X Y σ x =
      curvatureOperator cov X Y σ x + mextDeriv θ.val x ![X x, Y x] • J x (σ x) := by
  -- The coefficients `θ(Z)` of the twist are differentiable functions.
  have hθ {Z : Π y : M, TangentSpace I y} (hZ : MDiffAt (T% Z) x) :
      MDifferentiableAt I 𝓘(ℝ) (fun y ↦ θ.val y ![Z y]) x := by
    simpa only [Matrix.vec_single_eq_const] using
      θ.mdifferentiableAt_apply_vectorField (V := fun _ ↦ Z) (fun _ ↦ hZ)
  -- The twist of `σ` along `Z` is the section `θ(Z) • J σ`.
  have htw (Z : Π y : M, TangentSpace I y) :
      (fun y ↦ smulRightOneForm θ J y (σ y) (Z y)) = fun y ↦ θ.val y ![Z y] • J y (σ y) :=
    funext fun y ↦ smulRightOneForm_apply θ J y (σ y) (Z y)
  have hdiff {Z : Π y : M, TangentSpace I y} (hZ : MDiffAt (T% Z) x) :
      MDiffAt (T% (fun y ↦ smulRightOneForm θ J y (σ y) (Z y))) x := by
    simpa only [smulRightOneForm_apply, Pi.smul_apply'] using (hθ hZ).smul_section hJσ
  -- The Leibniz rule and the parallelism of `J` differentiate the twist.
  have hcov {Z : Π y : M, TangentSpace I y} (hZ : MDiffAt (T% Z) x) (v : TangentSpace I x) :
      cov (fun y ↦ θ.val y ![Z y] • J y (σ y)) x v =
        θ.val x ![Z x] • J x (cov σ x v) + mvfderiv I (fun y ↦ θ.val y ![Z y]) x v • J x (σ x) := by
    have h := cov.isCovariantDerivativeOnUniv.leibniz hJσ (hθ hZ)
    rw [Pi.smul_def'] at h
    rw [h]
    simp [hJ]
  rw [curvatureOperator_addOneForm cov _ hXσ hYσ (hdiff hX) (hdiff hY), htw, htw, hcov hY,
    hcov hX, SmoothForm.mextDeriv_apply_one hX hY]
  simp only [smulRightOneForm_apply, map_smul, smul_apply]
  module

end Bundle

section Smooth

variable {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]

/-- **The twisted connection is as regular as the twist.** If `∇` is a `C^n` connection and `J`
is a `C^n` field of endomorphisms, `n ≤ ∞`, then `∇ + θ ⊗ J` is a `C^n` connection. -/
theorem contMDiffCovariantDerivative_addOneForm_smulRightOneForm {n : WithTop ℕ∞} [ENat.LEInfty n]
    {cov : _root_.CovariantDerivative I F V} (hcov : ContMDiffCovariantDerivative cov n)
    (θ : SmoothForm I M ℝ 1) {J : Π x : M, V x →L[ℝ] V x}
    (hJ : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] F)) n
      (fun x ↦ TotalSpace.mk' (F →L[ℝ] F) (E := fun y ↦ V y →L[ℝ] V y) x (J x))) :
    ContMDiffCovariantDerivative (cov.addOneForm (smulRightOneForm θ J)) n := by
  refine hcov.addOneForm ?_
  have hθ : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) n (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ)
      (E := fun y : M ↦ TangentSpace I y →L[ℝ] ℝ) x (SmoothForm.degreeOneEquiv θ x)) :=
    (SmoothForm.degreeOneEquiv θ).contMDiff.of_le ENat.LEInfty.out
  let _ : ∀ x : M, IsNormableSpace ℝ (TangentSpace I x) :=
    fun x ↦ instIsNormableSpaceTangentSpace I x
  have hA : smulRightOneForm θ J = fun x ↦ ((SmoothForm.degreeOneEquiv θ x).smulRight (J x)).flip :=
    funext fun x ↦ ContinuousLinearMap.ext fun u ↦ ContinuousLinearMap.ext fun v ↦ by simp
  rw [hA]
  exact ContMDiff.clm_bundle_flip (V₁ := fun x : M ↦ TangentSpace I x) (V₂ := V) (V₃ := V)
    fun x ↦ (hθ x).clm_bundle_smulRight (hJ x)

end Smooth

section Metric

variable {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [FiniteDimensional ℝ F] [ContMDiffVectorBundle 1 F V I]
  [IsContMDiffRiemannianBundle I 1 F V]

/-- **The twisted connection of a metric connection by skew-adjoint endomorphisms is metric.** If
`∇` is metric and every `J x` is skew-adjoint, as multiplication by `i` is for a Hermitian metric,
then `∇ + θ ⊗ J` is metric for every real one-form `θ`. -/
theorem IsMetricCompatible.addOneForm_smulRightOneForm {cov : _root_.CovariantDerivative I F V}
    (hcov : cov.IsMetricCompatible) (θ : SmoothForm I M ℝ 1) {J : Π x : M, V x →L[ℝ] V x}
    (hJ : ∀ x (u w : V x), inner ℝ (J x u) w = -inner ℝ u (J x w)) :
    (cov.addOneForm (smulRightOneForm θ J)).IsMetricCompatible :=
  (hcov.addOneForm_iff _).2 fun x v u w ↦ by
    simp [inner_smul_left, inner_smul_right, hJ]

end Metric

end CovariantDerivative
