/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Contractible
public import TauCeti.Geometry.Manifold.ContMDiff.Subtype
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Action
public import TauCeti.Geometry.Manifold.Riemannian.Restriction.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Conformal
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Hyperbolic space in the Poincaré ball model

For a real inner product space `E`, the Poincaré ball model `PoincareBall E` of real hyperbolic
space is the open unit ball `{x : E | ‖x‖ < 1}` endowed with the conformal Riemannian metric
`4 ⟪dx, dy⟫ / (1 - ‖x‖²)²`, normalized to sectional curvature `-1`. Because `x ↦ ‖x‖²` is a
continuous quadratic form on `E`, the conformal factor `4 / (1 - ‖x‖²)²` and the metric are
analytic in every real inner product space, finite- or infinite-dimensional. Every linear isometry
equivalence `A : E ≃ₗᵢ[ℝ] E` restricts to an origin-fixing Riemannian isometry of `PoincareBall E`.

## Main definitions and results

* `TauCeti.poincareBallOpens E`, `TauCeti.PoincareBall E`, `TauCeti.PoincareBall.conformalFactor`,
  and `TauCeti.PoincareBall.riemannianMetric`: the open unit ball and its analytic hyperbolic
  metric `4 ⟪dx, dy⟫ / (1 - ‖x‖²)²`.
* `TauCeti.PoincareBall.inner_def`, `TauCeti.PoincareBall.norm_def`,
  `TauCeti.PoincareBall.eNorm_def`, and `TauCeti.PoincareBall.two_mul_norm_le_norm`.
* `TauCeti.PoincareBall.orthogonalIsometry`, `TauCeti.PoincareBall.orthogonalToIsom`, and
  `TauCeti.PoincareBall.orthogonalToIsom_injective`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 3.
* J. G. Ratcliffe, *Foundations of Hyperbolic Manifolds*, 3rd ed., Springer GTM 149 (2019), §4.5.
-/

public section

open Bundle Manifold Metric TopologicalSpace
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti

variable (E : Type*) [NormedAddCommGroup E]

/-- The open unit ball `{x : E | ‖x‖ < 1}` as an open subset of `E`. -/
def poincareBallOpens : Opens E := ⟨ball 0 1, isOpen_ball⟩

variable {E} in
@[simp] theorem mem_poincareBallOpens {x : E} : x ∈ poincareBallOpens E ↔ ‖x‖ < 1 :=
  mem_ball_zero_iff

/-- The Poincaré ball model of real hyperbolic space: the open unit ball `{x : E | ‖x‖ < 1}` of
`E`, carrying the conformal Riemannian metric `4 ⟪dx, dy⟫ / (1 - ‖x‖²)²` as its
`RiemannianBundle` instance. -/
def PoincareBall : Type _ := poincareBallOpens E

/- `PoincareBall E` is a type synonym for `poincareBallOpens E`, so that it carries its own
Riemannian bundle and Riemannian metric-space instances rather than the Euclidean subspace
metric; the `show poincareBallOpens E from ...` terms below unfold this synonym to access the
open-subset fields and lemmas. -/

namespace PoincareBall

instance : TopologicalSpace (PoincareBall E) :=
  inferInstanceAs (TopologicalSpace (poincareBallOpens E))

instance : ChartedSpace E (PoincareBall E) := inferInstanceAs (ChartedSpace E (poincareBallOpens E))

instance : T3Space (PoincareBall E) := inferInstanceAs (T3Space (poincareBallOpens E))

variable {E}

/-- The vector in `E` represented by a point of the Poincaré ball. -/
@[coe] def coe (x : PoincareBall E) : E := (show poincareBallOpens E from x).val

instance : CoeOut (PoincareBall E) E := ⟨coe⟩

/-- Construct a point of the Poincaré ball from a vector of norm strictly less than `1`. -/
def mk (p : E) (hp : ‖p‖ < 1) : PoincareBall E :=
  (⟨p, mem_poincareBallOpens.2 hp⟩ : poincareBallOpens E)

@[simp] theorem coe_mk (p : E) (hp : ‖p‖ < 1) : (mk p hp : E) = p := (rfl)

/-- The inclusion of the Poincaré ball into `E` is injective. -/
theorem coe_injective : Function.Injective (coe : PoincareBall E → E) := Subtype.val_injective

/-- The inclusion of the Poincaré ball into `E` induces its topology. -/
theorem isInducing_coe : Topology.IsInducing (coe : PoincareBall E → E) :=
  Topology.IsInducing.subtypeVal

@[ext] theorem ext {x y : PoincareBall E} (h : (x : E) = y) : x = y := coe_injective h

/-- Every point of the Poincaré ball has Euclidean norm strictly less than `1`. -/
theorem norm_lt_one (x : PoincareBall E) : ‖(x : E)‖ < 1 :=
  mem_poincareBallOpens.1 (show poincareBallOpens E from x).property

/-- Every point of the Poincaré ball has Euclidean norm at most `1`. -/
theorem norm_le_one (x : PoincareBall E) : ‖(x : E)‖ ≤ 1 := (norm_lt_one x).le

/-- Every point of the Poincaré ball has squared Euclidean norm strictly less than `1`. -/
theorem norm_sq_lt_one (x : PoincareBall E) : ‖(x : E)‖ ^ 2 < 1 :=
  pow_lt_one₀ (norm_nonneg _) (norm_lt_one x) two_ne_zero

/-- The denominator `1 - ‖x‖²` is strictly positive on the Poincaré ball. -/
theorem one_sub_norm_sq_pos (x : PoincareBall E) : 0 < 1 - ‖(x : E)‖ ^ 2 :=
  sub_pos.2 (norm_sq_lt_one x)

@[simp] theorem mk_coe (x : PoincareBall E) : mk (x : E) (norm_lt_one x) = x := (rfl)

/-- The origin of `E` as the base point of the Poincaré ball. -/
instance : Zero (PoincareBall E) := ⟨mk 0 (by simp)⟩

instance : Inhabited (PoincareBall E) := ⟨0⟩

@[simp] theorem coe_zero : ((0 : PoincareBall E) : E) = 0 := (rfl)

@[simp] theorem coe_eq_zero {x : PoincareBall E} : (x : E) = 0 ↔ x = 0 :=
  coe_injective.eq_iff' coe_zero

/-- Antipodal negation on the Poincaré ball. -/
instance : Neg (PoincareBall E) := ⟨fun x ↦ mk (-(x : E)) (by simpa using norm_lt_one x)⟩

@[simp] theorem coe_neg (x : PoincareBall E) : ((-x : PoincareBall E) : E) = -(x : E) := (rfl)

instance : InvolutiveNeg (PoincareBall E) where neg_neg x := ext (by simp)

@[simp] theorem neg_zero : -(0 : PoincareBall E) = 0 := ext (by simp)

/-- Every chart of the Poincaré ball is its inclusion in the model space `E`. -/
@[simp] theorem chartAt_apply (x y : PoincareBall E) : chartAt E x y = (y : E) := (rfl)

/-- The conformal factor `4 / (1 - ‖x‖²)²` multiplying the Euclidean inner product in the Poincaré
ball metric. -/
def conformalFactor (x : PoincareBall E) : ℝ := 4 / (1 - ‖(x : E)‖ ^ 2) ^ 2

theorem conformalFactor_def (x : PoincareBall E) :
    conformalFactor x = 4 / (1 - ‖(x : E)‖ ^ 2) ^ 2 := (rfl)

@[simp] theorem conformalFactor_zero : conformalFactor (0 : PoincareBall E) = 4 := by
  simp [conformalFactor_def]

@[simp] theorem conformalFactor_neg (x : PoincareBall E) :
    conformalFactor (-x) = conformalFactor x := by simp [conformalFactor_def]

/-- The conformal factor is strictly positive everywhere on the Poincaré ball. -/
theorem conformalFactor_pos (x : PoincareBall E) : 0 < conformalFactor x :=
  div_pos (by norm_num) (pow_pos (one_sub_norm_sq_pos x) 2)

/-- The conformal factor is at least `4` everywhere on the Poincaré ball, with equality at `0`. -/
theorem four_le_conformalFactor (x : PoincareBall E) : 4 ≤ conformalFactor x := by
  rw [conformalFactor_def, le_div_iff₀ (pow_pos (one_sub_norm_sq_pos x) 2)]
  nlinarith [one_sub_norm_sq_pos x, sq_nonneg ‖(x : E)‖]

section NormedSpace

variable (E) [NormedSpace ℝ E]

/-- The Poincaré ball is contractible by straight-line contraction to the origin. -/
instance : ContractibleSpace (PoincareBall E) :=
  (convex_ball (0 : E) 1).contractibleSpace ⟨0, by simp⟩

instance : IsManifold 𝓘(ℝ, E) ω (PoincareBall E) :=
  inferInstanceAs (IsManifold 𝓘(ℝ, E) ω (poincareBallOpens E))

variable {E}

/-- Every extended chart of the Poincaré ball acts as the inclusion into `E`. -/
theorem extChartAt_apply (x y : PoincareBall E) : extChartAt 𝓘(ℝ, E) x y = (y : E) := (rfl)

/-- The inclusion of the Poincaré ball into `E` is analytic. -/
theorem contMDiff_coe : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ω (coe : PoincareBall E → E) :=
  contMDiff_subtypeVal (U := poincareBallOpens E)

/-- A map into the Poincaré ball is `C^n` if and only if its composite with the inclusion into `E`
is `C^n`. -/
@[simp] theorem contMDiff_coe_comp_iff
    {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
    {HM : Type*} [TopologicalSpace HM] {I : ModelWithCorners ℝ EM HM}
    {M : Type*} [TopologicalSpace M] [ChartedSpace HM M] {n : ℕ∞ω} {f : M → PoincareBall E} :
    ContMDiff I 𝓘(ℝ, E) n (coe ∘ f) ↔ ContMDiff I 𝓘(ℝ, E) n f :=
  TauCeti.ContMDiff.subtypeVal_comp_iff (poincareBallOpens E) (f : M → poincareBallOpens E)

/-- If a map `f : PoincareBall E → PoincareBall F` restricts an ambient map `A : E → F` with
Fréchet derivative `L` at `x`, then the manifold differential of `f` at `x` is `L`. -/
theorem tangentSpaceCastModel_mfderiv_apply
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : PoincareBall E → PoincareBall F} {A : E → F} {L : E →L[ℝ] F} {x : PoincareBall E}
    (hA : HasFDerivAt A L (x : E)) (hcomp : coe ∘ f = A ∘ coe)
    (v : TangentSpace 𝓘(ℝ, E) x) :
    tangentSpaceCastModel 𝓘(ℝ, F) (f x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x v) =
      L (tangentSpaceCastModel 𝓘(ℝ, E) x v) := by
  -- Read the base point in `poincareBallOpens E`; `tangentSpaceCastModel` acts as the identity.
  have hA' : HasFDerivAt A L (show poincareBallOpens E from x).val := hA
  have h := TauCeti.Manifold.mfderiv_apply_of_subtype_val_comp_eq (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, F))
    (U := poincareBallOpens E) (V := poincareBallOpens F) (f := f) hcomp v
  rwa [hA'.hasMFDerivAt.mfderiv] at h

/-- The vector-valued manifold derivative of the inclusion `PoincareBall E → E` sends each tangent
vector to its model-space coordinate. -/
theorem mvfderiv_coe_apply (x : PoincareBall E) (v : TangentSpace 𝓘(ℝ, E) x) :
    mvfderiv 𝓘(ℝ, E) (coe : PoincareBall E → E) x v = tangentSpaceCastModel 𝓘(ℝ, E) x v := by
  -- `TangentSpace 𝓘(ℝ, E) x` is a type synonym of `E`, and `tangentSpaceCastModel` is the identity
  -- on vectors (`Mathlib/Geometry/Manifold/IsManifold/Basic.lean`).
  have h2 : tangentSpaceCastModel 𝓘(ℝ, E) x v = (v : E) := (rfl)
  exact (TauCeti.Manifold.mvfderiv_subtype_val_apply (U := poincareBallOpens E)
    (show poincareBallOpens E from x) v).trans h2.symm

/-- The differential of the inclusion `PoincareBall E → E` identifies each tangent space with the
ambient tangent space through `tangentSpaceCastModel` and `NormedSpace.fromTangentSpace`. -/
theorem mfderiv_coe (x : PoincareBall E) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (coe : PoincareBall E → E) x =
      ((tangentSpaceCastModel 𝓘(ℝ, E) x).trans
        (NormedSpace.fromTangentSpace (x : E)).symm).toContinuousLinearMap := by
  ext v : 1
  apply (NormedSpace.fromTangentSpace (x : E)).injective
  simpa [mvfderiv] using mvfderiv_coe_apply x v

/-- Near `x`, the inverse canonical tangent-bundle trivialization of `PoincareBall E` agrees with
the model-space coordinate identification `tangentSpaceCastModel`. -/
theorem eventually_symmL_trivializationAt_eq (x : PoincareBall E) :
    ∀ᶠ y in nhds x, ∀ v : E,
      (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x).symmL ℝ y v =
        (tangentSpaceCastModel 𝓘(ℝ, E) y).symm v := by
  filter_upwards [TauCeti.Manifold.eventually_tangentSpaceOpenEquiv_symmL_trivializationAt_eq
    (I := 𝓘(ℝ, E)) (show poincareBallOpens E from x)] with y hy v
  apply (tangentSpaceCastModel 𝓘(ℝ, E) y).injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  set w : TangentSpace 𝓘(ℝ, E) y := (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x).symmL ℝ y v
  -- Both `tangentSpaceCastModel` and `tangentSpaceOpenEquiv` act as the identity on vectors in `E`.
  have hw : tangentSpaceCastModel 𝓘(ℝ, E) y w = (w : E) := (rfl)
  have he := TauCeti.Manifold.tangentSpaceOpenEquiv_apply (I := 𝓘(ℝ, E))
    (show poincareBallOpens E from y) w
  have hy' := hy v
  rw [TangentBundle.symmL_model_space] at hy'
  exact hw.trans (he.symm.trans ((congrArg (NormedSpace.fromTangentSpace (y : E)) hy').trans
    (ContinuousLinearEquiv.apply_symm_apply _ v)))

/-- Reading the differential of a map into `PoincareBall E` in the model space `E` agrees with the
vector-valued derivative of its composition with `coe`. -/
theorem tangentSpaceCastModel_mfderiv_coe_comp
    {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
    {HM : Type*} [TopologicalSpace HM] {I : ModelWithCorners ℝ EM HM}
    {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
    (f : M → PoincareBall E) (x : M) (v : TangentSpace I x) :
    tangentSpaceCastModel 𝓘(ℝ, E) (f x) (mfderiv I 𝓘(ℝ, E) f x v) =
      mvfderiv I (coe ∘ f) x v := by
  -- `tangentSpaceCastModel` is the identity on the model-space vector underlying `TangentSpace`.
  have h1 : tangentSpaceCastModel 𝓘(ℝ, E) (f x) (mfderiv I 𝓘(ℝ, E) f x v) =
      (mfderiv I 𝓘(ℝ, E) f x v : E) := (rfl)
  rw [mvfderiv_apply_eq_mfderiv_apply]
  exact h1.trans (TauCeti.Manifold.mfderiv_subtype_val_comp_apply
    (I := 𝓘(ℝ, E)) (J := I) (U := poincareBallOpens E) (f := f) (x := x) v).symm

end NormedSpace

section InnerProductSpace

variable [InnerProductSpace ℝ E]

/-- The conformal factor `4 / (1 - ‖x‖²)²` is analytic on the Poincaré ball. -/
theorem contMDiff_conformalFactor :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ω (conformalFactor : PoincareBall E → ℝ) := fun x ↦
  (contDiffAt_const.div ((contDiffAt_const.sub (contDiff_norm_sq ℝ).contDiffAt).pow 2)
    (pow_ne_zero 2 (one_sub_norm_sq_pos x).ne')).contMDiffAt.comp x (contMDiff_coe x)

private def euclideanMetric :
    ContMDiffRiemannianMetric 𝓘(ℝ, E) ω E (fun x : PoincareBall E ↦ TangentSpace 𝓘(ℝ, E) x) :=
  (riemannianMetricVectorSpace E).restrictOpenTangentSpace (poincareBallOpens E)

private theorem euclideanMetric_inner (x : PoincareBall E) (v w : TangentSpace 𝓘(ℝ, E) x) :
    euclideanMetric.inner x v w =
      inner ℝ (tangentSpaceCastModel 𝓘(ℝ, E) x v) (tangentSpaceCastModel 𝓘(ℝ, E) x w) := by
  let y : poincareBallOpens E := x
  have h := Bundle.ContMDiffRiemannianMetric.restrictOpenTangentSpace_inner
    (riemannianMetricVectorSpace E) (poincareBallOpens E) y v w
  rwa [TauCeti.Manifold.tangentSpaceOpenEquiv_apply (I := 𝓘(ℝ, E)) y v,
    TauCeti.Manifold.tangentSpaceOpenEquiv_apply (I := 𝓘(ℝ, E)) y w] at h

/-- The analytic hyperbolic metric `4 ⟪dx, dy⟫ / (1 - ‖x‖²)²` on the Poincaré ball. -/
def riemannianMetric :
    ContMDiffRiemannianMetric 𝓘(ℝ, E) ω E (fun x : PoincareBall E ↦ TangentSpace 𝓘(ℝ, E) x) :=
  euclideanMetric.rescale conformalFactor contMDiff_conformalFactor conformalFactor_pos

/-- The Poincaré ball carries the hyperbolic metric `4 ⟪dx, dy⟫ / (1 - ‖x‖²)²`. -/
instance : RiemannianBundle (fun x : PoincareBall E ↦ TangentSpace 𝓘(ℝ, E) x) :=
  ⟨riemannianMetric.toRiemannianMetric⟩

/-- The hyperbolic metric on the Poincaré ball is analytic. -/
instance : IsContMDiffRiemannianBundle 𝓘(ℝ, E) ω E
    (fun x : PoincareBall E ↦ TangentSpace 𝓘(ℝ, E) x) :=
  Bundle.instIsContMDiffRiemannianBundle riemannianMetric

/-- The hyperbolic metric on the Poincaré ball is continuous. -/
instance : IsContinuousRiemannianBundle E (fun x : PoincareBall E ↦ TangentSpace 𝓘(ℝ, E) x) :=
  Bundle.instIsContinuousRiemannianBundle riemannianMetric.toContinuousRiemannianMetric

/-- Evaluation of the bundled Poincaré ball metric on two tangent vectors. -/
@[simp] theorem riemannianMetric_inner (x : PoincareBall E) (v w : TangentSpace 𝓘(ℝ, E) x) :
    riemannianMetric.inner x v w =
      4 * inner ℝ (tangentSpaceCastModel 𝓘(ℝ, E) x v) (tangentSpaceCastModel 𝓘(ℝ, E) x w) /
        (1 - ‖(x : E)‖ ^ 2) ^ 2 := by
  rw [riemannianMetric, Bundle.ContMDiffRiemannianMetric.rescale_inner, euclideanMetric_inner,
    conformalFactor_def, div_mul_eq_mul_div]

/-- The installed `RiemannianBundle` instance on `PoincareBall E` is `riemannianMetric`. -/
theorem riemannianBundle_g :
    RiemannianBundle.g (E := fun x : PoincareBall E ↦ TangentSpace 𝓘(ℝ, E) x) =
      riemannianMetric.toRiemannianMetric := (rfl)

/-- The hyperbolic inner product of two tangent vectors at `x` is `4 / (1 - ‖x‖²)²` times their
Euclidean inner product. -/
@[simp] theorem inner_def (x : PoincareBall E) (v w : TangentSpace 𝓘(ℝ, E) x) :
    inner ℝ v w =
      4 * inner ℝ (tangentSpaceCastModel 𝓘(ℝ, E) x v) (tangentSpaceCastModel 𝓘(ℝ, E) x w) /
        (1 - ‖(x : E)‖ ^ 2) ^ 2 :=
  riemannianMetric_inner x v w

/-- The hyperbolic norm of a tangent vector at `x` is `2 / (1 - ‖x‖²)` times its Euclidean norm. -/
@[simp] theorem norm_def (x : PoincareBall E) (v : TangentSpace 𝓘(ℝ, E) x) :
    ‖v‖ = 2 * ‖tangentSpaceCastModel 𝓘(ℝ, E) x v‖ / (1 - ‖(x : E)‖ ^ 2) := by
  have hden : 0 ≤ 2 * ‖tangentSpaceCastModel 𝓘(ℝ, E) x v‖ / (1 - ‖(x : E)‖ ^ 2) :=
    div_nonneg (mul_nonneg zero_le_two (norm_nonneg _)) (one_sub_norm_sq_pos x).le
  have hsq : 4 * ‖tangentSpaceCastModel 𝓘(ℝ, E) x v‖ ^ 2 / (1 - ‖(x : E)‖ ^ 2) ^ 2 =
      (2 * ‖tangentSpaceCastModel 𝓘(ℝ, E) x v‖ / (1 - ‖(x : E)‖ ^ 2)) ^ 2 := by
    rw [div_pow, mul_pow]
    norm_num
  rw [norm_eq_sqrt_real_inner, inner_def, real_inner_self_eq_norm_sq, hsq, Real.sqrt_sq hden]

/-- The hyperbolic extended norm of a tangent vector at `x`. -/
@[simp] theorem eNorm_def (x : PoincareBall E) (v : TangentSpace 𝓘(ℝ, E) x) :
    ‖v‖ₑ = 2 * ‖tangentSpaceCastModel 𝓘(ℝ, E) x v‖ₑ / ENNReal.ofReal (1 - ‖(x : E)‖ ^ 2) := by
  rw [← ofReal_norm, ← ofReal_norm, norm_def, ENNReal.ofReal_div_of_pos (one_sub_norm_sq_pos x),
    ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat]

/-- Every tangent vector has hyperbolic norm at least twice its Euclidean norm. -/
theorem two_mul_norm_le_norm (x : PoincareBall E) (v : TangentSpace 𝓘(ℝ, E) x) :
    2 * ‖tangentSpaceCastModel 𝓘(ℝ, E) x v‖ ≤ ‖v‖ := by
  rw [norm_def, le_div_iff₀ (one_sub_norm_sq_pos x)]
  nlinarith [sub_le_self (1 : ℝ) (sq_nonneg ‖(x : E)‖),
    norm_nonneg (tangentSpaceCastModel 𝓘(ℝ, E) x v)]

/-! ### Orthogonal transformations -/

private def orthogonalMap (A : E ≃ₗᵢ[ℝ] E) (x : PoincareBall E) : PoincareBall E :=
  mk (A (x : E)) (by simpa using norm_lt_one x)

private theorem tangentSpaceCastModel_mfderiv_orthogonalMap (A : E ≃ₗᵢ[ℝ] E)
    (x : PoincareBall E) (v : TangentSpace 𝓘(ℝ, E) x) :
    tangentSpaceCastModel 𝓘(ℝ, E) (orthogonalMap A x)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (orthogonalMap A) x v) =
      A (tangentSpaceCastModel 𝓘(ℝ, E) x v) :=
  tangentSpaceCastModel_mfderiv_apply A.toContinuousLinearEquiv.hasFDerivAt (rfl) v

private def orthogonalDiffeomorph (A : E ≃ₗᵢ[ℝ] E) :
    Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) (PoincareBall E) (PoincareBall E) ∞ where
  toFun := orthogonalMap A
  invFun := orthogonalMap A.symm
  left_inv x := ext (A.symm_apply_apply (x : E))
  right_inv x := ext (A.apply_symm_apply (x : E))
  contMDiff_toFun :=
    contMDiff_coe_comp_iff.1 (A.contDiff.contMDiff.comp (contMDiff_coe.of_le le_top))
  contMDiff_invFun :=
    contMDiff_coe_comp_iff.1 (A.symm.contDiff.contMDiff.comp (contMDiff_coe.of_le le_top))

private theorem coe_orthogonalDiffeomorph (A : E ≃ₗᵢ[ℝ] E) :
    ⇑(orthogonalDiffeomorph A) = orthogonalMap A := (rfl)

/-- A linear isometry equivalence of `E` restricts to a Riemannian isometry of the Poincaré ball
fixing the origin. -/
def orthogonalIsometry (A : E ≃ₗᵢ[ℝ] E) : Isom 𝓘(ℝ, E) (PoincareBall E) where
  toDiffeomorph := orthogonalDiffeomorph A
  inner_mfderiv' x v w := by
    rw [coe_orthogonalDiffeomorph, inner_def, inner_def,
      tangentSpaceCastModel_mfderiv_orthogonalMap, tangentSpaceCastModel_mfderiv_orthogonalMap]
    simp [orthogonalMap]

private theorem coe_orthogonalIsometry (A : E ≃ₗᵢ[ℝ] E) :
    ⇑(orthogonalIsometry A) = orthogonalMap A := (rfl)

@[simp] theorem coe_orthogonalIsometry_apply (A : E ≃ₗᵢ[ℝ] E) (x : PoincareBall E) :
    (orthogonalIsometry A x : E) = A (x : E) := (rfl)

@[simp] theorem orthogonalIsometry_zero (A : E ≃ₗᵢ[ℝ] E) : orthogonalIsometry A 0 = 0 :=
  ext (by simp)

/-- The differential of `orthogonalIsometry A` acts as `A` on the model space `E`. -/
theorem tangentSpaceCastModel_mfderiv_orthogonalIsometry (A : E ≃ₗᵢ[ℝ] E)
    (x : PoincareBall E) (v : TangentSpace 𝓘(ℝ, E) x) :
    tangentSpaceCastModel 𝓘(ℝ, E) (orthogonalIsometry A x)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (orthogonalIsometry A) x v) =
      A (tangentSpaceCastModel 𝓘(ℝ, E) x v) := by
  rw [coe_orthogonalIsometry]
  exact tangentSpaceCastModel_mfderiv_orthogonalMap A x v

@[simp] theorem orthogonalIsometry_refl : orthogonalIsometry (.refl ℝ E) = 1 :=
  RiemannianIsometry.ext fun x ↦ ext (by simp)

@[simp] theorem orthogonalIsometry_trans (A B : E ≃ₗᵢ[ℝ] E) :
    orthogonalIsometry (A.trans B) = orthogonalIsometry B * orthogonalIsometry A :=
  RiemannianIsometry.ext fun x ↦ ext (by simp)

@[simp] theorem orthogonalIsometry_symm (A : E ≃ₗᵢ[ℝ] E) :
    orthogonalIsometry A.symm = (orthogonalIsometry A)⁻¹ :=
  (inv_eq_iff_mul_eq_one.2 ((orthogonalIsometry_trans A.symm A).symm.trans (by simp))).symm

variable (E) in
/-- The group homomorphism embedding the orthogonal group `E ≃ₗᵢ[ℝ] E` into the Riemannian isometry
group of `PoincareBall E`. -/
def orthogonalToIsom : (E ≃ₗᵢ[ℝ] E) →* Isom 𝓘(ℝ, E) (PoincareBall E) where
  toFun := orthogonalIsometry
  map_one' := orthogonalIsometry_refl
  map_mul' A B := orthogonalIsometry_trans B A

@[simp] theorem orthogonalToIsom_apply (A : E ≃ₗᵢ[ℝ] E) :
    orthogonalToIsom E A = orthogonalIsometry A := (rfl)

/-- Distinct linear isometries of `E` induce distinct Riemannian isometries of the Poincaré ball,
determined already by their action on radii of length `1 / 2`. -/
theorem orthogonalToIsom_injective : Function.Injective (orthogonalToIsom E) := by
  intro A B hAB
  ext v
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  set c : ℝ := (2 * ‖v‖)⁻¹
  have hv0 : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv
  have hnorm : ‖c • v‖ < 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_mul, abs_two, abs_norm]
    have hhalf : (2 * ‖v‖)⁻¹ * ‖v‖ = 2⁻¹ := by field_simp
    rw [hhalf]
    norm_num
  have hpt := congrArg (fun Φ : Isom 𝓘(ℝ, E) (PoincareBall E) ↦ (Φ (mk (c • v) hnorm) : E)) hAB
  simp only [orthogonalToIsom_apply, coe_orthogonalIsometry_apply, coe_mk, map_smul] at hpt
  exact smul_right_injective E (inv_ne_zero (mul_ne_zero two_ne_zero hv0)) hpt

end InnerProductSpace

end PoincareBall

end TauCeti
