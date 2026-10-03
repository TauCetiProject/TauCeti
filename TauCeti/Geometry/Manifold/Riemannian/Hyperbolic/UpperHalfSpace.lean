/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import TauCeti.Geometry.Manifold.ContMDiff.Subtype
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Action
public import TauCeti.Geometry.Manifold.Riemannian.Restriction
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Conformal

/-!
# Hyperbolic space in the upper half-space model

For a real inner product space `E`, the hyperbolic space `HyperbolicSpace E` is the open upper
half-space `{(x, t) | 0 < t}` of the Euclidean product `E × ℝ` (that is, `WithLp 2 (E × ℝ)`), with
the Riemannian metric `(‖dx‖² + dt²) / t²`: the Euclidean inner product of two tangent vectors at
`(x, t)` divided by `t²`. Taking `E = EuclideanSpace ℝ (Fin (n - 1))` gives hyperbolic `n`-space
`ℍⁿ`; in particular `E = EuclideanSpace ℝ (Fin 2)` gives the model space `ℍ³` of hyperbolic
three-manifolds.

The metric is the Euclidean metric of `E × ℝ`, restricted to the upper half-space and rescaled by
the analytic positive function `t⁻²`, so it is an analytic Riemannian metric.

For `0 < c` and `b ∈ E`, the similarity `(x, t) ↦ (c • x + b, c • t)` preserves the upper
half-space and scales tangent vectors and the height `t` by the same factor `c`, so it is a
Riemannian isometry. These similarities act transitively, so hyperbolic space is a homogeneous
Riemannian manifold.

## Main definitions

* `TauCeti.upperHalfSpace E`: the open upper half-space in `E × ℝ`.
* `TauCeti.HyperbolicSpace E`: the upper half-space as a manifold, with its hyperbolic metric as
  `RiemannianBundle` instance.
* `TauCeti.HyperbolicSpace.height`: the last coordinate `t` of a point.
* `TauCeti.HyperbolicSpace.riemannianMetric`: the analytic hyperbolic metric.
* `TauCeti.HyperbolicSpace.similarity`: the isometry `(x, t) ↦ (c • x + b, c • t)`.

## Main results

* `TauCeti.HyperbolicSpace.inner_def`: the inner product of tangent vectors at `x` is their
  Euclidean inner product divided by `height x ^ 2`.
* `TauCeti.HyperbolicSpace.isPretransitive_isom`: the isometry group of hyperbolic space acts
  transitively on it.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 3
  (the upper half-space model of hyperbolic space and its isometries).
* W. P. Thurston, *Three-Dimensional Geometry and Topology, Vol. 1*, Princeton (1997), §2.4 and
  §3.8 (the upper half-space model, and hyperbolic space among the eight model geometries).
-/

public section

open Bundle Manifold TopologicalSpace
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti

variable (E : Type*) [NormedAddCommGroup E]

/-- The open upper half-space `{(x, t) | 0 < t}` in the Euclidean product `E × ℝ`. -/
def upperHalfSpace : Opens (WithLp 2 (E × ℝ)) :=
  ⟨{p | 0 < p.snd}, isOpen_lt continuous_const (WithLp.continuous_snd 2 E ℝ)⟩

variable {E} in
@[simp]
theorem mem_upperHalfSpace {p : WithLp 2 (E × ℝ)} : p ∈ upperHalfSpace E ↔ 0 < p.snd :=
  Iff.rfl

/-- Real hyperbolic space in the upper half-space model: the open upper half-space
`{(x, t) | 0 < t}` of `E × ℝ`, with the hyperbolic metric `(‖dx‖² + dt²) / t²` as its
`RiemannianBundle` instance. For `E = EuclideanSpace ℝ (Fin (n - 1))` this is hyperbolic
`n`-space. -/
def HyperbolicSpace : Type _ := upperHalfSpace E

/- `HyperbolicSpace E` is a type synonym for the open subset `upperHalfSpace E`, so that it can
carry its own `RiemannianBundle` instance; the `show` terms below unfold the synonym to read the
subtype fields. -/

namespace HyperbolicSpace

instance : TopologicalSpace (HyperbolicSpace E) :=
  inferInstanceAs (TopologicalSpace (upperHalfSpace E))

instance : ChartedSpace (WithLp 2 (E × ℝ)) (HyperbolicSpace E) :=
  inferInstanceAs (ChartedSpace (WithLp 2 (E × ℝ)) (upperHalfSpace E))

variable {E}

/-- The point of `E × ℝ` represented by a point of hyperbolic space. -/
@[coe]
def coe (x : HyperbolicSpace E) : WithLp 2 (E × ℝ) :=
  (show upperHalfSpace E from x).1

instance : CoeOut (HyperbolicSpace E) (WithLp 2 (E × ℝ)) := ⟨coe⟩

/-- The point of hyperbolic space represented by a point of `E × ℝ` with positive last
coordinate. -/
def mk (p : WithLp 2 (E × ℝ)) (hp : 0 < p.snd) : HyperbolicSpace E :=
  (⟨p, hp⟩ : upperHalfSpace E)

@[simp]
theorem coe_mk (p : WithLp 2 (E × ℝ)) (hp : 0 < p.snd) : (mk p hp : WithLp 2 (E × ℝ)) = p :=
  (rfl)

/-- A point of hyperbolic space is determined by the point of `E × ℝ` it represents. -/
theorem coe_injective : Function.Injective (coe : HyperbolicSpace E → WithLp 2 (E × ℝ)) :=
  Subtype.val_injective

@[ext]
theorem ext {x y : HyperbolicSpace E} (h : (x : WithLp 2 (E × ℝ)) = y) : x = y :=
  coe_injective h

/-- The height of a point `(x, t)` of hyperbolic space: its last coordinate `t`. -/
def height (x : HyperbolicSpace E) : ℝ :=
  (x : WithLp 2 (E × ℝ)).snd

@[simp]
theorem snd_coe (x : HyperbolicSpace E) : (x : WithLp 2 (E × ℝ)).snd = height x :=
  (rfl)

/-- Points of hyperbolic space have positive height. -/
theorem height_pos (x : HyperbolicSpace E) : 0 < height x :=
  (show upperHalfSpace E from x).2

@[simp]
theorem mk_coe (x : HyperbolicSpace E) :
    mk (x : WithLp 2 (E × ℝ)) (by rw [snd_coe]; exact height_pos x) = x :=
  (rfl)

@[simp]
theorem height_mk (p : WithLp 2 (E × ℝ)) (hp : 0 < p.snd) : height (mk p hp) = p.snd :=
  (rfl)

variable (E) [InnerProductSpace ℝ E]

instance : IsManifold 𝓘(ℝ, WithLp 2 (E × ℝ)) ω (HyperbolicSpace E) :=
  inferInstanceAs (IsManifold 𝓘(ℝ, WithLp 2 (E × ℝ)) ω (upperHalfSpace E))

variable {E}

/-- The inclusion of hyperbolic space into `E × ℝ` is analytic. -/
theorem contMDiff_coe :
    ContMDiff 𝓘(ℝ, WithLp 2 (E × ℝ)) 𝓘(ℝ, WithLp 2 (E × ℝ)) ω
      (coe : HyperbolicSpace E → WithLp 2 (E × ℝ)) :=
  contMDiff_subtype_val (U := upperHalfSpace E)

/-- The differential of the inclusion of hyperbolic space into `E × ℝ` is the identity of the
model vector space. -/
theorem mfderiv_coe_apply (x : HyperbolicSpace E)
    (v : TangentSpace 𝓘(ℝ, WithLp 2 (E × ℝ)) x) :
    mfderiv 𝓘(ℝ, WithLp 2 (E × ℝ)) 𝓘(ℝ, WithLp 2 (E × ℝ)) coe x v =
      tangentSpaceCastModel 𝓘(ℝ, WithLp 2 (E × ℝ)) x v := by
  have h := congrArg (· v) (TauCeti.Manifold.mfderiv_subtype_val (I := 𝓘(ℝ, WithLp 2 (E × ℝ)))
    (U := upperHalfSpace E) x)
  exact h.trans (TauCeti.Manifold.tangentSpaceOpenEquiv_apply (I := 𝓘(ℝ, WithLp 2 (E × ℝ))) x v)

/-- The conformal factor `t⁻²` of the hyperbolic metric is analytic on the upper half-space. -/
theorem contMDiff_inv_height_sq :
    ContMDiff 𝓘(ℝ, WithLp 2 (E × ℝ)) 𝓘(ℝ) ω fun x : HyperbolicSpace E ↦ (height x ^ 2)⁻¹ := by
  intro x
  have h : ContDiffAt ℝ ω (fun p : WithLp 2 (E × ℝ) ↦ (p.snd ^ 2)⁻¹) x :=
    (((WithLp.sndL 2 ℝ E ℝ).contDiff.contDiffAt).pow 2).inv
      (pow_ne_zero 2 (height_pos x).ne')
  exact h.contMDiffAt.comp x (contMDiff_coe x)

/-- The Euclidean metric of `E × ℝ`, restricted to the upper half-space. -/
private def euclideanMetric :
    ContMDiffRiemannianMetric 𝓘(ℝ, WithLp 2 (E × ℝ)) ω (WithLp 2 (E × ℝ))
      (fun x : HyperbolicSpace E ↦ TangentSpace 𝓘(ℝ, WithLp 2 (E × ℝ)) x) :=
  (riemannianMetricVectorSpace (WithLp 2 (E × ℝ))).restrictOpenTangentSpace (upperHalfSpace E)

private theorem euclideanMetric_inner (x : HyperbolicSpace E)
    (v w : TangentSpace 𝓘(ℝ, WithLp 2 (E × ℝ)) x) :
    euclideanMetric.inner x v w =
      inner ℝ (tangentSpaceCastModel 𝓘(ℝ, WithLp 2 (E × ℝ)) x v)
        (tangentSpaceCastModel 𝓘(ℝ, WithLp 2 (E × ℝ)) x w) := by
  let y : upperHalfSpace E := x
  have h := Bundle.ContMDiffRiemannianMetric.restrictOpenTangentSpace_inner
    (riemannianMetricVectorSpace (WithLp 2 (E × ℝ))) (upperHalfSpace E) y v w
  have ev := TauCeti.Manifold.tangentSpaceOpenEquiv_apply (I := 𝓘(ℝ, WithLp 2 (E × ℝ))) y v
  have ew := TauCeti.Manifold.tangentSpaceOpenEquiv_apply (I := 𝓘(ℝ, WithLp 2 (E × ℝ))) y w
  rw [ev, ew] at h
  exact h

/-- The analytic hyperbolic metric `(‖dx‖² + dt²) / t²` on the upper half-space: the Euclidean
metric of `E × ℝ` multiplied by the positive function `t⁻²`. -/
def riemannianMetric :
    ContMDiffRiemannianMetric 𝓘(ℝ, WithLp 2 (E × ℝ)) ω (WithLp 2 (E × ℝ))
      (fun x : HyperbolicSpace E ↦ TangentSpace 𝓘(ℝ, WithLp 2 (E × ℝ)) x) :=
  euclideanMetric.conformal (fun x : HyperbolicSpace E ↦ (height x ^ 2)⁻¹)
    contMDiff_inv_height_sq fun x ↦ inv_pos.mpr (pow_pos (height_pos x) 2)

/-- The hyperbolic metric at `x` is the Euclidean inner product divided by `height x ^ 2`. -/
@[simp]
theorem riemannianMetric_inner (x : HyperbolicSpace E)
    (v w : TangentSpace 𝓘(ℝ, WithLp 2 (E × ℝ)) x) :
    riemannianMetric.inner x v w =
      inner ℝ (tangentSpaceCastModel 𝓘(ℝ, WithLp 2 (E × ℝ)) x v)
        (tangentSpaceCastModel 𝓘(ℝ, WithLp 2 (E × ℝ)) x w) / height x ^ 2 := by
  rw [riemannianMetric, Bundle.ContMDiffRiemannianMetric.conformal_inner, euclideanMetric_inner,
    div_eq_inv_mul]

/-- Hyperbolic space carries the hyperbolic metric `(‖dx‖² + dt²) / t²`. -/
instance : RiemannianBundle (fun x : HyperbolicSpace E ↦ TangentSpace 𝓘(ℝ, WithLp 2 (E × ℝ)) x) :=
  ⟨riemannianMetric.toRiemannianMetric⟩

/-- The hyperbolic metric is analytic. -/
instance : IsContMDiffRiemannianBundle 𝓘(ℝ, WithLp 2 (E × ℝ)) ω (WithLp 2 (E × ℝ))
    (fun x : HyperbolicSpace E ↦ TangentSpace 𝓘(ℝ, WithLp 2 (E × ℝ)) x) :=
  Bundle.instIsContMDiffRiemannianBundle riemannianMetric

/-- The hyperbolic metric is continuous, as the Riemannian volume construction requires. -/
instance : IsContinuousRiemannianBundle (WithLp 2 (E × ℝ))
    (fun x : HyperbolicSpace E ↦ TangentSpace 𝓘(ℝ, WithLp 2 (E × ℝ)) x) :=
  Bundle.instIsContinuousRiemannianBundle riemannianMetric.toContinuousRiemannianMetric

/-- The inner product of two tangent vectors at a point of hyperbolic space is their Euclidean
inner product divided by the square of the height. -/
theorem inner_def (x : HyperbolicSpace E) (v w : TangentSpace 𝓘(ℝ, WithLp 2 (E × ℝ)) x) :
    inner ℝ v w =
      inner ℝ (tangentSpaceCastModel 𝓘(ℝ, WithLp 2 (E × ℝ)) x v)
        (tangentSpaceCastModel 𝓘(ℝ, WithLp 2 (E × ℝ)) x w) / height x ^ 2 :=
  riemannianMetric_inner x v w

/-- A self-map of hyperbolic space whose composite with the inclusion into `E × ℝ` is a `C^n`
map is itself `C^n`. -/
private theorem contMDiff_of_contMDiff_coe_comp {n : ℕ∞ω}
    {f : HyperbolicSpace E → HyperbolicSpace E}
    (h : ContMDiff 𝓘(ℝ, WithLp 2 (E × ℝ)) 𝓘(ℝ, WithLp 2 (E × ℝ)) n (coe ∘ f)) :
    ContMDiff 𝓘(ℝ, WithLp 2 (E × ℝ)) 𝓘(ℝ, WithLp 2 (E × ℝ)) n f :=
  (TauCeti.ContMDiff.subtypeVal_comp_iff (upperHalfSpace E)
    (f : HyperbolicSpace E → upperHalfSpace E)).1 h

/-- If a differentiable self-map `f` of hyperbolic space is the restriction of a map `A` of
`E × ℝ` with derivative `L` at `x`, then the differential of `f` at `x` is `L`. -/
private theorem tangentSpaceCastModel_mfderiv_apply {f : HyperbolicSpace E → HyperbolicSpace E}
    {A : WithLp 2 (E × ℝ) → WithLp 2 (E × ℝ)} {L : WithLp 2 (E × ℝ) →L[ℝ] WithLp 2 (E × ℝ)}
    {x : HyperbolicSpace E}
    (hf : MDifferentiableAt 𝓘(ℝ, WithLp 2 (E × ℝ)) 𝓘(ℝ, WithLp 2 (E × ℝ)) f x)
    (hA : HasFDerivAt A L (x : WithLp 2 (E × ℝ))) (hcomp : coe ∘ f = A ∘ coe)
    (v : TangentSpace 𝓘(ℝ, WithLp 2 (E × ℝ)) x) :
    tangentSpaceCastModel 𝓘(ℝ, WithLp 2 (E × ℝ)) (f x)
        (mfderiv 𝓘(ℝ, WithLp 2 (E × ℝ)) 𝓘(ℝ, WithLp 2 (E × ℝ)) f x v) =
      L (tangentSpaceCastModel 𝓘(ℝ, WithLp 2 (E × ℝ)) x v) := by
  have hcoe : ∀ y : HyperbolicSpace E,
      MDifferentiableAt 𝓘(ℝ, WithLp 2 (E × ℝ)) 𝓘(ℝ, WithLp 2 (E × ℝ)) coe y :=
    fun y ↦ (contMDiff_coe y).mdifferentiableAt (by simp)
  have h₁ := mfderiv_comp_apply x (hcoe (f x)) hf v
  have h₂ := mfderiv_comp_apply x hA.differentiableAt.mdifferentiableAt (hcoe x) v
  rw [hcomp, h₂, mfderiv_coe_apply, mfderiv_coe_apply, hA.hasMFDerivAt.mfderiv] at h₁
  exact h₁.symm

/-- The underlying map `(x, t) ↦ (c • x + b, c • t)` of `similarity c hc b`. -/
private def similarityMap (c : ℝ) (hc : 0 < c) (b : E) (x : HyperbolicSpace E) :
    HyperbolicSpace E :=
  mk (c • (x : WithLp 2 (E × ℝ)) + WithLp.toLp 2 (b, 0)) (by
    simpa using mul_pos hc (height_pos x))

private theorem coe_similarityMap (c : ℝ) (hc : 0 < c) (b : E) (x : HyperbolicSpace E) :
    (similarityMap c hc b x : WithLp 2 (E × ℝ)) =
      c • (x : WithLp 2 (E × ℝ)) + WithLp.toLp 2 (b, 0) :=
  (rfl)

private theorem height_similarityMap (c : ℝ) (hc : 0 < c) (b : E) (x : HyperbolicSpace E) :
    height (similarityMap c hc b x) = c * height x := by
  simp [← snd_coe, coe_similarityMap]

private theorem similarityMap_inv_similarityMap (c : ℝ) (hc : 0 < c) (b : E)
    (x : HyperbolicSpace E) :
    similarityMap c⁻¹ (inv_pos.mpr hc) (-(c⁻¹ • b)) (similarityMap c hc b x) = x := by
  ext : 1
  rw [WithLp.ext_iff]
  ext <;> simp [coe_similarityMap, smul_smul, inv_mul_cancel₀ hc.ne']

private theorem similarityMap_similarityMap_inv (c : ℝ) (hc : 0 < c) (b : E)
    (x : HyperbolicSpace E) :
    similarityMap c hc b (similarityMap c⁻¹ (inv_pos.mpr hc) (-(c⁻¹ • b)) x) = x := by
  ext : 1
  rw [WithLp.ext_iff]
  ext <;> simp [coe_similarityMap, smul_smul, mul_inv_cancel₀ hc.ne']

private theorem contMDiff_similarityMap {n : ℕ∞ω} (c : ℝ) (hc : 0 < c) (b : E) :
    ContMDiff 𝓘(ℝ, WithLp 2 (E × ℝ)) 𝓘(ℝ, WithLp 2 (E × ℝ)) n (similarityMap c hc b) := by
  refine contMDiff_of_contMDiff_coe_comp ?_
  have h : ContDiff ℝ n fun p : WithLp 2 (E × ℝ) ↦ c • p + WithLp.toLp 2 (b, 0) :=
    (contDiff_id.const_smul c).add contDiff_const
  exact h.contMDiff.comp (contMDiff_coe.of_le le_top)

private theorem tangentSpaceCastModel_mfderiv_similarityMap (c : ℝ) (hc : 0 < c) (b : E)
    (x : HyperbolicSpace E) (v : TangentSpace 𝓘(ℝ, WithLp 2 (E × ℝ)) x) :
    tangentSpaceCastModel 𝓘(ℝ, WithLp 2 (E × ℝ)) (similarityMap c hc b x)
        (mfderiv 𝓘(ℝ, WithLp 2 (E × ℝ)) 𝓘(ℝ, WithLp 2 (E × ℝ)) (similarityMap c hc b) x v) =
      c • tangentSpaceCastModel 𝓘(ℝ, WithLp 2 (E × ℝ)) x v := by
  have hA : HasFDerivAt (fun p : WithLp 2 (E × ℝ) ↦ c • p + WithLp.toLp 2 (b, 0))
      (c • ContinuousLinearMap.id ℝ (WithLp 2 (E × ℝ))) (x : WithLp 2 (E × ℝ)) :=
    ((hasFDerivAt_id _).const_smul c).add_const _
  exact tangentSpaceCastModel_mfderiv_apply
    ((contMDiff_similarityMap (n := 1) c hc b x).mdifferentiableAt one_ne_zero) hA (rfl) v

/-- The similarity `(x, t) ↦ (c • x + b, c • t)`, for `0 < c`, as an isometry of hyperbolic
space: it scales tangent vectors and the height by the same factor `c`. -/
def similarity (c : ℝ) (hc : 0 < c) (b : E) : Isom 𝓘(ℝ, WithLp 2 (E × ℝ)) (HyperbolicSpace E) where
  toFun := similarityMap c hc b
  invFun := similarityMap c⁻¹ (inv_pos.mpr hc) (-(c⁻¹ • b))
  left_inv := similarityMap_inv_similarityMap c hc b
  right_inv := similarityMap_similarityMap_inv c hc b
  contMDiff_toFun := contMDiff_similarityMap c hc b
  contMDiff_invFun := contMDiff_similarityMap c⁻¹ (inv_pos.mpr hc) (-(c⁻¹ • b))
  inner_mfderiv' x v w := by
    -- The diffeomorphism under construction is `similarityMap c hc b` by definition; `change`
    -- states the goal in terms of that function, so that its differential lemma applies.
    change inner ℝ
        (mfderiv 𝓘(ℝ, WithLp 2 (E × ℝ)) 𝓘(ℝ, WithLp 2 (E × ℝ)) (similarityMap c hc b) x v)
        (mfderiv 𝓘(ℝ, WithLp 2 (E × ℝ)) 𝓘(ℝ, WithLp 2 (E × ℝ)) (similarityMap c hc b) x w) =
      inner ℝ v w
    rw [inner_def, inner_def, tangentSpaceCastModel_mfderiv_similarityMap,
      tangentSpaceCastModel_mfderiv_similarityMap, height_similarityMap, real_inner_smul_left,
      real_inner_smul_right]
    have := (height_pos x).ne'
    field_simp

/-- The similarity `similarity c hc b` sends `(x, t)` to `(c • x + b, c • t)`. -/
@[simp]
theorem coe_similarity_apply (c : ℝ) (hc : 0 < c) (b : E) (x : HyperbolicSpace E) :
    (similarity c hc b x : WithLp 2 (E × ℝ)) =
      c • (x : WithLp 2 (E × ℝ)) + WithLp.toLp 2 (b, 0) :=
  (rfl)

/-- The similarity `similarity c hc b` multiplies heights by `c`. -/
@[simp]
theorem height_similarity_apply (c : ℝ) (hc : 0 < c) (b : E) (x : HyperbolicSpace E) :
    height (similarity c hc b x) = c * height x :=
  height_similarityMap c hc b x

/-- The differential of the similarity `similarity c hc b` is multiplication by `c`. -/
theorem tangentSpaceCastModel_mfderiv_similarity (c : ℝ) (hc : 0 < c) (b : E)
    (x : HyperbolicSpace E) (v : TangentSpace 𝓘(ℝ, WithLp 2 (E × ℝ)) x) :
    tangentSpaceCastModel 𝓘(ℝ, WithLp 2 (E × ℝ)) (similarity c hc b x)
        (mfderiv 𝓘(ℝ, WithLp 2 (E × ℝ)) 𝓘(ℝ, WithLp 2 (E × ℝ)) (similarity c hc b) x v) =
      c • tangentSpaceCastModel 𝓘(ℝ, WithLp 2 (E × ℝ)) x v :=
  tangentSpaceCastModel_mfderiv_similarityMap c hc b x v

/-- Composing similarities multiplies their scale factors. -/
theorem similarity_mul (c c' : ℝ) (hc : 0 < c) (hc' : 0 < c') (b b' : E) :
    similarity c hc b * similarity c' hc' b' =
      similarity (c * c') (mul_pos hc hc') (c • b' + b) := by
  ext x : 2
  rw [WithLp.ext_iff]
  ext <;> simp [RiemannianIsometry.mul_apply, smul_smul, add_assoc, mul_assoc]

/-- The inverse of a similarity is the similarity with the inverse scale factor. -/
theorem similarity_inv (c : ℝ) (hc : 0 < c) (b : E) :
    (similarity c hc b)⁻¹ = similarity c⁻¹ (inv_pos.mpr hc) (-(c⁻¹ • b)) := by
  rw [inv_eq_iff_mul_eq_one, similarity_mul]
  ext x : 2
  rw [WithLp.ext_iff]
  ext <;> simp [mul_inv_cancel₀ hc.ne', smul_smul]

/-- The isometry group of hyperbolic space acts transitively: hyperbolic space is a homogeneous
Riemannian manifold. The similarity with factor `height y / height x`, followed by a horizontal
translation, carries `x` to `y`. -/
instance isPretransitive_isom :
    MulAction.IsPretransitive (Isom 𝓘(ℝ, WithLp 2 (E × ℝ)) (HyperbolicSpace E))
      (HyperbolicSpace E) := by
  refine ⟨fun x y ↦ ?_⟩
  have hc : 0 < height y / height x := div_pos (height_pos y) (height_pos x)
  refine ⟨similarity (height y / height x) hc
    ((y : WithLp 2 (E × ℝ)).fst - (height y / height x) • (x : WithLp 2 (E × ℝ)).fst), ?_⟩
  ext : 1
  rw [WithLp.ext_iff]
  ext <;> simp [(height_pos x).ne']

end HyperbolicSpace

end TauCeti
