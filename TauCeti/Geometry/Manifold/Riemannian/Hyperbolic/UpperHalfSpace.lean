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

For a real inner product space `E`, the upper half-space model `UpperHalfSpace E` of real
hyperbolic space is the open upper half-space `{(x, t) | 0 < t}` of the Euclidean product `E × ℝ`
(that is, `WithLp 2 (E × ℝ)`), with the Riemannian metric `(‖dx‖² + dt²) / t²`: the Euclidean
inner product of two tangent vectors at `(x, t)` divided by `t²`. For `1 ≤ n`, taking
`E = EuclideanSpace ℝ (Fin (n - 1))` gives hyperbolic `n`-space `ℍⁿ`; in particular
`E = EuclideanSpace ℝ (Fin 2)` gives the model space `ℍ³` of hyperbolic three-manifolds.

The metric is the Euclidean metric of `E × ℝ`, restricted to the upper half-space and rescaled by
the analytic positive function `t⁻²`, so it is an analytic Riemannian metric.

For `0 < c`, a linear isometry `A` of `E` and `b ∈ E`, the similarity
`(x, t) ↦ (c • A x + b, c • t)` preserves the upper half-space and scales tangent vectors and the
height `t` by the same factor `c`, so it is a Riemannian isometry. These similarities act
transitively, so the upper half-space model is a homogeneous Riemannian manifold.

Only analyticity of the metric and homogeneity are established here: the constant curvature `-1`
and the completeness of this metric are not proved, so it is not (yet) shown to be a
`TauCeti.HyperbolicMetric`.

## Main definitions

* `TauCeti.upperHalfSpaceOpens E`: the open upper half-space in `E × ℝ`.
* `TauCeti.UpperHalfSpace E`: the upper half-space as a manifold, with its hyperbolic metric as
  `RiemannianBundle` instance.
* `TauCeti.UpperHalfSpace.height`: the last coordinate `t` of a point.
* `TauCeti.UpperHalfSpace.riemannianMetric`: the analytic hyperbolic metric.
* `TauCeti.UpperHalfSpace.similarity`: the isometry `(x, t) ↦ (c • A x + b, c • t)`.

## Main results

* `TauCeti.UpperHalfSpace.inner_def`: the inner product of tangent vectors at `x` is their
  Euclidean inner product divided by `height x ^ 2` (`TauCeti.UpperHalfSpace.riemannianMetric_inner`
  is the same formula for the bundled metric `riemannianMetric`);
  `TauCeti.UpperHalfSpace.norm_def` and `TauCeti.UpperHalfSpace.enorm_def` are the corresponding
  norm forms.
* `TauCeti.UpperHalfSpace.contMDiff_coe_comp_iff`: a map into the upper half-space is `C^n` iff
  its composite with the inclusion into `E × ℝ` is.
* `TauCeti.UpperHalfSpace.isPretransitive_isom`: the isometry group of the upper half-space model
  acts transitively on it.

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
def upperHalfSpaceOpens : Opens (WithLp 2 (E × ℝ)) :=
  ⟨{p | 0 < p.snd}, isOpen_lt continuous_const (WithLp.continuous_snd 2 E ℝ)⟩

variable {E} in
@[simp]
theorem mem_upperHalfSpaceOpens {p : WithLp 2 (E × ℝ)} :
    p ∈ upperHalfSpaceOpens E ↔ 0 < p.snd :=
  Iff.rfl

/-- The upper half-space model of real hyperbolic space: the open upper half-space
`{(x, t) | 0 < t}` of `E × ℝ`, with the hyperbolic metric `(‖dx‖² + dt²) / t²` as its
`RiemannianBundle` instance. For `1 ≤ n` and `E = EuclideanSpace ℝ (Fin (n - 1))` this is
hyperbolic `n`-space. -/
def UpperHalfSpace : Type _ := upperHalfSpaceOpens E

/- `UpperHalfSpace E` is a type synonym for the open subset `upperHalfSpaceOpens E`, so that it
can carry its own `RiemannianBundle` instance; the `show` terms below unfold the synonym to read
the subtype fields. -/

namespace UpperHalfSpace

instance : TopologicalSpace (UpperHalfSpace E) :=
  inferInstanceAs (TopologicalSpace (upperHalfSpaceOpens E))

instance : ChartedSpace (WithLp 2 (E × ℝ)) (UpperHalfSpace E) :=
  inferInstanceAs (ChartedSpace (WithLp 2 (E × ℝ)) (upperHalfSpaceOpens E))

instance : T3Space (UpperHalfSpace E) :=
  inferInstanceAs (T3Space (upperHalfSpaceOpens E))

variable {E}

/-- The point of `E × ℝ` represented by a point of the upper half-space. -/
@[coe]
def coe (x : UpperHalfSpace E) : WithLp 2 (E × ℝ) :=
  (show upperHalfSpaceOpens E from x).1

instance : CoeOut (UpperHalfSpace E) (WithLp 2 (E × ℝ)) := ⟨coe⟩

/-- The point of the upper half-space represented by a point of `E × ℝ` with positive last
coordinate. -/
def mk (p : WithLp 2 (E × ℝ)) (hp : 0 < p.snd) : UpperHalfSpace E :=
  (⟨p, hp⟩ : upperHalfSpaceOpens E)

@[simp]
theorem coe_mk (p : WithLp 2 (E × ℝ)) (hp : 0 < p.snd) : (mk p hp : WithLp 2 (E × ℝ)) = p :=
  (rfl)

/-- A point of the upper half-space is determined by the point of `E × ℝ` it represents. -/
theorem coe_injective : Function.Injective (coe : UpperHalfSpace E → WithLp 2 (E × ℝ)) :=
  Subtype.val_injective

@[ext]
theorem ext {x y : UpperHalfSpace E} (h : (x : WithLp 2 (E × ℝ)) = y) : x = y :=
  coe_injective h

/-- The height of a point `(x, t)` of the upper half-space: its last coordinate `t`. -/
def height (x : UpperHalfSpace E) : ℝ :=
  (x : WithLp 2 (E × ℝ)).snd

@[simp]
theorem snd_coe (x : UpperHalfSpace E) : (x : WithLp 2 (E × ℝ)).snd = height x :=
  (rfl)

/-- Points of the upper half-space have positive height. -/
theorem height_pos (x : UpperHalfSpace E) : 0 < height x :=
  (show upperHalfSpaceOpens E from x).2

@[simp]
theorem mk_coe (x : UpperHalfSpace E) :
    mk (x : WithLp 2 (E × ℝ)) (by rw [snd_coe]; exact height_pos x) = x :=
  (rfl)

@[simp]
theorem height_mk (p : WithLp 2 (E × ℝ)) (hp : 0 < p.snd) : height (mk p hp) = p.snd :=
  (rfl)

/-- Two points of the upper half-space with the same horizontal coordinate and the same height
are equal. -/
theorem ext_fst_height {x y : UpperHalfSpace E}
    (hfst : (x : WithLp 2 (E × ℝ)).fst = (y : WithLp 2 (E × ℝ)).fst)
    (hheight : height x = height y) : x = y :=
  ext ((WithLp.ext_iff 2).2 (Prod.ext hfst hheight))

section NormedSpace

variable (E) [NormedSpace ℝ E]

instance : IsManifold 𝓘(ℝ, WithLp 2 (E × ℝ)) ω (UpperHalfSpace E) :=
  inferInstanceAs (IsManifold 𝓘(ℝ, WithLp 2 (E × ℝ)) ω (upperHalfSpaceOpens E))

variable {E}

/-- The inclusion of the upper half-space into `E × ℝ` is analytic. -/
theorem contMDiff_coe :
    ContMDiff 𝓘(ℝ, WithLp 2 (E × ℝ)) 𝓘(ℝ, WithLp 2 (E × ℝ)) ω
      (coe : UpperHalfSpace E → WithLp 2 (E × ℝ)) :=
  contMDiff_subtype_val (U := upperHalfSpaceOpens E)

/-- The conformal factor `t⁻²` of the hyperbolic metric is analytic on the upper half-space. -/
theorem contMDiff_inv_height_sq :
    ContMDiff 𝓘(ℝ, WithLp 2 (E × ℝ)) 𝓘(ℝ) ω fun x : UpperHalfSpace E ↦ (height x ^ 2)⁻¹ := by
  intro x
  have h : ContDiffAt ℝ ω (fun p : WithLp 2 (E × ℝ) ↦ (p.snd ^ 2)⁻¹) x :=
    (((WithLp.sndL 2 ℝ E ℝ).contDiff.contDiffAt).pow 2).inv
      (pow_ne_zero 2 (height_pos x).ne')
  exact h.contMDiffAt.comp x (contMDiff_coe x)

/-- A map into the upper half-space is `C^n` iff its composite with the inclusion into `E × ℝ`
is. -/
@[simp]
theorem contMDiff_coe_comp_iff
    {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
    {HM : Type*} [TopologicalSpace HM] {I : ModelWithCorners ℝ EM HM}
    {M : Type*} [TopologicalSpace M] [ChartedSpace HM M] {n : ℕ∞ω} {f : M → UpperHalfSpace E} :
    ContMDiff I 𝓘(ℝ, WithLp 2 (E × ℝ)) n (coe ∘ f) ↔
      ContMDiff I 𝓘(ℝ, WithLp 2 (E × ℝ)) n f :=
  TauCeti.ContMDiff.subtypeVal_comp_iff (upperHalfSpaceOpens E)
    (f : M → upperHalfSpaceOpens E)

/-- If a differentiable self-map `f` of the upper half-space is the restriction of a map `A` of
`E × ℝ` with derivative `L` at `x`, then the differential of `f` at `x` is `L`. -/
theorem tangentSpaceCastModel_mfderiv_apply {f : UpperHalfSpace E → UpperHalfSpace E}
    {A : WithLp 2 (E × ℝ) → WithLp 2 (E × ℝ)} {L : WithLp 2 (E × ℝ) →L[ℝ] WithLp 2 (E × ℝ)}
    {x : UpperHalfSpace E}
    (hf : MDifferentiableAt 𝓘(ℝ, WithLp 2 (E × ℝ)) 𝓘(ℝ, WithLp 2 (E × ℝ)) f x)
    (hA : HasFDerivAt A L (x : WithLp 2 (E × ℝ))) (hcomp : coe ∘ f = A ∘ coe)
    (v : TangentSpace 𝓘(ℝ, WithLp 2 (E × ℝ)) x) :
    tangentSpaceCastModel 𝓘(ℝ, WithLp 2 (E × ℝ)) (f x)
        (mfderiv 𝓘(ℝ, WithLp 2 (E × ℝ)) 𝓘(ℝ, WithLp 2 (E × ℝ)) f x v) =
      L (tangentSpaceCastModel 𝓘(ℝ, WithLp 2 (E × ℝ)) x v) := by
  -- Read the base point of `hA` as a point of the open subset, as in the general lemma.
  have hA' : HasFDerivAt A L (show upperHalfSpaceOpens E from x).1 := hA
  have h := TauCeti.Manifold.tangentSpaceOpenEquiv_mfderiv_apply
    (U := upperHalfSpaceOpens E) (V := upperHalfSpaceOpens E) (f := f) hf
    hA'.differentiableAt.mdifferentiableAt hcomp v
  rw [hA'.hasMFDerivAt.mfderiv] at h
  -- Both the open-subset identification and `tangentSpaceCastModel` are the identity of the model.
  have e₁ := TauCeti.Manifold.tangentSpaceOpenEquiv_apply (I := 𝓘(ℝ, WithLp 2 (E × ℝ)))
    (show upperHalfSpaceOpens E from f x)
    (mfderiv 𝓘(ℝ, WithLp 2 (E × ℝ)) 𝓘(ℝ, WithLp 2 (E × ℝ)) f x v)
  have e₂ := TauCeti.Manifold.tangentSpaceOpenEquiv_apply (I := 𝓘(ℝ, WithLp 2 (E × ℝ)))
    (show upperHalfSpaceOpens E from x) v
  exact e₁.symm.trans (h.trans (congrArg L e₂))

/-- The underlying map `(x, t) ↦ (c • A x + b, c • t)` of `similarity c hc A b`. -/
private def similarityMap (c : ℝ) (hc : 0 < c) (A : E ≃ₗᵢ[ℝ] E) (b : E) (x : UpperHalfSpace E) :
    UpperHalfSpace E :=
  mk (c • LinearIsometryEquiv.withLpProdCongr 2 A (.refl ℝ ℝ) (x : WithLp 2 (E × ℝ)) +
    WithLp.toLp 2 (b, 0)) (by simpa using mul_pos hc (height_pos x))

private theorem coe_similarityMap (c : ℝ) (hc : 0 < c) (A : E ≃ₗᵢ[ℝ] E) (b : E)
    (x : UpperHalfSpace E) :
    (similarityMap c hc A b x : WithLp 2 (E × ℝ)) =
      c • LinearIsometryEquiv.withLpProdCongr 2 A (.refl ℝ ℝ) (x : WithLp 2 (E × ℝ)) +
        WithLp.toLp 2 (b, 0) :=
  (rfl)

private theorem height_similarityMap (c : ℝ) (hc : 0 < c) (A : E ≃ₗᵢ[ℝ] E) (b : E)
    (x : UpperHalfSpace E) : height (similarityMap c hc A b x) = c * height x := by
  simp [← snd_coe, coe_similarityMap]

/-- The composition law of similarities. -/
private theorem similarityMap_similarityMap (c c' : ℝ) (hc : 0 < c) (hc' : 0 < c')
    (A A' : E ≃ₗᵢ[ℝ] E) (b b' : E) (x : UpperHalfSpace E) :
    similarityMap c hc A b (similarityMap c' hc' A' b' x) =
      similarityMap (c * c') (mul_pos hc hc') (A'.trans A) (c • A b' + b) x :=
  ext_fst_height (by simp [coe_similarityMap, smul_smul, add_assoc])
    (by simp [height_similarityMap, mul_assoc])

/-- The similarity with factor `1`, linear part the identity and translation `0` is the identity.
The factor, linear part and translation are hypotheses rather than literals because `hc` depends
on the factor. -/
private theorem similarityMap_eq_self {c : ℝ} (hc : 0 < c) {A : E ≃ₗᵢ[ℝ] E} {b : E} (hc₁ : c = 1)
    (hA : A = .refl ℝ E) (hb : b = 0) (x : UpperHalfSpace E) : similarityMap c hc A b x = x := by
  subst hc₁ hA hb
  exact ext_fst_height (by simp [coe_similarityMap]) (by simp [height_similarityMap])

private theorem similarityMap_inv_similarityMap (c : ℝ) (hc : 0 < c) (A : E ≃ₗᵢ[ℝ] E) (b : E)
    (x : UpperHalfSpace E) :
    similarityMap c⁻¹ (inv_pos.mpr hc) A.symm (-(c⁻¹ • A.symm b)) (similarityMap c hc A b x) =
      x := by
  rw [similarityMap_similarityMap]
  exact similarityMap_eq_self _ (inv_mul_cancel₀ hc.ne') A.self_trans_symm
    (add_neg_cancel _) x

private theorem similarityMap_similarityMap_inv (c : ℝ) (hc : 0 < c) (A : E ≃ₗᵢ[ℝ] E) (b : E)
    (x : UpperHalfSpace E) :
    similarityMap c hc A b (similarityMap c⁻¹ (inv_pos.mpr hc) A.symm (-(c⁻¹ • A.symm b)) x) =
      x := by
  rw [similarityMap_similarityMap]
  exact similarityMap_eq_self _ (mul_inv_cancel₀ hc.ne') A.symm_trans_self
    (by rw [map_neg, map_smul, LinearIsometryEquiv.apply_symm_apply, smul_neg, smul_smul,
      mul_inv_cancel₀ hc.ne', one_smul, neg_add_cancel]) x

private theorem contMDiff_similarityMap {n : ℕ∞ω} (c : ℝ) (hc : 0 < c) (A : E ≃ₗᵢ[ℝ] E)
    (b : E) :
    ContMDiff 𝓘(ℝ, WithLp 2 (E × ℝ)) 𝓘(ℝ, WithLp 2 (E × ℝ)) n (similarityMap c hc A b) := by
  refine contMDiff_coe_comp_iff.1 ?_
  have h : ContDiff ℝ n fun p : WithLp 2 (E × ℝ) ↦
      c • LinearIsometryEquiv.withLpProdCongr 2 A (.refl ℝ ℝ) p + WithLp.toLp 2 (b, 0) :=
    ((LinearIsometryEquiv.withLpProdCongr 2 A (.refl ℝ ℝ)).contDiff.const_smul c).add
      contDiff_const
  exact h.contMDiff.comp (contMDiff_coe.of_le le_top)

private theorem tangentSpaceCastModel_mfderiv_similarityMap (c : ℝ) (hc : 0 < c)
    (A : E ≃ₗᵢ[ℝ] E) (b : E) (x : UpperHalfSpace E)
    (v : TangentSpace 𝓘(ℝ, WithLp 2 (E × ℝ)) x) :
    tangentSpaceCastModel 𝓘(ℝ, WithLp 2 (E × ℝ)) (similarityMap c hc A b x)
        (mfderiv 𝓘(ℝ, WithLp 2 (E × ℝ)) 𝓘(ℝ, WithLp 2 (E × ℝ)) (similarityMap c hc A b) x v) =
      c • LinearIsometryEquiv.withLpProdCongr 2 A (.refl ℝ ℝ)
        (tangentSpaceCastModel 𝓘(ℝ, WithLp 2 (E × ℝ)) x v) := by
  have hA : HasFDerivAt (fun p : WithLp 2 (E × ℝ) ↦
      c • LinearIsometryEquiv.withLpProdCongr 2 A (.refl ℝ ℝ) p + WithLp.toLp 2 (b, 0))
      (c • ((LinearIsometryEquiv.withLpProdCongr 2 A (.refl ℝ ℝ)).toContinuousLinearEquiv :
        WithLp 2 (E × ℝ) →L[ℝ] WithLp 2 (E × ℝ))) (x : WithLp 2 (E × ℝ)) :=
    ((LinearIsometryEquiv.withLpProdCongr 2 A
      (.refl ℝ ℝ)).toContinuousLinearEquiv.hasFDerivAt.const_smul c).add_const _
  exact tangentSpaceCastModel_mfderiv_apply
    ((contMDiff_similarityMap (n := 1) c hc A b x).mdifferentiableAt one_ne_zero) hA (rfl) v

end NormedSpace

variable [InnerProductSpace ℝ E]

/-- The Euclidean metric of `E × ℝ`, restricted to the upper half-space. -/
private def euclideanMetric :
    ContMDiffRiemannianMetric 𝓘(ℝ, WithLp 2 (E × ℝ)) ω (WithLp 2 (E × ℝ))
      (fun x : UpperHalfSpace E ↦ TangentSpace 𝓘(ℝ, WithLp 2 (E × ℝ)) x) :=
  (riemannianMetricVectorSpace (WithLp 2 (E × ℝ))).restrictOpenTangentSpace
    (upperHalfSpaceOpens E)

private theorem euclideanMetric_inner (x : UpperHalfSpace E)
    (v w : TangentSpace 𝓘(ℝ, WithLp 2 (E × ℝ)) x) :
    euclideanMetric.inner x v w =
      inner ℝ (tangentSpaceCastModel 𝓘(ℝ, WithLp 2 (E × ℝ)) x v)
        (tangentSpaceCastModel 𝓘(ℝ, WithLp 2 (E × ℝ)) x w) := by
  let y : upperHalfSpaceOpens E := x
  have h := Bundle.ContMDiffRiemannianMetric.restrictOpenTangentSpace_inner
    (riemannianMetricVectorSpace (WithLp 2 (E × ℝ))) (upperHalfSpaceOpens E) y v w
  have ev := TauCeti.Manifold.tangentSpaceOpenEquiv_apply (I := 𝓘(ℝ, WithLp 2 (E × ℝ))) y v
  have ew := TauCeti.Manifold.tangentSpaceOpenEquiv_apply (I := 𝓘(ℝ, WithLp 2 (E × ℝ))) y w
  rw [ev, ew] at h
  exact h

/-- The analytic hyperbolic metric `(‖dx‖² + dt²) / t²` on the upper half-space: the Euclidean
metric of `E × ℝ` multiplied by the positive function `t⁻²`. -/
def riemannianMetric :
    ContMDiffRiemannianMetric 𝓘(ℝ, WithLp 2 (E × ℝ)) ω (WithLp 2 (E × ℝ))
      (fun x : UpperHalfSpace E ↦ TangentSpace 𝓘(ℝ, WithLp 2 (E × ℝ)) x) :=
  euclideanMetric.rescale (fun x : UpperHalfSpace E ↦ (height x ^ 2)⁻¹)
    contMDiff_inv_height_sq fun x ↦ inv_pos.mpr (pow_pos (height_pos x) 2)

/-- The upper half-space carries the hyperbolic metric `(‖dx‖² + dt²) / t²`. -/
instance : RiemannianBundle (fun x : UpperHalfSpace E ↦ TangentSpace 𝓘(ℝ, WithLp 2 (E × ℝ)) x) :=
  ⟨riemannianMetric.toRiemannianMetric⟩

/-- The hyperbolic metric is analytic. -/
instance : IsContMDiffRiemannianBundle 𝓘(ℝ, WithLp 2 (E × ℝ)) ω (WithLp 2 (E × ℝ))
    (fun x : UpperHalfSpace E ↦ TangentSpace 𝓘(ℝ, WithLp 2 (E × ℝ)) x) :=
  Bundle.instIsContMDiffRiemannianBundle riemannianMetric

/-- The hyperbolic metric is continuous, as the Riemannian volume construction requires. -/
instance : IsContinuousRiemannianBundle (WithLp 2 (E × ℝ))
    (fun x : UpperHalfSpace E ↦ TangentSpace 𝓘(ℝ, WithLp 2 (E × ℝ)) x) :=
  Bundle.instIsContinuousRiemannianBundle riemannianMetric.toContinuousRiemannianMetric

/-- The hyperbolic metric evaluated on two tangent vectors at a point of the upper half-space is
their Euclidean inner product divided by the square of the height. This is the characteristic
lemma of the bundled metric `riemannianMetric`; `inner_def` is its form for the installed
`RiemannianBundle` instance. -/
@[simp]
theorem riemannianMetric_inner (x : UpperHalfSpace E)
    (v w : TangentSpace 𝓘(ℝ, WithLp 2 (E × ℝ)) x) :
    riemannianMetric.inner x v w =
      inner ℝ (tangentSpaceCastModel 𝓘(ℝ, WithLp 2 (E × ℝ)) x v)
        (tangentSpaceCastModel 𝓘(ℝ, WithLp 2 (E × ℝ)) x w) / height x ^ 2 := by
  rw [riemannianMetric, Bundle.ContMDiffRiemannianMetric.rescale_inner, euclideanMetric_inner,
    div_eq_inv_mul]

/-- The metric installed as the `RiemannianBundle` instance of the upper half-space is the
hyperbolic metric `riemannianMetric`. -/
theorem riemannianBundle_g :
    RiemannianBundle.g (E := fun x : UpperHalfSpace E ↦ TangentSpace 𝓘(ℝ, WithLp 2 (E × ℝ)) x) =
      riemannianMetric.toRiemannianMetric :=
  rfl

/-- The inner product of two tangent vectors at a point of the upper half-space is their
Euclidean inner product divided by the square of the height. -/
@[simp]
theorem inner_def (x : UpperHalfSpace E) (v w : TangentSpace 𝓘(ℝ, WithLp 2 (E × ℝ)) x) :
    inner ℝ v w =
      inner ℝ (tangentSpaceCastModel 𝓘(ℝ, WithLp 2 (E × ℝ)) x v)
        (tangentSpaceCastModel 𝓘(ℝ, WithLp 2 (E × ℝ)) x w) / height x ^ 2 :=
  -- The `RiemannianBundle` instance is `riemannianMetric` (`riemannianBundle_g`), so the inner
  -- product of the instance is `riemannianMetric.inner` by definition.
  riemannianMetric_inner x v w

/-- The norm of a tangent vector at a point of the upper half-space is its Euclidean norm divided
by the height. -/
@[simp]
theorem norm_def (x : UpperHalfSpace E) (v : TangentSpace 𝓘(ℝ, WithLp 2 (E × ℝ)) x) :
    ‖v‖ = ‖tangentSpaceCastModel 𝓘(ℝ, WithLp 2 (E × ℝ)) x v‖ / height x := by
  rw [norm_eq_sqrt_real_inner, inner_def, real_inner_self_eq_norm_sq, ← div_pow,
    Real.sqrt_sq (div_nonneg (norm_nonneg _) (height_pos x).le)]

/-- The extended norm of a tangent vector at a point of the upper half-space is its Euclidean
extended norm divided by the height. -/
@[simp]
theorem enorm_def (x : UpperHalfSpace E) (v : TangentSpace 𝓘(ℝ, WithLp 2 (E × ℝ)) x) :
    ‖v‖ₑ = ‖tangentSpaceCastModel 𝓘(ℝ, WithLp 2 (E × ℝ)) x v‖ₑ / ENNReal.ofReal (height x) := by
  rw [← ofReal_norm, ← ofReal_norm, norm_def,
    ENNReal.ofReal_div_of_pos (height_pos x)]

/-- The similarity `(x, t) ↦ (c • A x + b, c • t)`, for `0 < c` and a linear isometry `A` of
`E`, as an isometry of the upper half-space model: it scales tangent vectors and the height by the
same factor `c`. -/
def similarity (c : ℝ) (hc : 0 < c) (A : E ≃ₗᵢ[ℝ] E) (b : E) :
    Isom 𝓘(ℝ, WithLp 2 (E × ℝ)) (UpperHalfSpace E) where
  toFun := similarityMap c hc A b
  invFun := similarityMap c⁻¹ (inv_pos.mpr hc) A.symm (-(c⁻¹ • A.symm b))
  left_inv := similarityMap_inv_similarityMap c hc A b
  right_inv := similarityMap_similarityMap_inv c hc A b
  contMDiff_toFun := contMDiff_similarityMap c hc A b
  contMDiff_invFun := contMDiff_similarityMap c⁻¹ (inv_pos.mpr hc) A.symm (-(c⁻¹ • A.symm b))
  inner_mfderiv' x v w := by
    -- The diffeomorphism under construction is `similarityMap c hc A b` by definition; `change`
    -- states the goal in terms of that function, so that its differential lemma applies.
    change inner ℝ
        (mfderiv 𝓘(ℝ, WithLp 2 (E × ℝ)) 𝓘(ℝ, WithLp 2 (E × ℝ)) (similarityMap c hc A b) x v)
        (mfderiv 𝓘(ℝ, WithLp 2 (E × ℝ)) 𝓘(ℝ, WithLp 2 (E × ℝ)) (similarityMap c hc A b) x w) =
      inner ℝ v w
    rw [inner_def, inner_def, tangentSpaceCastModel_mfderiv_similarityMap,
      tangentSpaceCastModel_mfderiv_similarityMap, height_similarityMap, real_inner_smul_left,
      real_inner_smul_right, LinearIsometryEquiv.inner_map_map]
    have := (height_pos x).ne'
    field_simp

/-- The coercion of `similarity c hc A b` to a function is `similarityMap c hc A b`: the coercion
of an isometry is the `toFun` field of its underlying equivalence. -/
private theorem coe_similarity (c : ℝ) (hc : 0 < c) (A : E ≃ₗᵢ[ℝ] E) (b : E) :
    ⇑(similarity c hc A b) = similarityMap c hc A b :=
  (rfl)

/-- The similarity `similarity c hc A b` sends `(x, t)` to `(c • A x + b, c • t)`. -/
@[simp]
theorem coe_similarity_apply (c : ℝ) (hc : 0 < c) (A : E ≃ₗᵢ[ℝ] E) (b : E)
    (x : UpperHalfSpace E) :
    (similarity c hc A b x : WithLp 2 (E × ℝ)) =
      WithLp.toLp 2 (c • A (x : WithLp 2 (E × ℝ)).fst + b, c * height x) := by
  rw [coe_similarity, coe_similarityMap]
  exact (WithLp.ext_iff 2).2 (Prod.ext (by simp) (by simp))

/-- The similarity `similarity c hc A b` multiplies heights by `c`. -/
@[simp]
theorem height_similarity_apply (c : ℝ) (hc : 0 < c) (A : E ≃ₗᵢ[ℝ] E) (b : E)
    (x : UpperHalfSpace E) : height (similarity c hc A b x) = c * height x := by
  rw [coe_similarity, height_similarityMap]

/-- The differential of the similarity `similarity c hc A b` is `c` times the linear isometry
`(x, t) ↦ (A x, t)`. -/
theorem tangentSpaceCastModel_mfderiv_similarity (c : ℝ) (hc : 0 < c) (A : E ≃ₗᵢ[ℝ] E) (b : E)
    (x : UpperHalfSpace E) (v : TangentSpace 𝓘(ℝ, WithLp 2 (E × ℝ)) x) :
    tangentSpaceCastModel 𝓘(ℝ, WithLp 2 (E × ℝ)) (similarity c hc A b x)
        (mfderiv 𝓘(ℝ, WithLp 2 (E × ℝ)) 𝓘(ℝ, WithLp 2 (E × ℝ)) (similarity c hc A b) x v) =
      c • LinearIsometryEquiv.withLpProdCongr 2 A (.refl ℝ ℝ)
        (tangentSpaceCastModel 𝓘(ℝ, WithLp 2 (E × ℝ)) x v) := by
  rw [coe_similarity]
  exact tangentSpaceCastModel_mfderiv_similarityMap c hc A b x v

/-- The similarity with factor `1`, linear part the identity and translation `0` is the identity
isometry. -/
@[simp]
theorem similarity_one : similarity 1 one_pos (.refl ℝ E) 0 = 1 := by
  ext x
  rw [coe_similarity, similarityMap_eq_self one_pos rfl rfl rfl, RiemannianIsometry.one_apply]

/-- Composing similarities multiplies their scale factors and composes their linear parts. -/
@[simp]
theorem similarity_mul_similarity (c c' : ℝ) (hc : 0 < c) (hc' : 0 < c') (A A' : E ≃ₗᵢ[ℝ] E)
    (b b' : E) :
    similarity c hc A b * similarity c' hc' A' b' =
      similarity (c * c') (mul_pos hc hc') (A'.trans A) (c • A b' + b) := by
  ext x
  rw [RiemannianIsometry.mul_apply, coe_similarity, coe_similarity, coe_similarity,
    similarityMap_similarityMap]

/-- The inverse of a similarity is the similarity with the inverse scale factor and the inverse
linear part. -/
@[simp]
theorem similarity_inv (c : ℝ) (hc : 0 < c) (A : E ≃ₗᵢ[ℝ] E) (b : E) :
    (similarity c hc A b)⁻¹ = similarity c⁻¹ (inv_pos.mpr hc) A.symm (-(c⁻¹ • A.symm b)) :=
  inv_eq_iff_mul_eq_one.2 (by
    ext x
    rw [RiemannianIsometry.mul_apply, coe_similarity, coe_similarity,
      similarityMap_similarityMap_inv, RiemannianIsometry.one_apply])

/-- The isometry group of the upper half-space model acts transitively: it is a homogeneous
Riemannian manifold. -/
instance isPretransitive_isom :
    MulAction.IsPretransitive (Isom 𝓘(ℝ, WithLp 2 (E × ℝ)) (UpperHalfSpace E))
      (UpperHalfSpace E) := by
  refine ⟨fun x y ↦ ?_⟩
  -- Scale by `height y / height x`, then translate horizontally to land on `y`.
  have hc : 0 < height y / height x := div_pos (height_pos y) (height_pos x)
  refine ⟨similarity (height y / height x) hc (.refl ℝ E)
    ((y : WithLp 2 (E × ℝ)).fst - (height y / height x) • (x : WithLp 2 (E × ℝ)).fst), ?_⟩
  rw [RiemannianIsometry.smul_def]
  exact ext_fst_height (by simp) (by simp [(height_pos x).ne'])

end UpperHalfSpace

end TauCeti
