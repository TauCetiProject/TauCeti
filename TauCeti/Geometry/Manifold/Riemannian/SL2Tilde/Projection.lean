/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.SL2Tilde.Curvature
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Curvature
public import TauCeti.Geometry.Manifold.Riemannian.Hyperbolic.UpperHalfSpace.Basic
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
-- Identify the open-subset tangent map with the cast used by the metric API.
import all TauCeti.Geometry.Manifold.VectorBundle.Tangent
-- The coordinate derivative uses the inherited model-space atlas of SL2Tilde.
import all TauCeti.Geometry.Manifold.Riemannian.SL2Tilde.Basic
-- Identify the inclusion with the open-subset inclusion in its differential.
import all TauCeti.Geometry.Manifold.Riemannian.Hyperbolic.UpperHalfSpace.Basic

/-!
# The hyperbolic projection of `SL₂ℝ~`

The Sasaki model projects to the hyperbolic plane by `(x, y, z) ↦ (x, exp y)`.
Its differential is surjective and its horizontal metric is the pullback of the
existing upper-half-space metric. The Sasaki metric and Ricci tensor together
determine this pullback metric, so every Riemannian isometry preserves it.
Consequently, a diffeomorphism induced on the base by an isometry is itself a
hyperbolic isometry. The analytic zero-fibre-coordinate section supplies a smooth
right inverse for constructing such base maps.

## References

* P. Scott, *The geometries of 3-manifolds*, Bull. London Math. Soc. 15 (1983),
  401–487, Section 4, pp. 464–465 (the base action of the isometries of `SL₂ℝ~`).
* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 3
  (Riemannian submersions and the upper-half-space metric).
-/

public section

noncomputable section

open Bundle Manifold Real
open scoped Manifold ContDiff

namespace TauCeti.SL2Tilde

local notation "P" => ℝ × ℝ × ℝ
local notation "Q" => WithLp 2 (ℝ × ℝ)
local notation "J" => 𝓘(ℝ, P)
local notation "K" => 𝓘(ℝ, Q)

/-- The projection of the universal cover of the unit tangent bundle to the hyperbolic plane.
The second coordinate of `SL2Tilde` is the logarithm of the upper-half-plane height. -/
def projection (p : SL2Tilde) : UpperHalfSpace ℝ :=
  UpperHalfSpace.mk (WithLp.toLp 2 (p.x, exp p.y)) (exp_pos p.y)

/-- The hyperbolic projection in upper-half-plane coordinates. -/
@[simp] theorem coe_projection (p : SL2Tilde) :
    (projection p : Q) = WithLp.toLp 2 (p.x, exp p.y) := by
  exact UpperHalfSpace.coe_mk _ _

/-- Hyperbolic height is the exponential of the logarithmic height coordinate. -/
@[simp] theorem height_projection (p : SL2Tilde) :
    UpperHalfSpace.height (projection p) = exp p.y := by
  exact UpperHalfSpace.height_mk _ _

/-- The zero-fibre-coordinate section of the hyperbolic projection. -/
def projectionSection (q : UpperHalfSpace ℝ) : SL2Tilde :=
  mk (q : Q).fst (log (UpperHalfSpace.height q)) 0

/-- The section in global horocyclic coordinates. -/
@[simp] theorem toProd_projectionSection (q : UpperHalfSpace ℝ) :
    toProd (projectionSection q) = ((q : Q).fst, log (UpperHalfSpace.height q), 0) := by
  simp [projectionSection]

/-- The zero-coordinate section is a right inverse of the hyperbolic projection. -/
@[simp] theorem projection_projectionSection (q : UpperHalfSpace ℝ) :
    projection (projectionSection q) = q := by
  apply UpperHalfSpace.ext_fst_height <;>
    simp [projectionSection, exp_log (UpperHalfSpace.height_pos q)]

/-- The hyperbolic projection is onto; the fibre coordinate may be chosen to be zero. -/
theorem projection_surjective : Function.Surjective projection :=
  fun q => ⟨projectionSection q, projection_projectionSection q⟩

private theorem contDiff_projection_coordinates :
    ContDiff ℝ ω (fun p : P => WithLp.toLp 2 (p.1, exp p.2.1)) :=
  WithLp.contDiff_toLp.comp (contDiff_fst.prodMk contDiff_snd.fst.exp)

/-- The projection to the hyperbolic plane is analytic. -/
theorem contMDiff_projection : ContMDiff J K ω projection := by
  apply UpperHalfSpace.contMDiff_coe_comp_iff.mp
  -- The global coordinates carry exactly the inherited model-space atlas.
  have ht : ContMDiff J J ω toProd := contDiff_id.contMDiff
  have h := contDiff_projection_coordinates.contMDiff.comp ht
  simpa only [Function.comp_def, coe_projection, x, y] using h

/-- The zero-coordinate section of the projection is analytic. -/
theorem contMDiff_projectionSection : ContMDiff K J ω projectionSection := by
  have hc : ContMDiff K 𝓘(ℝ, ℝ × ℝ) ω
      (fun q : UpperHalfSpace ℝ => WithLp.ofLp (q : Q)) :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ).contDiff.contMDiff.comp
      UpperHalfSpace.contMDiff_coe
  have hx : ContMDiff K 𝓘(ℝ, ℝ) ω (fun q : UpperHalfSpace ℝ => (q : Q).fst) :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).contMDiff.comp hc
  have hy : ContMDiff K 𝓘(ℝ, ℝ) ω
      (fun q : UpperHalfSpace ℝ => UpperHalfSpace.height q) := by
    simpa only [ContinuousLinearMap.coe_snd', Function.comp_def, ← UpperHalfSpace.snd_coe,
      WithLp.snd]
      using (ContinuousLinearMap.snd ℝ ℝ ℝ).contMDiff.comp hc
  have hl : ContMDiff K 𝓘(ℝ, ℝ) ω (fun q : UpperHalfSpace ℝ =>
      log (UpperHalfSpace.height q)) := by
    intro q
    exact (contDiffAt_log.mpr (UpperHalfSpace.height_pos q).ne').contMDiffAt.comp q (hy q)
  -- Inverse global coordinates carry SL2Tilde's inherited analytic model-space atlas.
  have h : ContMDiff J J ω toProd.symm := contDiff_id.contMDiff
  exact h.comp (hx.prodMk_space (hl.prodMk_space contMDiff_const))

private def projectionDerivative (p : SL2Tilde) : P →L[ℝ] Q :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).prod
      (exp p.y • (ContinuousLinearMap.fst ℝ ℝ ℝ).comp
        (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))))

private theorem projectionDerivative_apply (p : SL2Tilde) (u : P) :
    projectionDerivative p u = WithLp.toLp 2 (u.1, exp p.y * u.2.1) := by
  simp [projectionDerivative]

/-- In coordinates the differential of the projection is `(dx, exp y * dy)`. -/
@[simp] theorem tangentSpaceCastModel_mfderiv_projection (p : SL2Tilde)
    (u : TangentSpace J p) :
    tangentSpaceCastModel K (projection p) (mfderiv J K projection p u) =
      WithLp.toLp 2 ((tangentSpaceCastModel J p u).1,
        exp p.y * (tangentSpaceCastModel J p u).2.1) := by
  have hd : HasFDerivAt (fun r : P => WithLp.toLp 2 (r.1, exp r.2.1))
      (projectionDerivative p) (toProd p) :=
    ((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ).symm.hasFDerivAt).comp (toProd p)
      (hasFDerivAt_fst.prodMk
        (((hasFDerivAt_fst (p := (toProd p).2)).comp (toProd p) hasFDerivAt_snd).exp))
  have h := mfderiv_comp_apply p (UpperHalfSpace.contMDiff_coe.mdifferentiableAt (by simp))
    (contMDiff_projection.mdifferentiableAt (by simp)) u
  have hc : UpperHalfSpace.coe ∘ projection =
      (fun r : P => WithLp.toLp 2 (r.1, exp r.2.1)) ∘ toProd := by
    funext r
    exact coe_projection r
  have hi : ∀ w : TangentSpace K (projection p),
      NormedSpace.fromTangentSpace (projection p : Q)
        (mfderiv K K UpperHalfSpace.coe (projection p) w) =
      tangentSpaceCastModel K (projection p) w := by
    intro w
    have hinc := TauCeti.Manifold.mfderiv_subtype_val (I := K)
      (show upperHalfSpaceOpens ℝ from projection p)
    -- The inclusion uses the open-subset atlas and its canonical tangent identification.
    convert congrArg (fun L => L w) hinc using 1 <;> rfl
  have hn (w : TangentSpace J (toProd p)) :
      NormedSpace.fromTangentSpace (WithLp.toLp 2 ((toProd p).1, exp (toProd p).2.1))
        (mfderiv J K (fun r : P => WithLp.toLp 2 (r.1, exp r.2.1)) (toProd p) w) =
      projectionDerivative p (NormedSpace.fromTangentSpace (toProd p) w) := by
    -- For maps of model spaces, HasMFDerivAt is HasFDerivAt with these canonical casts.
    convert congrArg (fun L => L w) hd.hasMFDerivAt.mfderiv using 1 <;> rfl
  have hread := congrArg (NormedSpace.fromTangentSpace (projection p : Q)) h
  rw [hi] at hread
  rw [hc, mfderiv_comp_apply p hd.differentiableAt.mdifferentiableAt
    (by simpa only [coe_toProdDiffeomorph] using
      toProdDiffeomorph.mdifferentiable (by simp) p)] at hread
  -- Inherited global coordinates identify this model-space cast with the coordinate vector.
  have hv : NormedSpace.fromTangentSpace (toProd p) (mfderiv J J toProd p u) =
      tangentSpaceCastModel J p u := by
    rw [mfderiv_toProd_apply]
    rfl
  -- Read the codomain of the coordinate map at the explicit coordinate point.
  have hread' :
      NormedSpace.fromTangentSpace (WithLp.toLp 2 ((toProd p).1, exp (toProd p).2.1))
        (mfderiv J K (fun r : P => WithLp.toLp 2 (r.1, exp r.2.1)) (toProd p)
          (mfderiv J J toProd p u)) =
      tangentSpaceCastModel K (projection p) (mfderiv J K projection p u) := by
    convert hread using 1; rfl
  simpa only [hn, hv, projectionDerivative_apply] using hread'.symm

/-- Equality of projected points is equality of the two hyperbolic-base coordinates. -/
@[simp] theorem projection_eq_projection_iff (p q : SL2Tilde) :
    projection p = projection q ↔ p.x = q.x ∧ p.y = q.y := by
  constructor
  · intro h
    have hx := congrArg (fun r : UpperHalfSpace ℝ => (r : Q).fst) h
    have hy := congrArg UpperHalfSpace.height h
    exact ⟨by simpa using hx, exp_injective (by simpa using hy)⟩
  · rintro ⟨hx, hy⟩
    apply UpperHalfSpace.ext_fst_height <;> simp [hx, hy]

/-- The differential of the hyperbolic projection is onto at every point. -/
theorem mfderiv_projection_surjective (p : SL2Tilde) :
    Function.Surjective (mfderiv J K projection p) := by
  intro u
  let v := tangentSpaceCastModel K (projection p) u
  refine ⟨(tangentSpaceCastModel J p).symm (v.fst, exp (-p.y) * v.snd, 0), ?_⟩
  apply (tangentSpaceCastModel K (projection p)).injective
  rw [tangentSpaceCastModel_mfderiv_projection]
  simp only [ContinuousLinearEquiv.apply_symm_apply, ← mul_assoc, ← exp_add,
    add_neg_cancel, exp_zero, one_mul]
  exact WithLp.toLp_ofLp 2 v

private theorem inner_projection_coordinates (p : SL2Tilde) (u v : TangentSpace J p) :
    inner ℝ (mfderiv J K projection p u) (mfderiv J K projection p v) =
      exp (-2 * p.y) * (tangentSpaceCastModel J p u).1 *
        (tangentSpaceCastModel J p v).1 +
      (tangentSpaceCastModel J p u).2.1 * (tangentSpaceCastModel J p v).2.1 := by
  rw [UpperHalfSpace.inner_def, tangentSpaceCastModel_mfderiv_projection,
    tangentSpaceCastModel_mfderiv_projection, height_projection, WithLp.prod_inner_apply]
  simp only [Real.inner_apply]
  have he : exp (-2 * p.y) * exp p.y ^ 2 = 1 := by
    rw [← exp_nat_mul, ← exp_add]
    ring_nf
    exact exp_zero
  simp only [neg_mul] at he
  field_simp
  linear_combination -(tangentSpaceCastModel J p u).1 *
    (tangentSpaceCastModel J p v).1 * he

/-- The pullback of the hyperbolic metric is determined by the Sasaki metric and its Ricci
tensor: its value is `(g - 2 Ricci) / 4`. This holds for all tangent vectors, including those
with a nonzero vertical component. -/
theorem inner_mfderiv_projection (p : SL2Tilde) (u v : TangentSpace J p) :
    inner ℝ (mfderiv J K projection p u) (mfderiv J K projection p v) =
      (inner ℝ u v - 2 * (CovariantDerivative.leviCivitaConnection J SL2Tilde).ricciTensor
        p u v) / 4 := by
  rw [inner_projection_coordinates, inner_def, ricciTensor_eq]
  ring

/-- Every Sasaki isometry preserves the pullback of the hyperbolic metric. No assumption
about the induced base map or its orientation is required. -/
theorem inner_mfderiv_projection_mfderiv (Φ : Isom J SL2Tilde) (p : SL2Tilde)
    (u v : TangentSpace J p) :
    inner ℝ (mfderiv J K projection (Φ p) (mfderiv J J Φ p u))
      (mfderiv J K projection (Φ p) (mfderiv J J Φ p v)) =
    inner ℝ (mfderiv J K projection p u) (mfderiv J K projection p v) := by
  simp only [inner_mfderiv_projection, Φ.inner_mfderiv, Φ.ricciTensor_mfderiv]

/-- A diffeomorphism of the hyperbolic base induced by a Sasaki isometry is a Riemannian
isometry. Together with fibre preservation, this gives descent to hyperbolic isometries. -/
theorem exists_isometry_of_projection_eq (Φ : Isom J SL2Tilde)
    (f : UpperHalfSpace ℝ ≃ₘ⟮K, K⟯ UpperHalfSpace ℝ)
    (h : ∀ p, projection (Φ p) = f (projection p)) :
    ∃ Ψ : Isom K (UpperHalfSpace ℝ), Ψ.toDiffeomorph = f := by
  suffices hf : ∀ q (u v : TangentSpace K q),
      inner ℝ (mfderiv K K f q u) (mfderiv K K f q v) = inner ℝ u v by
    exact ⟨{ toDiffeomorph := f, inner_mfderiv' := hf }, rfl⟩
  intro q u v
  obtain ⟨p, rfl⟩ := projection_surjective q
  obtain ⟨a, rfl⟩ := mfderiv_projection_surjective p u
  obtain ⟨b, rfl⟩ := mfderiv_projection_surjective p v
  have heq : projection ∘ Φ = f ∘ projection := funext h
  have hcomp := congrArg (fun F : SL2Tilde → UpperHalfSpace ℝ =>
    inner ℝ (mfderiv J K F p a) (mfderiv J K F p b)) heq
  simp only [mfderiv_comp_apply p (contMDiff_projection.mdifferentiableAt (by simp))
      (Φ.mdifferentiableAt p),
    mfderiv_comp_apply p (f.mdifferentiable (by simp) _)
      (contMDiff_projection.mdifferentiableAt (by simp))] at hcomp
  exact hcomp.symm.trans (inner_mfderiv_projection_mfderiv Φ p a b)

/-- The existing affine lifts project to the corresponding hyperbolic similarities;
the fibre-translation parameter does not affect the base. -/
@[simp] theorem projection_translate (a s c : ℝ) (p : SL2Tilde) :
    projection (translate a s c p) =
      UpperHalfSpace.similarity (exp s) (exp_pos s) (.refl ℝ ℝ) a (projection p) := by
  apply UpperHalfSpace.ext
  rw [coe_projection, UpperHalfSpace.coe_similarity_apply, coe_projection]
  simp [exp_add, mul_comm]

end TauCeti.SL2Tilde
