/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.PositiveScalarCurvature.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.VectorSpace
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Piecewise
public import TauCeti.Geometry.Manifold.Instances.Icc
import TauCeti.Analysis.SpecialFunctions.SmoothTransition

/-!
# Concordance of metrics of positive scalar curvature

Two metrics `g₀` and `g₁` of positive scalar curvature on `M` are *concordant* if there is a metric
of positive scalar curvature on the cylinder `M × ℝ` which is the product metric `g₀ + dt²` where
`t ≤ 0` and `g₁ + dt²` where `t ≥ 1`. Concordance is the relation between metrics of positive
scalar curvature produced by the surgery and bordism constructions.

This file sets up the cylinder metric `g + dt²`, whose scalar curvature at `(x, t)` is that of `g`
at `x`, and reparametrisations of the `ℝ`-coordinate of a metric on `M × ℝ`, pullbacks along
`(x, t) ↦ (x, φ t)` for a smooth `φ` with nowhere vanishing derivative. Reparametrising by
`t ↦ 1 - t` reverses a concordance. To concatenate two concordances, the second is translated by
`2`, glued to the first along `1 < t < 2`, where both are the same product metric, and the window
`[0, 3]` is compressed into `[0, 1]`. The compression is a reparametrisation which is a translation
near both ends: an affine rescaling of `t` would replace `dt²` by a multiple and destroy the product
ends. Hence concordance is an equivalence relation on metrics of positive scalar curvature.

Concordance is natural. Pulling a concordance back along `(x, t) ↦ (f x, t)`, for a smooth map
`f` whose differential is invertible at every point, such as a diffeomorphism or a covering map,
gives a concordance between the pullbacks of its ends. Multiplying a concordance by a constant
`c > 0` multiplies `dt²` by `c` as well; reparametrising by `t ↦ t / √c` restores the product ends,
so `c g₀` and `c g₁` are concordant when `g₀` and `g₁` are. The product of a concordance from `g₀`
to `g₁` with a metric `g₂` of nonnegative scalar curvature, with the cylinder coordinate moved
from `M × ℝ` to `(M × N) × ℝ`, is a concordance from `g₀ × g₂` to `g₁ × g₂`.

Concordances can equivalently be taken on the manifold with boundary `M × [0, 1]`: a *collared
concordance* is a metric of positive scalar curvature on `M × [0, 1]` which is `g₀ + dt²` near
`t = 0` and `g₁ + dt²` near `t = 1`, where `g + dt²` on `M × [0, 1]` is the restriction
`Bundle.ContMDiffRiemannianMetric.restrictIcc` of the cylinder metric. The restriction of a
concordance to `M × [0, 1]` itself need not have product collars. Instead, a concordance is
pulled back along `(x, t) ↦ (x, ψ t)` for a smooth increasing `ψ : [0, 1] → [-1, 2]` which is
`t ↦ t - 1` near `0` and `t ↦ t + 1` near `1`. Conversely, a collared concordance is extended by
the product ends: it is pulled back to `M × ℝ` along `(x, t) ↦ (x, θ t)` for a smooth increasing
`θ : ℝ → (0, 1)` which is the identity away from the two collars, and glued to `g₀ + dt²` and
`g₁ + dt²` over the collars.

## Main definitions

* `Bundle.ContMDiffRiemannianMetric.cylinder`: the cylinder metric `g + dt²` on `M × ℝ`.
* `Bundle.ContMDiffRiemannianMetric.reparamTime`: the pullback of a metric on `M × ℝ` along
  `(x, t) ↦ (x, φ t)`.
* `Bundle.ContMDiffRiemannianMetric.IsConcordance`: a concordance from `g₀` to `g₁`.
* `Bundle.ContMDiffRiemannianMetric.Concordant`: `g₀` and `g₁` are concordant, characterised by
  `Bundle.ContMDiffRiemannianMetric.concordant_iff`.
* `Bundle.ContMDiffRiemannianMetric.IsCollaredConcordance`: a collared concordance from `g₀` to
  `g₁` on `M × [0, 1]`.

## Main results

* `Bundle.ContMDiffRiemannianMetric.scalarCurvature_cylinder`: `Scal(g + dt²)(x, t) = Scal(g)(x)`.
* `Bundle.ContMDiffRiemannianMetric.scalarCurvature_reparamTime`: the scalar curvature of the
  reparametrised metric at `(x, t)` is that of the original metric at `(x, φ t)`.
* `Bundle.ContMDiffRiemannianMetric.cylinder_reparamTime_inner`: a reparametrisation with
  `|φ'| = 1` preserves the cylinder metric.
* `Bundle.ContMDiffRiemannianMetric.IsConcordance.hasPositiveScalarCurvature_left` and
  `Bundle.ContMDiffRiemannianMetric.IsConcordance.hasPositiveScalarCurvature_right`: the ends of a
  concordance have positive scalar curvature.
* `Bundle.ContMDiffRiemannianMetric.concordant_self_iff`: a metric is concordant to itself exactly
  when it has positive scalar curvature.
* `Bundle.ContMDiffRiemannianMetric.IsConcordance.reparamTime_one_sub` and
  `Bundle.ContMDiffRiemannianMetric.Concordant.symm`: reversal of concordances.
* `Bundle.ContMDiffRiemannianMetric.Concordant.trans`: concatenation of concordances.
* `Bundle.ContMDiffRiemannianMetric.equivalence_concordant`: concordance is an equivalence relation
  on metrics of positive scalar curvature.
* `Bundle.ContMDiffRiemannianMetric.concordant_of_inner_eq_cylinder`: a metric of positive scalar
  curvature on `M × ℝ` with product ends outside any window `[a, b]` witnesses a concordance.
* `Bundle.ContMDiffRiemannianMetric.Concordant.pullback` and
  `Bundle.ContMDiffRiemannianMetric.concordant_pullback_iff`: concordance is preserved by pullback
  along maps with invertible differential, and preserved and reflected by pullback along
  diffeomorphisms.
* `Bundle.ContMDiffRiemannianMetric.Concordant.rescale_const` and
  `Bundle.ContMDiffRiemannianMetric.concordant_rescale_const_iff`: rescaling by a positive constant
  preserves and reflects concordance.
* `Bundle.ContMDiffRiemannianMetric.Concordant.prodTangentSpace_of_nonneg`: concordance is preserved
  by products with a metric of nonnegative scalar curvature.
* `Bundle.ContMDiffRiemannianMetric.IsConcordance.exists_isCollaredConcordance` and
  `Bundle.ContMDiffRiemannianMetric.IsCollaredConcordance.concordant`: concordances give collared
  concordances with the same ends, and conversely, so that
  `Bundle.ContMDiffRiemannianMetric.concordant_iff_exists_isCollaredConcordance`.

## References

* M. Gromov, H. B. Lawson, *The classification of simply connected manifolds of positive
  scalar curvature*, Ann. of Math. 111 (1980), 423–434.
* S. Stolz, *Positive scalar curvature—constructions and obstructions*, arXiv:2202.05904, for
  concordance and isotopy of metrics of positive scalar curvature.
-/

public section

open Bundle Set Topology Filter
open TauCeti.Manifold (tangentSpaceProdEquiv tangentSpaceProdEquiv_apply mfderiv_prodMap_apply
  tangentSpaceProdEquiv_mfderiv_prodMap_id isInvertible_mfderiv_prodMap_id
  isInvertible_mfderiv_prodMap_id_right isInvertible_mfderiv_prodMap_id_subtypeVal_Icc
  contMDiff_prod_right_comm isInvertible_mfderiv_prod_right_comm mfderiv_prod_right_comm_apply)
open scoped ContDiff Manifold

noncomputable section

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

section Cylinder

variable (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))

/-- The cylinder metric `g + dt²` on `M × ℝ`: the product of `g` with the standard metric of
`ℝ`. -/
def cylinder : ContMDiffRiemannianMetric (I.prod 𝓘(ℝ)) ∞ (E × ℝ)
    (fun p : M × ℝ ↦ TangentSpace (I.prod 𝓘(ℝ)) p) :=
  g.prodTangentSpace ((riemannianMetricVectorSpace ℝ).ofLE le_top)

/-- The cylinder metric `g + dt²` pairs the `M`-components with `g` and multiplies the
`ℝ`-components. -/
@[simp]
theorem cylinder_inner (p : M × ℝ) (v w : TangentSpace (I.prod 𝓘(ℝ)) p) :
    g.cylinder.inner p v w =
      g.inner p.1 (tangentSpaceProdEquiv p v).1 (tangentSpaceProdEquiv p w).1 +
        NormedSpace.fromTangentSpace p.2 (tangentSpaceProdEquiv p v).2 *
          NormedSpace.fromTangentSpace p.2 (tangentSpaceProdEquiv p w).2 := by
  rw [cylinder, prodTangentSpace_inner, ofLE_inner]
  -- The standard metric of `ℝ` is the inner product of `ℝ`, read through the identification
  -- `NormedSpace.fromTangentSpace` of each tangent space of `ℝ` with `ℝ`, which is the identity.
  exact congrArg (_ + ·) (Real.inner_apply _ _)

variable [FiniteDimensional ℝ E] [T2Space M]

/-- The scalar curvature of the cylinder metric `g + dt²` at `(x, t)` is that of `g` at `x`. -/
@[simp]
theorem scalarCurvature_cylinder (p : M × ℝ) :
    g.cylinder.scalarCurvature p = g.scalarCurvature p.1 := by
  -- Mathlib's `RiemannianBundle` instance on the tangent spaces of `ℝ` is defined to be the
  -- standard metric `riemannianMetricVectorSpace ℝ`, whose scalar curvature vanishes.
  rw [cylinder, scalarCurvature_prodTangentSpace,
    scalarCurvature_eq_scalarCurvature_leviCivitaConnection
      ((riemannianMetricVectorSpace ℝ).ofLE le_top) (by rw [toRiemannianMetric_ofLE]; rfl),
    TauCeti.Manifold.scalarCurvature_leviCivitaConnection_model_space, add_zero]

/-- The cylinder metric `g + dt²` has positive scalar curvature exactly when `g` does. -/
@[simp]
theorem hasPositiveScalarCurvature_cylinder_iff :
    g.cylinder.HasPositiveScalarCurvature ↔ g.HasPositiveScalarCurvature := by
  simp only [hasPositiveScalarCurvature_iff, scalarCurvature_cylinder, Prod.forall]
  exact ⟨fun h x ↦ h x 0, fun h x _ ↦ h x⟩

end Cylinder

section ReparamTime

variable [FiniteDimensional ℝ E] {φ : ℝ → ℝ}

variable (G : ContMDiffRiemannianMetric (I.prod 𝓘(ℝ)) ∞ (E × ℝ)
    (fun p : M × ℝ ↦ TangentSpace (I.prod 𝓘(ℝ)) p))

/-- Reparametrise the `ℝ`-coordinate of a metric `G` on `M × ℝ` by a smooth `φ : ℝ → ℝ` with
nowhere vanishing derivative: the pullback of `G` along `(x, t) ↦ (x, φ t)`. -/
def reparamTime (hφ : ContDiff ℝ ∞ φ) (hφ' : ∀ t, deriv φ t ≠ 0) :
    ContMDiffRiemannianMetric (I.prod 𝓘(ℝ)) ∞ (E × ℝ)
      (fun p : M × ℝ ↦ TangentSpace (I.prod 𝓘(ℝ)) p) :=
  G.pullback (Prod.map id φ) (contMDiff_id.prodMap (hφ.contMDiff.of_le (by simp))) fun p ↦
    (isInvertible_mfderiv_prodMap_id (hφ.differentiable (by simp) p.2) (hφ' p.2)).injective

variable {G}

/-- The reparametrised metric at `(x, t)` is `G` at `(x, φ t)`, evaluated on the images of the
tangent vectors under the differential of `(x, t) ↦ (x, φ t)`. -/
@[simp]
theorem reparamTime_inner (hφ : ContDiff ℝ ∞ φ) (hφ' : ∀ t, deriv φ t ≠ 0) (p : M × ℝ)
    (v w : TangentSpace (I.prod 𝓘(ℝ)) p) :
    (G.reparamTime hφ hφ').inner p v w =
      G.inner (p.1, φ p.2) (mfderiv (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ)) (Prod.map id φ) p v)
        (mfderiv (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ)) (Prod.map id φ) p w) :=
  G.pullback_inner _ _ _ p v w

/-- The reparametrised metric at `(x, t)` only depends on `G` at `(x, φ t)`. -/
theorem reparamTime_inner_congr
    {G' : ContMDiffRiemannianMetric (I.prod 𝓘(ℝ)) ∞ (E × ℝ)
      (fun p : M × ℝ ↦ TangentSpace (I.prod 𝓘(ℝ)) p)}
    (hφ : ContDiff ℝ ∞ φ) (hφ' : ∀ t, deriv φ t ≠ 0) {p : M × ℝ}
    (h : G.inner (p.1, φ p.2) = G'.inner (p.1, φ p.2)) :
    (G.reparamTime hφ hφ').inner p = (G'.reparamTime hφ hφ').inner p := by
  ext v w
  rw [reparamTime_inner, reparamTime_inner, h]

/-- The scalar curvature of the reparametrised metric at `(x, t)` is that of `G` at `(x, φ t)`. -/
@[simp]
theorem scalarCurvature_reparamTime [T2Space M] (hφ : ContDiff ℝ ∞ φ) (hφ' : ∀ t, deriv φ t ≠ 0)
    (p : M × ℝ) :
    (G.reparamTime hφ hφ').scalarCurvature p = G.scalarCurvature (p.1, φ p.2) :=
  scalarCurvature_pullback_of_isInvertible G
    (contMDiff_id.prodMap (hφ.contMDiff.of_le (by simp)))
    (fun p ↦ isInvertible_mfderiv_prodMap_id (hφ.differentiable (by simp) p.2) (hφ' p.2)) p

/-- Reparametrising the `ℝ`-coordinate preserves positive scalar curvature. -/
theorem HasPositiveScalarCurvature.reparamTime [T2Space M] (h : G.HasPositiveScalarCurvature)
    (hφ : ContDiff ℝ ∞ φ) (hφ' : ∀ t, deriv φ t ≠ 0) :
    (G.reparamTime hφ hφ').HasPositiveScalarCurvature :=
  (hasPositiveScalarCurvature_iff _).2 fun p ↦ by
    rw [scalarCurvature_reparamTime]
    exact (hasPositiveScalarCurvature_iff _).1 h _

/-- A reparametrisation of the `ℝ`-coordinate with `|φ' t| = 1` leaves the cylinder metric
`g + dt²` unchanged at `(x, t)`. -/
theorem cylinder_reparamTime_inner
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (hφ : ContDiff ℝ ∞ φ)
    (hφ' : ∀ t, deriv φ t ≠ 0) {p : M × ℝ} (h : |deriv φ p.2| = 1) :
    (g.cylinder.reparamTime hφ hφ').inner p = g.cylinder.inner p := by
  have hd := hφ.differentiable (by simp) p.2
  have h₁ : deriv φ p.2 * deriv φ p.2 = 1 := by rw [← abs_mul_abs_self, h, one_mul]
  ext v w
  rw [reparamTime_inner, cylinder_inner, cylinder_inner,
    tangentSpaceProdEquiv_mfderiv_prodMap_id hd, tangentSpaceProdEquiv_mfderiv_prodMap_id hd]
  simp only [ContinuousLinearEquiv.apply_symm_apply]
  linear_combination (NormedSpace.fromTangentSpace p.2 (tangentSpaceProdEquiv p v).2 *
    NormedSpace.fromTangentSpace p.2 (tangentSpaceProdEquiv p w).2) * h₁

/-- A reparametrisation of the `ℝ`-coordinate with `|φ' t| = 1` of a metric which is the cylinder
metric `g + dt²` at `(x, φ t)` is the cylinder metric `g + dt²` at `(x, t)`. -/
theorem reparamTime_inner_eq_cylinder_inner
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} (hφ : ContDiff ℝ ∞ φ)
    (hφ' : ∀ t, deriv φ t ≠ 0) {p : M × ℝ}
    (h : G.inner (p.1, φ p.2) = g.cylinder.inner (p.1, φ p.2)) (hd : |deriv φ p.2| = 1) :
    (G.reparamTime hφ hφ').inner p = g.cylinder.inner p :=
  (reparamTime_inner_congr hφ hφ' h).trans (cylinder_reparamTime_inner g hφ hφ' hd)

end ReparamTime

section Concordance

variable [FiniteDimensional ℝ E] [T2Space M]
  {G G₁ G₂ : ContMDiffRiemannianMetric (I.prod 𝓘(ℝ)) ∞ (E × ℝ)
    (fun p : M × ℝ ↦ TangentSpace (I.prod 𝓘(ℝ)) p)}
  {g g₀ g₁ g₂ : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}

variable (G g₀ g₁) in
/-- A **concordance** from `g₀` to `g₁` is a metric of positive scalar curvature on `M × ℝ` which
is the cylinder metric `g₀ + dt²` where `t ≤ 0` and the cylinder metric `g₁ + dt²` where
`t ≥ 1`. -/
structure IsConcordance : Prop where
  /-- A concordance has positive scalar curvature. -/
  hasPositiveScalarCurvature : G.HasPositiveScalarCurvature
  /-- A concordance from `g₀` is `g₀ + dt²` where `t ≤ 0`. -/
  inner_of_nonpos : ∀ p : M × ℝ, p.2 ≤ 0 → G.inner p = g₀.cylinder.inner p
  /-- A concordance to `g₁` is `g₁ + dt²` where `t ≥ 1`. -/
  inner_of_one_le : ∀ p : M × ℝ, 1 ≤ p.2 → G.inner p = g₁.cylinder.inner p

variable (g₀ g₁) in
/-- Two metrics on `M` are **concordant** if there is a concordance from one to the other. -/
def Concordant : Prop :=
  ∃ G, IsConcordance G g₀ g₁

variable (g₀ g₁) in
/-- Two metrics are concordant exactly when there is a concordance from one to the other. -/
theorem concordant_iff : Concordant g₀ g₁ ↔ ∃ G, IsConcordance G g₀ g₁ :=
  Iff.rfl

/-- The ends of a concordance are concordant. -/
theorem IsConcordance.concordant (h : IsConcordance G g₀ g₁) : Concordant g₀ g₁ :=
  ⟨G, h⟩

/-- The metric at the start of a concordance has positive scalar curvature. -/
theorem IsConcordance.hasPositiveScalarCurvature_left (h : IsConcordance G g₀ g₁) :
    g₀.HasPositiveScalarCurvature := (hasPositiveScalarCurvature_iff _).2 fun x ↦ by
  have hU : IsOpen {p : M × ℝ | p.2 < 0} := isOpen_lt continuous_snd continuous_const
  have := (hasPositiveScalarCurvature_iff _).1 h.hasPositiveScalarCurvature (x, -1)
  rwa [eqOn_scalarCurvature hU (fun p hp ↦ h.inner_of_nonpos p (le_of_lt hp))
    (show (-1 : ℝ) < 0 by norm_num), scalarCurvature_cylinder] at this

/-- The metric at the end of a concordance has positive scalar curvature. -/
theorem IsConcordance.hasPositiveScalarCurvature_right (h : IsConcordance G g₀ g₁) :
    g₁.HasPositiveScalarCurvature := (hasPositiveScalarCurvature_iff _).2 fun x ↦ by
  have hU : IsOpen {p : M × ℝ | 1 < p.2} := isOpen_lt continuous_const continuous_snd
  have := (hasPositiveScalarCurvature_iff _).1 h.hasPositiveScalarCurvature (x, 2)
  rwa [eqOn_scalarCurvature hU (fun p hp ↦ h.inner_of_one_le p (le_of_lt hp))
    (show (1 : ℝ) < 2 by norm_num), scalarCurvature_cylinder] at this

/-- The cylinder metric `g + dt²` of a metric of positive scalar curvature is a concordance from
`g` to itself. -/
theorem HasPositiveScalarCurvature.isConcordance_cylinder (h : g.HasPositiveScalarCurvature) :
    IsConcordance g.cylinder g g :=
  ⟨(hasPositiveScalarCurvature_cylinder_iff g).2 h, fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩

/-- A metric is concordant to itself exactly when it has positive scalar curvature. -/
theorem concordant_self_iff : Concordant g g ↔ g.HasPositiveScalarCurvature :=
  ⟨fun ⟨_, h⟩ ↦ h.hasPositiveScalarCurvature_left, fun h ↦ h.isConcordance_cylinder.concordant⟩

/-- Reversing the `ℝ`-coordinate by `t ↦ 1 - t` turns a concordance from `g₀` to `g₁` into a
concordance from `g₁` to `g₀`. -/
theorem IsConcordance.reparamTime_one_sub (h : IsConcordance G g₀ g₁) :
    IsConcordance (G.reparamTime (φ := fun t ↦ 1 - t) (contDiff_const.sub contDiff_id)
      (fun t ↦ by simp)) g₁ g₀ := by
  have hd (t : ℝ) : |deriv (fun t : ℝ ↦ 1 - t) t| = 1 := by simp
  refine ⟨h.hasPositiveScalarCurvature.reparamTime _ _, fun p hp ↦ ?_, fun p hp ↦ ?_⟩
  · exact reparamTime_inner_eq_cylinder_inner _ _ (h.inner_of_one_le _ (by simp; linarith))
      (hd p.2)
  · exact reparamTime_inner_eq_cylinder_inner _ _ (h.inner_of_nonpos _ (by simp; linarith))
      (hd p.2)

/-- Concordance is symmetric. -/
theorem Concordant.symm (h : Concordant g₀ g₁) : Concordant g₁ g₀ :=
  let ⟨_, hG⟩ := h
  hG.reparamTime_one_sub.concordant

/-- Concordance is a symmetric relation. -/
theorem concordant_comm : Concordant g₀ g₁ ↔ Concordant g₁ g₀ :=
  ⟨Concordant.symm, Concordant.symm⟩

/-- For `d ≥ 0`, the smooth increasing map `t ↦ t + d s(3t - 1)` of `ℝ`, with `s` the smooth
transition from `0` to `1` on `[0, 1]`. It is the identity on `t ≤ 1/3` and the translation by `d`
on `t ≥ 2/3`, so it compresses the window `[0, 1 + d]` into `[0, 1]`. -/
private def stretch (d t : ℝ) : ℝ :=
  t + d * Real.smoothTransition (3 * t - 1)

private theorem contDiff_stretch (d : ℝ) : ContDiff ℝ ∞ (stretch d) :=
  contDiff_id.add (contDiff_const.mul
    ((Real.smoothTransition.contDiff (n := ⊤)).comp (by fun_prop)))

private theorem hasDerivAt_stretch (d t : ℝ) :
    HasDerivAt (stretch d) (1 + d * (deriv Real.smoothTransition (3 * t - 1) * 3)) t := by
  have h : HasDerivAt (fun t : ℝ ↦ 3 * t - 1) 3 t := by
    simpa using ((hasDerivAt_id t).const_mul 3).sub_const 1
  exact (hasDerivAt_id t).add
    ((Real.smoothTransition.contDiffAt (n := 1)).differentiableAt one_ne_zero
      |>.hasDerivAt.comp t h |>.const_mul d)

private theorem deriv_stretch_ne_zero {d : ℝ} (hd : 0 ≤ d) (t : ℝ) : deriv (stretch d) t ≠ 0 := by
  rw [(hasDerivAt_stretch d t).deriv]
  have := Real.smoothTransition.monotone.deriv_nonneg (x := 3 * t - 1)
  positivity

private theorem stretch_eventuallyEq_of_lt (d : ℝ) {t : ℝ} (ht : t < 1 / 3) :
    stretch d =ᶠ[𝓝 t] id := by
  filter_upwards [eventually_lt_nhds ht] with s hs
  simp [stretch, Real.smoothTransition.zero_of_nonpos (by linarith : 3 * s - 1 ≤ 0)]

private theorem stretch_eventuallyEq_of_gt (d : ℝ) {t : ℝ} (ht : 2 / 3 < t) :
    stretch d =ᶠ[𝓝 t] (· + d) := by
  filter_upwards [eventually_gt_nhds ht] with s hs
  simp [stretch, Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 3 * s - 1)]

/-- If a metric of positive scalar curvature on `M × ℝ` is `g₀ + dt²` where `t ≤ a` and
`g₁ + dt²` where `t ≥ b`, then `g₀` and `g₁` are concordant, whatever the window `[a, b]`. -/
theorem concordant_of_inner_eq_cylinder (hG : G.HasPositiveScalarCurvature) {a b : ℝ}
    (h₀ : ∀ p : M × ℝ, p.2 ≤ a → G.inner p = g₀.cylinder.inner p)
    (h₁ : ∀ p : M × ℝ, b ≤ p.2 → G.inner p = g₁.cylinder.inner p) : Concordant g₀ g₁ := by
  -- Reparametrise by `t ↦ stretch d t + a`, which is `t ↦ t + a` near `t ≤ 0` and
  -- `t ↦ t + (d + a)` near `t ≥ 1`, where `1 + d + a ≥ b`.
  set d := max (b - a - 1) 0
  have hd : 0 ≤ d := le_max_right _ _
  have hφ : ContDiff ℝ ∞ fun t ↦ stretch d t + a := (contDiff_stretch d).add contDiff_const
  have hφ' (t : ℝ) : deriv (fun t ↦ stretch d t + a) t ≠ 0 := by
    rw [deriv_add_const]
    exact deriv_stretch_ne_zero hd t
  refine ⟨G.reparamTime hφ hφ', hG.reparamTime _ _, fun p hp ↦ ?_, fun p hp ↦ ?_⟩
  · have hψ : (fun t ↦ stretch d t + a) =ᶠ[𝓝 p.2] (· + a) :=
      (stretch_eventuallyEq_of_lt d (show p.2 < 1 / 3 by linarith)).fun_comp (· + a)
    refine reparamTime_inner_eq_cylinder_inner _ _ ?_ (by simp [hψ.deriv_eq])
    rw [hψ.eq_of_nhds]
    exact h₀ _ (by simp; linarith)
  · have hψ : (fun t ↦ stretch d t + a) =ᶠ[𝓝 p.2] (· + (d + a)) := by
      filter_upwards [stretch_eventuallyEq_of_gt d (show 2 / 3 < p.2 by linarith)] with t ht
      simp only [ht]
      ring
    refine reparamTime_inner_eq_cylinder_inner _ _ ?_ (by simp [hψ.deriv_eq])
    rw [hψ.eq_of_nhds]
    exact h₁ _ (by simp; linarith [le_max_left (b - a - 1) 0])

/-- **Concatenation of concordances**: concordance is transitive. Translate a concordance from
`g₁` to `g₂` to the window `[2, 3]`, glue it to a concordance from `g₀` to `g₁` along `1 < t < 2`,
where both are `g₁ + dt²`, and compress the window `[0, 3]` into `[0, 1]`. -/
theorem Concordant.trans (h₁ : Concordant g₀ g₁) (h₂ : Concordant g₁ g₂) : Concordant g₀ g₂ := by
  obtain ⟨G₁, h₁⟩ := h₁
  obtain ⟨G₂, h₂⟩ := h₂
  have hd (t : ℝ) : |deriv (fun t : ℝ ↦ t - 2) t| = 1 := by simp
  -- `G₂` translated to the window `[2, 3]`.
  let G₂' := G₂.reparamTime (φ := fun t ↦ t - 2) (contDiff_id.sub contDiff_const)
    (fun t ↦ by simp)
  have hG₂'₁ (p : M × ℝ) (hp : p.2 ≤ 2) : G₂'.inner p = g₁.cylinder.inner p :=
    reparamTime_inner_eq_cylinder_inner _ _ (h₂.inner_of_nonpos _ (by simpa using hp)) (hd p.2)
  have hG₂'₂ (p : M × ℝ) (hp : 3 ≤ p.2) : G₂'.inner p = g₂.cylinder.inner p :=
    reparamTime_inner_eq_cylinder_inner _ _ (h₂.inner_of_one_le _ (by simp; linarith)) (hd p.2)
  -- Glue `G₁` on `t < 2` to the translate of `G₂` on `t > 1`.
  have hU : IsOpen {p : M × ℝ | p.2 < 2} := isOpen_lt continuous_snd continuous_const
  have hV : IsOpen {p : M × ℝ | 1 < p.2} := isOpen_lt continuous_const continuous_snd
  have hUV : {p : M × ℝ | p.2 < 2} ∪ {p | 1 < p.2} = univ :=
    eq_univ_of_forall fun p ↦ (lt_or_ge p.2 2).imp id fun hp ↦ by simp; linarith
  refine concordant_of_inner_eq_cylinder (a := 0) (b := 3)
    (G := G₁.piecewise G₂' hU hV hUV fun p hp ↦ by
      rw [h₁.inner_of_one_le p hp.2.le, hG₂'₁ p hp.1.le])
    ((hasPositiveScalarCurvature_iff _).2 fun p ↦ ?_)
    (fun p hp ↦ (piecewise_inner_of_mem_left (show p.2 < 2 by linarith)).trans
      (h₁.inner_of_nonpos p hp))
    (fun p hp ↦ (piecewise_inner_of_mem_right (show 1 < p.2 by linarith)).trans (hG₂'₂ p hp))
  rcases lt_or_ge p.2 2 with hp | hp
  · rw [eqOn_scalarCurvature hU (fun q hq ↦ piecewise_inner_of_mem_left hq) hp]
    exact (hasPositiveScalarCurvature_iff _).1 h₁.hasPositiveScalarCurvature p
  · rw [eqOn_scalarCurvature hV (fun q hq ↦ piecewise_inner_of_mem_right hq)
      (show 1 < p.2 by linarith)]
    exact (hasPositiveScalarCurvature_iff _).1 (h₂.hasPositiveScalarCurvature.reparamTime _ _) p

/-- Concordance is an equivalence relation on the metrics of positive scalar curvature on `M`. -/
theorem equivalence_concordant :
    Equivalence fun g₀ g₁ : {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x) //
      g.HasPositiveScalarCurvature} ↦ Concordant g₀.1 g₁.1 :=
  ⟨fun g ↦ concordant_self_iff.2 g.2, Concordant.symm, Concordant.trans⟩

end Concordance

section Collar

/-! ### Collared concordances on `M × [0, 1]` -/

variable [FiniteDimensional ℝ E]

/-! The time map used to extend a collared concordance by product ends. -/

/-- The map `s ↦ s / (1 + s e^{-1/s})`, read as the identity for `s ≤ 0`. It is smooth with
everywhere positive derivative and bounded above by `1`. -/
private def saturate (s : ℝ) : ℝ :=
  s / (1 + s * expNegInvGlue s)

private theorem one_add_mul_expNegInvGlue_pos (s : ℝ) : 0 < 1 + s * expNegInvGlue s := by
  rcases le_or_gt s 0 with hs | hs
  · simp [expNegInvGlue.zero_of_nonpos hs]
  · have := mul_pos hs (expNegInvGlue.pos_of_pos hs)
    linarith

private theorem saturate_of_nonpos {s : ℝ} (hs : s ≤ 0) : saturate s = s := by
  simp [saturate, expNegInvGlue.zero_of_nonpos hs]

private theorem saturate_nonneg {s : ℝ} (hs : 0 ≤ s) : 0 ≤ saturate s :=
  div_nonneg hs (one_add_mul_expNegInvGlue_pos s).le

private theorem saturate_lt_one (s : ℝ) : saturate s < 1 := by
  rcases le_or_gt s 0 with hs | hs
  · rw [saturate_of_nonpos hs]
    linarith
  · -- `s (1 - e^{-1/s}) < s (1 - (1 - s⁻¹)) = 1`.
    rw [saturate, div_lt_one (one_add_mul_expNegInvGlue_pos s)]
    have he : expNegInvGlue s = Real.exp (-s⁻¹) := by simp [expNegInvGlue, hs.not_ge]
    have h := mul_lt_mul_of_pos_left (Real.add_one_lt_exp (x := -s⁻¹) (by simp [hs.ne'])) hs
    rw [mul_add, mul_neg, mul_inv_cancel₀ hs.ne', mul_one] at h
    rw [he]
    linarith

private theorem contDiff_saturate : ContDiff ℝ ∞ saturate :=
  contDiff_id.div (contDiff_const.add (contDiff_id.mul (expNegInvGlue.contDiff (n := ⊤))))
    fun s ↦ (one_add_mul_expNegInvGlue_pos s).ne'

private theorem exists_hasDerivAt_saturate (s : ℝ) : ∃ d, 0 < d ∧ HasDerivAt saturate d s := by
  have hd := (hasDerivAt_id s).div
    (((hasDerivAt_id s).mul (expNegInvGlue.hasDerivAt s)).const_add 1)
    (one_add_mul_expNegInvGlue_pos s).ne'
  refine ⟨(1 - expNegInvGlue s) / (1 + s * expNegInvGlue s) ^ 2,
    div_pos (sub_pos.2 (expNegInvGlue.lt_one s)) (pow_pos (one_add_mul_expNegInvGlue_pos s) 2), ?_⟩
  convert hd using 1
  · funext x
    simp [saturate]
  -- `s ^ 2 * s⁻¹ ^ 2 * e = e`, also for `s = 0`, where `e = 0`.
  rcases eq_or_ne s 0 with rfl | hs
  · simp
  · simp only [id_eq, one_mul, Pi.mul_apply]
    field_simp
    ring

/-- The smooth increasing map `t ↦ (1 - δ) + δ saturate ((t - (1 - δ)) / δ)`, the identity for
`t ≤ 1 - δ` and bounded above by `1`. -/
private def collarTimeUpper (δ t : ℝ) : ℝ :=
  1 - δ + δ * saturate ((t - (1 - δ)) / δ)

/-- The smooth increasing map `t ↦ δ - δ saturate ((δ - u t) / δ)` of `ℝ` into `(0, 1)`, with `u`
the map `collarTimeUpper δ`. It is the identity on `[δ, 1 - δ]`. -/
private def collarTime (δ t : ℝ) : ℝ :=
  δ - δ * saturate ((δ - collarTimeUpper δ t) / δ)

variable {δ : ℝ}

private theorem collarTimeUpper_lt_one (hδ : 0 < δ) (t : ℝ) : collarTimeUpper δ t < 1 := by
  have := mul_lt_mul_of_pos_left (saturate_lt_one ((t - (1 - δ)) / δ)) hδ
  rw [collarTimeUpper]
  linarith

private theorem collarTime_of_mem (hδ : 0 < δ) {t : ℝ} (ht : t ∈ Icc δ (1 - δ)) :
    collarTime δ t = t := by
  have hu : collarTimeUpper δ t = t := by
    rw [collarTimeUpper, saturate_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith [ht.2])
      hδ.le)]
    field_simp
    ring
  rw [collarTime, hu, saturate_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith [ht.1])
    hδ.le)]
  field_simp
  ring

private theorem collarTime_pos (hδ : 0 < δ) (t : ℝ) : 0 < collarTime δ t := by
  have := mul_lt_mul_of_pos_left (saturate_lt_one ((δ - collarTimeUpper δ t) / δ)) hδ
  rw [collarTime]
  linarith

private theorem collarTime_lt_one (hδ : 0 < δ) (hδ₁ : δ < 1) (t : ℝ) : collarTime δ t < 1 := by
  have hu := collarTimeUpper_lt_one hδ t
  rcases le_or_gt δ (collarTimeUpper δ t) with h | h
  · rw [collarTime, saturate_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le)]
    field_simp
    linarith
  · have := mul_nonneg hδ.le (saturate_nonneg (div_nonneg (sub_nonneg.2 h.le) hδ.le))
    rw [collarTime]
    linarith

private theorem contDiff_collarTime : ContDiff ℝ ∞ (collarTime δ) :=
  contDiff_const.sub (contDiff_const.mul (contDiff_saturate.comp ((contDiff_const.sub
    (contDiff_const.add (contDiff_const.mul (contDiff_saturate.comp
      ((contDiff_id.sub contDiff_const).div_const δ))))).div_const δ)))

private theorem deriv_collarTime_ne_zero (hδ : 0 < δ) (t : ℝ) : deriv (collarTime δ) t ≠ 0 := by
  obtain ⟨d₁, hd₁, h₁⟩ := exists_hasDerivAt_saturate ((t - (1 - δ)) / δ)
  have hu : HasDerivAt (collarTimeUpper δ) (δ * (d₁ * (1 / δ))) t :=
    ((h₁.comp t (((hasDerivAt_id t).sub_const (1 - δ)).div_const δ)).const_mul δ).const_add _
  obtain ⟨d₂, hd₂, h₂⟩ := exists_hasDerivAt_saturate ((δ - collarTimeUpper δ t) / δ)
  have hl : HasDerivAt (fun t ↦ (δ - collarTimeUpper δ t) / δ) ((0 - δ * (d₁ * (1 / δ))) / δ) t :=
    ((hasDerivAt_const t δ).sub hu).div_const δ
  have hc : HasDerivAt (fun t ↦ saturate ((δ - collarTimeUpper δ t) / δ))
      (d₂ * ((0 - δ * (d₁ * (1 / δ))) / δ)) t :=
    HasDerivAt.comp (h := fun t ↦ (δ - collarTimeUpper δ t) / δ) t h₂ hl
  have h : HasDerivAt (collarTime δ) (-(δ * (d₂ * ((0 - δ * (d₁ * (1 / δ))) / δ)))) t :=
    (hc.const_mul δ).const_sub δ
  rw [h.deriv]
  have : -(δ * (d₂ * ((0 - δ * (d₁ * (1 / δ))) / δ))) = d₂ * d₁ := by
    field_simp
    ring
  rw [this]
  positivity

/-- `collarTime δ`, as a map into the unit interval. -/
private def collarTimeIcc (hδ : 0 < δ) (hδ₁ : δ < 1) (t : ℝ) : unitInterval :=
  ⟨collarTime δ t, (collarTime_pos hδ t).le, (collarTime_lt_one hδ hδ₁ t).le⟩

@[simp]
private theorem coe_collarTimeIcc (hδ : 0 < δ) (hδ₁ : δ < 1) (t : ℝ) :
    (collarTimeIcc hδ hδ₁ t : ℝ) = collarTime δ t :=
  rfl

omit [IsManifold I ∞ M] [FiniteDimensional ℝ E] in
private theorem contMDiff_prodMap_id_collarTimeIcc (hδ : 0 < δ) (hδ₁ : δ < 1) {n : ℕ∞ω}
    (hn : n ≤ ∞) : ContMDiff (I.prod 𝓘(ℝ)) (I.prod (𝓡∂ 1)) n
      (Prod.map id (collarTimeIcc hδ hδ₁) : M × ℝ → M × unitInterval) := by
  refine contMDiff_id.prodMap (contMDiff_iff_comp_subtypeVal_Icc.2 ⟨?_, ?_⟩)
  · exact (contDiff_collarTime.continuous).subtype_mk _
  · exact (contDiff_collarTime (δ := δ)).contMDiff.of_le hn

omit [IsManifold I ∞ M] [FiniteDimensional ℝ E] in
/-- The inclusion `M × [0, 1] → M × ℝ` after `(x, t) ↦ (x, collarTime δ t)` is
`(x, t) ↦ (x, collarTime δ t)` on `M × ℝ`. -/
private theorem mfderiv_prodMap_id_collarTime (hδ : 0 < δ) (hδ₁ : δ < 1) (p : M × ℝ) :
    mfderiv (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ)) (Prod.map id (collarTime δ)) p =
      (mfderiv (I.prod (𝓡∂ 1)) (I.prod 𝓘(ℝ)) (Prod.map id Subtype.val : M × unitInterval → M × ℝ)
        (Prod.map id (collarTimeIcc hδ hδ₁) p)).comp
      (mfderiv (I.prod 𝓘(ℝ)) (I.prod (𝓡∂ 1)) (Prod.map id (collarTimeIcc hδ hδ₁)) p) :=
  mfderiv_comp p ((contMDiff_id.prodMap (contMDiff_subtypeVal_Icc (n := 1))).mdifferentiableAt
    one_ne_zero) ((contMDiff_prodMap_id_collarTimeIcc hδ hδ₁ (n := 1) (by simp)).mdifferentiableAt
      one_ne_zero)

omit [IsManifold I ∞ M] [FiniteDimensional ℝ E] in
private theorem mfderiv_prodMap_id_collarTime_apply (hδ : 0 < δ) (hδ₁ : δ < 1) (p : M × ℝ)
    (v : TangentSpace (I.prod 𝓘(ℝ)) p) :
    mfderiv (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ)) (Prod.map id (collarTime δ)) p v =
      mfderiv (I.prod (𝓡∂ 1)) (I.prod 𝓘(ℝ)) (Prod.map id Subtype.val : M × unitInterval → M × ℝ)
        (Prod.map id (collarTimeIcc hδ hδ₁) p)
        (mfderiv (I.prod 𝓘(ℝ)) (I.prod (𝓡∂ 1)) (Prod.map id (collarTimeIcc hδ hδ₁)) p v) :=
  congrArg (· v) (mfderiv_prodMap_id_collarTime hδ hδ₁ p)

omit [IsManifold I ∞ M] [FiniteDimensional ℝ E] in
private theorem isInvertible_mfderiv_prodMap_id_collarTimeIcc (hδ : 0 < δ) (hδ₁ : δ < 1)
    (p : M × ℝ) :
    (mfderiv (I.prod 𝓘(ℝ)) (I.prod (𝓡∂ 1))
      (Prod.map id (collarTimeIcc hδ hδ₁) : M × ℝ → M × unitInterval) p).IsInvertible := by
  -- The composite with the invertible differential of the inclusion is the differential of
  -- `(x, t) ↦ (x, collarTime δ t)`, invertible since `collarTime δ` has nonzero derivative.
  have h := isInvertible_mfderiv_prodMap_id (I := I)
    ((contDiff_collarTime (δ := δ)).differentiable (by simp) p.2)
    (deriv_collarTime_ne_zero hδ p.2)
  obtain ⟨e, he⟩ := isInvertible_mfderiv_prodMap_id_subtypeVal_Icc (I := I)
    (Prod.map id (collarTimeIcc hδ hδ₁) p)
  refine (ContinuousLinearMap.isInvertible_equiv_comp (e := e)).1 ?_
  rw [he, ← mfderiv_prodMap_id_collarTime hδ hδ₁]
  exact h

variable [T2Space M]
  {G : ContMDiffRiemannianMetric (I.prod 𝓘(ℝ)) ∞ (E × ℝ)
    (fun p : M × ℝ ↦ TangentSpace (I.prod 𝓘(ℝ)) p)}
  {Gc : ContMDiffRiemannianMetric (I.prod (𝓡∂ 1)) ∞ (E × EuclideanSpace ℝ (Fin 1))
    (fun p : M × unitInterval ↦ TangentSpace (I.prod (𝓡∂ 1)) p)}
  {g g₀ g₁ : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}

variable (Gc g₀ g₁) in
/-- A **collared concordance** from `g₀` to `g₁` is a metric of positive scalar curvature on the
manifold with boundary `M × [0, 1]` with product collars: for some `ε > 0` it is the product metric
`g₀ + dt²` where `t < ε` and the product metric `g₁ + dt²` where `t > 1 - ε`. Here `g + dt²` on
`M × [0, 1]` is the restriction of the cylinder metric. -/
structure IsCollaredConcordance : Prop where
  /-- A collared concordance has positive scalar curvature. -/
  hasPositiveScalarCurvature : Gc.HasPositiveScalarCurvature
  /-- A collared concordance is `g₀ + dt²` where `t < ε` and `g₁ + dt²` where `t > 1 - ε`. -/
  exists_collar : ∃ ε : ℝ, 0 < ε ∧
    (∀ p : M × unitInterval, (p.2 : ℝ) < ε →
      Gc.inner p = (g₀.cylinder.restrictIcc 0 1).inner p) ∧
    (∀ p : M × unitInterval, 1 - ε < (p.2 : ℝ) →
      Gc.inner p = (g₁.cylinder.restrictIcc 0 1).inner p)

/-- A metric on `M × [0, 1]` which is `g + dt²` on an open set has the scalar curvature of `g`
there. -/
private theorem scalarCurvature_eq_of_inner_eq_restrictIcc_cylinder {U : Set (M × unitInterval)}
    (hU : IsOpen U) (h : ∀ p ∈ U, Gc.inner p = (g.cylinder.restrictIcc 0 1).inner p)
    {p : M × unitInterval} (hp : p ∈ U) : Gc.scalarCurvature p = g.scalarCurvature p.1 := by
  rw [eqOn_scalarCurvature hU h hp, scalarCurvature_restrictIcc, scalarCurvature_cylinder]

omit [T2Space M] in
/-- Where `collarTime δ` is the identity and `Gc` is the product metric `g + dt²`, the pullback of
`Gc` along `(x, t) ↦ (x, collarTime δ t)` is `g + dt²`. -/
private theorem pullback_prodMap_id_collarTimeIcc_inner (hδ : 0 < δ) (hδ₁ : δ < 1) {p : M × ℝ}
    (hp : p.2 ∈ Ioo δ (1 - δ))
    (hg : Gc.inner (Prod.map id (collarTimeIcc hδ hδ₁) p) =
      (g.cylinder.restrictIcc 0 1).inner (Prod.map id (collarTimeIcc hδ hδ₁) p)) :
    (Gc.pullback (Prod.map id (collarTimeIcc hδ hδ₁))
      (contMDiff_prodMap_id_collarTimeIcc hδ hδ₁ (by simp))
      fun p ↦ (isInvertible_mfderiv_prodMap_id_collarTimeIcc hδ hδ₁ p).injective).inner p =
      g.cylinder.inner p := by
  have hθ : collarTime δ =ᶠ[𝓝 p.2] id := by
    filter_upwards [Ioo_mem_nhds hp.1 hp.2] with t ht
    exact collarTime_of_mem hδ (Ioo_subset_Icc_self ht)
  rw [← cylinder_reparamTime_inner g contDiff_collarTime (deriv_collarTime_ne_zero hδ)
    (by simp [hθ.deriv_eq])]
  ext v w
  rw [pullback_inner, hg, restrictIcc_inner, reparamTime_inner,
    mfderiv_prodMap_id_collarTime_apply hδ hδ₁, mfderiv_prodMap_id_collarTime_apply hδ hδ₁]
  -- Unfold the map, so that both sides are evaluated at `(p.1, collarTime δ p.2)`.
  simp only [Prod.map_fst, Prod.map_snd, id_eq, coe_collarTimeIcc]
  -- The sides now differ only in how the tangent fibres containing the vectors are written:
  -- the fibres over `Prod.map id (collarTimeIcc hδ hδ₁) p` and over `(p.1, collarTime δ p.2)` are
  -- both `E × ℝ`.
  rfl

/-- A metric on `M × ℝ` has positive scalar curvature if it is `g₀ + dt²` where `t < a`,
`g₁ + dt²` where `t > b`, and agrees with a metric of positive scalar curvature where `c < t < d`,
for some `c < a` and `b < d`. -/
private theorem hasPositiveScalarCurvature_of_inner_eq_cylinder
    {G B : ContMDiffRiemannianMetric (I.prod 𝓘(ℝ)) ∞ (E × ℝ)
      (fun p : M × ℝ ↦ TangentSpace (I.prod 𝓘(ℝ)) p)}
    (hg₀ : g₀.HasPositiveScalarCurvature) (hg₁ : g₁.HasPositiveScalarCurvature)
    (hB : B.HasPositiveScalarCurvature) {a b c d : ℝ} (hca : c < a) (hbd : b < d)
    (h₀ : ∀ p : M × ℝ, p.2 < a → G.inner p = g₀.cylinder.inner p)
    (h₁ : ∀ p : M × ℝ, b < p.2 → G.inner p = g₁.cylinder.inner p)
    (hGB : ∀ p : M × ℝ, c < p.2 → p.2 < d → G.inner p = B.inner p) :
    G.HasPositiveScalarCurvature := by
  refine (hasPositiveScalarCurvature_iff _).2 fun p ↦ ?_
  rcases lt_or_ge p.2 a with hp | hp
  · rw [eqOn_scalarCurvature (isOpen_lt continuous_snd continuous_const) h₀ hp,
      scalarCurvature_cylinder]
    exact (hasPositiveScalarCurvature_iff _).1 hg₀ p.1
  rcases lt_or_ge b p.2 with hp' | hp'
  · rw [eqOn_scalarCurvature (isOpen_lt continuous_const continuous_snd) h₁ hp',
      scalarCurvature_cylinder]
    exact (hasPositiveScalarCurvature_iff _).1 hg₁ p.1
  · have hW : IsOpen {q : M × ℝ | c < q.2 ∧ q.2 < d} :=
      (isOpen_lt continuous_const continuous_snd).inter (isOpen_lt continuous_snd continuous_const)
    rw [eqOn_scalarCurvature hW (fun q hq ↦ hGB q hq.1 hq.2) ⟨by linarith, by linarith⟩]
    exact (hasPositiveScalarCurvature_iff _).1 hB p

/-- The metric at the start of a collared concordance has positive scalar curvature. -/
theorem IsCollaredConcordance.hasPositiveScalarCurvature_left
    (h : IsCollaredConcordance Gc g₀ g₁) : g₀.HasPositiveScalarCurvature :=
  (hasPositiveScalarCurvature_iff _).2 fun x ↦ by
  obtain ⟨ε, hε, h₀, -⟩ := h.exists_collar
  rw [← scalarCurvature_eq_of_inner_eq_restrictIcc_cylinder (U := {p | (p.2 : ℝ) < ε})
    (isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const) h₀
    (p := (x, 0)) (by simpa using hε)]
  exact (hasPositiveScalarCurvature_iff _).1 h.hasPositiveScalarCurvature _

/-- The metric at the end of a collared concordance has positive scalar curvature. -/
theorem IsCollaredConcordance.hasPositiveScalarCurvature_right
    (h : IsCollaredConcordance Gc g₀ g₁) : g₁.HasPositiveScalarCurvature :=
  (hasPositiveScalarCurvature_iff _).2 fun x ↦ by
  obtain ⟨ε, hε, -, h₁⟩ := h.exists_collar
  rw [← scalarCurvature_eq_of_inner_eq_restrictIcc_cylinder (U := {p | 1 - ε < (p.2 : ℝ)})
    (isOpen_lt continuous_const (continuous_subtype_val.comp continuous_snd)) h₁
    (p := (x, 1)) (by simpa using hε)]
  exact (hasPositiveScalarCurvature_iff _).1 h.hasPositiveScalarCurvature _

/-- The product metric `g + dt²` on `M × [0, 1]` of a metric of positive scalar curvature is a
collared concordance from `g` to itself. -/
theorem HasPositiveScalarCurvature.isCollaredConcordance_restrictIcc_cylinder
    (h : g.HasPositiveScalarCurvature) :
    IsCollaredConcordance (g.cylinder.restrictIcc 0 1) g g :=
  ⟨((hasPositiveScalarCurvature_cylinder_iff g).2 h).restrictIcc,
    1, one_pos, fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩

/-- **Concordances give collared concordances.** A concordance from `g₀` to `g₁` gives a collared
concordance from `g₀` to `g₁` on `M × [0, 1]`. -/
theorem IsConcordance.exists_isCollaredConcordance (h : IsConcordance G g₀ g₁) :
    ∃ Gc, IsCollaredConcordance Gc g₀ g₁ := by
  have hd (t : ℝ) : |deriv (fun t : ℝ ↦ t - 1) t| = 1 := by simp
  -- `G` translated to be `g₀ + dt²` where `t ≤ 1` and `g₁ + dt²` where `t ≥ 2`.
  let G' := G.reparamTime (φ := fun t ↦ t - 1) (contDiff_id.sub contDiff_const) (fun t ↦ by simp)
  have hG'₀ (q : M × ℝ) (hq : q.2 ≤ 1) : G'.inner q = g₀.cylinder.inner q :=
    reparamTime_inner_eq_cylinder_inner _ _ (h.inner_of_nonpos _ (by simpa using hq)) (hd q.2)
  have hG'₁ (q : M × ℝ) (hq : 2 ≤ q.2) : G'.inner q = g₁.cylinder.inner q :=
    reparamTime_inner_eq_cylinder_inner _ _ (h.inner_of_one_le _ (by simp; linarith)) (hd q.2)
  -- `stretch` maps `[0, 1]` onto `[0, 3]`, as the identity near `0` and the translation by `2`
  -- near `1`.
  refine ⟨(G'.reparamTime (contDiff_stretch 2)
      (deriv_stretch_ne_zero zero_le_two)).restrictIcc 0 1,
    ((h.hasPositiveScalarCurvature.reparamTime _ _).reparamTime _ _).restrictIcc,
    1 / 3, by norm_num, fun p hp ↦ restrictIcc_inner_congr ?_,
    fun p hp ↦ restrictIcc_inner_congr ?_⟩
  · have hψ := stretch_eventuallyEq_of_lt 2 hp
    refine reparamTime_inner_eq_cylinder_inner _ _ ?_ (by simp [hψ.deriv_eq])
    rw [hψ.eq_of_nhds]
    exact hG'₀ _ p.2.2.2
  · have hp' : 2 / 3 < (p.2 : ℝ) := by linarith
    have hψ := stretch_eventuallyEq_of_gt 2 hp'
    refine reparamTime_inner_eq_cylinder_inner _ _ ?_ (by simp [hψ.deriv_eq])
    rw [hψ.eq_of_nhds]
    exact hG'₁ _ (by simp [p.2.2.1])

/-- **Collared concordances give concordances.** If there is a collared concordance from `g₀` to
`g₁`, then `g₀` and `g₁` are concordant. -/
theorem IsCollaredConcordance.concordant (h : IsCollaredConcordance Gc g₀ g₁) :
    Concordant g₀ g₁ := by
  obtain ⟨ε₀, hε₀, h₀, h₁⟩ := h.exists_collar
  -- Shrink the collar to `ε ≤ 1 / 3`, and set `δ = ε / 2`.
  obtain ⟨ε, hε, hεε₀, hε₃⟩ : ∃ ε : ℝ, 0 < ε ∧ ε ≤ ε₀ ∧ ε ≤ 1 / 3 :=
    ⟨min ε₀ (1 / 3), by positivity, min_le_left _ _, min_le_right _ _⟩
  have hδ : 0 < ε / 2 := by positivity
  have hδ₁ : ε / 2 < 1 := by linarith
  -- The middle piece: `Gc` pulled back to `M × ℝ` along `(x, t) ↦ (x, collarTime (ε / 2) t)`.
  let Θ : M × ℝ → M × unitInterval := Prod.map id (collarTimeIcc hδ hδ₁)
  have hΘ (p : M × ℝ) : ((Θ p).2 : ℝ) = collarTime (ε / 2) p.2 := by
    simp only [Θ, Prod.map_snd, coe_collarTimeIcc]
  let B := Gc.pullback Θ (contMDiff_prodMap_id_collarTimeIcc hδ hδ₁ (by simp))
    fun p ↦ (isInvertible_mfderiv_prodMap_id_collarTimeIcc hδ hδ₁ p).injective
  have hB : B.HasPositiveScalarCurvature :=
    h.hasPositiveScalarCurvature.pullback_of_isInvertible _
      (isInvertible_mfderiv_prodMap_id_collarTimeIcc hδ hδ₁)
  have hB₀ (p : M × ℝ) (hp : p.2 ∈ Ioo (ε / 2) ε) : B.inner p = g₀.cylinder.inner p :=
    pullback_prodMap_id_collarTimeIcc_inner hδ hδ₁ ⟨hp.1, by linarith [hp.2]⟩ (h₀ _ (by
      rw [hΘ, collarTime_of_mem hδ ⟨hp.1.le, by linarith [hp.2]⟩]
      linarith [hp.2]))
  have hB₁ (p : M × ℝ) (hp : p.2 ∈ Ioo (1 - ε) (1 - ε / 2)) : B.inner p = g₁.cylinder.inner p :=
    pullback_prodMap_id_collarTimeIcc_inner hδ hδ₁ ⟨by linarith [hp.1], hp.2⟩ (h₁ _ (by
      rw [hΘ, collarTime_of_mem hδ ⟨by linarith [hp.1], hp.2.le⟩]
      linarith [hp.1]))
  -- Glue `g₀ + dt²` on `t < ε`, `B` on `ε / 2 < t < 1 - ε / 2` and `g₁ + dt²` on `t > 1 - ε`.
  have hU₀ : IsOpen {p : M × ℝ | p.2 < ε} := isOpen_lt continuous_snd continuous_const
  have hV₀ : IsOpen {p : M × ℝ | ε / 2 < p.2} := isOpen_lt continuous_const continuous_snd
  have hU₁ : IsOpen {p : M × ℝ | p.2 < 1 - ε / 2} := isOpen_lt continuous_snd continuous_const
  have hV₁ : IsOpen {p : M × ℝ | 1 - ε < p.2} := isOpen_lt continuous_const continuous_snd
  let G₀ := g₀.cylinder.piecewise B hU₀ hV₀
    (eq_univ_of_forall fun p ↦ (lt_or_ge p.2 ε).imp id fun hp ↦ by simp; linarith)
    fun p hp ↦ (hB₀ p ⟨hp.2, hp.1⟩).symm
  have hG₀B (p : M × ℝ) (hp : ε / 2 < p.2) : G₀.inner p = B.inner p :=
    piecewise_inner_of_mem_right (V := {p : M × ℝ | ε / 2 < p.2}) hp
  have hG₀ (p : M × ℝ) (hp : p.2 < ε) : G₀.inner p = g₀.cylinder.inner p :=
    piecewise_inner_of_mem_left (U := {p : M × ℝ | p.2 < ε}) hp
  let G₁ := G₀.piecewise g₁.cylinder hU₁ hV₁
    (eq_univ_of_forall fun p ↦ (lt_or_ge p.2 (1 - ε / 2)).imp id fun hp ↦ by simp; linarith)
    fun p hp ↦ (hG₀B p (by linarith [hp.2.out])).trans (hB₁ p ⟨hp.2, hp.1⟩)
  have hG₁₀ (p : M × ℝ) (hp : p.2 < 1 - ε / 2) : G₁.inner p = G₀.inner p :=
    piecewise_inner_of_mem_left (U := {p : M × ℝ | p.2 < 1 - ε / 2}) hp
  have hG₁ (p : M × ℝ) (hp : 1 - ε < p.2) : G₁.inner p = g₁.cylinder.inner p :=
    piecewise_inner_of_mem_right (V := {p : M × ℝ | 1 - ε < p.2}) hp
  refine ⟨G₁, hasPositiveScalarCurvature_of_inner_eq_cylinder h.hasPositiveScalarCurvature_left
    h.hasPositiveScalarCurvature_right hB (by linarith : ε / 2 < ε)
    (by linarith : 1 - ε < 1 - ε / 2) (fun p hp ↦ (hG₁₀ p (by linarith)).trans (hG₀ p hp)) hG₁
    (fun p hp hp' ↦ (hG₁₀ p hp').trans (hG₀B p hp)),
    fun p hp ↦ (hG₁₀ p (by linarith)).trans (hG₀ p (by linarith)),
    fun p hp ↦ hG₁ p (by linarith)⟩

/-- Two metrics are concordant exactly when there is a collared concordance from one to the
other. -/
theorem concordant_iff_exists_isCollaredConcordance :
    Concordant g₀ g₁ ↔ ∃ Gc, IsCollaredConcordance Gc g₀ g₁ :=
  ⟨fun ⟨_, hG⟩ ↦ hG.exists_isCollaredConcordance, fun ⟨_, hGc⟩ ↦ hGc.concordant⟩

end Collar

section Naturality

/-! ### Pullback and rescaling of concordances -/

variable [FiniteDimensional ℝ E] [T2Space M]
  {G : ContMDiffRiemannianMetric (I.prod 𝓘(ℝ)) ∞ (E × ℝ)
    (fun p : M × ℝ ↦ TangentSpace (I.prod 𝓘(ℝ)) p)}
  {g g₀ g₁ : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}

section Pullback

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [T2Space M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
  {f : M' → M}

omit [FiniteDimensional ℝ E] [T2Space M] [T2Space M'] in
/-- The cylinder metric `g + dt²` pulled back along `(x, t) ↦ (f x, t)` is the cylinder metric
`f^* g + dt²` of the pullback of `g`. -/
theorem pullback_prodMap_cylinder
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hf : ContMDiff I' I (∞ + 1) f) (hinj : ∀ x, Function.Injective (mfderiv I' I f x))
    (hinj' : ∀ p, Function.Injective
      (mfderiv (I'.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ)) (Prod.map f (id : ℝ → ℝ)) p)) :
    g.cylinder.pullback (Prod.map f id) (hf.prodMap contMDiff_id) hinj' =
      (g.pullback f hf hinj).cylinder := by
  ext p v w
  -- The differential of `(x, t) ↦ (f x, t)` acts componentwise.
  have hd (u : TangentSpace (I'.prod 𝓘(ℝ)) p) :
      tangentSpaceProdEquiv (Prod.map f id p)
          (mfderiv (I'.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ)) (Prod.map f id) p u) =
        (mfderiv I' I f p.1 (tangentSpaceProdEquiv p u).1, (tangentSpaceProdEquiv p u).2) := by
    have := mfderiv_prodMap_apply (hf.mdifferentiableAt (by simp)) mdifferentiableAt_id
      (tangentSpaceProdEquiv p u)
    rw [ContinuousLinearEquiv.symm_apply_apply, mfderiv_id, ContinuousLinearMap.id_apply] at this
    rw [this]
    exact (tangentSpaceProdEquiv (f p.1, p.2)).apply_symm_apply _
  rw [pullback_inner, cylinder_inner, cylinder_inner, pullback_inner, hd, hd]
  -- The sides differ only in writing the point `(f x, t)` as `Prod.map f id (x, t)`.
  rfl

/-- Pulling a concordance from `g₀` to `g₁` back along `(x, t) ↦ (f x, t)`, for a smooth map `f`
whose differential is invertible at every point, gives a concordance from `f^* g₀` to `f^* g₁`. -/
theorem IsConcordance.pullback_prodMap (h : IsConcordance G g₀ g₁) (hf : ContMDiff I' I (∞ + 1) f)
    (hinv : ∀ x, (mfderiv I' I f x).IsInvertible) :
    IsConcordance (G.pullback (Prod.map f id) (hf.prodMap contMDiff_id) fun p ↦
        (isInvertible_mfderiv_prodMap_id_right (hf.mdifferentiableAt (by simp))
          (hinv p.1)).injective)
      (g₀.pullback f hf fun x ↦ (hinv x).injective)
      (g₁.pullback f hf fun x ↦ (hinv x).injective) := by
  have hinv' (p : M' × ℝ) :=
    isInvertible_mfderiv_prodMap_id_right (J := 𝓘(ℝ)) (hf.mdifferentiableAt (by simp)) (hinv p.1)
  refine ⟨h.hasPositiveScalarCurvature.pullback_of_isInvertible _ hinv', fun p hp ↦ ?_,
    fun p hp ↦ ?_⟩
  · rw [← pullback_prodMap_cylinder g₀ hf _
      fun p ↦ (hinv' p).injective]
    ext v w
    rw [pullback_inner, pullback_inner, h.inner_of_nonpos _ hp]
  · rw [← pullback_prodMap_cylinder g₁ hf _
      fun p ↦ (hinv' p).injective]
    ext v w
    rw [pullback_inner, pullback_inner, h.inner_of_one_le _ hp]

/-- **Naturality of concordance.** If `g₀` and `g₁` are concordant, then so are their pullbacks
along a smooth map whose differential is invertible at every point, such as a diffeomorphism or a
covering map. -/
theorem Concordant.pullback (h : Concordant g₀ g₁) (hf : ContMDiff I' I (∞ + 1) f)
    (hinv : ∀ x, (mfderiv I' I f x).IsInvertible) :
    Concordant (g₀.pullback f hf fun x ↦ (hinv x).injective)
      (g₁.pullback f hf fun x ↦ (hinv x).injective) :=
  let ⟨_, hG⟩ := h
  (hG.pullback_prodMap hf hinv).concordant

/-- Two metrics are concordant exactly when their pullbacks along a diffeomorphism are. -/
@[simp]
theorem concordant_pullback_iff (Φ : M' ≃ₘ^∞⟮I', I⟯ M) (hf : ContMDiff I' I (∞ + 1) Φ)
    (hinj : ∀ x, Function.Injective (mfderiv I' I Φ x)) :
    Concordant (g₀.pullback Φ hf hinj) (g₁.pullback Φ hf hinj) ↔ Concordant g₀ g₁ := by
  have hinv (x : M') : (mfderiv I' I Φ x).IsInvertible := Φ.isInvertible_mfderiv (by simp)
  refine ⟨fun h ↦ ?_, fun h ↦ h.pullback hf hinv⟩
  -- Pull back along `Φ⁻¹`; pulling back along `Φ` and then along `Φ⁻¹` is the identity.
  have key (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) :
      (g.pullback Φ hf hinj).pullback Φ.symm (by rw [ENat.coe_top_add_one]; exact Φ.symm.contMDiff)
        (fun y ↦ (Φ.symm.isInvertible_mfderiv (by simp) (x := y)).injective) = g := by
    have hΦ : (Φ ∘ Φ.symm : M → M) = id := funext Φ.apply_symm_apply
    rw [← pullback_comp]
    simp only [hΦ, pullback_id]
  have := h.pullback (by rw [ENat.coe_top_add_one]; exact Φ.symm.contMDiff) fun y ↦
    Φ.symm.isInvertible_mfderiv (by simp)
  rwa [key, key] at this

end Pullback

section Rescale

variable {c : ℝ}

omit [T2Space M] in
/-- The cylinder metric `c g + dt²` of a rescaled metric is the rescaled cylinder metric
`c (g + dt²)` reparametrised by `t ↦ t / √c`. -/
theorem reparamTime_rescale_cylinder
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (hc : 0 < c) :
    (g.cylinder.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).reparamTime
        (φ := fun t ↦ t / √c) (contDiff_id.div_const _)
        (fun t ↦ by simp [Real.sqrt_ne_zero'.2 hc]) =
      (g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).cylinder := by
  have hd (t : ℝ) : DifferentiableAt ℝ (fun t ↦ t / √c) t := differentiableAt_id.div_const _
  ext p v w
  rw [reparamTime_inner, rescale_inner, cylinder_inner, cylinder_inner, rescale_inner,
    tangentSpaceProdEquiv_mfderiv_prodMap_id (hd p.2),
    tangentSpaceProdEquiv_mfderiv_prodMap_id (hd p.2)]
  simp only [ContinuousLinearEquiv.apply_symm_apply, deriv_div_const, deriv_id'']
  field_simp
  rw [Real.sq_sqrt hc.le]
  ring

/-- If `g₀` and `g₁` are concordant, then so are `c g₀` and `c g₁` for every constant `c > 0`. -/
theorem Concordant.rescale_const (h : Concordant g₀ g₁) (hc : 0 < c) :
    Concordant (g₀.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc)
      (g₁.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc) := by
  obtain ⟨G, hG⟩ := h
  have hsc : 0 < √c := Real.sqrt_pos.2 hc
  -- `c G` agrees with `c (gᵢ + dt²)` wherever `G` agrees with `gᵢ + dt²`.
  have key {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} {p : M × ℝ}
      (hp : G.inner (p.1, p.2 / √c) = g.cylinder.inner (p.1, p.2 / √c)) :
      ((G.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).reparamTime (φ := fun t ↦ t / √c)
          (contDiff_id.div_const _) (fun t ↦ by simp [Real.sqrt_ne_zero'.2 hc])).inner p =
        (g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).cylinder.inner p := by
    rw [← reparamTime_rescale_cylinder g hc]
    refine reparamTime_inner_congr _ _ ?_
    ext v w
    rw [rescale_inner, rescale_inner, hp]
  refine concordant_of_inner_eq_cylinder (a := 0) (b := √c)
    ((hG.hasPositiveScalarCurvature.rescale_const hc).reparamTime _ _)
    (fun p hp ↦ key (hG.inner_of_nonpos _ (div_nonpos_of_nonpos_of_nonneg hp hsc.le)))
    (fun p hp ↦ key (hG.inner_of_one_le _ ((one_le_div hsc).2 hp)))

/-- Rescaling by a positive constant preserves and reflects concordance. -/
@[simp]
theorem concordant_rescale_const_iff (hc : 0 < c) :
    Concordant (g₀.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc)
        (g₁.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc) ↔ Concordant g₀ g₁ := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.rescale_const hc⟩
  simpa [inv_mul_cancel₀ hc.ne'] using h.rescale_const (inv_pos.2 hc)

end Rescale

section Prod

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H'' : Type*} [TopologicalSpace H''] {J : ModelWithCorners ℝ F H''}
  {N : Type*} [TopologicalSpace N] [T2Space N] [ChartedSpace H'' N] [IsManifold J ∞ N]

omit [T2Space M] [T2Space N] in
/-- Where `G` is `g + dt²`, the pullback of `G × g₂` along `((x, y), t) ↦ ((x, t), y)` is the
cylinder metric `g × g₂ + dt²`. -/
private theorem pullback_prod_right_comm_inner {g₂ : ContMDiffRiemannianMetric J ∞ F
      (fun y : N ↦ TangentSpace J y)} {q : (M × N) × ℝ}
    (hG : G.inner (q.1.1, q.2) = g.cylinder.inner (q.1.1, q.2)) :
    ((G.prodTangentSpace g₂).pullback (fun q : (M × N) × ℝ ↦ ((q.1.1, q.2), q.1.2))
      contMDiff_prod_right_comm
      fun q ↦ (isInvertible_mfderiv_prod_right_comm q).injective).inner q =
      (g.prodTangentSpace g₂).cylinder.inner q := by
  ext v w
  rw [pullback_inner, prodTangentSpace_inner, hG, cylinder_inner, cylinder_inner,
    prodTangentSpace_inner]
  simp only [tangentSpaceProdEquiv_apply]
  rw [tangentSpaceProdEquiv_apply, tangentSpaceProdEquiv_apply, mfderiv_prod_right_comm_apply,
    mfderiv_prod_right_comm_apply]
  exact add_right_comm _ _ _

/-- **Products of concordances.** If `g₀` and `g₁` are concordant and `g₂` has nonnegative scalar
curvature, then `g₀ × g₂` and `g₁ × g₂` are concordant. -/
theorem Concordant.prodTangentSpace_of_nonneg (h : Concordant g₀ g₁)
    {g₂ : ContMDiffRiemannianMetric J ∞ F (fun y : N ↦ TangentSpace J y)}
    (h₂ : ∀ y, 0 ≤ g₂.scalarCurvature y) :
    Concordant (g₀.prodTangentSpace g₂) (g₁.prodTangentSpace g₂) :=
  let ⟨_, hG⟩ := h
  ⟨_, (hG.hasPositiveScalarCurvature.prodTangentSpace_of_nonneg h₂).pullback_of_isInvertible
      contMDiff_prod_right_comm isInvertible_mfderiv_prod_right_comm,
    fun _ hq ↦ pullback_prod_right_comm_inner (hG.inner_of_nonpos _ hq),
    fun _ hq ↦ pullback_prod_right_comm_inner (hG.inner_of_one_le _ hq)⟩

end Prod

end Naturality

end Bundle.ContMDiffRiemannianMetric
