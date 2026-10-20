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
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

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

## Main definitions

* `Bundle.ContMDiffRiemannianMetric.cylinder`: the cylinder metric `g + dt²` on `M × ℝ`.
* `Bundle.ContMDiffRiemannianMetric.reparamTime`: the pullback of a metric on `M × ℝ` along
  `(x, t) ↦ (x, φ t)`.
* `Bundle.ContMDiffRiemannianMetric.IsConcordance`: a concordance from `g₀` to `g₁`.
* `Bundle.ContMDiffRiemannianMetric.Concordant`: `g₀` and `g₁` are concordant, characterised by
  `Bundle.ContMDiffRiemannianMetric.concordant_iff`.

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

## References

* M. Gromov, H. B. Lawson, *The classification of simply connected manifolds of positive
  scalar curvature*, Ann. of Math. 111 (1980), 423–434.
* S. Stolz, *Positive scalar curvature—constructions and obstructions*, arXiv:2202.05904, for
  concordance and isotopy of metrics of positive scalar curvature.
-/

public section

open Bundle Set Topology Filter
open TauCeti.Manifold (tangentSpaceProdEquiv tangentSpaceProdEquiv_mfderiv_prodMap_id
  isInvertible_mfderiv_prodMap_id)
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

/-- The smooth increasing map `t ↦ t + 2 s(3t - 1)` of `ℝ`, with `s` the smooth transition from
`0` to `1` on `[0, 1]`. It is the identity on `t ≤ 1/3` and the translation by `2` on `t ≥ 2/3`,
so it compresses the window `[0, 3]` of a glued pair of concordances into `[0, 1]`. -/
private def stretch (t : ℝ) : ℝ :=
  t + 2 * Real.smoothTransition (3 * t - 1)

private theorem contDiff_stretch : ContDiff ℝ ∞ stretch :=
  contDiff_id.add (contDiff_const.mul
    ((Real.smoothTransition.contDiff (n := ⊤)).comp (by fun_prop)))

private theorem hasDerivAt_stretch (t : ℝ) :
    HasDerivAt stretch (1 + 2 * (deriv Real.smoothTransition (3 * t - 1) * 3)) t := by
  have h : HasDerivAt (fun t : ℝ ↦ 3 * t - 1) 3 t := by
    simpa using ((hasDerivAt_id t).const_mul 3).sub_const 1
  exact (hasDerivAt_id t).add
    ((Real.smoothTransition.contDiffAt (n := 1)).differentiableAt one_ne_zero
      |>.hasDerivAt.comp t h |>.const_mul 2)

private theorem deriv_stretch_ne_zero (t : ℝ) : deriv stretch t ≠ 0 := by
  rw [(hasDerivAt_stretch t).deriv]
  have := Real.smoothTransition.monotone.deriv_nonneg (x := 3 * t - 1)
  positivity

private theorem stretch_eventuallyEq_of_lt {t : ℝ} (ht : t < 1 / 3) : stretch =ᶠ[𝓝 t] id := by
  filter_upwards [eventually_lt_nhds ht] with s hs
  simp [stretch, Real.smoothTransition.zero_of_nonpos (by linarith : 3 * s - 1 ≤ 0)]

private theorem stretch_eventuallyEq_of_gt {t : ℝ} (ht : 2 / 3 < t) :
    stretch =ᶠ[𝓝 t] (· + 2) := by
  filter_upwards [eventually_gt_nhds ht] with s hs
  simp [stretch, Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 3 * s - 1)]

/-- A metric of positive scalar curvature on `M × ℝ` which is `g₀ + dt²` where `t ≤ 0` and
`g₂ + dt²` where `t ≥ 3` gives a concordance from `g₀` to `g₂`, after compressing the window
`[0, 3]` into `[0, 1]` by `stretch`. -/
private theorem concordant_of_window_three (hG : G.HasPositiveScalarCurvature)
    (h₀ : ∀ p : M × ℝ, p.2 ≤ 0 → G.inner p = g₀.cylinder.inner p)
    (h₃ : ∀ p : M × ℝ, 3 ≤ p.2 → G.inner p = g₂.cylinder.inner p) : Concordant g₀ g₂ := by
  refine ⟨G.reparamTime contDiff_stretch deriv_stretch_ne_zero,
    hG.reparamTime _ _, fun p hp ↦ ?_, fun p hp ↦ ?_⟩
  · -- Near `t ≤ 0`, `stretch` is the identity.
    have hψ := stretch_eventuallyEq_of_lt (show p.2 < 1 / 3 by linarith)
    refine reparamTime_inner_eq_cylinder_inner _ _ ?_ (by simp [hψ.deriv_eq])
    rw [hψ.eq_of_nhds]
    exact h₀ p hp
  · -- Near `t ≥ 1`, `stretch` is the translation by `2`.
    have hψ := stretch_eventuallyEq_of_gt (show 2 / 3 < p.2 by linarith)
    refine reparamTime_inner_eq_cylinder_inner _ _ ?_ (by simp [hψ.deriv_eq])
    rw [hψ.eq_of_nhds]
    exact h₃ _ (by simp; linarith)

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
  refine concordant_of_window_three (G := G₁.piecewise G₂' hU hV hUV fun p hp ↦ by
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

end Bundle.ContMDiffRiemannianMetric
