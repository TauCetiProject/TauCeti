/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.Algebra.SMul
public import TauCeti.Geometry.Manifold.Riemannian.Pullback.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Mean
public import TauCeti.Geometry.Manifold.ContMDiff.ParametricIntegral
public import TauCeti.Geometry.Manifold.Riemannian.Section
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Measure.Haar.Basic

/-!
# Invariant Riemannian metrics for finite and compact group actions

Average the pullbacks of a Riemannian metric over a group acting by diffeomorphisms. The result is
a metric preserved by every element of the group, including elements acting trivially. Its
regularity is `C^n` when the metric is `C^n` and the action is `C^(n+1)`. In particular a smooth
action of a finite group, or of a compact Lie group, admits a smooth invariant metric whenever the
manifold admits a smooth metric.

For a finite group, `TauCeti.averageRiemannianMetric` is the arithmetic mean of the pulled-back
metrics; it combines `TauCeti.meanRiemannianMetric` with
`Bundle.ContMDiffRiemannianMetric.pullback`. Such metrics give invariant orthonormal frame
bundles on finite quotient charts.

For a compact manifold `G` acting jointly `C^(n+1)` on a boundaryless manifold `M`, and a
probability measure `μ` on `G`, `TauCeti.measureAverageRiemannianMetric J μ g` is the metric

`⟨v, w⟩_x = ∫ g_{a • x}(d(a •)_x v, d(a •)_x w) dμ(a)`.

It is positive definite because each `d(a •)_x` is invertible. It is `C^n` because, read in a
bundle chart, the pulled-back forms depend `C^n` on the point and the group element
(`Bundle.contMDiffAt_trivializationAt_bilinearForm_pullback`), so their average is `C^n` by
differentiation under the integral over the compact parameter manifold `G`
(`TauCeti.contMDiffAt_parametric_integral`). When `μ` is right-invariant, for instance the image
under inversion of the normalized Haar measure, every element of `G` acts by an isometry of the
averaged metric, and an already invariant metric is unchanged by averaging. A compact Lie group
acting smoothly by symplectomorphisms thus has an invariant metric, the input from which an
invariant compatible almost complex structure is obtained by polar normalization.

## Main definitions

* `TauCeti.averageRiemannianMetric`: the average of a metric over a finite group action.
* `TauCeti.measureAverageRiemannianMetric`: the average of a metric over a compact group action
  against a probability measure on the group.

## Main results

* `TauCeti.averageRiemannianMetric_inner_mfderiv`,
  `TauCeti.measureAverageRiemannianMetric_inner_mfderiv`: the group acts by isometries of the
  averaged metric.
* `TauCeti.averageRiemannianMetric_eq_self_iff`,
  `TauCeti.measureAverageRiemannianMetric_eq_self_iff`: averaging fixes exactly the invariant
  metrics.
* `TauCeti.exists_contMDiffRiemannianMetric_inner_mfderiv`: a compact topological group acting
  `C^(n+1)` on a boundaryless manifold with a `C^n` metric preserves some `C^n` metric.

## References

* A. Adem, J. Leida and Y. Ruan, *Orbifolds and Stringy Topology*, Cambridge University Press
  (2007), Chapter 1, for invariant metrics on finite quotient charts.
* G. E. Bredon, *Introduction to Compact Transformation Groups*, Academic Press (1972),
  Chapter VI, for invariant Riemannian metrics of smooth compact group actions.
-/

public noncomputable section

open Bundle Manifold
open scoped Manifold ContDiff

namespace TauCeti

/-- Pulling a metric back along `a • ·` and then along `b • ·` is pulling it back along
`(b * a) • ·`. -/
private theorem inner_mfderiv_smul_mfderiv_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] {n : ℕ∞ω}
    {G : Type*} [Monoid G] [MulAction G M]
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) {a b : G} {x : M}
    (ha : MDifferentiableAt I I (a • ·) x) (hb : MDifferentiableAt I I (b • ·) (a • x))
    (v w : TangentSpace I x) :
    g.inner (b • a • x) (mfderiv I I (b • ·) (a • x) (mfderiv I I (a • ·) x v))
        (mfderiv I I (b • ·) (a • x) (mfderiv I I (a • ·) x w)) =
      g.inner ((b * a) • x) (mfderiv I I ((b * a) • ·) x v) (mfderiv I I ((b * a) • ·) x w) := by
  have hcomp : (fun y : M ↦ b • y) ∘ (a • ·) = ((b * a) • ·) :=
    funext fun y ↦ (mul_smul b a y).symm
  have hd := mfderiv_comp x hb ha
  -- Change the map, its value and both tangent vectors together, so that all fibre indices agree.
  have h := congrArg (fun f : M → M ↦
    g.inner (f x) (mfderiv I I f x v) (mfderiv I I f x w)) hcomp
  simp only [hd, ContinuousLinearMap.comp_apply, Function.comp_apply] at h
  convert! h using 1

section Finite

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {n : ℕ∞ω} (G : Type*) [Group G] [Fintype G] [MulAction G M]
  [ContMDiffConstSMul I (n + 1) G M]

/-- The invariant metric obtained by averaging all translates of a metric over a finite group.
The full group is used, without dividing out the ineffective kernel of the action. -/
def averageRiemannianMetric (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) :
    ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _) :=
  meanRiemannianMetric fun a : G ↦
    g.pullback (Diffeomorph.constSmul I (n + 1) a)
      (Diffeomorph.constSmul I (n + 1) a).contMDiff
      (fun _ ↦ ((Diffeomorph.constSmul I (n + 1) a).isInvertible_mfderiv (by simp)).injective)

/-- The averaged inner product is the normalized sum of the pulled-back inner products. -/
@[simp]
theorem averageRiemannianMetric_inner
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (x : M) (v w : TangentSpace I x) :
    (averageRiemannianMetric G g).inner x v w = (Fintype.card G : ℝ)⁻¹ *
      ∑ a : G, g.inner (a • x) (mfderiv I I (a • ·) x v) (mfderiv I I (a • ·) x w) := by
  have hcoe (a : G) : ⇑(Diffeomorph.constSmul I (n + 1) a : M ≃ₘ^ (n + 1)⟮I, I⟯ M) =
      (a • ·) := funext (Diffeomorph.constSmul_apply a)
  simp only [averageRiemannianMetric, meanRiemannianMetric_inner,
    ContMDiffRiemannianMetric.pullback_inner, hcoe]

/-- Every action map preserves the averaged metric. -/
theorem averageRiemannianMetric_inner_mfderiv
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (a : G) (x : M) (v w : TangentSpace I x) :
    (averageRiemannianMetric G g).inner (a • x)
        (mfderiv I I (a • ·) x v) (mfderiv I I (a • ·) x w) =
      (averageRiemannianMetric G g).inner x v w := by
  simp only [averageRiemannianMetric_inner]
  congr 1
  exact Fintype.sum_equiv (Equiv.mulRight a) _ _ fun b ↦ inner_mfderiv_smul_mfderiv_smul g
    ((contMDiff_const_smul a : ContMDiff I I (n + 1) _).mdifferentiableAt (by simp))
    ((contMDiff_const_smul b : ContMDiff I I (n + 1) _).mdifferentiableAt (by simp)) v w

/-- A metric is fixed by averaging exactly when all action maps preserve it. -/
theorem averageRiemannianMetric_eq_self_iff
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) :
    averageRiemannianMetric G g = g ↔
      ∀ (a : G) (x : M) (v w : TangentSpace I x),
        g.inner (a • x) (mfderiv I I (a • ·) x v) (mfderiv I I (a • ·) x w) = g.inner x v w := by
  constructor
  · intro h
    rw [← h]
    exact averageRiemannianMetric_inner_mfderiv G g
  · intro hg
    ext x v w
    simp [hg, Fintype.card_ne_zero]

/-- Averaging a metric twice gives the same invariant metric. -/
@[simp]
theorem averageRiemannianMetric_idempotent
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) :
    averageRiemannianMetric G (averageRiemannianMetric G g) = averageRiemannianMetric G g :=
  (averageRiemannianMetric_eq_self_iff G _).mpr (averageRiemannianMetric_inner_mfderiv G g)

end Finite

section Compact

open MeasureTheory Function Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

-- Cache the canonical operator-space instances: instance search for the normed and
-- measure-theoretic structure on the nested operator space `E →L[ℝ] E →L[ℝ] ℝ` otherwise
-- times out.
private local instance : NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
private local instance : NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace

variable {G : Type*} [Group G] [MulAction G M] {n : ℕ∞}

/-- The pullback `(v, w) ↦ g_{a x}(d(a •)_x v, d(a •)_x w)` of a metric by the action of `a`,
read as a bilinear form on the model vector space. -/
private def pullbackSMulInner (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (a : G) (x : M) : E →L[ℝ] E →L[ℝ] ℝ :=
  @id (E →L[ℝ] E →L[ℝ] ℝ) ((ContinuousLinearMap.precomp ℝ (mfderiv I I (a • ·) x)).comp
    ((g.inner (a • x)).comp (mfderiv I I (a • ·) x)))

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] (J : ModelWithCorners ℝ E' H')
  [TopologicalSpace G] [ChartedSpace H' G] [IsManifold J 1 G] [ContMDiffSMul J I (n + 1) G M]

include J

/-- In the trivialization at `x₀`, the pullbacks of a metric by the action are jointly `C^n` in
the point and the group element. -/
private theorem contMDiffAt_trivializationAt_pullbackSMul
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (x₀ : M) (a₀ : G) :
    ContMDiffAt (I.prod J) 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) n
      (fun p : M × G ↦ (trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
        (fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) x₀
        ⟨p.1, (ContinuousLinearMap.precomp ℝ (mfderiv I I (p.2 • ·) p.1)).comp
          ((g.inner (p.2 • p.1)).comp (mfderiv I I (p.2 • ·) p.1))⟩).2) (x₀, a₀) := by
  have hsmul : ContMDiff (I.prod J) I (n + 1) fun p : M × G ↦ p.2 • p.1 :=
    (contMDiff_smul (I := J) (I' := I)).comp (contMDiff_snd.prodMk contMDiff_fst)
  have hsmul' : ContMDiff ((I.prod J).prod I) I (n + 1)
      (Function.uncurry fun (p : M × G) (y : M) ↦ p.2 • y) :=
    (contMDiff_smul (I := J) (I' := I)).comp
      ((contMDiff_snd.comp contMDiff_fst).prodMk contMDiff_snd)
  have hL := ContMDiffAt.mfderiv (I := I) (I' := I) (m := n) (n := n + 1) (x₀ := (x₀, a₀))
    (fun (p : M × G) (y : M) ↦ p.2 • y) Prod.fst hsmul'.contMDiffAt
    (contMDiffAt_fst (I := I) (J := J)) le_rfl
  exact Bundle.contMDiffAt_trivializationAt_bilinearForm_pullback (p₀ := (x₀, a₀))
    (g := Prod.fst) (f := fun p : M × G ↦ p.2 • p.1) (b := fun p ↦ g.inner (p.2 • p.1))
    (L := fun p ↦ mfderiv I I (p.2 • ·) p.1) continuousAt_fst
    ((g.contMDiff _).comp _ (hsmul.of_le le_self_add).contMDiffAt) hL

/-- The pullbacks of a metric by the action depend continuously on the group element. -/
private theorem continuous_pullbackSMulInner
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (x : M) :
    Continuous fun a : G ↦ pullbackSMulInner g a x := by
  refine continuous_iff_continuousAt.2 fun a₀ ↦ ?_
  have h := ((contMDiffAt_trivializationAt_pullbackSMul J g x a₀).continuousAt).comp
    (f := fun a : G ↦ (x, a)) (continuous_const.prodMk continuous_id).continuousAt
  refine h.congr (Eventually.of_forall fun a ↦ ?_)
  ext v w
  exact Bundle.trivializationAt_self_bilinearForm_apply x _ v w

variable [CompactSpace G] [T2Space G] [MeasurableSpace G] [OpensMeasurableSpace G]
  (μ : Measure G) [IsProbabilityMeasure μ]

/-- The pullbacks of a metric by the action are integrable in the group element. -/
private theorem integrable_pullbackSMulInner
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (x : M) :
    Integrable (fun a : G ↦ pullbackSMulInner g a x) μ :=
  integrableOn_univ.1 <|
    (continuous_pullbackSMulInner J g x).continuousOn.integrableOn_compact isCompact_univ

omit [IsManifold J 1 G] [ContMDiffSMul J I (n + 1) G M] [CompactSpace G] [T2Space G]
  [OpensMeasurableSpace G] [IsProbabilityMeasure μ] in
/-- The average of the pullbacks of a metric over a measure on the acting group, as a bilinear
form on the model vector space. -/
private def averageInner (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (x : M) : E →L[ℝ] E →L[ℝ] ℝ :=
  ∫ a, pullbackSMulInner g a x ∂μ

private theorem averageInner_apply
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (x : M) (v w : E) :
    averageInner μ g x v w =
      ∫ a, g.inner (a • x) (mfderiv I I (a • ·) x v) (mfderiv I I (a • ·) x w) ∂μ := by
  rw [averageInner, ContinuousLinearMap.integral_apply (integrable_pullbackSMulInner J μ g x),
    ContinuousLinearMap.integral_apply
      ((integrable_pullbackSMulInner J μ g x).apply_continuousLinearMap v)]
  rfl

variable [I.Boundaryless] [SecondCountableTopology E'] [IsManifold I n M] [IsManifold J n G]

/-- The averaged forms are a `C^n` section of the bundle of bilinear forms. -/
private theorem contMDiff_averageInner
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) n
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) x
        (@id (E →L[ℝ] E →L[ℝ] ℝ) (averageInner μ g x))) := by
  intro x₀
  refine (contMDiffAt_section x₀).2 ?_
  -- In the trivialization at `x₀`, the section is the integral of the trivialized pullbacks.
  refine (contMDiffAt_parametric_integral (μ := μ) (J := J)
    (f := fun x (a : G) ↦ (trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
      (fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) x₀
      ⟨x, (ContinuousLinearMap.precomp ℝ (mfderiv I I (a • ·) x)).comp
        ((g.inner (a • x)).comp (mfderiv I I (a • ·) x))⟩).2)
    fun a ↦ contMDiffAt_trivializationAt_pullbackSMul J g x₀ a).congr_of_eventuallyEq ?_
  filter_upwards [(chartAt H x₀).open_source.mem_nhds (mem_chart_source H x₀)] with x hx
  simp only [Bundle.trivializationAt_bilinearForm_eq_pullbackBilinL hx]
  refine (Bundle.trivializationAt_bilinearForm_eq_pullbackBilinL hx _).trans ?_
  exact (ContinuousLinearMap.integral_comp_comm
    (ContinuousLinearMap.pullbackBilinL (V := E) (W := E) (G := ℝ) (tangentCoordChange I x₀ x x))
    (integrable_pullbackSMulInner J μ g x)).symm

variable [FiniteDimensional ℝ E]

/-- **The average of a Riemannian metric over a compact group action.** For a group `G` acting
`C^(n+1)` on a manifold `M`, with `G` a compact manifold carrying a probability measure `μ`, this
is the `C^n` metric

`⟨v, w⟩_x = ∫ g_{a • x}(d(a •)_x v, d(a •)_x w) dμ(a)`.

When `μ` is right-invariant, for instance the image under inversion of the normalized Haar
measure, every element of `G` acts by an isometry of it
(`TauCeti.measureAverageRiemannianMetric_inner_mfderiv`), and it agrees with `g` exactly when `g`
is already invariant (`TauCeti.measureAverageRiemannianMetric_eq_self_iff`). -/
def measureAverageRiemannianMetric
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) :
    ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _) :=
  ContMDiffRiemannianMetric.ofPositiveDefiniteSection
    ⟨fun x ↦ @id (E →L[ℝ] E →L[ℝ] ℝ) (averageInner μ g x), contMDiff_averageInner J μ g⟩
    ((Manifold.mem_positiveDefiniteBilinearSections _).2
    ⟨(Manifold.mem_symmetricBilinearSections _).2 fun x v w ↦
      (averageInner_apply J μ g x v w).trans <|
        (integral_congr_ae (Eventually.of_forall fun a ↦ g.symm _ _ _)).trans
          (averageInner_apply J μ g x w v).symm,
    fun x v hv ↦ by
      have hpos (a : G) :
          0 < g.inner (a • x) (mfderiv I I (a • ·) x v) (mfderiv I I (a • ·) x v) := by
        refine g.pos _ _ ((map_ne_zero_iff _ ?_).2 hv)
        exact ((Diffeomorph.smul J I (n + 1) a).isInvertible_mfderiv (x := x) (by simp)).injective
      have hint : Integrable (fun a : G ↦
          g.inner (a • x) (mfderiv I I (a • ·) x v) (mfderiv I I (a • ·) x v)) μ :=
        ((integrable_pullbackSMulInner J μ g x).apply_continuousLinearMap v
          ).apply_continuousLinearMap v
      have h :
          0 < ∫ a, g.inner (a • x) (mfderiv I I (a • ·) x v) (mfderiv I I (a • ·) x v) ∂μ := by
        rw [integral_pos_iff_support_of_nonneg (fun a ↦ (hpos a).le) hint,
          support_eq_univ fun a ↦ (hpos a).ne']
        simp
      exact h.trans_eq (averageInner_apply J μ g x v v).symm⟩)

/-- The averaged metric is the average of the pulled-back inner products. -/
@[simp]
theorem measureAverageRiemannianMetric_inner
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (x : M) (v w : TangentSpace I x) :
    (measureAverageRiemannianMetric J μ g).inner x v w =
      ∫ a, g.inner (a • x) (mfderiv I I (a • ·) x v) (mfderiv I I (a • ·) x w) ∂μ := by
  rw [measureAverageRiemannianMetric, ContMDiffRiemannianMetric.ofPositiveDefiniteSection_inner]
  exact averageInner_apply J μ g x v w

variable [MeasurableMul G] [μ.IsMulRightInvariant]

/-- Every element of the group acts by an isometry of the metric averaged over a right-invariant
probability measure. -/
theorem measureAverageRiemannianMetric_inner_mfderiv
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (b : G) (x : M) (v w : TangentSpace I x) :
    (measureAverageRiemannianMetric J μ g).inner (b • x)
        (mfderiv I I (b • ·) x v) (mfderiv I I (b • ·) x w) =
      (measureAverageRiemannianMetric J μ g).inner x v w := by
  simp only [measureAverageRiemannianMetric_inner]
  refine Eq.trans ?_ (integral_mul_right_eq_self (μ := μ) (fun a : G ↦
    g.inner (a • x) (mfderiv I I (a • ·) x v) (mfderiv I I (a • ·) x w)) b)
  exact integral_congr_ae (Eventually.of_forall fun a ↦ inner_mfderiv_smul_mfderiv_smul g
    ((ContMDiffSMul.contMDiff_const_smul (I := J) (I' := I) (n := n + 1) b).mdifferentiableAt
      (by simp))
    ((ContMDiffSMul.contMDiff_const_smul (I := J) (I' := I) (n := n + 1) a).mdifferentiableAt
      (by simp)) v w)

/-- A metric is fixed by averaging exactly when every element of the group acts by an isometry
of it. -/
theorem measureAverageRiemannianMetric_eq_self_iff
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) :
    measureAverageRiemannianMetric J μ g = g ↔
      ∀ (a : G) (x : M) (v w : TangentSpace I x),
        g.inner (a • x) (mfderiv I I (a • ·) x v) (mfderiv I I (a • ·) x w) = g.inner x v w := by
  constructor
  · intro h
    rw [← h]
    exact measureAverageRiemannianMetric_inner_mfderiv J μ g
  · intro hg
    ext x v w
    simp [hg]

/-- Averaging a metric twice gives the same invariant metric. -/
@[simp]
theorem measureAverageRiemannianMetric_idempotent
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) :
    measureAverageRiemannianMetric J μ (measureAverageRiemannianMetric J μ g) =
      measureAverageRiemannianMetric J μ g :=
  (measureAverageRiemannianMetric_eq_self_iff J μ _).mpr
    (measureAverageRiemannianMetric_inner_mfderiv J μ g)

omit [OpensMeasurableSpace G] [MeasurableMul G] in
/-- **Invariant metrics for compact group actions.** If a compact topological group acts
`C^(n+1)` on a manifold that carries a `C^n` Riemannian metric, then it carries a `C^n` Riemannian
metric for which every element of the group acts by isometries. -/
theorem exists_contMDiffRiemannianMetric_inner_mfderiv [IsTopologicalGroup G] [BorelSpace G]
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) :
    ∃ g' : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _),
      ∀ (a : G) (x : M) (v w : TangentSpace I x),
        g'.inner (a • x) (mfderiv I I (a • ·) x v) (mfderiv I I (a • ·) x w) = g'.inner x v w := by
  -- The inverse of the normalized Haar measure is a right-invariant probability measure.
  let ν : Measure G := (Measure.haarMeasure ⊤).inv
  have : IsProbabilityMeasure ν := ⟨by
    simpa [ν, Measure.inv_apply] using Measure.haarMeasure_self (G := G) (K₀ := ⊤)⟩
  exact ⟨measureAverageRiemannianMetric J ν g,
    measureAverageRiemannianMetric_inner_mfderiv J ν g⟩

end Compact

end TauCeti
