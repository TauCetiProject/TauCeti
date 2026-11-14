/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.IndexForm.Piecewise
public import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Conjugate.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Jacobi.ExpKernel
import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Smoothness
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Bootstrap
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Smoothness
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.ChartGram
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension
import TauCeti.Analysis.Calculus.ContDiff.ClosedInterval
import TauCeti.Analysis.Distribution.DuBoisReymond
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Kernel and nullity of the geodesic index form

Let `γ` be a geodesic on `[a, b]` (`a < b`). Every Jacobi field along `γ` is index-orthogonal to
every continuous piecewise `C¹` section vanishing at `a` and `b`. Conversely, if a continuous
piecewise `C¹` section `V` along `γ` satisfies `I(V, W) = 0` for all smooth-bump-scaled local
sections `W` supported strictly inside `(a, b)`, then `V` is an unbroken `C²` Jacobi field on
`[a, b]` (Milnor, *Morse Theory*, Theorem 14.1):

1. On each `C¹` piece of `V`, testing against compactly supported smooth multiples of a chart-local
   frame and applying the one-dimensional du Bois-Reymond lemma shows that `D_t V` has `C¹` chart
   pairings, hence a `C¹` tangent-bundle lift via the metric-dual chart frame. The connection
   bootstrap `CovariantDerivative.contMDiffOn_succ_of_alongCurveWithin` upgrades `V` to `C²` on the
   closed piece, and integration by parts then forces the Jacobi equation there.
2. Once `V` is a Jacobi field on each piece of its partition, broken-Jacobi integration by parts
   reduces `I(V, W)` to the negative sum of interior covariant-derivative jump pairings. Isolating
   each interior vertex with a bump-supported global section shows that every jump vanishes, and
   gluing across the partition yields `IsJacobiFieldOn I γ V (Icc a b)`.

Restricting to fixed-endpoint sections (`PiecewiseContMDiffSectionAlong.endpointZero`) identifies
the kernel of `endpointZeroIndexForm` linearly with `endpointJacobiFieldSpace` for every regularity
order `1 ≤ n ≤ ∞` (`[ENat.LEInfty n]`). Consequently, the nullity of `endpointZeroIndexForm` is
finite and equals `conjugateMultiplicity`, and `endpointZeroIndexForm` is nondegenerate precisely
when `a` and `b` are not conjugate along `γ` (on a boundaryless manifold along a radial geodesic
`t ↦ exp_p(t v)`, precisely when `d(exp_p)_{b v}` is injective).

## Main definitions and results

* `TauCeti.Manifold.IsJacobiFieldOn.isPiecewiseContMDiffOn`: every Jacobi field on `[a, b]`
  (`a < b`) has a piecewise `C^n` tangent-bundle lift (`n ≤ ∞`), without boundarylessness.
* `TauCeti.Manifold.IsJacobiFieldOn.union_Icc` and
  `TauCeti.Manifold.isJacobiFieldOn_Icc_of_partition`: gluing Jacobi fields with matching
  one-sided covariant derivatives across interior vertices.
* `TauCeti.Manifold.isJacobiFieldOn_Icc_of_indexForm_bump_smul_eq_zero`,
  `TauCeti.Manifold.isJacobiFieldOn_Icc_iff_indexForm_eq_zero`, and
  `TauCeti.Manifold.isJacobiFieldOn_Icc_iff_indexForm_eq_zero_of_contMDiffOn`: variational
  characterizations of Jacobi fields among continuous piecewise `C¹` sections.
* `TauCeti.Manifold.endpointJacobiEquivIndexFormKer`: linear equivalence between
  `endpointJacobiFieldSpace` and `LinearMap.ker (endpointZeroIndexForm hγ hn)`.
* `TauCeti.Manifold.finrank_ker_endpointZeroIndexForm`,
  `TauCeti.Manifold.ker_endpointZeroIndexForm_ne_bot_iff_isConjugateOn`, and
  `TauCeti.Manifold.nondegenerate_endpointZeroIndexForm_iff`: index-form nullity, conjugacy, and
  nondegeneracy, together with radial-exponential corollaries.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press (1963),
  Theorem 14.1, pp. 78–79.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 10, Proposition 10.14.
* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Chapter 10.
-/

public section

open Bundle CovariantDerivative Filter MeasureTheory Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-! ### Piecewise `C^n` regularity of Jacobi fields -/

/-- Every Jacobi field on `[a, b]` (`a < b`) has a piecewise `C^n` tangent-bundle lift on `[a, b]`
for every `n ≤ ∞`, without requiring `M` to be boundaryless. -/
theorem IsJacobiFieldOn.isPiecewiseContMDiffOn {n : ℕ∞ω} [ENat.LEInfty n]
    {γ : ℝ → M} {J : ∀ t, TangentSpace I (γ t)} {a b : ℝ} (hab : a < b)
    (h : IsJacobiFieldOn I γ J (Icc a b)) :
    IsPiecewiseContMDiffOn I.tangent n (fun r ↦ TotalSpace.mk' E (γ r) (J r)) a b :=
  .of_contMDiffOn hab (h.contMDiffOn_infty.of_le ENat.LEInfty.out)

/-! ### Gluing `C¹` sections and Jacobi fields across corners -/

section Gluing

omit [T2Space M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- Matching one-sided covariant derivatives at `c ∈ (a, b)` imply matching one-sided derivatives
of `sectionCoord` at `c`. -/
private lemma derivWithin_sectionCoord_eq_of_alongCurveWithin_eq
    (cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x))
    {γ : ℝ → M} {V : ∀ t, TangentSpace I (γ t)} {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc a b))
    (hD : alongCurveWithin cov γ V (Icc a c) c = alongCurveWithin cov γ V (Icc c b) c) :
    derivWithin (sectionCoord (F := E) γ V (γ c)) (Icc a c) c =
      derivWithin (sectionCoord (F := E) γ V (γ c)) (Icc c b) c := by
  have hc : c ∈ Icc a b := ⟨hac.le, hcb.le⟩
  have hu_diff : DifferentiableWithinAt ℝ (extChartAt I (γ c) ∘ γ) (Icc a b) c := by
    simpa [writtenInExtChartAt] using
      ((hγ c hc).mdifferentiableWithinAt one_ne_zero).differentiableWithinAt_writtenInExtChartAt
  have hu₁ := (hu_diff.hasDerivWithinAt.mono (Icc_subset_Icc_right hcb.le)).derivWithin
    (uniqueDiffOn_Icc hac c ⟨hac.le, le_rfl⟩)
  have hu₂ := (hu_diff.hasDerivWithinAt.mono (Icc_subset_Icc_left hac.le)).derivWithin
    (uniqueDiffOn_Icc hcb c ⟨le_rfl, hcb.le⟩)
  have hCLM := congrArg ((trivializationAt E (TangentSpace I) (γ c)).continuousLinearMapAt ℝ
    (γ c)) hD
  rw [continuousLinearMapAt_alongCurveWithin cov rfl V,
    continuousLinearMapAt_alongCurveWithin cov rfl V, hu₁, hu₂] at hCLM
  exact add_right_cancel hCLM

omit [T2Space M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- `C¹` smoothness within `[a, b]` at an interior parameter `c` where two `C¹` tangent-bundle
lifts have matching one-sided covariant derivatives. -/
private theorem contMDiffWithinAt_one_union_Icc_at_corner
    (cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x))
    {γ : ℝ → M} {V : ∀ t, TangentSpace I (γ t)} {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc a b))
    (hV₁ : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (V r)) (Icc a c))
    (hV₂ : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (V r)) (Icc c b))
    (hD : alongCurveWithin cov γ V (Icc a c) c = alongCurveWithin cov γ V (Icc c b) c) :
    ContMDiffWithinAt 𝓘(ℝ, ℝ) I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (V r)) (Icc a b) c := by
  let e := trivializationAt E (TangentSpace I) (γ c)
  let v := sectionCoord (F := E) γ V (γ c)
  have hc : c ∈ Icc a b := ⟨hac.le, hcb.le⟩
  have hx : γ c ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ c)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1
    ((hγ c hc).continuousWithinAt.preimage_mem_nhdsWithin (e.open_baseSet.mem_nhds hx))
  let δ := min ε (min (c - a) (b - c)) / 2
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hp_ge : a ≤ c - δ := by
    dsimp only [δ]; linarith [min_le_right ε (min (c - a) (b - c)), min_le_left (c - a) (b - c)]
  have hq_le : c + δ ≤ b := by
    dsimp only [δ]; linarith [min_le_right ε (min (c - a) (b - c)), min_le_right (c - a) (b - c)]
  have hbase : ∀ r ∈ Icc (c - δ) (c + δ), γ r ∈ e.baseSet := fun r hr ↦ by
    have hδ_le : δ ≤ ε / 2 := by dsimp only [δ]; linarith [min_le_left ε (min (c - a) (b - c))]
    refine hball ⟨Metric.mem_ball.2 ?_, hp_ge.trans hr.1, hr.2.trans hq_le⟩
    rw [Real.dist_eq, abs_lt]
    exact ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hv₁ : ContDiffOn ℝ 1 v (Icc (c - δ) c) := fun r hr ↦
    (contDiffWithinAt_sectionCoord_iff γ V ((hγ.mono (Icc_subset_Icc hp_ge hcb.le)) r hr)
      (hbase r ⟨hr.1, by linarith [hr.2]⟩)).2 (hV₁.mono (Icc_subset_Icc hp_ge le_rfl) r hr)
  have hv₂ : ContDiffOn ℝ 1 v (Icc c (c + δ)) := fun r hr ↦
    (contDiffWithinAt_sectionCoord_iff γ V ((hγ.mono (Icc_subset_Icc hac.le hq_le)) r hr)
      (hbase r ⟨by linarith [hr.1], hr.2⟩)).2 (hV₂.mono (Icc_subset_Icc le_rfl hq_le) r hr)
  have hdv₁ : derivWithin v (Icc (c - δ) c) c = derivWithin v (Icc a c) c :=
    (((contDiffWithinAt_sectionCoord_iff γ V (hγ.mono (Icc_subset_Icc_right hcb.le) c
        ⟨hac.le, le_rfl⟩) hx).2 (hV₁ c ⟨hac.le, le_rfl⟩)).differentiableWithinAt one_ne_zero
      |>.hasDerivWithinAt.mono (Icc_subset_Icc_left hp_ge)).derivWithin
      (uniqueDiffOn_Icc (by linarith) c ⟨by linarith, le_rfl⟩)
  have hdv₂ : derivWithin v (Icc c (c + δ)) c = derivWithin v (Icc c b) c :=
    (((contDiffWithinAt_sectionCoord_iff γ V (hγ.mono (Icc_subset_Icc_left hac.le) c
        ⟨le_rfl, hcb.le⟩) hx).2 (hV₂ c ⟨le_rfl, hcb.le⟩)).differentiableWithinAt one_ne_zero
      |>.hasDerivWithinAt.mono (Icc_subset_Icc_right hq_le)).derivWithin
      (uniqueDiffOn_Icc (by linarith) c ⟨le_rfl, by linarith⟩)
  have hv_union := TauCeti.contDiffOn_one_Icc_of_derivWithin_eq hv₁ hv₂
    (hdv₁.trans ((derivWithin_sectionCoord_eq_of_alongCurveWithin_eq cov hac hcb hγ hD).trans
      hdv₂.symm))
  refine (contDiffWithinAt_sectionCoord_iff γ V (hγ c hc) hx).1
    ((hv_union c ⟨by linarith, by linarith⟩).mono_of_mem_nhdsWithin ?_)
  exact mem_nhdsWithin.2 ⟨Ioo (c - δ) (c + δ), isOpen_Ioo, ⟨by linarith, by linarith⟩,
    fun r hr ↦ Ioo_subset_Icc_self hr.1⟩

omit [T2Space M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- Gluing two `C¹` tangent-bundle lifts along a `C¹` curve across `c ∈ (a, b)` when their
one-sided covariant derivatives agree at `c`. -/
private theorem contMDiffOn_one_union_Icc_of_alongCurveWithin_eq
    (cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x))
    {γ : ℝ → M} {V : ∀ t, TangentSpace I (γ t)} {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc a b))
    (hV₁ : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (V r)) (Icc a c))
    (hV₂ : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (V r)) (Icc c b))
    (hD : alongCurveWithin cov γ V (Icc a c) c = alongCurveWithin cov γ V (Icc c b) c) :
    ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (V r)) (Icc a b) := by
  intro t ht
  rcases lt_trichotomy t c with htc | htc | hct
  · exact (hV₁ t ⟨ht.1, htc.le⟩).mono_of_mem_nhdsWithin
      (mem_nhdsWithin.2 ⟨Iio c, isOpen_Iio, htc, fun r hr ↦ ⟨hr.2.1, hr.1.le⟩⟩)
  · subst t
    exact contMDiffWithinAt_one_union_Icc_at_corner cov hac hcb hγ hV₁ hV₂ hD
  · exact (hV₂ t ⟨hct.le, ht.2⟩).mono_of_mem_nhdsWithin
      (mem_nhdsWithin.2 ⟨Ioi c, isOpen_Ioi, hct, fun r hr ↦ ⟨hr.1.le, hr.2.2⟩⟩)

omit [T2Space M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- Restricting `alongCurveWithin` from `[a, b]` to a nondegenerate subinterval `[p, q] ⊆ [a, b]`
for a `C¹` section along a `C¹` curve. -/
private lemma alongCurveWithin_Icc_subset_of_contMDiffOn_one
    (cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x))
    {γ : ℝ → M} {W : ∀ t, TangentSpace I (γ t)} {a p q b : ℝ}
    (hpq : p < q) (hsub : Icc p q ⊆ Icc a b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc a b))
    (hW : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (W r)) (Icc a b))
    {r : ℝ} (hr : r ∈ Icc p q) :
    alongCurveWithin cov γ W (Icc p q) r = alongCurveWithin cov γ W (Icc a b) r :=
  CovariantDerivative.alongCurveWithin_subset cov γ W hsub (uniqueDiffOn_Icc hpq r hr)
    (TauCeti.Manifold.differentiableWithinAt_sectionCoord γ W
      ((hW r (hsub hr)).mdifferentiableWithinAt one_ne_zero)
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ r)))
    (by
      simpa [writtenInExtChartAt] using
        ((hγ r (hsub hr)).mdifferentiableWithinAt
          one_ne_zero).differentiableWithinAt_writtenInExtChartAt)

/-- **Two-piece Jacobi gluing.** If `γ` is a geodesic on `[a, b]` and `V` is a Jacobi field on
`[a, c]` and on `[c, b]` whose left and right covariant derivatives agree at `c`, then `V` is a
Jacobi field on `[a, b]`. When `c ≤ a` or `b ≤ c`, one piece already covers `[a, b]`. -/
theorem IsJacobiFieldOn.union_Icc {γ : ℝ → M} {V : ∀ t, TangentSpace I (γ t)} {a c b : ℝ}
    (hγ : IsGeodesicCurveOn I γ (Icc a b))
    (h₁ : IsJacobiFieldOn I γ V (Icc a c)) (h₂ : IsJacobiFieldOn I γ V (Icc c b))
    (hD : alongCurveWithin (leviCivitaConnection I M) γ V (Icc a c) c =
      alongCurveWithin (leviCivitaConnection I M) γ V (Icc c b) c) :
    IsJacobiFieldOn I γ V (Icc a b) := by
  rcases le_or_gt c a with hca | hac
  · exact h₂.mono hγ.uniqueDiffOn (Icc_subset_Icc hca le_rfl)
  rcases le_or_gt b c with hbc | hcb
  · exact h₁.mono hγ.uniqueDiffOn (Icc_subset_Icc le_rfl hbc)
  let cov := leviCivitaConnection I M
  have hγ1 : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc a b) := hγ.contMDiffOn.of_le one_le_two
  have hV1 := contMDiffOn_one_union_Icc_of_alongCurveWithin_eq cov hac hcb hγ1
    (h₁.contMDiffOn.of_le one_le_two) (h₂.contMDiffOn.of_le one_le_two) hD
  have hD₁ (r : ℝ) (hr : r ∈ Icc a c) :=
    alongCurveWithin_Icc_subset_of_contMDiffOn_one cov hac (Icc_subset_Icc_right hcb.le) hγ1 hV1 hr
  have hD₂ (r : ℝ) (hr : r ∈ Icc c b) :=
    alongCurveWithin_Icc_subset_of_contMDiffOn_one cov hcb (Icc_subset_Icc_left hac.le) hγ1 hV1 hr
  have hDD₁ (r : ℝ) (hr : r ∈ Icc a c) := alongCurveWithin_congr cov γ _
    (mem_of_superset self_mem_nhdsWithin fun s hs ↦ (hD₁ s hs).symm) (hD₁ r hr).symm
  have hDD₂ (r : ℝ) (hr : r ∈ Icc c b) := alongCurveWithin_congr cov γ _
    (mem_of_superset self_mem_nhdsWithin fun s hs ↦ (hD₂ s hs).symm) (hD₂ r hr).symm
  have hvel₁ (r : ℝ) (hr : r ∈ Icc a c) :=
    curveVelocityWithin_subset (Icc_subset_Icc_right hcb.le) (uniqueDiffOn_Icc hac r hr)
      (hγ.mdifferentiableOn r ⟨hr.1, hr.2.trans hcb.le⟩)
  have hvel₂ (r : ℝ) (hr : r ∈ Icc c b) :=
    curveVelocityWithin_subset (Icc_subset_Icc_left hac.le) (uniqueDiffOn_Icc hcb r hr)
      (hγ.mdifferentiableOn r ⟨hac.le.trans hr.1, hr.2⟩)
  have hDV1 : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1
      (fun r ↦ TotalSpace.mk' E (γ r) (alongCurveWithin cov γ V (Icc a b) r)) (Icc a b) := by
    refine contMDiffOn_one_union_Icc_of_alongCurveWithin_eq cov hac hcb hγ1
      (h₁.contMDiffOn_alongCurveWithin.congr fun r hr ↦ congrArg (TotalSpace.mk' E (γ r))
        (hD₁ r hr).symm)
      (h₂.contMDiffOn_alongCurveWithin.congr fun r hr ↦ congrArg (TotalSpace.mk' E (γ r))
        (hD₂ r hr).symm) ?_
    rw [hDD₁ c ⟨hac.le, le_rfl⟩, h₁.alongCurveWithin_alongCurveWithin_eq ⟨hac.le, le_rfl⟩,
      hDD₂ c ⟨le_rfl, hcb.le⟩, h₂.alongCurveWithin_alongCurveWithin_eq ⟨le_rfl, hcb.le⟩,
      hvel₁ c ⟨hac.le, le_rfl⟩, hvel₂ c ⟨le_rfl, hcb.le⟩]
  have hV2 := contMDiffOn_succ_of_alongCurveWithin cov γ V le_rfl
    (fun t _ ↦ contMDiffCovariantDerivativeOn_leviCivitaConnection (m := ∞) (k := ∞)
      (trivializationAt E (TangentSpace I) (γ t)).open_baseSet (by simp) (by simp))
    (uniqueDiffOn_Icc (hac.trans hcb)) hγ.contMDiffOn hV1 hDV1
  refine ⟨hγ, hV2, fun r hr ↦ ?_⟩
  rcases le_total r c with hrc | hcr
  · rw [← alongCurveWithin_Icc_subset_of_contMDiffOn_one cov hac (Icc_subset_Icc_right hcb.le)
        hγ1 hDV1 ⟨hr.1, hrc⟩, hDD₁ r ⟨hr.1, hrc⟩, ← hvel₁ r ⟨hr.1, hrc⟩]
    exact h₁.equation r ⟨hr.1, hrc⟩
  · rw [← alongCurveWithin_Icc_subset_of_contMDiffOn_one cov hcb (Icc_subset_Icc_left hac.le)
        hγ1 hDV1 ⟨hcr, hr.2⟩, hDD₂ r ⟨hcr, hr.2⟩, ← hvel₂ r ⟨hcr, hr.2⟩]
    exact h₂.equation r ⟨hcr, hr.2⟩

/-- **Partition Jacobi gluing.** If `γ` is a geodesic on `[a, b]` and `V` solves the Jacobi
equation on each closed piece of a strict partition `τ` of `[a, b]` with matching one-sided
covariant derivatives at every interior vertex, then `V` is an unbroken Jacobi field on `[a, b]`. -/
theorem isJacobiFieldOn_Icc_of_partition {γ : ℝ → M} {V : ∀ t, TangentSpace I (γ t)}
    {a b : ℝ} {k : ℕ} (τ : Fin (k + 2) → ℝ) (hτa : τ 0 = a) (hτb : τ (Fin.last (k + 1)) = b)
    (hτ : ∀ i : Fin (k + 1), τ i.castSucc < τ i.succ)
    (hγ : IsGeodesicCurveOn I γ (Icc a b))
    (hV : ∀ i : Fin (k + 1), IsJacobiFieldOn I γ V (Icc (τ i.castSucc) (τ i.succ)))
    (hjump : ∀ j : Fin k,
      alongCurveWithin (leviCivitaConnection I M) γ V
          (Icc (τ j.castSucc.castSucc) (τ j.castSucc.succ)) (τ j.castSucc.succ) =
        alongCurveWithin (leviCivitaConnection I M) γ V
          (Icc (τ j.succ.castSucc) (τ j.succ.succ)) (τ j.castSucc.succ)) :
    IsJacobiFieldOn I γ V (Icc a b) := by
  induction k generalizing a b with
  | zero =>
    subst hτa hτb
    exact hV 0
  | succ k ih =>
    subst hτa hτb
    let c := τ (Fin.last (k + 1)).castSucc
    have hac : τ 0 < c := Fin.strictMono_iff_lt_succ.mpr hτ (Fin.castSucc_pos Fin.last_pos')
    have hcb : c < τ (Fin.last (k + 2)) := by
      simpa only [Fin.succ_last] using hτ (Fin.last (k + 1))
    have hleft : IsJacobiFieldOn I γ V (Icc (τ 0) c) :=
      ih (fun i ↦ τ i.castSucc) rfl rfl
        (fun i ↦ by simpa only [Fin.succ_castSucc] using hτ i.castSucc)
        (hγ.mono (uniqueDiffOn_Icc hac) (Icc_subset_Icc_right hcb.le))
        (fun i ↦ by simpa only [Fin.succ_castSucc] using hV i.castSucc)
        (fun j ↦ by simpa only [Fin.succ_castSucc] using hjump j.castSucc)
    have hright : IsJacobiFieldOn I γ V (Icc c (τ (Fin.last (k + 2)))) := by
      simpa only [c, Fin.succ_last] using hV (Fin.last (k + 1))
    have hDc : alongCurveWithin (leviCivitaConnection I M) γ V (Icc (τ 0) c) c =
        alongCurveWithin (leviCivitaConnection I M) γ V (Icc c (τ (Fin.last (k + 2)))) c := by
      have hsub : Icc (τ (Fin.last k).castSucc.castSucc) c ⊆ Icc (τ 0) c :=
        Icc_subset_Icc_left ((Fin.strictMono_iff_lt_succ.mpr hτ).monotone (Fin.zero_le _))
      have hlast : τ (Fin.last k).castSucc.castSucc < c := by
        simpa only [c, Fin.succ_last, Fin.succ_castSucc] using hτ (Fin.last k).castSucc
      rw [← hleft.alongCurveWithin_subset (uniqueDiffOn_Icc hlast c ⟨hlast.le, le_rfl⟩)
        hsub ⟨hlast.le, le_rfl⟩]
      simpa only [c, Fin.succ_last, Fin.succ_castSucc] using hjump (Fin.last k)
    exact hleft.union_Icc hγ hright hDc

end Gluing

/-! ### Support localization and bump-scaled local sections -/

section BumpSupport

omit [FiniteDimensional ℝ E] [T2Space M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- Smooth-bump-scaled local sections supported in `U` are `C^n` along any `C^n` curve `γ`
(`n ≤ ∞`). -/
private lemma contMDiffOn_bump_smul_section {n : ℕ∞ω} (hn : n ≤ ∞)
    {γ : ℝ → M} {s : Set ℝ} (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I n γ s)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    {U : Set M} (hU : IsOpen U) (hγU : γ '' tsupport ψ ⊆ U)
    {Y : ∀ x, TangentSpace I x}
    (hY : ContMDiffOn I I.tangent ∞ (fun x ↦ TotalSpace.mk' E x (Y x)) U) :
    ContMDiffOn 𝓘(ℝ, ℝ) I.tangent n (fun t ↦ TotalSpace.mk' E (γ t) (ψ t • Y (γ t))) s := by
  intro t ht
  by_cases hts : t ∈ tsupport ψ
  · have hγt : γ t ∈ U := hγU ⟨t, hts, rfl⟩
    have hYt : ContMDiffWithinAt 𝓘(ℝ, ℝ) I.tangent n
        (fun r ↦ TotalSpace.mk' E (γ r) (Y (γ r))) s t :=
      (((hY.of_le hn) (γ t) hγt).contMDiffAt (hU.mem_nhds hγt)).comp_contMDiffWithinAt t (hγ t ht)
    exact ((hψ.of_le hn).contMDiff t).contMDiffWithinAt.smul_totalSpace hYt
  · have hzero : ContMDiffWithinAt 𝓘(ℝ, ℝ) I.tangent n
        (fun r ↦ TotalSpace.mk' E (γ r) (0 : TangentSpace I (γ r))) s t :=
      ((Bundle.contMDiff_zeroSection ℝ (TangentSpace I) (n := n)).comp_contMDiffOn hγ) t ht
    have hev : ∀ᶠ r in 𝓝[s] t, ψ r = 0 :=
      nhdsWithin_le_nhds (notMem_tsupport_iff_eventuallyEq.mp hts)
    refine hzero.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [hev] with r hr
      simp [hr]
    · simp [image_eq_zero_of_notMem_tsupport hts]

omit [FiniteDimensional ℝ E] [T2Space M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- Smooth-bump-scaled local sections are piecewise `C^n` along any piecewise `C^n` curve `γ`
(`n ≤ ∞`). -/
private lemma isPiecewiseContMDiffOn_bump_smul_section {n : ℕ∞ω} (hn : n ≤ ∞)
    {γ : ℝ → M} {a b : ℝ} (hγ : IsPiecewiseContMDiffOn I n γ a b)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    {U : Set M} (hU : IsOpen U) (hγU : γ '' tsupport ψ ⊆ U)
    {Y : ∀ x, TangentSpace I x}
    (hY : ContMDiffOn I I.tangent ∞ (fun x ↦ TotalSpace.mk' E x (Y x)) U) :
    IsPiecewiseContMDiffOn I.tangent n (fun t ↦ TotalSpace.mk' E (γ t) (ψ t • Y (γ t))) a b := by
  obtain ⟨k, τ, hτa, hτb, hτ, hpieces⟩ := hγ.exists_partition
  exact .of_partition τ hτa hτb hτ fun i ↦
    contMDiffOn_bump_smul_section hn (hpieces i) hψ hU hγU hY

/-- Restricting `indexForm` from `[a, b]` to `[u, v] ⊆ [a, b]` when `W` vanishes outside
`(u, v)`. -/
private lemma indexForm_subinterval_eq_of_tsupport_subset
    {γ : ℝ → M} {V W : ∀ t, TangentSpace I (γ t)} {a u v b : ℝ}
    (hau : a ≤ u) (huv : u < v) (hvb : v ≤ b)
    (hV : IsPiecewiseContMDiffOn I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (V r)) a b)
    (hW : IsPiecewiseContMDiffOn I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (W r)) a b)
    (hW0 : ∀ t, t ∉ Ioo u v → W t = 0) :
    indexForm I γ V W u v = indexForm I γ V W a b := by
  have hleft : indexForm I γ V W a u = 0 := by
    rcases eq_or_lt_of_le hau with rfl | hau'
    · exact indexForm_same
    · exact (indexForm_congr (fun _ _ ↦ rfl) (fun _ _ ↦ HEq.rfl) fun t ht ↦ by
        rw [uIoo_of_lt hau'] at ht
        exact heq_of_eq (hW0 t fun h ↦ h.1.not_ge ht.2.le)).trans indexForm_zero_right
  have hright : indexForm I γ V W v b = 0 := by
    rcases eq_or_lt_of_le hvb with rfl | hvb'
    · exact indexForm_same
    · exact (indexForm_congr (fun _ _ ↦ rfl) (fun _ _ ↦ HEq.rfl) fun t ht ↦ by
        rw [uIoo_of_lt hvb'] at ht
        exact heq_of_eq (hW0 t fun h ↦ h.2.not_ge ht.1.le)).trans indexForm_zero_right
  have hi_au : IntervalIntegrable (indexFormIntegrand I γ V W) volume a u := by
    rcases eq_or_lt_of_le hau with rfl | hau'
    · exact IntervalIntegrable.refl
    · exact (hV.mono le_rfl hau' (huv.le.trans hvb)).intervalIntegrable_indexFormIntegrand
        (hW.mono le_rfl hau' (huv.le.trans hvb))
  have hi_uv := (hV.mono hau huv hvb).intervalIntegrable_indexFormIntegrand
    (hW.mono hau huv hvb)
  have hi_vb : IntervalIntegrable (indexFormIntegrand I γ V W) volume v b := by
    rcases eq_or_lt_of_le hvb with rfl | hvb'
    · exact IntervalIntegrable.refl
    · exact (hV.mono (hau.trans huv.le) hvb' le_rfl).intervalIntegrable_indexFormIntegrand
        (hW.mono (hau.trans huv.le) hvb' le_rfl)
  rw [← indexForm_add_adjacent_intervals (hi_au.trans hi_uv) hi_vb,
    ← indexForm_add_adjacent_intervals hi_au hi_uv, hleft, hright, zero_add, add_zero]

end BumpSupport

/-! ### Variational bootstrap on a single piece -/

section SinglePiece

omit [FiniteDimensional ℝ E] [T2Space M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
variable (I) in
/-- Choosing a nondegenerate closed subinterval `[p, q] ⊆ [u, v]` that is a relative neighborhood
of `t₀ ∈ [u, v]` and maps under `γ` into the tangent-trivialization base set at `γ t₀`. -/
private lemma exists_subinterval_mapsTo_baseSet
    {γ : ℝ → M} {u v t₀ : ℝ}
    (huv : u < v) (hγ : ContinuousOn γ (Icc u v)) (ht₀ : t₀ ∈ Icc u v) :
    ∃ p q, u ≤ p ∧ p < q ∧ q ≤ v ∧ t₀ ∈ Icc p q ∧ Icc p q ∈ 𝓝[Icc u v] t₀ ∧
      MapsTo γ (Icc p q) (trivializationAt E (TangentSpace I) (γ t₀)).baseSet := by
  let e := trivializationAt E (TangentSpace I) (γ t₀)
  have hx₀ : γ t₀ ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t₀)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1
    ((hγ t₀ ht₀).preimage_mem_nhdsWithin (e.open_baseSet.mem_nhds hx₀))
  let δ := ε / 2
  let p := max u (t₀ - δ)
  let q := min v (t₀ + δ)
  refine ⟨p, q, le_max_left _ _, ?_, min_le_left _ _, ?_, ?_, fun r hr ↦ ?_⟩
  · dsimp only [p, q, δ]
    exact max_lt (lt_min huv (by linarith [ht₀.1])) (lt_min (by linarith [ht₀.2]) (by linarith))
  · exact ⟨max_le ht₀.1 (by dsimp only [δ]; linarith), le_min ht₀.2 (by dsimp only [δ]; linarith)⟩
  · exact mem_nhdsWithin.2 ⟨Ioo (t₀ - δ) (t₀ + δ), isOpen_Ioo,
      ⟨by dsimp only [δ]; linarith, by dsimp only [δ]; linarith⟩,
      fun r hr ↦ ⟨max_le hr.2.1 hr.1.1.le, le_min hr.2.2 hr.1.2.le⟩⟩
  · refine hball ⟨Metric.mem_ball.2 ?_, (le_max_left _ _).trans hr.1, hr.2.trans (min_le_left _ _)⟩
    rw [Real.dist_eq, abs_lt]
    dsimp only [p, q, δ] at hr
    exact ⟨by linarith [le_max_right u (t₀ - ε / 2), hr.1],
      by linarith [min_le_right v (t₀ + ε / 2), hr.2]⟩

/-- For a local smooth section `Y` on an open set containing `γ '' [p, q]` (`[p, q] ⊆ [u, v]`) and
a smooth bump `ψ` supported in `(p, q)`, `indexForm I γ V (ψ • (Y ∘ γ)) u v` reduces to a single
interval integral over `[p, q]`. -/
private lemma indexForm_bump_smul_section_eq {γ : ℝ → M} {V : ∀ t, TangentSpace I (γ t)}
    {u p q v : ℝ} (hup : u ≤ p) (hpq : p < q) (hqv : q ≤ v)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc u v))
    (hV : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (V r)) (Icc u v))
    {U : Set M} (hU : IsOpen U) (hγU : MapsTo γ (Icc p q) U)
    {Y : ∀ x, TangentSpace I x}
    (hY : ContMDiffOn I I.tangent ∞ (fun x ↦ TotalSpace.mk' E x (Y x)) U)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψs : tsupport ψ ⊆ Ioo p q) :
    indexForm I γ V (fun t ↦ ψ t • Y (γ t)) u v =
      ∫ t in p..q, (deriv ψ t *
          inner ℝ (alongCurveWithin (leviCivitaConnection I M) γ V (Icc u v) t) (Y (γ t)) +
        ψ t * (inner ℝ (alongCurveWithin (leviCivitaConnection I M) γ V (Icc u v) t)
            (alongCurveWithin (leviCivitaConnection I M) γ (fun r ↦ Y (γ r)) (Icc p q) t) -
          inner ℝ ((leviCivitaConnection I M).curvatureTensor (γ t) (V t)
            (curveVelocityWithin I γ (Icc u v) t) (curveVelocityWithin I γ (Icc u v) t))
            (Y (γ t)))) := by
  let W : ∀ t, TangentSpace I (γ t) := fun t ↦ ψ t • Y (γ t)
  have huv : u < v := (hup.trans_lt hpq).trans_le hqv
  have hYγ : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1
      (fun t ↦ TotalSpace.mk' E (γ t) (Y (γ t))) (Icc p q) :=
    (hY.of_le (by simp)).comp (hγ.mono (Icc_subset_Icc hup hqv)) hγU
  have hW_uv := contMDiffOn_bump_smul_section (by simp) hγ hψ hU
    ((image_mono (hψs.trans Ioo_subset_Icc_self)).trans hγU.image_subset) hY
  rw [← indexForm_subinterval_eq_of_tsupport_subset hup hpq hqv
    (.of_contMDiffOn huv hV) (.of_contMDiffOn huv hW_uv)
    (fun t ht ↦ by simp [image_eq_zero_of_notMem_tsupport fun h ↦ ht (hψs h)]),
    indexForm_eq_integral_indexFormIntegrandWithin (s := Icc u v)
      (uIoo_of_lt hpq ▸ Ioo_subset_Icc_self.trans (Icc_subset_Icc hup hqv))]
  refine intervalIntegral.integral_congr_uIoo fun t ht ↦ ?_
  rw [uIoo_of_lt hpq] at ht
  have hnhds_pq : Icc p q ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
  have hnhds_uv : Icc u v ∈ 𝓝 t := mem_of_superset hnhds_pq (Icc_subset_Icc hup hqv)
  have hDW : alongCurveWithin (leviCivitaConnection I M) γ W (Icc u v) t =
      deriv ψ t • Y (γ t) +
        ψ t • alongCurveWithin (leviCivitaConnection I M) γ (fun r ↦ Y (γ r)) (Icc p q) t := by
    rw [alongCurveWithin_of_mem_nhds _ γ W hnhds_uv,
      alongCurveWithin_of_mem_nhds _ γ (fun r ↦ Y (γ r)) hnhds_pq,
      alongCurve_smul _ γ (fun r ↦ Y (γ r)) ψ
        (hψ.contDiffAt.differentiableAt (by simp))
        (differentiableAt_sectionCoord γ (fun r ↦ Y (γ r))
          (((hYγ t (Ioo_subset_Icc_self ht)).contMDiffAt hnhds_pq).mdifferentiableAt one_ne_zero)
          (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t)))]
  rw [indexFormIntegrandWithin_def, hDW, inner_add_right, real_inner_smul_right,
    real_inner_smul_right, real_inner_smul_right]
  ring

/-- On a chart-contained subinterval `[p, q] ⊆ [u, v]`, index-orthogonality to bump-scaled local
sections upgrades each chart-local frame pairing of `D_t V` to `C¹`. -/
private lemma contDiffOn_inner_chartLocalFrame_alongCurveWithin
    {γ : ℝ → M} {V : ∀ t, TangentSpace I (γ t)} {u p q v : ℝ}
    (hup : u ≤ p) (hpq : p < q) (hqv : q ≤ v)
    (hγ : IsGeodesicCurveOn I γ (Icc u v))
    (hV : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (V r)) (Icc u v))
    {x₀ : M} (hγU : MapsTo γ (Icc p q) (trivializationAt E (TangentSpace I) x₀).baseSet)
    (horth : ∀ (ψ : ℝ → ℝ) (Y : ∀ x, TangentSpace I x) (U : Set M),
      ContDiff ℝ ∞ ψ → tsupport ψ ⊆ Ioo u v → IsOpen U → γ '' tsupport ψ ⊆ U →
      ContMDiffOn I I.tangent ∞ (fun x ↦ TotalSpace.mk' E x (Y x)) U →
      indexForm I γ V (fun t ↦ ψ t • Y (γ t)) u v = 0)
    (j : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ 1 (fun r ↦ inner ℝ (Riemannian.Tensor.chartLocalFrame (I := I) x₀ j (γ r))
      (alongCurveWithin (leviCivitaConnection I M) γ V (Icc u v) r)) (Icc p q) := by
  have : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  let cov := leviCivitaConnection I M
  let e := trivializationAt E (TangentSpace I) x₀
  let Y := Riemannian.Tensor.chartLocalFrame (I := I) x₀ j
  have huv : u < v := (hup.trans_lt hpq).trans_le hqv
  have hγ1 : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc u v) := hγ.contMDiffOn.of_le one_le_two
  have hDV0 := contMDiffOn_alongCurveWithin_leviCivitaConnection (n := 0) (m := ∞) (k := ∞)
    (by simp) (by simp) (uniqueDiffOn_Icc huv) (by simpa using hV)
  have hvel0 : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 0
      (fun r ↦ TotalSpace.mk' E (γ r) (curveVelocityWithin I γ (Icc u v) r)) (Icc u v) := by
    simpa only [funext (curveVelocityLiftWithin_apply (I := I) γ (Icc u v))] using
      hγ1.contMDiffOn_curveVelocityLiftWithin (m := 0) (by simp)
        (uniqueDiffOn_Icc huv).uniqueMDiffOn
  have hY := Riemannian.Tensor.contMDiffOn_chartLocalFrame (I := I) (n := ∞) x₀ j
  have hYγ : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 2
      (fun r ↦ TotalSpace.mk' E (γ r) (Y (γ r))) (Icc p q) :=
    (hY.of_le (by simp)).comp (hγ.contMDiffOn.mono (Icc_subset_Icc hup hqv)) hγU
  have hDY := contMDiffOn_alongCurveWithin_leviCivitaConnection (n := 0) (m := ∞) (k := ∞)
    (by simp) (by simp) (uniqueDiffOn_Icc hpq) (hYγ.of_le one_le_two)
  have hf_cont := (ContMDiffOn.inner_bundle (IB := I) (F := E)
    (E := fun x : M ↦ TangentSpace I x) (b := γ)
    (h := IsContMDiffRiemannianBundle.of_le (n := ∞) zero_le)
    (hDV0.mono (Icc_subset_Icc hup hqv)) (hYγ.of_le (by simp))).continuousOn
  have hg_cont := ((ContMDiffOn.inner_bundle (IB := I) (F := E)
      (E := fun x : M ↦ TangentSpace I x) (b := γ)
      (h := IsContMDiffRiemannianBundle.of_le (n := ∞) zero_le)
      (hDV0.mono (Icc_subset_Icc hup hqv)) hDY).continuousOn).sub
    (ContMDiffOn.inner_bundle (IB := I) (F := E) (E := fun x : M ↦ TangentSpace I x) (b := γ)
      (h := IsContMDiffRiemannianBundle.of_le (n := ∞) zero_le)
      ((cov.contMDiffOn_curvatureTensor (F := E) (V := TangentSpace I) (by simp)
        (hV.of_le zero_le_one) hvel0 hvel0).mono (Icc_subset_Icc hup hqv))
      (hYγ.of_le (by simp))).continuousOn
  refine (hf_cont.contDiffOn_one_Icc_of_integral_deriv_smul_add_eq_zero hg_cont
    fun ψ hψ hψs ↦ ?_).congr fun r _ ↦ real_inner_comm _ _
  simp only [Pi.sub_apply, smul_eq_mul]
  rw [← indexForm_bump_smul_section_eq hup hpq hqv hγ1 hV e.open_baseSet hγU hY hψ hψs]
  exact horth ψ Y e.baseSet hψ (hψs.trans (Ioo_subset_Ioo hup hqv)) e.open_baseSet
    ((image_mono (hψs.trans Ioo_subset_Icc_self)).trans hγU.image_subset) hY

/-- Regularity bootstrap on a single closed geodesic piece: if `V` has a `C¹` lift on `[u, v]`
(`u < v`) and is index-orthogonal to all smooth-bump-scaled local sections supported in `(u, v)`,
then `D_t V` has a `C¹` lift on `[u, v]`. -/
private lemma contMDiffOn_alongCurveWithin_of_indexForm_bump_smul_eq_zero
    {γ : ℝ → M} {V : ∀ t, TangentSpace I (γ t)} {u v : ℝ} (huv : u < v)
    (hγ : IsGeodesicCurveOn I γ (Icc u v))
    (hV : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (V r)) (Icc u v))
    (horth : ∀ (ψ : ℝ → ℝ) (Y : ∀ x, TangentSpace I x) (U : Set M),
      ContDiff ℝ ∞ ψ → tsupport ψ ⊆ Ioo u v → IsOpen U → γ '' tsupport ψ ⊆ U →
      ContMDiffOn I I.tangent ∞ (fun x ↦ TotalSpace.mk' E x (Y x)) U →
      indexForm I γ V (fun t ↦ ψ t • Y (γ t)) u v = 0) :
    ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1
      (fun r ↦ TotalSpace.mk' E (γ r)
        (alongCurveWithin (leviCivitaConnection I M) γ V (Icc u v) r)) (Icc u v) := by
  have : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  let cov := leviCivitaConnection I M
  have hγ1 : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc u v) := hγ.contMDiffOn.of_le one_le_two
  intro t₀ ht₀
  obtain ⟨p, q, hup, hpq, hqv, ht₀_pq, hnhds, hγU⟩ :=
    exists_subinterval_mapsTo_baseSet I huv hγ1.continuousOn ht₀
  have hsum_pq : ContMDiffWithinAt 𝓘(ℝ, ℝ) I.tangent 1
      (fun r ↦ TotalSpace.mk' E (γ r)
        (∑ j, inner ℝ (Riemannian.Tensor.chartLocalFrame (I := I) (γ t₀) j (γ r))
            (alongCurveWithin cov γ V (Icc u v) r) •
          Riemannian.Tensor.chartDualFrame (I := I) (γ t₀) j (γ r))) (Icc p q) t₀ := by
    refine ContMDiffWithinAt.sum_sectionAlong Finset.univ _
      ((hγ1.mono (Icc_subset_Icc hup hqv)) t₀ ht₀_pq) fun j _ ↦ ?_
    have hdual : ContMDiffWithinAt 𝓘(ℝ, ℝ) I.tangent 1
        (fun r ↦ TotalSpace.mk' E (γ r)
          (Riemannian.Tensor.chartDualFrame (I := I) (γ t₀) j (γ r))) (Icc p q) t₀ :=
      ((Riemannian.Tensor.contMDiffAt_chartDualFrame (I := I) (n := ∞) (γ t₀)
        (hγU ht₀_pq) j).of_le (by simp)).comp_contMDiffWithinAt t₀
        ((hγ1.mono (Icc_subset_Icc hup hqv)) t₀ ht₀_pq)
    have hcoeff := contDiffOn_inner_chartLocalFrame_alongCurveWithin hup hpq hqv hγ hV hγU horth j
    exact (contMDiffWithinAt_iff_contDiffWithinAt.2 (hcoeff t₀ ht₀_pq)).smul_totalSpace hdual
  refine (hsum_pq.congr (fun r hr ↦ congrArg (TotalSpace.mk' E (γ r)) ?_)
    (congrArg (TotalSpace.mk' E (γ t₀)) ?_)).mono_of_mem_nhdsWithin hnhds
  · exact (Riemannian.Tensor.sum_inner_chartDualFrame_smul (γ t₀)
      (by simpa only [TangentBundle.trivializationAt_baseSet] using hγU hr) _).2.symm
  · exact (Riemannian.Tensor.sum_inner_chartDualFrame_smul (γ t₀)
      (by simpa only [TangentBundle.trivializationAt_baseSet] using hγU ht₀_pq) _).2.symm

/-- For a `C²` section `V` on `[u, v]` index-orthogonal to smooth-bump-scaled local sections, each
chart-local frame pairing of the Jacobi residual vanishes at `t₀ ∈ [p, q] ⊆ [u, v]`. -/
private lemma inner_chartLocalFrame_jacobiResidual_eq_zero
    {γ : ℝ → M} {V : ∀ t, TangentSpace I (γ t)} {u p q v t₀ : ℝ}
    (hup : u ≤ p) (hpq : p < q) (hqv : q ≤ v) (ht₀_pq : t₀ ∈ Icc p q)
    (hγ1 : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc u v))
    (hV2 : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 2 (fun r ↦ TotalSpace.mk' E (γ r) (V r)) (Icc u v))
    (hR0 : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 0
      (fun r ↦ TotalSpace.mk' E (γ r)
        (alongCurveWithin (leviCivitaConnection I M) γ
            (alongCurveWithin (leviCivitaConnection I M) γ V (Icc u v)) (Icc u v) r +
          (leviCivitaConnection I M).curvatureTensor (γ r) (V r)
            (curveVelocityWithin I γ (Icc u v) r) (curveVelocityWithin I γ (Icc u v) r)))
      (Icc u v))
    (hγU : MapsTo γ (Icc p q) (trivializationAt E (TangentSpace I) (γ t₀)).baseSet)
    (horth : ∀ (ψ : ℝ → ℝ) (Y : ∀ x, TangentSpace I x) (U : Set M),
      ContDiff ℝ ∞ ψ → tsupport ψ ⊆ Ioo u v → IsOpen U → γ '' tsupport ψ ⊆ U →
      ContMDiffOn I I.tangent ∞ (fun x ↦ TotalSpace.mk' E x (Y x)) U →
      indexForm I γ V (fun t ↦ ψ t • Y (γ t)) u v = 0)
    (j : Fin (Module.finrank ℝ E)) :
    inner ℝ (Riemannian.Tensor.chartLocalFrame (I := I) (γ t₀) j (γ t₀))
      (alongCurveWithin (leviCivitaConnection I M) γ
          (alongCurveWithin (leviCivitaConnection I M) γ V (Icc u v)) (Icc u v) t₀ +
        (leviCivitaConnection I M).curvatureTensor (γ t₀) (V t₀)
          (curveVelocityWithin I γ (Icc u v) t₀) (curveVelocityWithin I γ (Icc u v) t₀)) = 0 := by
  have : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  have huv : u < v := (hup.trans_lt hpq).trans_le hqv
  let e := trivializationAt E (TangentSpace I) (γ t₀)
  let Y := Riemannian.Tensor.chartLocalFrame (I := I) (γ t₀) j
  have hY := Riemannian.Tensor.contMDiffOn_chartLocalFrame (I := I) (n := ∞) (γ t₀) j
  have hYγ : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1
      (fun r ↦ TotalSpace.mk' E (γ r) (Y (γ r))) (Icc p q) :=
    (hY.of_le (by simp)).comp (hγ1.mono (Icc_subset_Icc hup hqv)) hγU
  have hf_cont := (ContMDiffOn.inner_bundle (IB := I) (F := E)
    (E := fun x : M ↦ TangentSpace I x) (b := γ)
    (h := IsContMDiffRiemannianBundle.of_le (n := ∞) zero_le)
    (hYγ.of_le zero_le_one) (hR0.mono (Icc_subset_Icc hup hqv))).continuousOn
  refine hf_cont.eqOn_zero_Icc_of_integral_smul_eq_zero hpq (fun ψ hψ hψs ↦ ?_) ht₀_pq
  have hψ0 (t : ℝ) (ht : t ∉ Ioo p q) : ψ t = 0 :=
    image_eq_zero_of_notMem_tsupport fun h ↦ ht (hψs h)
  let W : ∀ t, TangentSpace I (γ t) := fun t ↦ ψ t • Y (γ t)
  have hW_uv := contMDiffOn_bump_smul_section (by simp) hγ1 hψ e.open_baseSet
    ((image_mono (hψs.trans Ioo_subset_Icc_self)).trans hγU.image_subset) hY
  have hI_pq : indexForm I γ V W p q = 0 :=
    (indexForm_subinterval_eq_of_tsupport_subset hup hpq hqv
      (.of_contMDiffOn huv (hV2.of_le one_le_two)) (.of_contMDiffOn huv hW_uv)
      fun t ht ↦ by simp [hψ0 t ht]).trans
      (horth ψ Y e.baseSet hψ (hψs.trans (Ioo_subset_Ioo hup hqv)) e.open_baseSet
        ((image_mono (hψs.trans Ioo_subset_Icc_self)).trans hγU.image_subset) hY)
  have hibp := indexForm_eq_inner_alongCurveWithin_sub_inner_sub_integral (s := Icc u v)
    (fun t ht ↦ hV2 t ((uIcc_of_le hpq.le ▸ ht : t ∈ Icc p q) |> Icc_subset_Icc hup hqv))
    (uIcc_of_le hpq.le ▸ hW_uv.mono (Icc_subset_Icc hup hqv))
    (uIcc_of_le hpq.le ▸ Icc_subset_Icc hup hqv)
  have hψp : ψ p = 0 := hψ0 p (by simp)
  have hψq : ψ q = 0 := hψ0 q (by simp)
  rw [hI_pq, hψp, hψq, zero_smul, zero_smul, inner_zero_right, inner_zero_right, sub_self,
    zero_sub, eq_comm, neg_eq_zero] at hibp
  exact (intervalIntegral.integral_congr fun t _ ↦ by
    rw [smul_eq_mul, real_inner_smul_right, real_inner_comm]).trans hibp

/-- **Variational Jacobi criterion on a single `C¹` piece.** If `γ` is a geodesic on `[u, v]` and
`V` has a `C¹` tangent-bundle lift on `[u, v]` that is index-orthogonal to all smooth-bump-scaled
local sections supported in `(u, v)`, then `V` is a `C²` Jacobi field on `[u, v]`. -/
theorem isJacobiFieldOn_Icc_of_indexForm_bump_smul_eq_zero
    {γ : ℝ → M} {V : ∀ t, TangentSpace I (γ t)} {u v : ℝ}
    (hγ : IsGeodesicCurveOn I γ (Icc u v))
    (hV : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (V r)) (Icc u v))
    (horth : ∀ (ψ : ℝ → ℝ) (Y : ∀ x, TangentSpace I x) (U : Set M),
      ContDiff ℝ ∞ ψ → tsupport ψ ⊆ Ioo u v → IsOpen U → γ '' tsupport ψ ⊆ U →
      ContMDiffOn I I.tangent ∞ (fun x ↦ TotalSpace.mk' E x (Y x)) U →
      indexForm I γ V (fun t ↦ ψ t • Y (γ t)) u v = 0) :
    IsJacobiFieldOn I γ V (Icc u v) := by
  rcases lt_trichotomy u v with huv | rfl | hvu
  · let cov := leviCivitaConnection I M
    have hγ1 : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc u v) := hγ.contMDiffOn.of_le one_le_two
    have hDV1 := contMDiffOn_alongCurveWithin_of_indexForm_bump_smul_eq_zero huv hγ hV horth
    have hV2 : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 2
        (fun r ↦ TotalSpace.mk' E (γ r) (V r)) (Icc u v) :=
      contMDiffOn_succ_of_alongCurveWithin cov γ V le_rfl
        (fun t _ ↦ contMDiffCovariantDerivativeOn_leviCivitaConnection (m := ∞) (k := ∞)
          (trivializationAt E (TangentSpace I) (γ t)).open_baseSet (by simp) (by simp))
        (uniqueDiffOn_Icc huv) hγ.contMDiffOn hV hDV1
    refine ⟨hγ, hV2, fun t₀ ht₀ ↦ ?_⟩
    have hvel0 : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 0
        (fun r ↦ TotalSpace.mk' E (γ r) (curveVelocityWithin I γ (Icc u v) r)) (Icc u v) := by
      simpa only [funext (curveVelocityLiftWithin_apply (I := I) γ (Icc u v))] using
        hγ1.contMDiffOn_curveVelocityLiftWithin (m := 0) (by simp)
          (uniqueDiffOn_Icc huv).uniqueMDiffOn
    have hR0 := (contMDiffOn_alongCurveWithin_leviCivitaConnection (n := 0) (m := ∞) (k := ∞)
        (by simp) (by simp) (uniqueDiffOn_Icc huv) (by simpa using hDV1)).add_sectionAlong
      (cov.contMDiffOn_curvatureTensor (F := E) (V := TangentSpace I) (by simp)
        (hV.of_le zero_le_one) hvel0 hvel0)
    obtain ⟨p, q, hup, hpq, hqv, ht₀_pq, _, hγU⟩ :=
      exists_subinterval_mapsTo_baseSet I huv hγ1.continuousOn ht₀
    have hexp := (Riemannian.Tensor.sum_inner_chartDualFrame_smul (γ t₀)
      (by simpa only [TangentBundle.trivializationAt_baseSet] using hγU ht₀_pq)
      (alongCurveWithin cov γ (alongCurveWithin cov γ V (Icc u v)) (Icc u v) t₀ +
        cov.curvatureTensor (γ t₀) (V t₀)
          (curveVelocityWithin I γ (Icc u v) t₀) (curveVelocityWithin I γ (Icc u v) t₀))).2
    simpa only [cov,
      inner_chartLocalFrame_jacobiResidual_eq_zero hup hpq hqv ht₀_pq hγ1 hV2 hR0 hγU horth,
      zero_smul, Finset.sum_const_zero] using hexp.symm
  · have hud := hγ.uniqueDiffOn u ⟨le_rfl, le_rfl⟩
    rw [Icc_self] at hud
    exact absurd (UniqueDiffWithinAt.eq_deriv {u} hud (hasDerivWithinAt_id u _)
      ((hasDerivWithinAt_const u {u} u).congr (fun x hx ↦ hx) rfl)) one_ne_zero
  · exact ⟨hγ, Icc_eq_empty hvu.not_ge ▸ contMDiffOn_empty, by simp [Icc_eq_empty hvu.not_ge]⟩

end SinglePiece

/-! ### Piecewise variational characterization of Jacobi fields -/

section PiecewiseCharacterization

omit [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- Existence of a smooth-bump-scaled global tangent section along `γ` that equals `v` at an
interior partition vertex `τ j.castSucc.succ`, vanishes at the endpoints and all other interior
vertices, and has closed support strictly inside `(a, b)`. -/
private lemma exists_bump_section_isolating_vertex {γ : ℝ → M} {a b : ℝ} {k : ℕ}
    (τ : Fin (k + 2) → ℝ) (hτa : τ 0 = a) (hτb : τ (Fin.last (k + 1)) = b)
    (hτ : ∀ i : Fin (k + 1), τ i.castSucc < τ i.succ)
    (j : Fin k) (v : TangentSpace I (γ (τ j.castSucc.succ))) :
    ∃ (φ : ℝ → ℝ) (X : ∀ x, TangentSpace I x),
      ContDiff ℝ ∞ φ ∧ tsupport φ ⊆ Ioo a b ∧
      ContMDiff I I.tangent ∞ (T% X) ∧
      φ (τ j.castSucc.succ) • X (γ (τ j.castSucc.succ)) = v ∧
      φ (τ 0) • X (γ (τ 0)) = 0 ∧
      φ (τ (Fin.last (k + 1))) • X (γ (τ (Fin.last (k + 1)))) = 0 ∧
      ∀ m : Fin k, m ≠ j → φ (τ m.castSucc.succ) • X (γ (τ m.castSucc.succ)) = 0 := by
  have hmono := (Fin.strictMono_iff_lt_succ.mpr hτ).monotone
  let c := τ j.castSucc.succ
  have hleft : τ j.castSucc.castSucc < c := hτ j.castSucc
  have hright : c < τ j.succ.succ := hτ j.succ
  let δ := min (c - τ j.castSucc.castSucc) (τ j.succ.succ - c) / 2
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  let φ : ContDiffBump c := ⟨δ / 2, δ, by positivity, by linarith⟩
  have hφ_tsupp : tsupport φ ⊆ Ioo (τ j.castSucc.castSucc) (τ j.succ.succ) := by
    rw [φ.tsupport_eq, Real.closedBall_eq_Icc]
    refine Icc_subset_Ioo ?_ ?_ <;> dsimp only [φ, δ]
    · linarith [min_le_left (c - τ j.castSucc.castSucc) (τ j.succ.succ - c)]
    · linarith [min_le_right (c - τ j.castSucc.castSucc) (τ j.succ.succ - c)]
  have hφ0 (t : ℝ) (ht : t ∉ Ioo (τ j.castSucc.castSucc) (τ j.succ.succ)) : φ t = 0 :=
    image_eq_zero_of_notMem_tsupport fun h ↦ ht (hφ_tsupp h)
  obtain ⟨X, hX, hXc⟩ := FiberBundle.exists_contMDiff_section_eq I E ∞ v
  refine ⟨φ, X, φ.contDiff, hφ_tsupp.trans (Ioo_subset_Ioo (hτa ▸ hmono (Fin.zero_le _))
      (hτb ▸ hmono (Fin.le_last _))), hX, ?_, ?_, ?_, fun m hmj ↦ ?_⟩
  · simp [c, φ.one_of_mem_closedBall (Metric.mem_closedBall_self φ.rIn_pos.le), hXc]
  · simp [hφ0 _ fun h ↦ h.1.not_ge (hmono (Fin.zero_le _))]
  · simp [hφ0 _ fun h ↦ h.2.not_ge (hmono (Fin.le_last _))]
  · rw [hφ0 _ fun hm ↦ ?_, zero_smul]
    rcases lt_or_gt_of_ne hmj with hlt | hgt
    · exact hm.1.not_ge (hmono (Fin.le_iff_val_le_val.mpr (by simp; omega)))
    · exact hm.2.not_ge (hmono (Fin.le_iff_val_le_val.mpr (by simp; omega)))

/-- Vanishing of each interior covariant-derivative jump of a broken Jacobi field that is
index-orthogonal to smooth-bump-scaled global sections. -/
private lemma alongCurveWithin_jump_eq_zero_of_indexForm_bump_smul_eq_zero
    {γ : ℝ → M} {V : ∀ t, TangentSpace I (γ t)} {a b : ℝ} {k : ℕ}
    (τ : Fin (k + 2) → ℝ) (hτa : τ 0 = a) (hτb : τ (Fin.last (k + 1)) = b)
    (hτ : ∀ i : Fin (k + 1), τ i.castSucc < τ i.succ)
    (hγ : IsGeodesicCurveOn I γ (Icc a b))
    (hJ_piece : ∀ i : Fin (k + 1), IsJacobiFieldOn I γ V (Icc (τ i.castSucc) (τ i.succ)))
    (horth : ∀ (ψ : ℝ → ℝ) (Y : ∀ x, TangentSpace I x) (U : Set M),
      ContDiff ℝ ∞ ψ → tsupport ψ ⊆ Ioo a b → IsOpen U → γ '' tsupport ψ ⊆ U →
      ContMDiffOn I I.tangent ∞ (fun x ↦ TotalSpace.mk' E x (Y x)) U →
      indexForm I γ V (fun t ↦ ψ t • Y (γ t)) a b = 0)
    (j : Fin k) :
    alongCurveWithin (leviCivitaConnection I M) γ V
        (Icc (τ j.castSucc.castSucc) (τ j.castSucc.succ)) (τ j.castSucc.succ) =
      alongCurveWithin (leviCivitaConnection I M) γ V
        (Icc (τ j.succ.castSucc) (τ j.succ.succ)) (τ j.castSucc.succ) := by
  have hmono := (Fin.strictMono_iff_lt_succ.mpr hτ).monotone
  have hsub (i : Fin (k + 1)) : Icc (τ i.castSucc) (τ i.succ) ⊆ Icc a b :=
    Icc_subset_Icc (hτa ▸ hmono (Fin.zero_le _)) (hτb ▸ hmono (Fin.le_last _))
  let c := τ j.castSucc.succ
  let Δ : TangentSpace I (γ c) :=
    alongCurveWithin (leviCivitaConnection I M) γ V
        (Icc (τ j.succ.castSucc) (τ j.succ.succ)) c -
      alongCurveWithin (leviCivitaConnection I M) γ V
        (Icc (τ j.castSucc.castSucc) (τ j.castSucc.succ)) c
  obtain ⟨φ, X, hφ, hφ_tsupp, hX, hWc, hWa, hWb, hWm⟩ :=
    exists_bump_section_isolating_vertex τ hτa hτb hτ j Δ
  let W : ∀ t, TangentSpace I (γ t) := fun t ↦ φ t • X (γ t)
  have hI0 : indexForm I γ V W (τ 0) (τ (Fin.last (k + 1))) = 0 := by
    rw [hτa, hτb]
    exact horth φ X univ hφ hφ_tsupp isOpen_univ (subset_univ _) (contMDiffOn_univ.2 hX)
  have hW_τ (i : Fin (k + 1)) : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1
      (fun r ↦ TotalSpace.mk' E (γ r) (W r)) (Icc (τ i.castSucc) (τ i.succ)) :=
    contMDiffOn_bump_smul_section (by simp) ((hγ.contMDiffOn.of_le one_le_two).mono (hsub i))
      hφ isOpen_univ (subset_univ _) (contMDiffOn_univ.2 hX)
  have hibp := indexForm_eq_inner_sub_sum_jump_of_isJacobiFieldOn τ (fun i ↦ (hτ i).le)
    hJ_piece hW_τ
  have hWj (m : Fin k) :
      inner ℝ (alongCurveWithin (leviCivitaConnection I M) γ V
          (Icc (τ m.succ.castSucc) (τ m.succ.succ)) (τ m.castSucc.succ) -
        alongCurveWithin (leviCivitaConnection I M) γ V
          (Icc (τ m.castSucc.castSucc) (τ m.castSucc.succ)) (τ m.castSucc.succ))
        (W (τ m.castSucc.succ)) =
      if m = j then inner ℝ Δ Δ else 0 := by
    split_ifs with hmj
    · subst hmj; simp [W, c, Δ, hWc]
    · simp [W, hWm m hmj]
  rw [hI0, show W (τ 0) = 0 from hWa, show W (τ (Fin.last (k + 1))) = 0 from hWb,
    inner_zero_right, inner_zero_right, sub_self, zero_sub,
    Finset.sum_congr rfl fun m _ ↦ hWj m, Finset.sum_ite_eq'] at hibp
  simp only [Finset.mem_univ, ↓reduceIte] at hibp
  rw [eq_comm, neg_eq_zero, inner_self_eq_zero] at hibp
  exact (sub_eq_zero.mp hibp).symm

/-- **Milnor's piecewise variational Jacobi criterion.** A continuous piecewise `C¹` section `V`
along a geodesic `γ` on `[a, b]` that is index-orthogonal to all smooth-bump-scaled local sections
supported in `(a, b)` is an unbroken `C²` Jacobi field on `[a, b]`. -/
theorem isJacobiFieldOn_Icc_of_indexForm_bump_smul_eq_zero_of_piecewise
    {γ : ℝ → M} {V : ∀ t, TangentSpace I (γ t)} {a b : ℝ}
    (hγ : IsGeodesicCurveOn I γ (Icc a b))
    (hV : IsPiecewiseContMDiffOn I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (V r)) a b)
    (horth : ∀ (ψ : ℝ → ℝ) (Y : ∀ x, TangentSpace I x) (U : Set M),
      ContDiff ℝ ∞ ψ → tsupport ψ ⊆ Ioo a b → IsOpen U → γ '' tsupport ψ ⊆ U →
      ContMDiffOn I I.tangent ∞ (fun x ↦ TotalSpace.mk' E x (Y x)) U →
      indexForm I γ V (fun t ↦ ψ t • Y (γ t)) a b = 0) :
    IsJacobiFieldOn I γ V (Icc a b) := by
  have hγ_pw : IsPiecewiseContMDiffOn I 1 γ a b :=
    .of_contMDiffOn hV.lt (hγ.contMDiffOn.of_le one_le_two)
  obtain ⟨k, τ, hτa, hτb, hτ, hpieces⟩ := hV.exists_partition
  have hmono := (Fin.strictMono_iff_lt_succ.mpr hτ).monotone
  have hsub (i : Fin (k + 1)) : Icc (τ i.castSucc) (τ i.succ) ⊆ Icc a b :=
    Icc_subset_Icc (hτa ▸ hmono (Fin.zero_le _)) (hτb ▸ hmono (Fin.le_last _))
  have hJ_piece (i : Fin (k + 1)) :
      IsJacobiFieldOn I γ V (Icc (τ i.castSucc) (τ i.succ)) := by
    refine isJacobiFieldOn_Icc_of_indexForm_bump_smul_eq_zero
      (hγ.mono (uniqueDiffOn_Icc (hτ i)) (hsub i)) (hpieces i)
      fun ψ Y U hψ hψs hU hγU hY ↦ ?_
    have hW_pw := isPiecewiseContMDiffOn_bump_smul_section (by simp) hγ_pw hψ hU hγU hY
    rw [indexForm_subinterval_eq_of_tsupport_subset
      (hτa ▸ hmono (Fin.zero_le _)) (hτ i) (hτb ▸ hmono (Fin.le_last _)) hV hW_pw
      fun t ht ↦ by simp [image_eq_zero_of_notMem_tsupport fun h ↦ ht (hψs h)]]
    exact horth ψ Y U hψ (hψs.trans (Ioo_subset_Ioo (hτa ▸ hmono (Fin.zero_le _))
      (hτb ▸ hmono (Fin.le_last _)))) hU hγU hY
  exact isJacobiFieldOn_Icc_of_partition τ hτa hτb hτ hγ hJ_piece fun j ↦
    alongCurveWithin_jump_eq_zero_of_indexForm_bump_smul_eq_zero τ hτa hτb hτ hγ hJ_piece horth j

/-- **Variational characterization of Jacobi fields.** For `1 ≤ n ≤ ∞` (`[ENat.LEInfty n]`), a
continuous piecewise `C¹` section `V` along a geodesic `γ` on `[a, b]` is a Jacobi field on
`[a, b]` if and only if `I(V, W) = 0` for every piecewise `C^n` section `W` on `[a, b]` vanishing
at `a` and `b`. -/
theorem isJacobiFieldOn_Icc_iff_indexForm_eq_zero {n : ℕ∞ω} [ENat.LEInfty n] (hn : 1 ≤ n)
    {γ : ℝ → M} {V : ∀ t, TangentSpace I (γ t)} {a b : ℝ}
    (hγ_geo : IsGeodesicCurveOn I γ (Icc a b))
    (hV : IsPiecewiseContMDiffOn I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (V r)) a b) :
    IsJacobiFieldOn I γ V (Icc a b) ↔
      ∀ W : ∀ t, TangentSpace I (γ t),
        IsPiecewiseContMDiffOn I.tangent n (fun r ↦ TotalSpace.mk' E (γ r) (W r)) a b →
        W a = 0 → W b = 0 → indexForm I γ V W a b = 0 := by
  have hγ_inf : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ (Icc a b) :=
    (Bundle.contMDiff_proj (TangentSpace I)).comp_contMDiffOn
      (isJacobiFieldOn_zero hγ_geo).contMDiffOn_infty
  have hγ : IsPiecewiseContMDiffOn I n γ a b :=
    .of_contMDiffOn hV.lt (hγ_inf.of_le ENat.LEInfty.out)
  refine ⟨fun hJ W hW hWa hWb ↦
    hJ.indexForm_eq_zero_of_isPiecewiseContMDiffOn (hW.of_le hn) Subset.rfl hWa hWb, fun horth ↦ ?_⟩
  refine isJacobiFieldOn_Icc_of_indexForm_bump_smul_eq_zero_of_piecewise hγ_geo hV
    fun ψ Y U hψ hψs hU hγU hY ↦ horth _
      (isPiecewiseContMDiffOn_bump_smul_section ENat.LEInfty.out hγ hψ hU hγU hY) ?_ ?_
  · simp [image_eq_zero_of_notMem_tsupport fun h ↦ (hψs h).1.ne rfl]
  · simp [image_eq_zero_of_notMem_tsupport fun h ↦ (hψs h).2.ne rfl]

/-- **Unbroken `C^n` test-field characterization of Jacobi fields.** For `1 ≤ n ≤ ∞`
(`[ENat.LEInfty n]`), testing `indexForm I γ V W a b = 0` against unbroken `C^n` endpoint-zero
sections `W` along a geodesic `γ` on `[a, b]` already forces a continuous piecewise `C¹` section
`V` to be an unbroken Jacobi field on `[a, b]`. -/
theorem isJacobiFieldOn_Icc_iff_indexForm_eq_zero_of_contMDiffOn
    {n : ℕ∞ω} [ENat.LEInfty n] (hn : 1 ≤ n)
    {γ : ℝ → M} {V : ∀ t, TangentSpace I (γ t)} {a b : ℝ}
    (hγ_geo : IsGeodesicCurveOn I γ (Icc a b))
    (hV : IsPiecewiseContMDiffOn I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (V r)) a b) :
    IsJacobiFieldOn I γ V (Icc a b) ↔
      ∀ W : ∀ t, TangentSpace I (γ t),
        ContMDiffOn 𝓘(ℝ, ℝ) I.tangent n (fun r ↦ TotalSpace.mk' E (γ r) (W r)) (Icc a b) →
        W a = 0 → W b = 0 → indexForm I γ V W a b = 0 := by
  have hγ : ContMDiffOn 𝓘(ℝ, ℝ) I n γ (Icc a b) :=
    ((Bundle.contMDiff_proj (TangentSpace I)).comp_contMDiffOn
      (isJacobiFieldOn_zero hγ_geo).contMDiffOn_infty).of_le ENat.LEInfty.out
  refine ⟨fun hJ W hW hWa hWb ↦
    hJ.indexForm_eq_zero_of_isPiecewiseContMDiffOn (.of_contMDiffOn hV.lt (hW.of_le hn))
      Subset.rfl hWa hWb, fun horth ↦ ?_⟩
  refine isJacobiFieldOn_Icc_of_indexForm_bump_smul_eq_zero_of_piecewise hγ_geo hV
    fun ψ Y U hψ hψs hU hγU hY ↦ horth _
      (contMDiffOn_bump_smul_section ENat.LEInfty.out hγ hψ hU hγU hY) ?_ ?_
  · simp [image_eq_zero_of_notMem_tsupport fun h ↦ (hψs h).1.ne rfl]
  · simp [image_eq_zero_of_notMem_tsupport fun h ↦ (hψs h).2.ne rfl]

end PiecewiseCharacterization

/-! ### Kernel, nullity, and nondegeneracy of `endpointZeroIndexForm` -/

section EndpointKernel

variable {n : ℕ∞ω} [ENat.LEInfty n] {γ : ℝ → M} {a b : ℝ}

/-- Restrict a Jacobi field on `[a, b]` linearly to a bundled piecewise `C^n` interval section. -/
def jacobiToPiecewiseSection (hγ : IsPiecewiseContMDiffOn I n γ a b)
    (hγ_geo : IsGeodesicCurveOn I γ (Icc a b)) :
    jacobiFieldSpace hγ_geo →ₗ[ℝ]
      PiecewiseContMDiffSectionAlong (F := E) (V := TangentSpace I) hγ where
  toFun J :=
    .ofPiecewise J.val ((isJacobiFieldOn_of_mem_jacobiFieldSpace J).isPiecewiseContMDiffOn hγ.lt)
  map_add' _ _ := by
    ext t
    simp [PiecewiseContMDiffSectionAlong.ofPiecewise_apply]
  map_smul' _ _ := by
    ext t
    simp [PiecewiseContMDiffSectionAlong.ofPiecewise_apply]

/-- Evaluating `jacobiToPiecewiseSection` at an interval parameter returns the Jacobi field's
value there. -/
@[simp]
theorem jacobiToPiecewiseSection_apply (hγ : IsPiecewiseContMDiffOn I n γ a b)
    (hγ_geo : IsGeodesicCurveOn I γ (Icc a b)) (J : jacobiFieldSpace hγ_geo) (t : Icc a b) :
    (jacobiToPiecewiseSection hγ hγ_geo J).val t = J.val t :=
  PiecewiseContMDiffSectionAlong.ofPiecewise_apply _ _ t

/-- Restricting Jacobi fields on `[a, b]` to bundled interval sections is injective. -/
theorem jacobiToPiecewiseSection_injective (hγ : IsPiecewiseContMDiffOn I n γ a b)
    (hγ_geo : IsGeodesicCurveOn I γ (Icc a b)) :
    Function.Injective (jacobiToPiecewiseSection hγ hγ_geo) := by
  intro J₁ J₂ h
  apply jacobiFieldSpace_ext
  intro t ht
  simpa only [jacobiToPiecewiseSection_apply] using congrArg (fun S ↦ S.val ⟨t, ht⟩) h

/-- Embed endpoint-zero Jacobi fields on `[a, b]` linearly into the fixed-endpoint piecewise `C^n`
section module `PiecewiseContMDiffSectionAlong.endpointZero`. -/
def endpointJacobiToEndpointZero (hγ : IsPiecewiseContMDiffOn I n γ a b)
    (hγ_geo : IsGeodesicCurveOn I γ (Icc a b)) :
    endpointJacobiFieldSpace hγ_geo a b →ₗ[ℝ]
      PiecewiseContMDiffSectionAlong.endpointZero (F := E) (V := TangentSpace I) (hγ := hγ) :=
  ((jacobiToPiecewiseSection hγ hγ_geo).comp (endpointJacobiFieldSpace hγ_geo a b).subtype)
    |>.codRestrict _ fun J ↦ by
      rw [PiecewiseContMDiffSectionAlong.mem_endpointZero_iff]
      simpa only [LinearMap.comp_apply, Submodule.coe_subtype,
        jacobiToPiecewiseSection_apply] using
          (mem_endpointJacobiFieldSpace hγ_geo J.val).mp J.property

/-- Evaluating `endpointJacobiToEndpointZero` at an interval parameter returns the Jacobi field's
value there. -/
@[simp]
theorem endpointJacobiToEndpointZero_apply (hγ : IsPiecewiseContMDiffOn I n γ a b)
    (hγ_geo : IsGeodesicCurveOn I γ (Icc a b))
    (J : endpointJacobiFieldSpace hγ_geo a b) (t : Icc a b) :
    (endpointJacobiToEndpointZero hγ hγ_geo J).val.val t = J.val.val t :=
  jacobiToPiecewiseSection_apply hγ hγ_geo J.val t

/-- Embedding `endpointJacobiFieldSpace` into `PiecewiseContMDiffSectionAlong.endpointZero` is
injective. -/
theorem endpointJacobiToEndpointZero_injective (hγ : IsPiecewiseContMDiffOn I n γ a b)
    (hγ_geo : IsGeodesicCurveOn I γ (Icc a b)) :
    Function.Injective (endpointJacobiToEndpointZero hγ hγ_geo) := by
  intro J₁ J₂ h
  apply Subtype.ext
  exact jacobiToPiecewiseSection_injective hγ hγ_geo (congrArg Subtype.val h)

/-- **Kernel criterion for `endpointZeroIndexForm` (Milnor, Theorem 14.1).** A fixed-endpoint
continuous piecewise `C^n` section (`1 ≤ n ≤ ∞`) lies in the kernel of `endpointZeroIndexForm` if
and only if its zero extension solves the Jacobi equation on `[a, b]`. -/
theorem mem_ker_endpointZeroIndexForm_iff (hγ : IsPiecewiseContMDiffOn I n γ a b)
    (hγ_geo : IsGeodesicCurveOn I γ (Icc a b)) (hn : 1 ≤ n)
    (V : PiecewiseContMDiffSectionAlong.endpointZero (F := E) (V := TangentSpace I) (hγ := hγ)) :
    V ∈ LinearMap.ker (endpointZeroIndexForm hγ hn) ↔
      IsJacobiFieldOn I γ V.val.extendZero (Icc a b) := by
  rw [LinearMap.mem_ker, LinearMap.ext_iff]
  simp only [endpointZeroIndexForm_apply, piecewiseIndexForm_apply, LinearMap.zero_apply]
  rw [isJacobiFieldOn_Icc_iff_indexForm_eq_zero (n := n) hn hγ_geo
    (V.val.isPiecewiseContMDiffOn_extendZero.of_le hn)]
  constructor
  · intro h W hW hWa hWb
    let W₀ : PiecewiseContMDiffSectionAlong.endpointZero
        (F := E) (V := TangentSpace I) (hγ := hγ) :=
      ⟨.ofPiecewise W hW, by
        rw [PiecewiseContMDiffSectionAlong.mem_endpointZero_iff,
          PiecewiseContMDiffSectionAlong.ofPiecewise_apply,
          PiecewiseContMDiffSectionAlong.ofPiecewise_apply]
        exact ⟨hWa, hWb⟩⟩
    have h0 := h W₀
    refine (indexForm_congr (fun _ _ ↦ rfl) (fun _ _ ↦ HEq.rfl) fun t ht ↦ ?_).trans h0
    rw [uIoo_of_lt hγ.lt] at ht
    exact heq_of_eq ((PiecewiseContMDiffSectionAlong.ofPiecewise_apply W hW
      ⟨t, Ioo_subset_Icc_self ht⟩).symm.trans
      (W₀.val.extendZero_apply_of_mem (Ioo_subset_Icc_self ht)).symm)
  · intro h W
    obtain ⟨hWa, hWb⟩ := (PiecewiseContMDiffSectionAlong.mem_endpointZero_iff W.val).1 W.property
    exact h W.val.extendZero W.val.isPiecewiseContMDiffOn_extendZero
      ((W.val.extendZero_apply_of_mem ⟨le_rfl, hγ.lt.le⟩).trans hWa)
      ((W.val.extendZero_apply_of_mem ⟨hγ.lt.le, le_rfl⟩).trans hWb)

/-- **Milnor's endpoint-Jacobi kernel equivalence.** For every `1 ≤ n ≤ ∞` (`[ENat.LEInfty n]`),
embedding Jacobi fields into piecewise `C^n` sections identifies `endpointJacobiFieldSpace`
linearly with the kernel of `endpointZeroIndexForm`. -/
def endpointJacobiEquivIndexFormKer (hγ : IsPiecewiseContMDiffOn I n γ a b)
    (hγ_geo : IsGeodesicCurveOn I γ (Icc a b)) (hn : 1 ≤ n) :
    endpointJacobiFieldSpace hγ_geo a b ≃ₗ[ℝ] LinearMap.ker (endpointZeroIndexForm hγ hn) := by
  refine LinearEquiv.ofBijective
    ((endpointJacobiToEndpointZero hγ hγ_geo).codRestrict
      (LinearMap.ker (endpointZeroIndexForm hγ hn)) fun J ↦ ?_) ⟨?_, ?_⟩
  · rw [mem_ker_endpointZeroIndexForm_iff hγ hγ_geo hn]
    exact (isJacobiFieldOn_of_mem_jacobiFieldSpace J.val).congr fun t ht ↦
      ((endpointJacobiToEndpointZero hγ hγ_geo J).val.extendZero_apply_of_mem ht).trans
        (endpointJacobiToEndpointZero_apply hγ hγ_geo J ⟨t, ht⟩)
  · intro J₁ J₂ h
    exact endpointJacobiToEndpointZero_injective hγ hγ_geo (congrArg Subtype.val h)
  · intro V
    have hJV : IsJacobiFieldOn I γ V.val.val.extendZero (Icc a b) :=
      (mem_ker_endpointZeroIndexForm_iff hγ hγ_geo hn V.val).1 V.property
    obtain ⟨hVa, hVb⟩ :=
      (PiecewiseContMDiffSectionAlong.mem_endpointZero_iff V.val.val).1 V.val.property
    let J₀ : jacobiFieldSpace hγ_geo :=
      ⟨V.val.val.extendZero, (mem_jacobiFieldSpace hγ_geo _).2
        ⟨hJV, fun t ht ↦ V.val.val.extendZero_apply_of_notMem ht⟩⟩
    let J : endpointJacobiFieldSpace hγ_geo a b :=
      ⟨J₀, (mem_endpointJacobiFieldSpace hγ_geo J₀).2
        ⟨(V.val.val.extendZero_apply_of_mem ⟨le_rfl, hγ.lt.le⟩).trans hVa,
         (V.val.val.extendZero_apply_of_mem ⟨hγ.lt.le, le_rfl⟩).trans hVb⟩⟩
    refine ⟨J, Subtype.ext (Subtype.ext ?_)⟩
    ext t
    rw [LinearMap.codRestrict_apply, endpointJacobiToEndpointZero_apply]
    exact V.val.val.extendZero_apply_of_mem t.property

/-- Forward evaluation of `endpointJacobiEquivIndexFormKer`. -/
@[simp]
theorem endpointJacobiEquivIndexFormKer_apply (hγ : IsPiecewiseContMDiffOn I n γ a b)
    (hγ_geo : IsGeodesicCurveOn I γ (Icc a b)) (hn : 1 ≤ n)
    (J : endpointJacobiFieldSpace hγ_geo a b) (t : Icc a b) :
    (endpointJacobiEquivIndexFormKer hγ hγ_geo hn J).val.val.val t = J.val.val t :=
  endpointJacobiToEndpointZero_apply hγ hγ_geo J t

/-- Inverse evaluation of `endpointJacobiEquivIndexFormKer` on `[a, b]`. -/
@[simp]
theorem endpointJacobiEquivIndexFormKer_symm_apply (hγ : IsPiecewiseContMDiffOn I n γ a b)
    (hγ_geo : IsGeodesicCurveOn I γ (Icc a b)) (hn : 1 ≤ n)
    (V : LinearMap.ker (endpointZeroIndexForm hγ hn)) {t : ℝ} (ht : t ∈ Icc a b) :
    ((endpointJacobiEquivIndexFormKer hγ hγ_geo hn).symm V).val.val t = V.val.val.val ⟨t, ht⟩ := by
  let e := endpointJacobiEquivIndexFormKer hγ hγ_geo hn
  have h := congrArg (fun W : LinearMap.ker (endpointZeroIndexForm hγ hn) ↦ W.val.val.val ⟨t, ht⟩)
    (e.apply_symm_apply V)
  exact (endpointJacobiEquivIndexFormKer_apply hγ hγ_geo hn (e.symm V) ⟨t, ht⟩).symm.trans h

/-- The kernel of `endpointZeroIndexForm` along a geodesic is finite-dimensional. -/
theorem finiteDimensional_ker_endpointZeroIndexForm (hγ : IsPiecewiseContMDiffOn I n γ a b)
    (hγ_geo : IsGeodesicCurveOn I γ (Icc a b)) (hn : 1 ≤ n) :
    FiniteDimensional ℝ (LinearMap.ker (endpointZeroIndexForm hγ hn)) := by
  have := finiteDimensional_jacobiFieldSpace hγ_geo isPreconnected_Icc (left_mem_Icc.2 hγ.lt.le)
  exact Module.Finite.equiv (endpointJacobiEquivIndexFormKer hγ hγ_geo hn)

/-- **Index-form nullity equals conjugate multiplicity.** For every `1 ≤ n ≤ ∞`
(`[ENat.LEInfty n]`), the dimension of the kernel of `endpointZeroIndexForm` equals
`conjugateMultiplicity`. -/
theorem finrank_ker_endpointZeroIndexForm (hγ : IsPiecewiseContMDiffOn I n γ a b)
    (hγ_geo : IsGeodesicCurveOn I γ (Icc a b)) (hn : 1 ≤ n) :
    Module.finrank ℝ (LinearMap.ker (endpointZeroIndexForm hγ hn)) =
      conjugateMultiplicity hγ_geo isPreconnected_Icc (left_mem_Icc.2 hγ.lt.le) b := by
  rw [conjugateMultiplicity_eq_finrank]
  exact (endpointJacobiEquivIndexFormKer hγ hγ_geo hn).symm.finrank_eq

/-- Along a geodesic with nonzero velocity, the nullity of `endpointZeroIndexForm` is at most
`dim M - 1`. -/
theorem finrank_ker_endpointZeroIndexForm_le (hγ : IsPiecewiseContMDiffOn I n γ a b)
    (hγ_geo : IsGeodesicCurveOn I γ (Icc a b)) (hn : 1 ≤ n)
    (hv : curveVelocityWithin I γ (Icc a b) a ≠ 0) :
    Module.finrank ℝ (LinearMap.ker (endpointZeroIndexForm hγ hn)) ≤ Module.finrank ℝ E - 1 := by
  rw [finrank_ker_endpointZeroIndexForm hγ hγ_geo hn]
  exact conjugateMultiplicity_le hγ_geo isPreconnected_Icc
    (left_mem_Icc.2 hγ.lt.le) (right_mem_Icc.2 hγ.lt.le) hγ.lt.ne hv

/-- The kernel of `endpointZeroIndexForm` is nontrivial precisely when `a` and `b` are conjugate
along `γ` on `[a, b]`. -/
theorem ker_endpointZeroIndexForm_ne_bot_iff_isConjugateOn
    (hγ : IsPiecewiseContMDiffOn I n γ a b) (hγ_geo : IsGeodesicCurveOn I γ (Icc a b))
    (hn : 1 ≤ n) :
    LinearMap.ker (endpointZeroIndexForm hγ hn) ≠ ⊥ ↔ IsConjugateOn I γ (Icc a b) a b := by
  let := finiteDimensional_ker_endpointZeroIndexForm hγ hγ_geo hn
  rw [← conjugateMultiplicity_pos_iff hγ_geo isPreconnected_Icc
      (left_mem_Icc.2 hγ.lt.le) (right_mem_Icc.2 hγ.lt.le) hγ.lt.ne,
    ← finrank_ker_endpointZeroIndexForm hγ hγ_geo hn,
    Module.finrank_pos_iff, Submodule.nontrivial_iff_ne_bot]

/-- The kernel of `endpointZeroIndexForm` is trivial precisely when `a` and `b` are not conjugate
along `γ` on `[a, b]`. -/
theorem ker_endpointZeroIndexForm_eq_bot_iff_not_isConjugateOn
    (hγ : IsPiecewiseContMDiffOn I n γ a b) (hγ_geo : IsGeodesicCurveOn I γ (Icc a b))
    (hn : 1 ≤ n) :
    LinearMap.ker (endpointZeroIndexForm hγ hn) = ⊥ ↔ ¬ IsConjugateOn I γ (Icc a b) a b :=
  not_ne_iff.symm.trans (ker_endpointZeroIndexForm_ne_bot_iff_isConjugateOn hγ hγ_geo hn).not

/-- `endpointZeroIndexForm` is nondegenerate precisely when `a` and `b` are not conjugate along `γ`
on `[a, b]`. -/
theorem nondegenerate_endpointZeroIndexForm_iff
    (hγ : IsPiecewiseContMDiffOn I n γ a b) (hγ_geo : IsGeodesicCurveOn I γ (Icc a b))
    (hn : 1 ≤ n) :
    (endpointZeroIndexForm hγ hn).Nondegenerate ↔ ¬ IsConjugateOn I γ (Icc a b) a b := by
  have hflip : (endpointZeroIndexForm hγ hn).flip = endpointZeroIndexForm hγ hn :=
    LinearMap.BilinForm.isSymm_iff_flip.mp (isSymm_endpointZeroIndexForm hγ hn)
  change (LinearMap.SeparatingLeft (endpointZeroIndexForm hγ hn) ∧
      LinearMap.SeparatingLeft (endpointZeroIndexForm hγ hn).flip) ↔ _
  rw [hflip, and_self, LinearMap.separatingLeft_iff_ker_eq_bot,
    ker_endpointZeroIndexForm_eq_bot_iff_not_isConjugateOn hγ hγ_geo hn]

end EndpointKernel

/-! ### Radial exponential corollaries -/

section RadialExponential

variable [I.Boundaryless] {n : ℕ∞ω} [ENat.LEInfty n] {p : M} {v : TangentSpace I p} {b : ℝ}

/-- Along the radial geodesic `t ↦ exp_p(t v)` on `[0, b]` (`0 < b`, `b ∈ geodesicInterval`), the
kernel of `endpointZeroIndexForm` is linearly equivalent to `ker(d(exp_p)_{b v})`. -/
def endpointZeroIndexFormKerEquivExpKer
    (hγ : IsPiecewiseContMDiffOn I n (fun t : ℝ ↦ riemannianExp I M p (t • v)) 0 b)
    (hb : b ∈ geodesicInterval I M p v) (hn : 1 ≤ n) :
    LinearMap.ker (endpointZeroIndexForm hγ hn) ≃ₗ[ℝ]
      LinearMap.ker (mfderiv 𝓘(ℝ, TangentSpace I p) I
        (riemannianExp I M p) (b • v)).toLinearMap :=
  have hsub : Icc 0 b ⊆ geodesicInterval I M p v :=
    ordConnected_geodesicInterval.out zero_mem_geodesicInterval hb
  have hγ_geo : IsGeodesicCurveOn I (fun t : ℝ ↦ riemannianExp I M p (t • v)) (Icc 0 b) :=
    (isJacobiFieldOn_mfderiv_riemannianExp p v 0).isGeodesicCurveOn.mono
      (uniqueDiffOn_Icc hγ.lt) hsub
  (endpointJacobiEquivIndexFormKer hγ hγ_geo hn).symm.trans
    (endpointJacobiFieldEquivExpKer hγ_geo isPreconnected_Icc hsub
      (left_mem_Icc.2 hγ.lt.le) (right_mem_Icc.2 hγ.lt.le) hγ.lt.ne')

/-- Along `t ↦ exp_p(t v)` on `[0, b]` (`0 < b`), the nullity of `endpointZeroIndexForm` equals
`dim ker(d(exp_p)_{b v})`. -/
theorem finrank_ker_endpointZeroIndexForm_riemannianExp
    (hγ : IsPiecewiseContMDiffOn I n (fun t : ℝ ↦ riemannianExp I M p (t • v)) 0 b)
    (hb : b ∈ geodesicInterval I M p v) (hn : 1 ≤ n) :
    Module.finrank ℝ (LinearMap.ker (endpointZeroIndexForm hγ hn)) =
      Module.finrank ℝ (LinearMap.ker (mfderiv 𝓘(ℝ, TangentSpace I p) I
        (riemannianExp I M p) (b • v)).toLinearMap) :=
  (endpointZeroIndexFormKerEquivExpKer hγ hb hn).finrank_eq

/-- Along `t ↦ exp_p(t v)` on `[0, b]` (`0 < b`), `endpointZeroIndexForm` is nondegenerate
precisely when `d(exp_p)_{b v}` is injective. -/
theorem nondegenerate_endpointZeroIndexForm_riemannianExp_iff
    (hγ : IsPiecewiseContMDiffOn I n (fun t : ℝ ↦ riemannianExp I M p (t • v)) 0 b)
    (hb : b ∈ geodesicInterval I M p v) (hn : 1 ≤ n) :
    (endpointZeroIndexForm hγ hn).Nondegenerate ↔
      Function.Injective (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (b • v)) := by
  have hsub : Icc 0 b ⊆ geodesicInterval I M p v :=
    ordConnected_geodesicInterval.out zero_mem_geodesicInterval hb
  have hγ_geo : IsGeodesicCurveOn I (fun t : ℝ ↦ riemannianExp I M p (t • v)) (Icc 0 b) :=
    (isJacobiFieldOn_mfderiv_riemannianExp p v 0).isGeodesicCurveOn.mono
      (uniqueDiffOn_Icc hγ.lt) hsub
  rw [nondegenerate_endpointZeroIndexForm_iff hγ hγ_geo hn,
    isConjugateOn_iff_not_injective_mfderiv_riemannianExp hγ_geo isPreconnected_Icc hsub
      (left_mem_Icc.2 hγ.lt.le) (right_mem_Icc.2 hγ.lt.le) hγ.lt.ne', not_not]

end RadialExponential

end TauCeti.Manifold
