/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Tensor
import TauCeti.Analysis.Calculus.ParametricFDeriv
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Chart
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Pullback
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Coordinates
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.Trivialization

/-!
# Mixed covariant derivatives on a parametrized surface

Let `f` be a parametrized surface in a manifold, a map of two real parameters `(q, r)`, and let
`W` be a vector field along it, so that `W q r` is a tangent vector at `f q r`. Covariant
differentiation along the two families of parameter curves gives two operators `D_q` and `D_r` on
such fields. They do not commute: their commutator is the curvature of the connection,

`D_q D_r W - D_r D_q W = R(∂_q f, ∂_r f) W`,

for any smooth connection on the tangent bundle, with no metric or torsion hypothesis. This is
the identity behind the second variation of energy and behind the fact that the variation field of
a family of geodesics is a Jacobi field.

The proof reads everything in the chart at the point `f u v`. With `w` and `φ` the chart readings
of the field and of the surface and `Γ` the Christoffel map of the chart, `D_q D_r W` reads as
`∂_q ∂_r w + ∂_q(Γ(w, ∂_r φ)) + Γ(∂_r w + Γ(w, ∂_r φ), ∂_q φ)`. Second partial derivatives
commute, and the terms which are not symmetric in the two parameters are exactly the chart formula
for the curvature tensor (`CovariantDerivative.curvatureTensor_symm_trivializationAt`).

## Main results

* `CovariantDerivative.alongCurveWithin_alongCurveWithin_sub_alongCurveWithin_alongCurveWithin`:
  the commutator of the two within-set covariant derivatives along a `C²` field on `s₁ ×ˢ s₂` is
  the curvature tensor, at any point of `s₁ ×ˢ s₂` accumulated by the interiors of `s₁` and `s₂`.
* `CovariantDerivative.alongCurve_alongCurve_sub_alongCurve_alongCurve`: the unrestricted case for
  a field which is `C²` at `(u, v)`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Proposition 7.5.
* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 4, Lemma 4.1.
-/

public section

open Bundle Filter Module Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace CovariantDerivative

open TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  (cov : _root_.CovariantDerivative I E (TangentSpace I : M → Type _))
  [ContMDiffCovariantDerivative cov ∞]
  {f : ℝ → ℝ → M} {W : ∀ q r, TangentSpace I (f q r)} {u v : ℝ}

omit [FiniteDimensional ℝ E] in
/-- Differentiating in the first variable within `s₁` the partial derivative in the second variable
within `s₂` of a `C²` map on `s₁ ×ˢ s₂` computes the mixed second derivative in the directions
`(1, 0)` and `(0, 1)`. -/
private theorem hasDerivWithinAt_derivWithin_snd {g : ℝ × ℝ → E} {s₁ s₂ : Set ℝ}
    (hs₁ : UniqueDiffOn ℝ s₁) (hs₂ : UniqueDiffOn ℝ s₂) (hu : u ∈ s₁) (hv : v ∈ s₂)
    (hg : ContDiffWithinAt ℝ 2 g (s₁ ×ˢ s₂) (u, v)) :
    HasDerivWithinAt (fun q ↦ derivWithin (fun r ↦ g (q, r)) s₂ v)
      (fderivWithin ℝ (fderivWithin ℝ g (s₁ ×ˢ s₂)) (s₁ ×ˢ s₂) (u, v) (1, 0) (0, 1)) s₁ u := by
  set S := s₁ ×ˢ s₂
  have hS : UniqueDiffOn ℝ S := hs₁.prod hs₂
  have huv : (u, v) ∈ S := ⟨hu, hv⟩
  obtain ⟨U, hUo, huvU, hgU⟩ := hg.contDiffOn' (m := 2) le_rfl (by simp)
  rw [insert_eq_of_mem huv] at hgU
  have hslice : ∀ q ∈ s₁, (q, v) ∈ U →
      derivWithin (fun r ↦ g (q, r)) s₂ v = fderivWithin ℝ g S (q, v) (0, 1) := by
    intro q hq hqvU
    have hdiff : HasFDerivWithinAt g (fderivWithin ℝ g S (q, v)) S (q, v) := by
      have hd := ((hgU.differentiableOn two_ne_zero (q, v) ⟨⟨hq, hv⟩, hqvU⟩).mono_of_mem_nhdsWithin
        (inter_mem_nhdsWithin S (hUo.mem_nhds hqvU))).hasFDerivWithinAt
      rwa [hd.fderivWithin (hS (q, v) ⟨hq, hv⟩)] at hd
    exact (hdiff.comp v (hasFDerivAt_prodMk_right q v).hasFDerivWithinAt
      fun r hr ↦ Set.mk_mem_prod hq hr).hasDerivWithinAt.derivWithin (hs₂ v hv)
  have hD : HasFDerivWithinAt (fderivWithin ℝ g S)
      (fderivWithin ℝ (fderivWithin ℝ g S) S (u, v)) S (u, v) :=
    ((hg.fderivWithin_right hS (m := 1) le_rfl huv).differentiableWithinAt
      one_ne_zero).hasFDerivWithinAt
  have hDq : HasDerivWithinAt (fun q ↦ fderivWithin ℝ g S (q, v) (0, 1))
      (fderivWithin ℝ (fderivWithin ℝ g S) S (u, v) (1, 0) (0, 1)) s₁ u := by
    simpa only [ContinuousLinearMap.map_zero, add_zero, Function.comp_def,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply] using
      (hD.comp u ((hasFDerivAt_prodMk_left u v).hasFDerivWithinAt (s := s₁))
        fun q hq ↦ Set.mk_mem_prod hq hv).hasDerivWithinAt.clm_apply
        (hasDerivWithinAt_const u s₁ ((0 : ℝ), (1 : ℝ)))
  refine hDq.congr_of_eventuallyEq ?_ (hslice u hu huvU)
  filter_upwards [self_mem_nhdsWithin,
    (continuous_id.prodMk continuous_const).continuousWithinAt.preimage_mem_nhdsWithin
      (hUo.mem_nhds huvU)] with q hq hqvU
  exact hslice q hq hqvU

omit [FiniteDimensional ℝ E] in
/-- Iterated partial derivatives within `s₁` and `s₂` commute for a `C²` map on `s₁ ×ˢ s₂`, at a
point accumulated by the interiors of `s₁` and `s₂`. -/
private theorem derivWithin_derivWithin_comm {g : ℝ × ℝ → E} {s₁ s₂ : Set ℝ}
    (hs₁ : UniqueDiffOn ℝ s₁) (hs₂ : UniqueDiffOn ℝ s₂) (hu : u ∈ s₁) (hv : v ∈ s₂)
    (hu_cls : u ∈ closure (interior s₁)) (hv_cls : v ∈ closure (interior s₂))
    (hg : ContDiffWithinAt ℝ 2 g (s₁ ×ˢ s₂) (u, v)) :
    derivWithin (fun q ↦ derivWithin (fun r ↦ g (q, r)) s₂ v) s₁ u =
      derivWithin (fun r ↦ derivWithin (fun q ↦ g (q, r)) s₁ u) s₂ v := by
  set S := s₁ ×ˢ s₂
  have hS : UniqueDiffOn ℝ S := hs₁.prod hs₂
  have huv : (u, v) ∈ S := ⟨hu, hv⟩
  obtain ⟨U, hUo, huvU, hgU⟩ := hg.contDiffOn' (m := 2) le_rfl (by simp)
  rw [insert_eq_of_mem huv] at hgU
  have hslice : ∀ r ∈ s₂, (u, r) ∈ U →
      derivWithin (fun q ↦ g (q, r)) s₁ u = fderivWithin ℝ g S (u, r) (1, 0) := by
    intro r hr hurU
    have hdiff : HasFDerivWithinAt g (fderivWithin ℝ g S (u, r)) S (u, r) := by
      have hd := ((hgU.differentiableOn two_ne_zero (u, r) ⟨⟨hu, hr⟩, hurU⟩).mono_of_mem_nhdsWithin
        (inter_mem_nhdsWithin S (hUo.mem_nhds hurU))).hasFDerivWithinAt
      rwa [hd.fderivWithin (hS (u, r) ⟨hu, hr⟩)] at hd
    exact (hdiff.comp u ((hasFDerivAt_prodMk_left u r).hasFDerivWithinAt (s := s₁))
      fun q hq ↦ Set.mk_mem_prod hq hr).hasDerivWithinAt.derivWithin (hs₁ u hu)
  have hD : HasFDerivWithinAt (fderivWithin ℝ g S)
      (fderivWithin ℝ (fderivWithin ℝ g S) S (u, v)) S (u, v) :=
    ((hg.fderivWithin_right hS (m := 1) le_rfl huv).differentiableWithinAt
      one_ne_zero).hasFDerivWithinAt
  have hDr : HasDerivWithinAt (fun r ↦ derivWithin (fun q ↦ g (q, r)) s₁ u)
      (fderivWithin ℝ (fderivWithin ℝ g S) S (u, v) (0, 1) (1, 0)) s₂ v := by
    refine (?_ : HasDerivWithinAt (fun r ↦ fderivWithin ℝ g S (u, r) (1, 0)) _ s₂ v
        ).congr_of_eventuallyEq ?_ (hslice v hv huvU)
    · simpa only [ContinuousLinearMap.map_zero, add_zero, Function.comp_def,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply] using
        (hD.comp v ((hasFDerivAt_prodMk_right u v).hasFDerivWithinAt (s := s₂))
          fun r hr ↦ Set.mk_mem_prod hu hr).hasDerivWithinAt.clm_apply
          (hasDerivWithinAt_const v s₂ ((1 : ℝ), (0 : ℝ)))
    · filter_upwards [self_mem_nhdsWithin,
        (continuous_const.prodMk continuous_id).continuousWithinAt.preimage_mem_nhdsWithin
          (hUo.mem_nhds huvU)] with r hr hurU
      exact hslice r hr hurU
  have hcls : (u, v) ∈ closure (interior S) := by
    rw [interior_prod_eq, closure_prod_eq]
    exact ⟨hu_cls, hv_cls⟩
  rw [(hasDerivWithinAt_derivWithin_snd hs₁ hs₂ hu hv hg).derivWithin (hs₁ u hu),
    hDr.derivWithin (hs₂ v hv)]
  exact hg.isSymmSndFDerivWithinAt (by simp) hS hcls huv (1, 0) (0, 1)

omit [T2Space M] [cov.ContMDiffCovariantDerivative ∞] in
/-- **The inner covariant derivatives read in the chart.** Near `u` within `s₁`, the covariant
derivative within `s₂` along the second-parameter curve of a `C²` field on `s₁ ×ˢ s₂`, read in the
chart at `f u v`, is given by the coordinate formula. -/
private theorem sectionCoord_alongCurveWithin_eventuallyEq {s₁ s₂ : Set ℝ}
    (hu : u ∈ s₁) (hv : v ∈ s₂)
    (hW : ContMDiffWithinAt 𝓘(ℝ, ℝ × ℝ) I.tangent 2
      (fun z : ℝ × ℝ ↦ TotalSpace.mk' E (f z.1 z.2) (W z.1 z.2)) (s₁ ×ˢ s₂) (u, v))
    {φ w : ℝ × ℝ → E} (hφdef : φ = fun z ↦ extChartAt I (f u v) (f z.1 z.2))
    (hwdef : w = fun z ↦ (trivializationAt E (TangentSpace I) (f u v)).continuousLinearMapAt ℝ
      (f z.1 z.2) (W z.1 z.2)) :
    letI e := trivializationAt E (TangentSpace I) (f u v)
    letI Γ := christoffelMap (finBasis ℝ E) (cov.isCovariantDerivativeOn (s := e.baseSet))
    sectionCoord (F := E) (fun q ↦ f q v) (fun q ↦ alongCurveWithin cov (f q) (W q) s₂ v)
      (f u v) =ᶠ[𝓝[s₁] u]
      fun q ↦ derivWithin (fun r ↦ w (q, r)) s₂ v +
        Γ (f q v) (w (q, v)) (derivWithin (fun r ↦ φ (q, r)) s₂ v) := by
  set e := trivializationAt E (TangentSpace I) (f u v)
  set S := s₁ ×ˢ s₂
  have huv : (u, v) ∈ S := ⟨hu, hv⟩
  have : IsManifold I (∞ + 1 + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  have : ContMDiffVectorBundle (∞ + 1) E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  have hbase : f u v ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) _
  have hf : ContMDiffWithinAt 𝓘(ℝ, ℝ × ℝ) I 2 (fun z : ℝ × ℝ ↦ f z.1 z.2) S (u, v) :=
    (contMDiff_proj (TangentSpace I)).contMDiffAt.comp_contMDiffWithinAt (u, v) hW
  have hWnhds : ∀ᶠ z in 𝓝[S] (u, v), ContMDiffWithinAt 𝓘(ℝ, ℝ × ℝ) I.tangent 2
      (fun z : ℝ × ℝ ↦ TotalSpace.mk' E (f z.1 z.2) (W z.1 z.2)) S z := by
    simpa only [insert_eq_of_mem huv] using
      (contMDiffWithinAt_iff_contMDiffWithinAt_nhdsWithin (by simp)).mp hW
  have htend : Tendsto (fun q : ℝ ↦ (q, v)) (𝓝[s₁] u) (𝓝[S] (u, v)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (((continuous_id.prodMk continuous_const).tendsto u).mono_left nhdsWithin_le_nhds)
      (Filter.mem_of_superset self_mem_nhdsWithin fun q hq ↦ ⟨hq, hv⟩)
  have hcoord (q : ℝ) : sectionCoord (F := E) (f q) (W q) (f u v) = fun r ↦ w (q, r) :=
    funext fun r ↦ by rw [sectionCoord_apply, hwdef]
  filter_upwards [self_mem_nhdsWithin, htend.eventually (hWnhds.and
    (hf.continuousWithinAt.preimage_mem_nhdsWithin (e.open_baseSet.mem_nhds hbase)))]
    with q hqs ⟨hq, hqb⟩
  have hcurve : ContMDiffWithinAt 𝓘(ℝ, ℝ) I.tangent 2
      (fun r ↦ TotalSpace.mk' E (f q r) (W q r)) s₂ v :=
    hq.comp v ((contDiff_prodMk_right (n := 2) q).contMDiff.contMDiffAt.contMDiffWithinAt (s := s₂))
      fun r hr ↦ ⟨hqs, hr⟩
  have hfq : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I (f q) s₂ v :=
    ((contMDiff_proj (TangentSpace I)).contMDiffAt.comp_contMDiffWithinAt v
      hcurve).mdifferentiableWithinAt (by norm_num)
  have hV : DifferentiableWithinAt ℝ (sectionCoord (F := E) (f q) (W q) (f q v)) s₂ v :=
    differentiableWithinAt_sectionCoord (f q) (W q) (hcurve.mdifferentiableWithinAt (by norm_num))
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) _)
  rw [sectionCoord_apply, ← symmL_alongCurveInChartWithin cov (f q) (W q) hqb hfq hV,
    e.continuousLinearMapAt_symmL (R := ℝ) hqb, alongCurveInChartWithin_apply,
    Function.comp_def, hcoord q, hφdef]

omit [FiniteDimensional ℝ E] [T2Space M] cov [cov.ContMDiffCovariantDerivative ∞] in
/-- Smoothness of the base chart coordinates and trivialized fiber coordinates of `W` within
`s₁ ×ˢ s₂`. -/
private theorem contDiffWithinAt_extChartAt_and_coord {s₁ s₂ : Set ℝ}
    (hW : ContMDiffWithinAt 𝓘(ℝ, ℝ × ℝ) I.tangent 2
      (fun z : ℝ × ℝ ↦ TotalSpace.mk' E (f z.1 z.2) (W z.1 z.2)) (s₁ ×ˢ s₂) (u, v))
    {φ w : ℝ × ℝ → E} (hφdef : φ = fun z ↦ extChartAt I (f u v) (f z.1 z.2))
    (hwdef : w = fun z ↦ (trivializationAt E (TangentSpace I) (f u v)).continuousLinearMapAt ℝ
      (f z.1 z.2) (W z.1 z.2)) :
    ContMDiffWithinAt 𝓘(ℝ, ℝ × ℝ) I 2 (fun z : ℝ × ℝ ↦ f z.1 z.2) (s₁ ×ˢ s₂) (u, v) ∧
      ContDiffWithinAt ℝ 2 φ (s₁ ×ˢ s₂) (u, v) ∧ ContDiffWithinAt ℝ 2 w (s₁ ×ˢ s₂) (u, v) := by
  have : IsManifold I (∞ + 1 + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  have : ContMDiffVectorBundle (∞ + 1) E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  set e := trivializationAt E (TangentSpace I) (f u v)
  have hbase : f u v ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) _
  have hf : ContMDiffWithinAt 𝓘(ℝ, ℝ × ℝ) I 2 (fun z : ℝ × ℝ ↦ f z.1 z.2) (s₁ ×ˢ s₂) (u, v) :=
    (contMDiff_proj (TangentSpace I)).contMDiffAt.comp_contMDiffWithinAt (u, v) hW
  refine ⟨hf, hφdef ▸ contMDiffWithinAt_iff_contDiffWithinAt.mp
    ((contMDiffAt_extChartAt' (mem_chart_source H (f u v))).comp_contMDiffWithinAt (u, v) hf), ?_⟩
  refine (contMDiffWithinAt_iff_contDiffWithinAt.mp
    (contMDiffWithinAt_totalSpace_iff.mp hW).2).congr_of_eventuallyEq ?_
    (hwdef ▸ e.continuousLinearMapAt_apply_of_mem (R := ℝ) hbase _)
  filter_upwards [hf.continuousWithinAt.preimage_mem_nhdsWithin (e.open_baseSet.mem_nhds hbase)]
    with z hz
  exact hwdef ▸ e.continuousLinearMapAt_apply_of_mem (R := ℝ) hz _

/-- **The mixed covariant derivative within a product set, read in the chart at the point.** -/
private theorem alongCurveWithin_alongCurveWithin_eq_symmL {s₁ s₂ : Set ℝ}
    (hs₁ : UniqueDiffOn ℝ s₁) (hs₂ : UniqueDiffOn ℝ s₂) (hu : u ∈ s₁) (hv : v ∈ s₂)
    (hW : ContMDiffWithinAt 𝓘(ℝ, ℝ × ℝ) I.tangent 2
      (fun z : ℝ × ℝ ↦ TotalSpace.mk' E (f z.1 z.2) (W z.1 z.2)) (s₁ ×ˢ s₂) (u, v))
    {φ w : ℝ × ℝ → E} (hφdef : φ = fun z ↦ extChartAt I (f u v) (f z.1 z.2))
    (hwdef : w = fun z ↦ (trivializationAt E (TangentSpace I) (f u v)).continuousLinearMapAt ℝ
      (f z.1 z.2) (W z.1 z.2)) :
    letI e := trivializationAt E (TangentSpace I) (f u v)
    letI Γ := christoffelMap (finBasis ℝ E) (cov.isCovariantDerivativeOn (s := e.baseSet))
    alongCurveWithin cov (fun q ↦ f q v) (fun q ↦ alongCurveWithin cov (f q) (W q) s₂ v) s₁ u =
      e.symmL ℝ (f u v)
        (derivWithin (fun q ↦ derivWithin (fun r ↦ w (q, r)) s₂ v) s₁ u +
          (mvfderiv I Γ (f u v) (curveVelocityWithin I (fun q ↦ f q v) s₁ u) (w (u, v))
              (derivWithin (fun r ↦ φ (u, r)) s₂ v) +
            Γ (f u v) (derivWithin (fun q ↦ w (q, v)) s₁ u)
              (derivWithin (fun r ↦ φ (u, r)) s₂ v) +
            Γ (f u v) (w (u, v))
              (derivWithin (fun q ↦ derivWithin (fun r ↦ φ (q, r)) s₂ v) s₁ u)) +
          Γ (f u v) (derivWithin (fun r ↦ w (u, r)) s₂ v +
              Γ (f u v) (w (u, v)) (derivWithin (fun r ↦ φ (u, r)) s₂ v))
            (derivWithin (fun q ↦ φ (q, v)) s₁ u)) := by
  set e := trivializationAt E (TangentSpace I) (f u v)
  have hcov := cov.isCovariantDerivativeOn (s := e.baseSet)
  set Γ := christoffelMap (finBasis ℝ E) hcov
  have : ContMDiffCovariantDerivativeOn E ∞ cov.toFun e.baseSet :=
    contMDiffCovariantDerivativeOn_of_isOpen (n := ∞) cov e.open_baseSet
  have : IsManifold I (∞ + 1 + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  have : ContMDiffVectorBundle (∞ + 1) E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  have hbase : f u v ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) _
  have hΓ : MDifferentiableAt I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E) Γ (f u v) :=
    ((contMDiffOn_christoffelMap (n := ∞) (finBasis ℝ E) hcov).contMDiffAt
      (e.open_baseSet.mem_nhds hbase)).mdifferentiableAt (by simp)
  obtain ⟨hf, hφ, hw⟩ := contDiffWithinAt_extChartAt_and_coord hW hφdef hwdef
  have hinner := sectionCoord_alongCurveWithin_eventuallyEq cov hu hv hW hφdef hwdef
  have hfu : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I (fun q ↦ f q v) s₁ u :=
    (hf.comp u ((contDiff_prodMk_left (n := 2) v).contMDiff.contMDiffAt.contMDiffWithinAt (s := s₁))
      fun q hq ↦ Set.mk_mem_prod hq hv).mdifferentiableWithinAt (by norm_num)
  have hΓq : HasDerivWithinAt (fun q ↦ Γ (f q v))
      (mvfderiv I Γ (f u v) (curveVelocityWithin I (fun q ↦ f q v) s₁ u)) s₁ u :=
    hasDerivWithinAt_comp_curve hΓ (hasMFDerivWithinAt_curveVelocityWithin hfu)
  have hw₁ : HasDerivWithinAt (fun q ↦ w (q, v)) (derivWithin (fun q ↦ w (q, v)) s₁ u) s₁ u :=
    ((hw.differentiableWithinAt (by norm_num)).comp u
      ((differentiableAt_id.prodMk (differentiableAt_const v)).differentiableWithinAt (s := s₁))
      fun q hq ↦ Set.mk_mem_prod hq hv).hasDerivWithinAt
  have hA : HasDerivWithinAt
      (fun q ↦ derivWithin (fun r ↦ w (q, r)) s₂ v +
        Γ (f q v) (w (q, v)) (derivWithin (fun r ↦ φ (q, r)) s₂ v)) _ s₁ u :=
    (hasDerivWithinAt_derivWithin_snd hs₁ hs₂ hu hv hw).differentiableWithinAt
      |>.hasDerivWithinAt.add ((hΓq.clm_apply hw₁).clm_apply
        (hasDerivWithinAt_derivWithin_snd hs₁ hs₂ hu hv hφ).differentiableWithinAt.hasDerivWithinAt)
  have hinner_u := mem_of_mem_nhdsWithin hu hinner
  rw [alongCurveWithin_apply, alongCurveInChartWithin_apply, hinner.derivWithin_eq hinner_u,
    hinner_u, hA.derivWithin (hs₁ u hu), Function.comp_def, add_apply, hφdef]

/-- **Mixed within-set covariant derivatives commute up to curvature.** Let `s₁` and `s₂` have
unique derivatives, let `u ∈ s₁` and `v ∈ s₂` lie in the closures of the interiors of `s₁` and
`s₂`, and let `W` be a field along `f` whose lift to the tangent bundle is `C²` within `s₁ ×ˢ s₂`
at `(u, v)`. Then `D_q D_r W - D_r D_q W = R(∂_q f, ∂_r f) W`, with all covariant derivatives and
velocities taken within `s₁` and `s₂`. -/
theorem alongCurveWithin_alongCurveWithin_sub_alongCurveWithin_alongCurveWithin {s₁ s₂ : Set ℝ}
    (hs₁ : UniqueDiffOn ℝ s₁) (hs₂ : UniqueDiffOn ℝ s₂) (hu : u ∈ s₁) (hv : v ∈ s₂)
    (hu_cls : u ∈ closure (interior s₁)) (hv_cls : v ∈ closure (interior s₂))
    (hW : ContMDiffWithinAt 𝓘(ℝ, ℝ × ℝ) I.tangent 2
      (fun z : ℝ × ℝ ↦ TotalSpace.mk' E (f z.1 z.2) (W z.1 z.2)) (s₁ ×ˢ s₂) (u, v)) :
    alongCurveWithin cov (fun q ↦ f q v) (fun q ↦ alongCurveWithin cov (f q) (W q) s₂ v) s₁ u -
        alongCurveWithin cov (f u)
          (fun r ↦ alongCurveWithin cov (fun q ↦ f q r) (fun q ↦ W q r) s₁ u) s₂ v =
      cov.curvatureTensor (f u v) (curveVelocityWithin I (fun q ↦ f q v) s₁ u)
        (curveVelocityWithin I (f u) s₂ v) (W u v) := by
  have hW' : ContMDiffWithinAt 𝓘(ℝ, ℝ × ℝ) I.tangent 2
      (fun z : ℝ × ℝ ↦ TotalSpace.mk' E (f z.2 z.1) (W z.2 z.1)) (s₂ ×ˢ s₁) (v, u) :=
    hW.comp (v, u)
      ((by fun_prop : ContDiff ℝ 2 fun z : ℝ × ℝ ↦ (z.2, z.1)
        ).contMDiff.contMDiffAt.contMDiffWithinAt (s := s₂ ×ˢ s₁))
      fun _ hz ↦ Set.mk_mem_prod hz.2 hz.1
  set e := trivializationAt E (TangentSpace I) (f u v)
  set φ : ℝ × ℝ → E := fun z ↦ extChartAt I (f u v) (f z.1 z.2) with hφdef
  set w : ℝ × ℝ → E := fun z ↦ e.continuousLinearMapAt ℝ (f z.1 z.2) (W z.1 z.2) with hwdef
  rw [alongCurveWithin_alongCurveWithin_eq_symmL cov hs₁ hs₂ hu hv hW hφdef hwdef,
    alongCurveWithin_alongCurveWithin_eq_symmL cov (f := fun a b ↦ f b a) (W := fun a b ↦ W b a)
      (u := v) (v := u) hs₂ hs₁ hv hu hW' (φ := fun z ↦ φ (z.2, z.1)) (w := fun z ↦ w (z.2, z.1))
      rfl rfl]
  dsimp only
  have hbase : f u v ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) _
  obtain ⟨hf, hφ, hw⟩ := contDiffWithinAt_extChartAt_and_coord hW hφdef hwdef
  have hvel {γ : ℝ → M} {s : Set ℝ} {t : ℝ} (hγt : γ t ∈ e.baseSet) (hst : UniqueDiffWithinAt ℝ s t)
      (hγ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ s t) :
      curveVelocityWithin I γ s t =
        e.symmL ℝ (γ t) (derivWithin (fun r ↦ extChartAt I (f u v) (γ r)) s t) := by
    have h := derivWithin_extChartAt_comp (x := f u v) γ hγt hst
      (hasMFDerivWithinAt_curveVelocityWithin hγ)
    rw [Function.comp_def] at h
    rw [h, e.symmL_continuousLinearMapAt (R := ℝ) hγt]
  have hWuv : W u v = e.symmL ℝ (f u v) (w (u, v)) :=
    (e.symmL_continuousLinearMapAt (R := ℝ) hbase _).symm
  rw [hvel (γ := fun q ↦ f q v) hbase (hs₁ u hu)
      ((hf.comp u (contDiff_prodMk_left (n := 2) v).contMDiff.contMDiffAt.contMDiffWithinAt
        fun q hq ↦ Set.mk_mem_prod hq hv).mdifferentiableWithinAt (by norm_num)),
    hvel (γ := f u) hbase (hs₂ v hv)
      ((hf.comp v (contDiff_prodMk_right (n := 2) u).contMDiff.contMDiffAt.contMDiffWithinAt
        fun r hr ↦ Set.mk_mem_prod hu hr).mdifferentiableWithinAt (by norm_num)), hWuv]
  simp only [e.symmL_apply (R := ℝ) hbase]
  rw [curvatureTensor_symm_trivializationAt cov (finBasis ℝ E) (f u v) (mem_extChartAt_source _),
    ← map_sub, e.symmL_apply (R := ℝ) hbase,
    ← derivWithin_derivWithin_comm hs₁ hs₂ hu hv hu_cls hv_cls hw,
    ← derivWithin_derivWithin_comm hs₁ hs₂ hu hv hu_cls hv_cls hφ]
  congr 1
  simp only [hφdef, map_add, add_apply]
  abel

/-- **Mixed covariant derivatives commute up to curvature.** For a `C²` vector field `W` along a
parametrized surface `f`, the covariant derivative along the first-parameter curves of the
covariant derivatives along the second-parameter curves, minus the same derivatives taken in the
other order, is the curvature: `D_q D_r W - D_r D_q W = R(∂_q f, ∂_r f) W`. No metric or torsion
hypothesis on the connection is needed. -/
theorem alongCurve_alongCurve_sub_alongCurve_alongCurve
    (hW : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I.tangent 2
      (fun z : ℝ × ℝ ↦ TotalSpace.mk' E (f z.1 z.2) (W z.1 z.2)) (u, v)) :
    alongCurve cov (fun q ↦ f q v) (fun q ↦ alongCurve cov (f q) (W q) v) u -
        alongCurve cov (f u) (fun r ↦ alongCurve cov (fun q ↦ f q r) (fun q ↦ W q r) u) v =
      cov.curvatureTensor (f u v) (curveVelocity I (fun q ↦ f q v) u) (curveVelocity I (f u) v)
        (W u v) := by
  simpa only [alongCurveWithin_univ, curveVelocityWithin_univ] using
    alongCurveWithin_alongCurveWithin_sub_alongCurveWithin_alongCurveWithin cov
      uniqueDiffOn_univ uniqueDiffOn_univ (mem_univ u) (mem_univ v) (by simp) (by simp)
      (by rwa [univ_prod_univ, contMDiffWithinAt_univ])

end CovariantDerivative
