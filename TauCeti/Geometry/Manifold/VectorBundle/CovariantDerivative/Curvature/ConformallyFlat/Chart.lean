/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Flat
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.ConformallyFlat.Basic
import TauCeti.Geometry.Manifold.ContMDiff.Log
import TauCeti.Geometry.Manifold.ContMDiffMap.Extension
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic

/-!
# Conformal Euclidean coordinate charts and locally conformally flat metrics

Classically, a smooth Riemannian metric `g` on an `n`-dimensional manifold `M` is locally
conformally flat if around every point there is a smooth coordinate chart into `ℝⁿ` in which `g` is
a positive smooth multiple of the Euclidean metric. In
`TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.ConformallyFlat.Basic`,
`Bundle.ContMDiffRiemannianMetric.IsLocallyConformallyFlat` is instead defined intrinsically: every
point has a neighbourhood on which a global conformal rescaling `f g` has vanishing Riemann
curvature tensor.

This file proves the equivalence of the two descriptions, together with the locality and pullback
invariance of `IsLocallyConformallyFlat`:

* **Transport along local Riemannian isometries**: if an open neighbourhood `(W, g|_W)` of `x`
  admits a local Riemannian isometry into a locally conformally flat manifold `(N, g_N)`, then `g`
  admits a global positive smooth factor flattening it near `x`
  (`exists_eventually_curvatureTensor_rescale_eq_zero_of_isLocalRiemannianIsometry`). Extending the
  logarithm of the pulled-back factor by a smooth bump function keeps the factor positive everywhere
  while preserving its germ at `x`. Consequently `IsLocallyConformallyFlat` restricts to open
  submanifolds, is local on open covers, and pulls back along local diffeomorphisms and
  diffeomorphisms.
* **From `IsLocallyConformallyFlat` to conformal Euclidean charts**: if `f g` has vanishing
  curvature near an interior point `x₀`, the local flatness theorem
  `TauCeti.exists_riemannianIsometry_ball_of_eventually_curvatureTensor_eq_zero_of_isInteriorPoint`
  produces a Riemannian isometry from `(W, (f g)|_W)` onto an open ball `B(0, r)` in any real
  inner-product space `F` of the same dimension. Packaging that diffeomorphism as a
  `PartialDiffeomorph` gives a chart `e` sending `x₀` to `0` on which `g = f⁻¹ (e^* g_Eucl)`.
* **From conformal Euclidean charts to `IsLocallyConformallyFlat`**: if around every point `x` there
  is a partial diffeomorphism `e` into `F` on whose source `g = c (e^* g_Eucl)` for a smooth
  positive function `c`, extending `log (c ∘ e⁻¹)` near `e x` to a global smooth function on `F`
  expresses `g` near `x` as locally isometric to a conformally rescaled Euclidean metric on `F`,
  which is locally conformally flat by
  `TauCeti.Manifold.isLocallyConformallyFlat_rescale_model_space`.

## Main results

In `Bundle.ContMDiffRiemannianMetric`:

* `exists_eventually_curvatureTensor_rescale_eq_zero_of_isLocalRiemannianIsometry`: local-isometry
  transport of conformal flatness at a point.
* `IsLocallyConformallyFlat.restrictOpenTangentSpace` and
  `isLocallyConformallyFlat_iff_forall_exists_opens`: restriction to open submanifolds and
  open-cover locality.
* `IsLocallyConformallyFlat.pullback_of_isInvertible` and `IsLocallyConformallyFlat.pullback`:
  pullback invariance along local diffeomorphisms and diffeomorphisms.
* `IsLocallyConformallyFlat.exists_partialDiffeomorph_ball_of_isInteriorPoint` and
  `IsLocallyConformallyFlat.exists_partialDiffeomorph_ball`: conformal Euclidean-ball charts around
  interior points (and around all points of a boundaryless manifold).
* `isLocallyConformallyFlat_of_forall_exists_partialDiffeomorph`: conformal charts into a real
  inner-product space imply `IsLocallyConformallyFlat` (without any boundaryless assumption).
* `isLocallyConformallyFlat_iff_forall_exists_partialDiffeomorph` and
  `isLocallyConformallyFlat_iff_forall_exists_partialDiffeomorph_ball`: equivalence between
  `IsLocallyConformallyFlat` and conformal Euclidean coordinate charts on boundaryless manifolds.

## References

* A. L. Besse, *Einstein Manifolds*, Springer (1987), Section 1.G.
* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), 37–91,
  Section 2.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 7.
-/

public section

open Bundle Filter Function Set TopologicalSpace TauCeti.Manifold
open scoped ContDiff InnerProductSpace Manifold Topology

noncomputable section

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]

/-! ### Locality and pullback invariance of `IsLocallyConformallyFlat` -/

/-- Vanishing of the Riemann curvature tensor is preserved and reflected by a local Riemannian
isometry. -/
private theorem curvatureTensor_eq_zero_iff_of_isLocalRiemannianIsometry
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [T2Space N] [IsManifold J ∞ N]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [RiemannianBundle (fun z : N ↦ TangentSpace J z)]
    [IsContMDiffRiemannianBundle J ∞ F (fun z : N ↦ TangentSpace J z)]
    {f : M → N} (hf : TauCeti.IsLocalRiemannianIsometry I J f) (x : M) :
    (CovariantDerivative.leviCivitaConnection J N).curvatureTensor (f x) = 0 ↔
      (CovariantDerivative.leviCivitaConnection I M).curvatureTensor x = 0 := by
  constructor
  · intro h
    ext u v w
    apply hf.mfderiv_injective x
    simp [hf.mfderiv_curvatureTensor, h]
  · intro h
    ext u v w
    obtain ⟨u, rfl⟩ := hf.mfderiv_surjective x u
    obtain ⟨v, rfl⟩ := hf.mfderiv_surjective x v
    obtain ⟨w, rfl⟩ := hf.mfderiv_surjective x w
    simp [← hf.mfderiv_curvatureTensor, h]

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- Rescaling both source and target metrics by compatible positive factors preserves a local
Riemannian isometry on a smaller open submanifold. -/
private theorem isLocalRiemannianIsometry_rescale_opens
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J 1 N]
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {W₁ W : Opens M} (hW₁W : W₁ ≤ W)
    (gN : ContMDiffRiemannianMetric J ∞ F (fun z : N ↦ TangentSpace J z))
    {f : W → N}
    (hf : letI : RiemannianBundle (fun y : W ↦ TangentSpace I y) :=
            ⟨(g.restrictOpenTangentSpace W).toRiemannianMetric⟩
          letI : RiemannianBundle (fun z : N ↦ TangentSpace J z) := ⟨gN.toRiemannianMetric⟩
          TauCeti.IsLocalRiemannianIsometry I J f)
    {c : M → ℝ} (hc : ContMDiff I 𝓘(ℝ) ∞ c) (hc_pos : ∀ y, 0 < c y)
    {h : N → ℝ} (hh : ContMDiff J 𝓘(ℝ) ∞ h) (hh_pos : ∀ z, 0 < h z)
    (hch : ∀ y : W₁, h (f (Opens.inclusion hW₁W y)) = c y.1) :
    letI : RiemannianBundle (fun y : W₁ ↦ TangentSpace I y) :=
      ⟨((g.rescale c hc hc_pos).restrictOpenTangentSpace W₁).toRiemannianMetric⟩
    letI : RiemannianBundle (fun z : N ↦ TangentSpace J z) :=
      ⟨(gN.rescale h hh hh_pos).toRiemannianMetric⟩
    TauCeti.IsLocalRiemannianIsometry I J (f ∘ Opens.inclusion hW₁W) := by
  obtain ⟨hf_smooth, hf_inv, hf_inner⟩ : ContMDiff I J ∞ f ∧
      (∀ z : W, (mfderiv I J f z).IsInvertible) ∧
      ∀ (y : W₁) (u v : TangentSpace I y),
        gN.inner (f (Opens.inclusion hW₁W y))
          (mfderiv I J f (Opens.inclusion hW₁W y) (mfderiv I I (Opens.inclusion hW₁W) y u))
          (mfderiv I J f (Opens.inclusion hW₁W y) (mfderiv I I (Opens.inclusion hW₁W) y v)) =
        g.inner y.1 (tangentSpaceOpenEquiv (I := I) y u)
          (tangentSpaceOpenEquiv (I := I) y v) := by
    let _ : RiemannianBundle (fun z : W ↦ TangentSpace I z) :=
      ⟨(g.restrictOpenTangentSpace W).toRiemannianMetric⟩
    let _ : RiemannianBundle (fun z : N ↦ TangentSpace J z) := ⟨gN.toRiemannianMetric⟩
    refine ⟨hf.contMDiff, hf.isInvertible_mfderiv, fun y u v ↦ ?_⟩
    have hteq (w : TangentSpace I y) :
        tangentSpaceOpenEquiv (I := I) (Opens.inclusion hW₁W y)
            (mfderiv I I (Opens.inclusion hW₁W) y w) =
          tangentSpaceOpenEquiv (I := I) y w := by
      simpa only [mfderiv_id, ContinuousLinearMap.id_apply] using
        tangentSpaceOpenEquiv_mfderiv_apply (A := id)
          ((contMDiff_inclusion (n := ∞) hW₁W).mdifferentiableAt (by simp)) rfl w
    have h₀ := hf.inner_mfderiv (Opens.inclusion hW₁W y)
      (mfderiv I I (Opens.inclusion hW₁W) y u) (mfderiv I I (Opens.inclusion hW₁W) y v)
    rwa [inner_riemannianBundle gN, inner_riemannianBundle (g.restrictOpenTangentSpace W),
      restrictOpenTangentSpace_inner, hteq u, hteq v] at h₀
  let _ : RiemannianBundle (fun y : W₁ ↦ TangentSpace I y) :=
    ⟨((g.rescale c hc hc_pos).restrictOpenTangentSpace W₁).toRiemannianMetric⟩
  let _ : RiemannianBundle (fun z : N ↦ TangentSpace J z) :=
    ⟨(gN.rescale h hh hh_pos).toRiemannianMetric⟩
  have hmf (y : W₁) :
      mfderiv I J (f ∘ Opens.inclusion hW₁W) y =
        (mfderiv I J f (Opens.inclusion hW₁W y)).comp (mfderiv I I (Opens.inclusion hW₁W) y) :=
    mfderiv_comp y (hf_smooth.mdifferentiableAt (by simp))
      ((contMDiff_inclusion (n := ∞) hW₁W).mdifferentiableAt (by simp))
  refine
    { contMDiff := hf_smooth.comp (contMDiff_inclusion hW₁W)
      isInvertible_mfderiv := fun y ↦ by
        obtain ⟨e_f, he_f⟩ := hf_inv (Opens.inclusion hW₁W y)
        refine ⟨(ContinuousLinearEquiv.refl ℝ (TangentSpace I y)).trans e_f, ?_⟩
        ext v
        rw [hmf y, ContinuousLinearMap.comp_apply, mfderiv_inclusion_apply, ← he_f]
        rfl
      inner_mfderiv := fun y u v ↦ ?_ }
  rw [inner_riemannianBundle (gN.rescale h hh hh_pos),
    inner_riemannianBundle ((g.rescale c hc hc_pos).restrictOpenTangentSpace W₁)]
  simp only [Function.comp_apply, rescale_inner, restrictOpenTangentSpace_inner, hmf y,
    ContinuousLinearMap.comp_apply, hch y]
  rw [hf_inner y u v]

/-- **Transporting conformal flatness along a local Riemannian isometry.** If an open neighbourhood
`(W, g|_W)` of `x` admits a local Riemannian isometry `f : W → N` into `(N, g_N)` and `g_N` is
locally conformally flat, then `g` admits a globally smooth positive factor `c : M → ℝ` whose
rescaling `c g` is flat near `x`. -/
theorem exists_eventually_curvatureTensor_rescale_eq_zero_of_isLocalRiemannianIsometry
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [T2Space N] [IsManifold J ∞ N]
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {W : Opens M} {x : M} (hxW : x ∈ W)
    (gN : ContMDiffRiemannianMetric J ∞ F (fun z : N ↦ TangentSpace J z))
    (hgN : gN.IsLocallyConformallyFlat) {f : W → N}
    (hf : letI : RiemannianBundle (fun y : W ↦ TangentSpace I y) :=
            ⟨(g.restrictOpenTangentSpace W).toRiemannianMetric⟩
          letI : RiemannianBundle (fun z : N ↦ TangentSpace J z) := ⟨gN.toRiemannianMetric⟩
          TauCeti.IsLocalRiemannianIsometry I J f) :
    ∃ (c : M → ℝ) (hc : ContMDiff I 𝓘(ℝ) ∞ c) (hc_pos : ∀ y, 0 < c y),
      ∀ᶠ y in 𝓝 x, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
          ⟨(g.rescale c hc hc_pos).toRiemannianMetric⟩;
        (CovariantDerivative.leviCivitaConnection I M).curvatureTensor y) = 0 := by
  have hf_smooth : ContMDiff I J ∞ f :=
    letI : RiemannianBundle (fun y : W ↦ TangentSpace I y) :=
      ⟨(g.restrictOpenTangentSpace W).toRiemannianMetric⟩
    letI : RiemannianBundle (fun z : N ↦ TangentSpace J z) := ⟨gN.toRiemannianMetric⟩
    hf.contMDiff
  obtain ⟨h, hh, hh_pos, hflat_N⟩ := (gN.isLocallyConformallyFlat_iff).1 hgN (f ⟨x, hxW⟩)
  let lW : W → ℝ := fun y ↦ Real.log (h (f y))
  have hlW : ContMDiff I 𝓘(ℝ) ∞ lW := (hh.comp hf_smooth).log fun y ↦ (hh_pos (f y)).ne'
  obtain ⟨G, hG_eq⟩ :=
    (ContMDiffMap.contMDiffOn_extend W ⟨lW, hlW⟩ 0).exists_contMDiffMap_eventuallyEq
      (n := (⊤ : ℕ∞)) (W.isOpen.mem_nhds hxW)
  let c (y : M) : ℝ := Real.exp (G y)
  have hc : ContMDiff I 𝓘(ℝ) ∞ c := Real.contDiff_exp.comp_contMDiff G.contMDiff
  have hc_pos (y : M) : 0 < c y := Real.exp_pos _
  obtain ⟨U_W, hUW_flat, hUW_open, hxUW⟩ :=
    eventually_nhds_iff.1 (hf_smooth.continuous.continuousAt.eventually hflat_N)
  have hU_M : Subtype.val '' U_W ∈ 𝓝 x :=
    (W.isOpen.isOpenMap_subtype_val U_W hUW_open).mem_nhds ⟨⟨x, hxW⟩, hxUW, rfl⟩
  obtain ⟨V, hV_sub, hV_open, hxV⟩ :=
    eventually_nhds_iff.1 ((hG_eq.and (W.isOpen.mem_nhds hxW)).and hU_M)
  let W₁ : Opens M := ⟨V, hV_open⟩
  have hW₁W : W₁ ≤ W := fun y hy ↦ (hV_sub y hy).1.2
  let g₁ := g.rescale c hc hc_pos
  let gN₁ := gN.rescale h hh hh_pos
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g₁.toRiemannianMetric⟩
  have : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) :=
    ⟨g₁.inner, g₁.contMDiff, fun _ _ _ ↦ rfl⟩
  let _ : RiemannianBundle (fun y : W₁ ↦ TangentSpace I y) :=
    ⟨(g₁.restrictOpenTangentSpace W₁).toRiemannianMetric⟩
  have : IsContMDiffRiemannianBundle I ∞ E (fun y : W₁ ↦ TangentSpace I y) :=
    ⟨(g₁.restrictOpenTangentSpace W₁).inner, (g₁.restrictOpenTangentSpace W₁).contMDiff,
      fun _ _ _ ↦ rfl⟩
  let _ : RiemannianBundle (fun z : N ↦ TangentSpace J z) := ⟨gN₁.toRiemannianMetric⟩
  have : IsContMDiffRiemannianBundle J ∞ F (fun z : N ↦ TangentSpace J z) :=
    ⟨gN₁.inner, gN₁.contMDiff, fun _ _ _ ↦ rfl⟩
  have hf₁ := isLocalRiemannianIsometry_rescale_opens g hW₁W gN hf hc hc_pos hh hh_pos fun y ↦ by
    have hGy : G y.1 = extend Subtype.val lW 0 y.1 := (hV_sub y.1 y.2).1.1
    have hext : extend Subtype.val lW 0 y.1 = lW (Opens.inclusion hW₁W y) :=
      congrFun (extend_comp Subtype.val_injective lW 0) (Opens.inclusion hW₁W y)
    simp only [c, hGy, hext, lW, Real.exp_log (hh_pos _)]
  refine ⟨c, hc, hc_pos, eventually_of_mem (hV_open.mem_nhds hxV) fun y hy ↦ ?_⟩
  obtain ⟨y', hy'UW, hy'eq⟩ := (hV_sub y hy).2
  have hyW₁ : Opens.inclusion hW₁W ⟨y, hy⟩ ∈ U_W :=
    (Subtype.ext hy'eq : y' = Opens.inclusion hW₁W ⟨y, hy⟩) ▸ hy'UW
  exact (curvatureTensor_eq_zero_iff_of_isLocalRiemannianIsometry
      (g₁.isLocalRiemannianIsometry_restrictOpenTangentSpace W₁) ⟨y, hy⟩).2
    ((curvatureTensor_eq_zero_iff_of_isLocalRiemannianIsometry hf₁ ⟨y, hy⟩).1 (hUW_flat _ hyW₁))

/-- Restricting a locally conformally flat metric to an open submanifold yields a locally
conformally flat metric. -/
theorem IsLocallyConformallyFlat.restrictOpenTangentSpace
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    (hg : g.IsLocallyConformallyFlat) (U : Opens M) :
    (g.restrictOpenTangentSpace U).IsLocallyConformallyFlat := by
  rw [(g.restrictOpenTangentSpace U).isLocallyConformallyFlat_iff]
  intro x
  obtain ⟨f, hf, hf_pos, hflat⟩ := (g.isLocallyConformallyFlat_iff).1 hg x.1
  let fU : U → ℝ := f ∘ Subtype.val
  have hfU : ContMDiff I 𝓘(ℝ) ∞ fU := hf.comp contMDiff_subtype_val
  have hfU_pos (y : U) : 0 < fU y := hf_pos y.1
  have hres_eq : (g.restrictOpenTangentSpace U).rescale fU hfU hfU_pos =
      (g.rescale f hf hf_pos).restrictOpenTangentSpace U := by
    ext y v w
    simp only [fU, Function.comp_apply, rescale_inner, restrictOpenTangentSpace_inner]
  refine ⟨fU, hfU, hfU_pos, (continuous_subtype_val.continuousAt.eventually hflat).mono
    fun y hy ↦ ?_⟩
  let g₁ := g.rescale f hf hf_pos
  let _ : RiemannianBundle (fun z : M ↦ TangentSpace I z) := ⟨g₁.toRiemannianMetric⟩
  have : IsContMDiffRiemannianBundle I ∞ E (fun z : M ↦ TangentSpace I z) :=
    ⟨g₁.inner, g₁.contMDiff, fun _ _ _ ↦ rfl⟩
  let _ : RiemannianBundle (fun z : U ↦ TangentSpace I z) :=
    ⟨(g₁.restrictOpenTangentSpace U).toRiemannianMetric⟩
  have : IsContMDiffRiemannianBundle I ∞ E (fun z : U ↦ TangentSpace I z) :=
    ⟨(g₁.restrictOpenTangentSpace U).inner, (g₁.restrictOpenTangentSpace U).contMDiff,
      fun _ _ _ ↦ rfl⟩
  exact (curvatureTensor_leviCivitaConnection_eq_of_riemannianBundle_eq
    (by rw [hres_eq]; rfl) y).trans
    ((curvatureTensor_eq_zero_iff_of_isLocalRiemannianIsometry
      (g₁.isLocalRiemannianIsometry_restrictOpenTangentSpace U) y).1 hy)

/-- **Locality of `IsLocallyConformallyFlat` on open covers.** A smooth Riemannian metric `g` is
locally conformally flat if and only if every point belongs to an open subset `W` on which the
restricted metric `g|_W` is locally conformally flat. -/
theorem isLocallyConformallyFlat_iff_forall_exists_opens
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) :
    g.IsLocallyConformallyFlat ↔
      ∀ x : M, ∃ W : Opens M, x ∈ W ∧ (g.restrictOpenTangentSpace W).IsLocallyConformallyFlat := by
  refine ⟨fun hg x ↦ ⟨⊤, trivial, hg.restrictOpenTangentSpace ⊤⟩, fun h ↦ ?_⟩
  rw [g.isLocallyConformallyFlat_iff]
  intro x
  obtain ⟨W, hxW, hgW⟩ := h x
  exact g.exists_eventually_curvatureTensor_rescale_eq_zero_of_isLocalRiemannianIsometry hxW
    (g.restrictOpenTangentSpace W) hgW
    (letI : RiemannianBundle (fun y : W ↦ TangentSpace I y) :=
      ⟨(g.restrictOpenTangentSpace W).toRiemannianMetric⟩
     TauCeti.IsLocalRiemannianIsometry.id I W)

/-- Pulling back a locally conformally flat metric along a smooth map whose differential is
invertible at every point yields a locally conformally flat metric. -/
theorem IsLocallyConformallyFlat.pullback_of_isInvertible
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [T2Space N] [IsManifold J ∞ N]
    {gN : ContMDiffRiemannianMetric J ∞ F (fun z : N ↦ TangentSpace J z)}
    (hgN : gN.IsLocallyConformallyFlat) {f : M → N} (hf : ContMDiff I J ∞ f)
    (hinv : ∀ x, (mfderiv I J f x).IsInvertible) :
    (gN.pullback f (by simpa using hf) fun x ↦ (hinv x).injective).IsLocallyConformallyFlat := by
  rw [isLocallyConformallyFlat_iff]
  intro x
  obtain ⟨h, hh, hh_pos, hflat⟩ := (gN.isLocallyConformallyFlat_iff).1 hgN (f x)
  have hhf : ContMDiff I 𝓘(ℝ) ∞ (h ∘ f) := hh.comp hf
  have hhf_pos (y : M) : 0 < (h ∘ f) y := hh_pos (f y)
  have hinj : ∀ y, Injective (mfderiv I J f y) := fun y ↦ (hinv y).injective
  have hpull_eq : (gN.pullback f (by simpa using hf) hinj).rescale (h ∘ f) hhf hhf_pos =
      (gN.rescale h hh hh_pos).pullback f (by simpa using hf) hinj := by
    ext y u v
    simp
  refine ⟨h ∘ f, hhf, hhf_pos, (hf.continuous.continuousAt.eventually hflat).mono fun y hy ↦ ?_⟩
  let gN₁ := gN.rescale h hh hh_pos
  let gM₁ := gN₁.pullback f (by simpa using hf) hinj
  let _ : RiemannianBundle (fun z : N ↦ TangentSpace J z) := ⟨gN₁.toRiemannianMetric⟩
  have : IsContMDiffRiemannianBundle J ∞ F (fun z : N ↦ TangentSpace J z) :=
    ⟨gN₁.inner, gN₁.contMDiff, fun _ _ _ ↦ rfl⟩
  let _ : RiemannianBundle (fun z : M ↦ TangentSpace I z) := ⟨gM₁.toRiemannianMetric⟩
  have : IsContMDiffRiemannianBundle I ∞ E (fun z : M ↦ TangentSpace I z) :=
    ⟨gM₁.inner, gM₁.contMDiff, fun _ _ _ ↦ rfl⟩
  have hiso : TauCeti.IsLocalRiemannianIsometry I J f :=
    gN₁.isLocalRiemannianIsometry_pullback_of_isInvertible hf hinv
  exact (curvatureTensor_leviCivitaConnection_eq_of_riemannianBundle_eq
    (by rw [hpull_eq]; rfl) y).trans
    ((curvatureTensor_eq_zero_iff_of_isLocalRiemannianIsometry hiso y).1 hy)

/-- Pulling back a locally conformally flat metric along a diffeomorphism preserves local conformal
flatness. -/
theorem IsLocallyConformallyFlat.pullback
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [T2Space N] [IsManifold J ∞ N]
    {gN : ContMDiffRiemannianMetric J ∞ F (fun z : N ↦ TangentSpace J z)}
    (hgN : gN.IsLocallyConformallyFlat) (Φ : M ≃ₘ^∞⟮I, J⟯ N) :
    (gN.pullback Φ (by simpa using Φ.contMDiff)
      fun _ ↦ (Φ.isInvertible_mfderiv (by simp)).injective).IsLocallyConformallyFlat :=
  hgN.pullback_of_isInvertible Φ.contMDiff fun _ ↦ Φ.isInvertible_mfderiv (by simp)

/-! ### Conformal Euclidean coordinate charts -/

/-- Package a smooth diffeomorphism `d : W ≃ₘ B` between open subsets of `M` and `F` as an ambient
`PartialDiffeomorph` with exact source `W` and target `B`. -/
private def partialDiffeomorphOfDiffeomorphOpens {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {W : Opens M} {B : Opens F} (x₀ : M) (d : W ≃ₘ^∞⟮I, 𝓘(ℝ, F)⟯ B) :
    PartialDiffeomorph I 𝓘(ℝ, F) M F ∞ where
  toPartialEquiv :=
    { toFun := extend Subtype.val (Subtype.val ∘ d) 0
      invFun := extend Subtype.val (Subtype.val ∘ d.symm) (fun _ ↦ x₀)
      source := W
      target := B
      map_source' := fun y hy ↦ by
        have h := congrFun (extend_comp Subtype.val_injective (Subtype.val ∘ d) 0) ⟨y, hy⟩
        simp only [Function.comp_apply] at h
        rw [h]
        exact (d ⟨y, hy⟩).2
      map_target' := fun z hz ↦ by
        have h := congrFun (extend_comp Subtype.val_injective
          (Subtype.val ∘ d.symm) (fun _ ↦ x₀)) ⟨z, hz⟩
        simp only [Function.comp_apply] at h
        rw [h]
        exact (d.symm ⟨z, hz⟩).2
      left_inv' := fun y hy ↦ by
        have h₁ := congrFun (extend_comp Subtype.val_injective (Subtype.val ∘ d) 0) ⟨y, hy⟩
        have h₂ := congrFun (extend_comp Subtype.val_injective
          (Subtype.val ∘ d.symm) (fun _ ↦ x₀)) (d ⟨y, hy⟩)
        simp only [Function.comp_apply] at h₁ h₂
        rw [h₁, h₂, d.symm_apply_apply]
      right_inv' := fun z hz ↦ by
        have h₁ := congrFun (extend_comp Subtype.val_injective
          (Subtype.val ∘ d.symm) (fun _ ↦ x₀)) ⟨z, hz⟩
        have h₂ := congrFun (extend_comp Subtype.val_injective
          (Subtype.val ∘ d) 0) (d.symm ⟨z, hz⟩)
        simp only [Function.comp_apply] at h₁ h₂
        rw [h₁, h₂, d.apply_symm_apply] }
  open_source := W.isOpen
  open_target := B.isOpen
  contMDiffOn_toFun := ContMDiffMap.contMDiffOn_extend W
    ⟨Subtype.val ∘ d, contMDiff_subtype_val.comp d.contMDiff⟩ 0
  contMDiffOn_invFun := ContMDiffMap.contMDiffOn_extend B
    ⟨Subtype.val ∘ d.symm, contMDiff_subtype_val.comp d.symm.contMDiff⟩ (fun _ ↦ x₀)

open scoped TauCeti in
/-- **Conformal Euclidean-ball charts around an interior point.** Let `g` be a locally conformally
flat metric on `M` and `F` a finite-dimensional real inner-product space of the same dimension as
`E`. Then inside any neighbourhood `U ∈ 𝓝 x₀` of an interior point `x₀`, there exist a radius
`r > 0`, a globally smooth positive function `c : M → ℝ`, and a smooth partial diffeomorphism
`e : PartialDiffeomorph I 𝓘(ℝ, F) M F ∞` with `x₀ ∈ e.source`, `e.source ⊆ U`,
`e.target = Metric.ball 0 r`, `e x₀ = 0`, and
`g.inner y u v = c y * ⟪mfderiv I 𝓘(ℝ, F) e y u, mfderiv I 𝓘(ℝ, F) e y v⟫_ℝ` on `e.source`. -/
theorem IsLocallyConformallyFlat.exists_partialDiffeomorph_ball_of_isInteriorPoint
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    (hg : g.IsLocallyConformallyFlat) (hdim : Module.finrank ℝ E = Module.finrank ℝ F)
    {x₀ : M} (hx₀ : I.IsInteriorPoint x₀) {U : Set M} (hU : U ∈ 𝓝 x₀) :
    ∃ (r : ℝ) (_ : 0 < r) (c : M → ℝ) (_ : ContMDiff I 𝓘(ℝ) ∞ c) (_ : ∀ y, 0 < c y)
      (e : PartialDiffeomorph I 𝓘(ℝ, F) M F ∞),
      x₀ ∈ e.source ∧ e.source ⊆ U ∧ e.target = Metric.ball 0 r ∧ e x₀ = 0 ∧
        ∀ y ∈ e.source, ∀ u v : TangentSpace I y,
          g.inner y u v = c y * ⟪mfderiv I 𝓘(ℝ, F) e y u, mfderiv I 𝓘(ℝ, F) e y v⟫_ℝ := by
  obtain ⟨f, hf, hf_pos, hflat⟩ := (g.isLocallyConformallyFlat_iff).1 hg x₀
  let g₁ := g.rescale f hf hf_pos
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g₁.toRiemannianMetric⟩
  have : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) :=
    ⟨g₁.inner, g₁.contMDiff, fun _ _ _ ↦ rfl⟩
  let L : TangentSpace I x₀ ≃ₗᵢ[ℝ] F :=
    (stdOrthonormalBasis ℝ (TangentSpace I x₀)).equiv (stdOrthonormalBasis ℝ F)
      (finCongr ((TauCeti.finrank_tangentSpace x₀).trans hdim))
  obtain ⟨W, hx₀W, r, hr, Ψ, hWU, hΨ0, -⟩ :=
    TauCeti.exists_riemannianIsometry_ball_of_eventually_curvatureTensor_eq_zero_of_isInteriorPoint
      hx₀ hflat hU L
  let B : Opens F := ⟨Metric.ball (0 : F) r, Metric.isOpen_ball⟩
  let e := partialDiffeomorphOfDiffeomorphOpens x₀ Ψ.toDiffeomorph
  have he_comp : (e : M → F) ∘ (Subtype.val : W → M) = (Subtype.val : B → F) ∘ Ψ :=
    extend_comp Subtype.val_injective (Subtype.val ∘ Ψ.toDiffeomorph) 0
  have hc : ContMDiff I 𝓘(ℝ) ∞ fun y ↦ (f y)⁻¹ := hf.inv₀ fun y ↦ (hf_pos y).ne'
  have hc_pos (y : M) : 0 < (f y)⁻¹ := inv_pos.2 (hf_pos y)
  refine ⟨r, hr, fun y ↦ (f y)⁻¹, hc, hc_pos, e, hx₀W, hWU, rfl,
    (congrFun he_comp ⟨x₀, hx₀W⟩).trans hΨ0, fun y hy u v ↦ ?_⟩
  let yW : W := ⟨y, hy⟩
  have hm (w : TangentSpace I yW) :
      mfderiv I 𝓘(ℝ, F) e y (tangentSpaceOpenEquiv (I := I) yW w) =
        tangentSpaceOpenEquiv (I := 𝓘(ℝ, F)) (Ψ yW) (mfderiv I 𝓘(ℝ, F) Ψ yW w) := by
    have he_diff : MDifferentiableAt I 𝓘(ℝ, F) e y :=
      (e.contMDiffOn.contMDiffAt (e.open_source.mem_nhds hy)).mdifferentiableAt (by simp)
    have h₁ :=
      mfderiv_comp_apply yW he_diff ((contMDiff_subtype_val (n := ∞)).mdifferentiableAt (by simp)) w
    have h₂ := mfderiv_comp_apply yW ((contMDiff_subtype_val (n := ∞)).mdifferentiableAt (by simp))
      (Ψ.mdifferentiableAt yW) w
    rw [mfderiv_subtype_val, ContinuousLinearEquiv.coe_coe] at h₁ h₂
    exact h₁.symm.trans ((congrFun (congrArg (fun k ↦ mfderiv I 𝓘(ℝ, F) k yW) he_comp) w).trans h₂)
  have hΨ_in := Ψ.inner_mfderiv yW ((tangentSpaceOpenEquiv (I := I) yW).symm u)
    ((tangentSpaceOpenEquiv (I := I) yW).symm v)
  rw [inner_tangentSpace_open B, ← hm, ← hm, inner_tangentSpace_open W,
    ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply] at hΨ_in
  have hg₁_in : RiemannianBundle.g.inner y u v = f y * g.inner y u v :=
    g.rescale_inner f hf hf_pos y u v
  rw [hg₁_in] at hΨ_in
  have hΨ_in' : ⟪mfderiv I 𝓘(ℝ, F) e y u, mfderiv I 𝓘(ℝ, F) e y v⟫_ℝ = f y * g.inner y u v :=
    hΨ_in
  rw [hΨ_in', inv_mul_cancel_left₀ (hf_pos y).ne']

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- A conformal partial diffeomorphism `e` into `F` induces a local Riemannian isometry on any open
subset `W ⊆ e.source` where `hF ∘ e = c`. -/
private theorem isLocalRiemannianIsometry_partialDiffeomorph_rescale
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (e : PartialDiffeomorph I 𝓘(ℝ, F) M F ∞) {W : Opens M} (hWe : (W : Set M) ⊆ e.source)
    {c : M → ℝ}
    (hinner : ∀ y ∈ e.source, ∀ u v : TangentSpace I y,
      g.inner y u v = c y * ⟪mfderiv I 𝓘(ℝ, F) e y u, mfderiv I 𝓘(ℝ, F) e y v⟫_ℝ)
    {hF : F → ℝ} (hhF : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ) ∞ hF) (hhF_pos : ∀ z, 0 < hF z)
    (hhe : ∀ y : W, hF (e y.1) = c y.1) :
    letI : RiemannianBundle (fun y : W ↦ TangentSpace I y) :=
      ⟨(g.restrictOpenTangentSpace W).toRiemannianMetric⟩
    letI : RiemannianBundle (fun z : F ↦ TangentSpace 𝓘(ℝ, F) z) :=
      ⟨(((riemannianMetricVectorSpace F).ofLE le_top).rescale hF hhF hhF_pos).toRiemannianMetric⟩
    TauCeti.IsLocalRiemannianIsometry I 𝓘(ℝ, F) (e ∘ (Subtype.val : W → M)) := by
  let gF := ((riemannianMetricVectorSpace F).ofLE le_top).rescale hF hhF hhF_pos
  let _ : RiemannianBundle (fun y : W ↦ TangentSpace I y) :=
    ⟨(g.restrictOpenTangentSpace W).toRiemannianMetric⟩
  let _ : RiemannianBundle (fun z : F ↦ TangentSpace 𝓘(ℝ, F) z) := ⟨gF.toRiemannianMetric⟩
  have hmf (y : W) :
      mfderiv I 𝓘(ℝ, F) (e ∘ (Subtype.val : W → M)) y =
        (mfderiv I 𝓘(ℝ, F) e y.1).comp
          (tangentSpaceOpenEquiv (I := I) y).toContinuousLinearMap := by
    rw [mfderiv_comp y
      ((e.contMDiffOn.contMDiffAt (e.open_source.mem_nhds (hWe y.2))).mdifferentiableAt (by simp))
      ((contMDiff_subtype_val (n := ∞)).mdifferentiableAt (by simp)), mfderiv_subtype_val]
  refine
    { contMDiff := fun y ↦
        (e.contMDiffOn.contMDiffAt (e.open_source.mem_nhds (hWe y.2))).comp y
          contMDiff_subtype_val.contMDiffAt
      isInvertible_mfderiv := fun y ↦ by
        obtain ⟨e_lin, he_lin⟩ :=
          (e.isLocalDiffeomorphAt I 𝓘(ℝ, F) ∞ (hWe y.2)).isInvertible_mfderiv (by simp)
        refine ⟨(tangentSpaceOpenEquiv (I := I) y).trans e_lin, ?_⟩
        rw [hmf y, ← he_lin]
        rfl
      inner_mfderiv := fun y u v ↦ ?_ }
  rw [inner_riemannianBundle gF, inner_riemannianBundle (g.restrictOpenTangentSpace W)]
  simp only [Function.comp_apply, gF, rescale_inner, ofLE_inner, hmf y,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, hhe y,
    restrictOpenTangentSpace_inner, hinner y.1 (hWe y.2)]
  rfl

/-- **Conformal charts into a real inner-product space imply local conformal flatness.** Suppose
every point `x : M` lies in the source of a smooth partial diffeomorphism `e` into `F` on which `g`
is a smooth positive multiple `c` of the pulled-back Euclidean metric. Then `g` is locally
conformally flat. No boundaryless assumption on `M` is needed. -/
theorem isLocallyConformallyFlat_of_forall_exists_partialDiffeomorph
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (h : ∀ x : M, ∃ (e : PartialDiffeomorph I 𝓘(ℝ, F) M F ∞) (c : M → ℝ),
      x ∈ e.source ∧ ContMDiffOn I 𝓘(ℝ) ∞ c e.source ∧ (∀ y ∈ e.source, 0 < c y) ∧
        ∀ y ∈ e.source, ∀ u v : TangentSpace I y,
          g.inner y u v = c y * ⟪mfderiv I 𝓘(ℝ, F) e y u, mfderiv I 𝓘(ℝ, F) e y v⟫_ℝ) :
    g.IsLocallyConformallyFlat := by
  rw [g.isLocallyConformallyFlat_iff]
  intro x
  obtain ⟨e, c, hx, hc_on, hc_pos, hinner⟩ := h x
  have hl_on : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ) ∞ (fun z ↦ Real.log (c (e.symm z))) e.target :=
    fun z hz ↦ (((hc_on.comp e.symm.contMDiffOn e.symm.mapsTo).contMDiffAt
      (e.open_target.mem_nhds hz)).log (hc_pos _ (e.map_target hz)).ne').contMDiffWithinAt
  obtain ⟨G, hG_eq⟩ := hl_on.exists_contMDiffMap_eventuallyEq (n := (⊤ : ℕ∞))
    (e.open_target.mem_nhds (e.map_source hx))
  let hF (z : F) : ℝ := Real.exp (G z)
  have hhF : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ) ∞ hF := Real.contDiff_exp.comp_contMDiff G.contMDiff
  have hhF_pos (z : F) : 0 < hF z := Real.exp_pos _
  obtain ⟨V_F, hVF_sub, hVF_open, hexVF⟩ :=
    eventually_nhds_iff.1 (hG_eq.and (e.open_target.mem_nhds (e.map_source hx)))
  let W : Opens M :=
    ⟨e.source ∩ e ⁻¹' V_F, e.contMDiffOn.continuousOn.isOpen_inter_preimage e.open_source hVF_open⟩
  have hf_iso := isLocalRiemannianIsometry_partialDiffeomorph_rescale g e
    (W := W) inter_subset_left hinner hhF hhF_pos fun y ↦ by
      have hGe : G (e y.1) = Real.log (c (e.symm (e y.1))) := (hVF_sub (e y.1) y.2.2).1
      have hleft : e.symm (e y.1) = y.1 := e.left_inv y.2.1
      simp only [hF, hGe, hleft, Real.exp_log (hc_pos y.1 y.2.1)]
  exact g.exists_eventually_curvatureTensor_rescale_eq_zero_of_isLocalRiemannianIsometry
    (W := W) ⟨hx, hexVF⟩ (((riemannianMetricVectorSpace F).ofLE le_top).rescale hF hhF hhF_pos)
    (isLocallyConformallyFlat_rescale_model_space hhF hhF_pos) hf_iso

section Boundaryless

variable [BoundarylessManifold I M]

/-- **Conformal Euclidean-ball charts on a boundaryless manifold.** -/
theorem IsLocallyConformallyFlat.exists_partialDiffeomorph_ball
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
    (hg : g.IsLocallyConformallyFlat) (hdim : Module.finrank ℝ E = Module.finrank ℝ F)
    {x₀ : M} {U : Set M} (hU : U ∈ 𝓝 x₀) :
    ∃ (r : ℝ) (_ : 0 < r) (c : M → ℝ) (_ : ContMDiff I 𝓘(ℝ) ∞ c) (_ : ∀ y, 0 < c y)
      (e : PartialDiffeomorph I 𝓘(ℝ, F) M F ∞),
      x₀ ∈ e.source ∧ e.source ⊆ U ∧ e.target = Metric.ball 0 r ∧ e x₀ = 0 ∧
        ∀ y ∈ e.source, ∀ u v : TangentSpace I y,
          g.inner y u v = c y * ⟪mfderiv I 𝓘(ℝ, F) e y u, mfderiv I 𝓘(ℝ, F) e y v⟫_ℝ :=
  hg.exists_partialDiffeomorph_ball_of_isInteriorPoint hdim BoundarylessManifold.isInteriorPoint hU

/-- **Conformal-chart characterization of local conformal flatness.** On a boundaryless smooth
manifold `M`, a metric `g` is locally conformally flat if and only if every point lies in the source
of a smooth partial diffeomorphism into a real inner-product space `F` of the same dimension on
which `g` is a smooth positive multiple of the pulled-back inner product. -/
theorem isLocallyConformallyFlat_iff_forall_exists_partialDiffeomorph
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) :
    g.IsLocallyConformallyFlat ↔
      ∀ x : M, ∃ (e : PartialDiffeomorph I 𝓘(ℝ, F) M F ∞) (c : M → ℝ),
        x ∈ e.source ∧ ContMDiffOn I 𝓘(ℝ) ∞ c e.source ∧ (∀ y ∈ e.source, 0 < c y) ∧
          ∀ y ∈ e.source, ∀ u v : TangentSpace I y,
            g.inner y u v = c y * ⟪mfderiv I 𝓘(ℝ, F) e y u, mfderiv I 𝓘(ℝ, F) e y v⟫_ℝ := by
  refine ⟨fun hg x ↦ ?_, g.isLocallyConformallyFlat_of_forall_exists_partialDiffeomorph⟩
  obtain ⟨_, -, c, hc, hc_pos, e, hx, -, -, -, hinner⟩ :=
    hg.exists_partialDiffeomorph_ball hdim univ_mem
  exact ⟨e, c, hx, hc.contMDiffOn, fun y _ ↦ hc_pos y, hinner⟩

/-- **Centred Euclidean-ball chart characterization of local conformal flatness.** On a boundaryless
smooth manifold `M`, a metric `g` is locally conformally flat if and only if around every point
`x : M` there exist `r > 0`, a globally smooth positive function `c : M → ℝ`, and a smooth partial
diffeomorphism `e` onto the open ball `B(0, r)` in `EuclideanSpace ℝ (Fin (Module.finrank ℝ E))`
sending `x` to `0` on which `g` is `c` times the pulled-back Euclidean inner product. -/
theorem isLocallyConformallyFlat_iff_forall_exists_partialDiffeomorph_ball
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) :
    g.IsLocallyConformallyFlat ↔
      ∀ x : M, ∃ (r : ℝ) (_ : 0 < r) (c : M → ℝ) (_ : ContMDiff I 𝓘(ℝ) ∞ c) (_ : ∀ y, 0 < c y)
        (e : PartialDiffeomorph I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) M
          (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) ∞),
        x ∈ e.source ∧ e.target = Metric.ball 0 r ∧ e x = 0 ∧
          ∀ y ∈ e.source, ∀ u v : TangentSpace I y,
            g.inner y u v =
              c y * ⟪mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) e y u,
                mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) e y v⟫_ℝ := by
  refine ⟨fun hg x ↦ ?_, fun h ↦ g.isLocallyConformallyFlat_of_forall_exists_partialDiffeomorph
    (F := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) fun x ↦ ?_⟩
  · obtain ⟨r, hr, c, hc, hc_pos, e, hx, -, htarget, hex0, hinner⟩ :=
      hg.exists_partialDiffeomorph_ball
        (F := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) (by simp) (x₀ := x) univ_mem
    exact ⟨r, hr, c, hc, hc_pos, e, hx, htarget, hex0, hinner⟩
  · obtain ⟨_, -, c, hc, hc_pos, e, hx, -, -, hinner⟩ := h x
    exact ⟨e, c, hx, hc.contMDiffOn, fun y _ ↦ hc_pos y, hinner⟩

end Boundaryless

end Bundle.ContMDiffRiemannianMetric
