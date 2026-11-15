/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Flat
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.ConformallyFlat.Basic
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Manifold.IsManifold.InteriorChart
import TauCeti.Geometry.Manifold.Riemannian.Isometry.Chart

/-!
# Conformally Euclidean coordinate characterizations of locally conformally flat metrics

Classically, a smooth Riemannian metric `g` on an `n`-manifold `M` is *locally conformally flat* if
every point admits a coordinate chart in which `g` is a smooth positive multiple of the Euclidean
metric. In the basic conformal-flatness module,
`Bundle.ContMDiffRiemannianMetric.IsLocallyConformallyFlat` is instead defined via the existence
around each point of a global smooth positive conformal rescaling `f g` whose Levi-Civita curvature
tensor vanishes near the point. This file proves the equivalence of the two viewpoints:

1. **Converse (no interior-point hypothesis needed).** If an open neighbourhood `W` of `x₀` carries
   a smooth map `φ : W → F` into a finite-dimensional real inner-product space `F` with invertible
   differential everywhere on `W` such that `g|_W` is a smooth positive multiple `h` of the
   pulled-back inner product of `F`, extending `h⁻¹` off a smaller neighbourhood of `x₀` by a
   smooth bump function produces a global smooth positive conformal factor `f : M → ℝ` making
   `φ` a local Riemannian isometry from `(W', (f g)|_{W'})` into `F`. By
   `TauCeti.curvatureTensor_leviCivitaConnection_eq_zero_of_isLocalRiemannianIsometry`, the
   curvature tensor of `f g` vanishes near `x₀`.

2. **Forward direction and equivalence at interior points.** Conversely, if `x₀` is an interior
   point of `M` and `f g` has vanishing curvature tensor near `x₀`, applying the flat-metric
   Euclidean-isometry theorem (`eventually_curvatureTensor_leviCivitaConnection_eq_zero_iff` at an
   interior point) to `f g` produces an open neighbourhood `W` of `x₀` and a smooth diffeomorphism
   `Ψ` onto an open ball around `0` in `EuclideanSpace ℝ (Fin (Module.finrank ℝ E))` sending `x₀`
   to `0` along which `g|_W` equals `f⁻¹` times the pulled-back Euclidean inner product. On a
   boundaryless manifold this yields a global equivalence for `g.IsLocallyConformallyFlat`.

3. **Maximal-atlas charts when the model space carries an inner product.** When the model vector
   space `E` is itself an inner-product space, transporting the open-ball isometry into `E`,
   translating by `extChartAt I x₀ x₀ ∈ interior (range I)`, and reading back through
   `I.interiorChart.symm` (`OpenPartialHomeomorph.trans_interiorChart_symm_mem_maximalAtlas`)
   produces an actual smooth chart `c ∈ IsManifold.maximalAtlas I ∞ M` around `x₀` on whose source
   `g` is a smooth positive multiple of the pullback of the inner product of `E` along `c.extend I`.

## Main results

* `exists_eventually_curvatureTensor_rescale_eq_zero_of_inner_mfderiv_eq`
  (in `Bundle.ContMDiffRiemannianMetric`): a local conformal map into an inner-product space around
  `x₀` produces a global smooth positive rescaling `f g` with vanishing curvature near `x₀`
  (no interior-point assumption).
* `exists_eventually_curvatureTensor_rescale_eq_zero_iff_exists_diffeomorph_ball_of_isInteriorPoint`
  (in `Bundle.ContMDiffRiemannianMetric`): at an interior point `x₀`, existence of a locally flat
  conformal rescaling is equivalent to a conformally Euclidean diffeomorphism onto an open ball in
  `EuclideanSpace ℝ (Fin (Module.finrank ℝ E))`.
* `Bundle.ContMDiffRiemannianMetric.isLocallyConformallyFlat_iff_exists_diffeomorph_ball`:
  global characterization of `g.IsLocallyConformallyFlat` on a boundaryless manifold via
  conformally Euclidean open-ball diffeomorphisms.
* `exists_eventually_curvatureTensor_rescale_eq_zero_of_mem_maximalAtlas`
  (in `Bundle.ContMDiffRiemannianMetric`): a conformally Euclidean chart in
  `IsManifold.maximalAtlas I ∞ M` around `x₀` yields a locally flat global rescaling `f g` near
  `x₀` (no interior-point assumption).
* `exists_eventually_curvatureTensor_rescale_eq_zero_iff_exists_mem_maximalAtlas_of_isInteriorPoint`
  (in `Bundle.ContMDiffRiemannianMetric`): at an interior point of a manifold modelled on an
  inner-product space `E`, existence of a locally flat conformal rescaling is equivalent to a
  conformally Euclidean chart in `IsManifold.maximalAtlas I ∞ M`.
* `Bundle.ContMDiffRiemannianMetric.isLocallyConformallyFlat_iff_exists_mem_maximalAtlas`:
  global maximal-atlas conformally Euclidean chart characterization of `g.IsLocallyConformallyFlat`
  on a boundaryless manifold modelled on an inner-product space `E`.

## References

* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), 37–91,
  Section 2.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 7, Theorem 7.10 and Problem 7-7.
-/

public section

noncomputable section

open Bundle Filter Function Metric Module Set TopologicalSpace
open scoped ContDiff InnerProductSpace Manifold Topology TauCeti

namespace Bundle.ContMDiffRiemannianMetric

section NormedModel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]

/-- Extend the reciprocal `h⁻¹` of a smooth positive function `h` on an open neighbourhood `W` of
`x₀` to a global smooth positive function `f : M → ℝ` that agrees with `h⁻¹` on a smaller open
neighbourhood `W' ⊆ W` of `x₀`. -/
private theorem exists_contMDiff_pos_eq_inv_of_opens
    {W : Opens M} {x₀ : M} (hx₀W : x₀ ∈ W) {h : W → ℝ}
    (hh : ContMDiff I 𝓘(ℝ) ∞ h) (hh_pos : ∀ y, 0 < h y) :
    ∃ (f : M → ℝ) (_ : ContMDiff I 𝓘(ℝ) ∞ f) (_ : ∀ y, 0 < f y)
      (W' : Opens M) (_ : x₀ ∈ W') (hW'_W : (W' : Set M) ⊆ W),
      ∀ y : W', f y.1 = (h ⟨y.1, hW'_W y.2⟩)⁻¹ := by
  obtain ⟨χ, -, hχW⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := I) x₀).mem_iff.1 (W.2.mem_nhds hx₀W)
  let g₀ : W → ℝ := fun z ↦ (h z)⁻¹ - 1
  have hg₀ : ContMDiff I 𝓘(ℝ) ∞ g₀ := (hh.inv₀ fun z ↦ (hh_pos z).ne').sub contMDiff_const
  let f : M → ℝ := fun y ↦ 1 + χ y * Subtype.val.extend g₀ 0 y
  have hf : ContMDiff I 𝓘(ℝ) ∞ f := by
    intro y
    by_cases hy : y ∈ tsupport χ
    · let y' : W := ⟨y, hχW hy⟩
      exact contMDiffAt_const.add
        (χ.contMDiff.contMDiffAt.mul ((hg₀.contMDiffAt (x := y')).extend_subtypeVal 0))
    · refine (contMDiffAt_const (c := (1 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hy] with z hz
      simp only [f, image_eq_zero_of_notMem_tsupport hz, zero_mul, add_zero]
  have hf_pos (y : M) : 0 < f y := by
    by_cases hyW : y ∈ W
    · have hext : Subtype.val.extend g₀ 0 y = (h ⟨y, hyW⟩)⁻¹ - 1 :=
        Subtype.val_injective.extend_apply g₀ 0 ⟨y, hyW⟩
      have hrew : f y = (1 - χ y) + χ y * (h ⟨y, hyW⟩)⁻¹ := by simp only [f, hext]; ring
      rw [hrew]
      rcases (χ.nonneg (x := y)).eq_or_lt with h0 | hpos
      · simp [← h0]
      · exact add_pos_of_nonneg_of_pos (sub_nonneg.2 χ.le_one)
          (mul_pos hpos (inv_pos.2 (hh_pos _)))
    · have hyχ : y ∉ tsupport χ := fun hy ↦ hyW (hχW hy)
      simp [f, image_eq_zero_of_notMem_tsupport hyχ]
  let W' : Opens M := ⟨interior {y : M | χ y = 1}, isOpen_interior⟩
  have hx₀W' : x₀ ∈ W' := mem_interior_iff_mem_nhds.2 χ.eventuallyEq_one
  have hW'_W : (W' : Set M) ⊆ W :=
    (interior_subset.trans fun _ hy ↦
      subset_tsupport _ (mem_support.2 (by rw [mem_ofPred.1 hy]; exact one_ne_zero))).trans hχW
  refine ⟨f, hf, hf_pos, W', hx₀W', hW'_W, fun y ↦ ?_⟩
  have hχy : χ y.1 = 1 := interior_subset y.2
  have hext : Subtype.val.extend g₀ 0 y.1 = (h ⟨y.1, hW'_W y.2⟩)⁻¹ - 1 :=
    Subtype.val_injective.extend_apply g₀ 0 ⟨y.1, hW'_W y.2⟩
  simp only [f, hχy, hext, one_mul, add_sub_cancel]

/-- **A local conformal map into a real inner-product space yields a locally flat rescaling.** If
an open neighbourhood `W` of `x₀` carries a smooth map `φ : W → F` into a finite-dimensional real
inner-product space `F` with invertible differential everywhere on `W` along which `g|_W` is a
smooth positive multiple `h` of the Euclidean inner product, then `g` admits a globally defined
smooth positive rescaling `f g` whose curvature tensor vanishes near `x₀`. No interior-point or
boundaryless assumption on `M` is needed. -/
theorem exists_eventually_curvatureTensor_rescale_eq_zero_of_inner_mfderiv_eq
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {W : Opens M} {x₀ : M} (hx₀W : x₀ ∈ W) {φ : W → F} (hφ : ContMDiff I 𝓘(ℝ, F) ∞ φ)
    (hφ_inv : ∀ y : W, (mfderiv I 𝓘(ℝ, F) φ y).IsInvertible)
    {h : W → ℝ} (hh : ContMDiff I 𝓘(ℝ) ∞ h) (hh_pos : ∀ y, 0 < h y)
    (hinner : ∀ (y : W) (u v : TangentSpace I y),
      (g.restrictOpenTangentSpace W).inner y u v =
        h y * ⟪mfderiv I 𝓘(ℝ, F) φ y u, mfderiv I 𝓘(ℝ, F) φ y v⟫_ℝ) :
    ∃ (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hf_pos : ∀ y, 0 < f y),
      ∀ᶠ y in 𝓝 x₀, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
          ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩;
        (CovariantDerivative.leviCivitaConnection I M).curvatureTensor y) = 0 := by
  obtain ⟨f, hf, hf_pos, W', hx₀W', hW'_W, hf_eq⟩ :=
    exists_contMDiff_pos_eq_inv_of_opens hx₀W hh hh_pos
  let g' := g.rescale f hf hf_pos
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g'.toRiemannianMetric⟩
  have : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) :=
    ⟨g'.inner, g'.contMDiff, fun _ _ _ ↦ rfl⟩
  have hinc := TauCeti.IsLocalRiemannianIsometry.inclusion (I := I) hW'_W
  let inc : W' → W := fun y ↦ ⟨y.1, hW'_W y.2⟩
  have hψ : TauCeti.IsLocalRiemannianIsometry I 𝓘(ℝ, F) (φ ∘ inc) := by
    refine ⟨hφ.comp hinc.contMDiff, fun y ↦ ?_, fun y u v ↦ ?_⟩
    · rw [mfderiv_comp y (hφ.mdifferentiableAt (by simp)) (hinc.mdifferentiableAt y)]
      exact (hφ_inv (inc y)).comp (hinc.isInvertible_mfderiv y)
    · have hsubW := TauCeti.IsLocalRiemannianIsometry.subtype_val (I := I) W
      rw [mfderiv_comp y (hφ.mdifferentiableAt (by simp)) (hinc.mdifferentiableAt y),
        ← hinc.inner_mfderiv y u v, ← hsubW.inner_mfderiv (inc y),
        g'.inner_riemannianBundle, rescale_inner,
        TauCeti.Manifold.mfderiv_subtype_val, ContinuousLinearEquiv.coe_coe,
        ← g.restrictOpenTangentSpace_inner W (inc y), hinner (inc y),
        show f (inc y).1 = (h (inc y))⁻¹ from hf_eq y,
        inv_mul_cancel_left₀ (hh_pos (inc y)).ne']
      rfl
  exact ⟨f, hf, hf_pos, eventually_of_mem (W'.2.mem_nhds hx₀W') fun y hy ↦
    TauCeti.curvatureTensor_leviCivitaConnection_eq_zero_of_isLocalRiemannianIsometry hψ hy⟩

/-- **Pointwise conformally Euclidean open-ball characterization near an interior point.** At an
interior point `x₀` of `M`, a smooth Riemannian metric `g` admits a global smooth positive
conformal rescaling `f g` flat near `x₀` if and only if `x₀` admits an open neighbourhood `W`, a
radius `r > 0`, a smooth diffeomorphism `Ψ` from `W` onto the open ball `Metric.ball 0 r` in
`EuclideanSpace ℝ (Fin (Module.finrank ℝ E))` sending `x₀` to `0`, and a smooth positive function
`h : W → ℝ` such that `g|_W` equals `h` times the pullback of the Euclidean inner product along
`Ψ`. -/
theorem
    exists_eventually_curvatureTensor_rescale_eq_zero_iff_exists_diffeomorph_ball_of_isInteriorPoint
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) {x₀ : M}
    (hx₀ : I.IsInteriorPoint x₀) :
    (∃ (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hf_pos : ∀ y, 0 < f y),
      ∀ᶠ y in 𝓝 x₀, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
          ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩;
        (CovariantDerivative.leviCivitaConnection I M).curvatureTensor y) = 0) ↔
      ∃ (W : Opens M) (hx₀W : x₀ ∈ W) (r : ℝ) (_ : 0 < r)
        (Ψ : W ≃ₘ^∞⟮I, 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))⟯
          (⟨Metric.ball 0 r, Metric.isOpen_ball⟩ :
            Opens (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))))
        (h : W → ℝ),
        ContMDiff I 𝓘(ℝ) ∞ h ∧ (∀ y, 0 < h y) ∧
        (Ψ ⟨x₀, hx₀W⟩ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) = 0 ∧
        ∀ (y : W) (u v : TangentSpace I y),
          (g.restrictOpenTangentSpace W).inner y u v =
            h y * ⟪mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))
                ((Subtype.val : _ → _) ∘ Ψ) y u,
              mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))
                ((Subtype.val : _ → _) ∘ Ψ) y v⟫_ℝ := by
  let F := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
  refine ⟨?_, ?_⟩
  · rintro ⟨f, hf, hf_pos, hflat⟩
    let g' := g.rescale f hf hf_pos
    obtain ⟨W, hx₀W, r, hr, Ψiso, hΨ0⟩ :=
      (g'.eventually_curvatureTensor_leviCivitaConnection_eq_zero_iff_of_isInteriorPoint hx₀).1
        hflat
    let B : Opens F := ⟨Metric.ball 0 r, Metric.isOpen_ball⟩
    let _ : RiemannianBundle (fun y : W ↦ TangentSpace I y) :=
      ⟨(g'.restrictOpenTangentSpace W).toRiemannianMetric⟩
    have hiso : TauCeti.IsLocalRiemannianIsometry I 𝓘(ℝ, F) ((Subtype.val : B → F) ∘ Ψiso) :=
      (TauCeti.IsLocalRiemannianIsometry.subtype_val B).comp Ψiso.isLocalRiemannianIsometry
    refine ⟨W, hx₀W, r, hr, Ψiso.toDiffeomorph, fun y ↦ (f y.1)⁻¹,
      (hf.comp contMDiff_subtype_val).inv₀ fun y ↦ (hf_pos y.1).ne',
      fun y ↦ inv_pos.2 (hf_pos y.1), hΨ0, fun y u v ↦ ?_⟩
    have h1 := hiso.inner_mfderiv y u v
    rw [(g'.restrictOpenTangentSpace W).inner_riemannianBundle,
      restrictOpenTangentSpace_inner, rescale_inner, ← g.restrictOpenTangentSpace_inner] at h1
    change (g.restrictOpenTangentSpace W).inner y u v =
      (f y.1)⁻¹ * ⟪mfderiv I 𝓘(ℝ, F) ((Subtype.val : B → F) ∘ Ψiso) y u,
        mfderiv I 𝓘(ℝ, F) ((Subtype.val : B → F) ∘ Ψiso) y v⟫_ℝ
    rw [h1, inv_mul_cancel_left₀ (hf_pos y.1).ne']
  · rintro ⟨W, hx₀W, r, -, Ψ, h, hh, hh_pos, -, hinner⟩
    let B : Opens F := ⟨Metric.ball 0 r, Metric.isOpen_ball⟩
    have hιB := TauCeti.IsLocalRiemannianIsometry.subtype_val (I := 𝓘(ℝ, F)) B
    refine g.exists_eventually_curvatureTensor_rescale_eq_zero_of_inner_mfderiv_eq hx₀W
      (contMDiff_subtype_val.comp Ψ.contMDiff) (fun y ↦ ?_) hh hh_pos hinner
    rw [mfderiv_comp y ((contMDiff_subtype_val (n := ∞)).mdifferentiableAt (by simp))
      (Ψ.contMDiff.mdifferentiableAt (by simp))]
    exact (hιB.isInvertible_mfderiv (Ψ y)).comp (Ψ.isInvertible_mfderiv (by simp))

/-- **Characterization of locally conformally flat metrics via conformally Euclidean open-ball
diffeomorphisms.** On a boundaryless smooth manifold `M`, a smooth Riemannian metric `g` is locally
conformally flat if and only if every point `x : M` admits an open neighbourhood `W` diffeomorphic
to an open ball around `0` in `EuclideanSpace ℝ (Fin (Module.finrank ℝ E))` sending `x` to `0`
along which `g|_W` is a smooth positive multiple of the pulled-back Euclidean inner product. -/
theorem isLocallyConformallyFlat_iff_exists_diffeomorph_ball [BoundarylessManifold I M]
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) :
    g.IsLocallyConformallyFlat ↔
      ∀ x : M, ∃ (W : Opens M) (hxW : x ∈ W) (r : ℝ) (_ : 0 < r)
        (Ψ : W ≃ₘ^∞⟮I, 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))⟯
          (⟨Metric.ball 0 r, Metric.isOpen_ball⟩ :
            Opens (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))))
        (h : W → ℝ),
        ContMDiff I 𝓘(ℝ) ∞ h ∧ (∀ y, 0 < h y) ∧
        (Ψ ⟨x, hxW⟩ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) = 0 ∧
        ∀ (y : W) (u v : TangentSpace I y),
          (g.restrictOpenTangentSpace W).inner y u v =
            h y * ⟪mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))
                ((Subtype.val : _ → _) ∘ Ψ) y u,
              mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))
                ((Subtype.val : _ → _) ∘ Ψ) y v⟫_ℝ :=
  (g.isLocallyConformallyFlat_iff).trans <| forall_congr' fun x ↦
  exists_eventually_curvatureTensor_rescale_eq_zero_iff_exists_diffeomorph_ball_of_isInteriorPoint
    g (BoundarylessManifold.isInteriorPoint (I := I) (x := x))

omit [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M] in
/-- Package a smooth diffeomorphism `Ψ : W ≃ₘ^∞⟮I, 𝓘(ℝ, E)⟯ B` between nonempty open subsets of `M`
and `E` as an `OpenPartialHomeomorph M E` with smooth forward and inverse maps. -/
private theorem exists_openPartialHomeomorph_of_diffeomorph
    {W : Opens M} {x₀ : M} (hx₀W : x₀ ∈ W) {B : Opens E} (Ψ : W ≃ₘ^∞⟮I, 𝓘(ℝ, E)⟯ B) :
    ∃ e₀ : OpenPartialHomeomorph M E,
      e₀.source = W ∧ ContMDiffOn I 𝓘(ℝ, E) ∞ e₀ e₀.source ∧
      ContMDiffOn 𝓘(ℝ, E) I ∞ e₀.symm e₀.target ∧ ∀ y : W, e₀ y.1 = (Ψ y : E) := by
  let w₀ : W := ⟨x₀, hx₀W⟩
  let cW := W.openPartialHomeomorphSubtypeCoe ⟨w₀⟩
  let cB := B.openPartialHomeomorphSubtypeCoe ⟨Ψ w₀⟩
  let e₀ : OpenPartialHomeomorph M E :=
    (cW.symm.trans Ψ.toHomeomorph.toOpenPartialHomeomorph).trans cB
  have he₀_src : e₀.source = W := by
    simp [e₀, cW, cB, Opens.openPartialHomeomorphSubtypeCoe_source,
      Opens.openPartialHomeomorphSubtypeCoe_target]
  have he₀_tgt : e₀.target = B := by
    simp [e₀, cW, cB, Opens.openPartialHomeomorphSubtypeCoe_source,
      Opens.openPartialHomeomorphSubtypeCoe_target]
  have he₀_apply (y : W) : e₀ y.1 = (Ψ y : E) := by
    change cB (Ψ.toHomeomorph (cW.symm (cW y))) = (Ψ y : E)
    rw [cW.left_inv (by simp [cW, Opens.openPartialHomeomorphSubtypeCoe_source])]
    rfl
  have he₀_symm_apply (b : B) : e₀.symm b.1 = (Ψ.symm b : M) := by
    change cW (Ψ.toHomeomorph.symm (cB.symm (cB b))) = (Ψ.symm b : M)
    rw [cB.left_inv (by simp [cB, Opens.openPartialHomeomorphSubtypeCoe_source])]
    rfl
  refine ⟨e₀, he₀_src, ?_, ?_, he₀_apply⟩
  · rw [he₀_src]
    exact fun y hy ↦ ((contMDiffAt_subtype_iff (U := W) (x := ⟨y, hy⟩)).1
      (by simpa only [he₀_apply, Function.comp_def] using
        (contMDiff_subtype_val.comp Ψ.contMDiff).contMDiffAt)).contMDiffWithinAt
  · rw [he₀_tgt]
    exact fun z hz ↦ ((contMDiffAt_subtype_iff (U := B) (x := ⟨z, hz⟩)).1
      (by simpa only [he₀_symm_apply, Function.comp_def] using
        (contMDiff_subtype_val.comp Ψ.symm.contMDiff).contMDiffAt)).contMDiffWithinAt

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- Turn a smooth diffeomorphism `Ψ : W ≃ₘ^∞⟮I, 𝓘(ℝ, E)⟯ B` sending an interior point `x₀ ∈ W` to
`0` into a chart `c ∈ IsManifold.maximalAtlas I ∞ M` around `x₀` whose extended map `c.extend I`
agrees on `c.source ⊆ W` with `y ↦ Ψ y + extChartAt I x₀ x₀`. -/
private theorem exists_mem_maximalAtlas_eqOn_of_diffeomorph
    {x₀ : M} (hx₀ : I.IsInteriorPoint x₀) {W : Opens M} (hx₀W : x₀ ∈ W)
    {B : Opens E} (Ψ : W ≃ₘ^∞⟮I, 𝓘(ℝ, E)⟯ B) (hΨ0 : (Ψ ⟨x₀, hx₀W⟩ : E) = 0) :
    ∃ (c : OpenPartialHomeomorph M H) (_ : c ∈ IsManifold.maximalAtlas I ∞ M)
      (_ : x₀ ∈ c.source) (hcW : c.source ⊆ W),
      ∀ y (hy : y ∈ c.source), c.extend I y = (Ψ ⟨y, hcW hy⟩ : E) + extChartAt I x₀ x₀ := by
  obtain ⟨e₀, he₀_src, he₀, he₀', he₀_apply⟩ :=
    exists_openPartialHomeomorph_of_diffeomorph hx₀W Ψ
  let z₀ : E := extChartAt I x₀ x₀
  let e : OpenPartialHomeomorph M E := e₀.trans (Homeomorph.addRight z₀).toOpenPartialHomeomorph
  have he_src : e.source = W := by
    simp [e, he₀_src]
  have he : ContMDiffOn I 𝓘(ℝ, E) ∞ e e.source :=
    (contDiff_id.add contDiff_const).contMDiff.comp_contMDiffOn (he₀.mono inter_subset_left)
  have he' : ContMDiffOn 𝓘(ℝ, E) I ∞ e.symm e.target :=
    he₀'.comp (contDiff_id.add contDiff_const).contMDiff.contMDiffOn fun _ hz ↦ hz.2
  let c : OpenPartialHomeomorph M H := e.trans I.interiorChart.symm
  have hc_mem {y : M} (hy : y ∈ c.source) : y ∈ W ∧ e y ∈ interior (range I) := by
    simpa [c, he_src, OpenPartialHomeomorph.trans_source] using hy
  have hx₀c : x₀ ∈ c.source := by
    simp only [c, he_src, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      ModelWithCorners.interiorChart_target, mem_inter_iff, mem_preimage]
    refine ⟨hx₀W, ?_⟩
    rw [show e x₀ = (Ψ ⟨x₀, hx₀W⟩ : E) + z₀ from congrArg (· + z₀) (he₀_apply ⟨x₀, hx₀W⟩),
      hΨ0, zero_add]
    exact hx₀
  refine ⟨c, OpenPartialHomeomorph.trans_interiorChart_symm_mem_maximalAtlas he he',
    hx₀c, fun _ hy ↦ (hc_mem hy).1, fun y hy ↦ ?_⟩
  change I (I.interiorChart.symm (e y)) = _
  rw [ModelWithCorners.interiorChart_coe_symm, I.right_inv (interior_subset (hc_mem hy).2)]
  exact congrArg (· + z₀) (he₀_apply ⟨y, (hc_mem hy).1⟩)

end NormedModel

section InnerProductModel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]

/-- **A conformally Euclidean maximal-atlas chart around `x₀` yields a locally flat rescaling.**
When the model vector space `E` carries an inner product, if a smooth chart
`c ∈ IsManifold.maximalAtlas I ∞ M` around `x₀` pulls the inner product of `E` along `c.extend I`
back to a smooth positive multiple of `g` on `c.source`, then `g` admits a globally defined smooth
positive rescaling `f g` whose curvature tensor vanishes near `x₀`. No interior-point or
boundaryless assumption is needed. -/
theorem exists_eventually_curvatureTensor_rescale_eq_zero_of_mem_maximalAtlas
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {x₀ : M} {c : OpenPartialHomeomorph M H} (hc : c ∈ IsManifold.maximalAtlas I ∞ M)
    (hx₀c : x₀ ∈ c.source) {h : M → ℝ} (hh : ContMDiffOn I 𝓘(ℝ) ∞ h c.source)
    (hh_pos : ∀ y ∈ c.source, 0 < h y)
    (hinner : ∀ y ∈ c.source, ∀ u v : TangentSpace I y,
      g.inner y u v =
        h y * ⟪mfderiv I 𝓘(ℝ, E) (c.extend I) y u, mfderiv I 𝓘(ℝ, E) (c.extend I) y v⟫_ℝ) :
    ∃ (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hf_pos : ∀ y, 0 < f y),
      ∀ᶠ y in 𝓝 x₀, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
          ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩;
        (CovariantDerivative.leviCivitaConnection I M).curvatureTensor y) = 0 := by
  let Wc : Opens M := ⟨c.source, c.open_source⟩
  let φ : Wc → E := c.extend I ∘ Subtype.val
  have hφ : ContMDiff I 𝓘(ℝ, E) ∞ φ :=
    (c.contMDiffOn_extend hc).comp_contMDiff contMDiff_subtype_val fun y ↦ y.2
  have hc1 : c ∈ IsManifold.maximalAtlas I 1 M :=
    IsManifold.maximalAtlas_subset_of_le (by simp) hc
  refine g.exists_eventually_curvatureTensor_rescale_eq_zero_of_inner_mfderiv_eq
    (W := Wc) hx₀c hφ (fun y ↦ ?_)
    (hh.comp_contMDiff contMDiff_subtype_val fun y ↦ y.2) (fun y ↦ hh_pos y.1 y.2)
    (fun y u v ↦ ?_)
  · rw [mfderiv_comp y ((c.contMDiffAt_extend hc y.2).mdifferentiableAt (by simp))
      ((contMDiff_subtype_val (n := ∞)).mdifferentiableAt (by simp))]
    exact (isInvertible_mfderiv_extend hc1 y.2).comp
      ⟨TauCeti.Manifold.tangentSpaceOpenEquiv (I := I) y,
        (TauCeti.Manifold.mfderiv_subtype_val y).symm⟩
  · rw [g.restrictOpenTangentSpace_inner, ← ContinuousLinearEquiv.coe_coe,
      ← TauCeti.Manifold.mfderiv_subtype_val, hinner y.1 y.2,
      ← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply,
      ← mfderiv_comp y ((c.contMDiffAt_extend hc y.2).mdifferentiableAt (by simp))
        ((contMDiff_subtype_val (n := ∞)).mdifferentiableAt (by simp))]
    rfl

omit [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M] in
/-- If `c.extend I` agrees on `c.source ⊆ W` with a differentiable map `ψ : W → E` shifted by a
constant vector `z₀`, then the inner product of `mfderiv I 𝓘(ℝ, E) (c.extend I) y` equals that of
`mfderiv I 𝓘(ℝ, E) ψ ⟨y, hcW hy⟩` along `tangentSpaceOpenEquiv.symm`. -/
private theorem inner_mfderiv_extend_eq_of_eq_add_const
    {W : Opens M} {c : OpenPartialHomeomorph M H} (hc : c ∈ IsManifold.maximalAtlas I ∞ M)
    (hcW : c.source ⊆ W) {ψ : W → E} (hψ : ∀ w, MDifferentiableAt I 𝓘(ℝ, E) ψ w) {z₀ : E}
    (hc_eq : ∀ y (hy : y ∈ c.source), c.extend I y = ψ ⟨y, hcW hy⟩ + z₀)
    {y : M} (hy : y ∈ c.source) (u v : TangentSpace I y) :
    ⟪mfderiv I 𝓘(ℝ, E) (c.extend I) y u, mfderiv I 𝓘(ℝ, E) (c.extend I) y v⟫_ℝ =
      ⟪mfderiv I 𝓘(ℝ, E) ψ ⟨y, hcW hy⟩
          ((TauCeti.Manifold.tangentSpaceOpenEquiv (I := I) ⟨y, hcW hy⟩).symm u),
        mfderiv I 𝓘(ℝ, E) ψ ⟨y, hcW hy⟩
          ((TauCeti.Manifold.tangentSpaceOpenEquiv (I := I) ⟨y, hcW hy⟩).symm v)⟫_ℝ := by
  let y' : W := ⟨y, hcW hy⟩
  have hev : (c.extend I ∘ (Subtype.val : W → M)) =ᶠ[𝓝 y'] (ψ + fun _ ↦ z₀) :=
    eventually_of_mem ((c.open_source.preimage continuous_subtype_val).mem_nhds hy) fun q hq ↦
      hc_eq q.1 hq
  have hmvd (w : TangentSpace I y') :
      mvfderiv I (c.extend I) y (mfderiv I I (Subtype.val : W → M) y' w) =
        mvfderiv I ψ y' w := by
    rw [← mvfderiv_comp_apply y' ((c.contMDiffAt_extend hc hy).mdifferentiableAt (by simp))
      ((contMDiff_subtype_val (n := ∞)).mdifferentiableAt (by simp))]
    have hcast : mvfderiv I (c.extend I ∘ (Subtype.val : W → M)) y' w =
        mvfderiv I (ψ + fun _ ↦ z₀) y' w :=
      congrArg (NormedSpace.fromTangentSpace _) (congrFun (congrArg DFunLike.coe hev.mfderiv_eq) w)
    rw [hcast, mvfderiv_add (hψ y') mdifferentiableAt_const, mvfderiv_const,
      add_apply, zero_apply, add_zero]
  let u' := (TauCeti.Manifold.tangentSpaceOpenEquiv (I := I) y').symm u
  let v' := (TauCeti.Manifold.tangentSpaceOpenEquiv (I := I) y').symm v
  have hu' : mfderiv I I (Subtype.val : W → M) y' u' = u := by
    rw [TauCeti.Manifold.mfderiv_subtype_val]; exact ContinuousLinearEquiv.apply_symm_apply _ u
  have hv' : mfderiv I I (Subtype.val : W → M) y' v' = v := by
    rw [TauCeti.Manifold.mfderiv_subtype_val]; exact ContinuousLinearEquiv.apply_symm_apply _ v
  change ⟪mvfderiv I (c.extend I) y u, mvfderiv I (c.extend I) y v⟫_ℝ =
    ⟪mvfderiv I ψ y' u', mvfderiv I ψ y' v'⟫_ℝ
  rw [← hu', ← hv', hmvd u', hmvd v']

/-- **Pointwise conformally Euclidean maximal-atlas chart characterization near an interior
point.** On a smooth manifold `M` modelled on a finite-dimensional real inner-product space `E`, a
smooth Riemannian metric `g` admits a global smooth positive conformal rescaling `f g` flat near an
interior point `x₀` if and only if `x₀` lies in the source of a smooth chart
`c ∈ IsManifold.maximalAtlas I ∞ M` on which `g` is a smooth positive multiple of the pullback of
the inner product of `E` along `c.extend I`. -/
theorem
    exists_eventually_curvatureTensor_rescale_eq_zero_iff_exists_mem_maximalAtlas_of_isInteriorPoint
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) {x₀ : M}
    (hx₀ : I.IsInteriorPoint x₀) :
    (∃ (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hf_pos : ∀ y, 0 < f y),
      ∀ᶠ y in 𝓝 x₀, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
          ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩;
        (CovariantDerivative.leviCivitaConnection I M).curvatureTensor y) = 0) ↔
      ∃ c ∈ IsManifold.maximalAtlas I ∞ M, x₀ ∈ c.source ∧
        ∃ h : M → ℝ, ContMDiffOn I 𝓘(ℝ) ∞ h c.source ∧ (∀ y ∈ c.source, 0 < h y) ∧
          ∀ y ∈ c.source, ∀ u v : TangentSpace I y,
            g.inner y u v =
              h y * ⟪mfderiv I 𝓘(ℝ, E) (c.extend I) y u, mfderiv I 𝓘(ℝ, E) (c.extend I) y v⟫_ℝ := by
  refine ⟨?_, fun ⟨c, hc, hx₀c, h, hh, hh_pos, hinner⟩ ↦
    g.exists_eventually_curvatureTensor_rescale_eq_zero_of_mem_maximalAtlas hc hx₀c hh hh_pos
      hinner⟩
  rintro ⟨f, hf, hf_pos, hflat⟩
  let g' := g.rescale f hf hf_pos
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g'.toRiemannianMetric⟩
  have : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) :=
    ⟨g'.inner, g'.contMDiff, fun _ _ _ ↦ rfl⟩
  let L : TangentSpace I x₀ ≃ₗᵢ[ℝ] E :=
    ((stdOrthonormalBasis ℝ (TangentSpace I x₀)).reindex
      (finCongr (TauCeti.finrank_tangentSpace x₀))).repr.trans (stdOrthonormalBasis ℝ E).repr.symm
  obtain ⟨W, hx₀W, r, -, Ψiso, -, hΨ0, -⟩ :=
    TauCeti.exists_riemannianIsometry_ball_of_eventually_curvatureTensor_eq_zero_of_isInteriorPoint
      hx₀ hflat univ_mem L
  let B : Opens E := ⟨Metric.ball (0 : E) r, Metric.isOpen_ball⟩
  obtain ⟨c, hc, hx₀c, hcW, hc_eq⟩ :=
    exists_mem_maximalAtlas_eqOn_of_diffeomorph hx₀ hx₀W Ψiso.toDiffeomorph hΨ0
  have hiso : TauCeti.IsLocalRiemannianIsometry I 𝓘(ℝ, E) ((Subtype.val : B → E) ∘ Ψiso) :=
    (TauCeti.IsLocalRiemannianIsometry.subtype_val B).comp Ψiso.isLocalRiemannianIsometry
  refine ⟨c, hc, hx₀c, fun y ↦ (f y)⁻¹,
    (hf.inv₀ fun y ↦ (hf_pos y).ne').contMDiffOn, fun y _ ↦ inv_pos.2 (hf_pos y),
    fun y hy u v ↦ ?_⟩
  let y' : W := ⟨y, hcW hy⟩
  let u' := (TauCeti.Manifold.tangentSpaceOpenEquiv (I := I) y').symm u
  let v' := (TauCeti.Manifold.tangentSpaceOpenEquiv (I := I) y').symm v
  have hu' : mfderiv I I (Subtype.val : W → M) y' u' = u := by
    rw [TauCeti.Manifold.mfderiv_subtype_val]; exact ContinuousLinearEquiv.apply_symm_apply _ u
  have hv' : mfderiv I I (Subtype.val : W → M) y' v' = v := by
    rw [TauCeti.Manifold.mfderiv_subtype_val]; exact ContinuousLinearEquiv.apply_symm_apply _ v
  rw [inner_mfderiv_extend_eq_of_eq_add_const hc hcW hiso.mdifferentiableAt hc_eq hy u v,
    hiso.inner_mfderiv y' u' v',
    ← (TauCeti.IsLocalRiemannianIsometry.subtype_val (I := I) W).inner_mfderiv y' u' v',
    hu', hv', g'.inner_riemannianBundle, rescale_inner, inv_mul_cancel_left₀ (hf_pos y).ne']

/-- **Conformally Euclidean maximal-atlas chart characterization of locally conformally flat
metrics.** On a boundaryless smooth manifold `M` modelled on a finite-dimensional real
inner-product space `E`, a smooth Riemannian metric `g` is locally conformally flat if and only if
every point `x : M` lies in the source of a smooth chart `c ∈ IsManifold.maximalAtlas I ∞ M` on
which `g` is a smooth positive multiple of the pullback of the inner product of `E` along
`c.extend I`. -/
theorem isLocallyConformallyFlat_iff_exists_mem_maximalAtlas [BoundarylessManifold I M]
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) :
    g.IsLocallyConformallyFlat ↔
      ∀ x : M, ∃ c ∈ IsManifold.maximalAtlas I ∞ M, x ∈ c.source ∧
        ∃ h : M → ℝ, ContMDiffOn I 𝓘(ℝ) ∞ h c.source ∧ (∀ y ∈ c.source, 0 < h y) ∧
          ∀ y ∈ c.source, ∀ u v : TangentSpace I y,
            g.inner y u v =
              h y * ⟪mfderiv I 𝓘(ℝ, E) (c.extend I) y u, mfderiv I 𝓘(ℝ, E) (c.extend I) y v⟫_ℝ :=
  (g.isLocallyConformallyFlat_iff).trans <| forall_congr' fun x ↦
  exists_eventually_curvatureTensor_rescale_eq_zero_iff_exists_mem_maximalAtlas_of_isInteriorPoint
    g (BoundarylessManifold.isInteriorPoint (I := I) (x := x))

end InnerProductModel

end Bundle.ContMDiffRiemannianMetric
