/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Flat
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.ConformallyFlat.Basic
import TauCeti.Geometry.Manifold.ContMDiff.Log
import TauCeti.Geometry.Manifold.ContMDiffMap.Extension
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Geometry.Manifold.Riemannian.Gradient.NormedSpace

/-!
# Conformally Euclidean coordinate charts

Classically, a smooth Riemannian metric `g` on `M` is called locally conformally flat when every
point admits a smooth coordinate chart into `ℝⁿ` in which `g` is a smooth positive multiple of the
pullback of the Euclidean metric. In `ConformallyFlat.Basic`, `g.IsLocallyConformallyFlat` is
defined intrinsically by the existence near each point of a globally smooth positive function `f`
whose rescaled metric `f g` has vanishing Levi-Civita curvature tensor near that point.

This file proves that the two definitions agree in every dimension:

* From a conformally Euclidean partial diffeomorphism `φ` around `x₀` with conformal factor `h` on
  `φ.source` (`g = h · φ^* g_Eucl`), extending `-log h` from a neighbourhood of `x₀` to a globally
  smooth function `ψ` produces `f = exp ψ > 0` agreeing with `h⁻¹` on an open neighbourhood `W` of
  `x₀`, so `φ|_W` is a local Riemannian isometry from `(W, f g)` to the Euclidean model space and
  `f g` is flat near `x₀`. This direction needs no interior-point assumption and works for any
  finite-dimensional real inner-product space target.
* Conversely, at an interior point `x₀` where `f g` is flat nearby, the local Euclidean-isometry
  characterization of flat metrics
  (`eventually_curvatureTensor_leviCivitaConnection_eq_zero_iff_of_isInteriorPoint`) furnishes a
  smooth Riemannian isometry from an open neighbourhood `W` of `x₀` with `(f g)|_W` onto an open
  ball around `0` in `EuclideanSpace ℝ (Fin (Module.finrank ℝ E))` sending `x₀` to `0`. Viewing
  this diffeomorphism as a partial diffeomorphism via `Diffeomorph.toPartialDiffeomorphOpens`
  expresses `g` on `W` as `f⁻¹` times the Euclidean pullback.

## Main results

In `Bundle.ContMDiffRiemannianMetric`:

* `exists_eventually_curvatureTensor_rescale_eq_zero_of_partialDiffeomorph`: a conformally
  Euclidean partial diffeomorphism around `x₀` yields a globally smooth positive factor flattening
  `g` near `x₀`.
* `isLocallyConformallyFlat_of_forall_exists_partialDiffeomorph`: existence of conformally
  Euclidean charts around every point implies `g.IsLocallyConformallyFlat`.
* `exists_eventually_curvatureTensor_rescale_eq_zero_iff_partialDiffeomorph_of_isInteriorPoint` and
  `exists_eventually_curvatureTensor_rescale_eq_zero_iff_partialDiffeomorph`: pointwise equivalence
  at an interior point (and on a boundaryless manifold).
* `isLocallyConformallyFlat_iff_forall_exists_partialDiffeomorph`: on a boundaryless manifold of
  arbitrary dimension, `g.IsLocallyConformallyFlat` holds if and only if every point admits a
  conformally Euclidean `PartialDiffeomorph` sending it to `0`.

## References

* A. L. Besse, *Einstein Manifolds*, Springer (1987), Section 1.G.
* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), Section 2.
-/

public section

open Bundle Filter Function Manifold Set TopologicalSpace
open scoped ContDiff InnerProductSpace Manifold Topology TauCeti

noncomputable section

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]

/-- If `g` is a smooth positive multiple `h` of the pullback of the inner product of a
finite-dimensional real inner-product space `F` along a partial diffeomorphism `φ` around `x₀`,
then some globally smooth positive rescaling `f g` has vanishing curvature tensor near `x₀`. No
interior-point assumption is needed. -/
theorem exists_eventually_curvatureTensor_rescale_eq_zero_of_partialDiffeomorph
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {x₀ : M} (φ : PartialDiffeomorph I 𝓘(ℝ, F) M F ∞) (hx₀ : x₀ ∈ φ.source)
    {h : M → ℝ} (hh : ContMDiffOn I 𝓘(ℝ) ∞ h φ.source) (hh_pos : ∀ y ∈ φ.source, 0 < h y)
    (hinner : ∀ y ∈ φ.source, ∀ v w : TangentSpace I y,
      g.inner y v w = h y * ⟪mfderiv I 𝓘(ℝ, F) φ y v, mfderiv I 𝓘(ℝ, F) φ y w⟫_ℝ) :
    ∃ (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hf_pos : ∀ y, 0 < f y),
      ∀ᶠ y in 𝓝 x₀, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
          ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩;
        (CovariantDerivative.leviCivitaConnection I M).curvatureTensor y) = 0 := by
  have hneg_log : ContMDiffOn I 𝓘(ℝ) (⊤ : ℕ∞) (fun y ↦ -Real.log (h y)) φ.source := fun y hy ↦
    ((hh.contMDiffAt (φ.open_source.mem_nhds hy)).log (hh_pos y hy).ne').neg.contMDiffWithinAt
  obtain ⟨ψ, hψ_eq⟩ := hneg_log.exists_contMDiffMap_eventuallyEq (φ.open_source.mem_nhds hx₀)
  let f : M → ℝ := fun y ↦ Real.exp (ψ y)
  have hf : ContMDiff I 𝓘(ℝ) ∞ f := Real.contDiff_exp.comp_contMDiff ψ.contMDiff
  have hf_pos (y : M) : 0 < f y := Real.exp_pos _
  obtain ⟨W₀, hW₀sub, hW₀open, hx₀W₀⟩ :=
    mem_nhds_iff.1 (Filter.inter_mem (φ.open_source.mem_nhds hx₀) hψ_eq)
  let W : Opens M := ⟨W₀, hW₀open⟩
  refine ⟨f, hf, hf_pos, eventually_of_mem (hW₀open.mem_nhds hx₀W₀) fun y hy ↦ ?_⟩
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩
  have : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) :=
    ⟨(g.rescale f hf hf_pos).inner, (g.rescale f hf hf_pos).contMDiff, fun _ _ _ ↦ rfl⟩
  have hloc (z : W) : IsLocalDiffeomorphAt I 𝓘(ℝ, F) ∞ (φ ∘ (Subtype.val : W → M)) z :=
    (TauCeti.isLocalDiffeomorph_subtype_val z).comp
      (hg := φ.isLocalDiffeomorphAt I 𝓘(ℝ, F) ∞ (hW₀sub z.2).1)
  have hiso : TauCeti.IsLocalRiemannianIsometry I 𝓘(ℝ, F) (φ ∘ (Subtype.val : W → M)) :=
    { contMDiff z := (hloc z).contMDiffAt
      isInvertible_mfderiv z := (hloc z).isInvertible_mfderiv (by simp)
      inner_mfderiv z v w := by
        have hzφ : (z : M) ∈ φ.source := (hW₀sub z.2).1
        have hzψ : ψ z = -Real.log (h z) := (hW₀sub z.2).2
        have hdφ :=
          (PartialDiffeomorph.isLocalDiffeomorphAt _ _ _ φ hzφ).mdifferentiableAt (by simp)
        have hdι :=
          (contMDiff_subtype_val (I := I) (U := W) (n := 1) z).mdifferentiableAt one_ne_zero
        have hfz : f z = (h z)⁻¹ := by
          simp only [f, hzψ, Real.exp_neg, Real.exp_log (hh_pos z hzφ)]
        rw [mfderiv_comp_apply z hdφ hdι, mfderiv_comp_apply z hdφ hdι,
          ← (TauCeti.IsLocalRiemannianIsometry.subtype_val W).inner_mfderiv z v w,
          (g.rescale f hf hf_pos).inner_riemannianBundle, rescale_inner, hinner z hzφ, hfz,
          inv_mul_cancel_left₀ (hh_pos z hzφ).ne'] }
  exact TauCeti.curvatureTensor_leviCivitaConnection_eq_zero_of_isLocalRiemannianIsometry hiso hy

/-- If every point of `M` admits a partial diffeomorphism into a finite-dimensional real
inner-product space `F` pulling the Euclidean inner product back to a smooth positive multiple of
`g`, then `g` is locally conformally flat. -/
theorem isLocallyConformallyFlat_of_forall_exists_partialDiffeomorph
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (h : ∀ x : M, ∃ (φ : PartialDiffeomorph I 𝓘(ℝ, F) M F ∞) (u : M → ℝ),
      x ∈ φ.source ∧ ContMDiffOn I 𝓘(ℝ) ∞ u φ.source ∧ (∀ y ∈ φ.source, 0 < u y) ∧
      ∀ y ∈ φ.source, ∀ v w : TangentSpace I y,
        g.inner y v w = u y * ⟪mfderiv I 𝓘(ℝ, F) φ y v, mfderiv I 𝓘(ℝ, F) φ y w⟫_ℝ) :
    g.IsLocallyConformallyFlat :=
  g.isLocallyConformallyFlat_iff.2 fun x ↦ by
    obtain ⟨φ, u, hx, hu, hu_pos, hinner⟩ := h x
    exact g.exists_eventually_curvatureTensor_rescale_eq_zero_of_partialDiffeomorph φ hx hu hu_pos
      hinner

/-- **Conformally Euclidean chart characterization at an interior point.** Near an interior point
`x₀`, a smooth Riemannian metric `g` admits a flat positive rescaling if and only if `x₀` admits a
`C^∞` partial diffeomorphism `φ` into `EuclideanSpace ℝ (Fin (Module.finrank ℝ E))` sending `x₀`
to `0` on whose source `g` is a smooth positive multiple of the Euclidean pullback. -/
theorem exists_eventually_curvatureTensor_rescale_eq_zero_iff_partialDiffeomorph_of_isInteriorPoint
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) {x₀ : M}
    (hx₀ : I.IsInteriorPoint x₀) :
    (∃ (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hf_pos : ∀ y, 0 < f y),
      ∀ᶠ y in 𝓝 x₀, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
          ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩;
        (CovariantDerivative.leviCivitaConnection I M).curvatureTensor y) = 0) ↔
    ∃ (φ : PartialDiffeomorph I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) M
        (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) ∞) (h : M → ℝ),
      x₀ ∈ φ.source ∧ φ x₀ = 0 ∧ ContMDiffOn I 𝓘(ℝ) ∞ h φ.source ∧
      (∀ y ∈ φ.source, 0 < h y) ∧
      ∀ y ∈ φ.source, ∀ v w : TangentSpace I y,
        g.inner y v w = h y *
          ⟪mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) φ y v,
            mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) φ y w⟫_ℝ := by
  let F := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
  refine ⟨?_, ?_⟩
  · rintro ⟨f, hf, hf_pos, hflat⟩
    let g' := g.rescale f hf hf_pos
    obtain ⟨W, hx₀W, r, -, rest⟩ :=
      (g'.eventually_curvatureTensor_leviCivitaConnection_eq_zero_iff_of_isInteriorPoint hx₀).1
        hflat
    let _ : RiemannianBundle (fun x : W ↦ TangentSpace I x) :=
      ⟨(g'.restrictOpenTangentSpace W).toRiemannianMetric⟩
    obtain ⟨Ψ, hΨ0⟩ := rest
    let B : Opens F := ⟨Metric.ball 0 r, Metric.isOpen_ball⟩
    let φ : PartialDiffeomorph I 𝓘(ℝ, F) M F ∞ :=
      Ψ.toDiffeomorph.toPartialDiffeomorphOpens ⟨⟨x₀, hx₀W⟩⟩
    have hφ_comp : (φ : M → F) ∘ (Subtype.val : W → M) = (Subtype.val : B → F) ∘ Ψ :=
      funext fun z ↦ Ψ.toDiffeomorph.toPartialDiffeomorphOpens_apply_coe ⟨⟨x₀, hx₀W⟩⟩ z
    refine ⟨φ, fun y ↦ (f y)⁻¹, by simpa [φ] using hx₀W,
      (Ψ.toDiffeomorph.toPartialDiffeomorphOpens_apply ⟨⟨x₀, hx₀W⟩⟩ hx₀W).trans hΨ0,
      (hf.inv₀ fun y ↦ (hf_pos y).ne').contMDiffOn, fun y _ ↦ inv_pos.2 (hf_pos y),
      fun y hy v w ↦ ?_⟩
    have hyW : y ∈ W := by simpa [φ] using hy
    let yW : W := ⟨y, hyW⟩
    let vW : TangentSpace I yW := (TauCeti.Manifold.tangentSpaceOpenEquiv (I := I) yW).symm v
    let wW : TangentSpace I yW := (TauCeti.Manifold.tangentSpaceOpenEquiv (I := I) yW).symm w
    have hmf_val (u : TangentSpace I y) :
        mfderiv I I (Subtype.val : W → M) yW
          ((TauCeti.Manifold.tangentSpaceOpenEquiv (I := I) yW).symm u) = u := by
      rw [TauCeti.Manifold.mfderiv_subtype_val]
      exact (TauCeti.Manifold.tangentSpaceOpenEquiv (I := I) yW).apply_symm_apply u
    have hdφ := (PartialDiffeomorph.isLocalDiffeomorphAt _ _ _ φ hy).mdifferentiableAt (by simp)
    have hdιW := (contMDiff_subtype_val (I := I) (U := W) (n := 1) yW).mdifferentiableAt one_ne_zero
    have hmv (u : TangentSpace I y) :
        mvfderiv I φ y u = mvfderiv I ((Subtype.val : B → F) ∘ Ψ) yW
          ((TauCeti.Manifold.tangentSpaceOpenEquiv (I := I) yW).symm u) := by
      rw [← hφ_comp, mvfderiv_comp_apply yW hdφ hdιW, hmf_val]
    have hiso : TauCeti.IsLocalRiemannianIsometry I 𝓘(ℝ, F) ((Subtype.val : B → F) ∘ Ψ) :=
      (TauCeti.IsLocalRiemannianIsometry.subtype_val B).comp Ψ.isLocalRiemannianIsometry
    have hinner_eq : ⟪mfderiv I 𝓘(ℝ, F) φ y v, mfderiv I 𝓘(ℝ, F) φ y w⟫_ℝ = ⟪vW, wW⟫_ℝ := by
      rw [TauCeti.Manifold.inner_mfderiv_eq_inner_mvfderiv φ y v w, hmv v, hmv w,
        ← TauCeti.Manifold.inner_mfderiv_eq_inner_mvfderiv ((Subtype.val : B → F) ∘ Ψ) yW vW wW]
      exact hiso.inner_mfderiv yW vW wW
    have hinnerW : ⟪vW, wW⟫_ℝ = f y * g.inner y v w := by
      rw [(g'.restrictOpenTangentSpace W).inner_riemannianBundle yW vW wW,
        g'.restrictOpenTangentSpace_inner W yW vW wW,
        (TauCeti.Manifold.tangentSpaceOpenEquiv (I := I) yW).apply_symm_apply,
        (TauCeti.Manifold.tangentSpaceOpenEquiv (I := I) yW).apply_symm_apply]
      exact g.rescale_inner f hf hf_pos y v w
    rw [hinner_eq, hinnerW, inv_mul_cancel_left₀ (hf_pos y).ne']
  · rintro ⟨φ, h, hx₀φ, -, hh, hh_pos, hinner⟩
    exact g.exists_eventually_curvatureTensor_rescale_eq_zero_of_partialDiffeomorph φ hx₀φ hh
      hh_pos hinner

section Boundaryless

variable [BoundarylessManifold I M]

/-- On a boundaryless manifold, `g` admits a flat positive rescaling near `x₀` if and only if `x₀`
admits a conformally Euclidean `PartialDiffeomorph` sending `x₀` to `0`. -/
theorem exists_eventually_curvatureTensor_rescale_eq_zero_iff_partialDiffeomorph
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (x₀ : M) :
    (∃ (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hf_pos : ∀ y, 0 < f y),
      ∀ᶠ y in 𝓝 x₀, (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
          ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩;
        (CovariantDerivative.leviCivitaConnection I M).curvatureTensor y) = 0) ↔
    ∃ (φ : PartialDiffeomorph I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) M
        (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) ∞) (h : M → ℝ),
      x₀ ∈ φ.source ∧ φ x₀ = 0 ∧ ContMDiffOn I 𝓘(ℝ) ∞ h φ.source ∧
      (∀ y ∈ φ.source, 0 < h y) ∧
      ∀ y ∈ φ.source, ∀ v w : TangentSpace I y,
        g.inner y v w = h y *
          ⟪mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) φ y v,
            mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) φ y w⟫_ℝ :=
  g.exists_eventually_curvatureTensor_rescale_eq_zero_iff_partialDiffeomorph_of_isInteriorPoint
    BoundarylessManifold.isInteriorPoint

/-- **Conformally Euclidean coordinate chart characterization of local conformal flatness.** On a
boundaryless smooth manifold of any dimension, a smooth Riemannian metric `g` is locally
conformally flat if and only if every point `x` admits a `C^∞` partial diffeomorphism `φ` into
`EuclideanSpace ℝ (Fin (Module.finrank ℝ E))` sending `x` to `0` on whose source `g` is a smooth
positive multiple of the pullback of the Euclidean inner product. -/
theorem isLocallyConformallyFlat_iff_forall_exists_partialDiffeomorph
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) :
    g.IsLocallyConformallyFlat ↔
      ∀ x : M, ∃ (φ : PartialDiffeomorph I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) M
          (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) ∞) (h : M → ℝ),
        x ∈ φ.source ∧ φ x = 0 ∧ ContMDiffOn I 𝓘(ℝ) ∞ h φ.source ∧
        (∀ y ∈ φ.source, 0 < h y) ∧
        ∀ y ∈ φ.source, ∀ v w : TangentSpace I y,
          g.inner y v w = h y *
            ⟪mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) φ y v,
              mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) φ y w⟫_ℝ :=
  g.isLocallyConformallyFlat_iff.trans
    (forall_congr' g.exists_eventually_curvatureTensor_rescale_eq_zero_iff_partialDiffeomorph)

end Boundaryless

end Bundle.ContMDiffRiemannianMetric
