/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.Normed.Lp.ProdLp
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.Analysis.Calculus.FDeriv.WithLp
import TauCeti.Analysis.Calculus.GraphFlattening
import TauCeti.MeasureTheory.Integral.DivergenceTheorem.ProdHalfSpace
import TauCeti.MeasureTheory.Measure.Lebesgue.OrthogonalSlices

/-!
# The divergence theorem on a `C¹` subgraph and on a symmetric slab

Let `E` be a finite-dimensional real inner product space, `e` a unit vector, and
`H = (ℝ ∙ e)ᗮ` its orthogonal hyperplane, with orthogonal projection
`π_H = (ℝ ∙ e)ᗮ.orthogonalProjectionOnto`. For a `C¹` height function `f : H → ℝ` and a compactly
supported `C¹` vector field `ψ : E → E`, the open subgraph `{x : E | ⟪e, x⟫ < f (π_H x)}` has
outward normal proportional to `e - ∇f(π_H x)` and surface element `√(1 + ‖∇f‖²) dy`, whose
product `(e - ∇f(y)) dy` is polynomial in `Df`:

`∫_{⟪e, x⟫ < f (π_H x)} tr (Dψ x) dx = ∫_{y : H} (⟪e, ψ z_y⟫ - Df y (π_H (ψ z_y))) dy`,

where `z_y = (y : E) + f y • e` (`TauCeti.setIntegral_setOf_inner_lt_apply_trace_fderiv`).

No `C²` regularity of `f` is needed. Rather than pulling the vector field back by the Jacobian of
graph flattening (which would differentiate `Df`), we pull each scalar coordinate `g` back along
the inverse graph shear `(t, y) ↦ (t + γ y, y)` on `WithLp 2 (ℝ × H)`. The pulled-back scalar
function `G = g ∘ (graphFlattening γ _).symm` remains `C¹` with compact support, and the chain
rule expresses `Dg` on the epigraph `{γ x.snd < x.fst}` as a tangential derivative of `G` (which
integrates to zero on each horizontal slice) plus a normal derivative weighted by `v.fst - Dγ(y)`,
which integrates along each vertical ray `(0, ∞)` by the one-dimensional fundamental theorem of
calculus (`TauCeti.setIntegral_setOf_lt_fst_fderiv_apply`).

For a nonnegative `C¹` width `w : H → ℝ`, subtracting the subgraph `{⟪e, x⟫ < -w (π_H x) / 2}`
from `{⟪e, x⟫ < w (π_H x) / 2}` (whose lower boundary graph is null by Cavalieri's principle,
`TauCeti.volume_setOf_inner_eq_apply_orthogonalProjectionOnto`) gives the divergence formula on the
symmetric slab `{x | |⟪e, x⟫| < w (π_H x) / 2}`
(`TauCeti.setIntegral_setOf_abs_inner_lt_div_two_trace_fderiv`), the smooth model of a Steiner
symmetral.

## Main declarations

* `TauCeti.setIntegral_setOf_lt_fst_fderiv_apply`: directional divergence theorem on the epigraph
  `{x : WithLp 2 (ℝ × E) | γ x.snd < x.fst}` of a `C¹` function `γ`.
* `TauCeti.volume_setOf_inner_eq_apply_orthogonalProjectionOnto`: the graph of any measurable
  function over `(ℝ ∙ e)ᗮ` has Lebesgue measure zero.
* `TauCeti.setIntegral_setOf_inner_lt_apply_fderiv_apply` and
  `TauCeti.setIntegral_setOf_inner_lt_apply_trace_fderiv`: directional and vector-field divergence
  theorems on the subgraph `{x : E | ⟪e, x⟫ < f ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x)}`.
* `TauCeti.setIntegral_setOf_abs_inner_lt_div_two_trace_fderiv` and
  `TauCeti.integrable_slab_boundary_integrand`: divergence theorem and boundary integrability on the
  symmetric slab `{x : E | |⟪e, x⟫| < w ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x) / 2}`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Appendix C.2 (the Gauss–Green theorem on
  a `C¹` graph domain by boundary flattening).
* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, Cambridge University
  Press, 2012, §9.3 and §14.2.
-/

public section

noncomputable section

namespace TauCeti

open Filter MeasureTheory Set Topology
open scoped ContDiff RealInnerProductSpace

section Epigraph

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- On `ℝ × E`, a normal derivative of a compactly supported `C¹` function `G` weighted by a
continuous factor `c(y)` of the tangential variable is integrable on `Ioi 0 ×ˢ E` and integrates to
`-∫ y, c y * G (0, y)`. -/
private theorem integrable_and_integral_prod_mul_fderiv_normal {G : WithLp 2 (ℝ × E) → ℝ}
    (hG : ContDiff ℝ 1 G) (hGc : HasCompactSupport G) {c : E → ℝ} (hc : Continuous c) :
    Integrable (fun z : ℝ × E => c z.2 * fderiv ℝ G (WithLp.toLp 2 z) (WithLp.toLp 2 (1, (0 : E))))
        ((volume.restrict (Ioi 0)).prod volume) ∧
      ∫ z : ℝ × E, c z.2 * fderiv ℝ G (WithLp.toLp 2 z) (WithLp.toLp 2 (1, (0 : E)))
          ∂((volume.restrict (Ioi 0)).prod volume) =
        -∫ y : E, c y * G (WithLp.toLp 2 (0, y)) := by
  have hGd : Differentiable ℝ G := hG.differentiable one_ne_zero
  have hd : Continuous fun z : ℝ × E =>
      fderiv ℝ G (WithLp.toLp 2 z) (WithLp.toLp 2 (1, (0 : E))) :=
    ((hG.continuous_fderiv one_ne_zero).clm_apply continuous_const).comp
      (WithLp.homeomorphProd 2 ℝ E).symm.continuous
  have hdc : HasCompactSupport fun z : ℝ × E =>
      fderiv ℝ G (WithLp.toLp 2 z) (WithLp.toLp 2 (1, (0 : E))) :=
    (hGc.fderiv_apply (𝕜 := ℝ) (WithLp.toLp 2 (1, (0 : E)))).comp_homeomorph
      (WithLp.homeomorphProd 2 ℝ E).symm
  have hint : Integrable (fun z : ℝ × E =>
      c z.2 * fderiv ℝ G (WithLp.toLp 2 z) (WithLp.toLp 2 (1, (0 : E))))
      ((volume.restrict (Ioi 0)).prod volume) := by
    have hvol :=
      ((hc.comp continuous_snd).mul hd).integrable_of_hasCompactSupport (μ := volume) hdc.mul_left
    rw [Measure.volume_eq_prod] at hvol
    exact hvol.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)
  refine ⟨hint, ?_⟩
  rw [integral_prod_symm _ hint, ← integral_neg]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  dsimp only
  have he : IsClosedEmbedding (fun t : ℝ => WithLp.toLp 2 (t, y)) :=
    (WithLp.homeomorphProd 2 ℝ E).symm.isClosedEmbedding.comp
      (.of_isEmbedding_isClosedMap (isEmbedding_prodMkLeft y) (isClosedMap_prodMk_right y))
  have hline : ContDiff ℝ 1 (fun t : ℝ => G (WithLp.toLp 2 (t, y))) :=
    hG.comp (((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ E).symm.contDiff).comp
      (contDiff_id.prodMk contDiff_const))
  rw [integral_const_mul, ← mul_neg,
    ← (hGc.comp_isClosedEmbedding he).integral_Ioi_deriv_eq hline 0]
  exact congrArg (c y * ·) (integral_congr_ae (Eventually.of_forall fun t =>
    (hasDerivAt_comp_toLp_fst (hGd _)).deriv.symm))

/-- **Directional divergence theorem above a `C¹` graph.** For a `C¹` height function `γ : E → ℝ`,
a compactly supported `C¹` function `g` on `WithLp 2 (ℝ × E)`, and a direction `v`, the integral
of `∂_v g` over the strict epigraph `{x | γ x.snd < x.fst}` equals
`∫ y, (Dγ y v.snd - v.fst) * g (γ y, y)`. -/
theorem setIntegral_setOf_lt_fst_fderiv_apply {γ : E → ℝ} (hγ : ContDiff ℝ 1 γ)
    {g : WithLp 2 (ℝ × E) → ℝ} (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g)
    (v : WithLp 2 (ℝ × E)) :
    ∫ x in {x : WithLp 2 (ℝ × E) | γ x.snd < x.fst}, fderiv ℝ g x v =
      ∫ y : E, (fderiv ℝ γ y v.snd - v.fst) * g (WithLp.toLp 2 (γ y, y)) := by
  let Φ := graphFlattening γ hγ.continuous
  let G : WithLp 2 (ℝ × E) → ℝ := g ∘ Φ.symm
  have hG : ContDiff ℝ 1 G := hg.comp (contDiff_graphFlattening_symm hγ)
  have hGc : HasCompactSupport G := hgc.comp_homeomorph Φ.symm
  -- Flatten the epigraph onto `Ioi 0 ×ˢ E` by the volume-preserving shear `Φ.symm`.
  have hpre : Φ.symm ⁻¹' {x : WithLp 2 (ℝ × E) | γ x.snd < x.fst} =
      {x : WithLp 2 (ℝ × E) | 0 < (WithLp.ofLp x).1} := by
    ext x; simp [Φ]
  have hcoord : ∫ x in {x : WithLp 2 (ℝ × E) | γ x.snd < x.fst}, fderiv ℝ g x v =
      ∫ z : ℝ × E, fderiv ℝ g (Φ.symm (WithLp.toLp 2 z)) v
        ∂((volume.restrict (Ioi 0)).prod volume) := by
    rw [← (measurePreserving_graphFlattening_symm γ hγ.continuous).setIntegral_preimage_emb
      Φ.symm.measurableEmbedding (fun x => fderiv ℝ g x v) _, hpre,
      Measure.restrict_prod_eq_prod_univ, Set.prod_univ]
    simpa only [Measure.volume_eq_prod, Set.preimage_ofPred_eq, WithLp.ofLp_toLp, Set.Ioi] using
      ((WithLp.volume_preserving_toLp ℝ E).setIntegral_preimage_emb
        (MeasurableEquiv.toLp 2 (ℝ × E)).measurableEmbedding
        (fun x => fderiv ℝ g (Φ.symm x) v) {x | 0 < (WithLp.ofLp x).1}).symm
  -- Express `Dg (Φ.symm z) v` via the tangential and normal derivatives of `G = g ∘ Φ.symm`.
  have hchain (z : ℝ × E) : fderiv ℝ g (Φ.symm (WithLp.toLp 2 z)) v =
      fderiv ℝ G (WithLp.toLp 2 z) (WithLp.toLp 2 (0, v.snd)) +
        (v.fst - fderiv ℝ γ z.2 v.snd) *
          fderiv ℝ G (WithLp.toLp 2 z) (WithLp.toLp 2 (1, (0 : E))) := by
    have hΦd : HasFDerivAt Φ.symm (graphFlatteningL (-fderiv ℝ γ z.2)).toContinuousLinearMap
        (WithLp.toLp 2 z) := by
      rw [show ⇑Φ.symm = ⇑(graphFlattening (-γ) hγ.continuous.neg) by
        rw [← graphFlattening_symm]]
      exact hasFDerivAt_graphFlattening hγ.continuous.neg
        (hγ.differentiable one_ne_zero z.2).hasFDerivAt.neg
    have hGd (u : WithLp 2 (ℝ × E)) : fderiv ℝ G (WithLp.toLp 2 z) u =
        fderiv ℝ g (Φ.symm (WithLp.toLp 2 z)) (graphFlatteningL (-fderiv ℝ γ z.2) u) := by
      rw [((hg.differentiable one_ne_zero _).hasFDerivAt.comp (WithLp.toLp 2 z) hΦd).fderiv]
      simp
    have hv : v = graphFlatteningL (-fderiv ℝ γ z.2) (WithLp.toLp 2 (0, v.snd)) +
        (v.fst - fderiv ℝ γ z.2 v.snd) •
          graphFlatteningL (-fderiv ℝ γ z.2) (WithLp.toLp 2 (1, (0 : E))) := by
      apply (WithLp.ext_iff 2).2
      ext <;> simp
    rw [hGd, hGd]
    conv_lhs => rw [hv]
    rw [map_add, map_smul, smul_eq_mul]
  have hc : Continuous fun y : E => v.fst - fderiv ℝ γ y v.snd :=
    continuous_const.sub ((hγ.continuous_fderiv one_ne_zero).clm_apply continuous_const)
  obtain ⟨hint2, hnorm_eq⟩ := integrable_and_integral_prod_mul_fderiv_normal hG hGc hc
  rw [hcoord, integral_congr_ae (Eventually.of_forall hchain),
    integral_add (integrable_fderiv_apply_prod hG hGc 0 _) hint2,
    integral_prod_fderiv_tangent hG hGc 0 v.snd, zero_add, hnorm_eq, ← integral_neg]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [G, Φ, Function.comp_apply, graphFlattening_symm_apply, WithLp.toLp_fst,
    WithLp.toLp_snd, zero_add]
  ring

end Epigraph

section Subgraph

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Projecting `(y : E) + t • e` onto `(ℝ ∙ e)ᗮ` recovers `y`. -/
private theorem orthogonalProjectionOnto_orthogonal_add_smul (e : E) (y : (ℝ ∙ e)ᗮ) (t : ℝ) :
    (ℝ ∙ e)ᗮ.orthogonalProjectionOnto ((y : E) + t • e) = y := by
  rw [map_add, (ℝ ∙ e)ᗮ.orthogonalProjectionOnto_mem_subspace_eq_self y, map_smul,
    Submodule.orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero, smul_zero, add_zero]

/-- For a continuous function `f : (ℝ ∙ e)ᗮ → ℝ`, the graph parametrization `y ↦ (y : E) + f y • e`
is a closed embedding, since orthogonal projection onto `(ℝ ∙ e)ᗮ` is a continuous left inverse. -/
private theorem isClosedEmbedding_add_smul_graph (e : E) {f : (ℝ ∙ e)ᗮ → ℝ} (hf : Continuous f) :
    IsClosedEmbedding fun y : (ℝ ∙ e)ᗮ => (y : E) + f y • e :=
  Function.LeftInverse.isClosedEmbedding
    (fun y => orthogonalProjectionOnto_orthogonal_add_smul e y (f y))
    (ℝ ∙ e)ᗮ.orthogonalProjectionOnto.continuous
    (continuous_subtype_val.add (hf.smul continuous_const))

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- **The graph of a measurable function over `(ℝ ∙ e)ᗮ` has Lebesgue measure zero.** -/
theorem volume_setOf_inner_eq_apply_orthogonalProjectionOnto (e : E) (he : ‖e‖ = 1)
    {f : (ℝ ∙ e)ᗮ → ℝ} (hf : Measurable f) :
    volume {x : E | ⟪e, x⟫ = f ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x)} = 0 := by
  have hm : MeasurableSet {x : E | ⟪e, x⟫ = f ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x)} :=
    measurableSet_eq_fun (continuous_const.inner continuous_id).measurable
      (hf.comp (ℝ ∙ e)ᗮ.orthogonalProjectionOnto.continuous.measurable)
  rw [volume_eq_lintegral_volume_lineSection e he hm.nullMeasurableSet]
  refine (lintegral_congr fun y => ?_).trans lintegral_zero
  have hsec : {t : ℝ | (y : E) + t • e ∈
      {x : E | ⟪e, x⟫ = f ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x)}} = {f y} := by
    ext t
    simp [inner_add_smul e he, orthogonalProjectionOnto_orthogonal_add_smul]
  rw [hsec, Real.volume_singleton]

/-- **Directional divergence theorem on a `C¹` subgraph.** For a unit vector `e`, a `C¹` height
function `f : (ℝ ∙ e)ᗮ → ℝ`, a compactly supported `C¹` function `g : E → ℝ`, and a direction `v`,
the integral of `∂_v g` over `{x : E | ⟪e, x⟫ < f ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x)}` is
`∫ y, (⟪e, v⟫ - Df y (π_H v)) * g (y + f y • e)`. -/
theorem setIntegral_setOf_inner_lt_apply_fderiv_apply (e : E) (he : ‖e‖ = 1)
    {f : (ℝ ∙ e)ᗮ → ℝ} (hf : ContDiff ℝ 1 f) {g : E → ℝ} (hg : ContDiff ℝ 1 g)
    (hgc : HasCompactSupport g) (v : E) :
    ∫ x in {x : E | ⟪e, x⟫ < f ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x)}, fderiv ℝ g x v =
      ∫ y : (ℝ ∙ e)ᗮ,
        (⟪e, v⟫ - fderiv ℝ f y ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto v)) *
          g ((y : E) + f y • e) := by
  -- Map `WithLp 2 (ℝ × (ℝ ∙ e)ᗮ)` isometrically to `E` by `(t, y) ↦ (y : E) - t • e`.
  let I : WithLp 2 (ℝ × (ℝ ∙ e)ᗮ) ≃ₗᵢ[ℝ] E :=
    (LinearIsometryEquiv.withLpProdComm 2 ℝ ℝ (ℝ ∙ e)ᗮ).trans
      ((LinearIsometryEquiv.withLpProdCongr 2 (.refl ℝ _) (LinearIsometryEquiv.neg ℝ)).trans
        (orthogonalLineIsometry e he))
  have hI (t : ℝ) (y : (ℝ ∙ e)ᗮ) : I (WithLp.toLp 2 (t, y)) = (y : E) + (-t) • e := by
    simp [I]
  have hIsymm (x : E) :
      I.symm x = WithLp.toLp 2 (-⟪e, x⟫, (ℝ ∙ e)ᗮ.orthogonalProjectionOnto x) := by
    apply I.injective
    rw [I.apply_symm_apply, hI, neg_neg]
    obtain ⟨⟨y, t⟩, rfl⟩ := (orthogonalLineEquiv e he).surjective x
    rw [orthogonalLineEquiv_apply, inner_add_smul e he,
      orthogonalProjectionOnto_orthogonal_add_smul]
  have hset : {x : E | ⟪e, x⟫ < f ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x)} =
      I.symm ⁻¹' {z : WithLp 2 (ℝ × (ℝ ∙ e)ᗮ) | (-f) z.snd < z.fst} := by
    ext x
    simp [hIsymm]
  have hd (z : WithLp 2 (ℝ × (ℝ ∙ e)ᗮ)) :
      fderiv ℝ (g ∘ I) z (I.symm v) = fderiv ℝ g (I z) v := by
    rw [((hg.differentiable one_ne_zero (I z)).hasFDerivAt.comp z
      I.toContinuousLinearEquiv.hasFDerivAt).fderiv]
    simp
  have hcov := I.symm.measurePreserving.setIntegral_preimage_emb
    I.symm.toHomeomorph.measurableEmbedding (fun z => fderiv ℝ g (I z) v)
    {z : WithLp 2 (ℝ × (ℝ ∙ e)ᗮ) | (-f) z.snd < z.fst}
  simp only [LinearIsometryEquiv.apply_symm_apply] at hcov
  have hmodel := setIntegral_setOf_lt_fst_fderiv_apply (γ := -f) hf.neg
    (hg.comp I.contDiff) (hgc.comp_homeomorph I.toHomeomorph) (I.symm v)
  simp only [hd] at hmodel
  rw [hset, hcov, hmodel]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp [hIsymm, hI, fderiv_neg, sub_eq_add_neg, add_comm]

/-- **The divergence theorem on a `C¹` subgraph.** For a unit vector `e`, a `C¹` height function
`f : (ℝ ∙ e)ᗮ → ℝ`, and a compactly supported `C¹` vector field `ψ : E → E`, the integral of
`tr (Dψ)` over `{x | ⟪e, x⟫ < f (π_H x)}` is `∫ y, (⟪e, ψ z_y⟫ - Df y (π_H (ψ z_y)))`, where
`z_y = (y : E) + f y • e` and `π_H = (ℝ ∙ e)ᗮ.orthogonalProjectionOnto`. -/
theorem setIntegral_setOf_inner_lt_apply_trace_fderiv (e : E) (he : ‖e‖ = 1)
    {f : (ℝ ∙ e)ᗮ → ℝ} (hf : ContDiff ℝ 1 f) {ψ : E → E} (hψ : ContDiff ℝ 1 ψ)
    (hψc : HasCompactSupport ψ) :
    ∫ x in {x : E | ⟪e, x⟫ < f ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x)},
        LinearMap.trace ℝ E (fderiv ℝ ψ x : E →ₗ[ℝ] E) =
      ∫ y : (ℝ ∙ e)ᗮ,
        (⟪e, ψ ((y : E) + f y • e)⟫ -
          fderiv ℝ f y ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto (ψ ((y : E) + f y • e)))) := by
  let b := stdOrthonormalBasis ℝ E
  have hg (i) : ContDiff ℝ 1 fun x => ⟪b i, ψ x⟫ := contDiff_const.inner ℝ hψ
  have hgc (i) : HasCompactSupport fun x => ⟪b i, ψ x⟫ :=
    hψc.comp_left (g := fun w => ⟪b i, w⟫) (inner_zero_right _)
  have htr (x : E) : LinearMap.trace ℝ E (fderiv ℝ ψ x : E →ₗ[ℝ] E) =
      ∑ i, fderiv ℝ (fun z => ⟪b i, ψ z⟫) x (b i) := by
    rw [LinearMap.trace_eq_sum_inner _ b]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [fderiv_inner_apply ℝ (differentiableAt_const _) (hψ.differentiable one_ne_zero x)]
    simp
  have hemb := isClosedEmbedding_add_smul_graph e hf.continuous
  have hbdry (i) : Integrable fun y : (ℝ ∙ e)ᗮ =>
      (⟪e, b i⟫ - fderiv ℝ f y ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto (b i))) *
        ⟪b i, ψ ((y : E) + f y • e)⟫ := by
    have hc1 : Continuous fun y : (ℝ ∙ e)ᗮ =>
        ⟪e, b i⟫ - fderiv ℝ f y ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto (b i)) :=
      continuous_const.sub ((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const)
    have hc2 : Continuous fun y : (ℝ ∙ e)ᗮ => ⟪b i, ψ ((y : E) + f y • e)⟫ :=
      (hg i).continuous.comp hemb.continuous
    exact (hc1.mul hc2).integrable_of_hasCompactSupport
      ((hgc i).comp_isClosedEmbedding hemb).mul_left
  simp_rw [htr]
  rw [integral_finsetSum _ fun i _ => (((hg i).continuous_fderiv one_ne_zero).clm_apply
    continuous_const).integrable_of_hasCompactSupport
      ((hgc i).fderiv_apply (𝕜 := ℝ) (b i)) |>.integrableOn]
  simp_rw [setIntegral_setOf_inner_lt_apply_fderiv_apply e he hf (hg _) (hgc _)]
  rw [← integral_finsetSum _ fun i _ => hbdry i]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  set w := ψ ((y : E) + f y • e)
  let L : E →L[ℝ] ℝ := innerSL ℝ e - (fderiv ℝ f y).comp (ℝ ∙ e)ᗮ.orthogonalProjectionOnto
  have hw : ∑ i, ⟪b i, w⟫ • (b i : E) = w := b.sum_repr' w
  have hLw := congrArg L hw
  simpa [L, map_sum, map_smul, smul_eq_mul, mul_comm] using hLw

/-- Integrability of the boundary integrand on the `C¹` graph `y ↦ (y : E) + f y • e` of a
compactly supported `C¹` vector field `ψ`. -/
private theorem integrable_subgraph_boundary_integrand (e : E) {f : (ℝ ∙ e)ᗮ → ℝ}
    (hf : ContDiff ℝ 1 f) {ψ : E → E} (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) :
    Integrable (fun y : (ℝ ∙ e)ᗮ =>
      ⟪e, ψ ((y : E) + f y • e)⟫ -
        fderiv ℝ f y ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto (ψ ((y : E) + f y • e)))) volume := by
  let π := (ℝ ∙ e)ᗮ.orthogonalProjectionOnto
  have hemb := isClosedEmbedding_add_smul_graph e hf.continuous
  have hψf : Continuous fun y : (ℝ ∙ e)ᗮ => ψ ((y : E) + f y • e) :=
    hψ.continuous.comp hemb.continuous
  have hψfc : HasCompactSupport fun y : (ℝ ∙ e)ᗮ => ψ ((y : E) + f y • e) :=
    hψc.comp_isClosedEmbedding hemb
  have h1 : Integrable (fun y : (ℝ ∙ e)ᗮ => ⟪e, ψ ((y : E) + f y • e)⟫) volume :=
    (continuous_const.inner hψf).integrable_of_hasCompactSupport
      (hψfc.comp_left (inner_zero_right e))
  have h2 : Integrable (fun y : (ℝ ∙ e)ᗮ => fderiv ℝ f y (π (ψ ((y : E) + f y • e)))) volume :=
    ((hf.continuous_fderiv one_ne_zero).clm_apply (π.continuous.comp hψf))
      |>.integrable_of_hasCompactSupport (hψfc.mono fun _ hy h0 => hy (by simp [h0]))
  exact h1.sub h2

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Pointwise algebraic identity identifying the difference of upper and lower `C¹` graph boundary
integrands with the symmetric-slab boundary integrand. -/
private theorem subgraph_boundary_sub_eq_slab_boundary (e : E) {w : (ℝ ∙ e)ᗮ → ℝ}
    (hw : ContDiff ℝ 1 w) (ψ : E → E) (y : (ℝ ∙ e)ᗮ) :
    (⟪e, ψ ((y : E) + (w y / 2) • e)⟫ -
        fderiv ℝ (fun z : (ℝ ∙ e)ᗮ => w z / 2) y
          ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto (ψ ((y : E) + (w y / 2) • e)))) -
      (⟪e, ψ ((y : E) + -(w y / 2) • e)⟫ -
        fderiv ℝ (fun z : (ℝ ∙ e)ᗮ => -(w z / 2)) y
          ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto (ψ ((y : E) + -(w y / 2) • e)))) =
      ⟪e, ψ ((y : E) + (w y / 2) • e) - ψ ((y : E) - (w y / 2) • e)⟫ -
        (2 : ℝ)⁻¹ * fderiv ℝ w y
          ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto
            (ψ ((y : E) + (w y / 2) • e) + ψ ((y : E) - (w y / 2) • e))) := by
  have hfpos : ContDiff ℝ 1 fun z : (ℝ ∙ e)ᗮ => w z / 2 := hw.div_const 2
  have hdpos : fderiv ℝ (fun z : (ℝ ∙ e)ᗮ => w z / 2) y = (2 : ℝ)⁻¹ • fderiv ℝ w y := by
    simpa [div_eq_inv_mul] using
      ((hw.differentiable one_ne_zero y).hasFDerivAt.const_mul (2 : ℝ)⁻¹).fderiv
  have hdneg : fderiv ℝ (fun z : (ℝ ∙ e)ᗮ => -(w z / 2)) y = -((2 : ℝ)⁻¹ • fderiv ℝ w y) := by
    have h := ((hfpos.differentiable one_ne_zero y).hasFDerivAt.neg).fderiv
    rwa [Pi.neg_def, hdpos] at h
  rw [hdpos, hdneg, neg_smul, ← sub_eq_add_neg (y : E)]
  simp only [neg_apply, smul_apply, smul_eq_mul, inner_sub_right, map_add]
  ring

/-- **Integrability of the boundary integrand on a smooth symmetric slab.** -/
theorem integrable_slab_boundary_integrand (e : E) {w : (ℝ ∙ e)ᗮ → ℝ} (hw : ContDiff ℝ 1 w)
    {ψ : E → E} (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) :
    Integrable (fun y : (ℝ ∙ e)ᗮ =>
      ⟪e, ψ ((y : E) + (w y / 2) • e) - ψ ((y : E) - (w y / 2) • e)⟫ -
        (2 : ℝ)⁻¹ * fderiv ℝ w y
          ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto
            (ψ ((y : E) + (w y / 2) • e) + ψ ((y : E) - (w y / 2) • e)))) volume := by
  refine ((integrable_subgraph_boundary_integrand e (hw.div_const 2) hψ hψc).sub
    (integrable_subgraph_boundary_integrand e (hw.div_const 2).neg hψ hψc)).congr
    (Eventually.of_forall fun y => ?_)
  simpa only [Pi.sub_apply, neg_smul] using subgraph_boundary_sub_eq_slab_boundary e hw ψ y

/-- **The divergence theorem on a smooth symmetric slab.** For a unit vector `e`, a nonnegative
`C¹` width `w : (ℝ ∙ e)ᗮ → ℝ`, and a compactly supported `C¹` vector field `ψ : E → E`,
`∫_{|⟪e, x⟫| < w (π_H x) / 2} tr (Dψ x) dx =
  ∫ y, (⟪e, ψ z_+ - ψ z_-⟫ - (1/2) Dw y (π_H (ψ z_+ + ψ z_-)))`,
where `z_± = (y : E) ± (w y / 2) • e` and `π_H = (ℝ ∙ e)ᗮ.orthogonalProjectionOnto`. -/
theorem setIntegral_setOf_abs_inner_lt_div_two_trace_fderiv (e : E) (he : ‖e‖ = 1)
    {w : (ℝ ∙ e)ᗮ → ℝ} (hw : ContDiff ℝ 1 w) (hw0 : ∀ y, 0 ≤ w y) {ψ : E → E}
    (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) :
    ∫ x in {x : E | |⟪e, x⟫| < w ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x) / 2},
        LinearMap.trace ℝ E (fderiv ℝ ψ x : E →ₗ[ℝ] E) =
      ∫ y : (ℝ ∙ e)ᗮ,
        (⟪e, ψ ((y : E) + (w y / 2) • e) - ψ ((y : E) - (w y / 2) • e)⟫ -
          (2 : ℝ)⁻¹ * fderiv ℝ w y
            ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto
              (ψ ((y : E) + (w y / 2) • e) + ψ ((y : E) - (w y / 2) • e)))) := by
  let π := (ℝ ∙ e)ᗮ.orthogonalProjectionOnto
  set S := {x : E | |⟪e, x⟫| < w (π x) / 2}
  set Upos := {x : E | ⟪e, x⟫ < w (π x) / 2}
  set Uneg := {x : E | ⟪e, x⟫ < -(w (π x) / 2)}
  -- Up to the null lower boundary graph, the symmetric slab is `Upos \ Uneg` with `Uneg ⊆ Upos`.
  have hsub : Uneg ⊆ Upos := fun x (hx : ⟪e, x⟫ < -(w (π x) / 2)) =>
    hx.trans_le (by linarith [hw0 (π x)])
  have hUneg_m : MeasurableSet Uneg :=
    measurableSet_lt (continuous_const.inner continuous_id).measurable
      ((hw.continuous.div_const 2).neg.comp π.continuous).measurable
  have hae : S =ᵐ[volume] (Upos \ Uneg : Set E) := by
    have hSS : S ⊆ Upos \ Uneg := fun x (hx : |⟪e, x⟫| < w (π x) / 2) => by
      obtain ⟨h1, h2⟩ := abs_lt.1 hx
      exact ⟨h2, not_lt.2 h1.le⟩
    have hnull : volume ((Upos \ Uneg) \ S) = 0 := by
      refine measure_mono_null (fun x hx => ?_)
        (volume_setOf_inner_eq_apply_orthogonalProjectionOnto e he
          ((hw.continuous.div_const 2).neg.measurable))
      have h1 : ⟪e, x⟫ < w (π x) / 2 := hx.1.1
      have h2 : -(w (π x) / 2) ≤ ⟪e, x⟫ := not_lt.1 hx.1.2
      have h3 : ¬ |⟪e, x⟫| < w (π x) / 2 := hx.2
      exact le_antisymm (by contrapose! h3; exact abs_lt.2 ⟨h3, h1⟩) h2
    exact (ae_eq_set.2 ⟨by simp [sdiff_eq_empty.2 hSS], hnull⟩)
  have hdiv_cont : Continuous fun x : E => LinearMap.trace ℝ E (fderiv ℝ ψ x : E →ₗ[ℝ] E) := by
    let b := stdOrthonormalBasis ℝ E
    simpa only [LinearMap.trace_eq_sum_inner _ b, ContinuousLinearMap.coe_coe] using
      continuous_finsetSum _ fun i _ =>
        continuous_const.inner ((hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const)
  have hdiv_int : Integrable fun x : E => LinearMap.trace ℝ E (fderiv ℝ ψ x : E →ₗ[ℝ] E) :=
    hdiv_cont.integrable_of_hasCompactSupport
      ((hψc.fderiv ℝ).comp_left (g := fun L : E →L[ℝ] E => LinearMap.trace ℝ E (L : E →ₗ[ℝ] E))
        (by simp))
  -- Subtract the upper and lower subgraph divergence identities.
  rw [setIntegral_congr_set hae, setIntegral_sdiff hUneg_m hdiv_int.integrableOn hsub,
    setIntegral_setOf_inner_lt_apply_trace_fderiv e he (hw.div_const 2) hψ hψc,
    setIntegral_setOf_inner_lt_apply_trace_fderiv e he (hw.div_const 2).neg hψ hψc,
    ← integral_sub (integrable_subgraph_boundary_integrand e (hw.div_const 2) hψ hψc)
      (integrable_subgraph_boundary_integrand e (hw.div_const 2).neg hψ hψc)]
  exact integral_congr_ae (Eventually.of_forall fun y =>
    by simpa only [neg_smul] using subgraph_boundary_sub_eq_slab_boundary e hw ψ y)

end Subgraph

end TauCeti
