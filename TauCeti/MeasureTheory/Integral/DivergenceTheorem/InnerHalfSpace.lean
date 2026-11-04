/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Euclidean.Volume.Measure
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.LinearAlgebra.Trace
import TauCeti.Analysis.Sobolev.Trace.IntegrationByParts
import TauCeti.Geometry.Euclidean.Volume.Measure
import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# The divergence theorem on a half-space of an inner product space

Let `F` be a finite-dimensional real inner product space of dimension `n`, let `ν` be a unit
vector and `c` a real number. This file proves the divergence theorem on the open half-space
`H = {x | ⟪x, ν⟫ < c}`, whose outward unit normal is `ν` and whose boundary is the hyperplane
`{x | ⟪x, ν⟫ = c}` carrying the normalized `(n - 1)`-dimensional Hausdorff measure `μHE[n - 1]`.
For a compactly supported `C¹` vector field `φ`,

`∫_H tr (Dφ) = ∫_{⟪x, ν⟫ = c} ⟪φ x, ν⟫ dμHE[n - 1]`.

The hyperplane is the image of the orthogonal complement `(ℝ ∙ ν)ᗮ` under the isometry
`y ↦ c • ν + y`, so its Hausdorff measure is the image of the Lebesgue measure of that
`(n - 1)`-dimensional inner product space
(`TauCeti.euclideanHausdorffMeasure_restrict_setOf_inner_eq`, in
`TauCeti.Geometry.Euclidean.Volume.Measure`). The divergence theorem is transported
by a linear isometry `F ≃ ℝ × (ℝ ∙ ν)ᗮ` from its form on the coordinate half-space of the `ℓ²`
product, `TauCeti.setIntegral_normalHalfSpace_fderiv_apply`.

## Main results

* `TauCeti.setIntegral_setOf_inner_lt_fderiv_apply`: for a compactly supported `C¹` function `g`
  and a direction `v`, `∫_H ∂_v g = ⟪v, ν⟫ ∫_{⟪x, ν⟫ = c} g dμHE[n - 1]`.
* `TauCeti.setIntegral_setOf_inner_lt_trace_fderiv`: the divergence theorem on `H` for compactly
  supported `C¹` vector fields.

## References

* L. C. Evans, *Partial Differential Equations*, Appendix C.2 (the Gauss–Green theorem).
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Set Module
open scoped RealInnerProductSpace

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] {ν : F}

variable [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

/-- **The divergence theorem on a half-space, directional form.** For a unit vector `ν`, a
compactly supported `C¹` function `g` and a direction `v`, the integral of `∂_v g` over the
half-space `{x | ⟪x, ν⟫ < c}` is the integral of `g` over the boundary hyperplane against
`(n - 1)`-dimensional Hausdorff measure, weighted by the normal component `⟪v, ν⟫` of `v`. -/
theorem setIntegral_setOf_inner_lt_fderiv_apply (hν : ‖ν‖ = 1) (c : ℝ) {g : F → ℝ}
    (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) (v : F) :
    ∫ x in {x | ⟪x, ν⟫ < c}, fderiv ℝ g x v =
      ⟪v, ν⟫ * ∫ x in {x | ⟪x, ν⟫ = c}, g x ∂μHE[finrank ℝ F - 1] := by
  -- The linear isometry `x ↦ (-⟪x, ν⟫, x - ⟪x, ν⟫ • ν)` onto the `ℓ²` product `ℝ × (ℝ ∙ ν)ᗮ`.
  let e : F ≃ₗᵢ[ℝ] WithLp 2 (ℝ × (ℝ ∙ ν)ᗮ) := (ℝ ∙ ν).orthogonalDecomposition.trans
    (LinearIsometryEquiv.withLpProdCongr 2
      ((LinearIsometryEquiv.toSpanUnitSingleton ν hν).symm.trans (LinearIsometryEquiv.neg ℝ))
      (LinearIsometryEquiv.refl ℝ (ℝ ∙ ν)ᗮ))
  have he (t : ℝ) (y : (ℝ ∙ ν)ᗮ) : e.symm (WithLp.toLp 2 (t, y)) = (-t) • ν + (y : F) := by
    simp [e, LinearIsometryEquiv.symm_apply_eq, LinearIsometryEquiv.coe_refl]
  have hfst (x : F) : (e x).fst = -⟪x, ν⟫ := by
    have hy : ⟪((e x).snd : F), ν⟫ = 0 :=
      Submodule.mem_orthogonal_singleton_iff_inner_left.1 (e x).snd.2
    have hx : x = (-(e x).fst) • ν + ((e x).snd : F) := by
      rw [← he, ← WithLp.ofLp_fst, ← WithLp.ofLp_snd, Prod.mk.eta, WithLp.toLp_ofLp,
        e.symm_apply_apply]
    conv_rhs => rw [hx]
    simp [inner_add_left, real_inner_smul_left, hν, hy]
  have hH : {x : F | ⟪x, ν⟫ < c} = e ⁻¹' (normalHalfSpace (E := (ℝ ∙ ν)ᗮ) (-c)) := by
    ext x
    simp [hfst]
  have hmodel := setIntegral_normalHalfSpace_fderiv_apply (E := (ℝ ∙ ν)ᗮ) (g := g ∘ e.symm)
    (hg.comp e.symm.contDiff) (hgc.comp_homeomorph e.symm.toHomeomorph) (-c) (e v)
  have hd (z : WithLp 2 (ℝ × (ℝ ∙ ν)ᗮ)) :
      fderiv ℝ (g ∘ e.symm) z (e v) = fderiv ℝ g (e.symm z) v := by
    have h := ((hg.differentiable one_ne_zero (e.symm z)).hasFDerivAt.comp z
      e.symm.toContinuousLinearEquiv.hasFDerivAt).fderiv
    rw [h]
    simp
  have hcov := e.measurePreserving.setIntegral_preimage_emb e.toHomeomorph.measurableEmbedding
    (fun z => fderiv ℝ g (e.symm z) v) (normalHalfSpace (E := (ℝ ∙ ν)ᗮ) (-c))
  simp only [LinearIsometryEquiv.symm_apply_apply] at hcov
  simp only [hd] at hmodel
  rw [hH, hcov, hmodel, setIntegral_setOf_inner_eq hν, hfst]
  simp only [Function.comp_apply, he, neg_neg, neg_mul]

/-- **The divergence theorem on a half-space.** For a unit vector `ν` and a compactly supported
`C¹` vector field `φ`, the integral of the divergence `tr (Dφ)` over the half-space
`{x | ⟪x, ν⟫ < c}` is the flux `∫ ⟪φ, ν⟫` of `φ` through the boundary hyperplane
`{x | ⟪x, ν⟫ = c}` against `(n - 1)`-dimensional Hausdorff measure. -/
theorem setIntegral_setOf_inner_lt_trace_fderiv (hν : ‖ν‖ = 1) (c : ℝ) {φ : F → F}
    (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) :
    ∫ x in {x | ⟪x, ν⟫ < c}, LinearMap.trace ℝ F (fderiv ℝ φ x : F →ₗ[ℝ] F) =
      ∫ x in {x | ⟪x, ν⟫ = c}, ⟪φ x, ν⟫ ∂μHE[finrank ℝ F - 1] := by
  -- Expand the trace in an orthonormal basis `b` and apply the directional form to each
  -- coordinate `⟪b i, φ⟫` in the direction `b i`; then `∑ i, ⟪b i, ν⟫ ⟪b i, φ⟫ = ⟪φ, ν⟫`.
  let b := stdOrthonormalBasis ℝ F
  have hg (i) : ContDiff ℝ 1 fun x => ⟪b i, φ x⟫ := contDiff_const.inner ℝ hφ
  have hgc (i) : HasCompactSupport fun x => ⟪b i, φ x⟫ :=
    hφc.comp_left (g := fun w => ⟪b i, w⟫) (inner_zero_right _)
  have htr (x : F) : LinearMap.trace ℝ F (fderiv ℝ φ x : F →ₗ[ℝ] F) =
      ∑ i, fderiv ℝ (fun y => ⟪b i, φ y⟫) x (b i) := by
    rw [LinearMap.trace_eq_sum_inner _ b]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [fderiv_inner_apply ℝ (differentiableAt_const _) (hφ.differentiable one_ne_zero x)]
    simp
  simp_rw [htr]
  rw [integral_finsetSum _ fun i _ => ((hg i).continuous_fderiv one_ne_zero).clm_apply
    continuous_const |>.integrable_of_hasCompactSupport
      ((hgc i).fderiv_apply (𝕜 := ℝ) (b i)) |>.integrableOn]
  simp_rw [setIntegral_setOf_inner_lt_fderiv_apply hν c (hg _) (hgc _), ← integral_const_mul]
  rw [← integral_finsetSum _ fun i _ => (integrableOn_setOf_inner_eq hν c (hg i).continuous
    (hgc i)).const_mul _]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  beta_reduce
  rw [← real_inner_comm, ← b.sum_inner_mul_inner]
  exact Finset.sum_congr rfl fun i _ => by rw [real_inner_comm ν]

end TauCeti
