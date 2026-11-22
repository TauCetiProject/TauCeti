/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.Spectral.Flow
public import TauCeti.Analysis.InnerProductSpace.ContinuousFunctionalCalculus
public import TauCeti.Analysis.Matrix.HermitianSignature.Crossing
import TauCeti.LinearAlgebra.QuadraticForm.Isometry
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
public import Mathlib.Analysis.Calculus.Deriv.Slope
import TauCeti.Topology.Algebra.Indicator
import TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Eigenvector
import TauCeti.Analysis.InnerProductSpace.Symmetric.Signature
import TauCeti.Analysis.Normed.Operator.Restrict
import TauCeti.LinearAlgebra.End.Idempotent

/-!
# The spectral flow at a regular crossing

Let `A` be a path of self-adjoint operators on a real Hilbert space `H`, continuous near `t₀`,
with `A t₀` Fredholm and derivative `A'` at `t₀`. Its *crossing form* at `t₀` is the quadratic
form `Γ v = ⟪A' v, v⟫` on the kernel of `A t₀`
(`ContinuousLinearMap.crossingForm ((innerSL ℝ).comp (A t₀)) ((innerSL ℝ).comp A')`), and the
crossing is *regular* when `Γ` is nondegenerate. This file proves the regular-crossing formula
for Phillips' spectral flow `TauCeti.spectralFlow`: across a regular crossing the spectral flow is
the signature of the crossing form,

`spectralFlow A a b = sigPos Γ - sigNeg Γ`

for every `a < t₀` close to `t₀` and every `b > t₀` close enough to `t₀` (how close may depend on
`a`), so that positive crossings count positively. One-sided versions hold for a path given only
on one side of `t₀`, with one-sided continuity and derivatives: from `t₀` to `b > t₀` the spectral
flow is `-sigNeg Γ`, and from `a < t₀` to `t₀` it is `sigPos Γ`; they apply to a crossing at an
endpoint of the parameter interval. This is the infinite-dimensional counterpart of the crossing
computations of `TauCeti.Analysis.Matrix.HermitianSignature.Crossing`, to which the proof
reduces.

**Reduction to a finite-dimensional path.** Take a cut `c > 0` of `A t₀` for which the spectral
projection `P t₀` of `A t₀` for `[-c, c]` is the projection onto `K = ker (A t₀)`. For `t` near
`t₀` the spectral projection `P t` of `A t` for `[-c, c]` has the same finite rank and is close to
`P t₀`, so it maps `K` isomorphically onto its range. The path of forms on the fixed
finite-dimensional space `K`

`V t (v, w) = ⟪A t (P t v), P t w⟫`

vanishes at `t₀` and has derivative `⟪A' v, w⟫` there, since `V t (v, w) = ⟪(A t - A t₀) v, P t w⟫`.
Its crossing form at `t₀` is therefore `Γ`, and the finite-dimensional crossing theorems
(`ContinuousLinearMap.eventually_sigNeg_eq_add_sigNeg_crossingForm` and
`ContinuousLinearMap.eventually_sigNeg_eq_add_sigPos_crossingForm`) give the negative index of
`V t` just after and just before `t₀`. On the other hand the negative index of `V t` counts the
eigenvalues of `A t` in `[-c, 0)` (`IsSelfAdjoint.sigNeg_add_spectralCount_eq_finrank`): the form
`x ↦ ⟪A t x, x⟫` is negative definite on the spectral subspace for `[-c, 0)` and nonnegative on
that for `[0, c]`
(`ContinuousLinearMap.re_inner_apply_self_neg_of_mem_range_cfc_indicator` and
`ContinuousLinearMap.re_inner_apply_self_nonneg_of_mem_range_cfc_indicator`), and these two
subspaces split the range of `P t`, so Sylvester's law of inertia
(`QuadraticForm.sigNeg_eq_finrank_of_injective`) applies. So `V t` has negative index
`dim K - spectralCount c (A t)`, and the spectral flow over an interval with the single cut `c` is
a difference of these counts.

**Regular crossings are isolated.** The compressed path also detects injectivity: a vector of the
kernel of `A t` is an eigenvector for the eigenvalue `0 ∈ [-c, c]`, so it is fixed by `P t` and is
`P t v` for some `v ∈ K`, along which `V t` vanishes. So `A t` is injective wherever `V t` is
nondegenerate, and by the finite-dimensional isolation of regular crossings
(`ContinuousLinearMap.eventually_nondegenerate_of_crossingForm_nondegenerate`) `A t` is injective
at every `t ≠ t₀` close to a regular crossing `t₀`
(`TauCeti.eventually_ker_eq_bot_of_crossingForm_nondegenerate`). These local results are summed
over the crossings of a path on a compact interval in
`TauCeti.Analysis.Fredholm.Spectral.RegularCrossings`.

## Main results

* `IsSelfAdjoint.sigNeg_add_spectralCount_eq_finrank`: the negative index of the form of a
  self-adjoint operator on the range of its spectral projection for a cut `[-c, c]`, plus the
  number of its eigenvalues in `[0, c]`, is the rank of that projection.
* `TauCeti.eventually_spectralFlow_right_eq_neg_sigNeg_crossingForm`: the spectral flow just after
  a regular crossing.
* `TauCeti.eventually_spectralFlow_left_eq_sigPos_crossingForm`: the spectral flow just before a
  regular crossing.
* `TauCeti.eventually_spectralFlow_eq_sigPos_sub_sigNeg_crossingForm`: **the regular-crossing
  formula**, the spectral flow across a regular crossing.
* `TauCeti.eventually_ker_eq_bot_of_crossingForm_nondegenerate`: regular crossings are isolated.

## References

* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc.
  **27** (1995), 1--33, Section 4 (the crossing operator, and Theorem 4.21 on the spectral flow
  across regular crossings).
* J. Phillips, *Self-adjoint Fredholm operators and spectral flow*, Canad. Math. Bull. **39**
  (1996), 460--467.
-/

public section

open Filter Function Set Topology ContinuousLinearMap
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

namespace TauCeti

/-! ### The negative index of a self-adjoint operator near a cut -/

/-- **The spectral splitting at a cut.** At a cut `c` of a self-adjoint operator `S`, the ranges of
the spectral projections for `[-c, 0)` and for `[0, c]` lie in the range of the projection `P` for
`[-c, c]`, are finite-dimensional and independent, and their dimensions add up to the rank of `P`.
-/
private theorem spectralSplitting {S : H →L[ℝ] H} (hS : IsSelfAdjoint S) {c : ℝ} (hc : 0 ≤ c)
    (h₁ : -c ∉ spectrum ℝ S) (h₂ : c ∉ spectrum ℝ S)
    (hfd : FiniteDimensional ℝ (cfc ((Icc (-c) c).indicator (1 : ℝ → ℝ)) S).range) :
    ∃ (_ : FiniteDimensional ℝ (cfc ((Ico (-c) 0).indicator (1 : ℝ → ℝ)) S).range)
      (_ : FiniteDimensional ℝ (cfc ((Icc 0 c).indicator (1 : ℝ → ℝ)) S).range),
      (cfc ((Ico (-c) 0).indicator (1 : ℝ → ℝ)) S).range ≤
          (cfc ((Icc (-c) c).indicator (1 : ℝ → ℝ)) S).range ∧
        (cfc ((Icc 0 c).indicator (1 : ℝ → ℝ)) S).range ≤
          (cfc ((Icc (-c) c).indicator (1 : ℝ → ℝ)) S).range ∧
        (cfc ((Ico (-c) 0).indicator (1 : ℝ → ℝ)) S).range ⊓
          (cfc ((Icc 0 c).indicator (1 : ℝ → ℝ)) S).range = ⊥ ∧
        Module.finrank ℝ (cfc ((Icc (-c) c).indicator (1 : ℝ → ℝ)) S).range =
          Module.finrank ℝ (cfc ((Ico (-c) 0).indicator (1 : ℝ → ℝ)) S).range +
            spectralCount c S := by
  set Em := cfc ((Ico (-c) 0).indicator (1 : ℝ → ℝ)) S
  set Ep := cfc ((Icc 0 c).indicator (1 : ℝ → ℝ)) S
  have hfr : Disjoint (frontier (Icc (-c) c)) (spectrum ℝ S) := by
    rw [frontier_Icc (by linarith), disjoint_left]
    rintro x (rfl | rfl)
    exacts [h₁, h₂]
  have hcP : ContinuousOn ((Icc (-c) c).indicator (1 : ℝ → ℝ)) (spectrum ℝ S) :=
    continuousOn_const.continuousOn_indicator_of_disjoint_frontier hfr
  have hfin : (spectrum ℝ S ∩ Icc (-c) c).Finite :=
    hS.finite_spectrum_inter_of_finiteDimensional_range_cfc_indicator hcP hfd
  have hsubm : Ico (-c) 0 ⊆ Icc (-c) c := fun x hx ↦ ⟨hx.1, by linarith [hx.2]⟩
  have hsubp : Icc 0 c ⊆ Icc (-c) c := Icc_subset_Icc (by linarith) le_rfl
  have hcm := hfin.continuousOn_indicator (f := (1 : ℝ → ℝ)) hsubm hfr
  have hcp := hfin.continuousOn_indicator (f := (1 : ℝ → ℝ)) hsubp hfr
  have hmP : Em.range ≤ _ := S.range_cfc_indicator_le_of_subset hsubm hcm hcP
  have hpP : Ep.range ≤ _ := S.range_cfc_indicator_le_of_subset hsubp hcp hcP
  have : FiniteDimensional ℝ Em.range := Submodule.finiteDimensional_of_le hmP
  have : FiniteDimensional ℝ Ep.range := Submodule.finiteDimensional_of_le hpP
  have hdisj : Disjoint (Ico (-c) 0) (Icc 0 c) :=
    disjoint_left.2 fun x (hx : x ∈ Ico (-c) 0) (hx' : x ∈ Icc 0 c) ↦ (not_lt.2 hx'.1) hx.2
  refine ⟨‹_›, ‹_›, hmP, hpP, ?_, ?_⟩
  · -- The two projections are idempotents with product `0`.
    have hE : IsIdempotentElem (Em : Module.End ℝ H) :=
      (TauCeti.isStarProjection_cfc_indicator S _).isIdempotentElem.map toLinearMapRingHom
    have h0 : (Em : Module.End ℝ H) * Ep = 0 := by
      simpa using congr(($(show Em * Ep = 0 by
        simp [Em, Ep, TauCeti.cfc_indicator_mul_cfc_indicator S hcm hcp, hdisj.inter_eq]) :
          Module.End ℝ H))
    exact disjoint_iff.1 (hE.disjoint_range_of_mul_eq_zero h0)
  · have h := S.finrank_range_cfc_indicator_union hdisj hcm hcp
    rwa [Ico_union_Icc_eq_Icc (by linarith) hc, ← spectralCount_def] at h

/-- **Counting the eigenvalues below `0` by a negative index.** Let `c ≥ 0` be a cut of a
self-adjoint operator `S`: neither `-c` nor `c` is in its spectrum, and its spectral projection
`P` for `[-c, c]` has finite rank. Let `U : K → H` be an injective map onto the range of `P`. Then
the negative index of the form `(v, w) ↦ ⟪S (U v), U w⟫` on `K`, plus the number
`spectralCount c S` of eigenvalues of `S` in `[0, c]`, is the dimension of `K`: the negative index
counts the eigenvalues of `S` in `[-c, 0)`. -/
theorem _root_.IsSelfAdjoint.sigNeg_add_spectralCount_eq_finrank {S : H →L[ℝ] H}
    (hS : IsSelfAdjoint S) {c : ℝ} (hc : 0 ≤ c) (h₁ : -c ∉ spectrum ℝ S) (h₂ : c ∉ spectrum ℝ S)
    (hfd : FiniteDimensional ℝ (cfc ((Icc (-c) c).indicator (1 : ℝ → ℝ)) S).range)
    {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K] {U : K →L[ℝ] H} (hU : Injective U)
    (hUr : (U : K →ₗ[ℝ] H).range = (cfc ((Icc (-c) c).indicator (1 : ℝ → ℝ)) S).range) :
    sigNeg (((innerSL ℝ).comp S).bilinearComp U U).toBilinForm.toQuadraticMap +
      spectralCount c S = Module.finrank ℝ K := by
  obtain ⟨_, _, hmP, hpP, hdisj, hsum⟩ := spectralSplitting hS hc h₁ h₂ hfd
  have : FiniteDimensional ℝ (U : K →ₗ[ℝ] H).range := by rw [hUr]; exact hfd
  have : FiniteDimensional ℝ K :=
    FiniteDimensional.of_injective (U : K →ₗ[ℝ] H).rangeRestrict
      ((LinearMap.injective_rangeRestrict_iff _).2 hU)
  have hKF : Module.finrank ℝ K =
      Module.finrank ℝ (cfc ((Icc (-c) c).indicator (1 : ℝ → ℝ)) S).range := by
    rw [← hUr, LinearMap.finrank_range_of_inj hU]
  -- On `K`, the form is negative definite on the preimage of the spectral subspace for `[-c, 0)`
  -- and nonnegative on that for `[0, c]`.
  rw [QuadraticForm.sigNeg_eq_finrank_of_injective _ (U := (U : K →ₗ[ℝ] H)) hU (hUr ▸ hmP)
    (hUr ▸ hpP) hdisj
    (by rw [hKF, hsum, spectralCount_def])
    (fun v hv hv0 ↦ by
      simpa using S.re_inner_apply_self_neg_of_mem_range_cfc_indicator
        (fun x (hx : x ∈ Ico (-c) 0) ↦ hx.2) hv fun h ↦ hv0 (hU (h.trans (map_zero U).symm)))
    (fun v hv ↦ by
      simpa using S.re_inner_apply_self_nonneg_of_mem_range_cfc_indicator
        (fun x (hx : x ∈ Icc 0 c) ↦ hx.1) hv), hKF, hsum]

/-! ### The compressed path of forms -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The form `(v, w) ↦ ⟪B (ι v), ι w⟫` on `E` of an operator `B` on `H`, as a continuous linear
map in `B`. -/
private noncomputable def restrictForm (ι : E →L[ℝ] H) :
    (H →L[ℝ] H) →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ :=
  compL ℝ E (H →L[ℝ] ℝ) (E →L[ℝ] ℝ) ((compL ℝ E H ℝ).flip ι) ∘L
    compL ℝ E H (H →L[ℝ] ℝ) (innerSL ℝ) ∘L (compL ℝ E H H).flip ι

omit [CompleteSpace H] in
private theorem restrictForm_apply (ι : E →L[ℝ] H) (B : H →L[ℝ] H) (v w : E) :
    restrictForm ι B v w = ⟪B (ι v), ι w⟫_ℝ := by
  -- `compL` sees `innerSL ℝ` with `RingHom.id ℝ` for `starRingEnd ℝ`, which `simp` cannot match.
  simp only [restrictForm, coe_comp, Function.comp_apply, flip_apply, compL_apply]
  exact innerSL_apply_apply ..

variable {A : ℝ → H →L[ℝ] H} {A' : H →L[ℝ] H} {t₀ c : ℝ} {ι : E →L[ℝ] H}

/-- The path of forms `V t (v, w) = ⟪A t (P t (ι v)), P t (ι w)⟫` on `E`, where `P t` is the
spectral projection of `A t` for `[-c, c]`. -/
private noncomputable def compressedForm (A : ℝ → H →L[ℝ] H) (c : ℝ) (ι : E →L[ℝ] H) (t : ℝ) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  ((innerSL ℝ).comp (A t)).bilinearComp (cfc ((Icc (-c) c).indicator (1 : ℝ → ℝ)) (A t) ∘L ι)
    (cfc ((Icc (-c) c).indicator (1 : ℝ → ℝ)) (A t) ∘L ι)

/-- If `A t₀` vanishes on the image of `ι`, then `V t (v, w) = ⟪P t ((A t - A t₀) (ι v)), ι w⟫`,
since `P t` is a self-adjoint idempotent commuting with `A t`. -/
private theorem compressedForm_eq (hK : ∀ v, A t₀ (ι v) = 0) (t : ℝ) :
    compressedForm A c ι t =
      restrictForm ι (cfc ((Icc (-c) c).indicator (1 : ℝ → ℝ)) (A t) * (A t - A t₀)) := by
  set P := cfc ((Icc (-c) c).indicator (1 : ℝ → ℝ)) (A t)
  have hcomm : P * A t = A t * P := (Commute.cfc_real (Commute.refl (A t)) _).eq
  have hP := (cfc_predicate _ (A t) : IsSelfAdjoint P).isSymmetric
  ext v w
  have h₁ : A t (P (ι v)) = P (A t (ι v)) := by
    simpa [mul_def] using congr($hcomm.symm (ι v))
  have h₂ : ⟪P (P (A t (ι v))), ι w⟫_ℝ = ⟪P (A t (ι v)), P (ι w)⟫_ℝ := hP _ _
  rw [restrictForm_apply, mul_def, ContinuousLinearMap.comp_apply, sub_apply, hK v, sub_zero]
  simp only [compressedForm, bilinearComp_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply]
  rw [h₁, ← h₂, cfc_indicator_cfc_indicator_apply]

/-- The compressed path vanishes at `t₀` when `A t₀` vanishes on the image of `ι`. -/
private theorem compressedForm_self (hK : ∀ v, A t₀ (ι v) = 0) :
    compressedForm A c ι t₀ = 0 := by
  rw [compressedForm_eq hK, sub_self, mul_zero, map_zero]

/-- **The slope of the compressed path.** If `A t₀` vanishes on the image of `ι` and the spectral
projection `P t₀` fixes it, then along any filter on which `P t` tends to `P t₀` and the slope of
`A` at `t₀` tends to `A'`, the slope of the compressed path at `t₀` tends to
`(v, w) ↦ ⟪A' (ι v), ι w⟫`. -/
private theorem tendsto_slope_compressedForm {l : Filter ℝ} (hK : ∀ v, A t₀ (ι v) = 0)
    (hPK : ∀ v, cfc ((Icc (-c) c).indicator (1 : ℝ → ℝ)) (A t₀) (ι v) = ι v)
    (hP : Tendsto (fun t ↦ cfc ((Icc (-c) c).indicator (1 : ℝ → ℝ)) (A t)) l
      (𝓝 (cfc ((Icc (-c) c).indicator (1 : ℝ → ℝ)) (A t₀))))
    (hA : Tendsto (slope A t₀) l (𝓝 A')) :
    Tendsto (slope (compressedForm A c ι) t₀) l (𝓝 (restrictForm ι A')) := by
  set P := fun t ↦ cfc ((Icc (-c) c).indicator (1 : ℝ → ℝ)) (A t)
  have hlim : restrictForm ι A' = restrictForm ι (P t₀ * A') := by
    ext v w
    have h : ⟪P t₀ (A' (ι v)), ι w⟫_ℝ = ⟪A' (ι v), P t₀ (ι w)⟫_ℝ :=
      (cfc_predicate _ (A t₀) : IsSelfAdjoint (P t₀)).isSymmetric _ _
    rw [restrictForm_apply, restrictForm_apply, mul_def, ContinuousLinearMap.comp_apply, h, hPK w]
  have heq : slope (compressedForm A c ι) t₀ = fun t ↦ restrictForm ι (P t * slope A t₀ t) := by
    funext t
    rw [slope_def_module, slope_def_module, compressedForm_self hK,
      sub_zero (compressedForm A c ι t), compressedForm_eq hK, mul_smul_comm, map_smul]
  rw [heq, hlim]
  exact ((restrictForm ι).continuous.tendsto _).comp (hP.mul hA)

/-- **The derivative of the compressed path.** If `A t₀` vanishes on the image of `ι`, the spectral
projection `P t₀` fixes it and `P` is continuous within `s` at `t₀`, then the compressed path has
derivative `(v, w) ↦ ⟪A' (ι v), ι w⟫` within `s` at `t₀`. -/
private theorem hasDerivWithinAt_compressedForm {s : Set ℝ} (hK : ∀ v, A t₀ (ι v) = 0)
    (hPK : ∀ v, cfc ((Icc (-c) c).indicator (1 : ℝ → ℝ)) (A t₀) (ι v) = ι v)
    (hP : ContinuousWithinAt (fun t ↦ cfc ((Icc (-c) c).indicator (1 : ℝ → ℝ)) (A t)) s t₀)
    (hA : HasDerivWithinAt A A' s t₀) :
    HasDerivWithinAt (compressedForm A c ι) (restrictForm ι A') s t₀ := by
  rw [hasDerivWithinAt_iff_tendsto_slope] at hA
  rw [hasDerivWithinAt_iff_tendsto_slope (f := compressedForm A c ι) (f' := restrictForm ι A')]
  exact tendsto_slope_compressedForm hK hPK
    (hP.tendsto.mono_left (nhdsWithin_mono _ sdiff_subset)) hA

/-- **The derivative of the compressed path**, two-sided version of
`hasDerivWithinAt_compressedForm`. -/
private theorem hasDerivAt_compressedForm (hK : ∀ v, A t₀ (ι v) = 0)
    (hPK : ∀ v, cfc ((Icc (-c) c).indicator (1 : ℝ → ℝ)) (A t₀) (ι v) = ι v)
    (hP : ContinuousAt (fun t ↦ cfc ((Icc (-c) c).indicator (1 : ℝ → ℝ)) (A t)) t₀)
    (hA : HasDerivAt A A' t₀) :
    HasDerivAt (compressedForm A c ι) (restrictForm ι A') t₀ := by
  rw [hasDerivAt_iff_tendsto_slope] at hA
  rw [hasDerivAt_iff_tendsto_slope (f := compressedForm A c ι) (f' := restrictForm ι A')]
  exact tendsto_slope_compressedForm hK hPK (hP.tendsto.mono_left nhdsWithin_le_nhds) hA

/-- The compressed path is symmetric at every time at which `A` is self-adjoint. -/
private theorem isSymm_compressedForm {t : ℝ} (hst : IsSelfAdjoint (A t)) :
    (compressedForm A c ι t).toBilinForm.IsSymm :=
  isSymm_toBilinForm_iff.2 fun v w ↦ by
    simp only [compressedForm, bilinearComp_apply, ContinuousLinearMap.comp_apply,
      innerSL_apply_apply]
    exact (hst.isSymmetric _ _).trans (real_inner_comm _ _)

/-- **The compressed path detects the kernel.** Let `c ≥ 0` be such that neither `-c` nor `c` is in
the spectrum of the self-adjoint operator `A t`, and let `P t ∘ ι` map onto the range of the
spectral projection `P t` of `A t` for `[-c, c]`. If `V t` is nondegenerate, then `A t` is
injective: a vector of its kernel is an eigenvector for `0 ∈ [-c, c]`, so it is fixed by `P t`,
hence of the form `P t (ι v)`, and then `V t (v, ·) = 0`. -/
private theorem ker_eq_bot_of_nondegenerate_compressedForm {t : ℝ} (hst : IsSelfAdjoint (A t))
    (hc : 0 ≤ c) (h₁ : -c ∉ spectrum ℝ (A t)) (h₂ : c ∉ spectrum ℝ (A t))
    (hrange : ((cfc ((Icc (-c) c).indicator (1 : ℝ → ℝ)) (A t) ∘L ι : E →L[ℝ] H) :
      E →ₗ[ℝ] H).range = (cfc ((Icc (-c) c).indicator (1 : ℝ → ℝ)) (A t)).range)
    (hnd : (compressedForm A c ι t).toBilinForm.Nondegenerate) : (A t).ker = ⊥ := by
  set P := cfc ((Icc (-c) c).indicator (1 : ℝ → ℝ)) (A t) with hP
  have h0 : (0 : ℝ) ∈ Icc (-c) c := ⟨by linarith, hc⟩
  refine (Submodule.eq_bot_iff _).2 fun x hx ↦ ?_
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hx
  -- The difference quotient of the indicator at `0` is continuous on the spectrum, so `P t` acts
  -- on the eigenvector `x` for the eigenvalue `0` by the value `1` of the indicator at `0`.
  have hfun : (fun u : ℝ ↦ ((Icc (-c) c).indicator (1 : ℝ → ℝ) u -
      (Icc (-c) c).indicator (1 : ℝ → ℝ) 0) / (u - 0)) = (Icc (-c) c)ᶜ.indicator fun u ↦ -u⁻¹ := by
    funext u
    by_cases hu : u ∈ Icc (-c) c
    · simp [hu, h0]
    · simp [hu, h0, div_eq_mul_inv]
  have hg : ContinuousOn (fun u : ℝ ↦ ((Icc (-c) c).indicator (1 : ℝ → ℝ) u -
      (Icc (-c) c).indicator (1 : ℝ → ℝ) 0) / (u - 0)) (spectrum ℝ (A t)) := by
    rw [hfun]
    refine ContinuousOn.continuousOn_indicator_of_disjoint_frontier ?_ ?_
    · rw [interior_compl, closure_Icc]
      exact (continuousOn_inv₀.mono (compl_subset_compl.2 (singleton_subset_iff.2 h0))).neg
    · rw [frontier_compl, frontier_Icc (by linarith), disjoint_left]
      rintro u (rfl | rfl)
      exacts [h₁, h₂]
  have hPx : P x = x := by
    have h := TauCeti.cfc_smul_of_smul_eq_algebraMap_smul (A := H →L[ℝ] H) (m := x)
      ((Icc (-c) c).indicator (1 : ℝ → ℝ)) (μ := 0)
      (by simp [ContinuousLinearMap.smul_def, hx]) hg hst
    simpa [hP, ContinuousLinearMap.smul_def, h0] using h
  obtain ⟨v, hv⟩ : x ∈ ((P ∘L ι : E →L[ℝ] H) : E →ₗ[ℝ] H).range := hrange ▸ ⟨x, hPx⟩
  have hv0 : v = 0 := hnd.1 v fun w ↦ by
    have hv' : P (ι v) = x := hv
    simp [compressedForm, ← hP, hv', hx]
  rw [← hv, hv0, map_zero]

/-! ### The spectral flow across a regular crossing -/

/-- **The spectral flow near a crossing as a drop of negative index.** Let `s` contain `t₀`, and
let `A` be continuous within `s` and self-adjoint at the times of `s` near `t₀`, with `A t₀`
Fredholm and kernel `K`. There is a cut `c > 0` such that the spectral projection `P t₀` of `A t₀`
for `[-c, c]` fixes `K`, `P` is continuous within `s` at `t₀`, at the times of `s` near `t₀` the
operator `A t` is injective as soon as the compressed path `V t (v, w) = ⟪A t (P t v), P t w⟫` on
`K` is nondegenerate, and for `a ≤ b` near `t₀` with `[a, b] ⊆ s` the spectral flow from `a` to `b`
is the drop of the negative index of `V`. -/
private theorem exists_spectralFlow_eq_sigNeg_sub_sigNeg {s : Set ℝ} (ht₀ : t₀ ∈ s)
    {K : Submodule ℝ H} (hK : K = (A t₀).ker) (hA : ∀ᶠ t in 𝓝[s] t₀, ContinuousWithinAt A s t)
    (hsa : ∀ᶠ t in 𝓝[s] t₀, IsSelfAdjoint (A t)) (hF : (A t₀).IsFredholm) :
    ∃ c > 0, (∀ v : K, cfc ((Icc (-c) c).indicator (1 : ℝ → ℝ)) (A t₀) v = v) ∧
      ContinuousWithinAt (fun t ↦ cfc ((Icc (-c) c).indicator (1 : ℝ → ℝ)) (A t)) s t₀ ∧
      (∀ᶠ t in 𝓝[s] t₀,
        (compressedForm A c K.subtypeL t).toBilinForm.Nondegenerate → (A t).ker = ⊥) ∧
      ∃ ε > 0, ∀ a b, t₀ - ε < a → a ≤ b → b < t₀ + ε → Icc a b ⊆ s →
        spectralFlow A a b =
          (sigNeg (compressedForm A c K.subtypeL a).toBilinForm.toQuadraticMap : ℤ) -
            sigNeg (compressedForm A c K.subtypeL b).toBilinForm.toQuadraticMap := by
  have hsa₀ := hsa.self_of_nhdsWithin ht₀
  obtain ⟨c, hc, hfr, hP₀, hev⟩ :=
    hsa₀.exists_pos_cfc_indicator_Icc_eq_starProjection_ker_of_isFredholm hF
  set P := fun t ↦ cfc ((Icc (-c) c).indicator (1 : ℝ → ℝ)) (A t)
  have hPK (v : K) : P t₀ v = v := by
    simp only [P, hP₀]
    exact Submodule.starProjection_eq_self_iff.2 (hK ▸ v.property)
  have hT : Tendsto A (𝓝[s] t₀) (𝓝[{S | IsSelfAdjoint S}] (A t₀)) :=
    tendsto_nhdsWithin_iff.2 ⟨hA.self_of_nhdsWithin ht₀, hsa⟩
  have hPc : ContinuousWithinAt P s t₀ :=
    (hsa₀.continuousWithinAt_cfc_indicator hfr).tendsto.comp hT
  have : FiniteDimensional ℝ (A t₀).ker := hF.finite_ker
  -- Near `t₀`, `c` is a cut and `P t` maps `K` isomorphically onto its range, so the negative
  -- index of the compressed path counts the eigenvalues of `A t` in `[-c, 0)`, and its
  -- nondegeneracy detects the injectivity of `A t`.
  have hloc : ∀ᶠ t in 𝓝[s] t₀, ContinuousWithinAt A s t ∧ IsSelfAdjoint (A t) ∧
      -c ∉ spectrum ℝ (A t) ∧ c ∉ spectrum ℝ (A t) ∧ FiniteDimensional ℝ (P t).range ∧
      sigNeg (compressedForm A c K.subtypeL t).toBilinForm.toQuadraticMap +
        spectralCount c (A t) = Module.finrank ℝ K ∧
      ((compressedForm A c K.subtypeL t).toBilinForm.Nondegenerate → (A t).ker = ⊥) := by
    filter_upwards [hA, hsa, hT.eventually hev, hPc.eventually_mem (Metric.ball_mem_nhds _ one_pos)]
      with t hAt hst ⟨h₁, h₂, hfd, hrk⟩ hdist
    have hinj : Injective (P t ∘L K.subtypeL) :=
      injective_comp_subtypeL_of_norm_sub_lt_one hPK (by rwa [← dist_eq_norm, dist_comm])
    have hrange : ((P t ∘L K.subtypeL : K →L[ℝ] H) : K →ₗ[ℝ] H).range = (P t).range := by
      refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
      · rintro _ ⟨v, rfl⟩
        exact ⟨v, by simp⟩
      · rw [LinearMap.finrank_range_of_inj hinj, hrk, hK]
    exact ⟨hAt, hst, h₁, h₂, hfd,
      hst.sigNeg_add_spectralCount_eq_finrank hc.le h₁ h₂ hfd hinj hrange,
      ker_eq_bot_of_nondegenerate_compressedForm hst hc.le h₁ h₂ hrange⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1 hloc
  refine ⟨c, hc, hPK, hPc, hloc.mono fun _ h ↦ h.2.2.2.2.2.2, ε, hε, fun a b ha hab hb hs ↦ ?_⟩
  have hsub : Icc a b ⊆ Metric.ball t₀ ε ∩ s := fun u hu ↦ by
    rw [Real.ball_eq_Ioo]
    exact ⟨⟨by linarith [hu.1], by linarith [hu.2]⟩, hs hu⟩
  have hcont : ContinuousOn A (Icc a b) := fun u hu ↦ by
    obtain ⟨hAu, -⟩ := hball (hsub hu)
    exact hAu.mono hs
  have hsab : ∀ u ∈ Icc a b, IsSelfAdjoint (A u) := fun u hu ↦ by
    obtain ⟨-, hsu, -⟩ := hball (hsub hu)
    exact hsu
  have hcut : IsSpectralCutOn A c (Icc a b) := isSpectralCutOn_iff.2 ⟨hc, fun u hu ↦ by
    obtain ⟨-, -, h₁, h₂, hfd, -⟩ := hball (hsub hu)
    exact ⟨h₁, h₂, hfd⟩⟩
  obtain ⟨-, -, -, -, -, ha', -⟩ := hball (hsub ⟨le_rfl, hab⟩)
  obtain ⟨-, -, -, -, -, hb', -⟩ := hball (hsub ⟨hab, le_rfl⟩)
  rw [spectralFlow_eq_of_isSpectralCutOn hab hcont hsab hcut]
  omega

/-- **The compressed path at a crossing.** Let `s` contain `t₀`, and let `A` be continuous within
`s` and self-adjoint at the times of `s` near `t₀`, with `A t₀` Fredholm. The kernel `K` of the
form `⟪A t₀ ·, ·⟫` is finite-dimensional, and there are a cut `c` and `ε > 0` such that the
compressed path `V` on `K` is symmetric with negative index `0` at `t₀`, has derivative
`⟪A' ·, ·⟫` within `s` at `t₀` whenever `A` has derivative `A'` within `s` there (and at `t₀` when
`s` is a neighbourhood of `t₀` and `A` has derivative `A'` at `t₀`), has crossing form
at `t₀` equivalent to the crossing form `Γ` of `A`, computes the spectral flow of `A` between
any two times `a ≤ b` within `ε` of `t₀` with `[a, b] ⊆ s`, and is nondegenerate at the times of
`s` near `t₀` only where `A` is injective. -/
private theorem exists_compressedForm_of_crossing {s : Set ℝ} (ht₀ : t₀ ∈ s)
    {K : Submodule ℝ H} (hK : K = ((innerSL ℝ).comp (A t₀)).ker)
    (hA : ∀ᶠ t in 𝓝[s] t₀, ContinuousWithinAt A s t)
    (hsa : ∀ᶠ t in 𝓝[s] t₀, IsSelfAdjoint (A t)) (hF : (A t₀).IsFredholm) :
    ∃ _ : FiniteDimensional ℝ K, ∃ c, ∃ ε > 0,
      (HasDerivWithinAt A A' s t₀ →
        HasDerivWithinAt (compressedForm A c K.subtypeL) (restrictForm K.subtypeL A') s t₀) ∧
      (s ∈ 𝓝 t₀ → HasDerivAt A A' t₀ →
        HasDerivAt (compressedForm A c K.subtypeL) (restrictForm K.subtypeL A') t₀) ∧
      (compressedForm A c K.subtypeL t₀).toBilinForm.IsSymm ∧
      sigNeg (compressedForm A c K.subtypeL t₀).toBilinForm.toQuadraticMap = 0 ∧
      (crossingForm (compressedForm A c K.subtypeL t₀) (restrictForm K.subtypeL A')).Equivalent
        (crossingForm ((innerSL ℝ).comp (A t₀)) ((innerSL ℝ).comp A')) ∧
      (∀ a b, t₀ - ε < a → a ≤ b → b < t₀ + ε → Icc a b ⊆ s →
        spectralFlow A a b =
          (sigNeg (compressedForm A c K.subtypeL a).toBilinForm.toQuadraticMap : ℤ) -
            sigNeg (compressedForm A c K.subtypeL b).toBilinForm.toQuadraticMap) ∧
      ∀ᶠ t in 𝓝[s] t₀,
        (compressedForm A c K.subtypeL t).toBilinForm.Nondegenerate → (A t).ker = ⊥ := by
  have hKer : K = (A t₀).ker := hK.trans (ker_innerSL_comp (A t₀))
  have : FiniteDimensional ℝ K := hKer ▸ hF.finite_ker
  have hK₀ (v : K) : A t₀ v = 0 := by
    have hv : (v : H) ∈ (A t₀).ker := hKer ▸ v.property
    rwa [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hv
  obtain ⟨c, -, hPK, hPc, hker, ε, hε, hSF⟩ :=
    exists_spectralFlow_eq_sigNeg_sub_sigNeg ht₀ hKer hA hsa hF
  have hV₀ := compressedForm_self (c := c) (ι := K.subtypeL) hK₀
  have hB₀ : (compressedForm A c K.subtypeL t₀).toBilinForm = 0 := by ext; simp [hV₀]
  refine ⟨this, c, ε, hε, fun hd ↦ hasDerivWithinAt_compressedForm hK₀ hPK hPc hd,
    fun hs hd ↦ hasDerivAt_compressedForm hK₀ hPK (hPc.continuousAt hs) hd,
    hB₀ ▸ LinearMap.BilinForm.isSymm_zero, by simp [hB₀],
    (crossingForm_equivalent_of_eq_zero hV₀).trans ?_, hSF, hker⟩
  refine ⟨{ toLinearEquiv := LinearEquiv.ofEq _ _ hK, map_app' := fun v ↦ ?_ }⟩
  calc crossingForm ((innerSL ℝ).comp (A t₀)) ((innerSL ℝ).comp A') (LinearEquiv.ofEq _ _ hK v)
      = ((innerSL ℝ).comp A') v v := crossingForm_apply _ _ _
    _ = _ := by simp [restrictForm_apply]

/-- **The spectral flow just after a regular crossing.** Let `A` be a path of operators on a real
Hilbert space, defined on `[t₀, ∞)` near `t₀`: continuous and self-adjoint there, with `A t₀`
Fredholm and right derivative `A'` at `t₀`. If the crossing form `Γ v = ⟪A' v, v⟫` on the kernel
of `A t₀` is nondegenerate, then the spectral flow of `A` from `t₀` to every `b > t₀` close to
`t₀` is `-sigNeg Γ`: the eigenvalues leaving `0` downwards are those of the negative directions
of `Γ`. -/
theorem eventually_spectralFlow_right_eq_neg_sigNeg_crossingForm
    (hA : ∀ᶠ t in 𝓝[≥] t₀, ContinuousWithinAt A (Ici t₀) t)
    (hsa : ∀ᶠ t in 𝓝[≥] t₀, IsSelfAdjoint (A t))
    (hF : (A t₀).IsFredholm) (hd : HasDerivWithinAt A A' (Ici t₀) t₀)
    (hreg : (crossingForm ((innerSL ℝ).comp (A t₀)) ((innerSL ℝ).comp A')).Nondegenerate) :
    ∀ᶠ b in 𝓝[>] t₀, spectralFlow A t₀ b =
      -(sigNeg (crossingForm ((innerSL ℝ).comp (A t₀)) ((innerSL ℝ).comp A')) : ℤ) := by
  obtain ⟨_, c, ε, hε, hder, -, hsymm, hV₀, ⟨e⟩, hSF, -⟩ :=
    exists_compressedForm_of_crossing (A' := A') self_mem_Ici rfl hA hsa hF
  filter_upwards [eventually_sigNeg_eq_add_sigNeg_crossingForm hsymm (hder hd)
      (e.nondegenerate_iff.2 hreg), Ioo_mem_nhdsGT (show t₀ < t₀ + ε by linarith)] with b hb hbε
  rw [hSF t₀ b (by linarith) hbε.1.le hbε.2 Icc_subset_Ici_self, hb, hV₀,
    QuadraticMap.Equivalent.sigNeg_eq ⟨e⟩]
  push_cast
  ring

/-- **The spectral flow just before a regular crossing.** Let `A` be a path of operators on a real
Hilbert space, defined on `(-∞, t₀]` near `t₀`: continuous and self-adjoint there, with `A t₀`
Fredholm and left derivative `A'` at `t₀`. If the crossing form `Γ v = ⟪A' v, v⟫` on the kernel
of `A t₀` is nondegenerate, then the spectral flow of `A` from every `a < t₀` close to `t₀` to
`t₀` is `sigPos Γ`: the eigenvalues arriving at `0` from below are those of the positive
directions of `Γ`. -/
theorem eventually_spectralFlow_left_eq_sigPos_crossingForm
    (hA : ∀ᶠ t in 𝓝[≤] t₀, ContinuousWithinAt A (Iic t₀) t)
    (hsa : ∀ᶠ t in 𝓝[≤] t₀, IsSelfAdjoint (A t))
    (hF : (A t₀).IsFredholm) (hd : HasDerivWithinAt A A' (Iic t₀) t₀)
    (hreg : (crossingForm ((innerSL ℝ).comp (A t₀)) ((innerSL ℝ).comp A')).Nondegenerate) :
    ∀ᶠ a in 𝓝[<] t₀, spectralFlow A a t₀ =
      sigPos (crossingForm ((innerSL ℝ).comp (A t₀)) ((innerSL ℝ).comp A')) := by
  obtain ⟨_, c, ε, hε, hder, -, hsymm, hV₀, ⟨e⟩, hSF, -⟩ :=
    exists_compressedForm_of_crossing (A' := A') self_mem_Iic rfl hA hsa hF
  filter_upwards [eventually_sigNeg_eq_add_sigPos_crossingForm hsymm (hder hd)
      (e.nondegenerate_iff.2 hreg), Ioo_mem_nhdsLT (show t₀ - ε < t₀ by linarith)] with a ha haε
  rw [hSF a t₀ haε.1 haε.2.le (by linarith) Icc_subset_Iic_self, ha, hV₀,
    QuadraticMap.Equivalent.sigPos_eq ⟨e⟩]
  push_cast
  ring

/-- **The regular-crossing formula.** Let `A` be a path of self-adjoint operators on a real Hilbert
space, continuous near `t₀`, with `A t₀` Fredholm and derivative `A'` at `t₀`. If the crossing
form `Γ v = ⟪A' v, v⟫` on the kernel of `A t₀` is nondegenerate, then the spectral flow of `A`
across `t₀` is the signature `sigPos Γ - sigNeg Γ` of the crossing form: for every `a < t₀` close
to `t₀`, it holds from `a` to every `b > t₀` close enough to `t₀`, where how close `b` must be may
depend on `a`. -/
theorem eventually_spectralFlow_eq_sigPos_sub_sigNeg_crossingForm
    (hA : ∀ᶠ t in 𝓝 t₀, ContinuousAt A t) (hsa : ∀ᶠ t in 𝓝 t₀, IsSelfAdjoint (A t))
    (hF : (A t₀).IsFredholm) (hd : HasDerivAt A A' t₀)
    (hreg : (crossingForm ((innerSL ℝ).comp (A t₀)) ((innerSL ℝ).comp A')).Nondegenerate) :
    ∀ᶠ a in 𝓝[<] t₀, ∀ᶠ b in 𝓝[>] t₀, spectralFlow A a b =
      (sigPos (crossingForm ((innerSL ℝ).comp (A t₀)) ((innerSL ℝ).comp A')) : ℤ) -
        sigNeg (crossingForm ((innerSL ℝ).comp (A t₀)) ((innerSL ℝ).comp A')) := by
  obtain ⟨_, c, ε, hε, -, hder, hsymm, -, ⟨e⟩, hSF, -⟩ :=
    exists_compressedForm_of_crossing (A' := A') (mem_univ t₀) rfl
      (by rw [nhdsWithin_univ]; exact hA.mono fun _ h ↦ h.continuousWithinAt)
      (by rwa [nhdsWithin_univ]) hF
  filter_upwards [eventually_sigNeg_sub_sigNeg_eq_sigPos_sub_sigNeg_crossingForm hsymm
      (hder univ_mem hd) (e.nondegenerate_iff.2 hreg),
    Ioo_mem_nhdsLT (show t₀ - ε < t₀ by linarith)] with a ha haε
  filter_upwards [ha, Ioo_mem_nhdsGT (show t₀ < t₀ + ε by linarith)] with b hab hbε
  rw [hSF a b haε.1 (haε.2.trans hbε.1).le hbε.2 (subset_univ _), hab,
    QuadraticMap.Equivalent.sigPos_eq ⟨e⟩, QuadraticMap.Equivalent.sigNeg_eq ⟨e⟩]

/-- **Regular crossings are isolated.** Let `A` be a path of self-adjoint operators on a real
Hilbert space, continuous near `t₀`, with `A t₀` Fredholm and derivative `A'` at `t₀`. If the
crossing form `Γ v = ⟪A' v, v⟫` on the kernel of `A t₀` is nondegenerate, then `A t` is injective
at every `t ≠ t₀` close to `t₀`. -/
theorem eventually_ker_eq_bot_of_crossingForm_nondegenerate
    (hA : ∀ᶠ t in 𝓝 t₀, ContinuousAt A t) (hsa : ∀ᶠ t in 𝓝 t₀, IsSelfAdjoint (A t))
    (hF : (A t₀).IsFredholm) (hd : HasDerivAt A A' t₀)
    (hreg : (crossingForm ((innerSL ℝ).comp (A t₀)) ((innerSL ℝ).comp A')).Nondegenerate) :
    ∀ᶠ t in 𝓝[≠] t₀, (A t).ker = ⊥ := by
  obtain ⟨_, c, -, -, -, hder, -, -, ⟨e⟩, -, hker⟩ :=
    exists_compressedForm_of_crossing (A' := A') (mem_univ t₀) rfl
      (by rw [nhdsWithin_univ]; exact hA.mono fun _ h ↦ h.continuousWithinAt)
      (by rwa [nhdsWithin_univ]) hF
  rw [nhdsWithin_univ] at hker
  -- The compressed path is nondegenerate near `t₀`, except at `t₀`, and detects injectivity.
  filter_upwards [eventually_nondegenerate_of_crossingForm_nondegenerate
      (hsa.mono fun _ ↦ isSymm_compressedForm) (hder univ_mem hd) (e.nondegenerate_iff.2 hreg),
    nhdsWithin_le_nhds hker] with t hnd ht
  exact ht hnd

end TauCeti
