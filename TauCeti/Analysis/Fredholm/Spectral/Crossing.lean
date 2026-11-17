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

/-!
# The spectral flow at a regular crossing

Let `A` be a path of self-adjoint operators on a real Hilbert space `H`, continuous near `t₀`,
with `A t₀` Fredholm and derivative `A'` at `t₀`. Its *crossing form* at `t₀` is the quadratic
form `Γ v = ⟪A' v, v⟫` on the kernel of `A t₀`
(`ContinuousLinearMap.crossingForm ((innerSL ℝ).comp (A t₀)) ((innerSL ℝ).comp A')`), and the
crossing is *regular* when `Γ` is nondegenerate. This file proves the regular-crossing formula
for Phillips' spectral flow `TauCeti.spectralFlow`: across a regular crossing the spectral flow is
the signature of the crossing form,

`spectralFlow A a b = sigPos Γ - sigNeg Γ`  for `a < t₀ < b` close to `t₀`,

so that positive crossings count positively. One-sided versions hold with one-sided derivatives:
from `t₀` to `b > t₀` the spectral flow is `-sigNeg Γ`, and from `a < t₀` to `t₀` it is
`sigPos Γ`. This is the infinite-dimensional counterpart of the crossing computations of
`TauCeti.Analysis.Matrix.HermitianSignature.Crossing`, to which the proof reduces.

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
eigenvalues of `A t` in `[-c, 0)` (`TauCeti.sigNeg_add_spectralCount_eq_finrank`): the form
`x ↦ ⟪A t x, x⟫` is negative definite on the spectral subspace for `[-c, 0)` and nonnegative on
that for `[0, c]`, and these two subspaces split the range of `P t`. So `V t` has negative index
`dim K - spectralCount c (A t)`, and the spectral flow over an interval with the single cut `c` is
a difference of these counts.

## Main results

* `ContinuousLinearMap.inner_apply_self_nonneg_of_mem_range_cfc_indicator` and
  `ContinuousLinearMap.inner_apply_self_neg_of_mem_range_cfc_indicator`: the quadratic form of an
  operator on its spectral subspaces for a set of nonnegative numbers and for a set of negative
  numbers.
* `TauCeti.sigNeg_add_spectralCount_eq_finrank`: the negative index of the form of a self-adjoint
  operator on the range of its spectral projection for a cut `[-c, c]`, plus the number of its
  eigenvalues in `[0, c]`, is the rank of that projection.
* `TauCeti.eventually_spectralFlow_self_eq_neg_sigNeg_crossingForm`: the spectral flow just after
  a regular crossing.
* `TauCeti.eventually_spectralFlow_eq_sigPos_crossingForm`: the spectral flow just before a
  regular crossing.
* `TauCeti.eventually_spectralFlow_eq_sigPos_sub_sigNeg_crossingForm`: **the regular-crossing
  formula**, the spectral flow across a regular crossing.

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

/-! ### The quadratic form of a self-adjoint operator on its spectral subspaces -/

namespace ContinuousLinearMap

variable (S : H →L[ℝ] H) {Ω : Set ℝ} {x : H}

/-- The spectral projection `E` of `S` for `Ω`, applied twice, is `E`. -/
private theorem cfc_indicator_cfc_indicator_apply (Ω : Set ℝ) (y : H) :
    cfc (Ω.indicator (1 : ℝ → ℝ)) S (cfc (Ω.indicator (1 : ℝ → ℝ)) S y) =
      cfc (Ω.indicator (1 : ℝ → ℝ)) S y := by
  simpa using congr($((TauCeti.isStarProjection_cfc_indicator S Ω).isIdempotentElem.eq) y)

/-- **The form of a self-adjoint operator on a nonnegative spectral subspace.** On the range of
the spectral projection `cfc (Ω.indicator 1) S` of an operator `S` for a set `Ω` of nonnegative
numbers, the quadratic form `x ↦ ⟪S x, x⟫` is nonnegative. (When `S` is not self-adjoint, or the
indicator is not continuous on its spectrum, the projection is `0`.) -/
theorem inner_apply_self_nonneg_of_mem_range_cfc_indicator (hΩ : Ω ⊆ Ici 0)
    (hx : x ∈ (cfc (Ω.indicator (1 : ℝ → ℝ)) S).range) : 0 ≤ ⟪S x, x⟫_ℝ := by
  by_cases h : IsSelfAdjoint S ∧ ContinuousOn (Ω.indicator (1 : ℝ → ℝ)) (spectrum ℝ S)
  swap
  · rw [cfc_apply_of_not_and S h] at hx
    obtain ⟨y, rfl⟩ := hx
    simp
  obtain ⟨hS, hf⟩ := h
  -- `S E = R²` for the spectral projection `E` and `R = cfc (√ ⬝ 1_Ω) S`.
  set r : ℝ → ℝ := Ω.indicator Real.sqrt
  have hr : ContinuousOn r (spectrum ℝ S) :=
    hf.continuousOn_indicator_of_continuousOn_indicator_one fun _ _ ↦
      Real.continuous_sqrt.continuousWithinAt
  have hSE : S * cfc (Ω.indicator (1 : ℝ → ℝ)) S = cfc r S * cfc r S := by
    calc S * cfc (Ω.indicator (1 : ℝ → ℝ)) S
        = cfc (fun y ↦ y * Ω.indicator (1 : ℝ → ℝ) y) S := by
          rw [cfc_mul (fun y ↦ y) _ S (by fun_prop) hf, cfc_id' ℝ S]
      _ = cfc (fun y ↦ r y * r y) S := cfc_congr fun y _ ↦ by
          by_cases hy : y ∈ Ω
          · simp [r, hy, Real.mul_self_sqrt (hΩ hy)]
          · simp [r, hy]
      _ = cfc r S * cfc r S := cfc_mul r r S hr hr
  obtain ⟨y, hy⟩ := hx
  rw [ContinuousLinearMap.coe_coe] at hy
  subst hy
  have hR := (cfc_predicate r S : IsSelfAdjoint (cfc r S)).isSymmetric
  calc (0 : ℝ) ≤ ⟪cfc r S (cfc (Ω.indicator (1 : ℝ → ℝ)) S y),
        cfc r S (cfc (Ω.indicator (1 : ℝ → ℝ)) S y)⟫_ℝ := real_inner_self_nonneg
    _ = ⟪(S * cfc (Ω.indicator (1 : ℝ → ℝ)) S) (cfc (Ω.indicator (1 : ℝ → ℝ)) S y),
        cfc (Ω.indicator (1 : ℝ → ℝ)) S y⟫_ℝ := by
      rw [hSE, mul_def, ContinuousLinearMap.comp_apply]
      exact (hR _ _).symm
    _ = _ := by rw [mul_def, ContinuousLinearMap.comp_apply, cfc_indicator_cfc_indicator_apply]

/-- **The form of a self-adjoint operator on a negative spectral subspace.** On the range of the
spectral projection `cfc (Ω.indicator 1) S` of an operator `S` for a set `Ω` of negative numbers,
the quadratic form `x ↦ ⟪S x, x⟫` is negative definite. -/
theorem inner_apply_self_neg_of_mem_range_cfc_indicator (hΩ : Ω ⊆ Iio 0)
    (hx : x ∈ (cfc (Ω.indicator (1 : ℝ → ℝ)) S).range) (hx0 : x ≠ 0) : ⟪S x, x⟫_ℝ < 0 := by
  by_cases h : IsSelfAdjoint S ∧ ContinuousOn (Ω.indicator (1 : ℝ → ℝ)) (spectrum ℝ S)
  swap
  · rw [cfc_apply_of_not_and S h] at hx
    obtain ⟨y, rfl⟩ := hx
    exact absurd (by simp) hx0
  obtain ⟨hS, hf⟩ := h
  -- `S E = -R²` for the spectral projection `E` and `R = cfc (√(-·) ⬝ 1_Ω) S`, and `E = R' R` for
  -- `R' = cfc ((√(-·))⁻¹ ⬝ 1_Ω) S`; both functions are continuous on the spectrum, since near a
  -- spectral value the spectrum lies either in `Ω`, where `√(-·)` does not vanish, or outside it.
  set r : ℝ → ℝ := Ω.indicator fun y ↦ √(-y)
  set k : ℝ → ℝ := Ω.indicator fun y ↦ (√(-y))⁻¹
  have hr : ContinuousOn r (spectrum ℝ S) :=
    hf.continuousOn_indicator_of_continuousOn_indicator_one fun _ _ ↦
      (continuous_neg.sqrt).continuousWithinAt
  have hk : ContinuousOn k (spectrum ℝ S) :=
    hf.continuousOn_indicator_of_continuousOn_indicator_one fun y hy ↦
      ((continuous_neg.sqrt.continuousAt).inv₀
        (Real.sqrt_pos.2 (neg_pos.2 (hΩ hy.1))).ne').continuousWithinAt
  have hSE : S * cfc (Ω.indicator (1 : ℝ → ℝ)) S = -(cfc r S * cfc r S) := by
    calc S * cfc (Ω.indicator (1 : ℝ → ℝ)) S
        = cfc (fun y ↦ y * Ω.indicator (1 : ℝ → ℝ) y) S := by
          rw [cfc_mul (fun y ↦ y) _ S (by fun_prop) hf, cfc_id' ℝ S]
      _ = cfc (fun y ↦ -(r y * r y)) S := cfc_congr fun y _ ↦ by
          by_cases hy : y ∈ Ω
          · simp [r, hy, Real.mul_self_sqrt (neg_nonneg.2 (hΩ hy).le)]
          · simp [r, hy]
      _ = -(cfc r S * cfc r S) := by rw [cfc_neg _ S, cfc_mul r r S hr hr]
  have hEk : cfc (Ω.indicator (1 : ℝ → ℝ)) S = cfc k S * cfc r S := by
    rw [← cfc_mul k r S hk hr]
    refine cfc_congr fun y _ ↦ ?_
    by_cases hy : y ∈ Ω
    · simp [k, r, hy, inv_mul_cancel₀ (Real.sqrt_pos.2 (neg_pos.2 (hΩ hy))).ne']
    · simp [k, r, hy]
  obtain ⟨y, hy⟩ := hx
  rw [ContinuousLinearMap.coe_coe] at hy
  subst hy
  set E := cfc (Ω.indicator (1 : ℝ → ℝ)) S
  have hrx : cfc r S (E y) ≠ 0 := fun h ↦ hx0 <| by
    rw [← cfc_indicator_cfc_indicator_apply, congr($hEk (E y)), mul_def,
      ContinuousLinearMap.comp_apply, h, map_zero]
  have hR := (cfc_predicate r S : IsSelfAdjoint (cfc r S)).isSymmetric
  calc ⟪S (E y), E y⟫_ℝ = ⟪(S * E) (E y), E y⟫_ℝ := by
        rw [mul_def, ContinuousLinearMap.comp_apply, cfc_indicator_cfc_indicator_apply]
    _ = -⟪cfc r S (E y), cfc r S (E y)⟫_ℝ := by
        rw [hSE, neg_apply, mul_def, ContinuousLinearMap.comp_apply, inner_neg_left]
        exact congrArg _ (hR _ _)
    _ < 0 := neg_neg_iff_pos.2 (real_inner_self_pos.2 hrx)

end ContinuousLinearMap

namespace TauCeti

/-! ### The negative index of a self-adjoint operator near a cut -/

/-- **Sylvester's law of inertia through an embedding.** Let `U : K → M` be injective and let
`R₋`, `R₊` be independent subspaces of its range whose dimensions add up to that of `K`. If a
quadratic form on `K` is negative definite on the vectors sent into `R₋` and nonnegative on those
sent into `R₊`, its negative index is the dimension of `R₋`. -/
private theorem sigNeg_eq_finrank_of_injective {K M : Type*} [AddCommGroup K] [Module ℝ K]
    [FiniteDimensional ℝ K] [AddCommGroup M] [Module ℝ M] (Q : QuadraticForm ℝ K)
    {U : K →ₗ[ℝ] M} (hU : Injective U) {Rm Rp : Submodule ℝ M} [FiniteDimensional ℝ Rm]
    [FiniteDimensional ℝ Rp] (hm : Rm ≤ U.range) (hp : Rp ≤ U.range) (hd : Rm ⊓ Rp = ⊥)
    (hdim : Module.finrank ℝ K = Module.finrank ℝ Rm + Module.finrank ℝ Rp)
    (hneg : ∀ v, U v ∈ Rm → v ≠ 0 → Q v < 0) (hpos : ∀ v, U v ∈ Rp → 0 ≤ Q v) :
    sigNeg Q = Module.finrank ℝ Rm := by
  set A := Rm.comap U
  set B := Rp.comap U
  have hfA : Module.finrank ℝ A = Module.finrank ℝ Rm := by
    have h := (Submodule.equivMapOfInjective _ hU A).finrank_eq
    rwa [Submodule.map_comap_eq_of_le hm] at h
  have hfB : Module.finrank ℝ B = Module.finrank ℝ Rp := by
    have h := (Submodule.equivMapOfInjective _ hU B).finrank_eq
    rwa [Submodule.map_comap_eq_of_le hp] at h
  have hcompl : IsCompl A B := by
    have hAB : Disjoint A B := by
      rw [disjoint_iff, ← Submodule.comap_inf, hd, Submodule.comap_bot]
      exact LinearMap.ker_eq_bot.2 hU
    refine ⟨hAB, codisjoint_iff.2 (Submodule.eq_top_of_finrank_eq ?_)⟩
    have h := Submodule.finrank_sup_add_finrank_inf_eq A B
    rw [disjoint_iff.1 hAB, finrank_bot, add_zero, hfA, hfB] at h
    rw [h, hdim]
  have hnegA : ((-Q).restrict A).PosDef := fun v hv0 ↦ by
    have := hneg v v.2 fun h ↦ hv0 (Subtype.ext h)
    rw [QuadraticMap.restrict_apply, _root_.neg_apply]
    linarith
  rw [QuadraticForm.sigNeg_eq_finrank_of_isCompl_of_negDef Q hcompl hnegA hpos, hfA]

/-- **The spectral splitting at a cut.** At a cut `c` of a self-adjoint operator `S`, the ranges of
the spectral projections for `[-c, 0)` and for `[0, c]` lie in the range of the projection `P` for
`[-c, c]`, are finite-dimensional and independent, and their dimensions add up to the rank of `P`.
-/
private theorem spectralSplitting {S : H →L[ℝ] H} (hS : IsSelfAdjoint S) {c : ℝ} (hc : 0 < c)
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
  · -- A vector in both ranges is fixed by both projections, whose product is `0`.
    have h0 : Em * Ep = 0 := by
      simp [Em, Ep, TauCeti.cfc_indicator_mul_cfc_indicator S hcm hcp, hdisj.inter_eq]
    rw [eq_bot_iff]
    rintro x ⟨⟨y, hy⟩, ⟨z, hz⟩⟩
    rw [ContinuousLinearMap.coe_coe] at hy hz
    have hxm : Em x = x := hy ▸ S.cfc_indicator_cfc_indicator_apply _ y
    have hxp : Ep x = x := hz ▸ S.cfc_indicator_cfc_indicator_apply _ z
    rw [Submodule.mem_bot]
    calc x = (Em * Ep) x := by rw [mul_def, ContinuousLinearMap.comp_apply, hxp, hxm]
      _ = 0 := by rw [h0, zero_apply]
  · have h := S.finrank_range_cfc_indicator_union hdisj hcm hcp
    rwa [Ico_union_Icc_eq_Icc (by linarith) hc.le, ← spectralCount_def] at h

/-- **Counting the eigenvalues below `0` by a negative index.** Let `c > 0` be a cut of a
self-adjoint operator `S`: neither `-c` nor `c` is in its spectrum, and its spectral projection
`P` for `[-c, c]` has finite rank. Let `U : K → H` be an injective map onto the range of `P`. Then
the negative index of the form `(v, w) ↦ ⟪S (U v), U w⟫` on `K`, plus the number
`spectralCount c S` of eigenvalues of `S` in `[0, c]`, is the dimension of `K`: the negative index
counts the eigenvalues of `S` in `[-c, 0)`. -/
theorem sigNeg_add_spectralCount_eq_finrank {S : H →L[ℝ] H} (hS : IsSelfAdjoint S) {c : ℝ}
    (hc : 0 < c) (h₁ : -c ∉ spectrum ℝ S) (h₂ : c ∉ spectrum ℝ S)
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
  rw [sigNeg_eq_finrank_of_injective _ (U := (U : K →ₗ[ℝ] H)) hU (hUr ▸ hmP) (hUr ▸ hpP) hdisj
    (by rw [hKF, hsum, spectralCount_def])
    (fun v hv hv0 ↦ by
      simpa using S.inner_apply_self_neg_of_mem_range_cfc_indicator
        (fun x (hx : x ∈ Ico (-c) 0) ↦ hx.2) hv fun h ↦ hv0 (hU (h.trans (map_zero U).symm)))
    (fun v hv ↦ by
      simpa using S.inner_apply_self_nonneg_of_mem_range_cfc_indicator
        (fun x (hx : x ∈ Icc 0 c) ↦ hx.1) hv), hKF, hsum]

/-! ### The compressed path of forms -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The form `(v, w) ↦ ⟪B (ι v), ι w⟫` on `E` of an operator `B` on `H`. -/
private noncomputable def restrictForm (ι : E →L[ℝ] H) (B : H →L[ℝ] H) : E →L[ℝ] E →L[ℝ] ℝ :=
  ((innerSL ℝ).comp B).bilinearComp ι ι

omit [CompleteSpace H] in
private theorem restrictForm_apply (ι : E →L[ℝ] H) (B : H →L[ℝ] H) (v w : E) :
    restrictForm ι B v w = ⟪B (ι v), ι w⟫_ℝ := by
  simp [restrictForm]

omit [CompleteSpace H] in
private theorem restrictForm_sub (ι : E →L[ℝ] H) (B C : H →L[ℝ] H) :
    restrictForm ι (B - C) = restrictForm ι B - restrictForm ι C := by
  ext v w
  simp [restrictForm_apply, inner_sub_left]

omit [CompleteSpace H] in
private theorem restrictForm_smul (ι : E →L[ℝ] H) (a : ℝ) (B : H →L[ℝ] H) :
    restrictForm ι (a • B) = a • restrictForm ι B := by
  ext v w
  simp [restrictForm_apply, inner_smul_left]

omit [CompleteSpace H] in
private theorem norm_restrictForm_le (ι : E →L[ℝ] H) (B : H →L[ℝ] H) :
    ‖restrictForm ι B‖ ≤ ‖ι‖ * ‖ι‖ * ‖B‖ := by
  refine ContinuousLinearMap.opNorm_le_bound₂ (restrictForm ι B) (by positivity) fun v w ↦ ?_
  rw [restrictForm_apply]
  calc ‖⟪B (ι v), ι w⟫_ℝ‖ ≤ ‖B (ι v)‖ * ‖ι w‖ := norm_inner_le_norm _ _
    _ ≤ (‖B‖ * (‖ι‖ * ‖v‖)) * (‖ι‖ * ‖w‖) := by
      gcongr
      · exact B.le_opNorm_of_le (ι.le_opNorm v)
      · exact ι.le_opNorm w
    _ = ‖ι‖ * ‖ι‖ * ‖B‖ * ‖v‖ * ‖w‖ := by ring

omit [CompleteSpace H] in
/-- `B ↦ ⟪B (ι ·), ι ·⟫` is continuous. -/
private theorem tendsto_restrictForm {α : Type*} {l : Filter α} (ι : E →L[ℝ] H)
    {B : α → H →L[ℝ] H} {B₀ : H →L[ℝ] H} (hB : Tendsto B l (𝓝 B₀)) :
    Tendsto (fun a ↦ restrictForm ι (B a)) l (𝓝 (restrictForm ι B₀)) := by
  have hB' := (tendsto_iff_norm_sub_tendsto_zero.1 hB).const_mul (‖ι‖ * ‖ι‖)
  rw [mul_zero] at hB'
  refine (tendsto_iff_norm_sub_tendsto_zero (f := fun a ↦ restrictForm ι (B a))
    (b := restrictForm ι B₀)).2 (squeeze_zero
      (f := fun a ↦ ‖restrictForm ι (B a) - restrictForm ι B₀‖)
      (fun a ↦ norm_nonneg (restrictForm ι (B a) - restrictForm ι B₀)) (fun a ↦ ?_) hB')
  rw [← restrictForm_sub]
  exact norm_restrictForm_le ι _

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
  rw [compressedForm_eq hK, sub_self, mul_zero]
  ext v w
  simp [restrictForm_apply]

/-- **The derivative of the compressed path.** If `A t₀` vanishes on the image of `ι`, the spectral
projection `P t₀` fixes it and `P` is continuous at `t₀`, then the compressed path has derivative
`(v, w) ↦ ⟪A' (ι v), ι w⟫` at `t₀`. -/
private theorem hasDerivWithinAt_compressedForm {s : Set ℝ} (hK : ∀ v, A t₀ (ι v) = 0)
    (hPK : ∀ v, cfc ((Icc (-c) c).indicator (1 : ℝ → ℝ)) (A t₀) (ι v) = ι v)
    (hP : ContinuousWithinAt (fun t ↦ cfc ((Icc (-c) c).indicator (1 : ℝ → ℝ)) (A t)) s t₀)
    (hA : HasDerivWithinAt A A' s t₀) :
    HasDerivWithinAt (compressedForm A c ι) (restrictForm ι A') s t₀ := by
  set P := fun t ↦ cfc ((Icc (-c) c).indicator (1 : ℝ → ℝ)) (A t)
  rw [hasDerivWithinAt_iff_tendsto_slope] at hA
  rw [hasDerivWithinAt_iff_tendsto_slope (f := compressedForm A c ι) (f' := restrictForm ι A')]
  have hlim : restrictForm ι A' = restrictForm ι (P t₀ * A') := by
    ext v w
    have h : ⟪P t₀ (A' (ι v)), ι w⟫_ℝ = ⟪A' (ι v), P t₀ (ι w)⟫_ℝ :=
      (cfc_predicate _ (A t₀) : IsSelfAdjoint (P t₀)).isSymmetric _ _
    rw [restrictForm_apply, restrictForm_apply, mul_def, ContinuousLinearMap.comp_apply, h, hPK w]
  have heq : slope (compressedForm A c ι) t₀ = fun t ↦ restrictForm ι (P t * slope A t₀ t) := by
    funext t
    rw [slope_def_module, slope_def_module, compressedForm_self hK,
      sub_zero (compressedForm A c ι t), compressedForm_eq hK, mul_smul_comm, restrictForm_smul]
  rw [heq, hlim]
  exact tendsto_restrictForm ι ((hP.tendsto.mono_left (nhdsWithin_mono _ sdiff_subset)).mul hA)

/-! ### The spectral flow across a regular crossing -/

/-- At `B = 0` the crossing form of `B` and `V'` is the quadratic form of `V'` on the whole
space. -/
private theorem crossingForm_equivalent_of_eq_zero {B V' : E →L[ℝ] E →L[ℝ] ℝ} (hB : B = 0) :
    (crossingForm B V').Equivalent V'.toBilinForm.toQuadraticMap := by
  subst hB
  refine ⟨{ toLinearEquiv := LinearEquiv.ofTop _ (by simp), map_app' := fun v ↦ ?_ }⟩
  simpa using (crossingForm_apply (0 : E →L[ℝ] E →L[ℝ] ℝ) V' v).symm

omit [CompleteSpace H] in
/-- An operator within distance `1` of an operator fixing a subspace `K` is injective on `K`. -/
private theorem injective_comp_subtypeL_of_norm_sub_lt_one {P P₀ : H →L[ℝ] H}
    {K : Submodule ℝ H} (hP₀ : ∀ v : K, P₀ v = v) (h : ‖P₀ - P‖ < 1) :
    Injective (P ∘L K.subtypeL) := by
  refine (injective_iff_map_eq_zero _).2 fun v hv ↦ ?_
  by_contra hv0
  have hv0' : 0 < ‖(v : H)‖ := norm_pos_iff.2 fun h ↦ hv0 (Subtype.ext h)
  have hlt : ‖(v : H)‖ < ‖(v : H)‖ :=
    calc ‖(v : H)‖ = ‖(P₀ - P) v‖ := by
          rw [sub_apply, hP₀ v, show P v = 0 from hv, sub_zero]
      _ ≤ ‖P₀ - P‖ * ‖(v : H)‖ := (P₀ - P).le_opNorm _
      _ < 1 * ‖(v : H)‖ := by gcongr
      _ = ‖(v : H)‖ := one_mul _
  exact lt_irrefl _ hlt

/-- **The spectral flow near a crossing as a drop of negative index.** Let `A` be continuous at
`t₀`, self-adjoint near `t₀`, with `A t₀` Fredholm and kernel `K`. There is a cut `c > 0` such that
the spectral projection `P t₀` of `A t₀` for `[-c, c]` fixes `K`, `P` is continuous at `t₀`, and for
`a ≤ b` near `t₀` the spectral flow from `a` to `b` is the drop of the negative index of the
compressed path `V t (v, w) = ⟪A t (P t v), P t w⟫` on `K`. -/
private theorem exists_spectralFlow_eq_sigNeg_sub_sigNeg {K : Submodule ℝ H}
    (hK : K = (A t₀).ker) (hA : ∀ᶠ t in 𝓝 t₀, ContinuousAt A t)
    (hsa : ∀ᶠ t in 𝓝 t₀, IsSelfAdjoint (A t)) (hF : (A t₀).IsFredholm) :
    ∃ c > 0, (∀ v : K, cfc ((Icc (-c) c).indicator (1 : ℝ → ℝ)) (A t₀) v = v) ∧
      ContinuousAt (fun t ↦ cfc ((Icc (-c) c).indicator (1 : ℝ → ℝ)) (A t)) t₀ ∧
      ∃ ε > 0, ∀ a b, t₀ - ε < a → a ≤ b → b < t₀ + ε →
        spectralFlow A a b =
          (sigNeg (compressedForm A c K.subtypeL a).toBilinForm.toQuadraticMap : ℤ) -
            sigNeg (compressedForm A c K.subtypeL b).toBilinForm.toQuadraticMap := by
  have hsa₀ := hsa.self_of_nhds
  obtain ⟨c, hc, hfr, hP₀, hev⟩ :=
    hsa₀.exists_pos_cfc_indicator_Icc_eq_starProjection_ker_of_isFredholm hF
  set P := fun t ↦ cfc ((Icc (-c) c).indicator (1 : ℝ → ℝ)) (A t)
  have hPK (v : K) : P t₀ v = v := by
    simp only [P, hP₀]
    exact Submodule.starProjection_eq_self_iff.2 (hK ▸ v.2)
  have hT : Tendsto A (𝓝 t₀) (𝓝[{S | IsSelfAdjoint S}] (A t₀)) :=
    tendsto_nhdsWithin_iff.2 ⟨hA.self_of_nhds, hsa⟩
  have hPc : ContinuousAt P t₀ := (hsa₀.continuousWithinAt_cfc_indicator hfr).tendsto.comp hT
  refine ⟨c, hc, hPK, hPc, ?_⟩
  have : FiniteDimensional ℝ (A t₀).ker := hF.finite_ker
  -- Near `t₀`, `c` is a cut and `P t` maps `K` isomorphically onto its range, so the negative
  -- index of the compressed path counts the eigenvalues of `A t` in `[-c, 0)`.
  have hloc : ∀ᶠ t in 𝓝 t₀, ContinuousAt A t ∧ IsSelfAdjoint (A t) ∧ -c ∉ spectrum ℝ (A t) ∧
      c ∉ spectrum ℝ (A t) ∧ FiniteDimensional ℝ (P t).range ∧
      sigNeg (compressedForm A c K.subtypeL t).toBilinForm.toQuadraticMap +
        spectralCount c (A t) = Module.finrank ℝ K := by
    filter_upwards [hA, hsa, hT.eventually hev, hPc.eventually (Metric.ball_mem_nhds _ one_pos)]
      with t hAt hst ⟨h₁, h₂, hfd, hrk⟩ hdist
    refine ⟨hAt, hst, h₁, h₂, hfd, ?_⟩
    have hinj : Injective (P t ∘L K.subtypeL) :=
      injective_comp_subtypeL_of_norm_sub_lt_one hPK (by rwa [← dist_eq_norm, dist_comm])
    have hrange : ((P t ∘L K.subtypeL : K →L[ℝ] H) : K →ₗ[ℝ] H).range = (P t).range := by
      refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
      · rintro _ ⟨v, rfl⟩
        exact ⟨v, rfl⟩
      · rw [LinearMap.finrank_range_of_inj hinj, hrk, hK]
    exact sigNeg_add_spectralCount_eq_finrank hst hc h₁ h₂ hfd hinj hrange
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 hloc
  refine ⟨ε, hε, fun a b ha hab hb ↦ ?_⟩
  have hsub : Icc a b ⊆ Metric.ball t₀ ε := fun u hu ↦ by
    rw [Real.ball_eq_Ioo]
    exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hcut : IsSpectralCutOn A c (Icc a b) := isSpectralCutOn_iff.2
    ⟨hc, fun u hu ↦ ⟨(hball u (hsub hu)).2.2.1, (hball u (hsub hu)).2.2.2.1,
      (hball u (hsub hu)).2.2.2.2.1⟩⟩
  rw [spectralFlow_eq_of_isSpectralCutOn hab
    (fun u hu ↦ (hball u (hsub hu)).1.continuousWithinAt) (fun u hu ↦ (hball u (hsub hu)).2.1)
    hcut]
  have ha' := (hball a (hsub ⟨le_rfl, hab⟩)).2.2.2.2.2
  have hb' := (hball b (hsub ⟨hab, le_rfl⟩)).2.2.2.2.2
  omega

/-- The zero form is symmetric. -/
private theorem isSymm_toBilinForm_of_eq_zero {B : E →L[ℝ] E →L[ℝ] ℝ} (hB : B = 0) :
    B.toBilinForm.IsSymm := by
  subst hB
  exact ⟨fun x y ↦ by simp⟩

/-- The zero form has negative index `0`. -/
private theorem sigNeg_toBilinForm_of_eq_zero [FiniteDimensional ℝ E] {B : E →L[ℝ] E →L[ℝ] ℝ}
    (hB : B = 0) :
    sigNeg B.toBilinForm.toQuadraticMap = 0 := by
  subst hB
  exact (QuadraticForm.forall_nonneg_iff_sigNeg_eq_zero _).1 fun x ↦ by simp

omit [CompleteSpace H] in
/-- The kernel of the form `(v, w) ↦ ⟪T v, w⟫` is the kernel of `T`. -/
private theorem ker_innerSL_comp (T : H →L[ℝ] H) :
    (((innerSL ℝ).comp T : H →L[ℝ] H →L[ℝ] ℝ) : H →ₗ[ℝ] H →L[ℝ] ℝ).ker = T.ker := by
  ext v
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  have h' : ⟪T v, T v⟫_ℝ = 0 := by simpa using congr($h (T v))
  exact inner_self_eq_zero.1 h'

/-- **The compressed path at a crossing.** For a path `A` continuous and self-adjoint near `t₀`,
with `A t₀` Fredholm, there are a cut `c > 0` and `ε > 0` such that the compressed path `V` on
`K = ker (A t₀)` vanishes at `t₀`, has derivative `⟪A' ·, ·⟫` wherever `A` has derivative `A'`,
has crossing form at `t₀` equivalent to the crossing form `Γ` of `A`, and computes the spectral
flow of `A` between any two times within `ε` of `t₀`. -/
private theorem exists_compressedForm_of_crossing (hA : ∀ᶠ t in 𝓝 t₀, ContinuousAt A t)
    (hsa : ∀ᶠ t in 𝓝 t₀, IsSelfAdjoint (A t)) (hF : (A t₀).IsFredholm) :
    ∃ c, ∃ ε > 0,
      (∀ s : Set ℝ, HasDerivWithinAt A A' s t₀ →
        HasDerivWithinAt (compressedForm A c
            ((((innerSL ℝ).comp (A t₀) : H →L[ℝ] H →L[ℝ] ℝ) : H →ₗ[ℝ] H →L[ℝ] ℝ).ker.subtypeL))
          (restrictForm
            ((((innerSL ℝ).comp (A t₀) : H →L[ℝ] H →L[ℝ] ℝ) : H →ₗ[ℝ] H →L[ℝ] ℝ).ker.subtypeL) A')
          s t₀) ∧
      compressedForm A c
          ((((innerSL ℝ).comp (A t₀) : H →L[ℝ] H →L[ℝ] ℝ) : H →ₗ[ℝ] H →L[ℝ] ℝ).ker.subtypeL) t₀ =
        0 ∧
      (crossingForm (compressedForm A c
          ((((innerSL ℝ).comp (A t₀) : H →L[ℝ] H →L[ℝ] ℝ) : H →ₗ[ℝ] H →L[ℝ] ℝ).ker.subtypeL) t₀)
        (restrictForm
          ((((innerSL ℝ).comp (A t₀) : H →L[ℝ] H →L[ℝ] ℝ) : H →ₗ[ℝ] H →L[ℝ] ℝ).ker.subtypeL)
          A')).Equivalent (crossingForm ((innerSL ℝ).comp (A t₀)) ((innerSL ℝ).comp A')) ∧
      ∀ a b, t₀ - ε < a → a ≤ b → b < t₀ + ε →
        spectralFlow A a b =
          (sigNeg (compressedForm A c
            ((((innerSL ℝ).comp (A t₀) : H →L[ℝ] H →L[ℝ] ℝ) : H →ₗ[ℝ] H →L[ℝ] ℝ).ker.subtypeL)
              a).toBilinForm.toQuadraticMap : ℤ) -
            sigNeg (compressedForm A c
              ((((innerSL ℝ).comp (A t₀) : H →L[ℝ] H →L[ℝ] ℝ) : H →ₗ[ℝ] H →L[ℝ] ℝ).ker.subtypeL)
                b).toBilinForm.toQuadraticMap := by
  set K := (((innerSL ℝ).comp (A t₀) : H →L[ℝ] H →L[ℝ] ℝ) : H →ₗ[ℝ] H →L[ℝ] ℝ).ker
  have hKer : K = (A t₀).ker := ker_innerSL_comp (A t₀)
  have hK (v : K) : A t₀ v = 0 := by
    have hv : (v : H) ∈ (A t₀).ker := hKer ▸ v.2
    rwa [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hv
  obtain ⟨c, -, hPK, hPc, ε, hε, hSF⟩ := exists_spectralFlow_eq_sigNeg_sub_sigNeg hKer hA hsa hF
  have hV₀ := compressedForm_self (c := c) (ι := K.subtypeL) hK
  refine ⟨c, ε, hε, fun s hd ↦ hasDerivWithinAt_compressedForm hK hPK hPc.continuousWithinAt hd,
    hV₀, (crossingForm_equivalent_of_eq_zero hV₀).trans ?_, hSF⟩
  refine ⟨{ toLinearEquiv := LinearEquiv.refl ℝ K, map_app' := fun v ↦ ?_ }⟩
  have h₂ : (restrictForm K.subtypeL A').toBilinForm.toQuadraticMap v = ⟪A' v, v⟫_ℝ := by
    simp [restrictForm_apply]
  calc crossingForm ((innerSL ℝ).comp (A t₀)) ((innerSL ℝ).comp A') (LinearEquiv.refl ℝ K v)
      = ((innerSL ℝ).comp A') v v := crossingForm_apply _ _ v
    _ = ⟪A' v, v⟫_ℝ := by rw [ContinuousLinearMap.comp_apply, innerSL_apply_apply]
    _ = _ := h₂.symm

/-- **The spectral flow just after a regular crossing.** Let `A` be a path of self-adjoint
operators on a real Hilbert space, continuous near `t₀`, with `A t₀` Fredholm and right derivative
`A'` at `t₀`. If the crossing form `Γ v = ⟪A' v, v⟫` on the kernel of `A t₀` is nondegenerate,
then the spectral flow of `A` from `t₀` to every `b > t₀` close to `t₀` is `-sigNeg Γ`: the
eigenvalues leaving `0` downwards are those of the negative directions of `Γ`. -/
theorem eventually_spectralFlow_self_eq_neg_sigNeg_crossingForm
    (hA : ∀ᶠ t in 𝓝 t₀, ContinuousAt A t) (hsa : ∀ᶠ t in 𝓝 t₀, IsSelfAdjoint (A t))
    (hF : (A t₀).IsFredholm) (hd : HasDerivWithinAt A A' (Ici t₀) t₀)
    (hreg : (crossingForm ((innerSL ℝ).comp (A t₀)) ((innerSL ℝ).comp A')).Nondegenerate) :
    ∀ᶠ b in 𝓝[>] t₀, spectralFlow A t₀ b =
      -(sigNeg (crossingForm ((innerSL ℝ).comp (A t₀)) ((innerSL ℝ).comp A')) : ℤ) := by
  obtain ⟨c, ε, hε, hder, hV₀, ⟨e⟩, hSF⟩ := exists_compressedForm_of_crossing (A' := A') hA hsa hF
  have : FiniteDimensional ℝ (((innerSL ℝ).comp (A t₀) : H →L[ℝ] H →L[ℝ] ℝ) :
      H →ₗ[ℝ] H →L[ℝ] ℝ).ker := ker_innerSL_comp (A t₀) ▸ hF.finite_ker
  have hsymm := isSymm_toBilinForm_of_eq_zero hV₀
  filter_upwards [eventually_sigNeg_eq_add_sigNeg_crossingForm hsymm (hder _ hd)
      (e.nondegenerate_iff.2 hreg), Ioo_mem_nhdsGT (show t₀ < t₀ + ε by linarith)] with b hb hbε
  rw [hSF t₀ b (by linarith) hbε.1.le hbε.2, hb, sigNeg_toBilinForm_of_eq_zero hV₀,
    (QuadraticMap.Equivalent.sigNeg_eq ⟨e⟩)]
  push_cast
  ring

/-- **The spectral flow just before a regular crossing.** Let `A` be a path of self-adjoint
operators on a real Hilbert space, continuous near `t₀`, with `A t₀` Fredholm and left derivative
`A'` at `t₀`. If the crossing form `Γ v = ⟪A' v, v⟫` on the kernel of `A t₀` is nondegenerate,
then the spectral flow of `A` from every `a < t₀` close to `t₀` to `t₀` is `sigPos Γ`: the
eigenvalues arriving at `0` from below are those of the positive directions of `Γ`. -/
theorem eventually_spectralFlow_eq_sigPos_crossingForm
    (hA : ∀ᶠ t in 𝓝 t₀, ContinuousAt A t) (hsa : ∀ᶠ t in 𝓝 t₀, IsSelfAdjoint (A t))
    (hF : (A t₀).IsFredholm) (hd : HasDerivWithinAt A A' (Iic t₀) t₀)
    (hreg : (crossingForm ((innerSL ℝ).comp (A t₀)) ((innerSL ℝ).comp A')).Nondegenerate) :
    ∀ᶠ a in 𝓝[<] t₀, spectralFlow A a t₀ =
      sigPos (crossingForm ((innerSL ℝ).comp (A t₀)) ((innerSL ℝ).comp A')) := by
  obtain ⟨c, ε, hε, hder, hV₀, ⟨e⟩, hSF⟩ := exists_compressedForm_of_crossing (A' := A') hA hsa hF
  have : FiniteDimensional ℝ (((innerSL ℝ).comp (A t₀) : H →L[ℝ] H →L[ℝ] ℝ) :
      H →ₗ[ℝ] H →L[ℝ] ℝ).ker := ker_innerSL_comp (A t₀) ▸ hF.finite_ker
  filter_upwards [eventually_sigNeg_eq_add_sigPos_crossingForm (isSymm_toBilinForm_of_eq_zero hV₀)
      (hder _ hd) (e.nondegenerate_iff.2 hreg), Ioo_mem_nhdsLT (show t₀ - ε < t₀ by linarith)]
    with a ha haε
  rw [hSF a t₀ haε.1 haε.2.le (by linarith), ha, sigNeg_toBilinForm_of_eq_zero hV₀,
    QuadraticMap.Equivalent.sigPos_eq ⟨e⟩]
  push_cast
  ring

/-- **The regular-crossing formula.** Let `A` be a path of self-adjoint operators on a real Hilbert
space, continuous near `t₀`, with `A t₀` Fredholm and derivative `A'` at `t₀`. If the crossing
form `Γ v = ⟪A' v, v⟫` on the kernel of `A t₀` is nondegenerate, then the spectral flow of `A`
across `t₀`, from every `a < t₀` to every `b > t₀` close to `t₀`, is the signature
`sigPos Γ - sigNeg Γ` of the crossing form. -/
theorem eventually_spectralFlow_eq_sigPos_sub_sigNeg_crossingForm
    (hA : ∀ᶠ t in 𝓝 t₀, ContinuousAt A t) (hsa : ∀ᶠ t in 𝓝 t₀, IsSelfAdjoint (A t))
    (hF : (A t₀).IsFredholm) (hd : HasDerivAt A A' t₀)
    (hreg : (crossingForm ((innerSL ℝ).comp (A t₀)) ((innerSL ℝ).comp A')).Nondegenerate) :
    ∀ᶠ a in 𝓝[<] t₀, ∀ᶠ b in 𝓝[>] t₀, spectralFlow A a b =
      (sigPos (crossingForm ((innerSL ℝ).comp (A t₀)) ((innerSL ℝ).comp A')) : ℤ) -
        sigNeg (crossingForm ((innerSL ℝ).comp (A t₀)) ((innerSL ℝ).comp A')) := by
  obtain ⟨c, ε, hε, hder, hV₀, ⟨e⟩, hSF⟩ := exists_compressedForm_of_crossing (A' := A') hA hsa hF
  have : FiniteDimensional ℝ (((innerSL ℝ).comp (A t₀) : H →L[ℝ] H →L[ℝ] ℝ) :
      H →ₗ[ℝ] H →L[ℝ] ℝ).ker := ker_innerSL_comp (A t₀) ▸ hF.finite_ker
  have hsymm := isSymm_toBilinForm_of_eq_zero hV₀
  have hreg' := e.nondegenerate_iff.2 hreg
  filter_upwards [eventually_sigNeg_eq_add_sigPos_crossingForm hsymm
      (hder _ hd.hasDerivWithinAt) hreg', Ioo_mem_nhdsLT (show t₀ - ε < t₀ by linarith)]
    with a ha haε
  filter_upwards [eventually_sigNeg_eq_add_sigNeg_crossingForm hsymm
      (hder _ hd.hasDerivWithinAt) hreg', Ioo_mem_nhdsGT (show t₀ < t₀ + ε by linarith)]
    with b hb hbε
  rw [hSF a b haε.1 (haε.2.trans hbε.1).le hbε.2, ha, hb, sigNeg_toBilinForm_of_eq_zero hV₀,
    QuadraticMap.Equivalent.sigPos_eq ⟨e⟩, QuadraticMap.Equivalent.sigNeg_eq ⟨e⟩]
  push_cast
  ring

end TauCeti
