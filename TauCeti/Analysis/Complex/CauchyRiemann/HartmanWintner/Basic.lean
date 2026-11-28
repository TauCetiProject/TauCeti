/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import TauCeti.Analysis.Normed.Module.Complexification
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import TauCeti.Analysis.Asymptotics.Lemmas
import TauCeti.Analysis.Calculus.MeanValue
import TauCeti.Analysis.Complex.CauchyRiemann.Similarity
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.MeasureTheory.Function.RankOne

/-!
# The Hartman–Wintner expansion at a zero

Let `X` be a finite-dimensional real normed space and `u : ℂ → X` a `C²` map on an open set
`Ω ⊆ ℂ` satisfying the differential inequality

`‖Δu‖ ≤ K (‖u‖ + ‖Du‖)`

on `Ω`. Hartman and Wintner proved that at a zero `z₀ ∈ Ω` of `u` either `u` vanishes near `z₀`,
or `u` has a nonzero homogeneous harmonic leading polynomial: there are `k ≥ 1` and a nonzero
`c` in the complexification `X_ℂ` of `X` with

`u z = Re ((z - z₀) ^ k • c) + o(‖z - z₀‖ ^ k)`,
`Du z = D (Re ((· - z₀) ^ k • c)) z + o(‖z - z₀‖ ^ (k - 1))`

(`TauCeti.eventually_eq_zero_or_exists_isLittleO_sub_re_pow_smul`). The real homogeneous harmonic
polynomials of degree `k` on the plane with values in `X` are exactly the maps
`z ↦ Re (z ^ k • c)`, so this is the statement that the leading term is a nonzero homogeneous
polynomial of degree `k`, together with its derivative asymptotic. On a connected open set the
first alternative propagates: `u` then vanishes on all of `Ω`
(`TauCeti.eqOn_zero_or_exists_isLittleO_sub_re_pow_smul`). This finite-order expansion is the
analytic input to the Micallef–White normal form of a pseudoholomorphic curve near a point.
Isothermal coordinates flatten a variable elliptic principal part to a multiple of the Laplacian,
which extends the expansion to such operators
(`TauCeti.eventually_eq_zero_or_exists_isLittleO_sub_re_pow_smul_of_elliptic`).

## The proof

Write `ψ = ∂ₛu - i ∂ₜu`, twice the Wirtinger derivative `∂u`, with values in `X_ℂ`
(`TauCeti.Complexification`). For real `u` one has `∂ₛu + i ∂ₜu = conj ψ` and
`∂ₛψ + i ∂ₜψ = Δu`, by the symmetry of the second derivative. So the pair `ξ = (u, ψ)` solves the
first-order system

`∂ₛξ + i ∂ₜξ = (conj ψ, Δu)`,

whose right-hand side is bounded by a constant times `‖ξ‖` because of the differential
inequality. As in Carleman's argument, the second component is a real-linear coefficient applied
to `ξ`: the rank-one map `v ↦ ‖ξ‖⁻² ⟪ξ, v⟫ Δu` (`TauCeti.rankOneDivNormSq`, for an auxiliary
Euclidean structure) is bounded and measurable and sends `ξ` to `Δu`. The similarity principle
for classical solutions (`TauCeti.exists_similarity_of_contDiffOn`) then writes `ξ = Φ σ` near
`z₀`, with `Φ` continuous, complex-linear and invertible and `σ` holomorphic. Either `σ`
vanishes near `z₀`, or it has a finite order `m` there, and then
`ξ z = (z - z₀) ^ m • c + o(‖z - z₀‖ ^ m)` with `c ≠ 0`
(`TauCeti.eventually_eq_zero_or_exists_isLittleO_sub_pow_smul_of_eventually_eq_clm_apply`).

In the second case `Du = O(‖z - z₀‖ ^ m)`, so `u = O(‖z - z₀‖ ^ (m + 1))` since `u z₀ = 0`, and the
first component of `c` vanishes. Its second component `c₂` is therefore nonzero and
`ψ z = (z - z₀) ^ m • c₂ + o(‖z - z₀‖ ^ m)`. Since `Du z h = Re (h • ψ z)`, the derivative of `u`
is that of `Re ((· - z₀) ^ (m + 1) • c₂ / (m + 1))` up to `o(‖z - z₀‖ ^ m)`, and integrating along
segments from `z₀` (`TauCeti.sub_isLittleO_norm_rpow_add_one_of_fderiv`) gives the expansion of
`u` with `k = m + 1`.

## Main results

* `TauCeti.eventually_eq_zero_or_exists_isLittleO_sub_re_pow_smul`: the Hartman–Wintner
  alternative at a zero of `u`.
* `TauCeti.eqOn_zero_or_exists_isLittleO_sub_re_pow_smul`: its global form on a connected open
  set.
* `TauCeti.hasFDerivAt_re_sub_pow_smul`, `TauCeti.fderiv_re_sub_pow_smul_apply`: the derivative
  of the leading polynomial `w ↦ Re ((w - z₀) ^ k • c)`.

## References

* P. Hartman and A. Wintner, *On the local behavior of solutions of non-parabolic partial
  differential equations*, Amer. J. Math. **75** (1953), 449–476.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Theorem 2.3.5 (the similarity principle) and Appendix E (the Micallef–White theorem).
* M. J. Micallef and B. White, *The structure of branch points in minimal surfaces and in
  pseudoholomorphic curves*, Ann. of Math. **141** (1995), 35–85.
-/

public section

open Asymptotics Filter Metric Set Topology
open scoped Laplacian

namespace TauCeti

/-! ### The complexified derivative -/

section Derivative

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

open Complexification

/-- The complexified derivative `ψ = ∂ₛu - i ∂ₜu` of a map `u : ℂ → X`, twice its Wirtinger
derivative `∂u`. -/
private noncomputable def cxDeriv (u : ℂ → X) (z : ℂ) : Complexification X :=
  ofReal (fderiv ℝ u z 1) - Complex.I • ofReal (fderiv ℝ u z Complex.I)

private theorem cxDeriv_re (u : ℂ → X) (z : ℂ) : (cxDeriv u z).re = fderiv ℝ u z 1 := by
  simp [cxDeriv, smul_re]

private theorem cxDeriv_im (u : ℂ → X) (z : ℂ) :
    (cxDeriv u z).im = -fderiv ℝ u z Complex.I := by
  simp [cxDeriv, smul_im]

/-- The derivative of `u` is the real part of the product with `ψ`: `Du z h = Re (h • ψ z)`. -/
private theorem fderiv_apply_eq_re_smul_cxDeriv (u : ℂ → X) (z h : ℂ) :
    fderiv ℝ u z h = (h • cxDeriv u z).re := by
  have hh : h = h.re • (1 : ℂ) + h.im • Complex.I := by
    apply Complex.ext <;> simp
  conv_lhs => rw [hh]
  rw [map_add, map_smul, map_smul, smul_re, cxDeriv_re, cxDeriv_im, smul_neg, sub_neg_eq_add]

private theorem norm_fderiv_le_norm_cxDeriv (u : ℂ → X) (z : ℂ) :
    ‖fderiv ℝ u z‖ ≤ ‖cxDeriv u z‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun h ↦ by
    rw [fderiv_apply_eq_re_smul_cxDeriv, mul_comm, ← norm_smul]
    exact norm_re_le _

/-- `∂ₛu + i ∂ₜu = conj ψ` for the complexification of `u`. -/
private theorem fderiv_ofReal_comp_one_add_I_smul {u : ℂ → X} {z : ℂ}
    (hu : DifferentiableAt ℝ u z) :
    fderiv ℝ (fun w ↦ ofReal (u w)) z 1 +
        Complex.I • fderiv ℝ (fun w ↦ ofReal (u w)) z Complex.I =
      conj X (cxDeriv u z) := by
  have h : HasFDerivAt (fun w ↦ ofReal (u w))
      ((ofRealLI X).toContinuousLinearMap.comp (fderiv ℝ u z)) z := by
    convert (ofRealLI X).toContinuousLinearMap.hasFDerivAt.comp z hu.hasFDerivAt using 1
    funext w
    simp
  rw [h.fderiv]
  ext <;> simp [smul_re, smul_im, cxDeriv_re, cxDeriv_im]

/-- `∂ₛψ + i ∂ₜψ = Δu`, the identity `Δ = 4 ∂ bar∂` for real maps. -/
private theorem fderiv_cxDeriv_one_add_I_smul {u : ℂ → X} {z : ℂ} (hu : ContDiffAt ℝ 2 u z) :
    fderiv ℝ (cxDeriv u) z 1 + Complex.I • fderiv ℝ (cxDeriv u) z Complex.I = ofReal (Δ u z) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ u) z :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hline (v : ℂ) : HasFDerivAt (fun w ↦ ofReal (fderiv ℝ u w v) : ℂ → Complexification X)
      ((ofRealLI X).toContinuousLinearMap.comp
        ((ContinuousLinearMap.apply ℝ X v).comp (fderiv ℝ (fderiv ℝ u) z))) z := by
    convert (ofRealLI X).toContinuousLinearMap.hasFDerivAt.comp z
      ((ContinuousLinearMap.apply ℝ X v).hasFDerivAt.comp z hd.hasFDerivAt) using 1
    funext w
    simp
  have hψ : HasFDerivAt (cxDeriv u) _ z := (hline 1).sub ((hline Complex.I).const_smul Complex.I)
  have hsymm := hu.isSymmSndFDerivAt (by simp) Complex.I 1
  rw [hψ.fderiv, InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  ext <;> simp [smul_re, smul_im, iteratedFDeriv_two_apply, hsymm]

end Derivative

/-! ### The first-order system -/

section System

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

open Complexification

/-- The space `X_ℂ × X_ℂ` in which the pair `ξ = (u, ψ)` takes its values. -/
private abbrev CPair (X : Type*) :=
  Complexification X × Complexification X

/-- The pair `ξ = (u, ψ)` of a map and its complexified derivative, which solves a first-order
Cauchy–Riemann system when `u` satisfies the Hartman–Wintner inequality. -/
private noncomputable def hwPair (u : ℂ → X) (z : ℂ) : CPair X :=
  (ofReal (u z), cxDeriv u z)

private theorem contDiffOn_hwPair {Ω : Set ℂ} (hΩ : IsOpen Ω) {u : ℂ → X}
    (hu : ContDiffOn ℝ 2 u Ω) : ContDiffOn ℝ 1 (hwPair u) Ω := by
  have hU : ContDiffOn ℝ 1 (fun z ↦ ofReal (u z) : ℂ → Complexification X) Ω := by
    have := ((ofRealLI X).toContinuousLinearMap.contDiff.comp_contDiffOn hu).of_le
      (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
    simpa [Function.comp_def] using this
  have hd : ContDiffOn ℝ 1 (fun y ↦ fderiv ℝ u y) Ω := hu.fderiv_of_isOpen hΩ (by norm_num)
  have hline (v : ℂ) :
      ContDiffOn ℝ 1 (fun z ↦ ofReal (fderiv ℝ u z v) : ℂ → Complexification X) Ω := by
    have := (ofRealLI X).toContinuousLinearMap.contDiff.comp_contDiffOn
      ((ContinuousLinearMap.apply ℝ X v).contDiff.comp_contDiffOn hd)
    simpa [Function.comp_def] using this
  exact hU.prodMk ((hline 1).sub ((hline Complex.I).const_smul Complex.I))

/-- `∂ₛξ + i ∂ₜξ = (conj ψ, Δu)` for the pair `ξ = (u, ψ)`. -/
private theorem fderiv_hwPair_one_add_I_smul {u : ℂ → X} {z : ℂ} (hu : ContDiffAt ℝ 2 u z)
    (hξ : DifferentiableAt ℝ (hwPair u) z) :
    fderiv ℝ (hwPair u) z 1 + Complex.I • fderiv ℝ (hwPair u) z Complex.I =
      (conj X (cxDeriv u z), ofReal (Δ u z)) := by
  have h1 : DifferentiableAt ℝ (fun w ↦ ofReal (u w) : ℂ → Complexification X) z := hξ.fst
  have h2 : DifferentiableAt ℝ (cxDeriv u) z := hξ.snd
  unfold hwPair
  rw [(h1.hasFDerivAt.prodMk h2.hasFDerivAt).fderiv]
  ext1
  · simpa using fderiv_ofReal_comp_one_add_I_smul (hu.differentiableAt (by norm_num))
  · simpa using fderiv_cxDeriv_one_add_I_smul hu

/-- The conjugation part `v ↦ (conj v.2, 0)` of the coefficient of the first-order system. -/
private noncomputable def hwConjPart : CPair X →L[ℝ] CPair X :=
  (ContinuousLinearMap.inl ℝ (Complexification X) (Complexification X)).comp
    ((conjCLM X).comp (ContinuousLinearMap.snd ℝ (Complexification X) (Complexification X)))

/-- The coefficient `C` of the first-order system `∂ₛξ + i ∂ₜξ + C ξ = 0` solved by `ξ = (u, ψ)`:
`C v = -(conj v.2, ‖T ξ‖⁻² ⟪T ξ, T v⟫ Δu)`, for an injective map `T` into an inner product space,
which only serves to make the rank-one part measurable. -/
private noncomputable def hwCoeff {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : CPair X →L[ℝ] E) (u : ℂ → X) (z : ℂ) : CPair X →L[ℝ] CPair X :=
  -(hwConjPart + (ContinuousLinearMap.inr ℝ (Complexification X) (Complexification X)).comp
      ((rankOneDivNormSq ℝ (ofReal (Δ u z)) (T (hwPair u z))).comp T))

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem aestronglyMeasurable_hwCoeff {Ω : Set ℂ} (hΩ : IsOpen Ω) {u : ℂ → X}
    (hu : ContDiffOn ℝ 2 u Ω) (T : CPair X →L[ℝ] E) :
    MeasureTheory.AEStronglyMeasurable (hwCoeff T u) (MeasureTheory.volume.restrict Ω) := by
  have hc : ContinuousOn (fun z ↦ ofReal (Δ u z) : ℂ → Complexification X) Ω := by
    simpa [Function.comp_def] using
      (ofRealLI X).continuous.comp_continuousOn (hu.continuousOn_laplacian hΩ)
  have hx : MeasureTheory.AEStronglyMeasurable (fun z ↦ T (hwPair u z))
      (MeasureTheory.volume.restrict Ω) :=
    (T.continuous.comp_continuousOn (contDiffOn_hwPair hΩ hu).continuousOn).aestronglyMeasurable
      hΩ.measurableSet
  exact (continuous_const.add (continuous_const.clm_comp
    (continuous_id.clm_comp continuous_const))).neg.comp_aestronglyMeasurable
      ((hc.aestronglyMeasurable hΩ.measurableSet).rankOneDivNormSq (𝕜 := ℝ) hx)

/-- Under the Hartman–Wintner inequality, `‖Δu‖ ≤ 2 |K| ‖ξ‖`. -/
private theorem norm_laplacian_le_norm_hwPair {u : ℂ → X} {K : ℝ} {z : ℂ}
    (hK : ‖Δ u z‖ ≤ K * (‖u z‖ + ‖fderiv ℝ u z‖)) : ‖Δ u z‖ ≤ 2 * |K| * ‖hwPair u z‖ := by
  have h1 : ‖u z‖ ≤ ‖hwPair u z‖ := by simp [hwPair]
  have h2 : ‖fderiv ℝ u z‖ ≤ ‖hwPair u z‖ :=
    (norm_fderiv_le_norm_cxDeriv u z).trans (norm_snd_le (hwPair u z))
  calc ‖Δ u z‖ ≤ K * (‖u z‖ + ‖fderiv ℝ u z‖) := hK
    _ ≤ |K| * (‖u z‖ + ‖fderiv ℝ u z‖) :=
      mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity)
    _ ≤ |K| * (2 * ‖hwPair u z‖) := by gcongr; linarith
    _ = _ := by ring

private theorem norm_hwCoeff_le {u : ℂ → X} {K : ℝ} {z : ℂ}
    (hK : ‖Δ u z‖ ≤ K * (‖u z‖ + ‖fderiv ℝ u z‖)) (T : CPair X →L[ℝ] E) (T' : E →L[ℝ] CPair X)
    (hT : ∀ v, T' (T v) = v) :
    ‖hwCoeff T u z‖ ≤ ‖(hwConjPart : CPair X →L[ℝ] CPair X)‖ +
      ‖ContinuousLinearMap.inr ℝ (Complexification X) (Complexification X)‖ *
        (2 * |K| * ‖T'‖ * ‖T‖) := by
  -- the rank-one part has norm `‖Δu‖ / ‖T ξ‖ ≤ 2 |K| ‖T'‖`
  have hR : ‖rankOneDivNormSq ℝ (ofReal (Δ u z)) (T (hwPair u z))‖ ≤ 2 * |K| * ‖T'‖ := by
    have h3 : ‖hwPair u z‖ ≤ ‖T'‖ * ‖T (hwPair u z)‖ := by
      simpa [hT] using T'.le_opNorm (T (hwPair u z))
    have hΔ := norm_laplacian_le_norm_hwPair hK
    rw [norm_rankOneDivNormSq, norm_ofReal]
    rcases (norm_nonneg (T (hwPair u z))).eq_or_lt with h0 | hpos
    · rw [← h0, div_zero]
      positivity
    · rw [div_le_iff₀ hpos]
      calc ‖Δ u z‖ ≤ 2 * |K| * (‖T'‖ * ‖T (hwPair u z)‖) := by
            refine hΔ.trans ?_
            gcongr
        _ = _ := by ring
  rw [hwCoeff, norm_neg]
  refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_right hR (norm_nonneg _))

/-- The pair `ξ = (u, ψ)` of a `C²` solution of `‖Δu‖ ≤ K (‖u‖ + ‖Du‖)` solves the linear
Cauchy–Riemann equation `∂ₛξ + i ∂ₜξ + C ξ = 0` for the coefficient `C = hwCoeff T u`. -/
private theorem hwPair_equation {Ω : Set ℂ} (hΩ : IsOpen Ω) {u : ℂ → X} (hu : ContDiffOn ℝ 2 u Ω)
    {K : ℝ} (hK : ∀ z ∈ Ω, ‖Δ u z‖ ≤ K * (‖u z‖ + ‖fderiv ℝ u z‖))
    {T : CPair X →L[ℝ] E} (hT : Function.Injective T) {z : ℂ}
    (hz : z ∈ Ω) :
    fderiv ℝ (hwPair u) z 1 + Complex.I • fderiv ℝ (hwPair u) z Complex.I +
      hwCoeff T u z (hwPair u z) = 0 := by
  have hξ : DifferentiableAt ℝ (hwPair u) z :=
    ((contDiffOn_hwPair hΩ hu).contDiffAt (hΩ.mem_nhds hz)).differentiableAt one_ne_zero
  rw [fderiv_hwPair_one_add_I_smul (hu.contDiffAt (hΩ.mem_nhds hz)) hξ]
  by_cases h0 : hwPair u z = 0
  · -- where `ξ` vanishes, so do `ψ` and, by the inequality, `Δu`
    have hψ : cxDeriv u z = 0 := congrArg Prod.snd h0
    have hΔ : Δ u z = 0 := norm_le_zero_iff.1
      ((norm_laplacian_le_norm_hwPair (hK z hz)).trans (by simp [h0]))
    simp [hwCoeff, hwConjPart, h0, hψ, hΔ]
  · have he : T (hwPair u z) ≠ 0 := fun h ↦ h0 (hT (h.trans (map_zero T).symm))
    ext1
    · simp [hwCoeff, hwConjPart, hwPair]
    · simp [hwCoeff, hwConjPart, rankOneDivNormSq_apply_self _ he]

/-- The pair `ξ = (u, ψ)` of a `C²` solution of `‖Δu‖ ≤ K (‖u‖ + ‖Du‖)` solves a linear
Cauchy–Riemann equation `∂ₛξ + i ∂ₜξ + C ξ = 0` with a measurable, locally bounded real-linear
coefficient `C`: the hypotheses of the similarity principle. -/
private theorem exists_coeff_hwPair [FiniteDimensional ℝ X] {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {u : ℂ → X} (hu : ContDiffOn ℝ 2 u Ω) {K : ℝ}
    (hK : ∀ z ∈ Ω, ‖Δ u z‖ ≤ K * (‖u z‖ + ‖fderiv ℝ u z‖)) :
    ∃ C : ℂ → CPair X →L[ℝ]
        CPair X,
      MeasureTheory.AEStronglyMeasurable C (MeasureTheory.volume.restrict Ω) ∧
      (∀ z ∈ Ω, ∃ M, ∀ᶠ w in 𝓝 z, ‖C w‖ ≤ M) ∧
      ∀ z ∈ Ω, fderiv ℝ (hwPair u) z 1 + Complex.I • fderiv ℝ (hwPair u) z Complex.I +
        C z (hwPair u z) = 0 := by
  let e := toEuclidean (E := CPair X)
  let T : CPair X →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ (CPair X))) := e
  let T' : EuclideanSpace ℝ (Fin (Module.finrank ℝ (CPair X))) →L[ℝ] CPair X := e.symm
  exact ⟨hwCoeff T u, aestronglyMeasurable_hwCoeff hΩ hu T,
    fun z hz ↦ ⟨_, eventually_of_mem (hΩ.mem_nhds hz) fun w hw ↦
      norm_hwCoeff_le (hK w hw) T T' e.symm_apply_apply⟩,
    fun z hz ↦ hwPair_equation hΩ hu hK e.injective hz⟩

end System

/-! ### The Hartman–Wintner expansion -/

section Expansion

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

open Complexification

/-- The derivative of the homogeneous harmonic polynomial `w ↦ Re ((w - z₀) ^ k • c)`. -/
theorem hasFDerivAt_re_sub_pow_smul (k : ℕ) (c : Complexification X) (z₀ z : ℂ) :
    HasFDerivAt (fun w ↦ ((w - z₀) ^ k • c).re)
      ((reCLM X).comp ((ContinuousLinearMap.toSpanSingleton ℂ
        (((k : ℂ) * (z - z₀) ^ (k - 1)) • c)).restrictScalars ℝ)) z := by
  have h := ((hasDerivAt_pow k (z - z₀)).comp z ((hasDerivAt_id z).sub_const z₀)).smul_const c
  rw [mul_one] at h
  convert (reCLM X).hasFDerivAt.comp z (h.hasFDerivAt.restrictScalars ℝ) using 1
  funext w
  simp

/-- The derivative of `w ↦ Re ((w - z₀) ^ k • c)` at `z` in the direction `h` is
`Re (h • k (z - z₀) ^ (k - 1) • c)`. -/
theorem fderiv_re_sub_pow_smul_apply (k : ℕ) (c : Complexification X) (z₀ z h : ℂ) :
    fderiv ℝ (fun w ↦ ((w - z₀) ^ k • c).re) z h =
      (h • (((k : ℂ) * (z - z₀) ^ (k - 1)) • c)).re := by
  rw [(hasFDerivAt_re_sub_pow_smul k c z₀ z).fderiv]
  simp

/-- **From the leading term of `ψ` to the leading polynomial of `u`.** If `u z₀ = 0`, `u` is
differentiable near `z₀` and `ψ z = (z - z₀) ^ m • c + o(‖z - z₀‖ ^ m)` with `c ≠ 0`, then `u` is
`Re ((z - z₀) ^ (m + 1) • c / (m + 1))` up to `o(‖z - z₀‖ ^ (m + 1))`, with the corresponding
derivative estimate. -/
private theorem exists_isLittleO_sub_re_pow_smul_of_isLittleO_cxDeriv {u : ℂ → X} {z₀ : ℂ}
    (hu₀ : u z₀ = 0) (hdiff : ∀ᶠ z in 𝓝 z₀, DifferentiableAt ℝ u z) {m : ℕ}
    {c : Complexification X} (hc : c ≠ 0)
    (hlo : (fun z ↦ cxDeriv u z - (z - z₀) ^ m • c) =o[𝓝 z₀] fun z ↦ ‖z - z₀‖ ^ m) :
    ∃ (k : ℕ) (c : Complexification X), 0 < k ∧ c ≠ 0 ∧
      (fun z ↦ u z - ((z - z₀) ^ k • c).re) =o[𝓝 z₀] (fun z ↦ ‖z - z₀‖ ^ k) ∧
      (fun z ↦ fderiv ℝ u z - fderiv ℝ (fun w ↦ ((w - z₀) ^ k • c).re) z) =o[𝓝 z₀]
        fun z ↦ ‖z - z₀‖ ^ (k - 1) := by
  have hm : ((m : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  set c' : Complexification X := ((m : ℂ) + 1)⁻¹ • c with hc'
  have hcoef (z : ℂ) :
      (((m + 1 : ℕ) : ℂ) * (z - z₀) ^ (m + 1 - 1)) • c' = (z - z₀) ^ m • c := by
    rw [hc', smul_smul, Nat.add_sub_cancel]
    congr 1
    push_cast
    field_simp
  -- `Du z - DP z` is `h ↦ Re (h • (ψ z - (z - z₀) ^ m • c))`
  have hD : (fun z ↦ fderiv ℝ u z - fderiv ℝ (fun w ↦ ((w - z₀) ^ (m + 1) • c').re) z) =o[𝓝 z₀]
      fun z ↦ ‖z - z₀‖ ^ m := by
    refine (IsBigO.of_bound 1 (Eventually.of_forall fun z ↦ ?_)).trans_isLittleO hlo
    rw [one_mul]
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun h ↦ ?_
    rw [sub_apply, fderiv_apply_eq_re_smul_cxDeriv, fderiv_re_sub_pow_smul_apply, hcoef, ← sub_re,
      ← smul_sub, mul_comm, ← norm_smul]
    exact norm_re_le _
  refine ⟨m + 1, c', Nat.succ_pos m, smul_ne_zero (inv_ne_zero hm) hc, ?_, by simpa using hD⟩
  -- integrate the derivative estimate along segments from `z₀`
  have hdP (z : ℂ) : DifferentiableAt ℝ (fun w ↦ ((w - z₀) ^ (m + 1) • c').re) z :=
    (hasFDerivAt_re_sub_pow_smul (m + 1) c' z₀ z).differentiableAt
  have h := sub_isLittleO_norm_rpow_add_one_of_fderiv
    (f := fun z ↦ u z - ((z - z₀) ^ (m + 1) • c').re) (Nat.cast_nonneg m)
    (hdiff.mono fun z hz ↦ hz.sub (hdP z))
    (hD.congr' (hdiff.mono fun z hz ↦ (fderiv_sub hz (hdP z)).symm)
      (Eventually.of_forall fun z ↦ (Real.rpow_natCast _ _).symm))
  exact (h.congr_right fun z ↦ by rw [← Nat.cast_add_one, Real.rpow_natCast]).congr_left
    fun z ↦ by simp [hu₀]

/-- **The leading term of `ξ` is carried by `ψ`.** If `u z₀ = 0`, `u` is differentiable near `z₀`
and `ξ z = (z - z₀) ^ m • c + o(‖z - z₀‖ ^ m)` with `c ≠ 0`, then the first component of `c`
vanishes, because `u = O(‖z - z₀‖ ^ (m + 1))`, so the second one does not. -/
private theorem isLittleO_cxDeriv_of_isLittleO_hwPair {u : ℂ → X} {z₀ : ℂ} (hu₀ : u z₀ = 0)
    (hdiff : ∀ᶠ z in 𝓝 z₀, DifferentiableAt ℝ u z) {m : ℕ}
    {c : CPair X} (hc : c ≠ 0)
    (hlo : (fun z ↦ hwPair u z - (z - z₀) ^ m • c) =o[𝓝 z₀] fun z ↦ ‖z - z₀‖ ^ m) :
    c.2 ≠ 0 ∧ (fun z ↦ cxDeriv u z - (z - z₀) ^ m • c.2) =o[𝓝 z₀] fun z ↦ ‖z - z₀‖ ^ m := by
  have hlo₁ : (fun z ↦ ofReal (u z) - (z - z₀) ^ m • c.1) =o[𝓝 z₀] fun z ↦ ‖z - z₀‖ ^ m :=
    (IsBigO.of_bound 1 (Eventually.of_forall fun z ↦ by
      simpa [hwPair] using norm_fst_le (hwPair u z - (z - z₀) ^ m • c))).trans_isLittleO hlo
  have hlo₂ : (fun z ↦ cxDeriv u z - (z - z₀) ^ m • c.2) =o[𝓝 z₀] fun z ↦ ‖z - z₀‖ ^ m :=
    (IsBigO.of_bound 1 (Eventually.of_forall fun z ↦ by
      simpa [hwPair] using norm_snd_le (hwPair u z - (z - z₀) ^ m • c))).trans_isLittleO hlo
  -- `Du = O(‖z - z₀‖ ^ m)`, so `u = O(‖z - z₀‖ ^ (m + 1))` since `u z₀ = 0`
  have hpow : (fun z ↦ (z - z₀) ^ m • c.2) =O[𝓝 z₀] fun z ↦ ‖z - z₀‖ ^ m :=
    IsBigO.of_bound ‖c.2‖ (Eventually.of_forall fun z ↦ by
      rw [norm_smul, norm_pow, Real.norm_of_nonneg (by positivity), mul_comm])
  have hDu : fderiv ℝ u =O[𝓝 z₀] fun z ↦ ‖z - z₀‖ ^ (m : ℝ) := by
    refine ((IsBigO.of_bound 1 (Eventually.of_forall fun z ↦ by
      simpa using norm_fderiv_le_norm_cxDeriv u z)).trans
        ((hlo₂.isBigO.add hpow).congr_left fun z ↦ sub_add_cancel _ _)).congr_right fun z ↦ ?_
    rw [Real.rpow_natCast]
  have hu₁ : u =O[𝓝 z₀] fun z ↦ ‖z - z₀‖ ^ (m + 1) :=
    (isBigO_norm_rpow_add_one_of_fderiv_of_apply_eq_zero (Nat.cast_nonneg m) hdiff hDu
      hu₀).congr_right fun z ↦ by rw [← Nat.cast_add_one, Real.rpow_natCast]
  have hU : (fun z ↦ (ofReal (u z) : Complexification X)) =o[𝓝 z₀] fun z ↦ ‖z - z₀‖ ^ m :=
    ((IsBigO.of_bound 1 (Eventually.of_forall fun z ↦ (by simp :
      ‖(ofReal (u z) : Complexification X)‖ ≤ 1 * ‖u z‖)) :
      (fun z ↦ (ofReal (u z) : Complexification X)) =O[𝓝 z₀] u)).trans_isLittleO
      (hu₁.trans_isLittleO ((isLittleO_norm_pow_norm_pow (Nat.lt_succ_self m)).comp_tendsto
        (tendsto_sub_nhds_zero_iff.2 tendsto_id)))
  have hne : ∃ᶠ z in 𝓝 z₀, (z - z₀) ^ m ≠ 0 :=
    (eventually_nhdsWithin_of_forall (s := {z₀}ᶜ) fun z hz ↦
      pow_ne_zero m (sub_ne_zero.2 hz)).frequently
      |>.filter_mono nhdsWithin_le_nhds
  have hc₁ : c.1 = 0 := (isLittleO_smul_const_self_iff (.of_forall fun _ ↦ norm_nonneg _)
      (hne.mono fun _ ↦ norm_ne_zero_iff.mpr) (norm_smul · _)).mp <| isLittleO_norm_right.1 <|
    ((hU.sub hlo₁).congr_left fun z ↦ sub_sub_cancel _ _).congr_right fun z ↦ (norm_pow _ _).symm
  exact ⟨fun h ↦ hc (Prod.ext hc₁ h), hlo₂⟩

variable [FiniteDimensional ℝ X]

/-- **The Hartman–Wintner expansion.** Let `u : ℂ → X` be a `C²` map, into a finite-dimensional
real normed space, on an open set `Ω`, satisfying `‖Δu‖ ≤ K (‖u‖ + ‖Du‖)` on `Ω`, and let
`z₀ ∈ Ω` be a zero of `u`. Then either `u` vanishes near `z₀`, or there are `k ≥ 1` and a nonzero
`c` in the complexification of `X` such that `u` is the homogeneous harmonic polynomial
`Re ((z - z₀) ^ k • c)` up to `o(‖z - z₀‖ ^ k)`, and its derivative is the derivative of that
polynomial up to `o(‖z - z₀‖ ^ (k - 1))`. -/
theorem eventually_eq_zero_or_exists_isLittleO_sub_re_pow_smul {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {u : ℂ → X} (hu : ContDiffOn ℝ 2 u Ω) {K : ℝ}
    (hK : ∀ z ∈ Ω, ‖Δ u z‖ ≤ K * (‖u z‖ + ‖fderiv ℝ u z‖)) {z₀ : ℂ} (hz₀ : z₀ ∈ Ω)
    (hu₀ : u z₀ = 0) :
    (∀ᶠ z in 𝓝 z₀, u z = 0) ∨ ∃ (k : ℕ) (c : Complexification X), 0 < k ∧ c ≠ 0 ∧
      (fun z ↦ u z - ((z - z₀) ^ k • c).re) =o[𝓝 z₀] (fun z ↦ ‖z - z₀‖ ^ k) ∧
      (fun z ↦ fderiv ℝ u z - fderiv ℝ (fun w ↦ ((w - z₀) ^ k • c).re) z) =o[𝓝 z₀]
        fun z ↦ ‖z - z₀‖ ^ (k - 1) := by
  -- the similarity principle for `ξ = (u, ψ)` at `z₀`, and the leading term of `ξ`
  obtain ⟨C, hCm, hCb, heq⟩ := exists_coeff_hwPair hΩ hu hK
  obtain ⟨r, hr, -, Φ, σ, hΦ, hΦu, hσ, hEq⟩ :=
    exists_similarity_of_contDiffOn hΩ (contDiffOn_hwPair hΩ hu) hCm hCb heq hz₀
  have hb := ball_mem_nhds z₀ hr
  have hΦ₀ : Function.Injective (Φ z₀) := by
    obtain ⟨e, he⟩ := hΦu z₀ (mem_ball_self hr)
    exact he ▸ (ContinuousLinearEquiv.ofUnit e).injective
  rcases eventually_eq_zero_or_exists_isLittleO_sub_pow_smul_of_eventually_eq_clm_apply
      (hΦ.continuousAt hb) hΦ₀ (hσ.analyticAt hb)
      (eventually_of_mem hb hEq) with h0 | ⟨m, c, hc, hlo⟩
  · exact .inl (h0.mono fun z hz ↦ by simpa [hwPair] using congrArg (fun p ↦ p.1.re) hz)
  have hdiff : ∀ᶠ z in 𝓝 z₀, DifferentiableAt ℝ u z :=
    eventually_of_mem (hΩ.mem_nhds hz₀) fun z hz ↦
      (hu.contDiffAt (hΩ.mem_nhds hz)).differentiableAt (by norm_num)
  obtain ⟨hc₂, hlo₂⟩ := isLittleO_cxDeriv_of_isLittleO_hwPair hu₀ hdiff hc hlo
  exact .inr (exists_isLittleO_sub_re_pow_smul_of_isLittleO_cxDeriv hu₀ hdiff hc₂ hlo₂)

/-- **The Hartman–Wintner alternative** on a connected open set. Let `u : ℂ → X` be a `C²` map,
into a finite-dimensional real normed space, on a connected open set `Ω`, satisfying
`‖Δu‖ ≤ K (‖u‖ + ‖Du‖)` on `Ω`, and let `z₀ ∈ Ω` be a zero of `u`. Then either `u` vanishes
identically on `Ω`, or at `z₀` it has a nonzero homogeneous harmonic leading polynomial
`Re ((z - z₀) ^ k • c)` with `k ≥ 1`, in the sense of
`TauCeti.eventually_eq_zero_or_exists_isLittleO_sub_re_pow_smul`. -/
theorem eqOn_zero_or_exists_isLittleO_sub_re_pow_smul {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hΩc : IsPreconnected Ω) {u : ℂ → X} (hu : ContDiffOn ℝ 2 u Ω) {K : ℝ}
    (hK : ∀ z ∈ Ω, ‖Δ u z‖ ≤ K * (‖u z‖ + ‖fderiv ℝ u z‖)) {z₀ : ℂ} (hz₀ : z₀ ∈ Ω)
    (hu₀ : u z₀ = 0) :
    EqOn u 0 Ω ∨ ∃ (k : ℕ) (c : Complexification X), 0 < k ∧ c ≠ 0 ∧
      (fun z ↦ u z - ((z - z₀) ^ k • c).re) =o[𝓝 z₀] (fun z ↦ ‖z - z₀‖ ^ k) ∧
      (fun z ↦ fderiv ℝ u z - fderiv ℝ (fun w ↦ ((w - z₀) ^ k • c).re) z) =o[𝓝 z₀]
        fun z ↦ ‖z - z₀‖ ^ (k - 1) := by
  refine (eventually_eq_zero_or_exists_isLittleO_sub_re_pow_smul hΩ hu hK hz₀ hu₀).imp_left
    fun h0 ↦ ?_
  have := FiniteDimensional.completeSpace ℂ (CPair X)
  obtain ⟨C, hCm, hCb, heq⟩ := exists_coeff_hwPair hΩ hu hK
  have hξ := contDiffOn_hwPair hΩ hu
  -- `ξ = (u, ψ)` vanishes near `z₀`, hence on `Ω` by unique continuation
  have hξ₀ : ∀ᶠ z in 𝓝 z₀, hwPair u z = 0 := by
    filter_upwards [h0.eventually_nhds] with z hz
    have hD : fderiv ℝ u z = 0 := by
      rw [Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) (f := fun _ ↦ (0 : X)) hz]
      exact fderiv_const_apply _
    exact Prod.ext (by simp [hwPair, hz.self_of_nhds]) (by simp [hwPair, cxDeriv, hD])
  have hzero := eqOn_zero_of_hasSimilarityFactorizationAt_of_eventually_eq_zero hΩ hΩc
    hξ.continuousOn (fun z hz _ ↦ hasSimilarityFactorizationAt_of_contDiffOn hΩ hξ hCm hCb heq hz)
    hz₀ hξ₀
  intro z hz
  simpa [hwPair] using congrArg (fun p ↦ p.1.re) (hzero hz)

end Expansion

end TauCeti
