/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Circle.Nemytskii.Basic
public import TauCeti.Analysis.Sobolev.Circle.RealBilinear
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import TauCeti.Analysis.Calculus.Hadamard
import TauCeti.Analysis.Fourier.AddCircle
import TauCeti.Analysis.Fourier.FourierCoeffOn
import TauCeti.Analysis.Fourier.Monomial
import TauCeti.Analysis.Normed.Operator.FiniteDimensional
import TauCeti.Analysis.Sobolev.Circle.OfContinuousMap
import TauCeti.Analysis.Sobolev.Circle.Slobodeckij
import TauCeti.MeasureTheory.Constructions.UnitInterval
import TauCeti.MeasureTheory.Integral.ContinuousMap
import TauCeti.Topology.Compactness.Normed

/-!
# Smooth Nemytskii maps on the circle Sobolev spaces

For `s > 1/2`, the Fourier-coefficient Sobolev space `H^s(E)` on the circle consists of continuous
loops (`TauCeti.CircleSobolev.toContinuousMap`). While
`TauCeti/Analysis/Sobolev/Circle/Nemytskii/Basic.lean` treats holomorphic scalar maps by Cauchy
estimates in a complex strip, nonlinear elliptic boundary value problems on curves and manifolds
require postcomposition `u ↦ f ∘ u` by *smooth* maps `f : E → F` between finite-dimensional complex
normed spaces, defined on an arbitrary open subset `U ⊆ E`, together with its strict Fréchet
derivative and `C^∞` regularity over `ℝ`.

The proof proceeds in three stages:

1. **Fractional base case `1/2 < s < 1`.** A `C¹` map `f` on an open set `U` is Lipschitz on every
   compact subset `K ⊆ U`. Comparing `H⁰` norms with `L²` integrals in Euclidean coordinates shows
   that composition with `f` bounds the Gagliardo–Slobodeckij energy
   (`TauCeti.CircleSobolev.slobodeckijEnergy`) uniformly on `{u ∈ H^s(E) | range u ⊆ K, ‖u‖ ≤ R}`.
2. **Inductive bootstrap to all `s > 1/2`.** We induct in half-integer steps
   `1/2 < s < (m + 2) / 2`. When `s ≥ 1`, set `t = s - 1 ≥ 0` and choose intermediate supercritical
   orders `t + 1/2 < r' < r < (m + 2) / 2`. By the induction hypothesis applied to
   `fderiv ℝ f : E → E →L[ℝ] F` on a compact thickening of `K`, the derivative composition
   `(df) ∘ u` belongs to `H^r(E →L[ℝ] F)` with a uniform norm bound. The asymmetric real-bilinear
   product (`TauCeti.CircleSobolev.realConvolutionAsym`) multiplies `(df) ∘ u ∈ H^{r'}` against
   `u' ∈ H^t(E)` in `H^t(F)`. Approximating `u` by Fourier partial sums — which lie in `H^{r' + 1}`
   so that the classical chain rule applies — and passing to the limit via Ehrling's inequality
   identifies this product as the weak derivative of `f ∘ u`, lifting `f ∘ u` from `H^t(F)` to
   `H^s(F)` with an explicit uniform norm bound.
3. **Hadamard factorization, strict Fréchet differentiability, and `C^∞` smoothness.** On the open
   set of pairs `(x, y) ∈ E × E` whose connecting segment lies in `U`,
   `f y - f x = hadamardFactor f x y (y - x)` (`hadamardFactor`). Lifting `hadamardFactor f` to
   `H^s(E × E) → H^s(E →L[ℝ] F)` writes `nemytskii f u₂ - nemytskii f u₁` as a symmetric
   real-bilinear product (`TauCeti.CircleSobolev.realConvolution`) against `u₂ - u₁`. Uniform
   compact-range bounds on `hadamardFactor f` give local Lipschitz continuity and hence continuity;
   continuity of `nemytskii (uncurry (hadamardFactor f))` at the diagonal `(u₀, u₀)` then gives
   `HasStrictFDerivAt`, and induction on the differentiation order `k` yields `C^k` and `C^∞`
   smoothness on `{u ∈ H^s(E) | ∀ x, u x ∈ U}`.

## Main statements

* `TauCeti.CircleSobolev.toContinuousMap_nemytskii_of_contDiffOn`: if `f : E → F` is `C^n` on an
  open set `U` with `⌊2s⌋₊ ≤ n` (in particular for `f` smooth) and `u ∈ H^s(E)` maps into `U`,
  then the continuous representative of `nemytskii f u` is `f ∘ u`.
* `TauCeti.CircleSobolev.nemytskii_comp_of_contDiffOn`: functoriality
  `nemytskii (g ∘ f) u = nemytskii g (nemytskii f u)` for composable `C^n` maps.
* `TauCeti.CircleSobolev.exists_norm_nemytskii_le_of_isCompact`: `‖nemytskii f u‖` is uniformly
  bounded when `u` has range in a compact subset `K ⊆ U` and `‖u‖ ≤ R`.
* `TauCeti.CircleSobolev.exists_lipschitzOnWith_nemytskii` and
  `TauCeti.CircleSobolev.continuousOn_nemytskii`: `nemytskii f` is locally Lipschitz and continuous
  on `{u ∈ H^s(E) | ∀ x, u x ∈ U}` when `⌊2s⌋₊ + 1 ≤ n`.
* `TauCeti.CircleSobolev.hasStrictFDerivAt_nemytskii_of_contDiffOn` and
  `TauCeti.CircleSobolev.toContinuousMap_fderiv_nemytskii_of_contDiffOn`: for `⌊2s⌋₊ + 2 ≤ n`,
  `nemytskii f` is strictly Fréchet differentiable at `u`, with derivative
  `v ↦ realConvolution hs.out (.id ℝ (E →L[ℝ] F)) (nemytskii (fderiv ℝ f) u) v` acting pointwise
  as `x ↦ fderiv ℝ f (u x) (v x)`.
* `TauCeti.CircleSobolev.contDiffOn_nemytskii` and `TauCeti.CircleSobolev.contDiff_nemytskii`: if
  `f` is `C^∞` on `U` (respectively on `E`), then `nemytskii f` is `C^∞` on
  `{u ∈ H^s(E) | ∀ x, u x ∈ U}` (respectively on `H^s(E)`).

## References

* R. S. Palais, *Foundations of Global Non-Linear Analysis*, W. A. Benjamin, 1968, Chapter 9
  (smoothness of composition operators on Sobolev sections).
* M. E. Taylor, *Partial Differential Equations III*, Springer, 2011, Chapter 13, Section 3
  (Sobolev algebras and smooth Nemytskii operators).
* T. Runst and W. Sickel, *Sobolev Spaces of Fractional Order, Nemytskij Operators, and Nonlinear
  Partial Differential Equations*, de Gruyter, 1996, Chapter 5.
* J. W. Robbin and D. A. Salamon, *A construction of the Deligne–Mumford orbifold*,
  J. Eur. Math. Soc. **8** (2006), 611–699 (Banach manifolds of Sobolev boundary maps).
-/

public section

noncomputable section

open MeasureTheory Complex Filter Set
open scoped ContDiff ENNReal NNReal Real Topology

universe u v

namespace TauCeti

namespace CircleSobolev

/-- Every finite-dimensional complex normed space is complete, supplying `[CompleteSpace G]` for
continuous representatives on `CircleSobolev s G`. -/
local instance instCompleteSpaceOfFiniteDimensional {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℂ G] [FiniteDimensional ℂ G] : CompleteSpace G :=
  FiniteDimensional.completeSpace ℂ G

/-! ### Action of Nemytskii maps on continuous linear operators -/

section Linear

variable {s : ℝ} [hs : Fact (1 / 2 < s)]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- The Nemytskii map of a continuous complex-linear operator `L : E →L[ℂ] F` is `mapCLM L`. -/
@[simp]
theorem nemytskii_continuousLinearMap (L : E →L[ℂ] F) (u : CircleSobolev s E) :
    nemytskii (L : E → F) u = mapCLM L u := by
  have : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  exact nemytskii_eq_of_forall_toContinuousMap_apply 1 fun x ↦
    toContinuousMap_mapCLM_apply 1 hs.out L u x

/-- The Nemytskii map of a continuous real-linear operator `Ψ : E →L[ℝ] F` is `mapRealCLM Ψ`. -/
@[simp]
theorem nemytskii_continuousLinearMap_real (Ψ : E →L[ℝ] F) (u : CircleSobolev s E) :
    nemytskii (Ψ : E → F) u = mapRealCLM Ψ u := by
  have : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  exact nemytskii_eq_of_forall_toContinuousMap_apply 1 fun x ↦
    toContinuousMap_mapRealCLM_apply 1 hs.out Ψ u x

end Linear

/-! ### Fractional base case `1/2 < s < 1` via Gagliardo–Slobodeckij energy -/

section BaseCase

variable (T : ℝ) [hT : Fact (0 < T)]

private theorem norm_ofContinuousMap_sq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H] (g : C(AddCircle T, H)) :
    ‖ofContinuousMap T g‖ ^ 2 = ∫ x, ‖g x‖ ^ 2 ∂AddCircle.haarAddCircle := by
  have h := real_inner_ofContinuousMap T g g
  rw [real_inner_self_eq_norm_sq] at h
  refine h.trans (integral_congr_ae (ae_of_all _ fun x ↦ ?_))
  dsimp only
  rw [← RCLike.re_eq_complex_re, inner_self_eq_norm_sq]

private theorem mapCLM_ofContinuousMap {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    (L : E →L[ℂ] F) (g : C(AddCircle T, E)) :
    mapCLM L (ofContinuousMap T g) =
      ofContinuousMap T ((ContinuousMap.mk L L.continuous).comp g) := by
  refine CircleSobolev.ext <| funext fun n ↦ ?_
  rw [coeff_mapCLM, coeff_ofContinuousMap, coeff_ofContinuousMap]
  exact (L.fourierCoeff_comp (g.integrable AddCircle.haarAddCircle) n).symm

/-- Between finite-dimensional complex normed spaces, a pointwise norm bound `‖ψ x‖ ≤ M ‖υ x‖`
induces an `H⁰` norm bound `‖ofContinuousMap T ψ‖ ≤ C M ‖ofContinuousMap T υ‖` with `C` depending
only on `E` and `F`. -/
private theorem exists_norm_ofContinuousMap_le_pointwise {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [FiniteDimensional ℂ F] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {M : ℝ}, 0 ≤ M → ∀ (ψ : C(AddCircle T, F)) (υ : C(AddCircle T, E)),
      (∀ x, ‖ψ x‖ ≤ M * ‖υ x‖) → ‖ofContinuousMap T ψ‖ ≤ C * M * ‖ofContinuousMap T υ‖ := by
  let eE : E ≃L[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ E)) :=
    ((Module.finBasis ℂ E).equiv (EuclideanSpace.basisFun _ ℂ).toBasis
      (Equiv.refl _)).toContinuousLinearEquiv
  let eF : F ≃L[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ F)) :=
    ((Module.finBasis ℂ F).equiv (EuclideanSpace.basisFun _ ℂ).toBasis
      (Equiv.refl _)).toContinuousLinearEquiv
  let LE := eE.toContinuousLinearMap
  let LEi := eE.symm.toContinuousLinearMap
  let LF := eF.toContinuousLinearMap
  let LFi := eF.symm.toContinuousLinearMap
  refine ⟨‖LFi‖ * ‖LF‖ * ‖LEi‖ * ‖LE‖, by positivity, fun {M} hM ψ υ hpt ↦ ?_⟩
  let ψ' : C(AddCircle T, _) := (ContinuousMap.mk LF LF.continuous).comp ψ
  let υ' : C(AddCircle T, _) := (ContinuousMap.mk LE LE.continuous).comp υ
  have hK : 0 ≤ ‖LF‖ * M * ‖LEi‖ := by positivity
  have hsq : ‖ofContinuousMap T ψ'‖ ^ 2 ≤ (‖LF‖ * M * ‖LEi‖ * ‖ofContinuousMap T υ'‖) ^ 2 := by
    rw [mul_pow, norm_ofContinuousMap_sq, norm_ofContinuousMap_sq, ← integral_const_mul]
    refine integral_mono (ψ'.continuous.norm.pow 2 |>.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
      ((υ'.continuous.norm.pow 2 |>.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)).const_mul _) fun x ↦ ?_
    dsimp only
    rw [← mul_pow]
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
    calc ‖LF (ψ x)‖ ≤ ‖LF‖ * ‖ψ x‖ := LF.le_opNorm _
      _ ≤ ‖LF‖ * (M * ‖υ x‖) := mul_le_mul_of_nonneg_left (hpt x) (norm_nonneg _)
      _ = ‖LF‖ * M * ‖LEi (LE (υ x))‖ := by change _ = _ * ‖eE.symm (eE (υ x))‖; simp [mul_assoc]
      _ ≤ ‖LF‖ * M * (‖LEi‖ * ‖LE (υ x)‖) :=
        mul_le_mul_of_nonneg_left (LEi.le_opNorm _) (by positivity)
      _ = ‖LF‖ * M * ‖LEi‖ * ‖υ' x‖ := by
        change ‖LF‖ * M * (‖LEi‖ * ‖υ' x‖) = _
        ring
  have hL2 : ‖ofContinuousMap T ψ'‖ ≤ ‖LF‖ * M * ‖LEi‖ * ‖mapCLM LE (ofContinuousMap T υ)‖ := by
    rw [mapCLM_ofContinuousMap T LE υ]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq
  have hψ_eq : ofContinuousMap T ψ = mapCLM LFi (ofContinuousMap T ψ') := by
    rw [mapCLM_ofContinuousMap]
    exact congrArg (ofContinuousMap T) (ContinuousMap.ext fun x ↦ (eF.symm_apply_apply (ψ x)).symm)
  rw [hψ_eq]
  calc ‖mapCLM LFi (ofContinuousMap T ψ')‖
      ≤ ‖LFi‖ * ‖ofContinuousMap T ψ'‖ := norm_mapCLM_le _ _
    _ ≤ ‖LFi‖ * (‖LF‖ * M * ‖LEi‖ * ‖mapCLM LE (ofContinuousMap T υ)‖) :=
        mul_le_mul_of_nonneg_left hL2 (norm_nonneg _)
    _ ≤ ‖LFi‖ * (‖LF‖ * M * ‖LEi‖ * (‖LE‖ * ‖ofContinuousMap T υ‖)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (norm_mapCLM_le _ _) hK) (norm_nonneg _)
    _ = ‖LFi‖ * ‖LF‖ * ‖LEi‖ * ‖LE‖ * M * ‖ofContinuousMap T υ‖ := by ring

private theorem rotate_ofContinuousMap {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [FiniteDimensional ℂ F] (h : AddCircle T) (g : C(AddCircle T, F)) :
    rotate h (ofContinuousMap T g) =
      ofContinuousMap T (g.comp ⟨(· + h), continuous_add_const h⟩) := by
  refine CircleSobolev.ext <| funext fun n ↦ ?_
  rw [coeff_rotate, coeff_ofContinuousMap, coeff_ofContinuousMap, fourierCoeff, fourierCoeff,
    ← integral_smul, ← integral_add_right_eq_self (μ := AddCircle.haarAddCircle)
      (fun y ↦ fourier n h • fourier (-n) y • g y) h]
  refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  have hh : fourier n h * fourier (-n) h = 1 := by
    rw [← fourier_add, add_neg_cancel, fourier_zero]
  simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, smul_smul, fourier_apply_add]
  exact congrArg (· • g (x + h)) (by linear_combination fourier (-n) x * hh)

private theorem exists_lipschitzOnWith_of_contDiffOn_isCompact {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U K : Set E} (hU : IsOpen U) {f : E → F} (hf : ContDiffOn ℝ 1 f U)
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ L : ℝ≥0, LipschitzOnWith L f K := by
  refine LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hK fun x hx ↦ ?_
  obtain ⟨L, t, ht, hLip⟩ := (hf.contDiffAt (hU.mem_nhds (hKU hx))).exists_lipschitzOnWith
  exact ⟨L, t, mem_nhdsWithin_of_mem_nhds ht, hLip⟩

private theorem slobodeckijEnergy_ofContinuousMap_comp_le {s : ℝ} (hs : 1 / 2 < s)
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    {K : Set E} {L : ℝ≥0} {f : E → F} (hLip : LipschitzOnWith L f K) {C₀ : ℝ}
    (hpt0 : ∀ {M : ℝ}, 0 ≤ M → ∀ (ψ : C(AddCircle T, F)) (υ : C(AddCircle T, E)),
      (∀ x, ‖ψ x‖ ≤ M * ‖υ x‖) → ‖ofContinuousMap T ψ‖ ≤ C₀ * M * ‖ofContinuousMap T υ‖)
    {u : CircleSobolev s E} (huK : ∀ x, toContinuousMap T hs u x ∈ K)
    (fu : C(AddCircle T, F)) (hfu : ∀ x, fu x = f (toContinuousMap T hs u x)) :
    slobodeckijEnergy T s (ofContinuousMap T fu) ≤
      ENNReal.ofReal ((C₀ * L) ^ 2) *
        slobodeckijEnergy T s (inclusion (by linarith : (0 : ℝ) ≤ s) u) := by
  have hrot (h : AddCircle T) :
      ‖rotate h (ofContinuousMap T fu) - ofContinuousMap T fu‖ ≤
        C₀ * L * ‖rotate h (inclusion (by linarith : (0 : ℝ) ≤ s) u) -
          inclusion (by linarith : (0 : ℝ) ≤ s) u‖ := by
    rw [rotate_ofContinuousMap, ← map_sub, ← ofContinuousMap_toContinuousMap T hs u,
      rotate_ofContinuousMap, ← map_sub]
    refine hpt0 L.coe_nonneg _ _ fun x ↦ ?_
    simp only [ContinuousMap.sub_apply, ContinuousMap.comp_apply, ContinuousMap.coe_mk, hfu]
    exact hLip.norm_sub_le (huK (x + h)) (huK x)
  rw [slobodeckijEnergy_def, slobodeckijEnergy_def,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun h ↦ ?_
  rw [← ENNReal.ofReal_mul (sq_nonneg _), mul_div_assoc', ← mul_pow]
  gcongr
  exact hrot h

/-- **Base case `1/2 < s < 1`:** if `f : E → F` is `C¹` on an open set `U` and `K ⊆ U` is compact,
then `f ∘ u` belongs to `H^s(F)` with a uniform `H^s` norm bound across all `u ∈ H^s(E)` satisfying
`∀ x, u x ∈ K` and `‖u‖ ≤ R`. -/
private theorem exists_toContinuousMap_eq_comp_and_norm_le_base {s : ℝ} (hs : 1 / 2 < s)
    (hs1 : s < 1) {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    {U : Set E} (hU : IsOpen U) {f : E → F} (hf : ContDiffOn ℝ 1 f U)
    {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U) (R : ℝ) (_hR : 0 ≤ R) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ u : CircleSobolev s E,
      (∀ x, toContinuousMap T hs u x ∈ K) → ‖u‖ ≤ R →
        ∃ w : CircleSobolev s F,
          (∀ x, toContinuousMap T hs w x = f (toContinuousMap T hs u x)) ∧ ‖w‖ ≤ B := by
  have hs0 : 0 < s := by linarith
  obtain ⟨C₀, _, hpt0⟩ := exists_norm_ofContinuousMap_le_pointwise (E := E) (F := F) T
  obtain ⟨L, hLip⟩ := exists_lipschitzOnWith_of_contDiffOn_isCompact hU hf hK hKU
  obtain ⟨M₀, hM₀⟩ := hK.exists_bound_of_continuousOn (hf.continuousOn.mono hKU)
  set M := max M₀ 0
  have hM : 0 ≤ M := le_max_right _ _
  obtain ⟨CE, hCE, hSlobE⟩ := exists_slobodeckijEnergy_le (E := E) T hs0 hs1
  obtain ⟨CN, hCN_top, hNormSq⟩ := exists_norm_sq_le_slobodeckijEnergy (E := F) T hs0.le
  set Bsq := (‖ofContinuousMap T (E := F)‖ * M) ^ 2 +
    CN.toReal * ((C₀ * L) ^ 2 * (CE * R ^ 2))
  refine ⟨√Bsq, Real.sqrt_nonneg _, fun u huK huR ↦ ?_⟩
  let uC := toContinuousMap T hs u
  let fu : C(AddCircle T, F) :=
    ⟨fun x ↦ f (uC x), hf.continuousOn.comp_continuous uC.continuous fun x ↦ hKU (huK x)⟩
  set c : CircleSobolev 0 F := ofContinuousMap T fu
  have hc_norm : ‖c‖ ≤ ‖ofContinuousMap T (E := F)‖ * M :=
    (ofContinuousMap T).le_opNorm fu |>.trans
      (mul_le_mul_of_nonneg_left ((ContinuousMap.norm_le _ hM).2 fun x ↦
        (hM₀ _ (huK x)).trans (le_max_left _ _)) (norm_nonneg _))
  have hSlob_c : slobodeckijEnergy T s c ≤ ENNReal.ofReal ((C₀ * L) ^ 2 * (CE * R ^ 2)) := by
    refine (slobodeckijEnergy_ofContinuousMap_comp_le T hs hLip hpt0 huK fu fun _ ↦ rfl).trans ?_
    rw [ENNReal.ofReal_mul (sq_nonneg _)]
    gcongr
    exact (hSlobE u).trans (ENNReal.ofReal_le_ofReal (by gcongr))
  obtain ⟨w, hw⟩ := (exists_inclusion_eq_iff_slobodeckijEnergy_ne_top T hs0 hs1 c).2
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hSlob_c)
  have hwc : toContinuousMap T hs w = fu := (toContinuousMap_eq_iff T hs w fu).2 fun n ↦ by
    rw [← coeff_ofContinuousMap T, show ofContinuousMap T fu = c from rfl, ← hw, coeff_inclusion]
  refine ⟨w, fun x ↦ congrArg (· x) hwc, ?_⟩
  have hle_enn : ENNReal.ofReal (‖w‖ ^ 2) ≤ ENNReal.ofReal Bsq := by
    calc ENNReal.ofReal (‖w‖ ^ 2)
        ≤ ENNReal.ofReal (‖c‖ ^ 2) + CN * slobodeckijEnergy T s c := by
          simpa only [hw] using hNormSq w
      _ ≤ ENNReal.ofReal ((‖ofContinuousMap T (E := F)‖ * M) ^ 2) +
            CN * ENNReal.ofReal ((C₀ * L) ^ 2 * (CE * R ^ 2)) := by gcongr
      _ = ENNReal.ofReal Bsq := by
          rw [← ENNReal.ofReal_toReal hCN_top,
            ← ENNReal.ofReal_mul ENNReal.toReal_nonneg,
            ← ENNReal.ofReal_add (sq_nonneg _) (by positivity)]
  exact (Real.le_sqrt (norm_nonneg w) (by positivity)).2
    ((ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hle_enn)

end BaseCase

/-! ### Inductive bootstrap to all supercritical orders `s > 1/2` -/

section Bootstrap

variable (T : ℝ) [hT : Fact (0 < T)]

/-- By Ehrling's interpolation inequality (`exists_norm_inclusion_le`), an `H^r`-bounded family
whose continuous representatives converge uniformly converges in `H^{r'}` for every `0 < r' < r`. -/
private theorem tendsto_inclusion_of_norm_le_of_tendsto_toContinuousMap
    {r' r : ℝ} (hr'0 : 0 < r') (hr'r : r' < r) (hr : 1 / 2 < r)
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
    {ι : Type*} {l : Filter ι} {g : ι → CircleSobolev r G} {g₀ : CircleSobolev r G} {B : ℝ}
    (hB : ∀ᶠ i in l, ‖g i‖ ≤ B)
    (hcont : Tendsto (fun i ↦ toContinuousMap T hr (g i)) l (𝓝 (toContinuousMap T hr g₀))) :
    Tendsto (fun i ↦ inclusion hr'r.le (g i)) l (𝓝 (inclusion hr'r.le g₀)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set M := max (B + ‖g₀‖) 1
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  obtain ⟨C, _, hC⟩ :=
    exists_norm_inclusion_le (E := G) hr'0.le hr'r (div_pos (half_pos hε) hM)
  have h0 : Tendsto (fun i ↦ C * ‖ofContinuousMap T
      (toContinuousMap T hr (g i) - toContinuousMap T hr g₀)‖) l (𝓝 0) := by
    simpa using (((ofContinuousMap T (E := G)).continuous.tendsto 0).comp
      (tendsto_sub_nhds_zero_iff.2 hcont)).norm.const_mul C
  filter_upwards [hB, (tendsto_order.1 h0).2 (ε / 2) (half_pos hε)] with i hi hi0
  rw [dist_eq_norm, ← map_sub]
  have hnorm_d : ‖g i - g₀‖ ≤ M := by
    linarith [norm_sub_le (g i) g₀, le_max_left (B + ‖g₀‖) 1]
  have hincl0 : inclusion (by linarith : (0 : ℝ) ≤ r) (g i - g₀) =
      ofContinuousMap T (toContinuousMap T hr (g i) - toContinuousMap T hr g₀) := by
    rw [map_sub, ← ofContinuousMap_toContinuousMap T hr (g i),
      ← ofContinuousMap_toContinuousMap T hr g₀, ← map_sub]
  calc ‖inclusion hr'r.le (g i - g₀)‖
      ≤ ε / 2 / M * ‖g i - g₀‖ + C * ‖inclusion (by linarith : (0 : ℝ) ≤ r) (g i - g₀)‖ :=
        hC (g i - g₀)
    _ ≤ ε / 2 / M * M + C * ‖ofContinuousMap T
          (toContinuousMap T hr (g i) - toContinuousMap T hr g₀)‖ := by
        rw [hincl0]
        gcongr
    _ < ε / 2 + ε / 2 := by
        rw [div_mul_cancel₀ _ hM.ne']
        linarith
    _ = ε := add_halves ε

/-- For a trigonometric polynomial `∑_{k ∈ S} single k (c k)` taking values in `U`, the classical
chain rule identifies the Fourier coefficients of the asymmetric product `(df ∘ u_S) u_S'` with
`2πin/T` times the Fourier coefficients of `f ∘ u_S`. -/
private theorem coeff_realConvolutionAsym_sum_single {t r' r s : ℝ} (ht : 0 ≤ t)
    (htr' : t + 1 / 2 < r') (hr'r : r' < r) (hrs : r < s) (hts : t + 1 = s)
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    {U : Set E} (hU : IsOpen U) {f : E → F} (hf : ContDiffOn ℝ 1 f U)
    (S : Finset ℤ) (c : ℤ → E)
    (huU : ∀ x, toContinuousMap T (by linarith) (∑ k ∈ S, single (s := s) k (c k)) x ∈ U)
    {gS : CircleSobolev r (E →L[ℝ] F)}
    (hgS : ∀ x, toContinuousMap T (by linarith) gS x =
      fderiv ℝ f (toContinuousMap T (by linarith) (∑ k ∈ S, single (s := s) k (c k)) x))
    (n : ℤ) :
    (realConvolutionAsym ht htr' (.id ℝ (E →L[ℝ] F)) (inclusion hr'r.le gS)
      (derivative T hts.le (∑ k ∈ S, single (s := s) k (c k)))).coeff n =
      (2 * π * I * n / T : ℂ) • fourierCoeff
        (fun x ↦ f (toContinuousMap T (by linarith) (∑ k ∈ S, single (s := s) k (c k)) x)) n := by
  have : FiniteDimensional ℝ E := Module.Finite.trans ℂ E
  have : FiniteDimensional ℂ (E →L[ℝ] F) := ContinuousLinearMap.finiteDimensional_of_isScalarTower
  have hr' : 1 / 2 < r' := by linarith
  have hs : 1 / 2 < s := by linarith
  let p : CircleSobolev (r' + 1) E := ∑ k ∈ S, single k (c k)
  let uS : CircleSobolev s E := ∑ k ∈ S, single k (c k)
  have hp_incl : inclusion (by linarith : s ≤ r' + 1) p = uS := by simp [p, uS]
  have hp_eval (x : AddCircle T) :
      toContinuousMap T (by linarith) p x = toContinuousMap T hs uS x := by
    rw [← hp_incl, toContinuousMap_inclusion]
  have hp_deriv : inclusion (by linarith : t ≤ r') (derivative T le_rfl p) =
      derivative T hts.le uS := by
    rw [← hp_incl, derivative_inclusion, inclusion_derivative]
  let w : CircleSobolev r' F :=
    realConvolution hr' (.id ℝ (E →L[ℝ] F)) (inclusion hr'r.le gS) (derivative T le_rfl p)
  have hw_incl : realConvolutionAsym ht htr' (.id ℝ (E →L[ℝ] F)) (inclusion hr'r.le gS)
      (derivative T hts.le uS) = inclusion (by linarith : t ≤ r') w := by
    rw [← hp_deriv, realConvolutionAsym_inclusion_right]
  have hchain (x : ℝ) : HasDerivAt (fun y : ℝ ↦ f (toContinuousMap T hs uS y))
      (toContinuousMap T hr' w x) x := by
    have hd_p : HasDerivAt (fun y : ℝ ↦ toContinuousMap T hs uS y)
        (toContinuousMap T hr' (derivative T le_rfl p) x) x := by
      simpa only [hp_eval] using hasDerivAt_toContinuousMap T hr' le_rfl p x
    have hdf : HasFDerivAt f (fderiv ℝ f (toContinuousMap T hs uS x))
        (toContinuousMap T hs uS x) :=
      ((hf.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds (huU x))).hasFDerivAt
    have hwx : toContinuousMap T hr' w x =
        fderiv ℝ f (toContinuousMap T hs uS x)
          (toContinuousMap T hr' (derivative T le_rfl p) x) := by
      change toContinuousMap T hr'
          (realConvolution hr' (.id ℝ (E →L[ℝ] F)) (inclusion hr'r.le gS)
            (derivative T le_rfl p)) x = _
      rw [toContinuousMap_realConvolution_apply, ContinuousLinearMap.id_apply,
        toContinuousMap_inclusion, hgS x]
    rw [hwx]
    exact hdf.comp_hasDerivAt x hd_p
  rw [hw_incl, coeff_inclusion, ← fourierCoeff_toContinuousMap T hr' w n]
  exact fourierCoeff_of_hasDerivAt (f := fun x ↦ f (toContinuousMap T hs uS x))
    hchain (toContinuousMap T hr' w).continuous n

private theorem tendsto_continuousMap_of_eventually_eq_comp {E G : Type*}
    [MetricSpace E] [MetricSpace G] {K' : Set E} (hK' : IsCompact K') {g : E → G}
    (hg : ContinuousOn g K') {ι : Type*} {l : Filter ι}
    {φ : ι → C(AddCircle T, E)} {φ₀ : C(AddCircle T, E)} (hφ : Tendsto φ l (𝓝 φ₀))
    (hφ_mem : ∀ᶠ i in l, ∀ x, φ i x ∈ K') (hφ₀_mem : ∀ x, φ₀ x ∈ K')
    {ψ : ι → C(AddCircle T, G)} {ψ₀ : C(AddCircle T, G)}
    (hψ : ∀ᶠ i in l, ∀ x, ψ i x = g (φ i x)) (hψ₀ : ∀ x, ψ₀ x = g (φ₀ x)) :
    Tendsto ψ l (𝓝 ψ₀) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨η, hη, hη_uc⟩ := Metric.uniformContinuousOn_iff.1
    (hK'.uniformContinuousOn_of_continuous hg) ε hε
  filter_upwards [hψ, hφ_mem, Metric.tendsto_nhds.1 hφ η hη] with i hi hi_mem hi_dist
  refine (ContinuousMap.dist_lt_iff hε).2 fun x ↦ ?_
  rw [hi x, hψ₀ x]
  exact hη_uc _ (hi_mem x) _ (hφ₀_mem x) ((ContinuousMap.dist_apply_le_dist x).trans_lt hi_dist)

private theorem eventually_sum_single_mem_cthickening {r s : ℝ} (hrs : r ≤ s) (hs : 1 / 2 < s)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {K K' : Set E} {δ R : ℝ} (hδ : 0 < δ) (hcthick : Metric.cthickening δ K ⊆ K')
    {u : CircleSobolev s E} (huK : ∀ x, toContinuousMap T hs u x ∈ K) (huR : ‖u‖ ≤ R) :
    ∀ᶠ S : Finset ℤ in atTop,
      (∀ x, toContinuousMap T hs (∑ k ∈ S, single k (u.coeff k)) x ∈ K') ∧
        ‖inclusion hrs (∑ k ∈ S, single k (u.coeff k))‖ ≤ R + 1 := by
  let uS : Finset ℤ → CircleSobolev s E := fun S ↦ ∑ k ∈ S, single k (u.coeff k)
  have huS_tendsto : Tendsto uS atTop (𝓝 u) := hasSum_single u
  have huS_cont : Tendsto (fun S ↦ toContinuousMap T hs (uS S)) atTop
      (𝓝 (toContinuousMap T hs u)) :=
    (toContinuousMap T hs).continuous.tendsto u |>.comp huS_tendsto
  filter_upwards [Metric.tendsto_nhds.1 huS_cont δ hδ,
    Metric.tendsto_nhds.1 huS_tendsto 1 one_pos] with S hS1 hS2
  refine ⟨fun x ↦ hcthick (Metric.mem_cthickening_of_dist_le _ (toContinuousMap T hs u x)
    δ K (huK x) ((ContinuousMap.dist_apply_le_dist x).trans hS1.le)), ?_⟩
  rw [dist_eq_norm] at hS2
  calc ‖inclusion hrs (uS S)‖ ≤ ‖uS S‖ := norm_inclusion_le _ _
    _ ≤ ‖uS S - u‖ + ‖u‖ := norm_le_norm_sub_add (uS S) u
    _ ≤ 1 + R := add_le_add hS2.le huR
    _ = R + 1 := add_comm 1 R

/-- Passing from Fourier partial sums `u_S` to `u ∈ H^s(E)` via Ehrling's inequality identifies the
Fourier coefficients of `realConvolutionAsym` with `(2πin/T) • (f ∘ u)_n`. -/
private theorem coeff_realConvolutionAsym_eq_deriv_fourierCoeff {t r' r s : ℝ} (ht : 0 ≤ t)
    (htr' : t + 1 / 2 < r') (hr'r : r' < r) (hrs : r < s) (hts : t + 1 = s)
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    {U K K' : Set E} {δ R B₁ : ℝ} (hU : IsOpen U) (hK' : IsCompact K') (hK'U : K' ⊆ U)
    (hδ : 0 < δ) (hcthick : Metric.cthickening δ K ⊆ K')
    {f : E → F} (hf : ContDiffOn ℝ 1 f U)
    (hIH : ∀ v : CircleSobolev r E, (∀ x, toContinuousMap T (by linarith) v x ∈ K') →
      ‖v‖ ≤ R + 1 → ∃ g : CircleSobolev r (E →L[ℝ] F),
        (∀ x, toContinuousMap T (by linarith) g x =
          fderiv ℝ f (toContinuousMap T (by linarith) v x)) ∧ ‖g‖ ≤ B₁)
    {u : CircleSobolev s E} (huK : ∀ x, toContinuousMap T (by linarith) u x ∈ K)
    (huR : ‖u‖ ≤ R) {gu : CircleSobolev r (E →L[ℝ] F)}
    (hgu : ∀ x, toContinuousMap T (by linarith) gu x =
      fderiv ℝ f (toContinuousMap T (by linarith) u x))
    (n : ℤ) :
    (realConvolutionAsym ht htr' (.id ℝ (E →L[ℝ] F)) (inclusion hr'r.le gu)
      (derivative T hts.le u)).coeff n =
      (2 * π * I * n / T : ℂ) • fourierCoeff
        (fun x ↦ f (toContinuousMap T (by linarith) u x)) n := by
  have : FiniteDimensional ℝ E := Module.Finite.trans ℂ E
  have : FiniteDimensional ℂ (E →L[ℝ] F) := ContinuousLinearMap.finiteDimensional_of_isScalarTower
  have hr : 1 / 2 < r := by linarith
  have hs : 1 / 2 < s := by linarith
  let uS : Finset ℤ → CircleSobolev s E := fun S ↦ ∑ k ∈ S, single k (u.coeff k)
  have huS_tendsto : Tendsto uS atTop (𝓝 u) := hasSum_single u
  have huS_cont : Tendsto (fun S ↦ toContinuousMap T hs (uS S)) atTop
      (𝓝 (toContinuousMap T hs u)) :=
    (toContinuousMap T hs).continuous.tendsto u |>.comp huS_tendsto
  have huK' (x : AddCircle T) : toContinuousMap T hs u x ∈ K' :=
    hcthick (Metric.self_subset_cthickening _ (huK x))
  have hev : ∀ᶠ S in atTop,
      (∀ x, toContinuousMap T hs (uS S) x ∈ K') ∧ ‖inclusion hrs.le (uS S)‖ ≤ R + 1 :=
    eventually_sum_single_mem_cthickening T hrs.le hs hδ hcthick huK huR
  classical
  let gS : Finset ℤ → CircleSobolev r (E →L[ℝ] F) := fun S ↦
    if h : (∀ x, toContinuousMap T hs (uS S) x ∈ K') ∧ ‖inclusion hrs.le (uS S)‖ ≤ R + 1 then
      (hIH (inclusion hrs.le (uS S)) (by simpa [toContinuousMap_inclusion] using h.1) h.2).choose
    else gu
  have hgS_spec : ∀ᶠ S in atTop,
      (∀ x, toContinuousMap T hr (gS S) x = fderiv ℝ f (toContinuousMap T hs (uS S) x)) ∧
        ‖gS S‖ ≤ B₁ := by
    filter_upwards [hev] with S hS
    dsimp only [gS]
    rw [dite_eq_left hS]
    have hspec := (hIH (inclusion hrs.le (uS S))
      (by simpa [toContinuousMap_inclusion] using hS.1) hS.2).choose_spec
    exact ⟨fun x ↦ by simpa [toContinuousMap_inclusion] using hspec.1 x, hspec.2⟩
  have hgS_r' : Tendsto (fun S ↦ inclusion hr'r.le (gS S)) atTop (𝓝 (inclusion hr'r.le gu)) :=
    tendsto_inclusion_of_norm_le_of_tendsto_toContinuousMap T (by linarith) hr'r hr
      (hgS_spec.mono fun _ h ↦ h.2) <|
      tendsto_continuousMap_of_eventually_eq_comp T hK'
        ((hf.continuousOn_fderiv_of_isOpen hU le_rfl).mono hK'U) huS_cont
        (hev.mono fun _ h ↦ h.1) huK' (hgS_spec.mono fun _ h ↦ h.1) hgu
  let A := realConvolutionAsym ht htr' (.id ℝ (E →L[ℝ] F))
  have hLHS : Tendsto (fun S ↦ (A (inclusion hr'r.le (gS S)) (derivative T hts.le (uS S))).coeff n)
      atTop (𝓝 ((A (inclusion hr'r.le gu) (derivative T hts.le u)).coeff n)) := by
    simpa only [Function.comp_def, coeffCLM_apply] using
      ((coeffCLM n).continuous.tendsto _).comp
        ((A.isBoundedBilinearMap.continuous.tendsto _).comp
          (hgS_r'.prodMk_nhds (((derivative T hts.le).continuous.tendsto u).comp huS_tendsto)))
  let fu : C(AddCircle T, F) := ⟨fun x ↦ f (toContinuousMap T hs u x),
    hf.continuousOn.comp_continuous (toContinuousMap T hs u).continuous fun x ↦ hK'U (huK' x)⟩
  let fuS : Finset ℤ → C(AddCircle T, F) := fun S ↦
    if h : ∀ x, toContinuousMap T hs (uS S) x ∈ K' then
      ⟨fun x ↦ f (toContinuousMap T hs (uS S) x),
        hf.continuousOn.comp_continuous (toContinuousMap T hs (uS S)).continuous
          fun x ↦ hK'U (h x)⟩
    else fu
  have hfuS_cont : Tendsto fuS atTop (𝓝 fu) :=
    tendsto_continuousMap_of_eventually_eq_comp T hK' (hf.continuousOn.mono hK'U) huS_cont
      (hev.mono fun _ h ↦ h.1) huK'
      (hev.mono fun S hS x ↦ by dsimp only [fuS]; rw [dite_eq_left hS.1]; rfl) fun _ ↦ rfl
  have hRHS : Tendsto (fun S ↦ (2 * π * I * n / T : ℂ) • fourierCoeff (fuS S) n) atTop
      (𝓝 ((2 * π * I * n / T : ℂ) • fourierCoeff fu n)) := by
    have hfC : Tendsto (fun S ↦ (ofContinuousMap T (fuS S)).coeff n) atTop
        (𝓝 ((ofContinuousMap T fu).coeff n)) := by
      simpa only [Function.comp_def, ContinuousLinearMap.comp_apply, coeffCLM_apply] using
        (((coeffCLM n).comp (ofContinuousMap T)).continuous.tendsto fu).comp hfuS_cont
    simpa only [coeff_ofContinuousMap] using hfC.const_smul (2 * π * I * n / T : ℂ)
  refine tendsto_nhds_unique hLHS (hRHS.congr' ?_)
  filter_upwards [hev, hgS_spec] with S hS hgS
  dsimp only [fuS]
  rw [dite_eq_left hS.1]
  simp only [ContinuousMap.coe_mk]
  exact (coeff_realConvolutionAsym_sum_single T ht htr' hr'r hrs hts hU hf S u.coeff
    (fun x ↦ hK'U (hS.1 x)) hgS.1 n).symm

/-- Given `ar ∈ H^r(F)` representing `f ∘ u` (`1/2 < r < s`, `t ≤ r`) and `b ∈ H^t(F)` whose
Fourier coefficients satisfy `b_n = (2πin/T) • ar_n`, constructs `w ∈ H^s(F)` (`t + 1 = s`)
representing `f ∘ u` with `‖w‖ ≤ √(2 B₀² + 2 (T / 2π)² Bd²)`. -/
private theorem exists_toContinuousMap_eq_and_norm_le_of_derivative_coeff
    {t r s : ℝ} (htr : t ≤ r) (hr : 1 / 2 < r) (hrs : r < s) (hts : t + 1 = s)
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    {U : Set E} {f : E → F} (hf : ContinuousOn f U)
    {u : CircleSobolev s E} (huU : ∀ x, toContinuousMap T (by linarith) u x ∈ U)
    {B₀ Bd : ℝ} (ar : CircleSobolev r F)
    (har : ∀ x, toContinuousMap T hr ar x = f (toContinuousMap T (by linarith) u x))
    (har_norm : ‖ar‖ ≤ B₀) (b : CircleSobolev t F)
    (hb_coeff : ∀ n, b.coeff n = (2 * π * I * n / T : ℂ) • (inclusion htr ar).coeff n)
    (hb_norm : ‖b‖ ≤ Bd) :
    ∃ w : CircleSobolev s F,
      (∀ x, toContinuousMap T (by linarith) w x = f (toContinuousMap T (by linarith) u x)) ∧
        ‖w‖ ≤ √(2 * B₀ ^ 2 + 2 * (T / (2 * π)) ^ 2 * Bd ^ 2) := by
  have hs : 1 / 2 < s := by linarith
  let at_el : CircleSobolev t F := inclusion htr ar
  obtain ⟨c, hc_incl, hc_deriv⟩ := exists_inclusion_eq_and_derivative_eq T at_el b hb_coeff
  let w : CircleSobolev s F :=
    ⟨c.coeff, by simpa only [hts] using c.memℓp_weight_smul_coeff⟩
  have hw_incl : inclusion (by linarith : t ≤ s) w = at_el :=
    CircleSobolev.ext <| funext fun n ↦ by
      simpa only [coeff_inclusion] using congrArg (·.coeff n) hc_incl
  have hw_deriv : derivative T hts.le w = b :=
    CircleSobolev.ext <| funext fun n ↦ by
      simpa only [coeff_derivative] using congrArg (·.coeff n) hc_deriv
  have hw_eval (x : AddCircle T) :
      toContinuousMap T hs w x = f (toContinuousMap T hs u x) := by
    have heq : toContinuousMap T hs w =
        ⟨fun y ↦ f (toContinuousMap T hs u y),
          hf.comp_continuous (toContinuousMap T hs u).continuous huU⟩ :=
      (toContinuousMap_eq_iff T hs w _).2 fun n ↦ by
        have h1 : w.coeff n = ar.coeff n := by
          simpa [coeff_inclusion, at_el] using congrArg (·.coeff n) hw_incl
        rw [h1, ← fourierCoeff_toContinuousMap T hr ar n]
        exact congrArg (fun φ : AddCircle T → F ↦ fourierCoeff φ n)
          (funext fun x ↦ (har x).symm)
    exact congrArg (· x) heq
  have hat_norm : ‖at_el‖ ≤ B₀ := (norm_inclusion_le _ _).trans har_norm
  have hw_sq : ‖w‖ ^ 2 ≤ 2 * B₀ ^ 2 + 2 * (T / (2 * π)) ^ 2 * Bd ^ 2 := by
    calc ‖w‖ ^ 2
        ≤ 2 * ‖inclusion (by linarith : t ≤ s) w‖ ^ 2 +
            2 * (T / (2 * π)) ^ 2 * ‖derivative T hts.le w‖ ^ 2 :=
          norm_sq_le_of_derivative T hts w
      _ = 2 * ‖at_el‖ ^ 2 + 2 * (T / (2 * π)) ^ 2 * ‖b‖ ^ 2 := by rw [hw_incl, hw_deriv]
      _ ≤ 2 * B₀ ^ 2 + 2 * (T / (2 * π)) ^ 2 * Bd ^ 2 := by gcongr
  exact ⟨w, hw_eval, (Real.le_sqrt (norm_nonneg w) (by positivity)).2 hw_sq⟩

/-- Half-integer induction on `m : ℕ` proving Sobolev membership and uniform compact-range norm
bounds for `1/2 < s < (m + 2) / 2` under `ContDiffOn ℝ (m + 1) f U`, with `E` and `F` in a common
universe `u` so the inductive call on `E →L[ℝ] F` stays in `Type u`. -/
private theorem exists_toContinuousMap_eq_comp_and_norm_le_aux :
    ∀ (m : ℕ) {s : ℝ} (hs : 1 / 2 < s), s < (m + 2 : ℝ) / 2 →
      ∀ {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
        [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
        {U : Set E}, IsOpen U → ∀ {f : E → F},
        ContDiffOn ℝ ((m + 1 : ℕ) : ℕ∞ω) f U →
        ∀ {K : Set E}, IsCompact K → K ⊆ U → ∀ (R : ℝ), 0 ≤ R →
        ∃ B : ℝ, 0 ≤ B ∧ ∀ u : CircleSobolev s E,
          (∀ x, toContinuousMap T hs u x ∈ K) → ‖u‖ ≤ R →
            ∃ w : CircleSobolev s F,
              (∀ x, toContinuousMap T hs w x = f (toContinuousMap T hs u x)) ∧ ‖w‖ ≤ B
  | 0, s, hs, hsm, E, F, _, _, _, _, _, _, U, hU, f, hf, K, hK, hKU, R, hR =>
      exists_toContinuousMap_eq_comp_and_norm_le_base T hs (by norm_num at hsm; exact hsm)
        hU (by simpa using hf) hK hKU R hR
  | m + 1, s, hs, hsm, E, F, _, _, _, _, _, _, U, hU, f, hf, K, hK, hKU, R, hR => by
      by_cases hs_prev : s < (m + 2 : ℝ) / 2
      · exact exists_toContinuousMap_eq_comp_and_norm_le_aux m hs hs_prev hU
          (hf.of_le (by norm_cast; omega)) hK hKU R hR
      push Not at hs_prev
      push_cast at hsm
      have : (0 : ℝ) ≤ m := m.cast_nonneg
      have : FiniteDimensional ℝ E := Module.Finite.trans ℂ E
      have : FiniteDimensional ℂ (E →L[ℝ] F) :=
        ContinuousLinearMap.finiteDimensional_of_isScalarTower
      set t := s - 1 with ht_def
      have ht : 0 ≤ t := by linarith [ht_def]
      have hts_eq : t + 1 = s := sub_add_cancel s 1
      set r := (t + 1 / 2 + (m + 2 : ℝ) / 2) / 2 with hr_def
      have hr : 1 / 2 < r := by linarith [hr_def]
      have hrm : r < (m + 2 : ℝ) / 2 := by linarith [hr_def]
      have hrs : r < s := by linarith [hr_def]
      set r' := (t + 1 / 2 + r) / 2 with hr'_def
      have htr' : t + 1 / 2 < r' := by linarith [hr'_def]
      have hr'r : r' < r := by linarith [hr'_def]
      obtain ⟨δ, hδ, hK'U⟩ := hK.exists_cthickening_subset_open hU hKU
      obtain ⟨B₀, _, hIH₀⟩ := exists_toContinuousMap_eq_comp_and_norm_le_aux m hr hrm hU
        (hf.of_le (by norm_cast; omega)) hK hKU R hR
      obtain ⟨B₁, _, hIH₁⟩ := exists_toContinuousMap_eq_comp_and_norm_le_aux m hr hrm hU
        (hf.fderiv_of_isOpen hU (m := ((m + 1 : ℕ) : ℕ∞ω)) (by norm_cast))
        hK.cthickening hK'U (R + 1) (by positivity)
      let A := realConvolutionAsym ht htr' (.id ℝ (E →L[ℝ] F))
      have : 0 < T := hT.out
      set Bd := ‖A‖ * B₁ * (2 * π / T * R)
      refine ⟨√(2 * B₀ ^ 2 + 2 * (T / (2 * π)) ^ 2 * Bd ^ 2), Real.sqrt_nonneg _,
        fun u huK huR ↦ ?_⟩
      obtain ⟨ar, har, har_norm⟩ := hIH₀ (inclusion hrs.le u)
        (fun x ↦ by simpa [toContinuousMap_inclusion] using huK x)
        ((norm_inclusion_le _ _).trans huR)
      obtain ⟨gu, hgu, hgu_norm⟩ := hIH₁ (inclusion hrs.le u)
        (fun x ↦ Metric.self_subset_cthickening _
          (by simpa [toContinuousMap_inclusion] using huK x))
        ((norm_inclusion_le _ _).trans (by linarith))
      let b : CircleSobolev t F := A (inclusion hr'r.le gu) (derivative T hts_eq.le u)
      have har_eq : (toContinuousMap T hr ar : AddCircle T → F) =
          fun x ↦ f (toContinuousMap T (by linarith) u x) :=
        funext fun x ↦ by simpa only [toContinuousMap_inclusion] using har x
      have hb_coeff (n : ℤ) :
          b.coeff n = (2 * π * I * n / T : ℂ) • (inclusion (by linarith : t ≤ r) ar).coeff n := by
        rw [coeff_inclusion, ← fourierCoeff_toContinuousMap T hr ar n, har_eq]
        exact coeff_realConvolutionAsym_eq_deriv_fourierCoeff T ht htr' hr'r hrs hts_eq
          hU hK.cthickening hK'U hδ Subset.rfl (hf.of_le (by norm_cast; omega)) hIH₁ huK huR
          (fun x ↦ by simpa only [toContinuousMap_inclusion] using hgu x) n
      have hb_norm : ‖b‖ ≤ Bd :=
        (A.le_opNorm₂ _ _).trans <| mul_le_mul
          (mul_le_mul_of_nonneg_left ((norm_inclusion_le _ _).trans hgu_norm) (norm_nonneg A))
          ((norm_derivative_le T _ u).trans (mul_le_mul_of_nonneg_left huR (by positivity)))
          (norm_nonneg _) (by positivity)
      exact exists_toContinuousMap_eq_and_norm_le_of_derivative_coeff T (by linarith) hr hrs
        hts_eq hf.continuousOn (fun x ↦ hKU (huK x)) ar
        (fun x ↦ by simpa only [toContinuousMap_inclusion] using har x) har_norm b hb_coeff hb_norm

private theorem exists_toContinuousMap_eq_comp_and_norm_le {s : ℝ} (hs : 1 / 2 < s)
    {E : Type u} {F : Type v} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    {U K : Set E} (hU : IsOpen U) {n : ℕ∞ω} {f : E → F} (hf : ContDiffOn ℝ n f U)
    (hn : (⌊2 * s⌋₊ : ℕ∞ω) ≤ n) (hK : IsCompact K) (hKU : K ⊆ U) (R : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ u : CircleSobolev s E,
      (∀ x, toContinuousMap T hs u x ∈ K) → ‖u‖ ≤ R →
        ∃ w : CircleSobolev s F,
          (∀ x, toContinuousMap T hs w x = f (toContinuousMap T hs u x)) ∧ ‖w‖ ≤ B := by
  have hfl_pos : 1 ≤ ⌊2 * s⌋₊ := Nat.floor_pos.2 (by linarith)
  set m := ⌊2 * s⌋₊ - 1
  have hm1 : m + 1 = ⌊2 * s⌋₊ := Nat.sub_add_cancel hfl_pos
  have hsm : s < (m + 2 : ℝ) / 2 := by
    have hlt : 2 * s < (⌊2 * s⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one (2 * s)
    have hcast : (m + 2 : ℝ) = (⌊2 * s⌋₊ : ℝ) + 1 := by exact_mod_cast congrArg (· + 1) hm1
    linarith
  let eF : F ≃L[ℂ] (ULift.{u} (Fin (Module.finrank ℂ F)) → ℂ) :=
    ((Module.finBasis ℂ F).reindex Equiv.ulift.symm).equivFun.toContinuousLinearEquiv
  let L := eF.symm.toContinuousLinearMap
  have hf' : ContDiffOn ℝ ((m + 1 : ℕ) : ℕ∞ω) (eF ∘ f) U :=
    (eF.toContinuousLinearMap.restrictScalars ℝ).contDiff.comp_contDiffOn
      (hf.of_le (hm1.symm ▸ hn))
  obtain ⟨B', hB', h⟩ := exists_toContinuousMap_eq_comp_and_norm_le_aux T m hs hsm hU hf'
    hK hKU (max R 0) (le_max_right _ _)
  refine ⟨‖L‖ * B', mul_nonneg (norm_nonneg L) hB', fun u huK huR ↦ ?_⟩
  obtain ⟨w', hw', hw'B⟩ := h u huK (huR.trans (le_max_left _ _))
  refine ⟨mapCLM L w', fun x ↦ ?_,
    (norm_mapCLM_le L w').trans (mul_le_mul_of_nonneg_left hw'B (norm_nonneg L))⟩
  rw [toContinuousMap_mapCLM_apply T hs L w' x, hw' x]
  exact eF.symm_apply_apply (f (toContinuousMap T hs u x))

variable {s : ℝ} [hs : Fact (1 / 2 < s)]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]

/-- **Smooth functions act on `H^s(E) → H^s(F)` for `s > 1/2`.** If `f : E → F` is `C^n` on an
open set `U ⊆ E` with `⌊2s⌋₊ ≤ n` (in particular if `f` is `C^∞`) and `u ∈ H^s(E)` takes values
in `U`, then the continuous representative of `nemytskii f u` is `f ∘ u`. -/
theorem toContinuousMap_nemytskii_of_contDiffOn {U : Set E} (hU : IsOpen U) {n : ℕ∞ω} {f : E → F}
    (hf : ContDiffOn ℝ n f U) {u : CircleSobolev s E}
    (hu : ∀ x, toContinuousMap T hs.out u x ∈ U)
    (hn : (⌊2 * s⌋₊ : ℕ∞ω) ≤ n := by simp) (x : AddCircle T) :
    toContinuousMap T hs.out (nemytskii f u) x = f (toContinuousMap T hs.out u x) := by
  set K := Set.range (toContinuousMap T hs.out u)
  obtain ⟨_, _, h⟩ := exists_toContinuousMap_eq_comp_and_norm_le T hs.out hU hf hn
    (isCompact_range (toContinuousMap T hs.out u).continuous) (Set.range_subset_iff.2 hu) ‖u‖
  obtain ⟨w, hw, -⟩ := h u (fun y ↦ ⟨y, rfl⟩) le_rfl
  rw [nemytskii_eq_of_forall_toContinuousMap_apply T hw, hw x]

/-- Global version of `toContinuousMap_nemytskii_of_contDiffOn` for `f : E → F` of class `C^n` on
all of `E` (`⌊2s⌋₊ ≤ n`). -/
theorem toContinuousMap_nemytskii_of_contDiff {n : ℕ∞ω} {f : E → F} (hf : ContDiff ℝ n f)
    (u : CircleSobolev s E) (hn : (⌊2 * s⌋₊ : ℕ∞ω) ≤ n := by simp) (x : AddCircle T) :
    toContinuousMap T hs.out (nemytskii f u) x = f (toContinuousMap T hs.out u x) :=
  toContinuousMap_nemytskii_of_contDiffOn T isOpen_univ hf.contDiffOn (fun _ ↦ mem_univ _) hn x

/-- **Uniform `H^s` norm bound on compact-range bounded subsets.** If `f : E → F` is `C^n` on an
open set `U` (`⌊2s⌋₊ ≤ n`) and `K ⊆ U` is compact, then `‖nemytskii f u‖` is uniformly bounded
over all `u ∈ H^s(E)` with `∀ x, u x ∈ K` and `‖u‖ ≤ R`. -/
theorem exists_norm_nemytskii_le_of_isCompact {U K : Set E} (hU : IsOpen U) {n : ℕ∞ω} {f : E → F}
    (hf : ContDiffOn ℝ n f U) (hK : IsCompact K) (hKU : K ⊆ U) (R : ℝ)
    (hn : (⌊2 * s⌋₊ : ℕ∞ω) ≤ n := by simp) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ u : CircleSobolev s E,
      (∀ x, toContinuousMap T hs.out u x ∈ K) → ‖u‖ ≤ R → ‖nemytskii f u‖ ≤ B := by
  obtain ⟨B, hB, h⟩ := exists_toContinuousMap_eq_comp_and_norm_le T hs.out hU hf hn hK hKU R
  refine ⟨B, hB, fun u huK huR ↦ ?_⟩
  obtain ⟨w, hw, hwB⟩ := h u huK huR
  rwa [nemytskii_eq_of_forall_toContinuousMap_apply T hw]

/-- `nemytskii f` commutes with the Sobolev inclusion `H^s(E) → H^t(E)` for `1/2 < t ≤ s`. -/
theorem nemytskii_inclusion_of_contDiffOn {t : ℝ} [ht : Fact (1 / 2 < t)] (hts : t ≤ s)
    {U : Set E} (hU : IsOpen U) {n : ℕ∞ω} {f : E → F} (hf : ContDiffOn ℝ n f U)
    {u : CircleSobolev s E} (hu : ∀ x, toContinuousMap T hs.out u x ∈ U)
    (hn : (⌊2 * s⌋₊ : ℕ∞ω) ≤ n := by simp) :
    nemytskii f (inclusion hts u) = inclusion hts (nemytskii f u) := by
  refine nemytskii_eq_of_forall_toContinuousMap_apply T fun x ↦ ?_
  rw [toContinuousMap_inclusion, toContinuousMap_inclusion,
    toContinuousMap_nemytskii_of_contDiffOn T hU hf hu hn x]

/-- **Functoriality of `nemytskii` under composition.** If `f : E → F` is `C^n` on an open set `U`
(`⌊2s⌋₊ ≤ n`), `g : F → G` is `C^m` on an open set `V` (`⌊2s⌋₊ ≤ m`), `f` maps `U` into `V`, and
`u ∈ H^s(E)` takes values in `U`, then `nemytskii (g ∘ f) u = nemytskii g (nemytskii f u)`. -/
theorem nemytskii_comp_of_contDiffOn {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    [FiniteDimensional ℂ G] {U : Set E} {V : Set F} (hU : IsOpen U) (hV : IsOpen V)
    {n m : ℕ∞ω} {f : E → F} {g : F → G} (hf : ContDiffOn ℝ n f U) (hg : ContDiffOn ℝ m g V)
    (hUV : MapsTo f U V) {u : CircleSobolev s E}
    (hu : ∀ x, toContinuousMap T hs.out u x ∈ U)
    (hn : (⌊2 * s⌋₊ : ℕ∞ω) ≤ n := by simp) (hm : (⌊2 * s⌋₊ : ℕ∞ω) ≤ m := by simp) :
    nemytskii (g ∘ f) u = nemytskii g (nemytskii f u) := by
  have hfu (x : AddCircle T) : toContinuousMap T hs.out (nemytskii f u) x ∈ V := by
    rw [toContinuousMap_nemytskii_of_contDiffOn T hU hf hu hn x]
    exact hUV (hu x)
  refine nemytskii_eq_of_forall_toContinuousMap_apply T fun x ↦ ?_
  rw [toContinuousMap_nemytskii_of_contDiffOn T hV hg hfu hm x,
    toContinuousMap_nemytskii_of_contDiffOn T hU hf hu hn x, Function.comp_apply]

/-- Global functoriality `nemytskii (g ∘ f) u = nemytskii g (nemytskii f u)` for `C^n` maps. -/
theorem nemytskii_comp_of_contDiff {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    [FiniteDimensional ℂ G] {n m : ℕ∞ω} {f : E → F} {g : F → G}
    (hf : ContDiff ℝ n f) (hg : ContDiff ℝ m g) (u : CircleSobolev s E)
    (hn : (⌊2 * s⌋₊ : ℕ∞ω) ≤ n := by simp) (hm : (⌊2 * s⌋₊ : ℕ∞ω) ≤ m := by simp) :
    nemytskii (g ∘ f) u = nemytskii g (nemytskii f u) := by
  have : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  exact nemytskii_comp_of_contDiffOn 1 isOpen_univ isOpen_univ hf.contDiffOn hg.contDiffOn
    (mapsTo_univ f _) (fun _ ↦ mem_univ _) hn hm

end Bootstrap

/-! ### Hadamard factorization, strict Fréchet differentiability, and `C^∞` smoothness -/

section Smoothness

/-- Pairs `(x, y) ∈ E × E` whose connecting segment `[x, y]` lies inside `U`. -/
private def segmentPreimage {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (U : Set E) :
    Set (E × E) :=
  {p : E × E | ∀ τ : unitInterval, p.1 + (τ : ℝ) • (p.2 - p.1) ∈ U}

private theorem isOpen_segmentPreimage {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} (hU : IsOpen U) : IsOpen (segmentPreimage U) :=
  isOpen_forall_prodMk_mem continuous_subtype_val
    (hU.preimage
      (by fun_prop : Continuous fun q : (E × E) × ℝ ↦ q.1.1 + q.2 • (q.1.2 - q.1.1)))

private theorem mem_segmentPreimage_diag {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} {x : E} (hx : x ∈ U) : (x, x) ∈ segmentPreimage U := fun _ ↦ by
  simpa using hx

private theorem contDiffOn_uncurry_hadamardFactor {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set E} (hU : IsOpen U) {m : ℕ} {f : E → F}
    (hf : ContDiffOn ℝ ((m + 1 : ℕ) : ℕ∞ω) f U) :
    ContDiffOn ℝ (m : ℕ∞ω) (Function.uncurry (hadamardFactor f)) (segmentPreimage U) := by
  have hseg : ContDiff ℝ (m : ℕ∞)
      (fun q : (E × E) × ℝ ↦ q.1.1 + q.2 • (q.1.2 - q.1.1)) := by fun_prop
  have hd : ContDiffOn ℝ (m : ℕ∞) (fderiv ℝ f) U := by
    exact_mod_cast hf.fderiv_of_isOpen hU (m := (m : ℕ∞ω)) (by norm_cast)
  have hint := contDiffOn_integral_smul_of_contDiffOn (μ := (volume : Measure unitInterval))
    (U := segmentPreimage U) (integrable_const (1 : ℝ)) continuous_subtype_val
    (hU.preimage
      (by fun_prop : Continuous fun q : (E × E) × ℝ ↦ q.1.1 + q.2 • (q.1.2 - q.1.1)))
    (hd.comp hseg.contDiffOn fun _ h ↦ h) fun p hp τ ↦ hp τ
  exact_mod_cast hint.congr fun ⟨x, y⟩ _ ↦ by
    change hadamardFactor f x y = _
    rw [congrFun (hadamardFactor_eq_integral_Icc f x) y, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le zero_le_one, intervalIntegral_eq_integral_unitInterval]
    simp only [Function.comp_apply, one_smul]

private theorem sub_eq_hadamardFactor_apply_of_contDiffOn {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {U : Set E} (hU : IsOpen U) {f : E → F} (hf : ContDiffOn ℝ 1 f U)
    {p : E × E} (hp : p ∈ segmentPreimage U) :
    f p.2 - f p.1 = hadamardFactor f p.1 p.2 (p.2 - p.1) := by
  have hTaylor := map_add_eq_sum_add_integral_iteratedFDeriv (n := 0) (f := f) (x := p.1)
    (y := p.2 - p.1) fun τ hτ ↦ hf.contDiffAt (hU.mem_nhds (hp ⟨τ, hτ⟩))
  have hInt : IntervalIntegrable
      (fun t : ℝ ↦ fderiv ℝ f (p.1 + t • (p.2 - p.1))) volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le zero_le_one]
    exact (hf.continuousOn_fderiv_of_isOpen hU le_rfl).comp
      (by fun_prop : Continuous fun t : ℝ ↦ p.1 + t • (p.2 - p.1)).continuousOn
      fun t ht ↦ hp ⟨t, ht⟩
  rw [congrFun (hadamardFactor_eq_integral_Icc f p.1) p.2, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le zero_le_one,
    ContinuousLinearMap.intervalIntegral_apply hInt (p.2 - p.1)]
  simpa [sub_eq_iff_eq_add, add_comm] using hTaylor

variable (T : ℝ) [hT : Fact (0 < T)] {s : ℝ} [hs : Fact (1 / 2 < s)]
  {E : Type u} {F : Type v} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]

/-- When the pointwise segment between `u₁ x` and `u₂ x` stays in `U`, the difference
`nemytskii f u₂ - nemytskii f u₁` factors through `nemytskii (uncurry (hadamardFactor f))` and
`realConvolution`. -/
private theorem nemytskii_sub_eq_realConvolution_hadamardFactor {U : Set E} (hU : IsOpen U)
    {n : ℕ∞ω} {f : E → F} (hf : ContDiffOn ℝ n f U)
    (u₁ u₂ : CircleSobolev s E) (hn : ((⌊2 * s⌋₊ + 1 : ℕ) : ℕ∞ω) ≤ n)
    (hseg : ∀ x, (toContinuousMap T hs.out u₁ x, toContinuousMap T hs.out u₂ x) ∈
      segmentPreimage U) :
    nemytskii f u₂ - nemytskii f u₁ =
      realConvolution hs.out (.id ℝ (E →L[ℝ] F))
        (nemytskii (Function.uncurry (hadamardFactor f)) (prodEquiv.symm (u₁, u₂)))
        (u₂ - u₁) := by
  have : FiniteDimensional ℝ E := Module.Finite.trans ℂ E
  have : FiniteDimensional ℂ (E →L[ℝ] F) := ContinuousLinearMap.finiteDimensional_of_isScalarTower
  have : FiniteDimensional ℂ (E × E) := inferInstance
  have hu₁ (x : AddCircle T) : toContinuousMap T hs.out u₁ x ∈ U := by
    simpa only [Subtype.coe_mk, zero_smul, add_zero] using hseg x ⟨0, unitInterval.zero_mem⟩
  have hu₂ (x : AddCircle T) : toContinuousMap T hs.out u₂ x ∈ U := by
    simpa only [Subtype.coe_mk, one_smul, add_sub_cancel] using hseg x ⟨1, unitInterval.one_mem⟩
  have hp12 (y : AddCircle T) :
      toContinuousMap T hs.out (prodEquiv.symm (u₁, u₂)) y ∈ segmentPreimage U := by
    rw [toContinuousMap_prodEquiv_symm_apply]
    exact hseg y
  have hn0 : (⌊2 * s⌋₊ : ℕ∞ω) ≤ n := le_trans (by norm_cast; omega) hn
  have hn1 : (1 : ℕ∞ω) ≤ n := le_trans (by norm_cast; omega) hn
  have hH : ContDiffOn ℝ (⌊2 * s⌋₊ : ℕ∞ω) (Function.uncurry (hadamardFactor f))
      (segmentPreimage U) :=
    contDiffOn_uncurry_hadamardFactor hU (hf.of_le hn)
  refine toContinuousMap_injective T hs.out <| ContinuousMap.ext fun x ↦ ?_
  rw [map_sub, ContinuousMap.sub_apply,
    toContinuousMap_nemytskii_of_contDiffOn T hU hf hu₂ hn0 x,
    toContinuousMap_nemytskii_of_contDiffOn T hU hf hu₁ hn0 x,
    toContinuousMap_realConvolution_apply,
    toContinuousMap_nemytskii_of_contDiffOn T (isOpen_segmentPreimage hU) hH hp12 le_rfl x,
    map_sub (toContinuousMap T hs.out) u₂ u₁, ContinuousMap.sub_apply]
  simp only [toContinuousMap_prodEquiv_symm_apply, Function.uncurry_apply_pair,
    ContinuousLinearMap.id_apply]
  exact sub_eq_hadamardFactor_apply_of_contDiffOn hU (hf.of_le hn1) (hseg x)

/-- At the diagonal `(u₀, u₀)`, `nemytskii (uncurry (hadamardFactor f))` agrees with
`nemytskii (fderiv ℝ f) u₀`. -/
private theorem nemytskii_hadamardFactor_diag {U : Set E} (hU : IsOpen U) {n : ℕ∞ω} {f : E → F}
    (hf : ContDiffOn ℝ n f U) (u₀ : CircleSobolev s E)
    (hn : ((⌊2 * s⌋₊ + 1 : ℕ) : ℕ∞ω) ≤ n)
    (hu₀ : ∀ x, toContinuousMap T hs.out u₀ x ∈ U) :
    nemytskii (Function.uncurry (hadamardFactor f)) (prodEquiv.symm (u₀, u₀)) =
      nemytskii (fderiv ℝ f) u₀ := by
  have : FiniteDimensional ℝ E := Module.Finite.trans ℂ E
  have : FiniteDimensional ℂ (E →L[ℝ] F) := ContinuousLinearMap.finiteDimensional_of_isScalarTower
  have hH : ContDiffOn ℝ (⌊2 * s⌋₊ : ℕ∞ω) (Function.uncurry (hadamardFactor f))
      (segmentPreimage U) :=
    contDiffOn_uncurry_hadamardFactor hU (hf.of_le hn)
  have hdf : ContDiffOn ℝ (⌊2 * s⌋₊ : ℕ∞ω) (fderiv ℝ f) U :=
    (hf.of_le hn).fderiv_of_isOpen hU (m := (⌊2 * s⌋₊ : ℕ∞ω)) (by norm_cast)
  have hp₀ (y : AddCircle T) :
      toContinuousMap T hs.out (prodEquiv.symm (u₀, u₀)) y ∈ segmentPreimage U := by
    rw [toContinuousMap_prodEquiv_symm_apply]
    exact mem_segmentPreimage_diag (hu₀ y)
  refine toContinuousMap_injective T hs.out <| ContinuousMap.ext fun x ↦ ?_
  rw [toContinuousMap_nemytskii_of_contDiffOn T (isOpen_segmentPreimage hU) hH hp₀ le_rfl x,
    toContinuousMap_nemytskii_of_contDiffOn T hU hdf hu₀ le_rfl x]
  simp only [toContinuousMap_prodEquiv_symm_apply, Function.uncurry_apply_pair,
    hadamardFactor_self]

private theorem exists_ball_prodEquiv_symm_mem_cthickening (u₀ : CircleSobolev s E)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ r : ℝ, 0 < r ∧ ∀ ⦃u₁ u₂ : CircleSobolev s E⦄,
      u₁ ∈ Metric.ball u₀ r → u₂ ∈ Metric.ball u₀ r →
        (∀ x, toContinuousMap T hs.out (prodEquiv.symm (u₁, u₂)) x ∈
          Metric.cthickening δ (Set.range (toContinuousMap T hs.out (prodEquiv.symm (u₀, u₀))))) ∧
        ‖prodEquiv.symm (u₁, u₂)‖ ≤ ‖prodEquiv.symm (u₀, u₀)‖ + 1 := by
  let p₀ : CircleSobolev s (E × E) := prodEquiv.symm (u₀, u₀)
  let P : CircleSobolev s E × CircleSobolev s E →L[ℂ] CircleSobolev s (E × E) :=
    prodEquiv.symm.toContinuousLinearMap
  let E_ev : CircleSobolev s (E × E) →L[ℂ] C(AddCircle T, E × E) := toContinuousMap T hs.out
  set r := min (1 / (‖P‖ + 1)) (δ / (‖E_ev‖ * ‖P‖ + 1))
  have hr : 0 < r := lt_min (by positivity) (by positivity)
  refine ⟨r, hr, fun u₁ u₂ hu₁ hu₂ ↦ ?_⟩
  have hd_pair : ‖((u₁, u₂) - (u₀, u₀) : CircleSobolev s E × CircleSobolev s E)‖ ≤ r := by
    rw [Prod.norm_def]
    exact max_le (by simpa [dist_eq_norm] using (Metric.mem_ball.1 hu₁).le)
      (by simpa [dist_eq_norm] using (Metric.mem_ball.1 hu₂).le)
  have hdP : ‖prodEquiv.symm (u₁, u₂) - p₀‖ ≤ ‖P‖ * r := by
    rw [show prodEquiv.symm (u₁, u₂) - p₀ = P ((u₁, u₂) - (u₀, u₀)) from
      (prodEquiv.symm.map_sub (u₁, u₂) (u₀, u₀)).symm]
    exact (P.le_opNorm _).trans (mul_le_mul_of_nonneg_left hd_pair (norm_nonneg P))
  have hPr1 : ‖P‖ * r ≤ 1 :=
    (mul_le_mul (by linarith) (min_le_left _ _) hr.le (by positivity)).trans_eq
      (mul_one_div_cancel (by positivity))
  have hEPδ : ‖E_ev‖ * (‖P‖ * r) ≤ δ := by
    rw [← mul_assoc]
    exact (mul_le_mul (by linarith) (min_le_right _ _) hr.le (by positivity)).trans_eq
      (mul_div_cancel₀ δ (by positivity))
  refine ⟨fun x ↦ Metric.mem_cthickening_of_dist_le _ _ δ _ ⟨x, rfl⟩ ?_, ?_⟩
  · rw [dist_eq_norm, ← ContinuousMap.sub_apply, ← map_sub]
    exact ((E_ev (prodEquiv.symm (u₁, u₂) - p₀)).norm_coe_le_norm x).trans
      ((E_ev.le_opNorm _).trans ((mul_le_mul_of_nonneg_left hdP (norm_nonneg E_ev)).trans hEPδ))
  · linarith [norm_le_norm_sub_add (prodEquiv.symm (u₁, u₂)) p₀]

/-- **Local Lipschitz continuity of `nemytskii f`.** If `f : E → F` is `C^n` on an open set `U`
with `⌊2s⌋₊ + 1 ≤ n` and `u₀ ∈ H^s(E)` maps into `U`, then `nemytskii f` is Lipschitz on a ball
around `u₀` inside `{u ∈ H^s(E) | ∀ x, u x ∈ U}`. -/
theorem exists_lipschitzOnWith_nemytskii {U : Set E} (hU : IsOpen U) {n : ℕ∞ω} {f : E → F}
    (hf : ContDiffOn ℝ n f U) {u₀ : CircleSobolev s E}
    (hu₀ : ∀ x, toContinuousMap T hs.out u₀ x ∈ U)
    (hn : ((⌊2 * s⌋₊ + 1 : ℕ) : ℕ∞ω) ≤ n := by simp) :
    ∃ (r : ℝ) (L : ℝ≥0), 0 < r ∧
      Metric.ball u₀ r ⊆ {u : CircleSobolev s E | ∀ x, toContinuousMap T hs.out u x ∈ U} ∧
      LipschitzOnWith L (nemytskii (s := s) f) (Metric.ball u₀ r) := by
  have : FiniteDimensional ℝ E := Module.Finite.trans ℂ E
  have : FiniteDimensional ℂ (E →L[ℝ] F) := ContinuousLinearMap.finiteDimensional_of_isScalarTower
  let p₀ : CircleSobolev s (E × E) := prodEquiv.symm (u₀, u₀)
  set K₀ := Set.range (toContinuousMap T hs.out p₀)
  have hK₀ : IsCompact K₀ := isCompact_range (toContinuousMap T hs.out p₀).continuous
  have hK₀_sub : K₀ ⊆ segmentPreimage U := by
    rintro _ ⟨x, rfl⟩
    change toContinuousMap T hs.out (prodEquiv.symm (u₀, u₀)) x ∈ segmentPreimage U
    rw [toContinuousMap_prodEquiv_symm_apply]
    exact mem_segmentPreimage_diag (hu₀ x)
  obtain ⟨δ, hδ, hKδ_sub⟩ :=
    hK₀.exists_cthickening_subset_open (isOpen_segmentPreimage hU) hK₀_sub
  obtain ⟨B, hB, hB_bound⟩ :=
    exists_norm_nemytskii_le_of_isCompact T (isOpen_segmentPreimage hU)
      (contDiffOn_uncurry_hadamardFactor hU (hf.of_le hn))
      hK₀.cthickening hKδ_sub (‖p₀‖ + 1) le_rfl
  obtain ⟨r, hr, hmem_Kδ⟩ := exists_ball_prodEquiv_symm_mem_cthickening T u₀ hδ
  let A := realConvolution hs.out (.id ℝ (E →L[ℝ] F))
  refine ⟨r, ⟨‖A‖ * B, mul_nonneg (norm_nonneg A) hB⟩, hr, fun u hu x ↦ ?_,
    LipschitzOnWith.of_dist_le_mul fun u₁ hu₁ u₂ hu₂ ↦ ?_⟩
  · have hseg : (toContinuousMap T hs.out u x, toContinuousMap T hs.out u x) ∈ segmentPreimage U :=
      by simpa only [toContinuousMap_prodEquiv_symm_apply] using hKδ_sub ((hmem_Kδ hu hu).1 x)
    simpa only [Subtype.coe_mk, zero_smul, add_zero] using hseg ⟨0, unitInterval.zero_mem⟩
  · obtain ⟨hK12, hN12⟩ := hmem_Kδ hu₂ hu₁
    have hseg12 (x : AddCircle T) :
        (toContinuousMap T hs.out u₂ x, toContinuousMap T hs.out u₁ x) ∈ segmentPreimage U := by
      simpa only [toContinuousMap_prodEquiv_symm_apply] using hKδ_sub (hK12 x)
    rw [dist_eq_norm, dist_eq_norm,
      nemytskii_sub_eq_realConvolution_hadamardFactor T hU hf u₂ u₁ hn hseg12]
    exact (A.le_opNorm₂ _ _).trans <| mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hB_bound _ hK12 hN12) (norm_nonneg A)) (norm_nonneg _)

/-- **Continuity of `nemytskii f` on `H^s(E)`.** If `f : E → F` is `C^n` on an open set `U` with
`⌊2s⌋₊ + 1 ≤ n`, then `nemytskii f` is continuous on `{u ∈ H^s(E) | ∀ x, u x ∈ U}`. -/
theorem continuousOn_nemytskii {U : Set E} (hU : IsOpen U) {n : ℕ∞ω} {f : E → F}
    (hf : ContDiffOn ℝ n f U) (hn : ((⌊2 * s⌋₊ + 1 : ℕ) : ℕ∞ω) ≤ n := by simp) :
    ContinuousOn (nemytskii (s := s) f)
      {u : CircleSobolev s E | ∀ x, toContinuousMap T hs.out u x ∈ U} := by
  intro u₀ hu₀
  obtain ⟨r, _, hr, _, hLip⟩ := exists_lipschitzOnWith_nemytskii T hU hf hu₀ hn
  exact (hLip.continuousOn.continuousAt (Metric.ball_mem_nhds u₀ hr)).continuousWithinAt

/-- Global version of `continuousOn_nemytskii` for `f : E → F` of class `C^n`
(`⌊2s⌋₊ + 1 ≤ n`). -/
theorem continuous_nemytskii {n : ℕ∞ω} {f : E → F} (hf : ContDiff ℝ n f)
    (hn : ((⌊2 * s⌋₊ + 1 : ℕ) : ℕ∞ω) ≤ n := by simp) :
    Continuous (nemytskii (s := s) f) := by
  have : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  exact continuousOn_univ.1
    ((continuousOn_nemytskii 1 isOpen_univ hf.contDiffOn hn).mono fun _ _ _ ↦ mem_univ _)

/-- **Strict Fréchet derivative of `nemytskii f`.** If `f : E → F` is `C^n` on an open set `U`
with `⌊2s⌋₊ + 2 ≤ n` (in particular if `f` is `C^∞`) and `u₀ ∈ H^s(E)` takes values in `U`, then
`nemytskii f` is strictly Fréchet differentiable at `u₀`, with derivative
`v ↦ realConvolution hs.out (.id ℝ (E →L[ℝ] F)) (nemytskii (fderiv ℝ f) u₀) v`. -/
theorem hasStrictFDerivAt_nemytskii_of_contDiffOn {U : Set E} (hU : IsOpen U) {n : ℕ∞ω}
    {f : E → F} (hf : ContDiffOn ℝ n f U) {u₀ : CircleSobolev s E}
    (hu₀ : ∀ x, toContinuousMap T hs.out u₀ x ∈ U)
    (hn : ((⌊2 * s⌋₊ + 2 : ℕ) : ℕ∞ω) ≤ n := by simp) :
    HasStrictFDerivAt (nemytskii (s := s) f)
      (realConvolution hs.out (.id ℝ (E →L[ℝ] F)) (nemytskii (fderiv ℝ f) u₀)) u₀ := by
  have : FiniteDimensional ℝ E := Module.Finite.trans ℂ E
  have : FiniteDimensional ℂ (E →L[ℝ] F) := ContinuousLinearMap.finiteDimensional_of_isScalarTower
  let H := Function.uncurry (hadamardFactor f)
  let A := realConvolution hs.out (.id ℝ (E →L[ℝ] F))
  let p₀ : CircleSobolev s (E × E) := prodEquiv.symm (u₀, u₀)
  let ΩH : Set (CircleSobolev s (E × E)) :=
    {w | ∀ x, toContinuousMap T hs.out w x ∈ segmentPreimage U}
  have hΩH_open : IsOpen ΩH :=
    isOpen_setOf_forall_toContinuousMap_mem T hs.out (isOpen_segmentPreimage hU)
  have hp₀_mem : p₀ ∈ ΩH := fun x ↦ by
    change toContinuousMap T hs.out (prodEquiv.symm (u₀, u₀)) x ∈ segmentPreimage U
    rw [toContinuousMap_prodEquiv_symm_apply]
    exact mem_segmentPreimage_diag (hu₀ x)
  have hswap : Continuous (fun q : CircleSobolev s E × CircleSobolev s E ↦
      prodEquiv.symm (q.2, q.1)) :=
    prodEquiv.symm.continuous.comp (continuous_snd.prodMk continuous_fst)
  have hH_contAt : ContinuousAt (nemytskii (s := s) H) p₀ :=
    (continuousOn_nemytskii T (isOpen_segmentPreimage hU)
      (contDiffOn_uncurry_hadamardFactor hU (hf.of_le hn)) le_rfl).continuousAt
      (hΩH_open.mem_nhds hp₀_mem)
  have hdiff_tendsto : Tendsto
      (fun q : CircleSobolev s E × CircleSobolev s E ↦
        ‖A‖ * ‖nemytskii H (prodEquiv.symm (q.2, q.1)) - nemytskii H p₀‖)
      (𝓝 (u₀, u₀)) (𝓝 0) := by
    simpa using (tendsto_sub_nhds_zero_iff.2
      (hH_contAt.tendsto.comp (hswap.tendsto (u₀, u₀)))).norm.const_mul ‖A‖
  rw [hasStrictFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  filter_upwards [hswap.tendsto (u₀, u₀) (hΩH_open.mem_nhds hp₀_mem),
    (tendsto_order.1 hdiff_tendsto).2 c hc] with ⟨u₁, u₂⟩ hseg hc_lt
  have hseg21 (x : AddCircle T) :
      (toContinuousMap T hs.out u₂ x, toContinuousMap T hs.out u₁ x) ∈ segmentPreimage U := by
    simpa only [toContinuousMap_prodEquiv_symm_apply] using hseg x
  have hn1 : ((⌊2 * s⌋₊ + 1 : ℕ) : ℕ∞ω) ≤ n := le_trans (by norm_cast; omega) hn
  dsimp only
  rw [nemytskii_sub_eq_realConvolution_hadamardFactor T hU hf u₂ u₁ hn1 hseg21,
    ← nemytskii_hadamardFactor_diag T hU hf u₀ hn1 hu₀, ← sub_apply, ← map_sub]
  exact (A.le_opNorm₂ _ _).trans (mul_le_mul_of_nonneg_right hc_lt.le (norm_nonneg _))

/-- Global version of `hasStrictFDerivAt_nemytskii_of_contDiffOn` for `f : E → F` of class `C^n`
(`⌊2s⌋₊ + 2 ≤ n`). -/
theorem hasStrictFDerivAt_nemytskii {n : ℕ∞ω} {f : E → F} (hf : ContDiff ℝ n f)
    (u : CircleSobolev s E) (hn : ((⌊2 * s⌋₊ + 2 : ℕ) : ℕ∞ω) ≤ n := by simp) :
    HasStrictFDerivAt (nemytskii (s := s) f)
      (realConvolution hs.out (.id ℝ (E →L[ℝ] F)) (nemytskii (fderiv ℝ f) u)) u := by
  have : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  exact hasStrictFDerivAt_nemytskii_of_contDiffOn 1 isOpen_univ hf.contDiffOn
    (fun _ ↦ mem_univ _) hn

/-- **Fréchet derivative of `nemytskii f` on an open set.** -/
theorem hasFDerivAt_nemytskii_of_contDiffOn {U : Set E} (hU : IsOpen U) {n : ℕ∞ω} {f : E → F}
    (hf : ContDiffOn ℝ n f U) {u : CircleSobolev s E}
    (hu : ∀ x, toContinuousMap T hs.out u x ∈ U)
    (hn : ((⌊2 * s⌋₊ + 2 : ℕ) : ℕ∞ω) ≤ n := by simp) :
    HasFDerivAt (nemytskii (s := s) f)
      (realConvolution hs.out (.id ℝ (E →L[ℝ] F)) (nemytskii (fderiv ℝ f) u)) u :=
  (hasStrictFDerivAt_nemytskii_of_contDiffOn T hU hf hu hn).hasFDerivAt

/-- Global Fréchet derivative of `nemytskii f`. -/
theorem hasFDerivAt_nemytskii_of_contDiff {n : ℕ∞ω} {f : E → F} (hf : ContDiff ℝ n f)
    (u : CircleSobolev s E) (hn : ((⌊2 * s⌋₊ + 2 : ℕ) : ℕ∞ω) ≤ n := by simp) :
    HasFDerivAt (nemytskii (s := s) f)
      (realConvolution hs.out (.id ℝ (E →L[ℝ] F)) (nemytskii (fderiv ℝ f) u)) u :=
  (hasStrictFDerivAt_nemytskii hf u hn).hasFDerivAt

/-- Formula for `fderiv ℝ (nemytskii f) u` when `u` takes values in an open set `U` where `f` is
`C^n` (`⌊2s⌋₊ + 2 ≤ n`). -/
theorem fderiv_nemytskii_of_contDiffOn {U : Set E} (hU : IsOpen U) {n : ℕ∞ω} {f : E → F}
    (hf : ContDiffOn ℝ n f U) {u : CircleSobolev s E}
    (hu : ∀ x, toContinuousMap T hs.out u x ∈ U)
    (hn : ((⌊2 * s⌋₊ + 2 : ℕ) : ℕ∞ω) ≤ n := by simp) :
    fderiv ℝ (nemytskii (s := s) f) u =
      realConvolution hs.out (.id ℝ (E →L[ℝ] F)) (nemytskii (fderiv ℝ f) u) :=
  (hasFDerivAt_nemytskii_of_contDiffOn T hU hf hu hn).fderiv

/-- Global formula for `fderiv ℝ (nemytskii f) u`. -/
theorem fderiv_nemytskii_of_contDiff {n : ℕ∞ω} {f : E → F} (hf : ContDiff ℝ n f)
    (u : CircleSobolev s E) (hn : ((⌊2 * s⌋₊ + 2 : ℕ) : ℕ∞ω) ≤ n := by simp) :
    fderiv ℝ (nemytskii (s := s) f) u =
      realConvolution hs.out (.id ℝ (E →L[ℝ] F)) (nemytskii (fderiv ℝ f) u) :=
  (hasFDerivAt_nemytskii_of_contDiff hf u hn).fderiv

/-- Pointwise action of `fderiv ℝ (nemytskii f) u v` on continuous representatives: at every point
`x : AddCircle T`, `(d(nemytskii f)_u v)(x) = df_{u(x)}(v(x))`. -/
theorem toContinuousMap_fderiv_nemytskii_of_contDiffOn {U : Set E} (hU : IsOpen U) {n : ℕ∞ω}
    {f : E → F} (hf : ContDiffOn ℝ n f U) {u : CircleSobolev s E}
    (hu : ∀ x, toContinuousMap T hs.out u x ∈ U) (v : CircleSobolev s E)
    (hn : ((⌊2 * s⌋₊ + 2 : ℕ) : ℕ∞ω) ≤ n := by simp) (x : AddCircle T) :
    toContinuousMap T hs.out (fderiv ℝ (nemytskii (s := s) f) u v) x =
      fderiv ℝ f (toContinuousMap T hs.out u x) (toContinuousMap T hs.out v x) := by
  have : FiniteDimensional ℝ E := Module.Finite.trans ℂ E
  have : FiniteDimensional ℂ (E →L[ℝ] F) := ContinuousLinearMap.finiteDimensional_of_isScalarTower
  have hn1 : ((⌊2 * s⌋₊ + 1 : ℕ) : ℕ∞ω) ≤ n := le_trans (by norm_cast; omega) hn
  have hdf : ContDiffOn ℝ (⌊2 * s⌋₊ : ℕ∞ω) (fderiv ℝ f) U :=
    (hf.of_le hn1).fderiv_of_isOpen hU (m := (⌊2 * s⌋₊ : ℕ∞ω)) (by norm_cast)
  rw [fderiv_nemytskii_of_contDiffOn T hU hf hu hn, toContinuousMap_realConvolution_apply,
    ContinuousLinearMap.id_apply, toContinuousMap_nemytskii_of_contDiffOn T hU hdf hu le_rfl x]

/-- Global pointwise action of `fderiv ℝ (nemytskii f) u v` on continuous representatives. -/
theorem toContinuousMap_fderiv_nemytskii_of_contDiff {n : ℕ∞ω} {f : E → F} (hf : ContDiff ℝ n f)
    (u v : CircleSobolev s E) (hn : ((⌊2 * s⌋₊ + 2 : ℕ) : ℕ∞ω) ≤ n := by simp) (x : AddCircle T) :
    toContinuousMap T hs.out (fderiv ℝ (nemytskii (s := s) f) u v) x =
      fderiv ℝ f (toContinuousMap T hs.out u x) (toContinuousMap T hs.out v x) :=
  toContinuousMap_fderiv_nemytskii_of_contDiffOn T isOpen_univ hf.contDiffOn
    (fun _ ↦ mem_univ _) v hn x

private theorem contDiffOn_nemytskii_nat_aux :
    ∀ (k : ℕ) {F' : Type u} [NormedAddCommGroup F'] [NormedSpace ℂ F'] [FiniteDimensional ℂ F']
      {U : Set E} (_hU : IsOpen U) {n : ℕ∞ω} {f : E → F'} (_hf : ContDiffOn ℝ n f U)
      (_hn : ((⌊2 * s⌋₊ + 1 + k : ℕ) : ℕ∞ω) ≤ n),
      ContDiffOn ℝ (k : ℕ∞ω) (nemytskii (s := s) f)
        {u : CircleSobolev s E | ∀ x, toContinuousMap T hs.out u x ∈ U}
  | 0, F', _, _, _, U, hU, _, f, hf, hn =>
      contDiffOn_zero.2 (continuousOn_nemytskii T hU hf (by simpa using hn))
  | k + 1, F', _, _, _, U, hU, n, f, hf, hn => by
      have : FiniteDimensional ℝ E := Module.Finite.trans ℂ E
      have : FiniteDimensional ℂ (E →L[ℝ] F') :=
        ContinuousLinearMap.finiteDimensional_of_isScalarTower
      let Ω := {u : CircleSobolev s E | ∀ x, toContinuousMap T hs.out u x ∈ U}
      have hΩ : IsOpen Ω := isOpen_setOf_forall_toContinuousMap_mem T hs.out hU
      have hn2 : ((⌊2 * s⌋₊ + 2 : ℕ) : ℕ∞ω) ≤ n := le_trans (by norm_cast; omega) hn
      push_cast
      refine (contDiffOn_succ_iff_fderiv_of_isOpen hΩ).2 ⟨fun u hu ↦
        (hasFDerivAt_nemytskii_of_contDiffOn T hU hf hu hn2).differentiableAt
          |>.differentiableWithinAt,
        by simp, ?_⟩
      have hdf : ContDiffOn ℝ ((⌊2 * s⌋₊ + 1 + k : ℕ) : ℕ∞ω) (fderiv ℝ f) U :=
        (hf.of_le hn).fderiv_of_isOpen hU (m := ((⌊2 * s⌋₊ + 1 + k : ℕ) : ℕ∞ω)) (by norm_cast)
      have hcomp : ContDiffOn ℝ (k : ℕ∞ω)
          (fun u ↦
            realConvolution hs.out (.id ℝ (E →L[ℝ] F')) (nemytskii (fderiv ℝ f) u)) Ω :=
        (realConvolution hs.out (.id ℝ (E →L[ℝ] F'))).contDiff.comp_contDiffOn
          (contDiffOn_nemytskii_nat_aux k hU hdf le_rfl)
      exact hcomp.congr fun u hu ↦ fderiv_nemytskii_of_contDiffOn T hU hf hu hn2

/-- **`C^k` regularity of `nemytskii f` on `H^s(E)`.** If `f : E → F` is `C^n` on an open set `U`
with `⌊2s⌋₊ + 1 + k ≤ n`, then `nemytskii f` is `C^k` on `{u ∈ H^s(E) | ∀ x, u x ∈ U}`. -/
theorem contDiffOn_nemytskii_nat (k : ℕ) {U : Set E} (hU : IsOpen U) {n : ℕ∞ω} {f : E → F}
    (hf : ContDiffOn ℝ n f U) (hn : ((⌊2 * s⌋₊ + 1 + k : ℕ) : ℕ∞ω) ≤ n := by simp) :
    ContDiffOn ℝ (k : ℕ∞ω) (nemytskii (s := s) f)
      {u : CircleSobolev s E | ∀ x, toContinuousMap T hs.out u x ∈ U} := by
  let eF : F ≃L[ℂ] (ULift.{u} (Fin (Module.finrank ℂ F)) → ℂ) :=
    ((Module.finBasis ℂ F).reindex Equiv.ulift.symm).equivFun.toContinuousLinearEquiv
  let L := eF.symm.toContinuousLinearMap
  have hf' : ContDiffOn ℝ n (eF ∘ f) U :=
    (eF.toContinuousLinearMap.restrictScalars ℝ).contDiff.comp_contDiffOn hf
  have hn0 : (⌊2 * s⌋₊ : ℕ∞ω) ≤ n := le_trans (by norm_cast; omega) hn
  refine (((mapCLM (s := s) L).restrictScalars ℝ).contDiff.comp_contDiffOn
    (contDiffOn_nemytskii_nat_aux T k hU hf' hn)).congr fun u hu ↦ ?_
  refine nemytskii_eq_of_forall_toContinuousMap_apply T fun x ↦ ?_
  rw [Function.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    toContinuousMap_mapCLM_apply T hs.out L _ x,
    toContinuousMap_nemytskii_of_contDiffOn T hU hf' hu hn0 x]
  exact eF.symm_apply_apply (f (toContinuousMap T hs.out u x))

/-- Global `C^k` regularity of `nemytskii f` when `f : E → F` is `C^n` (`⌊2s⌋₊ + 1 + k ≤ n`). -/
theorem contDiff_nemytskii_nat (k : ℕ) {n : ℕ∞ω} {f : E → F} (hf : ContDiff ℝ n f)
    (hn : ((⌊2 * s⌋₊ + 1 + k : ℕ) : ℕ∞ω) ≤ n := by simp) :
    ContDiff ℝ (k : ℕ∞ω) (nemytskii (s := s) f) := by
  have : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  exact contDiffOn_univ.1
    ((contDiffOn_nemytskii_nat 1 k isOpen_univ hf.contDiffOn hn).mono fun _ _ _ ↦ mem_univ _)

/-- **`C^∞` smoothness of `nemytskii f` on open subsets of `H^s(E)`.** If `f : E → F` is smooth
on an open set `U ⊆ E`, then `u ↦ nemytskii f u` is smooth (`ContDiffOn ℝ ∞`) on the open subset
`{u ∈ H^s(E) | ∀ x, u x ∈ U}` for every `s > 1/2`. -/
theorem contDiffOn_nemytskii {U : Set E} (hU : IsOpen U) {f : E → F}
    (hf : ContDiffOn ℝ ∞ f U) :
    ContDiffOn ℝ ∞ (nemytskii (s := s) f)
      {u : CircleSobolev s E | ∀ x, toContinuousMap T hs.out u x ∈ U} :=
  contDiffOn_infty.2 fun k ↦ contDiffOn_nemytskii_nat T k hU hf (by simp)

/-- **Global `C^∞` smoothness of `nemytskii f` on `H^s(E)`.** If `f : E → F` is smooth on `E`,
then `u ↦ nemytskii f u` is smooth (`ContDiff ℝ ∞`) on `H^s(E)` for every `s > 1/2`. -/
theorem contDiff_nemytskii {f : E → F} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (nemytskii (s := s) f) :=
  contDiff_infty.2 fun k ↦ contDiff_nemytskii_nat k hf (by simp)

end Smoothness

end CircleSobolev

end TauCeti
