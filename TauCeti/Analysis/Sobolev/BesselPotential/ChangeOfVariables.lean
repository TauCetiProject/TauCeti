/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TemperedDistribution.ChangeOfVariables
public import TauCeti.Analysis.Sobolev.BesselPotential.Basic
public import TauCeti.Analysis.Sobolev.BesselPotential.Extension
public import TauCeti.Analysis.Sobolev.BesselPotential.Schwartz
public import TauCeti.Analysis.Sobolev.Wkp.ChangeOfVariables
import Mathlib.Analysis.Normed.Operator.Extend
import TauCeti.Analysis.Sobolev.BesselPotential.ComplexInterpolation
import TauCeti.Analysis.Sobolev.BesselPotential.Duality
import TauCeti.Analysis.Sobolev.BesselPotential.Inclusion
import TauCeti.Analysis.Sobolev.BesselPotential.SmoothMultiplier
import TauCeti.MeasureTheory.Function.Jacobian.Equiv
import TauCeti.MeasureTheory.Function.Lp.CastMeasure

/-!
# Changes of variables in Bessel-potential spaces

## Integer orders, `1 < p < ∞`

For `1 < p < ∞` and a natural order `k`, the real Bessel-potential functions
`TemperedDistribution.realSobolevFunctions E k p` are preserved by precomposition with a change of
variables of order `k` of the whole space (`TauCeti.Wkp.IsChangeOfVariables`): a `Cᵏ`
injective map with bounded derivatives of orders `1` through `k` and Jacobian determinant bounded
away from zero. In particular they are invariant under translations and under linear
automorphisms of `E`. The proof passes through the weak-derivative Sobolev space `W^{k,p}(E)`,
which has the same real elements by Calderón's theorem
(`MeasureTheory.Lp.memSobolev_natCast_iff_exists_wkp_value_eq`), and on which precomposition is
the bounded operator `TauCeti.Wkp.compL`.

## Every real order, `p = 2`

Let `φ` be a bijection of `E` such that `φ` and `φ⁻¹` have temperate growth and bounded
derivatives of every positive order, for instance an affine automorphism. The pullback of tempered
distributions `TemperedDistribution.compCLM` along `φ` preserves the Hilbert-space-valued
Bessel-potential space `H^s = H^{s,2}` for every real `s`, negative orders included
(`TemperedDistribution.MemSobolev.compCLM`), and restricts to a continuous linear automorphism of
`H^s` with inverse the pullback along `φ⁻¹` (`BesselPotentialSpace.compEquiv`). This is the
whole-space coordinate-change estimate behind the localization of the Sobolev scale to charts.

The bound `‖u ∘ φ‖_{H^s} ≤ C ‖u‖_{H^s}` is first proved on Schwartz functions
(`SchwartzMap.exists_norm_toBesselPotentialSpaceCLM_compCLM_le`), in three steps.

* **Nonnegative integer orders**, by induction. At order `0` it is the change of variables formula
  with the bound on `|det Dφ⁻¹|` (`TauCeti.integral_comp_equiv_le_mul_integral`). Raising the order
  by one adds the first derivatives, `‖v‖²_{H^{k+1}} = ‖v‖²_{H^k} + (2π)⁻² ∑ᵢ ‖∂ᵢ v‖²_{H^k}`
  (`SchwartzMap.norm_toBesselPotentialSpaceCLM_add_one_sq`), and by the chain rule
  `∂ᵢ (u ∘ φ) = ∑ⱼ ⟪bⱼ, Dφ bᵢ⟫ (∂ⱼ u) ∘ φ` (`SchwartzMap.lineDerivOp_compCLM`), whose coefficients
  are bounded multipliers on `H^k`
  (`SchwartzMap.exists_norm_toBesselPotentialSpaceCLM_smulLeftCLM_le`).
* **Negative integer orders**, by duality. For the `L²` pairing the transpose of `u ↦ u ∘ φ` is the
  pushforward of densities `φ_* v = |det Dφ⁻¹| (v ∘ φ⁻¹)` (`SchwartzMap.integral_inner_compCLM_eq`),
  which is bounded on `H^k` by the previous step applied to `φ⁻¹` and the multiplier bound for the
  Jacobian factor. The `H^{-k}` norm is computed by testing against `H^k`
  (`SchwartzMap.norm_toBesselPotentialSpaceCLM_neg_le_of_forall`).
* **Real orders**, by complex interpolation of the Hilbert scale between `⌊s⌋` and `⌊s⌋ + 1`
  (`SchwartzMap.norm_toBesselPotentialSpaceCLM_le_rpow_mul_rpow_mul_norm`).

Density of Schwartz functions then extends the bound to `H^s`, and the extension agrees with the
pullback of tempered distributions.

## Main results

* `TemperedDistribution.comp_mem_realSobolevFunctions_natCast`: precomposition with a change of
  variables of order `k` preserves the real elements of `H^{k,p}`.
* `TemperedDistribution.comp_add_mem_realSobolevFunctions_natCast`: translations.
* `TemperedDistribution.comp_continuousLinearEquiv_mem_realSobolevFunctions_natCast`: linear
  automorphisms.
* `SchwartzMap.exists_norm_toBesselPotentialSpaceCLM_compCLM_le`: the bound
  `‖u ∘ φ‖_{H^s} ≤ C ‖u‖_{H^s}` on Schwartz functions, for every real `s`.
* `TemperedDistribution.MemSobolev.compCLM`: the pullback preserves `H^s`.
* `BesselPotentialSpace.compCLM`, `BesselPotentialSpace.compEquiv`: the pullback as a bounded
  operator and as a continuous linear automorphism of `H^s`.
* `SchwartzMap.hasSobolevExtension_compCLM`: composition with `φ` on Schwartz functions extends to
  `H^s → H^s`, in the form `SchwartzMap.HasSobolevExtension` used for composing Sobolev estimates.

## References

* M. E. Taylor, *Partial Differential Equations I*, 2nd ed., Springer, 2011, Chapter 4, §1
  (invariance of `H^s` under diffeomorphisms, via integer orders, duality and interpolation).
* J. Bergh and J. Löfström, *Interpolation Spaces: An Introduction*, Springer, 1976, §§4.1, 6.4.
-/

public section

noncomputable section

namespace TemperedDistribution

open MeasureTheory TauCeti TopologicalSpace
open scoped ENNReal

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Changes of variables in `H^{k,p}`.** For `1 < p < ∞` and a natural order `k`, precomposition
with a change of variables of order `k` of the whole space preserves the real Bessel-potential
functions of order `k`. -/
theorem comp_mem_realSobolevFunctions_natCast (hp : 1 < p) (hp_top : p ≠ ∞) {k : ℕ}
    {Φ : E → E} {L c : ℝ} (hΦ : Wkp.IsChangeOfVariables k ⊤ ⊤ Φ L c) {f : E → ℝ}
    (hf : f ∈ realSobolevFunctions E k p) :
    (fun x ↦ f (Φ x)) ∈ realSobolevFunctions E k p := by
  obtain ⟨u, huf, hu⟩ := mem_realSobolevFunctions.1 hf
  have hvolume : (volume : Measure E) = volume.restrict ((⊤ : Opens E) : Set E) := by simp
  -- Pass to `W^{k,p}`, precompose there with `Φ`, and return to `H^{k,p}`.
  obtain ⟨w, hw⟩ := (Lp.memSobolev_natCast_iff_exists_wkp_value_eq hp hp_top k u).1 hu
  set w' := Wkp.compL (mu := volume) hΦ hp_top w
  set u' : Lp ℝ p (volume : Measure E) := castLpₗᵢ (𝕜 := ℝ) hvolume.symm (Wkp.value k w')
  have hu' : (u' : E → ℝ) = Wkp.value k w' := funext (coeFn_castLpₗᵢ hvolume.symm _)
  refine mem_realSobolevFunctions.2 ⟨u', ?_,
    (Lp.memSobolev_natCast_iff_exists_wkp_value_eq hp hp_top k u').2
      ⟨w', .of_forall fun x ↦ by rw [hu']⟩⟩
  have hae : ae (volume.restrict ((⊤ : Opens E) : Set E)) = ae (volume : Measure E) := by
    rw [← hvolume]
  have hcomp := Wkp.value_compL_ae (mu := volume) hΦ hp_top w
  have hpull := hΦ.ae_comp (mu := volume) (P := fun y ↦ Wkp.value k w y = f y) <| by
    rw [hae]
    filter_upwards [hw, huf] with y h₁ h₂
    rw [h₁, h₂]
  rw [Filter.EventuallyEq, hae] at hcomp
  rw [hae] at hpull
  filter_upwards [hcomp, hpull] with x h₁ h₂
  rw [hu', h₁, h₂]

/-- For `1 < p < ∞` and a natural order `k`, the real Bessel-potential functions of order `k` are
invariant under translation. -/
theorem comp_add_mem_realSobolevFunctions_natCast (hp : 1 < p) (hp_top : p ≠ ∞) {k : ℕ}
    (a : E) {f : E → ℝ} (hf : f ∈ realSobolevFunctions E k p) :
    (fun x ↦ f (x + a)) ∈ realSobolevFunctions E k p :=
  comp_mem_realSobolevFunctions_natCast hp hp_top
    (Wkp.IsChangeOfVariables.add_const a (Set.mapsTo_univ _ _)) hf

/-- For `1 < p < ∞` and a natural order `k`, the real Bessel-potential functions of order `k` are
invariant under linear automorphisms of `E`. -/
theorem comp_continuousLinearEquiv_mem_realSobolevFunctions_natCast (hp : 1 < p)
    (hp_top : p ≠ ∞) {k : ℕ} (e : E ≃L[ℝ] E) {f : E → ℝ}
    (hf : f ∈ realSobolevFunctions E k p) :
    (fun x ↦ f (e x)) ∈ realSobolevFunctions E k p :=
  comp_mem_realSobolevFunctions_natCast hp hp_top
    (Wkp.IsChangeOfVariables.continuousLinearEquiv e (Set.mapsTo_univ _ _)) hf

end TemperedDistribution

namespace SchwartzMap

open MeasureTheory TemperedDistribution
open scoped BesselPotentialSpace InnerProductSpace RealInnerProductSpace LineDeriv

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F] {φ : E ≃ E}

/-- The induction step of `SchwartzMap.exists_norm_toBesselPotentialSpaceCLM_compCLM_le_natCast`:
a bound for `u ↦ u ∘ φ` on `H^k` gives one on `H^{k+1}`, through the chain rule and the
multiplier bounds for its coefficients. -/
private theorem exists_sq_bound_compCLM_succ
    (hφ : (φ : E → E).HasTemperateGrowth) (hψ : (φ.symm : E → E).HasTemperateGrowth)
    (hb : ∀ n, ∃ C, ∀ x, ‖iteratedFDeriv ℝ (n + 1) φ x‖ ≤ C) (k : ℕ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ u : 𝓢(E, F), ‖toBesselPotentialSpaceCLM k 2
        (compCLM ℂ hφ (hψ.exists_norm_le_of_leftInverse φ.left_inv) u)‖ ^ 2 ≤
      C * ‖toBesselPotentialSpaceCLM k 2 u‖ ^ 2) :
    ∃ C', 0 ≤ C' ∧ ∀ u : 𝓢(E, F), ‖toBesselPotentialSpaceCLM (k + 1 : ℕ) 2
        (compCLM ℂ hφ (hψ.exists_norm_le_of_leftInverse φ.left_inv) u)‖ ^ 2 ≤
      C' * ‖toBesselPotentialSpaceCLM (k + 1 : ℕ) 2 u‖ ^ 2 := by
  set P := compCLM ℂ (F := F) hφ (hψ.exists_norm_le_of_leftInverse φ.left_inv)
  let b := stdOrthonormalBasis ℝ E
  -- The coefficients of the chain rule are bounded multipliers on `H^k`.
  have hc (i j : Fin (Module.finrank ℝ E)) : ∃ c, 0 ≤ c ∧ ∀ w : 𝓢(E, F),
      ‖toBesselPotentialSpaceCLM k 2
        (smulLeftCLM F (fun x ↦ ((⟪b j, fderiv ℝ φ x (b i)⟫ : ℝ) : ℂ)) w)‖ ≤
        c * ‖toBesselPotentialSpaceCLM k 2 w‖ :=
    exists_norm_toBesselPotentialSpaceCLM_smulLeftCLM_le (by norm_num) ENNReal.ofNat_ne_top k
      (hφ.inner_fderiv_apply _ _)
      fun n _ ↦ hφ.exists_norm_iteratedFDeriv_inner_fderiv_apply_le hb _ _ n
  choose c _ hc using hc
  set K := ∑ i, ∑ j, c i j ^ 2
  refine ⟨C * (1 + K), by positivity, fun u ↦ ?_⟩
  have hd (i : Fin (Module.finrank ℝ E)) :
      ‖toBesselPotentialSpaceCLM k 2 (∂_{b i} (P u))‖ ^ 2 ≤
        (∑ j, c i j ^ 2) * (C * ∑ j, ‖toBesselPotentialSpaceCLM k 2 (∂_{b j} u)‖ ^ 2) := by
    rw [lineDerivOp_compCLM b, map_sum]
    have h1 : ‖∑ j, toBesselPotentialSpaceCLM k 2
        (smulLeftCLM F (fun x ↦ ((⟪b j, fderiv ℝ φ x (b i)⟫ : ℝ) : ℂ)) (P (∂_{b j} u)))‖ ≤
        ∑ j, c i j * ‖toBesselPotentialSpaceCLM k 2 (P (∂_{b j} u))‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ hc i j _)
    calc _ ≤ (∑ j, c i j * ‖toBesselPotentialSpaceCLM k 2 (P (∂_{b j} u))‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ (∑ j, c i j ^ 2) * ∑ j, ‖toBesselPotentialSpaceCLM k 2 (P (∂_{b j} u))‖ ^ 2 :=
          Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ ≤ (∑ j, c i j ^ 2) * (C * ∑ j, ‖toBesselPotentialSpaceCLM k 2 (∂_{b j} u)‖ ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [Finset.mul_sum]
          exact Finset.sum_le_sum fun j _ ↦ hC _
  have hsum : ∑ i, ‖toBesselPotentialSpaceCLM k 2 (∂_{b i} (P u))‖ ^ 2 ≤
      K * (C * ∑ j, ‖toBesselPotentialSpaceCLM k 2 (∂_{b j} u)‖ ^ 2) := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun i _ ↦ hd i
  -- Expand both sides with `‖v‖²_{H^{k+1}} = ‖v‖²_{H^k} + (2π)⁻² ∑ᵢ ‖∂ᵢ v‖²_{H^k}`.
  have hrec := norm_toBesselPotentialSpaceCLM_add_one_sq (F := F) b (k : ℝ)
  rw [Nat.cast_succ, hrec, hrec]
  set X := ‖toBesselPotentialSpaceCLM k 2 u‖ ^ 2
  set Y := ∑ j, ‖toBesselPotentialSpaceCLM k 2 (∂_{b j} u)‖ ^ 2
  set π' := (2 * Real.pi)⁻¹ ^ 2
  calc _ ≤ C * X + π' * (K * (C * Y)) := by gcongr; exact hC u
    _ ≤ C * X + π' * (K * (C * Y)) + (C * K * X + π' * (C * Y)) :=
        le_add_of_nonneg_right (by positivity)
    _ = C * (1 + K) * (X + π' * Y) := by ring

/-- **Changes of variables on `H^k`, on Schwartz functions.** Let `φ` be a bijection such that `φ`
and `φ⁻¹` have temperate growth, the derivatives of `φ` of positive order are bounded and
`|det Dφ⁻¹| ≤ M`. Then `‖u ∘ φ‖_{H^k} ≤ C ‖u‖_{H^k}` for every natural `k` and every Schwartz
function `u`, with `C` independent of `u`. -/
theorem exists_norm_toBesselPotentialSpaceCLM_compCLM_le_natCast
    (hφ : (φ : E → E).HasTemperateGrowth) (hψ : (φ.symm : E → E).HasTemperateGrowth)
    (hb : ∀ n, ∃ C, ∀ x, ‖iteratedFDeriv ℝ (n + 1) φ x‖ ≤ C) {M : ℝ}
    (hM : ∀ y, |(fderiv ℝ φ.symm y).det| ≤ M) (k : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ u : 𝓢(E, F),
      ‖toBesselPotentialSpaceCLM k 2 (compCLM ℂ hφ (hψ.exists_norm_le_of_leftInverse φ.left_inv) u)‖
        ≤ C * ‖toBesselPotentialSpaceCLM k 2 u‖ := by
  set P := compCLM ℂ (F := F) hφ (hψ.exists_norm_le_of_leftInverse φ.left_inv)
  -- It suffices to bound the squares of the norms.
  suffices h : ∃ C, 0 ≤ C ∧ ∀ u : 𝓢(E, F),
      ‖toBesselPotentialSpaceCLM k 2 (P u)‖ ^ 2 ≤ C * ‖toBesselPotentialSpaceCLM k 2 u‖ ^ 2 by
    obtain ⟨C, hC0, hC⟩ := h
    refine ⟨√C, Real.sqrt_nonneg _, fun u ↦ ?_⟩
    rw [← Real.sqrt_sq (norm_nonneg (toBesselPotentialSpaceCLM k 2 (P u))),
      ← Real.sqrt_sq (norm_nonneg (toBesselPotentialSpaceCLM k 2 u)), ← Real.sqrt_mul hC0]
    exact Real.sqrt_le_sqrt (hC u)
  induction k with
  | zero =>
    refine ⟨max M 0, le_max_right _ _, fun u ↦ ?_⟩
    rw [Nat.cast_zero, norm_toBesselPotentialSpaceCLM_zero_sq,
      norm_toBesselPotentialSpaceCLM_zero_sq]
    exact (TauCeti.integral_comp_equiv_le_mul_integral volume (hψ.1.differentiable (by simp)) hM
      (g := fun x ↦ ‖u x‖ ^ 2) (fun _ ↦ by positivity)
      ((u.memLp 2).integrable_norm_pow two_ne_zero)).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (integral_nonneg fun _ ↦ by positivity))
  | succ k ih =>
    obtain ⟨C, hC0, hC⟩ := ih
    exact exists_sq_bound_compCLM_succ hφ hψ hb k hC0 hC

/-- **Changes of variables on `H^{-k}`, on Schwartz functions.** If `φ` and `φ⁻¹` have temperate
growth and bounded derivatives of positive order, then `‖w ∘ φ‖_{H^{-k}} ≤ C ‖w‖_{H^{-k}}` for every
natural `k` and every Schwartz function `w`. By duality this is the bound of the pushforward
`φ_* v = |det Dφ⁻¹| (v ∘ φ⁻¹)` on `H^k`. -/
private theorem exists_norm_toBesselPotentialSpaceCLM_compCLM_le_neg_natCast
    (hφ : (φ : E → E).HasTemperateGrowth) (hψ : (φ.symm : E → E).HasTemperateGrowth)
    (hb : ∀ n, ∃ C, ∀ x, ‖iteratedFDeriv ℝ (n + 1) φ x‖ ≤ C)
    (hb' : ∀ n, ∃ C, ∀ x, ‖iteratedFDeriv ℝ (n + 1) φ.symm x‖ ≤ C) (k : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ w : 𝓢(E, F),
      ‖toBesselPotentialSpaceCLM (-k) 2
          (compCLM ℂ hφ (hψ.exists_norm_le_of_leftInverse φ.left_inv) w)‖ ≤
        C * ‖toBesselPotentialSpaceCLM (-k) 2 w‖ := by
  have hφ' : (φ.symm.symm : E → E).HasTemperateGrowth := by simpa using hφ
  set J : E → ℂ := fun y ↦ ((|(fderiv ℝ φ.symm y).det| : ℝ) : ℂ)
  have hJ : J.HasTemperateGrowth :=
    (RCLike.hasTemperateGrowth_ofReal ℂ).comp (hφ.abs_det_fderiv_symm hψ)
  -- The pushforward `φ_* v = J (v ∘ φ⁻¹)` is bounded on `H^k`.
  obtain ⟨M, hM⟩ := hψ.exists_norm_iteratedFDeriv_abs_det_fderiv_symm_le hφ' (by simpa using hb) 0
  have hM' (y : E) : |(fderiv ℝ φ.symm.symm y).det| ≤ M := by simpa using hM y
  obtain ⟨Cs, hCs0, hCs⟩ := exists_norm_toBesselPotentialSpaceCLM_compCLM_le_natCast (F := F)
    (φ := φ.symm) hψ hφ' hb' hM' k
  obtain ⟨CJ, hCJ0, hCJ⟩ := exists_norm_toBesselPotentialSpaceCLM_smulLeftCLM_le (F := F) (p := 2)
    (by norm_num) ENNReal.ofNat_ne_top k hJ fun n _ ↦
      hφ.exists_norm_iteratedFDeriv_abs_det_fderiv_symm_le hψ hb' n
  have hQ (v : 𝓢(E, F)) : ‖toBesselPotentialSpaceCLM k 2 (pushforwardCLM ℂ φ hφ hψ v)‖ ≤
      CJ * (Cs * ‖toBesselPotentialSpaceCLM k 2 v‖) := by
    have hv : pushforwardCLM ℂ φ hφ hψ v = smulLeftCLM F J
        (compCLM ℂ hψ (hφ'.exists_norm_le_of_leftInverse φ.symm.left_inv) v) := by
      ext y
      rw [pushforwardCLM_apply, smulLeftCLM_apply_apply hJ, compCLM_apply, Function.comp_apply]
      rfl
    rw [hv]
    exact (hCJ _).trans (mul_le_mul_of_nonneg_left (hCs v) hCJ0)
  -- Duality turns the bound of the transpose `φ_*` on `H^k` into the bound on `H^{-k}`.
  refine ⟨CJ * Cs, mul_nonneg hCJ0 hCs0, fun w ↦ ?_⟩
  refine norm_toBesselPotentialSpaceCLM_neg_le_of_forall (k : ℝ) _
    (mul_nonneg (mul_nonneg hCJ0 hCs0) (norm_nonneg _)) fun v ↦ ?_
  rw [integral_inner_compCLM_eq hφ hψ]
  calc _ ≤ ‖toBesselPotentialSpaceCLM (-k) 2 w‖ *
        ‖toBesselPotentialSpaceCLM k 2 (pushforwardCLM ℂ φ hφ hψ v)‖ :=
        norm_integral_inner_le_norm_toBesselPotentialSpaceCLM_mul_norm (k : ℝ) w _
    _ ≤ ‖toBesselPotentialSpaceCLM (-k) 2 w‖ *
        (CJ * (Cs * ‖toBesselPotentialSpaceCLM k 2 v‖)) :=
        mul_le_mul_of_nonneg_left (hQ v) (norm_nonneg _)
    _ = _ := by ring

/-- **Changes of variables on `H^m` for integer `m`, on Schwartz functions.** -/
private theorem exists_norm_toBesselPotentialSpaceCLM_compCLM_le_intCast
    (hφ : (φ : E → E).HasTemperateGrowth) (hψ : (φ.symm : E → E).HasTemperateGrowth)
    (hb : ∀ n, ∃ C, ∀ x, ‖iteratedFDeriv ℝ (n + 1) φ x‖ ≤ C)
    (hb' : ∀ n, ∃ C, ∀ x, ‖iteratedFDeriv ℝ (n + 1) φ.symm x‖ ≤ C) (m : ℤ) :
    ∃ C, 0 ≤ C ∧ ∀ u : 𝓢(E, F),
      ‖toBesselPotentialSpaceCLM m 2
          (compCLM ℂ hφ (hψ.exists_norm_le_of_leftInverse φ.left_inv) u)‖ ≤
        C * ‖toBesselPotentialSpaceCLM m 2 u‖ := by
  obtain ⟨k, rfl | rfl⟩ := m.eq_nat_or_neg
  · obtain ⟨M, hM⟩ := hφ.exists_norm_iteratedFDeriv_abs_det_fderiv_symm_le hψ hb' 0
    rw [Int.cast_natCast]
    exact exists_norm_toBesselPotentialSpaceCLM_compCLM_le_natCast (F := F) hφ hψ hb
      (M := M) (fun y ↦ by simpa using hM y) k
  · rw [Int.cast_neg, Int.cast_natCast]
    exact exists_norm_toBesselPotentialSpaceCLM_compCLM_le_neg_natCast (F := F) hφ hψ hb hb' k

/-- **Changes of variables on `H^s`, on Schwartz functions.** If `φ` and `φ⁻¹` have temperate
growth and bounded derivatives of every positive order, then `‖u ∘ φ‖_{H^s} ≤ C ‖u‖_{H^s}` for
every real `s` and every Schwartz function `u`, with `C` independent of `u`. Between consecutive
integers this is interpolation of the Hilbert scale. -/
theorem exists_norm_toBesselPotentialSpaceCLM_compCLM_le
    (hφ : (φ : E → E).HasTemperateGrowth) (hψ : (φ.symm : E → E).HasTemperateGrowth)
    (hb : ∀ n, ∃ C, ∀ x, ‖iteratedFDeriv ℝ (n + 1) φ x‖ ≤ C)
    (hb' : ∀ n, ∃ C, ∀ x, ‖iteratedFDeriv ℝ (n + 1) φ.symm x‖ ≤ C) (s : ℝ) :
    ∃ C, ∀ u : 𝓢(E, F),
      ‖toBesselPotentialSpaceCLM s 2
          (compCLM ℂ hφ (hψ.exists_norm_le_of_leftInverse φ.left_inv) u)‖ ≤
        C * ‖toBesselPotentialSpaceCLM s 2 u‖ := by
  set P := compCLM ℂ (F := F) hφ (hψ.exists_norm_le_of_leftInverse φ.left_inv)
  obtain ⟨C₀, hC₀0, hC₀⟩ := exists_norm_toBesselPotentialSpaceCLM_compCLM_le_intCast (F := F) hφ hψ
    hb hb' ⌊s⌋
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_norm_toBesselPotentialSpaceCLM_compCLM_le_intCast (F := F) hφ hψ
    hb hb' (⌊s⌋ + 1)
  have h₀ (u : 𝓢(E, F)) : ‖toBesselPotentialSpaceCLM (⌊s⌋ : ℝ) 2 ((P : 𝓢(E, F) →ₗ[ℂ] 𝓢(E, F)) u)‖
      ≤ C₀ * ‖toBesselPotentialSpaceCLM (⌊s⌋ : ℝ) 2 u‖ := by
    rw [ContinuousLinearMap.coe_coe]
    exact hC₀ u
  have h₁ (u : 𝓢(E, F)) :
      ‖toBesselPotentialSpaceCLM ((⌊s⌋ : ℝ) + 1) 2 ((P : 𝓢(E, F) →ₗ[ℂ] 𝓢(E, F)) u)‖ ≤
        C₁ * ‖toBesselPotentialSpaceCLM ((⌊s⌋ : ℝ) + 1) 2 u‖ := by
    have h := hC₁ u
    rw [Int.cast_add, Int.cast_one] at h
    rw [ContinuousLinearMap.coe_coe]
    exact h
  have h := norm_toBesselPotentialSpaceCLM_le_rpow_mul_rpow_mul_norm hC₀0 hC₁0 h₀ h₁
    ⟨Int.fract_nonneg s, (Int.fract_lt_one s).le⟩
  rw [ContinuousLinearMap.coe_coe] at h
  have hs : (1 - Int.fract s) * (⌊s⌋ : ℝ) + Int.fract s * ((⌊s⌋ : ℝ) + 1) = s := by
    rw [Int.fract]
    ring
  rw [hs] at h
  exact ⟨_, h⟩

end SchwartzMap

namespace TemperedDistribution

open MeasureTheory
open scoped SchwartzMap BesselPotentialSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F] {φ : E ≃ E}

/-- **Changes of variables preserve `H^s`.** If `φ` and `φ⁻¹` have temperate growth and bounded
derivatives of every positive order, then the pullback `φ^* u` of a tempered distribution
`u ∈ H^s` lies in `H^s`, for every real `s`. -/
theorem MemSobolev.compCLM (hφ : (φ : E → E).HasTemperateGrowth)
    (hψ : (φ.symm : E → E).HasTemperateGrowth)
    (hb : ∀ n, ∃ C, ∀ x, ‖iteratedFDeriv ℝ (n + 1) φ x‖ ≤ C)
    (hb' : ∀ n, ∃ C, ∀ x, ‖iteratedFDeriv ℝ (n + 1) φ.symm x‖ ≤ C) {s : ℝ} {u : 𝓢'(E, F)}
    (hu : MemSobolev s 2 u) : MemSobolev s 2 (TemperedDistribution.compCLM F φ hφ hψ u) := by
  obtain ⟨C, hC⟩ := SchwartzMap.exists_norm_toBesselPotentialSpaceCLM_compCLM_le (F := F) hφ hψ hb
    hb' s
  set P := SchwartzMap.compCLM ℂ (F := F) hφ (hψ.exists_norm_le_of_leftInverse φ.left_inv)
  have hdense := SchwartzMap.denseRange_toBesselPotentialSpaceCLM (E := E) (F := F) s (p := 2)
    ENNReal.ofNat_ne_top
  -- The extension of `u ↦ u ∘ φ` from Schwartz functions to `H^s`.
  let S : H^{s}(E, F) →L[ℂ] H^{s}(E, F) :=
    ((SchwartzMap.toBesselPotentialSpaceCLM s 2).toLinearMap ∘ₗ P.toLinearMap).extendOfNorm
      (SchwartzMap.toBesselPotentialSpaceCLM s 2).toLinearMap
  have hS (v : 𝓢(E, F)) : S (SchwartzMap.toBesselPotentialSpaceCLM s 2 v) =
      SchwartzMap.toBesselPotentialSpaceCLM s 2 (P v) :=
    LinearMap.extendOfNorm_eq hdense ⟨C, hC⟩ v
  -- It is the pullback of tempered distributions, by density of Schwartz functions.
  have hS' (f : H^{s}(E, F)) :
      (S f).toDistr = TemperedDistribution.compCLM F φ hφ hψ f.toDistr := by
    refine hdense.induction_on f (isClosed_eq
      (BesselPotentialSpace.continuous_toDistr.comp S.continuous)
      ((TemperedDistribution.compCLM F φ hφ hψ).continuous.comp
        BesselPotentialSpace.continuous_toDistr)) fun v ↦ ?_
    rw [hS]
    simp [P, compCLM_toTemperedDistributionCLM]
  have h := (S hu.toBesselPotentialSpace).memSobolev_toDistr
  rwa [hS', hu.toBesselPotentialSpace_toDistr] at h

end TemperedDistribution


namespace BesselPotentialSpace

open TemperedDistribution
open scoped SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F] {φ : E ≃ E} {s : ℝ}

/-- **Pullback along a change of variables on `H^s`.** For a bijection `φ` such that `φ` and `φ⁻¹`
have temperate growth and bounded derivatives of every positive order, the pullback of tempered
distributions `TemperedDistribution.compCLM` restricts to a bounded operator `H^s → H^s`, for every
real `s` (`BesselPotentialSpace.toDistr_compCLM`). On Schwartz functions it is `u ↦ u ∘ φ`
(`BesselPotentialSpace.compCLM_toBesselPotentialSpaceCLM`). -/
def compCLM (φ : E ≃ E) (hφ : (φ : E → E).HasTemperateGrowth)
    (hψ : (φ.symm : E → E).HasTemperateGrowth)
    (hb : ∀ n, ∃ C, ∀ x, ‖iteratedFDeriv ℝ (n + 1) φ x‖ ≤ C)
    (hb' : ∀ n, ∃ C, ∀ x, ‖iteratedFDeriv ℝ (n + 1) φ.symm x‖ ≤ C) (s : ℝ) :
    H^{s}(E, F) →L[ℂ] H^{s}(E, F) :=
  restrictCLM (TemperedDistribution.compCLM F φ hφ hψ) fun u ↦
    u.memSobolev_toDistr.compCLM hφ hψ hb hb'

variable (hφ : (φ : E → E).HasTemperateGrowth) (hψ : (φ.symm : E → E).HasTemperateGrowth)
    (hb : ∀ n, ∃ C, ∀ x, ‖iteratedFDeriv ℝ (n + 1) φ x‖ ≤ C)
    (hb' : ∀ n, ∃ C, ∀ x, ‖iteratedFDeriv ℝ (n + 1) φ.symm x‖ ≤ C)

@[simp]
theorem toDistr_compCLM (u : H^{s}(E, F)) :
    (compCLM φ hφ hψ hb hb' s u).toDistr = TemperedDistribution.compCLM F φ hφ hψ u.toDistr :=
  toDistr_restrictCLM _ _ u

/-- On Schwartz functions the pullback is composition with `φ`. -/
@[simp]
theorem compCLM_toBesselPotentialSpaceCLM (u : 𝓢(E, F)) :
    compCLM φ hφ hψ hb hb' s (SchwartzMap.toBesselPotentialSpaceCLM s 2 u) =
      SchwartzMap.toBesselPotentialSpaceCLM s 2
        (SchwartzMap.compCLM ℂ hφ (hψ.exists_norm_le_of_leftInverse φ.left_inv) u) :=
  ext (by simp [compCLM_toTemperedDistributionCLM])

/-- Pulling back along `φ` and then along `φ⁻¹` is the identity of `H^s`. -/
@[simp]
theorem compCLM_symm_compCLM (hφ' : (φ.symm.symm : E → E).HasTemperateGrowth)
    (hb'' : ∀ n, ∃ C, ∀ x, ‖iteratedFDeriv ℝ (n + 1) φ.symm.symm x‖ ≤ C) (u : H^{s}(E, F)) :
    compCLM φ.symm hψ hφ' hb' hb'' s (compCLM φ hφ hψ hb hb' s u) = u :=
  ext (by simp)

/-- Pulling back along `φ⁻¹` and then along `φ` is the identity of `H^s`. -/
@[simp]
theorem compCLM_compCLM_symm (hφ' : (φ.symm.symm : E → E).HasTemperateGrowth)
    (hb'' : ∀ n, ∃ C, ∀ x, ‖iteratedFDeriv ℝ (n + 1) φ.symm.symm x‖ ≤ C) (u : H^{s}(E, F)) :
    compCLM φ hφ hψ hb hb' s (compCLM φ.symm hψ hφ' hb' hb'' s u) = u :=
  ext (by simp)

/-- **Changes of variables are isomorphisms of `H^s`.** The pullback along `φ` as a continuous
linear automorphism of `H^s`, with inverse the pullback along `φ⁻¹`. -/
def compEquiv (φ : E ≃ E) (hφ : (φ : E → E).HasTemperateGrowth)
    (hψ : (φ.symm : E → E).HasTemperateGrowth)
    (hb : ∀ n, ∃ C, ∀ x, ‖iteratedFDeriv ℝ (n + 1) φ x‖ ≤ C)
    (hb' : ∀ n, ∃ C, ∀ x, ‖iteratedFDeriv ℝ (n + 1) φ.symm x‖ ≤ C) (s : ℝ) :
    H^{s}(E, F) ≃L[ℂ] H^{s}(E, F) :=
  .equivOfInverse (compCLM φ hφ hψ hb hb' s)
    (compCLM φ.symm hψ (by simpa using hφ) hb' (by simpa using hb) s)
    (compCLM_symm_compCLM hφ hψ hb hb' _ _) (compCLM_compCLM_symm hφ hψ hb hb' _ _)

@[simp]
theorem compEquiv_apply (u : H^{s}(E, F)) :
    compEquiv φ hφ hψ hb hb' s u = compCLM φ hφ hψ hb hb' s u :=
  (rfl)

/-- The inverse of the pullback along `φ` is the pullback along `φ⁻¹`. -/
@[simp]
theorem compEquiv_symm_apply (u : H^{s}(E, F)) :
    (compEquiv φ hφ hψ hb hb' s).symm u =
      compCLM φ.symm hψ (by simpa using hφ) hb' (by simpa using hb) s u :=
  (rfl)

end BesselPotentialSpace

namespace SchwartzMap

open scoped BesselPotentialSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F] {φ : E ≃ E}

/-- **Changes of variables extend to `H^s`.** If `φ` and `φ⁻¹` have temperate growth and bounded
derivatives of every positive order, then composition with `φ` on Schwartz functions extends to a
bounded operator `H^s → H^s`, for every real `s`. -/
theorem hasSobolevExtension_compCLM (hφ : (φ : E → E).HasTemperateGrowth)
    (hψ : (φ.symm : E → E).HasTemperateGrowth)
    (hb : ∀ n, ∃ C, ∀ x, ‖iteratedFDeriv ℝ (n + 1) φ x‖ ≤ C)
    (hb' : ∀ n, ∃ C, ∀ x, ‖iteratedFDeriv ℝ (n + 1) φ.symm x‖ ≤ C) (s : ℝ) :
    HasSobolevExtension
      (compCLM ℂ (F := F) hφ (hψ.exists_norm_le_of_leftInverse φ.left_inv)) s s :=
  hasSobolevExtension_iff.2 ⟨BesselPotentialSpace.compCLM φ hφ hψ hb hb' s,
    ContinuousLinearMap.ext fun u ↦
      BesselPotentialSpace.compCLM_toBesselPotentialSpaceCLM hφ hψ hb hb' u⟩

end SchwartzMap
