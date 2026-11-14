/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Coordinates
public import TauCeti.Analysis.Sobolev.Local.Lipschitz
public import TauCeti.Analysis.Sobolev.Local.Sharpness
public import Mathlib.Analysis.Calculus.FDeriv.Affine
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Affine.ContinuousAffineMap
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
import TauCeti.Analysis.InnerProductSpace.NormPow
import TauCeti.Analysis.Sobolev.Poincare.Wirtinger.W1p
import TauCeti.Analysis.Sobolev.WeakDeriv.Coordinates
import TauCeti.Analysis.Sobolev.WeakDeriv.Lipschitz
import TauCeti.Analysis.Sobolev.WeakDeriv.MeasurePreserving
import TauCeti.Analysis.Sobolev.WeakDeriv.NormRpow
import TauCeti.Analysis.Sobolev.WeakDeriv.Removable
import TauCeti.MeasureTheory.Integral.NormRpow

/-!
# Affine, norm, radial, retraction, and jump maps in local Lebesgue and Sobolev classes

This file establishes exact membership and non-membership results for benchmark vector-valued and
singular maps in `TauCeti.MemLpLoc` and `TauCeti.MemWkpLoc` on finite-dimensional real spaces:

1. **Continuous affine maps and global vs local `Lᵖ`.** Every continuous affine map
   `T : E →ᴬ[ℝ] F` into a complete space belongs to `MemWkpLoc p U k` for all `p`, `U`, and `k`,
   with constant weak derivative `T.contLinear`. On any nontrivial space `E` and `p ≠ 0`
   (including `p = ∞`), `id : E → E` lies in `MemWkpLoc p Set.univ k` for all `k` while failing
   global `MemLp id p volume`.
2. **Norms on general normed spaces.** On any finite-dimensional real normed space `E`, `x ↦ ‖x‖`
   lies in `MemWkpLoc p U 1` for all `p` and `U` with `‖fderiv ℝ norm x‖ ≤ 1`, without assuming an
   inner product; on `Fin 2 → ℝ` (`ℓ∞` norm) at `![1, 1 / 2]`, `fderiv ℝ norm` is the first
   coordinate projection rather than a radial inner-product functional.
3. **Inverse norm in three dimensions and vector radial powers.** On `EuclideanSpace ℝ (Fin 3)`,
   `x ↦ ‖x‖⁻¹` lies in `MemLpLoc p U` near `0` iff `p < 3`. On any nontrivial finite-dimensional
   real inner product space `E`, for `-1 < α` and `1 ≤ p < ∞`, the continuous radial field
   `x ↦ ‖x‖ ^ α • x` is weakly differentiable on every open set and lies in `MemWkpLoc p U 1` near
   `0` iff `-Module.finrank ℝ E < α * p.toReal`.
4. **Unit radial retraction `x ↦ ‖x‖⁻¹ • x`.** On a finite-dimensional real inner product space `E`
   with `1 < Module.finrank ℝ E` (`dim E ≥ 2`) and any `p : ℝ≥0∞` (including `0` and `∞`), the
   discontinuous unit radial retraction lies in `MemWkpLoc p U 1` near `0` iff
   `p < Module.finrank ℝ E`.
5. **Hyperplane jumps.** For a nonzero continuous linear functional `φ : E →L[ℝ] ℝ` and nonzero
   vector `c : F`, the half-space indicator `{x | 0 < φ x}.indicator (fun _ => c)` belongs to
   `MemLpLoc p U` for all `p` and `U`, yet admits no weak Fréchet derivative on any open set
   meeting `ker φ`, and hence lies outside `MemWkpLoc p U (k + 1)` whenever `interior U` meets
   `ker φ`.

## Main declarations

* `ContinuousAffineMap.memWkpLoc`, `ContinuousAffineMap.hasWeakFDerivOn`,
  `TauCeti.not_memLp_id`, `TauCeti.memWkpLoc_id_and_not_memLp_id`.
* `TauCeti.memWkpLoc_one_norm`, `TauCeti.hasWeakFDerivOn_norm_and_norm_fderiv_le_one`,
  `TauCeti.hasFDerivAt_norm_pi_fin_two`, `TauCeti.fderiv_norm_pi_fin_two_apply`.
* `TauCeti.memLpLoc_norm_inv_euclidean_fin_three_iff`.
* `TauCeti.radialRpowDeriv`, `TauCeti.hasWeakFDerivOn_norm_rpow_smul`,
  `TauCeti.memWkpLoc_one_norm_rpow_smul`, `TauCeti.not_memWkpLoc_one_norm_rpow_smul`,
  `TauCeti.memWkpLoc_one_norm_rpow_smul_iff`.
* `TauCeti.unitRadialDeriv`, `TauCeti.hasWeakFDerivOn_norm_inv_smul`,
  `TauCeti.memWkpLoc_one_norm_inv_smul`, `TauCeti.not_memWkpLoc_one_norm_inv_smul`,
  `TauCeti.memWkpLoc_one_norm_inv_smul_iff`.
* `TauCeti.memLpLoc_indicator_pos`, `TauCeti.not_hasWeakFDerivOn_indicator_pos`,
  `TauCeti.not_memWkpLoc_indicator_pos`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.2.2.
* H. Brezis, L. Nirenberg, *Degree theory and BMO; part I: Compact manifolds without boundary*,
  Selecta Math. (N.S.) 1 (1995), 197–263.
-/

public noncomputable section

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ENNReal InnerProductSpace NNReal Topology

namespace TauCeti

/-! ### Continuous affine maps and global versus local `Lᵖ` -/

section Affine

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]
  [CompleteSpace F] in
/-- Every continuous affine map between real normed spaces is `C^n` for every smoothness order. -/
private theorem contDiff_continuousAffineMap (T : E →ᴬ[ℝ] F) (n : WithTop ℕ∞) :
    ContDiff ℝ n T := by
  have heq : (T : E → F) = fun x => T.contLinear x + T 0 := by
    ext x
    simpa [vadd_eq_add] using T.map_vadd 0 x
  rw [heq]
  exact T.contLinear.contDiff.add contDiff_const

/-- Every continuous affine map into a complete space has its linear part as weak Fréchet
derivative on every open set. -/
theorem _root_.ContinuousAffineMap.hasWeakFDerivOn (T : E →ᴬ[ℝ] F) (Ω : Opens E) :
    HasWeakFDerivOn volume Ω T (fun _ => T.contLinear) := by
  have hf : fderiv ℝ (T : E → F) = fun _ => T.contLinear := funext fun _ => T.fderiv
  have hcd := (contDiff_continuousAffineMap T 1).contDiffOn (s := (Ω : Set E))
  exact hf ▸ hcd.hasWeakFDerivOn_fderiv (μ := volume)

/-- Every continuous affine map into a complete space belongs to `MemWkpLoc p U k` for every
exponent `p`, subset `U`, and order `k`. -/
theorem _root_.ContinuousAffineMap.memWkpLoc (T : E →ᴬ[ℝ] F) (p : ℝ≥0∞) (U : Set E) (k : ℕ) :
    MemWkpLoc p U k T :=
  ((contDiff_continuousAffineMap T k).contDiffOn (s := ((⊤ : Opens E) : Set E))).memWkpLoc
    (subset_univ U)

/-- On a nontrivial finite-dimensional real normed space with additive Haar `volume`, the identity
map fails global `MemLp` for every nonzero exponent `p ≤ ∞`. -/
theorem not_memLp_id [Nontrivial E] {p : ℝ≥0∞} (hp0 : p ≠ 0) :
    ¬ MemLp (id : E → E) p (volume : Measure E) := by
  intro hid
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  have hv_pos : 0 < ‖v‖ := norm_pos_iff.2 hv
  rcases eq_or_ne p ∞ with rfl | hp
  · have hfin : eLpNormEssSup (id : E → E) (volume : Measure E) < ∞ :=
      eLpNorm_exponent_top hid.aestronglyMeasurable ▸ hid.eLpNorm_lt_top
    set C : ℝ := (eLpNormEssSup (id : E → E) volume).toReal
    set c : E := ((max C 0 + 2 * ‖v‖) / ‖v‖) • v
    have hball_sub : ball c ‖v‖ ⊆ {x : E | C < ‖x‖} := by
      intro x hx
      have hdist : ‖x - c‖ < ‖v‖ := by simpa [dist_eq_norm] using hx
      have hc_norm : ‖c‖ = max C 0 + 2 * ‖v‖ := by
        rw [norm_smul, Real.norm_of_nonneg (div_nonneg (by positivity) hv_pos.le),
          div_mul_cancel₀ _ hv_pos.ne']
      have htri : ‖c‖ - ‖x - c‖ ≤ ‖x‖ := by
        have := norm_sub_norm_le c (c - x)
        simpa [sub_sub_cancel, norm_sub_rev] using this
      have hC : C ≤ max C 0 := le_max_left C 0
      change C < ‖x‖
      linarith
    have hpos : 0 < (volume : Measure E) (ball c ‖v‖) :=
      isOpen_ball.measure_pos volume (nonempty_ball.2 hv_pos)
    have hnull : (volume : Measure E) {x : E | C < ‖x‖} = 0 := by
      refine measure_mono_null (fun x (hlt : C < ‖x‖) => ?_)
        (ae_iff.1 (eNorm_ae_le_eLpNormEssSup (id : E → E) volume))
      intro hx
      have hle : ‖x‖ ≤ C := by
        have hx' := ENNReal.toReal_mono hfin.ne hx
        simpa [C, toReal_eNorm] using hx'
      exact hle.not_gt hlt
    exact (hpos.trans_le (measure_mono hball_sub)).ne' hnull
  · have hcompl_top : (volume : Measure E) (ball (0 : E) 1)ᶜ = ∞ := by
      by_contra hlt
      have huniv : (volume : Measure E) univ < ∞ := by
        calc (volume : Measure E) univ
            = (volume : Measure E) (ball (0 : E) 1 ∪ (ball (0 : E) 1)ᶜ) := by
              rw [union_compl_self]
          _ ≤ (volume : Measure E) (ball (0 : E) 1) + (volume : Measure E) (ball (0 : E) 1)ᶜ :=
              measure_union_le _ _
          _ < ∞ := ENNReal.add_lt_top.2 ⟨measure_ball_lt_top, Ne.lt_top hlt⟩
      exact (measure_univ_of_isAddLeftInvariant (volume : Measure E)).symm.not_gt huniv
    have hge_lt : (volume : Measure E) {x : E | (1 : ℝ≥0) ≤ ‖(id : E → E) x‖₊} < ∞ :=
      hid.meas_ge_lt_top hp0 hp one_ne_zero
    have hsub : (ball (0 : E) 1)ᶜ ⊆ {x : E | (1 : ℝ≥0) ≤ ‖(id : E → E) x‖₊} := fun x hx => by
      have hx' : 1 ≤ ‖x‖ := by simpa using hx
      exact hx'
    exact (hcompl_top ▸ measure_mono hsub).not_gt hge_lt

/-- **Global `id : E → E` lies in every `MemWkpLoc` class but in no nonzero global `Lᵖ` space.** -/
theorem memWkpLoc_id_and_not_memLp_id [Nontrivial E] {p : ℝ≥0∞} (hp0 : p ≠ 0) (k : ℕ) :
    MemWkpLoc p (univ : Set E) k (id : E → E) ∧ ¬ MemLp (id : E → E) p (volume : Measure E) :=
  ⟨(ContinuousAffineMap.id ℝ E).memWkpLoc p univ k, not_memLp_id hp0⟩

end Affine

/-! ### The norm on an arbitrary finite-dimensional real normed space -/

section NormMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]

/-- On any open subset `Ω` of a finite-dimensional real normed space, `fderiv ℝ norm` is a weak
Fréchet derivative of `x ↦ ‖x‖` and has operator norm bounded everywhere by `1`. -/
theorem hasWeakFDerivOn_norm_and_norm_fderiv_le_one (Ω : Opens E) :
    HasWeakFDerivOn volume Ω (fun x : E => ‖x‖) (fderiv ℝ fun x : E => ‖x‖) ∧
      ∀ x : E, ‖fderiv ℝ (fun y : E => ‖y‖) x‖ ≤ 1 :=
  ⟨lipschitzWith_one_norm.locallyLipschitz.locallyLipschitzOn.hasWeakFDerivOn_fderiv,
    fun x => by simpa using norm_fderiv_le_of_lipschitz ℝ lipschitzWith_one_norm (x₀ := x)⟩

/-- On `Fin 2 → ℝ` equipped with the `ℓ∞` norm, at `![1, 1 / 2]` the norm locally coincides with
the first coordinate projection, so its Fréchet derivative is `ContinuousLinearMap.proj 0`. -/
theorem hasFDerivAt_norm_pi_fin_two :
    HasFDerivAt (fun y : Fin 2 → ℝ => ‖y‖)
      (ContinuousLinearMap.proj (R := ℝ) (0 : Fin 2)) ![1, (1 / 2 : ℝ)] := by
  let π₀ : (Fin 2 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj (R := ℝ) (0 : Fin 2)
  let S : Set (Fin 2 → ℝ) := {y | |y 1| < y 0}
  have hS_open : IsOpen S :=
    isOpen_lt (continuous_abs.comp (continuous_apply 1)) (continuous_apply 0)
  have hxS : (![1, (1 / 2 : ℝ)] : Fin 2 → ℝ) ∈ S := by
    simp [S]
    norm_num
  have heq : (fun y : Fin 2 → ℝ => ‖y‖) =ᶠ[𝓝 ![1, (1 / 2 : ℝ)]] π₀ := by
    filter_upwards [hS_open.mem_nhds hxS] with y hy
    have hy0 : 0 < y 0 := (abs_nonneg (y 1)).trans_lt hy
    refine le_antisymm ?_ ((le_abs_self (y 0)).trans (norm_le_pi_norm y 0))
    refine (pi_norm_le_iff_of_nonneg hy0.le).2 fun i => ?_
    fin_cases i
    · simp [Real.norm_of_nonneg hy0.le]
    · simpa [Real.norm_eq_abs] using hy.le
  exact π₀.hasFDerivAt.congr_of_eventuallyEq heq

/-- On `Fin 2 → ℝ` (`ℓ∞` norm), the derivative of `y ↦ ‖y‖` at `![1, 1 / 2]` annihilates `![0, 1]`,
witnessing that it is not proportional to a Euclidean inner-product functional. -/
theorem fderiv_norm_pi_fin_two_apply :
    fderiv ℝ (fun y : Fin 2 → ℝ => ‖y‖) ![1, (1 / 2 : ℝ)] ![0, 1] = 0 := by
  rw [hasFDerivAt_norm_pi_fin_two.fderiv]
  simp

end NormMap

/-! ### Three-dimensional inverse norm and vector radial powers `x ↦ ‖x‖ ^ α • x` -/

/-- **Inverse norm on `ℝ³`.** For any neighbourhood `U` of `0` in `EuclideanSpace ℝ (Fin 3)` and
every `p : ℝ≥0∞` (including `0` and `∞`), `x ↦ ‖x‖⁻¹` belongs to `MemLpLoc p U` iff `p < 3`. -/
theorem memLpLoc_norm_inv_euclidean_fin_three_iff {p : ℝ≥0∞}
    {U : Set (EuclideanSpace ℝ (Fin 3))} (hU : U ∈ 𝓝 0) :
    MemLpLoc p U (fun x : EuclideanSpace ℝ (Fin 3) => ‖x‖⁻¹) ↔ p < 3 := by
  simpa [finrank_euclideanSpace_fin] using memLpLoc_norm_inv_iff (p := p) hU

section RadialPower

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]

/-- Classical Fréchet derivative field of the vector radial power `x ↦ ‖x‖ ^ α • x` away from the
origin: `‖x‖ ^ α • id + (α * ‖x‖ ^ (α - 2)) • (⟪x, ·⟫ • x)`. -/
def radialRpowDeriv (α : ℝ) (x : E) : E →L[ℝ] E :=
  ‖x‖ ^ α • ContinuousLinearMap.id ℝ E +
    (α * ‖x‖ ^ (α - 2)) • (innerSL ℝ x).smulRight x

omit [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] in
private theorem hasFDerivAt_norm_rpow_smul_of_ne (α : ℝ) {x : E} (hx : x ≠ 0) :
    HasFDerivAt (fun y : E => ‖y‖ ^ α • y) (radialRpowDeriv α x) x := by
  refine ((hasFDerivAt_norm_rpow_of_ne α hx).smul (hasFDerivAt_id x)).congr_fderiv ?_
  ext v
  simp [radialRpowDeriv, mul_smul]

omit [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] in
private theorem continuous_norm_rpow_smul {α : ℝ} (hα : -1 < α) :
    Continuous (fun x : E => ‖x‖ ^ α • x) := by
  rw [continuous_iff_continuousAt]
  intro x
  rcases eq_or_ne x 0 with rfl | hx
  · rw [ContinuousAt, smul_zero, tendsto_zero_iff_norm_tendsto_zero]
    have hcont : Continuous (fun y : E => ‖y‖ ^ (α + 1)) :=
      (continuous_norm (E := E)).rpow_const fun _ => Or.inr (by linarith : 0 ≤ α + 1)
    have hpow : Tendsto (fun y : E => ‖y‖ ^ (α + 1)) (𝓝 0) (𝓝 0) := by
      have ht := (hcont.continuousAt (x := (0 : E))).tendsto
      rwa [norm_zero, Real.zero_rpow (by linarith : α + 1 ≠ 0)] at ht
    refine hpow.congr fun y => ?_
    rcases eq_or_ne y 0 with rfl | hy
    · simp [Real.zero_rpow (by linarith : α + 1 ≠ 0)]
    · rw [Real.rpow_add_one (norm_ne_zero_iff.2 hy), norm_smul,
        Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg y) α)]
  · exact ((continuous_norm.continuousAt.rpow_const
      (Or.inl (norm_ne_zero_iff.2 hx))).smul continuousAt_id)

omit [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] in
private theorem norm_radialRpowDeriv_le (α : ℝ) {x : E} (hx : x ≠ 0) :
    ‖radialRpowDeriv α x‖ ≤ (1 + |α|) * ‖x‖ ^ α := by
  have hx_pos : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hsq : ‖x‖ ^ (α - 2) * (‖x‖ * ‖x‖) = ‖x‖ ^ α := by
    calc ‖x‖ ^ (α - 2) * (‖x‖ * ‖x‖)
        = ‖x‖ ^ (α - 2) * ‖x‖ ^ (2 : ℝ) := by rw [Real.rpow_two, sq]
      _ = ‖x‖ ^ α := by
        rw [← Real.rpow_add hx_pos]
        ring_nf
  calc ‖radialRpowDeriv α x‖
      ≤ ‖‖x‖ ^ α • ContinuousLinearMap.id ℝ E‖ +
          ‖(α * ‖x‖ ^ (α - 2)) • (innerSL ℝ x).smulRight x‖ := norm_add_le _ _
    _ ≤ ‖x‖ ^ α * 1 + |α| * ‖x‖ ^ (α - 2) * (‖x‖ * ‖x‖) := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg hx_pos.le α),
          norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (Real.rpow_nonneg hx_pos.le _),
          ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm]
        gcongr
        exact ContinuousLinearMap.norm_id_le
    _ = (1 + |α|) * ‖x‖ ^ α := by
        rw [mul_assoc |α|, hsq]
        ring

omit [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] in
private theorem le_norm_radialRpowDeriv {α : ℝ} (hα : -1 < α) {x : E} (hx : x ≠ 0) :
    (1 + α) * ‖x‖ ^ α ≤ ‖radialRpowDeriv α x‖ := by
  have hx_pos : 0 < ‖x‖ := norm_pos_iff.2 hx
  let u₀ : E := ‖x‖⁻¹ • x
  have hu₀ : ‖u₀‖ = 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hx_pos.le), inv_mul_cancel₀ hx_pos.ne']
  have happly : radialRpowDeriv α x u₀ = ((1 + α) * ‖x‖ ^ α) • u₀ := by
    have hxx : ⟪x, x⟫_ℝ = ‖x‖ ^ (2 : ℝ) := by rw [real_inner_self_eq_norm_sq, Real.rpow_two]
    have hpow : ‖x‖ ^ (α - 2) * ‖x‖ ^ (2 : ℝ) = ‖x‖ ^ α := by
      rw [← Real.rpow_add hx_pos]
      ring_nf
    simp only [radialRpowDeriv, add_apply, smul_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
      u₀, real_inner_smul_right, hxx]
    rw [smul_smul, smul_smul, smul_smul, ← add_smul]
    congr 1
    calc ‖x‖ ^ α * ‖x‖⁻¹ + α * ‖x‖ ^ (α - 2) * (‖x‖⁻¹ * ‖x‖ ^ (2 : ℝ))
        = (1 + α) * (‖x‖ ^ α * ‖x‖⁻¹) := by
          rw [← hpow]
          ring
      _ = (1 + α) * ‖x‖ ^ α * ‖x‖⁻¹ := by ring
  have hle := (radialRpowDeriv α x).le_opNorm u₀
  rw [happly, norm_smul, hu₀, mul_one, mul_one,
    Real.norm_of_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg hx_pos.le α))] at hle
  exact hle

omit [(volume : Measure E).IsAddHaarMeasure] in
private theorem aestronglyMeasurable_radialRpowDeriv (α : ℝ) {μ : Measure E} :
    AEStronglyMeasurable (radialRpowDeriv (E := E) α) μ := by
  unfold radialRpowDeriv
  have hcont : Continuous (fun x : E => (innerSL ℝ x).smulRight x) :=
    ((ContinuousLinearMap.smulRightL ℝ E E).continuous.comp (innerSL ℝ).continuous).clm_apply
      continuous_id
  exact ((measurable_norm.pow_const α).aestronglyMeasurable.smul aestronglyMeasurable_const).add
    ((measurable_const.mul (measurable_norm.pow_const (α - 2))).aestronglyMeasurable.smul
      hcont.aestronglyMeasurable)

/-- **Weak differentiability of `x ↦ ‖x‖ ^ α • x` for `-1 < α`.** On any nontrivial
finite-dimensional real inner product space `E`, `-1 < α` makes `x ↦ ‖x‖ ^ α • x` continuous at
`0` and its classical derivative `radialRpowDeriv α` (of size `‖x‖ ^ α`, with `-dim E ≤ -1 < α`)
locally integrable, so `radialRpowDeriv α` is its weak derivative on every open set `Ω`. -/
theorem hasWeakFDerivOn_norm_rpow_smul [Nontrivial E] {α : ℝ} (hα : -1 < α) (Ω : Opens E) :
    HasWeakFDerivOn volume Ω (fun x : E => ‖x‖ ^ α • x) (radialRpowDeriv α) := by
  have hd : (1 : ℝ) ≤ Module.finrank ℝ E := by
    exact_mod_cast Nat.succ_le_of_lt (Module.finrank_pos (R := ℝ) (M := E))
  have hlp1 : MemLpLoc 1 (Ω : Set E) (radialRpowDeriv α) := by
    have hnorm := memLpLoc_norm_rpow (E := E) (p := 1) (U := Ω) (s := α) one_ne_zero
      ENNReal.one_ne_top (by simpa using by linarith : -(Module.finrank ℝ E : ℝ) < α * 1)
    refine memLpLoc_iff.2 fun K hKΩ hK => ?_
    refine ((memLpLoc_iff.1 hnorm K hKΩ hK).const_mul (1 + |α|)).of_le
      (aestronglyMeasurable_radialRpowDeriv α) ?_
    filter_upwards [ae_restrict_of_ae (Measure.ae_ne volume (0 : E))] with x hx
    refine (norm_radialRpowDeriv_le α hx).trans ?_
    rw [Real.norm_of_nonneg (by positivity)]
  exact hasWeakFDerivOn_of_hasFDerivAt_off_countable (countable_singleton 0)
    (continuous_norm_rpow_smul hα).continuousOn
    (hlp1.locallyIntegrableOn le_rfl Ω.isOpen.isLocallyClosed)
    fun x hx => hasFDerivAt_norm_rpow_smul_of_ne α hx.2

/-- For `-1 < α` and `1 ≤ p < ∞`, if `-Module.finrank ℝ E < α * p.toReal`, then `x ↦ ‖x‖ ^ α • x`
belongs to `MemWkpLoc p U 1` on every subset `U` of `E`. -/
theorem memWkpLoc_one_norm_rpow_smul [Nontrivial E] {p : ℝ≥0∞} {U : Set E} {α : ℝ}
    (hp1 : 1 ≤ p) (hp : p ≠ ∞) (hα : -1 < α)
    (hs : -(Module.finrank ℝ E : ℝ) < α * p.toReal) :
    MemWkpLoc p U 1 (fun x : E => ‖x‖ ^ α • x) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp1).ne'
  have hnorm := memLpLoc_norm_rpow (E := E) (p := p) (U := U) hp0 hp hs
  refine memWkpLoc_one_iff.2 ⟨(continuous_norm_rpow_smul hα).continuousOn.memLpLoc,
    radialRpowDeriv α, hasWeakFDerivOn_norm_rpow_smul hα _, memLpLoc_iff.2 fun K hKU hK => ?_⟩
  refine ((memLpLoc_iff.1 hnorm K hKU hK).const_mul (1 + |α|)).of_le
    (aestronglyMeasurable_radialRpowDeriv α) ?_
  filter_upwards [ae_restrict_of_ae (Measure.ae_ne volume (0 : E))] with x hx
  refine (norm_radialRpowDeriv_le α hx).trans ?_
  rw [Real.norm_of_nonneg (by positivity)]

/-- For `-1 < α` and `0 < p < ∞`, if `α * p.toReal ≤ -Module.finrank ℝ E`, then `x ↦ ‖x‖ ^ α • x`
does not belong to `MemWkpLoc p U 1` on any neighbourhood `U` of `0`. -/
theorem not_memWkpLoc_one_norm_rpow_smul [Nontrivial E] {p : ℝ≥0∞} {U : Set E} {α : ℝ}
    (hp0 : p ≠ 0) (hp : p ≠ ∞) (hU : U ∈ 𝓝 (0 : E)) (hα : -1 < α)
    (hs : α * p.toReal ≤ -(Module.finrank ℝ E : ℝ)) :
    ¬ MemWkpLoc p U 1 (fun x : E => ‖x‖ ^ α • x) := by
  intro h
  obtain ⟨-, D, hD, hDp⟩ := memWkpLoc_one_iff.1 h
  obtain ⟨r, hr, hrU⟩ := nhds_basis_closedBall.mem_iff.1 (interior_mem_nhds.2 hU)
  have hae : D =ᵐ[volume.restrict (Opens.interior U)] radialRpowDeriv α :=
    hD.ae_eq (hasWeakFDerivOn_norm_rpow_smul hα (Opens.interior U))
  have hDK : MemLp D p (volume.restrict (closedBall (0 : E) r)) :=
    memLpLoc_iff.1 hDp _ (hrU.trans interior_subset) (isCompact_closedBall (0 : E) r)
  have hradK : MemLp (radialRpowDeriv α) p (volume.restrict (closedBall (0 : E) r)) :=
    hDK.ae_eq (hae.filter_mono (ae_mono (Measure.restrict_mono hrU le_rfl)))
  have hc_pos : 0 < 1 + α := by linarith
  have hpowK : MemLp (fun x : E => ‖x‖ ^ α) p (volume.restrict (closedBall (0 : E) r)) := by
    refine (hradK.norm.const_mul (1 + α)⁻¹).of_le
      (measurable_norm.pow_const α).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_of_ae (Measure.ae_ne volume (0 : E))] with x hx
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg x) α),
      Real.norm_of_nonneg (mul_nonneg (inv_nonneg.2 hc_pos.le) (norm_nonneg _))]
    exact (le_inv_mul_iff₀ hc_pos).2 (le_norm_radialRpowDeriv hα hx)
  exact not_memLpLoc_norm_rpow hp0 hp (closedBall_mem_nhds (0 : E) hr) hs hpowK.memLpLoc

/-- **Local `W^{1,p}` threshold of `x ↦ ‖x‖ ^ α • x` (`-1 < α`).** On a nontrivial
finite-dimensional real inner product space `E`, for `1 ≤ p < ∞`, `-1 < α`, and any neighbourhood
`U` of `0`, `x ↦ ‖x‖ ^ α • x` belongs to `MemWkpLoc p U 1` iff
`-Module.finrank ℝ E < α * p.toReal`. -/
theorem memWkpLoc_one_norm_rpow_smul_iff [Nontrivial E] {p : ℝ≥0∞} {U : Set E} {α : ℝ}
    (hp1 : 1 ≤ p) (hp : p ≠ ∞) (hU : U ∈ 𝓝 (0 : E)) (hα : -1 < α) :
    MemWkpLoc p U 1 (fun x : E => ‖x‖ ^ α • x) ↔ -(Module.finrank ℝ E : ℝ) < α * p.toReal :=
  ⟨fun h => not_le.1 fun hs =>
      not_memWkpLoc_one_norm_rpow_smul (zero_lt_one.trans_le hp1).ne' hp hU hα hs h,
    memWkpLoc_one_norm_rpow_smul hp1 hp hα⟩

end RadialPower

/-! ### The unit radial retraction `x ↦ ‖x‖⁻¹ • x` in dimension at least `2` -/

section UnitRetraction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]

/-- Classical Fréchet derivative field of the unit radial retraction `x ↦ ‖x‖⁻¹ • x`:
`‖x‖⁻¹ • id - ‖x‖ ^ (-3 : ℝ) • (⟪x, ·⟫ • x)`. -/
def unitRadialDeriv (x : E) : E →L[ℝ] E :=
  ‖x‖⁻¹ • ContinuousLinearMap.id ℝ E - ‖x‖ ^ (-3 : ℝ) • (innerSL ℝ x).smulRight x

omit [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] in
private theorem norm_unitRadialDeriv_le (x : E) : ‖unitRadialDeriv x‖ ≤ 2 * ‖x‖⁻¹ := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [unitRadialDeriv]
  have hx_pos : 0 < ‖x‖ := norm_pos_iff.2 hx
  have h3 : ‖x‖ ^ (-3 : ℝ) * (‖x‖ * ‖x‖) = ‖x‖⁻¹ := by
    calc ‖x‖ ^ (-3 : ℝ) * (‖x‖ * ‖x‖)
        = ‖x‖ ^ (-3 : ℝ) * ‖x‖ ^ (2 : ℝ) := by rw [Real.rpow_two, sq]
      _ = ‖x‖ ^ (-1 : ℝ) := by
        rw [← Real.rpow_add hx_pos]
        norm_num
      _ = ‖x‖⁻¹ := Real.rpow_neg_one ‖x‖
  calc ‖unitRadialDeriv x‖
      ≤ ‖‖x‖⁻¹ • ContinuousLinearMap.id ℝ E‖ +
          ‖‖x‖ ^ (-3 : ℝ) • (innerSL ℝ x).smulRight x‖ := norm_sub_le _ _
    _ ≤ ‖x‖⁻¹ * 1 + ‖x‖ ^ (-3 : ℝ) * (‖x‖ * ‖x‖) := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hx_pos.le),
          Real.norm_of_nonneg (Real.rpow_nonneg hx_pos.le _),
          ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm]
        gcongr
        exact ContinuousLinearMap.norm_id_le
    _ = 2 * ‖x‖⁻¹ := by
        rw [h3]
        ring

omit [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure] in
private theorem norm_inv_le_norm_unitRadialDeriv (hd : 1 < Module.finrank ℝ E) {x : E}
    (hx : x ≠ 0) : ‖x‖⁻¹ ≤ ‖unitRadialDeriv x‖ := by
  let K : Submodule ℝ E := ℝ ∙ x
  have hK_le : Module.finrank ℝ K ≤ 1 := finrank_span_singleton hx |>.le
  have h_orth_pos : 0 < Module.finrank ℝ Kᗮ := by
    have hsum := K.finrank_add_finrank_orthogonal
    omega
  have : Nontrivial Kᗮ := Module.nontrivial_of_finrank_pos h_orth_pos
  obtain ⟨⟨v, hvK⟩, hv0⟩ := exists_ne (0 : Kᗮ)
  have hv_ne : v ≠ 0 := Subtype.coe_ne_coe.2 hv0
  have hv_pos : 0 < ‖v‖ := norm_pos_iff.2 hv_ne
  have hxv : ⟪x, v⟫_ℝ = 0 := Submodule.mem_orthogonal_singleton_iff_inner_right.1 hvK
  let w : E := ‖v‖⁻¹ • v
  have hw_norm : ‖w‖ = 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hv_pos.le), inv_mul_cancel₀ hv_pos.ne']
  have hxw : ⟪x, w⟫_ℝ = 0 := by simp [w, real_inner_smul_right, hxv]
  have happly : unitRadialDeriv x w = ‖x‖⁻¹ • w := by
    simp [unitRadialDeriv, ContinuousLinearMap.smulRight_apply, hxw]
  have hle := (unitRadialDeriv x).le_opNorm w
  rw [happly, norm_smul, hw_norm, mul_one, mul_one,
    Real.norm_of_nonneg (inv_nonneg.2 (norm_nonneg x))] at hle
  exact hle

omit [(volume : Measure E).IsAddHaarMeasure] in
private theorem aestronglyMeasurable_unitRadialDeriv {μ : Measure E} :
    AEStronglyMeasurable (unitRadialDeriv (E := E)) μ := by
  unfold unitRadialDeriv
  have hcont : Continuous (fun x : E => (innerSL ℝ x).smulRight x) :=
    ((ContinuousLinearMap.smulRightL ℝ E E).continuous.comp (innerSL ℝ).continuous).clm_apply
      continuous_id
  exact (measurable_norm.inv.aestronglyMeasurable.smul aestronglyMeasurable_const).sub
    ((measurable_norm.pow_const (-3 : ℝ)).aestronglyMeasurable.smul hcont.aestronglyMeasurable)

/-- **Weak differentiability of the unit radial retraction in dimension `≥ 2`.** When
`1 < Module.finrank ℝ E`, `x ↦ ‖x‖⁻¹ • x` has weak Fréchet derivative `unitRadialDeriv` on every
open set `Ω : Opens E`. -/
theorem hasWeakFDerivOn_norm_inv_smul (hd : 1 < Module.finrank ℝ E) (Ω : Opens E) :
    HasWeakFDerivOn volume Ω (fun x : E => ‖x‖⁻¹ • x) unitRadialDeriv := by
  let b := stdOrthonormalBasis ℝ E
  rw [hasWeakFDerivOn_iff_coordinates b.toBasis]
  intro i
  have hweak := hasWeakFDerivOn_norm_rpow_neg_one_mul_inner (μ := volume) hd (b i) Ω
  convert hweak using 1
  · funext x
    rw [Module.Basis.coord_apply, b.coe_toBasis_repr_apply, b.repr_apply_apply,
      real_inner_smul_right, real_inner_comm (b i) x, Real.rpow_neg_one]
  · funext x
    ext w
    rw [ContinuousLinearMap.comp_apply, LinearMap.coe_toContinuousLinearMap',
      Module.Basis.coord_apply, b.coe_toBasis_repr_apply, b.repr_apply_apply, unitRadialDeriv,
      sub_apply, smul_apply, smul_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, inner_sub_right,
      real_inner_smul_right, real_inner_smul_right, real_inner_smul_right, sub_apply, smul_apply,
      smul_apply, innerSL_apply_apply, innerSL_apply_apply, Real.rpow_neg_one,
      real_inner_comm (b i) x]
    simp only [smul_eq_mul]
    ring

/-- **Sufficiency for `x ↦ ‖x‖⁻¹ • x` in `W^{1,p}_loc`.** For `1 < Module.finrank ℝ E` and any
`p < Module.finrank ℝ E` (including `0 ≤ p < 1` and `1 ≤ p < dim E`), the unit radial retraction
lies in `MemWkpLoc p U 1` on every subset `U` of `E`. -/
theorem memWkpLoc_one_norm_inv_smul (hd : 1 < Module.finrank ℝ E) {p : ℝ≥0∞}
    (hp : p < Module.finrank ℝ E) (U : Set E) :
    MemWkpLoc p U 1 (fun x : E => ‖x‖⁻¹ • x) := by
  have hu : MemLpLoc p U (fun x : E => ‖x‖⁻¹ • x) := by
    refine memLpLoc_iff.2 fun K _ hK => ?_
    have : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hK.measure_lt_top⟩
    refine MemLp.of_bound (measurable_norm.inv.smul measurable_id).aestronglyMeasurable 1
      (Eventually.of_forall fun x => ?_)
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 (norm_nonneg x)),
        inv_mul_cancel₀ (norm_ne_zero_iff.2 hx)]
  have hinv := memLpLoc_norm_inv (E := E) (U := U) hp
  refine memWkpLoc_one_iff.2 ⟨hu, unitRadialDeriv, hasWeakFDerivOn_norm_inv_smul hd _,
    memLpLoc_iff.2 fun K hKU hK => ?_⟩
  refine ((memLpLoc_iff.1 hinv K hKU hK).const_mul 2).of_le
    aestronglyMeasurable_unitRadialDeriv (Eventually.of_forall fun x => ?_)
  refine (norm_unitRadialDeriv_le x).trans ?_
  rw [Real.norm_of_nonneg (by positivity)]

/-- **Sharp failure of `x ↦ ‖x‖⁻¹ • x` at and above the dimension (`dim E ≤ p ≤ ∞`).** When
`1 < Module.finrank ℝ E` and `U` is a neighbourhood of `0`, `x ↦ ‖x‖⁻¹ • x` does not belong to
`MemWkpLoc p U 1` for any `p ≥ Module.finrank ℝ E` (including `p = ∞`): in dimension `≥ 2`, every
nonzero point has a unit tangential direction along which `unitRadialDeriv x` stretches by
`‖x‖⁻¹`, which fails `Lᵖ` near `0`. -/
theorem not_memWkpLoc_one_norm_inv_smul (hd : 1 < Module.finrank ℝ E) {p : ℝ≥0∞} {U : Set E}
    (hU : U ∈ 𝓝 (0 : E)) (hp : (Module.finrank ℝ E : ℝ≥0∞) ≤ p) :
    ¬ MemWkpLoc p U 1 (fun x : E => ‖x‖⁻¹ • x) := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (zero_lt_one.trans hd)
  intro h
  obtain ⟨-, D, hD, hDp⟩ := memWkpLoc_one_iff.1 h
  obtain ⟨r, hr, hrU⟩ := nhds_basis_closedBall.mem_iff.1 (interior_mem_nhds.2 hU)
  have hae : D =ᵐ[volume.restrict (Opens.interior U)] unitRadialDeriv :=
    hD.ae_eq (hasWeakFDerivOn_norm_inv_smul hd (Opens.interior U))
  have hDK : MemLp D p (volume.restrict (closedBall (0 : E) r)) :=
    memLpLoc_iff.1 hDp _ (hrU.trans interior_subset) (isCompact_closedBall (0 : E) r)
  have hradK : MemLp unitRadialDeriv p (volume.restrict (closedBall (0 : E) r)) :=
    hDK.ae_eq (hae.filter_mono (ae_mono (Measure.restrict_mono hrU le_rfl)))
  have hinvK : MemLp (fun x : E => ‖x‖⁻¹) p (volume.restrict (closedBall (0 : E) r)) := by
    refine hradK.of_le measurable_norm.inv.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_of_ae (Measure.ae_ne volume (0 : E))] with x hx
    rw [Real.norm_of_nonneg (inv_nonneg.2 (norm_nonneg x))]
    exact norm_inv_le_norm_unitRadialDeriv hd hx
  exact not_memLp_norm_inv_closedBall hr hp hinvK

/-- **Complete `W^{1,p}_loc` classification of the unit radial retraction (`dim E ≥ 2`).** For
`1 < Module.finrank ℝ E`, any neighbourhood `U` of `0`, and any `p : ℝ≥0∞` (including `0` and `∞`),
`x ↦ ‖x‖⁻¹ • x` lies in `MemWkpLoc p U 1` iff `p < Module.finrank ℝ E`. -/
theorem memWkpLoc_one_norm_inv_smul_iff (hd : 1 < Module.finrank ℝ E) {p : ℝ≥0∞} {U : Set E}
    (hU : U ∈ 𝓝 (0 : E)) :
    MemWkpLoc p U 1 (fun x : E => ‖x‖⁻¹ • x) ↔ p < Module.finrank ℝ E :=
  ⟨fun h => not_le.1 fun hp => not_memWkpLoc_one_norm_inv_smul hd hU hp h,
    fun hp => memWkpLoc_one_norm_inv_smul hd hp U⟩

end UnitRetraction

/-! ### Hyperplane jump indicators -/

section HyperplaneJump

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [FiniteDimensional ℝ E] [NormedSpace ℝ F] in
/-- The indicator `{x | 0 < φ x}.indicator (fun _ => c)` of an open half-space belongs to
`MemLpLoc p U` for every exponent `p` (including `p = ∞`) and every subset `U`. -/
theorem memLpLoc_indicator_pos (φ : E →L[ℝ] ℝ) (c : F) (p : ℝ≥0∞) (U : Set E) :
    MemLpLoc p U ({x : E | 0 < φ x}.indicator fun _ => c) := by
  have hm : MeasurableSet {x : E | 0 < φ x} :=
    (isOpen_lt continuous_const φ.continuous).measurableSet
  refine memLpLoc_iff.2 fun K _ hK => ?_
  have : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hK.measure_lt_top⟩
  refine MemLp.of_bound (aestronglyMeasurable_const.indicator hm) ‖c‖
    (Eventually.of_forall fun x => ?_)
  by_cases hx : 0 < φ x <;> simp [hx]

/-- Any candidate weak Fréchet derivative of a half-space jump indicator vanishes almost
everywhere, because the indicator is locally constant on the two open half-spaces and the
separating hyperplane is Haar-null. -/
private theorem ae_eq_zero_of_hasWeakFDerivOn_indicator_pos {φ : E →L[ℝ] ℝ} (hφ : φ ≠ 0)
    {c : F} {Ω : Opens E} {D : E → E →L[ℝ] F}
    (hD : HasWeakFDerivOn volume Ω ({x : E | 0 < φ x}.indicator fun _ => c) D) :
    D =ᵐ[volume.restrict Ω] 0 := by
  have : CompleteSpace F := hD.completeSpace
  let Ωpos : Opens E := Ω ⊓ ⟨{x : E | 0 < φ x}, isOpen_lt continuous_const φ.continuous⟩
  let Ωneg : Opens E := Ω ⊓ ⟨{x : E | φ x < 0}, isOpen_lt φ.continuous continuous_const⟩
  have hpos : D =ᵐ[volume.restrict Ωpos] 0 := by
    have hc_eq : ({x : E | 0 < φ x}.indicator fun _ => c) =ᵐ[volume.restrict Ωpos] fun _ => c :=
      (ae_restrict_iff' Ωpos.isOpen.measurableSet).2 <| Eventually.of_forall fun x hx =>
        indicator_of_mem hx.2 _
    have h0 : HasWeakFDerivOn volume Ωpos (fun _ : E => c) 0 :=
      hasWeakFDerivOn_iff.mpr fun _ => hasWeakLineDerivOn_const c
    exact ((hD.mono inf_le_left).congr_ae hc_eq).ae_eq h0
  have hneg : D =ᵐ[volume.restrict Ωneg] 0 := by
    have h0_eq : ({x : E | 0 < φ x}.indicator fun _ => c) =ᵐ[volume.restrict Ωneg] 0 :=
      (ae_restrict_iff' Ωneg.isOpen.measurableSet).2 <| Eventually.of_forall fun x hx => by
        have hxlt : φ x < 0 := hx.2
        exact indicator_of_notMem (not_lt.2 hxlt.le) _
    have h0 : HasWeakFDerivOn volume Ωneg (fun _ : E => (0 : F)) 0 :=
      hasWeakFDerivOn_iff.mpr fun _ => hasWeakLineDerivOn_const 0
    exact ((hD.mono inf_le_left).congr_ae h0_eq).ae_eq h0
  have hker_ne : LinearMap.ker φ.toLinearMap ≠ ⊤ := by
    intro htop
    apply hφ
    ext x
    exact LinearMap.mem_ker.1 (htop ▸ Submodule.mem_top)
  have hker_zero : (volume : Measure E) (LinearMap.ker φ.toLinearMap : Set E) = 0 :=
    Measure.addHaar_submodule volume _ hker_ne
  have hpos' := (ae_restrict_iff' Ωpos.isOpen.measurableSet).1 hpos
  have hneg' := (ae_restrict_iff' Ωneg.isOpen.measurableSet).1 hneg
  rw [Filter.EventuallyEq, ae_restrict_iff' Ω.isOpen.measurableSet]
  filter_upwards [hpos', hneg', compl_mem_ae_iff.2 hker_zero] with x hxp hxn hxker hxΩ
  rcases lt_trichotomy (φ x) 0 with hlt | heq | hgt
  · exact hxn ⟨hxΩ, hlt⟩
  · exact False.elim (hxker heq)
  · exact hxp ⟨hxΩ, hgt⟩

/-- On a Euclidean ball centered on `ker ψ` (`ψ ≠ 0`), a scalar half-space jump `{0 < ψ}` with
nonzero height `a` cannot agree almost everywhere with a constant. -/
private theorem not_ae_eq_const_indicator_pos_ball {n : ℕ}
    {ψ : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ} (hψ : ψ ≠ 0) {y₀ : EuclideanSpace ℝ (Fin n)}
    (hy₀ : ψ y₀ = 0) {r : ℝ} (hr : 0 < r) {a m : ℝ} (ha : a ≠ 0) :
    ¬ (({y : EuclideanSpace ℝ (Fin n) | 0 < ψ y}.indicator fun _ => a) =ᵐ[
        volume.restrict (ball y₀ r)] fun _ => m) := by
  intro hm
  obtain ⟨w, hw⟩ : ∃ w, ψ w ≠ 0 := by
    by_contra! h0
    exact hψ (ContinuousLinearMap.ext h0)
  let v : EuclideanSpace ℝ (Fin n) := if 0 < ψ w then w else -w
  have hv_pos : 0 < ψ v := by
    dsimp [v]
    split_ifs with h
    · exact h
    · simpa using lt_of_le_of_ne (not_lt.1 h) hw
  have hv_norm : 0 < ‖v‖ := norm_pos_iff.2 fun hv0 => by simp [hv0] at hv_pos
  let t : ℝ := r / (2 * ‖v‖)
  have ht_pos : 0 < t := div_pos hr (by positivity)
  have htv_lt : ‖t • v‖ < r := by
    rw [norm_smul, Real.norm_of_nonneg ht_pos.le]
    calc r / (2 * ‖v‖) * ‖v‖ = r / 2 := by field_simp
      _ < r := half_lt_self hr
  let Bpos : Set (EuclideanSpace ℝ (Fin n)) := ball y₀ r ∩ {y | 0 < ψ y}
  let Bneg : Set (EuclideanSpace ℝ (Fin n)) := ball y₀ r ∩ {y | ψ y < 0}
  have hBpos_open : IsOpen Bpos := isOpen_ball.inter (isOpen_lt continuous_const ψ.continuous)
  have hBneg_open : IsOpen Bneg := isOpen_ball.inter (isOpen_lt ψ.continuous continuous_const)
  have hBpos_ne : Bpos.Nonempty := ⟨y₀ + t • v, by simpa [dist_eq_norm] using htv_lt,
    by simp [map_add, map_smul, hy₀, mul_pos ht_pos hv_pos]⟩
  have hBneg_ne : Bneg.Nonempty := ⟨y₀ - t • v,
    by simpa [dist_eq_norm, sub_eq_add_neg] using htv_lt,
    by simp [map_sub, map_smul, hy₀, mul_pos ht_pos hv_pos]⟩
  have hm' := (ae_restrict_iff' measurableSet_ball).1 hm
  have h1 : ∃ y ∈ Bpos, ({z | 0 < ψ z}.indicator fun _ => a) y = m := by
    by_contra! hcon
    have hzero : (volume : Measure _) Bpos = 0 :=
      measure_mono_null (fun y hy => fun hmy => hcon y hy (hmy hy.1)) (ae_iff.1 hm')
    exact (hBpos_open.measure_pos volume hBpos_ne).ne' hzero
  have h2 : ∃ y ∈ Bneg, ({z | 0 < ψ z}.indicator fun _ => a) y = m := by
    by_contra! hcon
    have hzero : (volume : Measure _) Bneg = 0 :=
      measure_mono_null (fun y hy => fun hmy => hcon y hy (hmy hy.1)) (ae_iff.1 hm')
    exact (hBneg_open.measure_pos volume hBneg_ne).ne' hzero
  obtain ⟨y₁, hy₁, heq₁⟩ := h1
  obtain ⟨y₂, hy₂, heq₂⟩ := h2
  have hylt : ψ y₂ < 0 := hy₂.2
  rw [indicator_of_mem hy₁.2] at heq₁
  rw [indicator_of_notMem (not_lt.2 hylt.le)] at heq₂
  exact ha (heq₁.trans heq₂.symm)

/-- On a Euclidean ball centered on `ker ψ` (`ψ ≠ 0`), a scalar half-space jump `{0 < ψ}` with
nonzero height `a` cannot have weak Fréchet derivative `0`. -/
private theorem not_hasWeakFDerivOn_zero_indicator_pos_ball {n : ℕ}
    {ψ : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ} (hψ : ψ ≠ 0) {y₀ : EuclideanSpace ℝ (Fin n)}
    (hy₀ : ψ y₀ = 0) {r : ℝ} (hr : 0 < r) {a : ℝ} (ha : a ≠ 0) :
    ¬ HasWeakFDerivOn volume ⟨ball y₀ r, isOpen_ball⟩
        ({y : EuclideanSpace ℝ (Fin n) | 0 < ψ y}.indicator fun _ => a) 0 := by
  let B : Opens (EuclideanSpace ℝ (Fin n)) := ⟨ball y₀ r, isOpen_ball⟩
  intro hB_weak
  have : IsFiniteMeasure (volume.restrict (ball y₀ r)) :=
    isFiniteMeasure_restrict.2 (measure_ball_lt_top (x := y₀) (r := r)).ne
  have hm : MeasurableSet {y : EuclideanSpace ℝ (Fin n) | 0 < ψ y} :=
    (isOpen_lt continuous_const ψ.continuous).measurableSet
  have hu_lp : MemLp ({y | 0 < ψ y}.indicator fun _ => a) 1 (volume.restrict (ball y₀ r)) :=
    MemLp.of_bound (aestronglyMeasurable_const.indicator hm) |a|
      (Eventually.of_forall fun y => by by_cases hy : 0 < ψ y <;> simp [hy])
  obtain ⟨w, hw_val, hw_grad⟩ :=
    W1p.exists_value_gradient_ae_eq_of_hasWeakFDerivOn (Omega := B) (p := 1) hu_lp MemLp.zero
      hB_weak
  have hw_grad0 : W1p.gradient w = 0 := by
    refine Lp.ext_iff.2 (EventuallyEq.trans ?_ (Lp.coeFn_zero _ _ _).symm)
    exact hw_grad.mono fun y hy => by simp [hy]
  obtain ⟨m, hm_const⟩ :=
    W1p.exists_value_ae_eq_const_of_gradient_eq_zero (convex_ball y₀ r).isPreconnected hw_grad0
  exact not_ae_eq_const_indicator_pos_ball hψ hy₀ hr ha (hw_val.symm.trans hm_const)

/-- **A nonzero hyperplane jump has no weak Fréchet derivative across the hyperplane.** If
`φ : E →L[ℝ] ℝ` is nonzero, `c : F` is nonzero, and `Ω` contains a point `x₀` on `ker φ`, then
`{x | 0 < φ x}.indicator (fun _ => c)` admits no weak Fréchet derivative on `Ω`. -/
theorem not_hasWeakFDerivOn_indicator_pos {φ : E →L[ℝ] ℝ} (hφ : φ ≠ 0) {c : F} (hc : c ≠ 0)
    {Ω : Opens E} {x₀ : E} (hx₀ : x₀ ∈ (Ω : Set E)) (hφ₀ : φ x₀ = 0)
    (D : E → E →L[ℝ] F) :
    ¬ HasWeakFDerivOn volume Ω ({x : E | 0 < φ x}.indicator fun _ => c) D := by
  intro hD
  have hD₀ : HasWeakFDerivOn volume Ω ({x : E | 0 < φ x}.indicator fun _ => c) 0 :=
    hD.congr_ae_deriv (ae_eq_zero_of_hasWeakFDerivOn_indicator_pos hφ hD)
  obtain ⟨ℓ, hℓ⟩ := SeparatingDual.exists_ne_zero (R := ℝ) hc
  have hℓ_weak : HasWeakFDerivOn volume Ω ({x : E | 0 < φ x}.indicator fun _ => ℓ c) 0 := by
    convert hD₀.clm_comp ℓ using 1
    · funext x
      by_cases hx : 0 < φ x <;> simp [hx]
    · funext x
      ext v
      simp
  let n := Module.finrank ℝ E
  let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] E :=
    ((EuclideanSpace.equiv (Fin n) ℝ).toLinearEquiv.trans
      (Module.finBasis ℝ E).equivFun.symm).toContinuousLinearEquiv
  let y₀ : EuclideanSpace ℝ (Fin n) := e.symm x₀
  obtain ⟨r, hr, hball⟩ :=
    Metric.isOpen_iff.1 (Ω.isOpen.preimage e.continuous) y₀ (by simp [y₀, hx₀])
  let ψ : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := φ.comp (e : EuclideanSpace ℝ (Fin n) →L[ℝ] E)
  have hψ : ψ ≠ 0 := fun h0 => hφ <| ContinuousLinearMap.ext fun x => by
    simpa [ψ] using DFunLike.congr_fun h0 (e.symm x)
  have hy₀ : ψ y₀ = 0 := by simp [ψ, y₀, hφ₀]
  refine not_hasWeakFDerivOn_zero_indicator_pos_ball hψ hy₀ hr hℓ ?_
  convert hℓ_weak.comp_continuousLinearEquiv_of_isAddHaarMeasure e (μ := volume)
    (U := ⟨ball y₀ r, isOpen_ball⟩) hball using 1
  · funext y
    simp only [Function.comp_apply, ψ, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe]
    by_cases hy : 0 < φ (e y)
    · rw [indicator_of_mem hy, indicator_of_mem hy]
    · rw [indicator_of_notMem hy, indicator_of_notMem hy]
  · funext y
    ext v
    simp

/-- **A nonzero hyperplane jump lies outside every positive-order `MemWkpLoc` class whose interior
meets the hyperplane.** -/
theorem not_memWkpLoc_indicator_pos {φ : E →L[ℝ] ℝ} (hφ : φ ≠ 0) {c : F} (hc : c ≠ 0)
    {p : ℝ≥0∞} {U : Set E} {x₀ : E} (hx₀ : x₀ ∈ interior U) (hφ₀ : φ x₀ = 0) (k : ℕ) :
    ¬ MemWkpLoc p U (k + 1) ({x : E | 0 < φ x}.indicator fun _ => c) := by
  intro h
  obtain ⟨-, D, hD, -⟩ := memWkpLoc_succ_iff.1 h
  exact not_hasWeakFDerivOn_indicator_pos hφ hc hx₀ hφ₀ D hD

end HyperplaneJump

end TauCeti
