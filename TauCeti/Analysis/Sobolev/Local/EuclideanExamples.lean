/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Basic
public import TauCeti.Analysis.Sobolev.Local.Haar
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Basic.Real.Sign
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.Analysis.InnerProductSpace.NormPow
import TauCeti.Analysis.Sobolev.Local.Coordinates
import TauCeti.Analysis.Sobolev.Local.Lipschitz
import TauCeti.Analysis.Sobolev.WeakDeriv.Lipschitz
import TauCeti.Analysis.Sobolev.WeakDeriv.MeasurePreserving
import TauCeti.Analysis.Sobolev.WeakDeriv.NormRpow
import TauCeti.Analysis.Sobolev.WeakDeriv.Removable
import TauCeti.MeasureTheory.Integral.NormRpow

/-!
# Membership and non-membership examples on finite-dimensional normed spaces

This file tests the generalized local Lebesgue and Sobolev classes `TauCeti.MemLpLoc` and
`TauCeti.MemWkpLoc` across finite-dimensional real normed domains `E` (including non-inner-product
norms), additive Haar measures, and infinite-dimensional Banach codomains `F` without a basis.

## Main examples

* **Identity, linear, and affine maps:** `id : E → E` and `x ↦ L x + c` lie in `MemWkpLoc p U k`
  for every exponent `p` and order `k` (`memWkpLoc_id_euclidean`, `memWkpLoc_affine`), while `id`
  is not globally `Lᵖ` on any nontrivial finite-dimensional space for `p ≠ 0` (`not_memLp_id`).
* **The norm `x ↦ ‖x‖`:** Lipschitz on every finite-dimensional real normed space `E`, hence in
  `MemWkpLoc p U 1` for all `p` with weak derivative bounded in operator norm by `1` almost
  everywhere (`memWkpLoc_one_norm_euclidean`, `ae_norm_le_one_of_hasWeakFDerivOn_norm`).
* **Haar scaling:** `example` checks confirm that replacing `μ` by `(2 : ℝ≥0∞) • μ` leaves
  `MemLpLoc` and `MemWkpLoc` unchanged.
* **Non-inner-product model norm (`ℝ × ℝ` vs `EuclideanSpace ℝ (Fin 2)`):** the continuous linear
  equivalence `prodEquivEuclideanSpaceFin2 : ℝ × ℝ ≃L[ℝ] EuclideanSpace ℝ (Fin 2)` carries
  `MemLpLoc` and `MemWkpLoc` between `ℝ × ℝ` (with the supremum norm `max |x₁| |x₂|` and product
  Lebesgue measure) and `EuclideanSpace ℝ (Fin 2)` (`memLpLoc_prod_iff_euclideanSpaceFin2`,
  `memWkpLoc_prod_iff_euclideanSpaceFin2`). Yet the derivatives of their norms differ sharply:
  on `ℝ × ℝ`, the derivative of `‖·‖` is `sign(x₁) dx₁` where `|x₂| < |x₁|` and `sign(x₂) dx₂`
  where `|x₁| < |x₂|`; at `(1, 1/2)` applied to `(0, 1)` it vanishes
  (`fderiv_norm_prod_one_half_apply_zero_one`), whereas the Euclidean gradient does not
  (`fderiv_norm_euclideanSpaceFin2_one_half_apply_zero_one_ne_zero`).
* **Infinite-dimensional Banach targets without a basis:** `example` checks verify that for any
  Banach space `F` (in particular `lp (fun _ : ℕ => ℝ) 2`), `x ↦ a x • v` lies in `W^{1,p}_loc`
  with weak derivative `x ↦ (Da x).smulRight v` whenever `a` is scalar `W^{1,p}_loc` with weak
  derivative `Da`.
* **Strong measurability counterexample:** `uncountableBasisMap : ℝ → lp (fun _ : ℝ => ℝ) 2`,
  `x ↦ lp.single 2 x 1`, satisfies `ℓ ∘ u =ᵐ[volume] 0` for every continuous linear functional
  `ℓ : StrongDual ℝ (lp (fun _ : ℝ => ℝ) 2)` (hence every scalar composition belongs to
  `MemWkpLoc p U k` for all `p, k`), yet `¬ MemLpLoc p U uncountableBasisMap` for every `p`
  (including `p = 0`) whenever `interior U` is nonempty, because its range is discrete and
  uncountable (`dual_comp_uncountableBasisMap_ae_eq_zero`, `not_memLpLoc_uncountableBasisMap`).
* **Inverse norm `x ↦ ‖x‖⁻¹`:** near the origin of a nontrivial finite-dimensional space `E`,
  `‖x‖⁻¹` belongs to `MemLpLoc p U μ` exactly when `p < Module.finrank ℝ E`
  (`memLpLoc_norm_inv_euclidean_iff`), with an `example` check specializing to `p < 3` on
  `EuclideanSpace ℝ (Fin 3)`.
* **Half-space indicator:** for any nonzero `ℓ : E →L[ℝ] ℝ`, the indicator of `{x | 0 < ℓ x}`
  belongs to `MemLpLoc p U μ` for every `p`, and has no weak derivative on any open set meeting
  `ker ℓ`, hence lies in no `MemWkpLoc p U (k + 1) μ` when `interior U` meets `ker ℓ`
  (`memLpLoc_indicator_clm_pos`, `not_hasWeakFDerivOn_indicator_clm_pos`,
  `not_memWkpLoc_indicator_clm_pos`).
* **Unit radial field `x ↦ ‖x‖⁻¹ • x`:** on a real inner product space `E` of dimension at least
  `2`, `x ↦ ‖x‖⁻¹ • x` belongs to `MemWkpLoc p U 1 μ` near the origin exactly when
  `p < Module.finrank ℝ E` (`memWkpLoc_one_unitRadial_iff`).
* **Radial power maps `x ↦ ‖x‖ ^ α • x`:** for `α > -1` on a real inner product space `E`,
  `x ↦ ‖x‖ ^ α • x` belongs to `MemWkpLoc p U 1 μ` whenever `x ↦ ‖x‖ ^ α` lies in `MemLpLoc p U μ`
  (`memWkpLoc_one_norm_rpow_smul_id`).

## References

* W. Arendt and M. Kreuter, *Mapping theorems for Sobolev spaces of vector-valued functions*,
  Studia Math. 240 (2018), §2, pp. 2–3.
-/

public section

noncomputable section

open MeasureTheory Metric Set TopologicalSpace Filter
open scoped ENNReal NNReal Topology Distributions RealInnerProductSpace

namespace TauCeti

/-! ### Identity, linear, and affine maps -/

section IdentityAndAffine

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℝ≥0∞} {U : Set E} {k : ℕ}

/-- The identity map on any finite-dimensional real normed space lies in `MemWkpLoc p U k` for
every exponent `p`, order `k`, and additive Haar measure `μ`. -/
theorem memWkpLoc_id_euclidean : MemWkpLoc p U k (id : E → E) μ :=
  (contDiff_id.contDiffOn : ContDiffOn ℝ k id ((⊤ : Opens E) : Set E)).memWkpLoc (subset_univ U)

/-- Every continuous affine map `x ↦ L x + c` into a Banach space lies in `MemWkpLoc p U k` for
every exponent `p`, order `k`, and additive Haar measure `μ`. -/
theorem memWkpLoc_affine [CompleteSpace F] (L : E →L[ℝ] F) (c : F) :
    MemWkpLoc p U k (fun x : E => L x + c) μ :=
  (L.contDiff.add contDiff_const).contDiffOn.memWkpLoc (Ω := ⊤) (subset_univ U)

/-- On any nontrivial finite-dimensional real normed space equipped with an additive Haar measure,
the identity map is not globally in `Lᵖ` for any `p ≠ 0` (including `p = ∞`): the class
`MemWkpLoc` is genuinely local. -/
theorem not_memLp_id [Nontrivial E] (hp : p ≠ 0) : ¬ MemLp (id : E → E) p μ := by
  intro h
  rcases eq_or_ne p ∞ with rfl | hptop
  · have hbound := eNorm_ae_le_eLpNormEssSup (id : E → E) μ
    have hlt : eLpNormEssSup (id : E → E) μ < ∞ := by
      simpa [eLpNorm_exponent_top h.aestronglyMeasurable] using h.eLpNorm_lt_top
    set R : ℝ := (eLpNormEssSup (id : E → E) μ).toReal + 1
    have hRpos : 0 < R := by linarith [ENNReal.toReal_nonneg (a := eLpNormEssSup (id : E → E) μ)]
    have hopen : IsOpen {x : E | R < ‖x‖} := isOpen_lt continuous_const continuous_norm
    obtain ⟨v, hv⟩ := exists_ne (0 : E)
    have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv
    have hne : ({x : E | R < ‖x‖}).Nonempty := by
      refine ⟨((R + 1) / ‖v‖) • v, ?_⟩
      rw [mem_ofPred_eq, norm_smul, Real.norm_of_nonneg (div_nonneg (by linarith) hvpos.le),
        div_mul_cancel₀ _ hvpos.ne']
      linarith
    have hpos : 0 < μ {x : E | R < ‖x‖} := hopen.measure_pos μ hne
    have hzero : μ {x : E | R < ‖x‖} = 0 := by
      refine measure_mono_null (fun x (hx : R < ‖x‖) => ?_) (ae_iff.1 hbound)
      simp only [mem_ofPred_eq, not_le]
      have h1 : eLpNormEssSup (id : E → E) μ < ENNReal.ofReal R := by
        rw [← ENNReal.ofReal_toReal hlt.ne]
        exact (ENNReal.ofReal_lt_ofReal_iff hRpos).2 (by linarith)
      have h2 : ENNReal.ofReal R < ‖id x‖ₑ := by
        rw [id_eq, ← ofReal_norm]
        exact (ENNReal.ofReal_lt_ofReal_iff (hRpos.trans hx)).2 hx
      exact lt_trans h1 h2
    exact hpos.ne' hzero
  · have hint : Integrable (fun x : E => ‖x‖ ^ p.toReal) μ := by
      simpa [id_eq] using (integrable_norm_rpow_iff h.aestronglyMeasurable hp hptop).2 h
    have hnot := Measure.not_integrable_norm_sub_rpow μ p.toReal (0 : E)
    simp only [sub_zero] at hnot
    exact hnot hint

end IdentityAndAffine

/-! ### The norm `x ↦ ‖x‖` on general finite-dimensional spaces -/

section NormExample

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  {p : ℝ≥0∞} {U : Set E}

/-- On any finite-dimensional real normed space `E`, the norm `x ↦ ‖x‖` is Lipschitz and therefore
lies in `MemWkpLoc p U 1` for every exponent `p` and additive Haar measure `μ`. -/
theorem memWkpLoc_one_norm_euclidean :
    MemWkpLoc p U 1 (fun x : E => ‖x‖) μ :=
  lipschitzWith_one_norm.memWkpLoc_one

/-- Every weak derivative of `x ↦ ‖x‖` on an open set `Ω ⊆ E` has operator norm at most `1` almost
everywhere. -/
theorem ae_norm_le_one_of_hasWeakFDerivOn_norm {Ω : Opens E} {D : E → E →L[ℝ] ℝ}
    (hD : HasWeakFDerivOn μ Ω (fun x : E => ‖x‖) D) :
    ∀ᵐ x ∂μ.restrict Ω, ‖D x‖ ≤ 1 := by
  have hcl : HasWeakFDerivOn μ Ω (fun x : E => ‖x‖) (fderiv ℝ fun x : E => ‖x‖) :=
    lipschitzWith_one_norm.locallyLipschitz.locallyLipschitzOn.hasWeakFDerivOn_fderiv
  filter_upwards [hD.ae_eq hcl] with x hx
  rw [hx]
  simpa using norm_fderiv_le_of_lipschitz ℝ (lipschitzWith_one_norm (E := E)) (x₀ := x)

end NormExample

/-! ### Haar scaling check -/

section HaarScaling

example {α ε : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [TopologicalSpace ε] [ENorm ε] {μ : Measure α} {p : ℝ≥0∞} {U : Set α} {f : α → ε} :
    MemLpLoc p U f ((2 : ℝ≥0∞) • μ) ↔ MemLpLoc p U f μ :=
  memLpLoc_smul_measure_iff (c := 2) two_ne_zero ENNReal.ofNat_ne_top

example {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] {μ : Measure E} {p : ℝ≥0∞}
    {U : Set E} {k : ℕ} {f : E → F} :
    MemWkpLoc p U k f ((2 : ℝ≥0∞) • μ) ↔ MemWkpLoc p U k f μ :=
  memWkpLoc_smul_measure_iff (c := 2) two_ne_zero ENNReal.ofNat_ne_top

end HaarScaling

/-! ### Non-inner-product model norm: `ℝ × ℝ` vs `EuclideanSpace ℝ (Fin 2)` -/

section NonInnerProductModel

/-- The canonical continuous linear equivalence between `ℝ × ℝ` (with the supremum norm
`‖(x, y)‖ = max |x| |y|`) and `EuclideanSpace ℝ (Fin 2)` (with the Euclidean `ℓ²` norm). -/
def prodEquivEuclideanSpaceFin2 : (ℝ × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (LinearEquiv.toContinuousLinearEquiv
    { toFun := fun p : ℝ × ℝ => ![p.1, p.2]
      invFun := fun f : Fin 2 → ℝ => (f 0, f 1)
      left_inv := fun ⟨_, _⟩ => rfl
      right_inv := fun f => by ext i; fin_cases i <;> rfl
      map_add' := fun p q => by ext i; fin_cases i <;> rfl
      map_smul' := fun c p => by ext i; fin_cases i <;> rfl }).trans
    (EuclideanSpace.equiv (Fin 2) ℝ).symm

/-- The `0`-th coordinate of `prodEquivEuclideanSpaceFin2 p` is `p.1`. -/
@[simp]
theorem prodEquivEuclideanSpaceFin2_apply_zero (p : ℝ × ℝ) :
    prodEquivEuclideanSpaceFin2 p 0 = p.1 := by
  rfl

/-- The `1`-st coordinate of `prodEquivEuclideanSpaceFin2 p` is `p.2`. -/
@[simp]
theorem prodEquivEuclideanSpaceFin2_apply_one (p : ℝ × ℝ) :
    prodEquivEuclideanSpaceFin2 p 1 = p.2 := by
  rfl

/-- Local `Lᵖ` membership on `ℝ × ℝ` (with the supremum norm and product Lebesgue measure) matches
`EuclideanSpace ℝ (Fin 2)` under `prodEquivEuclideanSpaceFin2`. -/
theorem memLpLoc_prod_iff_euclideanSpaceFin2 {ε : Type*} [TopologicalSpace ε] [ContinuousENorm ε]
    {p : ℝ≥0∞} {V : Set (EuclideanSpace ℝ (Fin 2))} {u : EuclideanSpace ℝ (Fin 2) → ε} :
    MemLpLoc p (prodEquivEuclideanSpaceFin2 ⁻¹' V) (u ∘ prodEquivEuclideanSpaceFin2) volume ↔
      MemLpLoc p V u volume := by
  have : Measure.IsAddHaarMeasure (volume : Measure (ℝ × ℝ)) :=
    Measure.prod.instIsAddHaarMeasure _ _
  exact prodEquivEuclideanSpaceFin2.memLpLoc_comp_preimage_iff

/-- Local Sobolev membership on `ℝ × ℝ` (with the supremum norm and product Lebesgue measure)
matches `EuclideanSpace ℝ (Fin 2)` under `prodEquivEuclideanSpaceFin2`. -/
theorem memWkpLoc_prod_iff_euclideanSpaceFin2 {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {p : ℝ≥0∞} {V : Set (EuclideanSpace ℝ (Fin 2))} {k : ℕ}
    {u : EuclideanSpace ℝ (Fin 2) → F} :
    MemWkpLoc p (prodEquivEuclideanSpaceFin2 ⁻¹' V) k (u ∘ prodEquivEuclideanSpaceFin2) volume ↔
      MemWkpLoc p V k u volume := by
  have : Measure.IsAddHaarMeasure (volume : Measure (ℝ × ℝ)) :=
    Measure.prod.instIsAddHaarMeasure _ _
  exact prodEquivEuclideanSpaceFin2.memWkpLoc_comp_preimage_iff

/-- On the open region `{y : ℝ × ℝ | |y.2| < |y.1|}`, the supremum norm `y ↦ max |y.1| |y.2|` has
Fréchet derivative `Real.sign y.1 • dx₁`. -/
theorem hasFDerivAt_norm_prod_of_abs_snd_lt_abs_fst {y : ℝ × ℝ} (hy : |y.2| < |y.1|) :
    HasFDerivAt (fun z : ℝ × ℝ => ‖z‖)
      (Real.sign y.1 • ContinuousLinearMap.fst ℝ ℝ ℝ) y := by
  have hy1 : y.1 ≠ 0 := by intro h; simp [h] at hy; linarith [abs_nonneg y.2]
  have hopen : IsOpen {z : ℝ × ℝ | |z.2| < |z.1|} :=
    isOpen_lt (continuous_abs.comp continuous_snd) (continuous_abs.comp continuous_fst)
  have heq : (fun z : ℝ × ℝ => ‖z‖) =ᶠ[𝓝 y] (fun z : ℝ × ℝ => |z.1|) := by
    filter_upwards [hopen.mem_nhds hy] with z hz
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, max_eq_left hz.le]
  refine HasFDerivAt.congr_of_eventuallyEq ?_ heq
  rcases lt_or_gt_of_ne hy1 with hlt | hgt
  · have heq2 : (fun z : ℝ × ℝ => |z.1|) =ᶠ[𝓝 y] (fun z : ℝ × ℝ => -z.1) := by
      filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds hlt] with z hz
      exact abs_of_neg hz
    refine ((ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.neg.congr_of_eventuallyEq heq2).congr_fderiv
      ?_
    rw [Real.sign_of_neg hlt]; ext <;> simp
  · have heq2 : (fun z : ℝ × ℝ => |z.1|) =ᶠ[𝓝 y] (fun z : ℝ × ℝ => z.1) := by
      filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hgt] with z hz
      exact abs_of_pos hz
    refine ((ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.congr_of_eventuallyEq heq2).congr_fderiv ?_
    rw [Real.sign_of_pos hgt, one_smul]

/-- On the open region `{y : ℝ × ℝ | |y.1| < |y.2|}`, the supremum norm `y ↦ max |y.1| |y.2|` has
Fréchet derivative `Real.sign y.2 • dx₂`. -/
theorem hasFDerivAt_norm_prod_of_abs_fst_lt_abs_snd {y : ℝ × ℝ} (hy : |y.1| < |y.2|) :
    HasFDerivAt (fun z : ℝ × ℝ => ‖z‖)
      (Real.sign y.2 • ContinuousLinearMap.snd ℝ ℝ ℝ) y := by
  have hy2 : y.2 ≠ 0 := by intro h; simp [h] at hy; linarith [abs_nonneg y.1]
  have hopen : IsOpen {z : ℝ × ℝ | |z.1| < |z.2|} :=
    isOpen_lt (continuous_abs.comp continuous_fst) (continuous_abs.comp continuous_snd)
  have heq : (fun z : ℝ × ℝ => ‖z‖) =ᶠ[𝓝 y] (fun z : ℝ × ℝ => |z.2|) := by
    filter_upwards [hopen.mem_nhds hy] with z hz
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, max_eq_right hz.le]
  refine HasFDerivAt.congr_of_eventuallyEq ?_ heq
  rcases lt_or_gt_of_ne hy2 with hlt | hgt
  · have heq2 : (fun z : ℝ × ℝ => |z.2|) =ᶠ[𝓝 y] (fun z : ℝ × ℝ => -z.2) := by
      filter_upwards [(isOpen_lt continuous_snd continuous_const).mem_nhds hlt] with z hz
      exact abs_of_neg hz
    refine ((ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.neg.congr_of_eventuallyEq heq2).congr_fderiv
      ?_
    rw [Real.sign_of_neg hlt]; ext <;> simp
  · have heq2 : (fun z : ℝ × ℝ => |z.2|) =ᶠ[𝓝 y] (fun z : ℝ × ℝ => z.2) := by
      filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds hgt] with z hz
      exact abs_of_pos hz
    refine ((ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.congr_of_eventuallyEq heq2).congr_fderiv ?_
    rw [Real.sign_of_pos hgt, one_smul]

/-- At `x = (1, 1/2)`, the derivative of the supremum norm on `ℝ × ℝ` in the direction `(0, 1)`
vanishes. -/
theorem fderiv_norm_prod_one_half_apply_zero_one :
    fderiv ℝ (fun y : ℝ × ℝ => ‖y‖) (1, (1 / 2 : ℝ)) (0, 1) = 0 := by
  have h := hasFDerivAt_norm_prod_of_abs_snd_lt_abs_fst
    (y := (1, (1 / 2 : ℝ))) (by norm_num)
  rw [h.fderiv]
  simp

/-- At the corresponding point `(1, 1/2)` in `EuclideanSpace ℝ (Fin 2)`, the derivative of the
Euclidean norm in the direction `(0, 1)` is strictly positive (in particular nonzero), contrasting
with `fderiv_norm_prod_one_half_apply_zero_one`. -/
theorem fderiv_norm_euclideanSpaceFin2_one_half_apply_zero_one_ne_zero :
    fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 2) => ‖y‖)
      (prodEquivEuclideanSpaceFin2 (1, (1 / 2 : ℝ)))
      (prodEquivEuclideanSpaceFin2 (0, 1)) ≠ 0 := by
  set x : EuclideanSpace ℝ (Fin 2) := prodEquivEuclideanSpaceFin2 (1, (1 / 2 : ℝ))
  set v : EuclideanSpace ℝ (Fin 2) := prodEquivEuclideanSpaceFin2 (0, 1)
  have hx : x ≠ 0 := by
    intro h
    have h0 := congrArg (fun f : EuclideanSpace ℝ (Fin 2) => f 0) h
    norm_num [x] at h0
  have hd : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin 2) => ‖y‖) (‖x‖⁻¹ • innerSL ℝ x) x :=
    hasFDerivAt_norm_of_ne hx
  rw [hd.fderiv, smul_apply, innerSL_apply_apply, smul_eq_mul]
  have hinner : ⟪x, v⟫ = (1 / 2 : ℝ) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [Fin.sum_univ_two, x, v, dotProduct]
  rw [hinner]
  exact mul_ne_zero (inv_ne_zero (norm_ne_zero_iff.2 hx)) (by norm_num)

end NonInnerProductModel

/-! ### Infinite-dimensional Banach targets without a basis -/

section BanachTarget

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {μ : Measure E} {p : ℝ≥0∞} {U : Set E}

-- Banach-valued scalar products `x ↦ a x • v` need no basis, separability, or inner product on `F`.
example {a : E → ℝ} (ha : MemWkpLoc p U 1 a μ) (v : F) :
    MemWkpLoc p U 1 (fun x => a x • v) μ :=
  ha.smul_const v

example {Ω : Opens E} {a : E → ℝ} {Da : E → E →L[ℝ] ℝ}
    (hDa : HasWeakFDerivOn μ Ω a Da) (v : F) :
    HasWeakFDerivOn μ Ω (fun x => a x • v) (fun x => (Da x).smulRight v) := by
  let L : ℝ →L[ℝ] F := ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) v
  have h1 : (fun x => L (a x)) = fun x => a x • v := by funext x; simp [L]
  have h2 : (fun x => L.comp (Da x)) = fun x => (Da x).smulRight v := by
    funext x
    exact ContinuousLinearMap.ext fun w => by simp [L]
  simpa only [h1, h2] using hDa.clm_comp L

-- Specialization to the infinite-dimensional Hilbert space `ℓ²(ℕ, ℝ)`.
example {a : E → ℝ} {Da : E → E →L[ℝ] ℝ} (ha : MemWkpLoc p U 1 a μ)
    (hDa : HasWeakFDerivOn μ (Opens.interior U) a Da) (v : lp (fun _ : ℕ => ℝ) 2) :
    MemWkpLoc p U 1 (fun x => a x • v) μ ∧
      HasWeakFDerivOn μ (Opens.interior U) (fun x => a x • v)
        (fun x => (Da x).smulRight v) := by
  refine ⟨ha.smul_const v, ?_⟩
  let L : ℝ →L[ℝ] lp (fun _ : ℕ => ℝ) 2 := ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) v
  have h1 : (fun x => L (a x)) = fun x => a x • v := by funext x; simp [L]
  have h2 : (fun x => L.comp (Da x)) = fun x => (Da x).smulRight v := by
    funext x
    exact ContinuousLinearMap.ext fun w => by simp [L]
  simpa only [h1, h2] using hDa.clm_comp L

end BanachTarget

/-! ### Strong measurability counterexample: weakly zero a.e., not locally `Lᵖ` -/

section WeaklyZeroCounterexample

/-- The map `x ↦ eₓ` sending each real number to the corresponding standard basis vector in the
non-separable Hilbert space `ℓ²(ℝ, ℝ)`. Every scalar composition `ℓ ∘ u` vanishes outside a
countable set, yet `u` fails strong measurability and hence belongs to no `MemLpLoc p U` when
`interior U` is nonempty. -/
def uncountableBasisMap (x : ℝ) : lp (fun _ : ℝ => ℝ) 2 :=
  lp.single 2 x (1 : ℝ)

/-- Every continuous linear functional on `ℓ²(ℝ, ℝ)` vanishes almost everywhere when composed with
`uncountableBasisMap`. -/
theorem dual_comp_uncountableBasisMap_ae_eq_zero
    (ℓ : StrongDual ℝ (lp (fun _ : ℝ => ℝ) 2)) :
    (fun x : ℝ => ℓ (uncountableBasisMap x)) =ᵐ[volume] 0 := by
  obtain ⟨g, hg⟩ : ∃ g : lp (fun _ : ℝ => ℝ) 2, ∀ y, ℓ y = ⟪g, y⟫ :=
    ⟨(InnerProductSpace.toDual ℝ (lp (fun _ : ℝ => ℝ) 2)).symm ℓ, fun y => by
      simp [InnerProductSpace.toDual_symm_apply]⟩
  have hsum : Summable (fun x : ℝ => ‖g x‖ ^ (2 : ℝ)) := by
    have h2 : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
    simpa [ENNReal.toReal_ofNat] using (lp.memℓp g).summable h2
  have hcnt : {x : ℝ | ℓ (uncountableBasisMap x) ≠ 0}.Countable := by
    refine hsum.countable_support.mono fun x hx => ?_
    simp only [Function.mem_support, ne_eq]
    have hgx : g x ≠ 0 := by
      have hval : ℓ (uncountableBasisMap x) = g x := by
        rw [hg, uncountableBasisMap, lp.inner_single_right]
        simp
      exact hval ▸ hx
    exact (Real.rpow_pos_of_pos (norm_pos_iff.2 hgx) _).ne'
  rw [Filter.EventuallyEq, ae_iff]
  exact hcnt.measure_zero volume

/-- Every continuous scalar composition of `uncountableBasisMap` lies in `MemWkpLoc p U k` for
every exponent `p`, set `U`, and order `k`. -/
theorem memWkpLoc_dual_comp_uncountableBasisMap
    (ℓ : StrongDual ℝ (lp (fun _ : ℝ => ℝ) 2)) (p : ℝ≥0∞) (U : Set ℝ) (k : ℕ) :
    MemWkpLoc p U k (fun x : ℝ => ℓ (uncountableBasisMap x)) volume :=
  (memWkpLoc_zero_fun (μ := volume)).congr_ae
    (ae_restrict_of_ae (dual_comp_uncountableBasisMap_ae_eq_zero ℓ).symm)

private lemma dist_uncountableBasisMap_of_ne {x y : ℝ} (hxy : x ≠ y) :
    1 ≤ dist (uncountableBasisMap x) (uncountableBasisMap y) := by
  rw [dist_eq_norm]
  have h1 : ‖(uncountableBasisMap x - uncountableBasisMap y) x‖ ≤
      ‖uncountableBasisMap x - uncountableBasisMap y‖ :=
    lp.norm_apply_le_norm (by norm_num) _ x
  have hval : (uncountableBasisMap x - uncountableBasisMap y) x = 1 := by
    simp [uncountableBasisMap, lp.single_apply, hxy.symm]
  rw [hval, norm_one] at h1
  exact h1

/-- `uncountableBasisMap` fails `MemLpLoc p U` for every exponent `p` (even `p = 0`) on any set
`U ⊆ ℝ` with nonempty interior: weak scalar membership does not imply strong measurability. -/
theorem not_memLpLoc_uncountableBasisMap (p : ℝ≥0∞) {U : Set ℝ} (hU : (interior U).Nonempty) :
    ¬ MemLpLoc p U uncountableBasisMap volume := by
  intro h
  obtain ⟨x₀, hx₀⟩ := hU
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 isOpen_interior x₀ hx₀
  set K : Set ℝ := Icc (x₀ - r / 2) (x₀ + r / 2)
  have hKU : K ⊆ U := fun x hx => by
    apply interior_subset
    apply hball
    rw [mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hx.1, hx.2]
  have hmeas : AEStronglyMeasurable uncountableBasisMap (volume.restrict K) :=
    (memLpLoc_iff.1 h K hKU isCompact_Icc).aestronglyMeasurable
  obtain ⟨S, hSsep, hSae⟩ := hmeas.isSeparable_ae_range
  obtain ⟨D, hDcnt, hDdense⟩ := hSsep
  set T : Set ℝ := K ∩ {x : ℝ | uncountableBasisMap x ∈ S}
  have hTcnt : T.Countable := by
    have hDmap : ∀ x : T, ∃ d ∈ D, dist (uncountableBasisMap x.val) d < 1 / 2 := fun ⟨x, hx⟩ => by
      obtain ⟨d, hdD, hd⟩ := Metric.mem_closure_iff.1 (hDdense hx.2) (1 / 2) (by norm_num)
      exact ⟨d, hdD, hd⟩
    choose f hfD hfd using hDmap
    have hinj : Function.Injective f := by
      intro x y hxy
      by_contra hne
      have hne' : x.val ≠ y.val := fun h => hne (Subtype.ext h)
      have h1 : 1 ≤ dist (uncountableBasisMap x.val) (uncountableBasisMap y.val) :=
        dist_uncountableBasisMap_of_ne hne'
      have htri := dist_triangle_right (uncountableBasisMap x.val) (uncountableBasisMap y.val) (f x)
      have hfdx := hfd x
      rw [hxy] at htri hfdx
      linarith [hfdx, hfd y]
    have : Countable D := hDcnt.to_subtype
    have : Countable T :=
      Function.Injective.countable (f := fun x : T => (⟨f x, hfD x⟩ : D)) fun x y h =>
        hinj (congrArg Subtype.val h)
    exact Set.to_countable T
  have hTnull : volume.restrict K T = 0 :=
    le_antisymm ((Measure.restrict_apply_le K T).trans_eq (hTcnt.measure_zero volume)) zero_le
  have hKpos : 0 < volume K := by
    simp only [K, Real.volume_Icc]
    exact ENNReal.ofReal_pos.2 (by linarith)
  have hKeq : volume K = volume.restrict K T := by
    rw [← Measure.restrict_apply_univ K]
    refine measure_congr ?_
    filter_upwards [hSae, ae_restrict_mem measurableSet_Icc] with x hxS hxK
    simp only [mem_univ, true_iff, T]
    exact ⟨hxK, hxS⟩
  exact hKpos.ne' (hKeq.trans hTnull)

end WeaklyZeroCounterexample

/-! ### The inverse norm `x ↦ ‖x‖⁻¹` on general finite-dimensional spaces -/

section InverseNorm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  {p : ℝ≥0∞} {U : Set E}

/-- On a nontrivial finite-dimensional real normed space `E`, `x ↦ ‖x‖⁻¹` belongs to
`MemLpLoc p U μ` on a neighbourhood `U` of `0` exactly when `p < Module.finrank ℝ E`. -/
theorem memLpLoc_norm_inv_euclidean_iff [Nontrivial E] (hU : U ∈ 𝓝 (0 : E)) :
    MemLpLoc p U (fun x : E => ‖x‖⁻¹) μ ↔ p < Module.finrank ℝ E := by
  constructor
  · intro h
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hU
    have hK : closedBall (0 : E) (r / 2) ⊆ U :=
      (closedBall_subset_ball (by linarith)).trans hball
    by_contra hp
    exact not_memLp_norm_inv_closedBall (mu := μ) (half_pos hr) (not_lt.1 hp)
      (memLpLoc_iff.1 h _ hK (isCompact_closedBall 0 _))
  · intro hp
    exact memLpLoc_iff.2 fun K _ hK => hK.isBounded.memLp_norm_inv_restrict (mu := μ) hp

-- In dimension `3`, `x ↦ ‖x‖⁻¹` belongs to `MemLpLoc p U volume` near `0` iff `p < 3`.
example {U : Set (EuclideanSpace ℝ (Fin 3))}
    (hU : U ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin 3))) :
    MemLpLoc p U (fun x : EuclideanSpace ℝ (Fin 3) => ‖x‖⁻¹) volume ↔ p < 3 := by
  simpa [finrank_euclideanSpace_fin] using memLpLoc_norm_inv_euclidean_iff (μ := volume) hU

end InverseNorm

/-! ### Half-space indicator on general finite-dimensional spaces -/

section HalfSpaceIndicator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} {p : ℝ≥0∞} {U : Set E}

/-- The indicator of the open half-space `{x : E | 0 < ℓ x}` is locally `Lᵖ` on every set `U`,
for every exponent `p`, continuous linear functional `ℓ`, and measure `μ` finite on compacts. -/
theorem memLpLoc_indicator_clm_pos [IsFiniteMeasureOnCompacts μ] (ℓ : E →L[ℝ] ℝ) :
    MemLpLoc p U ({x : E | 0 < ℓ x}.indicator fun _ => (1 : ℝ)) μ := by
  refine memLpLoc_iff.2 fun K _ hK => ?_
  have : IsFiniteMeasure (μ.restrict K) := ⟨by simpa using hK.measure_lt_top⟩
  exact memLp_indicator_const p
    (isOpen_lt continuous_const ℓ.continuous).measurableSet.nullMeasurableSet 1
    (Or.inr (measure_ne_top _ _))

/-- On `ℝ × EuclideanSpace ℝ (Fin m)`, the indicator of `{q | 0 < q.1}` has no weak derivative on
any open set meeting `{0} × EuclideanSpace ℝ (Fin m)`. -/
private theorem not_hasWeakFDerivOn_indicator_fst_pos {m : ℕ}
    {Ω : Opens (ℝ × EuclideanSpace ℝ (Fin m))}
    {y₀ : EuclideanSpace ℝ (Fin m)} (hy₀ : ((0 : ℝ), y₀) ∈ Ω)
    (D : (ℝ × EuclideanSpace ℝ (Fin m)) → (ℝ × EuclideanSpace ℝ (Fin m)) →L[ℝ] ℝ) :
    ¬ HasWeakFDerivOn (volume : Measure (ℝ × EuclideanSpace ℝ (Fin m))) Ω
        ({q : ℝ × EuclideanSpace ℝ (Fin m) | 0 < q.1}.indicator fun _ => (1 : ℝ)) D := by
  intro hD
  -- Step 1: On `q.1 > 0` and `q.1 < 0`, `u` is locally constant, so `D = 0` a.e. on `Ω`
  -- once we discard the hyperplane `{q | q.1 = 0}`.
  have : Measure.IsAddHaarMeasure (volume : Measure (ℝ × EuclideanSpace ℝ (Fin m))) :=
    Measure.prod.instIsAddHaarMeasure _ _
  let u : ℝ × EuclideanSpace ℝ (Fin m) → ℝ :=
    {q : ℝ × EuclideanSpace ℝ (Fin m) | 0 < q.1}.indicator fun _ => (1 : ℝ)
  set Ωp : Opens (ℝ × EuclideanSpace ℝ (Fin m)) :=
    Ω ⊓ ⟨{q | 0 < q.1}, isOpen_lt continuous_const continuous_fst⟩
  set Ωn : Opens (ℝ × EuclideanSpace ℝ (Fin m)) :=
    Ω ⊓ ⟨{q | q.1 < 0}, isOpen_lt continuous_fst continuous_const⟩
  have hconst : HasWeakFDerivOn (volume : Measure (ℝ × EuclideanSpace ℝ (Fin m))) Ωp
      (fun _ => (1 : ℝ)) 0 :=
    hasWeakFDerivOn_iff.2 fun v => by
      simpa using (hasWeakLineDerivOn_const (1 : ℝ) :
        HasWeakLineDerivOn (volume : Measure (ℝ × EuclideanSpace ℝ (Fin m))) Ωp
          (fun _ => (1 : ℝ)) (fun _ => 0) v)
  have hp : HasWeakFDerivOn (volume : Measure (ℝ × EuclideanSpace ℝ (Fin m))) Ωp u 0 :=
    hconst.congr_ae <| (ae_restrict_iff' Ωp.isOpen.measurableSet).2 <|
      Eventually.of_forall fun q hq => by
        have hq' : q ∈ {q : ℝ × EuclideanSpace ℝ (Fin m) | 0 < q.1} := hq.2
        exact (Set.indicator_of_mem hq' (fun _ => (1 : ℝ))).symm
  have hn : HasWeakFDerivOn (volume : Measure (ℝ × EuclideanSpace ℝ (Fin m))) Ωn u 0 :=
    (hasWeakFDerivOn_zero (μ := (volume : Measure (ℝ × EuclideanSpace ℝ (Fin m))))).congr_ae <|
      (ae_restrict_iff' Ωn.isOpen.measurableSet).2 <| Eventually.of_forall fun q hq => by
        have hq' : q.1 < 0 := hq.2
        have hnot : ¬ (0 < q.1) := not_lt.2 hq'.le
        simp [u, hnot]
  have hDp := (ae_restrict_iff' Ωp.isOpen.measurableSet).1 ((hD.mono inf_le_left).ae_eq hp)
  have hDn := (ae_restrict_iff' Ωn.isOpen.measurableSet).1 ((hD.mono inf_le_left).ae_eq hn)
  have hker_null :
      (volume : Measure (ℝ × EuclideanSpace ℝ (Fin m))) {q | q.1 = 0} = 0 := by
    have hsub : LinearMap.ker (LinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin m))) ≠ ⊤ := by
      intro htop
      have : ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin m))) ∈
          LinearMap.ker (LinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin m))) := htop ▸ trivial
      simp at this
    exact Measure.addHaar_submodule volume
      (LinearMap.ker (LinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin m)))) hsub
  have hD0 : D =ᵐ[(volume : Measure (ℝ × EuclideanSpace ℝ (Fin m))).restrict Ω] 0 := by
    refine (ae_restrict_iff' Ω.isOpen.measurableSet).2 ?_
    filter_upwards [hDp, hDn, measure_eq_zero_iff_ae_notMem.1 hker_null] with q hqp hqn hq0 hqΩ
    rcases lt_or_gt_of_ne hq0 with h | h
    · exact hqn ⟨hqΩ, h⟩
    · exact hqp ⟨hqΩ, h⟩
  -- Step 2: Test against a product bump function `φ (t, y) = a t * b y` centered at `(0, y₀)`.
  have hline := (hD.congr_ae_deriv hD0).hasWeakLineDerivOn
    ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin m)))
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 Ω.isOpen ((0 : ℝ), y₀) hy₀
  let a : ContDiffBump (0 : ℝ) := ⟨ε / 6, ε / 3, by positivity, by linarith⟩
  let b : ContDiffBump y₀ := ⟨ε / 6, ε / 3, by positivity, by linarith⟩
  let f : ℝ × EuclideanSpace ℝ (Fin m) → ℝ := fun q => a q.1 * b q.2
  have hfs : tsupport f ⊆ closedBall ((0 : ℝ), y₀) (ε / 3) := by
    intro q hq
    have hq1 : q ∈ Prod.fst ⁻¹' tsupport a :=
      tsupport_comp_subset_preimage (a : ℝ → ℝ) continuous_fst (tsupport_mul_subset_left hq)
    have hq2 : q ∈ Prod.snd ⁻¹' tsupport b :=
      tsupport_comp_subset_preimage (b : EuclideanSpace ℝ (Fin m) → ℝ) continuous_snd
        (tsupport_mul_subset_right hq)
    rw [mem_preimage, a.tsupport_eq, mem_closedBall] at hq1
    rw [mem_preimage, b.tsupport_eq, mem_closedBall] at hq2
    rw [mem_closedBall, Prod.dist_eq]
    exact max_le hq1 hq2
  have hfΩ : tsupport f ⊆ Ω := fun q hq =>
    hball (closedBall_subset_ball (by linarith) (hfs hq))
  let φ : 𝓓(Ω, ℝ) := ⟨f, (a.contDiff.comp contDiff_fst).mul (b.contDiff.comp contDiff_snd),
    (isCompact_closedBall _ _).of_isClosed_subset (isClosed_tsupport f) hfs, hfΩ⟩
  have hφ : (φ : ℝ × EuclideanSpace ℝ (Fin m) → ℝ) = f := TestFunction.coe_mk
  have hkey := hline.integral_lineDeriv_smul_eq_neg_integral_smul φ
  simp only [Pi.zero_apply, zero_apply, smul_zero, integral_zero, neg_zero] at hkey
  -- Step 3: Factor the integral by Fubini; `∫_{t>0} a'(t) dt = -a(0) = -1` and `∫ b > 0`.
  have hda : ∀ t, HasDerivAt a (deriv a t) t := fun t =>
    ((a.contDiff (n := 1)).differentiable one_ne_zero t).hasDerivAt
  have hldf : ∀ q : ℝ × EuclideanSpace ℝ (Fin m),
      lineDeriv ℝ (φ : ℝ × EuclideanSpace ℝ (Fin m) → ℝ) q ((1 : ℝ), 0) =
        deriv a q.1 * b q.2 := fun q => by
    refine HasLineDerivAt.lineDeriv
      (?_ : HasDerivAt (fun t : ℝ =>
        (φ : ℝ × EuclideanSpace ℝ (Fin m) → ℝ) (q + t • ((1 : ℝ), 0))) _ 0)
    have h := ((hda (q.1 + 0)).comp_const_add q.1 0).mul_const (b q.2)
    simp only [add_zero] at h
    convert h using 1
    funext t
    simp [hφ, f]
  have hint :
      ∫ q : ℝ × EuclideanSpace ℝ (Fin m),
          lineDeriv ℝ (φ : ℝ × EuclideanSpace ℝ (Fin m) → ℝ) q ((1 : ℝ), 0) • u q =
        ∫ q : ℝ × EuclideanSpace ℝ (Fin m),
          (deriv a q.1 * (Ioi (0 : ℝ)).indicator 1 q.1) * b q.2 := by
    refine integral_congr_ae (Eventually.of_forall fun q => ?_)
    simp only [hldf, smul_eq_mul, u]
    by_cases hq : 0 < q.1 <;> simp [Set.indicator, hq]
  have hprod := integral_prod_mul (μ := (volume : Measure ℝ))
    (ν := (volume : Measure (EuclideanSpace ℝ (Fin m))))
    (fun t => deriv a t * (Ioi (0 : ℝ)).indicator 1 t) (fun y => b y)
  rw [hint, Measure.volume_eq_prod, hprod] at hkey
  have hIoi : ∫ t : ℝ, deriv a t * (Ioi (0 : ℝ)).indicator 1 t = -1 := by
    have hfun : (fun t : ℝ => deriv a t * (Ioi (0 : ℝ)).indicator 1 t) =
        (Ioi (0 : ℝ)).indicator (deriv a) := by
      funext t; by_cases ht : 0 < t <;> simp [Set.indicator, ht]
    rw [hfun, integral_indicator measurableSet_Ioi]
    have hdc : Continuous (deriv a) := (a.contDiff (n := 1)).continuous_deriv le_rfl
    rw [integral_Ioi_of_hasDerivAt_of_tendsto (m := 0) a.continuous.continuousWithinAt
      (fun t _ => hda t)
      (hdc.integrable_of_hasCompactSupport a.hasCompactSupport.deriv).integrableOn ?_,
      a.one_of_mem_closedBall (mem_closedBall_self (by simp only [a]; positivity))]
    · simp
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop (ε / 3)] with t ht
      refine (a.zero_of_le_dist ?_).symm
      simp only [a, Real.dist_eq, sub_zero]
      have ht0 : 0 ≤ t := by linarith
      rw [abs_of_nonneg ht0]
      exact ht
  have hbpos : 0 < ∫ y : EuclideanSpace ℝ (Fin m), (b : EuclideanSpace ℝ (Fin m) → ℝ) y := by
    rw [integral_pos_iff_support_of_nonneg (fun y => b.nonneg)
      (b.continuous.integrable_of_hasCompactSupport b.hasCompactSupport)]
    have hopen : IsOpen (Function.support (b : EuclideanSpace ℝ (Fin m) → ℝ)) :=
      isOpen_ne_fun b.continuous continuous_const
    refine hopen.measure_pos volume ⟨y₀, ?_⟩
    simp [Function.mem_support, b.one_of_mem_closedBall
      (mem_closedBall_self (by simp only [b]; positivity))]
  rw [hIoi] at hkey
  linarith

/-- For any nonzero continuous linear functional `ℓ : E →L[ℝ] ℝ` on a finite-dimensional real
normed space `E`, the indicator of the half-space `{x : E | 0 < ℓ x}` has no weak derivative on
any open set meeting `ker ℓ`. -/
theorem not_hasWeakFDerivOn_indicator_clm_pos [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure]
    {ℓ : E →L[ℝ] ℝ} (hℓ : ℓ ≠ 0) {Ω : Opens E} {x₀ : E} (hx₀ : x₀ ∈ Ω) (hker : ℓ x₀ = 0)
    (D : E → E →L[ℝ] ℝ) :
    ¬ HasWeakFDerivOn μ Ω ({x : E | 0 < ℓ x}.indicator fun _ => (1 : ℝ)) D := by
  intro hD
  obtain ⟨w, hw⟩ : ∃ w : E, ℓ w ≠ 0 := by
    by_contra h
    push Not at h
    exact hℓ (by ext x; exact h x)
  let v : E := (ℓ w)⁻¹ • w
  have hv : ℓ v = 1 := by simp [v, inv_mul_cancel₀ hw]
  set K := LinearMap.ker ℓ.toLinearMap
  let m : ℕ := Module.finrank ℝ K
  let bK : EuclideanSpace ℝ (Fin m) ≃L[ℝ] K :=
    (EuclideanSpace.equiv (Fin m) ℝ).trans (Module.finBasis ℝ K).equivFunL.symm
  let eLin : (ℝ × EuclideanSpace ℝ (Fin m)) ≃ₗ[ℝ] E :=
    { toFun := fun q => q.1 • v + (bK q.2 : E)
      invFun := fun x => (ℓ x, bK.symm ⟨x - ℓ x • v, by simp [K, hv]⟩)
      left_inv := fun ⟨t, y⟩ => by
        have hby : ℓ (bK y : E) = 0 := (bK y).property
        ext
        · simp [hv, hby]
        · simp only [map_add, map_smul, hv, hby, smul_eq_mul, mul_one, add_zero,
            add_sub_cancel_left]
          exact congrArg (fun z : EuclideanSpace ℝ (Fin m) => z _) (bK.symm_apply_apply y)
      right_inv := fun x => by simp
      map_add' := fun q r => by
        simp only [Prod.fst_add, Prod.snd_add, add_smul, map_add, Submodule.coe_add]
        abel
      map_smul' := fun c q => by
        simp only [Prod.smul_fst, Prod.smul_snd, map_smul, Submodule.coe_smul,
          RingHom.id_apply, smul_add, smul_smul, smul_eq_mul] }
  let e : (ℝ × EuclideanSpace ℝ (Fin m)) ≃L[ℝ] E := eLin.toContinuousLinearEquiv
  have hℓe : ∀ q : ℝ × EuclideanSpace ℝ (Fin m), ℓ (e q) = q.1 := fun ⟨t, y⟩ => by
    have hby : ℓ (bK y : E) = 0 := (bK y).property
    simp [e, eLin, hv, hby]
  set Ω' : Opens (ℝ × EuclideanSpace ℝ (Fin m)) :=
    ⟨e ⁻¹' (Ω : Set E), Ω.isOpen.preimage e.continuous⟩
  have : Measure.IsAddHaarMeasure (volume : Measure (ℝ × EuclideanSpace ℝ (Fin m))) :=
    Measure.prod.instIsAddHaarMeasure _ _
  have hpull := hD.comp_continuousLinearEquiv
    (μ := (volume : Measure (ℝ × EuclideanSpace ℝ (Fin m)))) (V := Ω) (U := Ω') e
    (mapsTo_preimage e Ω)
  have hcomp : ({x : E | 0 < ℓ x}.indicator fun _ => (1 : ℝ)) ∘ e =
      {q : ℝ × EuclideanSpace ℝ (Fin m) | 0 < q.1}.indicator fun _ => (1 : ℝ) := by
    funext q
    simp only [Function.comp_apply, Set.indicator, Set.mem_ofPred_eq, hℓe]
  rw [hcomp] at hpull
  have heq : e (0, bK.symm ⟨x₀, by simp [K, hker]⟩) = x₀ := by simp [e, eLin]
  have hy₀ : ((0 : ℝ), bK.symm ⟨x₀, by simp [K, hker]⟩) ∈ Ω' := by
    simpa [Ω', SetLike.mem_coe, heq] using hx₀
  exact not_hasWeakFDerivOn_indicator_fst_pos hy₀ _ hpull

/-- The indicator of the open half-space `{x : E | 0 < ℓ x}` for a nonzero `ℓ : E →L[ℝ] ℝ` lies in
no positive-order local Sobolev class `MemWkpLoc p U (k + 1) μ` whenever `interior U` meets
`ker ℓ`. -/
theorem not_memWkpLoc_indicator_clm_pos [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure]
    {ℓ : E →L[ℝ] ℝ} (hℓ : ℓ ≠ 0) {k : ℕ} {x₀ : E} (hx₀ : x₀ ∈ interior U) (hker : ℓ x₀ = 0) :
    ¬ MemWkpLoc p U (k + 1) ({x : E | 0 < ℓ x}.indicator fun _ => (1 : ℝ)) μ := by
  intro h
  obtain ⟨D, hD, -⟩ := h.exists_weakFDeriv
  exact not_hasWeakFDerivOn_indicator_clm_pos hℓ hx₀ hker D hD

end HalfSpaceIndicator

/-! ### Unit radial field `x ↦ ‖x‖⁻¹ • x` on inner product spaces of dimension `≥ 2` -/

section UnitRadial

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  {p : ℝ≥0∞} {U : Set E}

/-- On a real inner product space `E` of dimension at least `2`, the unit radial field
`x ↦ ‖x‖⁻¹ • x` belongs to `MemWkpLoc p U 1 μ` for every `p < Module.finrank ℝ E`. -/
theorem memWkpLoc_one_unitRadial (hd : 1 < Module.finrank ℝ E) (hp : p < Module.finrank ℝ E) :
    MemWkpLoc p U 1 (fun x : E => ‖x‖⁻¹ • x) μ := by
  have heq : (fun x : E => ‖x‖⁻¹ • x) = fun x : E => ‖x‖ ^ (-1 : ℝ) • x := by
    funext x
    rw [Real.rpow_neg_one]
  rw [heq]
  refine memWkpLoc_succ_iff.2 ⟨memLpLoc_iff.2 fun K _ hK => ?_, _,
    hasWeakFDerivOn_norm_rpow_neg_one_smul_self hd _,
    memWkpLoc_zero_iff.2 (memLpLoc_iff.2 fun K _ hK => ?_)⟩
  · have : IsFiniteMeasure (μ.restrict K) := ⟨by simpa using hK.measure_lt_top⟩
    refine MemLp.of_bound (by fun_prop : Measurable _).aestronglyMeasurable 1
      (Eventually.of_forall fun x => ?_)
    rw [norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg x) _), Real.rpow_neg_one]
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · rw [inv_mul_cancel₀ (norm_ne_zero_iff.2 hx)]
  · have hker : MemLp (fun x : E => ‖x‖⁻¹) p (μ.restrict K) :=
      hK.isBounded.memLp_norm_inv_restrict (mu := μ) hp
    refine (hker.const_mul (1 + |(-1 : ℝ)|)).of_le
      ((hasWeakFDerivOn_norm_rpow_neg_one_smul_self (μ := μ) hd
        (⊤ : Opens E)).locallyIntegrableOn_deriv.mono_set (subset_univ K)).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (by positivity), ← Real.rpow_neg_one]
    exact norm_rpow_smul_id_add_smulRight_le (-1) x

/-- On a real inner product space `E` of dimension at least `2`, the unit radial field
`x ↦ ‖x‖⁻¹ • x` belongs to `MemWkpLoc p U 1 μ` on any set whose interior contains `0` exactly when
`p < Module.finrank ℝ E`. -/
theorem not_memWkpLoc_one_unitRadial (hd : 1 < Module.finrank ℝ E)
    (hp : Module.finrank ℝ E ≤ p) (h0 : (0 : E) ∈ interior U) :
    ¬ MemWkpLoc p U 1 (fun x : E => ‖x‖⁻¹ • x) μ := by
  intro h
  -- Step 1: Promote `x ↦ ‖x‖⁻¹ • x ∈ W^{1,p}_loc` to `x ↦ ‖x‖ ∈ W^{2,p}_loc`.
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  let N : E → E →L[ℝ] ℝ := fderiv ℝ fun y : E => ‖y‖
  have hD_norm : HasWeakFDerivOn μ (Opens.interior U) (fun y : E => ‖y‖)
      (fun x : E => innerSL ℝ (‖x‖⁻¹ • x)) := by
    have hw := hasWeakFDerivOn_norm_rpow (μ := μ) (s := 1) (by
      have : (1 : ℝ) < Module.finrank ℝ E := by exact_mod_cast hd
      linarith) (Opens.interior U)
    refine (hw.congr_ae (Eventually.of_forall fun x => by simp)).congr_ae_deriv
      (Eventually.of_forall fun x => ?_)
    ext w
    have h12 : (1 : ℝ) - 2 = -1 := by norm_num
    rw [smul_apply, innerSL_apply_apply, innerSL_apply_apply, real_inner_smul_left,
      smul_eq_mul, one_mul, h12, Real.rpow_neg_one]
  have h1 : MemWkpLoc p U 1 (fun x : E => innerSL ℝ (‖x‖⁻¹ • x)) μ :=
    h.clm_comp (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ)
  have h2 : MemWkpLoc p U 2 (fun y : E => ‖y‖) μ :=
    memWkpLoc_succ_iff.2 ⟨continuous_norm.continuousOn.memLpLoc, _, hD_norm, h1⟩
  obtain ⟨-, D₁, hD₁, h₁⟩ := memWkpLoc_succ_iff.1 h2
  obtain ⟨-, D₂, hD₂, h₂⟩ := memWkpLoc_succ_iff.1 h₁
  have hL := memWkpLoc_zero_iff.1 h₂
  -- Step 2: Identify the weak second derivative `D₂` with the classical Hessian off `{0}`.
  set Ω : Opens E := Opens.interior U
  have hN : HasWeakFDerivOn μ Ω (fun y : E => ‖y‖) N :=
    lipschitzWith_one_norm.locallyLipschitz.locallyLipschitzOn.hasWeakFDerivOn_fderiv
  have hD₂N : HasWeakFDerivOn μ Ω N D₂ := hD₂.congr_ae (hD₁.ae_eq hN)
  set Ω' : Opens E := Ω ⊓ ⟨{0}ᶜ, isOpen_compl_singleton⟩
  have hNsmooth : ContDiffOn ℝ 1 N (Ω' : Set E) := fun x hx =>
    ((contDiffAt_norm ℝ hx.2 : ContDiffAt ℝ 2 (fun y : E => ‖y‖) x).fderiv_right
      (by norm_num)).contDiffWithinAt
  have hNw : HasWeakFDerivOn μ Ω' N (fderiv ℝ N) :=
    hasWeakFDerivOn_of_differentiableOn
      ((hNsmooth.continuousOn_fderiv_of_isOpen Ω'.isOpen le_rfl).locallyIntegrableOn
        Ω'.isOpen.measurableSet)
      fun x hx => (hNsmooth.differentiableOn one_ne_zero).differentiableAt (Ω'.isOpen.mem_nhds hx)
  have hae : D₂ =ᵐ[μ.restrict Ω'] fderiv ℝ N := (hD₂N.mono inf_le_left).ae_eq hNw
  -- Step 3: Compare `‖fderiv ℝ N x‖ ≥ ‖x‖⁻¹` on a ball around `0` to contradict `p ≥ dim E`.
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 isOpen_interior 0 h0
  have hK : closedBall (0 : E) (r / 2) ⊆ U :=
    (closedBall_subset_ball (by linarith)).trans (hrU.trans interior_subset)
  have hfin : IsFiniteMeasure (μ.restrict (closedBall (0 : E) (r / 2))) :=
    ⟨by simpa using (isCompact_closedBall (0 : E) (r / 2)).measure_lt_top⟩
  have hD₂d := ((memLpLoc_iff.1 hL _ hK (isCompact_closedBall 0 _)).mono_exponent hp).mono_measure
    (Measure.restrict_mono ball_subset_closedBall le_rfl :
      μ.restrict (ball (0 : E) (r / 2)) ≤ μ.restrict (closedBall (0 : E) (r / 2)))
  have hball : ball (0 : E) (r / 2) ⊆ Ω ∪ {0} := fun x hx =>
    Or.inl (interior_mono subset_rfl (hrU (ball_subset_ball (by linarith) hx)))
  have hnull : ∀ᵐ x ∂μ, x ≠ (0 : E) := by simp [ae_iff, measure_singleton]
  have hae' : D₂ =ᵐ[μ.restrict (ball (0 : E) (r / 2))] fderiv ℝ N := by
    rw [EventuallyEq, ae_restrict_iff' measurableSet_ball]
    have h1' := (ae_restrict_iff' Ω'.isOpen.measurableSet).1 hae
    filter_upwards [h1', hnull] with x hx hx0 hxb
    rcases hball hxb with hxΩ | hx'
    · exact hx ⟨hxΩ, hx0⟩
    · exact absurd hx' hx0
  have hG := hD₂d.ae_eq hae'
  have hd_ne0 : (Module.finrank ℝ E : ℝ≥0∞) ≠ 0 := by
    have : 0 < Module.finrank ℝ E := by omega
    positivity
  have hint := (integrable_norm_rpow_iff hG.norm.aestronglyMeasurable hd_ne0
    (ENNReal.natCast_ne_top _)).2 hG.norm
  have hsing : IntegrableOn (fun x : E => ‖x‖ ^ (-(Module.finrank ℝ E : ℝ)))
      (ball (0 : E) (r / 2)) μ := by
    refine hint.mono' (by fun_prop : Measurable _).aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_ball).2 ?_)
    filter_upwards [hnull] with x hx0 _
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg x) _), Real.rpow_neg (norm_nonneg x),
      ← Real.inv_rpow (norm_nonneg x), ENNReal.toReal_natCast]
    refine Real.rpow_le_rpow (by positivity) ?_ (Nat.cast_nonneg _)
    rw [norm_norm]
    have hker_pos : 0 < Module.finrank ℝ (Submodule.orthogonal (Submodule.span ℝ {x})) := by
      have hdim := Submodule.finrank_add_finrank_orthogonal (Submodule.span ℝ {x})
      have hspan : Module.finrank ℝ (Submodule.span ℝ {x}) = 1 := finrank_span_singleton hx0
      omega
    have : Nontrivial (Submodule.orthogonal (Submodule.span ℝ {x})) :=
      Module.nontrivial_of_finrank_pos (R := ℝ) hker_pos
    obtain ⟨⟨v, hvorth⟩, hv0⟩ := exists_ne (0 : Submodule.orthogonal (Submodule.span ℝ {x}))
    have hvne : v ≠ 0 := fun h => hv0 (Subtype.ext h)
    have hxv : ⟪x, v⟫ = 0 := by
      rw [real_inner_comm]
      exact Submodule.mem_orthogonal_singleton_iff_inner_left.1 hvorth
    exact inv_norm_le_norm_fderiv_fderiv_norm hx0 hvne hxv
  have hlt := (integrableOn_norm_rpow_ball_iff (E := E) (mu := μ) (half_pos hr)).1 hsing
  exact lt_irrefl _ hlt

/-- On a real inner product space `E` of dimension at least `2`, the unit radial field
`x ↦ ‖x‖⁻¹ • x` belongs to `MemWkpLoc p U 1 μ` on any set whose interior contains `0` exactly when
`p < Module.finrank ℝ E`. -/
theorem memWkpLoc_one_unitRadial_iff (hd : 1 < Module.finrank ℝ E) (h0 : (0 : E) ∈ interior U) :
    MemWkpLoc p U 1 (fun x : E => ‖x‖⁻¹ • x) μ ↔ p < Module.finrank ℝ E :=
  ⟨fun h => not_le.1 fun hp => not_memWkpLoc_one_unitRadial hd hp h0 h,
    memWkpLoc_one_unitRadial hd⟩

end UnitRadial

/-! ### Radial power maps `x ↦ ‖x‖ ^ α • x` for `α > -1` -/

section RadialPower

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  {p : ℝ≥0∞} {U : Set E}

/-- For `α > -1`, the radial power map `x ↦ ‖x‖ ^ α • x` is continuous on `E` and lies in
`MemWkpLoc p U 1 μ` whenever `x ↦ ‖x‖ ^ α` belongs to `MemLpLoc p U μ`. -/
theorem memWkpLoc_one_norm_rpow_smul_id {α : ℝ} (hα : -1 < α)
    (hp : MemLpLoc p U (fun x : E => ‖x‖ ^ α) μ) :
    MemWkpLoc p U 1 (fun x : E => ‖x‖ ^ α • x) μ := by
  refine memWkpLoc_succ_iff.2 ⟨(continuous_norm_rpow_smul_self hα).continuousOn.memLpLoc, _,
    hasWeakFDerivOn_norm_rpow_smul_self hα _,
    memWkpLoc_zero_iff.2 (memLpLoc_iff.2 fun K hKU hK => ?_)⟩
  have hbase : MemLp (fun x : E => ‖x‖ ^ α) p (μ.restrict K) := memLpLoc_iff.1 hp K hKU hK
  refine (hbase.const_mul (1 + |α|)).of_le
    ((hasWeakFDerivOn_norm_rpow_smul_self (μ := μ) hα
      (⊤ : Opens E)).locallyIntegrableOn_deriv.mono_set (subset_univ K)).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg (norm_nonneg x) _))]
  exact norm_rpow_smul_id_add_smulRight_le α x

end RadialPower

end TauCeti
