/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Interpolation.ComplexMethod.Basic
public import TauCeti.Analysis.Normed.Interpolation.ComplexMethod.Lebesgue
public import TauCeti.Analysis.Normed.Interpolation.Lebesgue
import Mathlib.Analysis.Complex.Hadamard
import TauCeti.Analysis.SpecialFunctions.Pow.Real
import TauCeti.Data.ENNReal.InterpolatedExponent
import TauCeti.MeasureTheory.Function.Holder
import TauCeti.MeasureTheory.Function.Lp.Duality
import TauCeti.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# The complex interpolation space of the Lebesgue couple is `Lᵖ`

Let `1 ≤ p₀, p₁ ≤ ∞`, `0 < θ < 1` and `1 / p = (1 - θ) / p₀ + θ / p₁` with `p < ∞`, on a
σ-finite measure space, for functions with values in a complex inner product space `E`. Every
element `u` of the complex interpolation space `[L^{p₀}, L^{p₁}]_θ` is a function of `Lᵖ`, with
`‖u‖_p ≤ ‖u‖_θ` (`TauCeti.CompatibleCouple.ComplexMethodSpace.eLpNorm_toAEEqFun_le`). This is the
inclusion `[L^{p₀}, L^{p₁}]_θ ⊆ Lᵖ` of Bergh–Löfström, Theorem 5.1.1.
`TauCeti.CompatibleCouple.ComplexMethodSpace.lebesgueToLp` is the resulting continuous linear
map, of norm at most one, lying over the embeddings of both spaces into `L¹ + L^∞`.
Together with the reverse inclusion `TauCeti.CompatibleCouple.lpToLebesgueComplexMethod` it gives
Calderón's identity `[L^{p₀}, L^{p₁}]_θ = Lᵖ` with equal norms, as the linear isometric equivalence
`TauCeti.CompatibleCouple.lebesgueComplexMethodEquiv`.

The proof of the inclusion is by duality. By
`MeasureTheory.AEStronglyMeasurable.eLpNorm_le_of_forall_enorm_integral_inner_simpleFunc_le` it
suffices to bound the pairing `∫ ⟪g, u⟫` by `‖u‖_θ ‖g‖_{p'}` for integrable simple functions `g`,
where `p'` is the conjugate exponent. Write `p₀'` and `p₁'` for the conjugates of `p₀` and `p₁`,
so that `1 / p' = (1 - θ) / p₀' + θ / p₁'`. For an admissible function `F` with `F θ = u` consider
the scalar function

`Φ z = ∫ ‖g‖ ^ (α z - 1) ⟪g, F z⟫`, where `α z = p' ((1 - z) / p₀' + z / p₁')`.

Since `g` is simple, `Φ` is a finite combination of continuous linear functionals of `F z` with
entire coefficients, so it is holomorphic in the strip and bounded on its closure. It equals
`∫ ⟪g, u⟫` at `θ`. On the line `re z = j` the test function has norm `‖g‖ ^ (p' / pⱼ')`, so
Hölder's inequality bounds `Φ` there by `‖F‖ ‖g‖_{p'} ^ (p' / pⱼ')`, and the three-lines theorem
gives `‖Φ θ‖ ≤ ‖F‖ ‖g‖_{p'}`. When `p = 1`, that is `p₀ = p₁ = 1`, the exponent `α` is taken to be
constantly `1`.

## Main declarations

* `TauCeti.CompatibleCouple.ComplexMethodSpace.eLpNorm_toAEEqFun_le`: the function of
  `L¹ + L^∞` represented by `u ∈ [L^{p₀}, L^{p₁}]_θ` has `Lᵖ` norm at most `‖u‖_θ`, and so lies in
  `Lᵖ` (`memLp_toAEEqFun`).
* `TauCeti.CompatibleCouple.ComplexMethodSpace.lebesgueToLp`: the inclusion
  `[L^{p₀}, L^{p₁}]_θ → Lᵖ`, with `ofLp_lebesgueToLp`, `norm_lebesgueToLp_le`,
  `opNorm_lebesgueToLp_le` and `lebesgueToLp_injective`.
* `TauCeti.CompatibleCouple.lebesgueComplexMethodEquiv`: the isometric identification
  `[L^{p₀}, L^{p₁}]_θ ≃ₗᵢ[ℂ] Lᵖ`, whose inverse is `lpToLebesgueComplexMethod`.

## References

* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Grundlehren 223,
  Springer, 1976, §5.1 (Theorem 5.1.1).
* A.-P. Calderón, *Intermediate spaces and interpolation, the complex method*, Studia Math. 24
  (1964), 113–190.
-/

public noncomputable section

open MeasureTheory Complex Complex.HadamardThreeLines Set
open scoped ENNReal InnerProductSpace ComplexConjugate ZeroAtInfty

namespace TauCeti.CompatibleCouple

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}

/-! ### Pairing with a simple function -/

section Pairing

/-- Integration against an integrable simple function `G`, `v ↦ ∫ ⟪G, v⟫`, as a continuous linear
functional on `L¹ + L^∞`. -/
private def innerSumCLM (G : SimpleFunc α E) (hG : Integrable G μ) : L1AddLinfty ℂ E μ →L[ℂ] ℂ :=
  (l1Linfty ℂ E μ).sumLift ((G.memLp_top μ).innerLpCLM ℂ (q' := 1))
    ((memLp_one_iff_integrable.2 hG).innerLpCLM ℂ (q' := ∞)) fun x => by
      have hx' := (l1Linfty ℂ E μ).mem_inter_iff.1 x.property
      rw [l1Linfty_embed₀, l1Linfty_embed₁] at hx'
      have hx := (L1AddLinfty.lpToAmbient_eq_lpToAmbient_iff ℂ).1 hx'
      rw [interFst_apply, interSnd_apply, MemLp.innerLpCLM_apply, MemLp.innerLpCLM_apply]
      exact integral_congr_ae (hx.mono fun y hy => by simp only [hy])

/-- Pairing an integrable simple function with a function of `L¹ + L^∞` is integrable, and its
integral is `innerSumCLM`. -/
private theorem integrable_inner_and_innerSumCLM_apply (G : SimpleFunc α E) (hG : Integrable G μ)
    (v : L1AddLinfty ℂ E μ) :
    Integrable (fun x => ⟪G x, L1AddLinfty.toAEEqFun ℂ v x⟫_ℂ) μ ∧
      innerSumCLM G hG v = ∫ x, ⟪G x, L1AddLinfty.toAEEqFun ℂ v x⟫_ℂ ∂μ := by
  obtain ⟨g, h, hgh⟩ := (l1Linfty ℂ E μ).exists_fstToSum_add_sndToSum_eq v
  have hae := L1AddLinfty.fstToSum_add_sndToSum_eq_iff.1 hgh
  have hg := (G.memLp_top μ).integrable_inner_of_holderConjugate (𝕜 := ℂ) (Lp.memLp g)
  have hh :=
    (memLp_one_iff_integrable.2 hG).integrable_inner_of_holderConjugate (𝕜 := ℂ) (Lp.memLp h)
  have hcongr : (fun x => ⟪G x, g x⟫_ℂ + ⟪G x, h x⟫_ℂ) =ᵐ[μ]
      fun x => ⟪G x, L1AddLinfty.toAEEqFun ℂ v x⟫_ℂ :=
    hae.mono fun x hx => by simp only [← hx, Pi.add_apply, inner_add_right]
  refine ⟨(hg.add hh).congr hcongr, ?_⟩
  rw [← hgh, map_add, innerSumCLM, sumLift_fstToSum, sumLift_sndToSum, MemLp.innerLpCLM_apply,
    MemLp.innerLpCLM_apply, ← integral_add hg hh, hgh]
  exact integral_congr_ae hcongr

open Classical in
/-- The part of a simple function `g` on its fibre over `w`: `w` where `g = w`, and `0`
elsewhere. -/
private def fibre (g : SimpleFunc α E) (w : E) : SimpleFunc α E :=
  g.map fun y => if y = w then w else 0

omit [InnerProductSpace ℂ E] in
private theorem integrable_fibre {g : SimpleFunc α E} (hg : Integrable g μ) (w : E) :
    Integrable (fibre g w) μ := by
  classical
  refine SimpleFunc.FinMeasSupp.integrable ?_
  refine (SimpleFunc.integrable_iff_finMeasSupp.1 hg).map ?_
  split_ifs with h <;> simp [h]

/-- Recombining the fibres of `g` with coefficients `c w`: the corresponding combination of
pairings is the pairing with `conj (c (g x)) • g x`. -/
private theorem sum_mul_innerSumCLM_fibre {g : SimpleFunc α E} (hg : Integrable g μ) (c : E → ℂ)
    (v : L1AddLinfty ℂ E μ) :
    ∑ w ∈ g.range, c w * innerSumCLM (fibre g w) (integrable_fibre hg w) v =
      ∫ x, ⟪conj (c (g x)) • g x, L1AddLinfty.toAEEqFun ℂ v x⟫_ℂ ∂μ := by
  classical
  have hint (w : E) := (integrable_inner_and_innerSumCLM_apply _ (integrable_fibre hg w) v)
  simp_rw [(hint _).2, ← integral_const_mul]
  rw [← integral_finsetSum _ fun w _ => (hint w).1.const_mul (c w)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [fibre, SimpleFunc.map_apply, inner_smul_left, conj_conj]
  rw [Finset.sum_congr rfl fun w _ => (by split_ifs <;> simp_all :
    c w * ⟪if g x = w then w else 0, L1AddLinfty.toAEEqFun ℂ v x⟫_ℂ =
      if g x = w then c w * ⟪w, L1AddLinfty.toAEEqFun ℂ v x⟫_ℂ else 0)]
  rw [Finset.sum_ite_eq, ite_eq_left_iff.2 fun h => absurd (g.mem_range_self x) h]

end Pairing

/-! ### Exponents -/

/-- The interpolation of the boundary bounds: the exponents `βⱼ = 1 + (j - θ) κ` satisfy
`(1 - θ) β₀ + θ β₁ = 1`, so `(a N ^ β₀) ^ (1 - θ) (a N ^ β₁) ^ θ = a N` for `a, N ≥ 0`. -/
private theorem rpow_mul_rpow_interp {a N θ κ : ℝ} (ha : 0 ≤ a) (hN : 0 ≤ N) :
    (a * N ^ (1 + (0 - θ) * κ)) ^ (1 - θ) * (a * N ^ (1 + (1 - θ) * κ)) ^ θ = a * N := by
  have hsum : (1 + (0 - θ) * κ) * (1 - θ) + (1 + (1 - θ) * κ) * θ = 1 := by ring
  rw [Real.mul_rpow_mul_mul_rpow_of_add_eq_one ha (sub_add_cancel 1 θ), ← Real.rpow_mul hN,
    ← Real.rpow_mul hN, ← Real.rpow_add' hN (by rw [hsum]; exact one_ne_zero), hsum, Real.rpow_one]

/-! ### The analytic family -/

section Family

variable {θ κ : ℝ}

/-- The coefficient `a ^ ((z - θ) κ)` of the analytic family, written with the exponential so
that it is entire in `z` also for `a = 0`. -/
private def coeff (θ κ a : ℝ) (z : ℂ) : ℂ :=
  exp ((z - θ) * κ * Real.log a)

private theorem norm_coeff (a : ℝ) (z : ℂ) :
    ‖coeff θ κ a z‖ = Real.exp ((z.re - θ) * κ * Real.log a) := by
  rw [coeff, norm_exp]
  congr 1
  simp

private theorem differentiable_coeff (a : ℝ) : Differentiable ℂ (coeff θ κ a) := by
  unfold coeff
  fun_prop

/-- On the vertical line `re z = t`, the test function `conj (coeff ‖g x‖ z) • g x` has norm at
most `‖g x‖ ^ (1 + (t - θ) κ)`. -/
private theorem norm_conj_coeff_smul_le (w : E) (z : ℂ) :
    ‖conj (coeff θ κ ‖w‖ z) • w‖ ≤ ‖w‖ ^ (1 + (z.re - θ) * κ) := by
  rcases eq_or_ne w 0 with rfl | hw
  · simpa using Real.rpow_nonneg le_rfl _
  · have hw' : 0 < ‖w‖ := norm_pos_iff.2 hw
    rw [norm_smul, RCLike.norm_conj, norm_coeff, Real.rpow_def_of_pos hw',
      show Real.log ‖w‖ * (1 + (z.re - θ) * κ) = (z.re - θ) * κ * Real.log ‖w‖ + Real.log ‖w‖ by
        ring, Real.exp_add, Real.exp_log hw']

/-- On the closed strip the coefficients are bounded by `exp |κ log a|`. -/
private theorem norm_coeff_le (hθ : θ ∈ Icc (0 : ℝ) 1) (a : ℝ) {z : ℂ}
    (hz : z ∈ verticalClosedStrip 0 1) :
    ‖coeff θ κ a z‖ ≤ Real.exp |κ * Real.log a| := by
  rw [norm_coeff, mul_assoc]
  refine Real.exp_le_exp.2 ((le_abs_self _).trans ?_)
  rw [abs_mul]
  refine mul_le_of_le_one_left (abs_nonneg _) (abs_le.2 ⟨?_, ?_⟩)
  · linarith [hz.1, hθ.2]
  · linarith [hz.2, hθ.1]

/-- The scalar analytic family `Φ z = ∑_w ‖w‖ ^ ((z - θ) κ) ∫ ⟪g_w, F z⟫` over the fibres `g_w`
of an integrable simple function `g`, for a family `F` in `L¹ + L^∞`. -/
private def pairingFamily {g : SimpleFunc α E} (hg : Integrable g μ) (θ κ : ℝ)
    (F : ℂ → L1AddLinfty ℂ E μ) (z : ℂ) : ℂ :=
  ∑ w ∈ g.range, coeff θ κ ‖w‖ z * innerSumCLM (fibre g w) (integrable_fibre hg w) (F z)

/-- The family is the pairing of `F z` with the test function `‖g‖ ^ ((z - θ) κ) g`. -/
private theorem pairingFamily_eq {g : SimpleFunc α E} (hg : Integrable g μ)
    (F : ℂ → L1AddLinfty ℂ E μ) (z : ℂ) :
    pairingFamily hg θ κ F z =
      ∫ x, ⟪conj (coeff θ κ ‖g x‖ z) • g x, L1AddLinfty.toAEEqFun ℂ (F z) x⟫_ℂ ∂μ :=
  sum_mul_innerSumCLM_fibre hg (fun w => coeff θ κ ‖w‖ z) _

/-- At `θ` the coefficients are `1`, so the family is the pairing of `F θ` with `g`. -/
private theorem pairingFamily_ofReal {g : SimpleFunc α E} (hg : Integrable g μ)
    (F : ℂ → L1AddLinfty ℂ E μ) :
    pairingFamily hg θ κ F θ = ∫ x, ⟪g x, L1AddLinfty.toAEEqFun ℂ (F θ) x⟫_ℂ ∂μ := by
  rw [pairingFamily_eq]
  simp [coeff]

/-- For `F` holomorphic in the strip and continuous on its closure, so is the family. -/
private theorem diffContOnCl_pairingFamily {g : SimpleFunc α E} (hg : Integrable g μ)
    {F : ℂ → L1AddLinfty ℂ E μ} (hF : DiffContOnCl ℂ F (verticalStrip 0 1)) :
    DiffContOnCl ℂ (pairingFamily hg θ κ F) (verticalStrip 0 1) := by
  have hw (w : E) : DiffContOnCl ℂ
      (fun z => coeff θ κ ‖w‖ z * innerSumCLM (fibre g w) (integrable_fibre hg w) (F z))
      (verticalStrip 0 1) :=
    (differentiable_coeff ‖w‖).diffContOnCl.smul
      ((innerSumCLM (fibre g w) (integrable_fibre hg w)).differentiable.comp_diffContOnCl hF)
  exact ⟨DifferentiableOn.fun_sum fun w _ => (hw w).differentiableOn,
    continuousOn_finsetSum _ fun w _ => (hw w).continuousOn⟩

/-- For `F` bounded on the closed strip, so is the family. -/
private theorem bddAbove_pairingFamily (hθ : θ ∈ Icc (0 : ℝ) 1) {g : SimpleFunc α E}
    (hg : Integrable g μ) {F : ℂ → L1AddLinfty ℂ E μ} {M : ℝ}
    (hM : ∀ z ∈ verticalClosedStrip 0 1, ‖F z‖ ≤ M) :
    BddAbove ((norm ∘ pairingFamily hg θ κ F) '' verticalClosedStrip 0 1) := by
  refine ⟨∑ w ∈ g.range, Real.exp |κ * Real.log ‖w‖| *
    (‖innerSumCLM (fibre g w) (integrable_fibre hg w)‖ * M), ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun w _ => ?_)
  rw [norm_mul]
  exact mul_le_mul (norm_coeff_le hθ ‖w‖ hz)
    (((innerSumCLM _ _).le_opNorm _).trans (mul_le_mul_of_nonneg_left (hM z hz) (norm_nonneg _)))
    (norm_nonneg _) (Real.exp_pos _).le

/-- **The family on a boundary line.** Let `1 / r' = β / q` for the conjugate exponent `r'` of
`r ≥ 1`, with `β = 1 + (re z - θ) κ ≥ 0`. If `F z` is a function `f ∈ Lʳ` with `‖f‖_r ≤ M`, then
Hölder's inequality bounds the family at `z` by `M ‖g‖_q ^ β`. -/
private theorem norm_pairingFamily_le {g : SimpleFunc α E} (hg : Integrable g μ) {q r : ℝ≥0∞}
    [Fact (1 ≤ r)] (hgq : eLpNorm g q μ ≠ ∞) {β : ℝ} (hβ : 0 ≤ β)
    (hr : r.conjExponent⁻¹ = ENNReal.ofReal β * q⁻¹) {F : ℂ → L1AddLinfty ℂ E μ} {z : ℂ}
    (hzβ : 1 + (z.re - θ) * κ = β) {f : Lp E r μ} {M : ℝ} (hfM : ‖f‖ ≤ M)
    (hFz : F z = L1AddLinfty.ofLp f) :
    ‖pairingFamily hg θ κ F z‖ ≤ M * (eLpNorm g q μ).toReal ^ β := by
  have : r.HolderConjugate r.conjExponent := .conjExponent Fact.out
  set u : α → E := fun x => conj (coeff θ κ ‖g x‖ z) • g x
  have hu : AEStronglyMeasurable u μ :=
    (g.map fun w => conj (coeff θ κ ‖w‖ z) • w).aestronglyMeasurable
  have hule : eLpNorm u r.conjExponent μ ≤ eLpNorm g q μ ^ β :=
    eLpNorm_le_eLpNorm_rpow hβ hu hr (ae_of_all _ fun x => by
      simpa [u, hzβ] using norm_conj_coeff_smul_le (θ := θ) (κ := κ) (g x) z)
  have hΦz : ‖pairingFamily hg θ κ F z‖ₑ ≤ eLpNorm g q μ ^ β * eLpNorm f r μ := by
    rw [pairingFamily_eq, hFz, L1AddLinfty.toAEEqFun_ofLp]
    exact (TauCeti.enorm_integral_inner_le (p := r.conjExponent) (q := r)).trans
      (mul_le_mul_left hule _)
  have hfin : eLpNorm g q μ ^ β * eLpNorm f r μ ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hβ hgq) (Lp.eLpNorm_ne_top f)
  calc ‖pairingFamily hg θ κ F z‖ ≤ (eLpNorm g q μ ^ β * eLpNorm f r μ).toReal := by
        rw [← toReal_eNorm]
        exact ENNReal.toReal_mono hfin hΦz
    _ = ‖f‖ * (eLpNorm g q μ).toReal ^ β := by
        rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, Lp.norm_def, mul_comm]
    _ ≤ M * (eLpNorm g q μ).toReal ^ β :=
        mul_le_mul_of_nonneg_right hfM (Real.rpow_nonneg ENNReal.toReal_nonneg _)

end Family

/-! ### The three-lines bound -/

section ThreeLines

variable {p₀ p₁ : ℝ≥0∞} [Fact (1 ≤ p₀)] [Fact (1 ≤ p₁)] {θ κ : ℝ}

/-- **The three-lines bound for the pairing.** Let `g` be an integrable simple function and `F` an
admissible function for the Lebesgue couple with boundary traces `g'`. If the factors
`β t = 1 + (t - θ) κ` are nonnegative and `β t / q = (1 - t) / p₀' + t / p₁'` for `0 ≤ t ≤ 1`, where
`pⱼ'` are the conjugate exponents, then `‖∫ ⟪g, F θ⟫‖ ≤ ‖g'‖ ‖g‖_q`. -/
private theorem norm_integral_inner_le_of_isStripFunction {q : ℝ≥0∞} (hθ : θ ∈ Ioo (0 : ℝ) 1)
    (hκ : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ 1 + (t - θ) * κ ∧ ENNReal.ofReal (1 + (t - θ) * κ) * q⁻¹ =
      ENNReal.ofReal (1 - t) * p₀.conjExponent⁻¹ + ENNReal.ofReal t * p₁.conjExponent⁻¹)
    {g : SimpleFunc α E} (hg : Integrable g μ) (hgq : eLpNorm g q μ ≠ ∞)
    {F : ℂ → (lebesgue ℂ E μ p₀ p₁).SumSpace} {g' : C₀(ℝ, Lp E p₀ μ) × C₀(ℝ, Lp E p₁ μ)}
    (hF : (lebesgue ℂ E μ p₀ p₁).IsStripFunction F g') :
    ‖∫ x, ⟪g x, L1AddLinfty.toAEEqFun ℂ ((lebesgue ℂ E μ p₀ p₁).sumSpaceEmbed (F θ)) x⟫_ℂ ∂μ‖ ≤
      ‖g'‖ * (eLpNorm g q μ).toReal := by
  have hθ' : θ ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hθ
  set F' := fun z => (lebesgue ℂ E μ p₀ p₁).sumSpaceEmbed (F z)
  have hd := diffContOnCl_pairingFamily (θ := θ) (κ := κ) hg (F := F')
    ((lebesgue ℂ E μ p₀ p₁).sumSpaceEmbed.differentiable.comp_diffContOnCl hF.diffContOnCl)
  obtain ⟨M, hM⟩ := hF.exists_norm_le
  have hB := bddAbove_pairingFamily (κ := κ) hθ' hg (F := F') fun z hz =>
    ((lebesgue ℂ E μ p₀ p₁).sumSpaceEmbed.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (hM z hz) (norm_nonneg _))
  -- On the boundary lines, `F` takes values in `L^{p₀}` and `L^{p₁}` of norm at most `‖g'‖`.
  obtain ⟨hβ₀, hq₀⟩ := hκ 0 ⟨le_rfl, zero_le_one⟩
  obtain ⟨hβ₁, hq₁⟩ := hκ 1 ⟨zero_le_one, le_rfl⟩
  have ha (z : ℂ) (hz : z ∈ re ⁻¹' {0}) : ‖pairingFamily hg θ κ F' z‖ ≤
      ‖g'‖ * (eLpNorm g q μ).toReal ^ (1 + (0 - θ) * κ) := by
    have hz : z.re = 0 := by simpa using hz
    have hFz : F z = (lebesgue ℂ E μ p₀ p₁).fstToSum (g'.1 z.im) := by
      conv_lhs => rw [← re_add_im z, hz, ofReal_zero, zero_add]
      exact hF.apply_mul_I z.im
    refine norm_pairingFamily_le hg hgq hβ₀ (by rw [hq₀]; simp) (by rw [hz])
      ((ZeroAtInftyContinuousMap.norm_coe_le_norm g'.1 z.im).trans (norm_fst_le g')) ?_
    simp only [F']
    rw [hFz, sumSpaceEmbed_fstToSum, lebesgue_embed₀]
  have hb (z : ℂ) (hz : z ∈ re ⁻¹' {1}) : ‖pairingFamily hg θ κ F' z‖ ≤
      ‖g'‖ * (eLpNorm g q μ).toReal ^ (1 + (1 - θ) * κ) := by
    have hz : z.re = 1 := by simpa using hz
    have hFz : F z = (lebesgue ℂ E μ p₀ p₁).sndToSum (g'.2 z.im) := by
      conv_lhs => rw [← re_add_im z, hz, ofReal_one]
      exact hF.apply_one_add_mul_I z.im
    refine norm_pairingFamily_le hg hgq hβ₁ (by rw [hq₁]; simp) (by rw [hz])
      ((ZeroAtInftyContinuousMap.norm_coe_le_norm g'.2 z.im).trans (norm_snd_le g')) ?_
    simp only [F']
    rw [hFz, sumSpaceEmbed_sndToSum, lebesgue_embed₁]
  -- The three-lines theorem at `θ`.
  have h3 := norm_le_interp_of_mem_verticalClosedStrip₀₁' _ (z := θ)
    (by simpa [verticalClosedStrip] using hθ') hd hB ha hb
  rw [pairingFamily_ofReal, ofReal_re,
    rpow_mul_rpow_interp (norm_nonneg _) ENNReal.toReal_nonneg] at h3
  exact h3

end ThreeLines

/-! ### The inclusion into `Lᵖ` -/

namespace ComplexMethodSpace

variable {p₀ p₁ p : ℝ≥0∞} [Fact (1 ≤ p₀)] [Fact (1 ≤ p₁)] {θ : ℝ}

/-- The pairing of `u ∈ [L^{p₀}, L^{p₁}]_θ` with an integrable simple function `g` is bounded by
`‖u‖_θ ‖g‖_q`, under the exponent relations of `norm_integral_inner_le_of_isStripFunction`. -/
private theorem norm_integral_inner_le {q : ℝ≥0∞} {κ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1)
    (hκ : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ 1 + (t - θ) * κ ∧ ENNReal.ofReal (1 + (t - θ) * κ) * q⁻¹ =
      ENNReal.ofReal (1 - t) * p₀.conjExponent⁻¹ + ENNReal.ofReal t * p₁.conjExponent⁻¹)
    {g : SimpleFunc α E} (hg : Integrable g μ) (hgq : eLpNorm g q μ ≠ ∞)
    (u : (lebesgue ℂ E μ p₀ p₁).ComplexMethodSpace θ) :
    ‖∫ x, ⟪g x, L1AddLinfty.toAEEqFun ℂ
      ((lebesgue ℂ E μ p₀ p₁).sumSpaceEmbed (toSum u)) x⟫_ℂ ∂μ‖ ≤
      ‖u‖ * (eLpNorm g q μ).toReal := by
  set N := (eLpNorm g q μ).toReal
  have hN : 0 ≤ N := ENNReal.toReal_nonneg
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  -- Choose an admissible representative of `u` with traces of norm close to `‖u‖`.
  obtain ⟨g', hu, hg'⟩ := norm_lt_iff.1
    (lt_add_of_pos_right (‖u‖) (show 0 < ε / (N + 1) by positivity))
  have hθF : toSum u = (lebesgue ℂ E μ p₀ p₁).stripFunction g' θ := by
    rw [← hu, toSum_mk, stripEval_apply]
  have h3 := norm_integral_inner_le_of_isStripFunction hθ hκ hg hgq
    ((lebesgue ℂ E μ p₀ p₁).isStripFunction_stripFunction g')
  rw [← hθF] at h3
  have hεN : ε / (N + 1) * N < ε := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  calc _ ≤ ‖(g' : C₀(ℝ, Lp E p₀ μ) × C₀(ℝ, Lp E p₁ μ))‖ * N := h3
    _ ≤ (‖u‖ + ε / (N + 1)) * N := mul_le_mul_of_nonneg_right hg'.le hN
    _ < ‖u‖ * N + ε := by linarith

/-- **`[L^{p₀}, L^{p₁}]_θ ⊆ Lᵖ`.** On a σ-finite measure space, let `0 < θ < 1` and
`1 / p = (1 - θ) / p₀ + θ / p₁` with `p < ∞`. The function of `L¹ + L^∞` represented by an element
`u` of the complex interpolation space `[L^{p₀}, L^{p₁}]_θ` has `Lᵖ` norm at most `‖u‖_θ`.
This is one half of Bergh–Löfström, Theorem 5.1.1. -/
theorem eLpNorm_toAEEqFun_le [SigmaFinite μ] (hθ : θ ∈ Ioo (0 : ℝ) 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹) (hp_top : p ≠ ∞)
    (u : (lebesgue ℂ E μ p₀ p₁).ComplexMethodSpace θ) :
    eLpNorm (L1AddLinfty.toAEEqFun ℂ ((lebesgue ℂ E μ p₀ p₁).sumSpaceEmbed (toSum u))) p μ ≤
      ENNReal.ofReal ‖u‖ := by
  have hθ' : θ ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hθ
  have hp₁ : 1 ≤ p := one_le_of_inv_eq Fact.out Fact.out hθ' hp
  have : p.HolderConjugate p.conjExponent := .conjExponent hp₁
  -- The conjugate exponents interpolate along the strip with some slope `κ`.
  obtain ⟨κ, hκ⟩ := exists_slope_of_inv_eq
    (ENNReal.HolderConjugate.conjExponent (Fact.out : 1 ≤ p₀)).symm.ne_zero
    (ENNReal.HolderConjugate.conjExponent (Fact.out : 1 ≤ p₁)).symm.ne_zero hθ
    (inv_conjExponent_eq_of_inv_eq Fact.out Fact.out hθ' hp)
  -- By duality it suffices to bound the pairings with integrable simple functions.
  refine (AEEqFun.aestronglyMeasurable _).eLpNorm_le_of_forall_enorm_integral_inner_simpleFunc_le
    (𝕜 := ℂ) (q' := p.conjExponent) hp_top fun g hg => ?_
  have hgq : eLpNorm g p.conjExponent μ ≠ ∞ := (SimpleFunc.memLp_of_finite_measure_preimage _
    (SimpleFunc.finMeasSupp_iff.1 (SimpleFunc.integrable_iff_finMeasSupp.1 hg))).eLpNorm_ne_top
  have hbound := norm_integral_inner_le hθ hκ hg hgq u
  -- Translate to extended norms, using `‖∫ ⟪h, g⟫‖ = ‖∫ ⟪g, h⟫‖`.
  rw [TauCeti.enorm_integral_inner_comm]
  generalize hN : (eLpNorm g p.conjExponent μ).toReal = N at hbound
  calc _ = ENNReal.ofReal ‖∫ x, ⟪g x, L1AddLinfty.toAEEqFun ℂ
        ((lebesgue ℂ E μ p₀ p₁).sumSpaceEmbed (toSum u)) x⟫_ℂ ∂μ‖ := (ofReal_norm _).symm
    _ ≤ ENNReal.ofReal (‖u‖ * N) := ENNReal.ofReal_le_ofReal hbound
    _ = ENNReal.ofReal ‖u‖ * eLpNorm g p.conjExponent μ := by
      rw [ENNReal.ofReal_mul (norm_nonneg _), ← hN, ENNReal.ofReal_toReal hgq]

/-- An element of `[L^{p₀}, L^{p₁}]_θ` is a function of `Lᵖ`. -/
theorem memLp_toAEEqFun [SigmaFinite μ] (hθ : θ ∈ Ioo (0 : ℝ) 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹) (hp_top : p ≠ ∞)
    (u : (lebesgue ℂ E μ p₀ p₁).ComplexMethodSpace θ) :
    MemLp (L1AddLinfty.toAEEqFun ℂ ((lebesgue ℂ E μ p₀ p₁).sumSpaceEmbed (toSum u))) p μ :=
  memLp_iff.2 ((eLpNorm_toAEEqFun_le hθ hp hp_top u).trans_lt ENNReal.ofReal_lt_top)

variable [SigmaFinite μ] (hθ : θ ∈ Ioo (0 : ℝ) 1)
  (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹) (hp_top : p ≠ ∞)

private theorem toLp_add (u v : (lebesgue ℂ E μ p₀ p₁).ComplexMethodSpace θ) :
    (memLp_toAEEqFun hθ hp hp_top (u + v)).toLp _ =
      (memLp_toAEEqFun hθ hp hp_top u).toLp _ + (memLp_toAEEqFun hθ hp hp_top v).toLp _ := by
  rw [← MemLp.toLp_add]
  refine MemLp.toLp_congr _ _ ?_
  simp only [map_add]
  exact AEEqFun.coeFn_add _ _

private theorem toLp_smul (c : ℂ) (u : (lebesgue ℂ E μ p₀ p₁).ComplexMethodSpace θ) :
    (memLp_toAEEqFun hθ hp hp_top (c • u)).toLp _ =
      c • (memLp_toAEEqFun hθ hp hp_top u).toLp _ := by
  rw [← MemLp.toLp_const_smul]
  refine MemLp.toLp_congr _ _ ?_
  simp only [map_smul]
  exact AEEqFun.coeFn_smul _ _

private theorem norm_toLp_le (u : (lebesgue ℂ E μ p₀ p₁).ComplexMethodSpace θ) :
    ‖(memLp_toAEEqFun hθ hp hp_top u).toLp _‖ ≤ 1 * ‖u‖ := by
  rw [one_mul, Lp.norm_toLp]
  exact ENNReal.toReal_le_of_le_ofReal (norm_nonneg u) (eLpNorm_toAEEqFun_le hθ hp hp_top u)

variable [Fact (1 ≤ p)]

/-- **The inclusion `[L^{p₀}, L^{p₁}]_θ → Lᵖ`.** On a σ-finite measure space, for `0 < θ < 1` and
`1 / p = (1 - θ) / p₀ + θ / p₁` with `p < ∞`, every element of the complex interpolation space of
the Lebesgue couple is a function of `Lᵖ`. The inclusion does not increase norms
(`norm_lebesgueToLp_le`) and lies over the embeddings of both spaces into `L¹ + L^∞`
(`ofLp_lebesgueToLp`). -/
def lebesgueToLp : (lebesgue ℂ E μ p₀ p₁).ComplexMethodSpace θ →L[ℂ] Lp E p μ :=
  LinearMap.mkContinuous
    { toFun u := (memLp_toAEEqFun hθ hp hp_top u).toLp _
      map_add' := toLp_add hθ hp hp_top
      map_smul' := toLp_smul hθ hp hp_top }
    1 (norm_toLp_le hθ hp hp_top)

/-- The inclusion sends `u` to the class in `Lᵖ` of the function of `L¹ + L^∞` it represents. -/
theorem lebesgueToLp_apply (u : (lebesgue ℂ E μ p₀ p₁).ComplexMethodSpace θ) :
    lebesgueToLp hθ hp hp_top u = (memLp_toAEEqFun hθ hp hp_top u).toLp _ :=
  (rfl)

/-- The inclusion `[L^{p₀}, L^{p₁}]_θ → Lᵖ` is compatible with the embeddings of both spaces into
`L¹ + L^∞`. -/
@[simp]
theorem ofLp_lebesgueToLp (u : (lebesgue ℂ E μ p₀ p₁).ComplexMethodSpace θ) :
    (L1AddLinfty.ofLp (lebesgueToLp hθ hp hp_top u) : L1AddLinfty ℂ E μ) =
      (lebesgue ℂ E μ p₀ p₁).sumSpaceEmbed (toSum u) := by
  refine L1AddLinfty.toAEEqFun_injective ?_
  rw [L1AddLinfty.toAEEqFun_ofLp, lebesgueToLp_apply]
  exact AEEqFun.ext (MemLp.coeFn_toLp _)

/-- **`‖u‖_p ≤ ‖u‖_θ`** for `u ∈ [L^{p₀}, L^{p₁}]_θ`. -/
theorem norm_lebesgueToLp_le (u : (lebesgue ℂ E μ p₀ p₁).ComplexMethodSpace θ) :
    ‖lebesgueToLp hθ hp hp_top u‖ ≤ ‖u‖ := by
  rw [lebesgueToLp_apply, ← one_mul ‖u‖]
  exact norm_toLp_le hθ hp hp_top u

/-- The inclusion `[L^{p₀}, L^{p₁}]_θ → Lᵖ` has operator norm at most one. -/
theorem opNorm_lebesgueToLp_le : ‖lebesgueToLp (E := E) (μ := μ) hθ hp hp_top‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- The inclusion `[L^{p₀}, L^{p₁}]_θ → Lᵖ` is injective. -/
theorem lebesgueToLp_injective :
    Function.Injective (lebesgueToLp (E := E) (μ := μ) hθ hp hp_top) := fun u v huv =>
  toSum_injective <| (lebesgue ℂ E μ p₀ p₁).sumSpaceEmbed_injective <| by
    rw [← ofLp_lebesgueToLp hθ hp hp_top, huv, ofLp_lebesgueToLp]

end ComplexMethodSpace

/-! ### The identification `[L^{p₀}, L^{p₁}]_θ = Lᵖ` -/

section Equiv

variable [CompleteSpace E] [SigmaFinite μ] {p₀ p₁ p : ℝ≥0∞} [Fact (1 ≤ p₀)] [Fact (1 ≤ p₁)]
  [Fact (1 ≤ p)] {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1)
  (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹) (hp_top : p ≠ ∞)

/-- The inclusion `[L^{p₀}, L^{p₁}]_θ → Lᵖ` is a left inverse of the inclusion
`Lᵖ → [L^{p₀}, L^{p₁}]_θ`. -/
@[simp]
theorem ComplexMethodSpace.lebesgueToLp_lpToLebesgueComplexMethod (f : Lp E p μ) :
    ComplexMethodSpace.lebesgueToLp hθ hp hp_top
        (lpToLebesgueComplexMethod (Ioo_subset_Icc_self hθ) hp hp_top f) = f :=
  L1AddLinfty.ofLp_injective (by
    rw [ComplexMethodSpace.ofLp_lebesgueToLp, sumSpaceEmbed_toSum_lpToLebesgueComplexMethod])

/-- The inclusion `Lᵖ → [L^{p₀}, L^{p₁}]_θ` is a left inverse of the inclusion
`[L^{p₀}, L^{p₁}]_θ → Lᵖ`. -/
@[simp]
theorem lpToLebesgueComplexMethod_lebesgueToLp
    (u : (lebesgue ℂ E μ p₀ p₁).ComplexMethodSpace θ) :
    lpToLebesgueComplexMethod (Ioo_subset_Icc_self hθ) hp hp_top
        (ComplexMethodSpace.lebesgueToLp hθ hp hp_top u) = u :=
  ComplexMethodSpace.toSum_injective <| (lebesgue ℂ E μ p₀ p₁).sumSpace_ext <| by
    rw [sumSpaceEmbed_toSum_lpToLebesgueComplexMethod, ComplexMethodSpace.ofLp_lebesgueToLp]

/-- **Complex interpolation of Lebesgue spaces** (Calderón; Bergh–Löfström, Theorem 5.1.1). On a
σ-finite measure space, for `1 ≤ p₀, p₁ ≤ ∞`, `0 < θ < 1` and the interpolated exponent
`1 / p = (1 - θ) / p₀ + θ / p₁` with `p < ∞`, the complex interpolation space of the Lebesgue
couple of functions with values in a complex Hilbert space is `Lᵖ`, with equal norms:
`[L^{p₀}, L^{p₁}]_θ ≃ₗᵢ[ℂ] Lᵖ`. The identification and its inverse are the inclusions
`ComplexMethodSpace.lebesgueToLp` and `lpToLebesgueComplexMethod`, which lie over the embeddings
of both spaces into `L¹ + L^∞`. -/
def lebesgueComplexMethodEquiv :
    (lebesgue ℂ E μ p₀ p₁).ComplexMethodSpace θ ≃ₗᵢ[ℂ] Lp E p μ where
  toLinearEquiv := LinearEquiv.ofLinearMap
    (ComplexMethodSpace.lebesgueToLp hθ hp hp_top : _ →L[ℂ] Lp E p μ).toLinearMap
    (lpToLebesgueComplexMethod (Ioo_subset_Icc_self hθ) hp hp_top :
      Lp E p μ →L[ℂ] _).toLinearMap
    (LinearMap.ext <| ComplexMethodSpace.lebesgueToLp_lpToLebesgueComplexMethod hθ hp hp_top)
    (LinearMap.ext <| lpToLebesgueComplexMethod_lebesgueToLp hθ hp hp_top)
  norm_map' u := by
    refine le_antisymm (ComplexMethodSpace.norm_lebesgueToLp_le hθ hp hp_top u) ?_
    conv_lhs => rw [← lpToLebesgueComplexMethod_lebesgueToLp hθ hp hp_top u]
    exact norm_lpToLebesgueComplexMethod_le _ hp hp_top _

@[simp]
theorem lebesgueComplexMethodEquiv_apply (u : (lebesgue ℂ E μ p₀ p₁).ComplexMethodSpace θ) :
    lebesgueComplexMethodEquiv hθ hp hp_top u = ComplexMethodSpace.lebesgueToLp hθ hp hp_top u :=
  (rfl)

@[simp]
theorem lebesgueComplexMethodEquiv_symm_apply (f : Lp E p μ) :
    (lebesgueComplexMethodEquiv hθ hp hp_top).symm f =
      lpToLebesgueComplexMethod (Ioo_subset_Icc_self hθ) hp hp_top f :=
  (rfl)

end Equiv

end TauCeti.CompatibleCouple
