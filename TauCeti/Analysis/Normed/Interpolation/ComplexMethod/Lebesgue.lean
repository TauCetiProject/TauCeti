/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Interpolation.ComplexMethod.Basic
public import TauCeti.Analysis.Normed.Interpolation.Lebesgue
import Mathlib.Analysis.Complex.Hadamard
import TauCeti.Analysis.Complex.VerticalStrip
import TauCeti.Data.ENNReal.InterpolatedExponent
import TauCeti.MeasureTheory.Function.Holder
import TauCeti.MeasureTheory.Function.Lp.Duality
import TauCeti.MeasureTheory.Function.SimpleFunc.AnalyticFamily

/-!
# Complex interpolation of Lebesgue spaces

On a σ-finite measure space, let `1 ≤ p₀, p₁ ≤ ∞`, `0 < θ < 1` and
`1 / p = (1 - θ) / p₀ + θ / p₁` with `p < ∞`. Then the complex interpolation space of the
Lebesgue couple `(L^{p₀}, L^{p₁})` of complex-valued (scalar) functions is `Lᵖ`, with equal norms
(Bergh–Löfström, Theorem 5.1.1):

`[L^{p₀}, L^{p₁}]_θ = Lᵖ`.

Both spaces sit inside `L¹ + L^∞`, and `TauCeti.CompatibleCouple.lpEquivComplexMethodSpace` is the
linear isometric equivalence `Lᵖ ≃ [L^{p₀}, L^{p₁}]_θ` that is the identity there
(`TauCeti.CompatibleCouple.sumSpaceEmbed_toSum_lpEquivComplexMethodSpace`). The scalars are
complex, as the complex method requires. The inclusion `Lᵖ ⊆ [L^{p₀}, L^{p₁}]_θ` holds without
σ-finiteness.

The two inclusions are proved separately, by Thorin's analytic families through simple functions
(`TauCeti.AnalyticFamily.powSign`).

* `Lᵖ ⊆ [L^{p₀}, L^{p₁}]_θ` with `‖f‖_θ ≤ ‖f‖_p`
  (`TauCeti.CompatibleCouple.exists_sumSpaceEmbed_toSum_eq_ofLp`). For a simple `f` with
  `‖f‖_p = 1`, the function `F(z) = exp (δ (z - θ)²) sgn(f) |f| ^ {p ((1 - z) / p₀ + z / p₁)}` is
  admissible, `F(θ) = f`, and on the line `re z = j` its values have `L^{p_j}` norm at most
  `exp (δ (|θ| + 1)²)`, which tends to `1` as `δ → 0`. Simple functions are dense in `Lᵖ` for
  `p < ∞` and the interpolation space is complete, so the inclusion extends to all of `Lᵖ`.
* `[L^{p₀}, L^{p₁}]_θ ⊆ Lᵖ` with `‖u‖_p ≤ ‖u‖_θ`
  (`TauCeti.CompatibleCouple.exists_ofLp_eq_sumSpaceEmbed_toSum`), on a σ-finite measure space.
  Given an admissible `F` with `F(θ) = u` and a simple `k` with `‖k‖_{p'} ≤ 1`, the function
  `Φ(z) = ∫ F(z) k_z` with `k_z = sgn(k) |k| ^ {p' ((1 - z) / p₀' + z / p₁')}` is a finite
  combination of continuous linear functionals of `F(z)`, hence holomorphic, and Hölder's
  inequality bounds it on the two boundary lines by the norms of the traces of `F`. The
  three-lines theorem bounds `|∫ u k| = |Φ(θ)|`, and duality against simple functions,
  applied to truncations of `u`, bounds `‖u‖_p`.

## References

* A.-P. Calderón, *Intermediate spaces and interpolation, the complex method*, Studia Math. 24
  (1964), 113–190.
* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Grundlehren 223,
  Springer, 1976, Theorem 5.1.1.
-/

public noncomputable section

open MeasureTheory Complex Complex.HadamardThreeLines Filter Set Topology TauCeti.AnalyticFamily
open scoped ENNReal ZeroAtInfty
open SimpleFunc (fiberIndicator map_apply_eq_sum_mul_fiberIndicator memLp_fiberIndicator
  integral_mul_map_eq_sum eLpNorm_map_powSign_exponent_le_one_of_re_eq_zero
  eLpNorm_map_powSign_exponent_le_one_of_re_eq_one)

namespace TauCeti.CompatibleCouple

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α} {p₀ p₁ p : ℝ≥0∞}
  [Fact (1 ≤ p₀)] [Fact (1 ≤ p₁)] [Fact (1 ≤ p)] {θ : ℝ}

/-! ### Fibre indicators in `L^{p₀} ∩ L^{p₁}` -/

open Classical in
/-- The fibre indicator `1_{u = c}` of a simple function as an element of `L^{p₀} ∩ L^{p₁}` when
it lies in both spaces, and `0` otherwise. -/
private def fiberInter (μ : Measure α) (p₀ p₁ : ℝ≥0∞) [Fact (1 ≤ p₀)] [Fact (1 ≤ p₁)]
    (u : SimpleFunc α ℂ) (c : ℂ) : (lebesgue ℂ ℂ μ p₀ p₁).inter :=
  if h : MemLp (fiberIndicator ℂ u c) p₀ μ ∧ MemLp (fiberIndicator ℂ u c) p₁ μ then
    ⟨(h.1.toLp _, h.2.toLp _),
      mem_lebesgue_inter_iff.2 (h.1.coeFn_toLp.trans h.2.coeFn_toLp.symm)⟩
  else 0

private theorem coeFn_interFst_fiberInter {u : SimpleFunc α ℂ} {c : ℂ}
    (h₀ : MemLp (fiberIndicator ℂ u c) p₀ μ) (h₁ : MemLp (fiberIndicator ℂ u c) p₁ μ) :
    ⇑((lebesgue ℂ ℂ μ p₀ p₁).interFst (fiberInter μ p₀ p₁ u c)) =ᵐ[μ] fiberIndicator ℂ u c := by
  unfold fiberInter
  split_ifs with h
  · rw [interFst_apply]
    exact h₀.coeFn_toLp
  · exact absurd ⟨h₀, h₁⟩ h

private theorem coeFn_interSnd_fiberInter {u : SimpleFunc α ℂ} {c : ℂ}
    (h₀ : MemLp (fiberIndicator ℂ u c) p₀ μ) (h₁ : MemLp (fiberIndicator ℂ u c) p₁ μ) :
    ⇑((lebesgue ℂ ℂ μ p₀ p₁).interSnd (fiberInter μ p₀ p₁ u c)) =ᵐ[μ] fiberIndicator ℂ u c := by
  unfold fiberInter
  split_ifs with h
  · rw [interSnd_apply]
    exact h₁.coeFn_toLp
  · exact absurd ⟨h₀, h₁⟩ h

/-- A combination of `Lq` classes of the fibre indicators of `u` is the class of `u.map φ`. -/
private theorem coeFn_sum_smul_eq_map {q : ℝ≥0∞} (u : SimpleFunc α ℂ)
    (G : ℂ → Lp ℂ q μ) (hG : ∀ c ≠ 0, ⇑(G c) =ᵐ[μ] fiberIndicator ℂ u c) (φ : ℂ → ℂ)
    (hφ : φ 0 = 0) :
    ⇑(∑ c ∈ u.range, φ c • G c) =ᵐ[μ] u.map φ := by
  have h : ∀ c ∈ u.range, ∀ᵐ x ∂μ, (φ c • G c) x = φ c * fiberIndicator ℂ u c x := by
    intro c _
    rcases eq_or_ne c 0 with rfl | hc
    · filter_upwards [Lp.coeFn_smul (φ 0) (G 0)] with x hx
      rw [hx, Pi.smul_apply, smul_eq_mul, hφ, zero_mul, zero_mul]
    · filter_upwards [Lp.coeFn_smul (φ c) (G c), hG c hc] with x hx hx'
      rw [hx, Pi.smul_apply, smul_eq_mul, hx']
  filter_upwards [Lp.coeFn_finsetSum u.range (fun c => φ c • G c),
    (eventually_all_finset u.range).2 h] with x hsum hx
  rw [hsum, Finset.sum_apply, map_apply_eq_sum_mul_fiberIndicator]
  exact Finset.sum_congr rfl hx

/-- A combination `∑ c, (a * powSign b c) • G c` of `Lq` classes of the fibre indicators of `u`
has norm at most `M` when `‖a‖ ≤ M` and the member `u.map (powSign b)` of the analytic family
lies in the unit ball of `Lq`. -/
private theorem norm_sum_mul_powSign_smul_le {q : ℝ≥0∞} [Fact (1 ≤ q)] (u : SimpleFunc α ℂ)
    (G : ℂ → Lp ℂ q μ) (hG : ∀ c ≠ 0, ⇑(G c) =ᵐ[μ] fiberIndicator ℂ u c) {a b : ℂ} {M : ℝ}
    (ha : ‖a‖ ≤ M) (hb : eLpNorm (u.map (powSign b)) q μ ≤ 1) :
    ‖∑ c ∈ u.range, (a * powSign b c) • G c‖ ≤ M := by
  have hle : ‖∑ c ∈ u.range, powSign b c • G c‖ ≤ 1 := by
    rw [Lp.norm_def, eLpNorm_congr_ae (coeFn_sum_smul_eq_map u G hG _ (powSign_zero_right b))]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hb)
  simp_rw [mul_smul, ← Finset.smul_sum]
  rw [norm_smul, ← mul_one M]
  exact mul_le_mul ha hle (norm_nonneg _) ((norm_nonneg a).trans ha)

omit [Fact (1 ≤ p)] in
private theorem injective_sumSpaceEmbed_toSum :
    Function.Injective fun v : (lebesgue ℂ ℂ μ p₀ p₁).ComplexMethodSpace θ =>
      (lebesgue ℂ ℂ μ p₀ p₁).sumSpaceEmbed (ComplexMethodSpace.toSum v) :=
  (lebesgue ℂ ℂ μ p₀ p₁).sumSpaceEmbed_injective.comp ComplexMethodSpace.toSum_injective

/-! ### `Lᵖ ⊆ [L^{p₀}, L^{p₁}]_θ` -/

section Inclusion

variable (hθ : θ ∈ Ioo (0 : ℝ) 1)
  (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹)
include hθ hp

/-- The admissible function `exp (δ (z - θ)²) sgn(f) |f| ^ {p ((1 - z) / p₀ + z / p₁)}` through a
simple function `f` in the unit ball of `Lᵖ`: it takes the value `f` at `θ` and its boundary
traces have norm at most `exp (δ (|θ| + 1)²)`. -/
private theorem exists_isStripFunction_of_simpleFunc {f : SimpleFunc α ℂ} (hfm : MemLp f p μ)
    (hf : eLpNorm f p μ ≤ 1) {δ : ℝ} (hδ : 0 < δ) :
    ∃ F g, (lebesgue ℂ ℂ μ p₀ p₁).IsStripFunction F g ∧
      (lebesgue ℂ ℂ μ p₀ p₁).sumSpaceEmbed (F θ) = L1AddLinfty.ofLp (hfm.toLp f) ∧
      ‖g‖ ≤ Real.exp (δ * (|θ| + 1) ^ 2) := by
  set C := lebesgue ℂ ℂ μ p₀ p₁
  have hp₀ : p₀ ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p₀)).ne'
  have hp₁ : p₁ ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p₁)).ne'
  set P := exponent (p₀⁻¹).toReal (p₁⁻¹).toReal θ
  -- The analytic family through `f` lies in the unit balls of `L^{p₀}` and `L^{p₁}` on the two
  -- boundary lines; in particular the fibres of `f` lie in both spaces.
  have hb₀ (z : ℂ) (hz : z.re = 0) : eLpNorm (f.map (powSign (P z))) p₀ μ ≤ 1 :=
    eLpNorm_map_powSign_exponent_le_one_of_re_eq_zero f hp₀ hp₁ hθ hp hf hz
  have hb₁ (z : ℂ) (hz : z.re = 1) : eLpNorm (f.map (powSign (P z))) p₁ μ ≤ 1 :=
    eLpNorm_map_powSign_exponent_le_one_of_re_eq_one f hp₀ hp₁ hθ hp hf hz
  have hfib (c : ℂ) (hc : c ≠ 0) :
      MemLp (fiberIndicator ℂ f c) p₀ μ ∧ MemLp (fiberIndicator ℂ f c) p₁ μ :=
    ⟨memLp_fiberIndicator f hc (memLp_iff.2 ((hb₀ 0 (by simp)).trans_lt ENNReal.one_lt_top)),
      memLp_fiberIndicator f hc (memLp_iff.2 ((hb₁ 1 (by simp)).trans_lt ENNReal.one_lt_top))⟩
  set x := fiberInter μ p₀ p₁ f
  set ψ : ℂ → ℂ → ℂ := fun c z => stripGaussian δ θ z * powSign (P z) c
  -- The coefficients are entire, bounded on the strip and decay along its boundary lines.
  have hψd (c : ℂ) : DiffContOnCl ℂ (ψ c) (verticalStrip 0 1) :=
    ((differentiable_stripGaussian δ θ).mul (differentiable_powSign_exponent _ _ _ c)).diffContOnCl
  set K : ℂ → ℝ := fun c =>
    Real.exp ((1 + |exponentSlope (p₀⁻¹).toReal (p₁⁻¹).toReal θ|) * |Real.log ‖c‖|)
  have hψb (c : ℂ) (z : ℂ) (hz : z ∈ verticalClosedStrip 0 1) :
      ‖ψ c z‖ ≤ Real.exp (δ * (|θ| + 1) ^ 2) * K c := by
    rw [TauCeti.Complex.HadamardThreeLines.mem_verticalClosedStrip_iff] at hz
    rw [norm_mul]
    exact mul_le_mul (norm_stripGaussian_le hδ.le θ hz)
      (norm_powSign_exponent_le (Ioo_subset_Icc_self hθ) hz c) (norm_nonneg _) (Real.exp_pos _).le
  have hψt (c : ℂ) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) :
      Tendsto (fun t : ℝ => ψ c (a + t * I)) (cocompact ℝ) (𝓝 0) := by
    refine squeeze_zero_norm (fun t => ?_)
      (by simpa using (tendsto_norm_stripGaussian hδ θ a).mul_const (K c))
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left
      (norm_powSign_exponent_le (Ioo_subset_Icc_self hθ) (by simpa using ha) c) (norm_nonneg _)
  obtain ⟨g, hF, hg₀, hg₁⟩ := C.exists_isStripFunction_sum_smul f.range ψ x
    (fun c _ => hψd c) (fun c _ => ⟨_, hψb c⟩)
    (fun c _ => by simpa using hψt c 0 (by simp))
    (fun c _ => by simpa using hψt c 1 (by simp))
  refine ⟨_, g, hF, ?_, ?_⟩
  · -- At `θ` the Gaussian factor is `1` and the analytic family passes through `f`.
    have hψθ (c : ℂ) : ψ c θ = powSign 1 c := by
      simp [ψ, P]
    simp only [hψθ, map_sum, map_smul, sumSpaceEmbed_fstToSum, C, lebesgue_embed₀]
    rw [show ∑ c ∈ f.range, powSign 1 c • L1AddLinfty.ofLp (C.interFst (x c)) =
        L1AddLinfty.ofLp (∑ c ∈ f.range, powSign 1 c • C.interFst (x c)) by
      simp only [map_sum, map_smul], L1AddLinfty.ofLp_eq_ofLp_iff]
    refine (coeFn_sum_smul_eq_map f _ (fun c hc => coeFn_interFst_fiberInter (hfib c hc).1
      (hfib c hc).2) _ (powSign_zero_right 1)).trans ?_
    rw [SimpleFunc.map_powSign_one]
    exact hfm.coeFn_toLp.symm
  · -- On each boundary line, the trace is the Gaussian factor times the analytic family.
    have hexp : 0 ≤ Real.exp (δ * (|θ| + 1) ^ 2) := (Real.exp_pos _).le
    refine norm_prod_le_iff.2 ⟨(ZeroAtInftyContinuousMap.norm_le hexp).2 fun t => ?_,
      (ZeroAtInftyContinuousMap.norm_le hexp).2 fun t => ?_⟩
    · rw [hg₀]
      exact norm_sum_mul_powSign_smul_le f _
        (fun c hc => coeFn_interFst_fiberInter (hfib c hc).1 (hfib c hc).2)
        (norm_stripGaussian_le hδ.le θ (z := t * I) (by simp)) (hb₀ _ (by simp))
    · rw [hg₁]
      exact norm_sum_mul_powSign_smul_le f _
        (fun c hc => coeFn_interSnd_fiberInter (hfib c hc).1 (hfib c hc).2)
        (norm_stripGaussian_le hδ.le θ (z := 1 + t * I) (by simp)) (hb₁ _ (by simp))

/-- A simple function in the unit ball of `Lᵖ` lies in the unit ball of `[L^{p₀}, L^{p₁}]_θ`. -/
private theorem exists_norm_le_one_of_simpleFunc {f : SimpleFunc α ℂ} (hfm : MemLp f p μ)
    (hf : eLpNorm f p μ ≤ 1) :
    ∃ v : (lebesgue ℂ ℂ μ p₀ p₁).ComplexMethodSpace θ,
      (lebesgue ℂ ℂ μ p₀ p₁).sumSpaceEmbed (ComplexMethodSpace.toSum v) =
        L1AddLinfty.ofLp (hfm.toLp f) ∧ ‖v‖ ≤ 1 := by
  have hθ' : θ ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hθ
  -- For each `δ > 0` the admissible function above gives an element of norm at most
  -- `exp (δ (|θ| + 1)²)`; all of them lie over `f`, so they coincide.
  have key (δ : ℝ) (hδ : 0 < δ) : ∃ v : (lebesgue ℂ ℂ μ p₀ p₁).ComplexMethodSpace θ,
      (lebesgue ℂ ℂ μ p₀ p₁).sumSpaceEmbed (ComplexMethodSpace.toSum v) =
        L1AddLinfty.ofLp (hfm.toLp f) ∧ ‖v‖ ≤ Real.exp (δ * (|θ| + 1) ^ 2) := by
    obtain ⟨F, g, hF, hFθ, hg⟩ := exists_isStripFunction_of_simpleFunc hθ hp hfm hf hδ
    obtain ⟨v, hv⟩ := (ComplexMethodSpace.exists_toSum_eq_iff hθ').2 ⟨F, g, hF, rfl⟩
    exact ⟨v, hv ▸ hFθ, (ComplexMethodSpace.norm_le_of_toSum_eq hθ' hF hv).trans hg⟩
  obtain ⟨v, hv, -⟩ := key 1 one_pos
  refine ⟨v, hv, ?_⟩
  have hle (δ : ℝ) (hδ : 0 < δ) : ‖v‖ ≤ Real.exp (δ * (|θ| + 1) ^ 2) := by
    obtain ⟨w, hw, hwδ⟩ := key δ hδ
    have : w = v := ComplexMethodSpace.ext <|
      (lebesgue ℂ ℂ μ p₀ p₁).sumSpaceEmbed_injective (hw.trans hv.symm)
    exact this ▸ hwδ
  have hlim : Tendsto (fun δ : ℝ => Real.exp (δ * (|θ| + 1) ^ 2)) (𝓝[>] 0) (𝓝 1) := by
    have : Continuous fun δ : ℝ => Real.exp (δ * (|θ| + 1) ^ 2) := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall hle)

/-- A simple function in `Lᵖ` lies in `[L^{p₀}, L^{p₁}]_θ`, with `‖f‖_θ ≤ ‖f‖_p`. -/
private theorem exists_norm_le_of_simpleFunc {f : SimpleFunc α ℂ} (hfm : MemLp f p μ) :
    ∃ v : (lebesgue ℂ ℂ μ p₀ p₁).ComplexMethodSpace θ,
      (lebesgue ℂ ℂ μ p₀ p₁).sumSpaceEmbed (ComplexMethodSpace.toSum v) =
        L1AddLinfty.ofLp (hfm.toLp f) ∧ ‖v‖ ≤ ‖hfm.toLp f‖ := by
  set a := ‖hfm.toLp f‖
  rcases (norm_nonneg (hfm.toLp f)).eq_or_lt with ha | ha
  · refine ⟨0, ?_, by rw [norm_zero]; exact norm_nonneg _⟩
    rw [norm_eq_zero.1 ha.symm]
    simp
  -- Normalize `f` to the unit sphere of `Lᵖ`.
  have hfm' : MemLp ((((a⁻¹ : ℝ) : ℂ)) • f) p μ := hfm.const_smul _
  have ha' : a = (eLpNorm f p μ).toReal := Lp.norm_toLp _ _
  have hf0 : eLpNorm f p μ ≠ 0 := fun h => by simp [h] at ha
  have hf' : eLpNorm ((((a⁻¹ : ℝ) : ℂ)) • f) p μ ≤ 1 := by
    rw [ha']
    exact (f.eLpNorm_inv_toReal_smul_eq_one hf0 hfm.eLpNorm_lt_top.ne).le
  obtain ⟨v, hv, hvn⟩ := exists_norm_le_one_of_simpleFunc hθ hp hfm' hf'
  refine ⟨(a : ℂ) • v, ?_, ?_⟩
  · have hto : hfm'.toLp _ = (((a⁻¹ : ℝ) : ℂ)) • hfm.toLp f := MemLp.toLp_const_smul _ hfm
    rw [map_smul, map_smul, hv, hto, map_smul, smul_smul, ← ofReal_mul,
      mul_inv_cancel₀ ha.ne', ofReal_one, one_smul]
  · rw [norm_smul, norm_real, Real.norm_of_nonneg ha.le]
    exact mul_le_of_le_one_right ha.le hvn

/-- **`Lᵖ ⊆ [L^{p₀}, L^{p₁}]_θ`.** Let `1 ≤ p₀, p₁ ≤ ∞`, `0 < θ < 1` and
`1 / p = (1 - θ) / p₀ + θ / p₁` with `p < ∞`. Every `f ∈ Lᵖ` lies in the complex interpolation
space `[L^{p₀}, L^{p₁}]_θ`, with `‖f‖_θ ≤ ‖f‖_p`. -/
theorem exists_sumSpaceEmbed_toSum_eq_ofLp (hpt : p ≠ ∞) (f : Lp ℂ p μ) :
    ∃ v : (lebesgue ℂ ℂ μ p₀ p₁).ComplexMethodSpace θ,
      (lebesgue ℂ ℂ μ p₀ p₁).sumSpaceEmbed (ComplexMethodSpace.toSum v) =
        L1AddLinfty.ofLp f ∧ ‖v‖ ≤ ‖f‖ := by
  set J : (lebesgue ℂ ℂ μ p₀ p₁).ComplexMethodSpace θ →L[ℂ] L1AddLinfty ℂ ℂ μ :=
    (lebesgue ℂ ℂ μ p₀ p₁).sumSpaceEmbed.comp ComplexMethodSpace.toSum
  have hJ : Function.Injective J := injective_sumSpaceEmbed_toSum
  -- The inclusion holds on the dense subgroup of simple functions.
  have hsimple (u : Lp ℂ p μ) (hu : u ∈ Lp.simpleFunc ℂ p μ) : ∃ v, J v = L1AddLinfty.ofLp u ∧
      ‖v‖ ≤ ‖u‖ := by
    obtain ⟨v, hv, hvn⟩ := exists_norm_le_of_simpleFunc hθ hp
      (Lp.simpleFunc.memLp (⟨u, hu⟩ : Lp.simpleFunc ℂ p μ))
    have hto : (Lp.simpleFunc.memLp (⟨u, hu⟩ : Lp.simpleFunc ℂ p μ)).toLp _ = u :=
      congrArg Subtype.val (Lp.simpleFunc.toLp_toSimpleFunc ⟨u, hu⟩)
    rw [hto] at hv hvn
    exact ⟨v, hv, hvn⟩
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.1 (Lp.simpleFunc.dense (E := ℂ) hpt f)
  choose v hv hvn using fun n => hsimple (u n) (hu n)
  -- The images of a Cauchy sequence of simple functions form a Cauchy sequence.
  have hdist (m n : ℕ) : dist (v m) (v n) ≤ dist (u m) (u n) := by
    obtain ⟨w, hw, hwn⟩ := hsimple (u m - u n) (AddSubgroup.sub_mem _ (hu m) (hu n))
    have : w = v m - v n := hJ (by rw [hw, map_sub, map_sub, hv, hv])
    rw [dist_eq_norm, dist_eq_norm, ← this]
    exact hwn
  have hv_cauchy : CauchySeq v := Metric.cauchySeq_iff.2 fun ε hε => by
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hlim.cauchySeq ε hε
    exact ⟨N, fun m hm n hn => (hdist m n).trans_lt (hN m hm n hn)⟩
  obtain ⟨w, hw⟩ := cauchySeq_tendsto_of_complete hv_cauchy
  refine ⟨w, tendsto_nhds_unique ((J.continuous.tendsto w).comp hw) ?_,
    le_of_tendsto_of_tendsto' hw.norm hlim.norm hvn⟩
  simpa [Function.comp_def, hv] using (L1AddLinfty.ofLp.continuous.tendsto f).comp hlim

end Inclusion

/-! ### `[L^{p₀}, L^{p₁}]_θ ⊆ Lᵖ` -/

section Pairing

/-- Integration against a function `φ ∈ L^{p₀'} ∩ L^{p₁'}`, a continuous linear functional on
`L^{p₀} + L^{p₁}`. -/
private def sumPairing (φ : α → ℂ) (h₀ : MemLp φ p₀.conjExponent μ)
    (h₁ : MemLp φ p₁.conjExponent μ) : (lebesgue ℂ ℂ μ p₀ p₁).SumSpace →L[ℂ] ℂ :=
  haveI : Fact (1 ≤ p₀.conjExponent) := ⟨ENNReal.HolderConjugate.one_le _ p₀⟩
  haveI : Fact (1 ≤ p₁.conjExponent) := ⟨ENNReal.HolderConjugate.one_le _ p₁⟩
  (lebesgue ℂ ℂ μ p₀ p₁).sumLift
    (((ContinuousLinearMap.mul ℂ ℂ).lpPairing μ p₀ p₀.conjExponent).flip (h₀.toLp φ))
    (((ContinuousLinearMap.mul ℂ ℂ).lpPairing μ p₁ p₁.conjExponent).flip (h₁.toLp φ))
    fun x => by
      simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.lpPairing_mul_eq_integral,
        interFst_apply, interSnd_apply]
      refine integral_congr_ae ?_
      filter_upwards [mem_lebesgue_inter_iff.1 x.2, h₀.coeFn_toLp, h₁.coeFn_toLp]
        with y hy hy₀ hy₁
      rw [hy, hy₀, hy₁]

private theorem sumPairing_fstToSum {φ : α → ℂ} (h₀ : MemLp φ p₀.conjExponent μ)
    (h₁ : MemLp φ p₁.conjExponent μ) (u : Lp ℂ p₀ μ) :
    sumPairing φ h₀ h₁ ((lebesgue ℂ ℂ μ p₀ p₁).fstToSum u) = ∫ x, u x * φ x ∂μ := by
  have : Fact (1 ≤ p₀.conjExponent) := ⟨ENNReal.HolderConjugate.one_le _ p₀⟩
  have : Fact (1 ≤ p₁.conjExponent) := ⟨ENNReal.HolderConjugate.one_le _ p₁⟩
  rw [sumPairing, sumLift_fstToSum, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.lpPairing_mul_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [h₀.coeFn_toLp] with x hx
  rw [hx]

private theorem sumPairing_sndToSum {φ : α → ℂ} (h₀ : MemLp φ p₀.conjExponent μ)
    (h₁ : MemLp φ p₁.conjExponent μ) (u : Lp ℂ p₁ μ) :
    sumPairing φ h₀ h₁ ((lebesgue ℂ ℂ μ p₀ p₁).sndToSum u) = ∫ x, u x * φ x ∂μ := by
  have : Fact (1 ≤ p₀.conjExponent) := ⟨ENNReal.HolderConjugate.one_le _ p₀⟩
  have : Fact (1 ≤ p₁.conjExponent) := ⟨ENNReal.HolderConjugate.one_le _ p₁⟩
  rw [sumPairing, sumLift_sndToSum, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.lpPairing_mul_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [h₁.coeFn_toLp] with x hx
  rw [hx]

open Classical in
/-- Integration against the fibre indicator `1_{k = d}` of a simple function, as a functional on
`L^{p₀} + L^{p₁}` when that indicator lies in `L^{p₀'} ∩ L^{p₁'}`, and `0` otherwise. -/
private def fiberPairing (μ : Measure α) (p₀ p₁ : ℝ≥0∞) [Fact (1 ≤ p₀)] [Fact (1 ≤ p₁)]
    (k : SimpleFunc α ℂ) (d : ℂ) : (lebesgue ℂ ℂ μ p₀ p₁).SumSpace →L[ℂ] ℂ :=
  if h : MemLp (fiberIndicator ℂ k d) p₀.conjExponent μ ∧
      MemLp (fiberIndicator ℂ k d) p₁.conjExponent μ then
    sumPairing _ h.1 h.2
  else 0

private theorem fiberPairing_fstToSum {k : SimpleFunc α ℂ} {d : ℂ}
    (h₀ : MemLp (fiberIndicator ℂ k d) p₀.conjExponent μ)
    (h₁ : MemLp (fiberIndicator ℂ k d) p₁.conjExponent μ)
    (u : Lp ℂ p₀ μ) :
    fiberPairing μ p₀ p₁ k d ((lebesgue ℂ ℂ μ p₀ p₁).fstToSum u) =
      ∫ x, u x * fiberIndicator ℂ k d x ∂μ := by
  unfold fiberPairing
  split_ifs with h
  · exact sumPairing_fstToSum _ _ u
  · exact absurd ⟨h₀, h₁⟩ h

private theorem fiberPairing_sndToSum {k : SimpleFunc α ℂ} {d : ℂ}
    (h₀ : MemLp (fiberIndicator ℂ k d) p₀.conjExponent μ)
    (h₁ : MemLp (fiberIndicator ℂ k d) p₁.conjExponent μ)
    (u : Lp ℂ p₁ μ) :
    fiberPairing μ p₀ p₁ k d ((lebesgue ℂ ℂ μ p₀ p₁).sndToSum u) =
      ∫ x, u x * fiberIndicator ℂ k d x ∂μ := by
  unfold fiberPairing
  split_ifs with h
  · exact sumPairing_sndToSum _ _ u
  · exact absurd ⟨h₀, h₁⟩ h

/-- On a boundary line, the combination `∑ d, powSign w d * Λ d` of the fibre functionals `Λ d` of
`k`, evaluated at `u ∈ L^q`, is the pairing of `u` with `k.map (powSign w)`; it has modulus at most
`‖u‖` when `k.map (powSign w)` lies in the unit ball of `L^{q'}`. -/
private theorem norm_sum_mul_le_of_eLpNorm_le_one {q : ℝ≥0∞} [Fact (1 ≤ q)] (k : SimpleFunc α ℂ)
    (w : ℂ) (u : Lp ℂ q μ) (hk : ∀ d ≠ 0, MemLp (fiberIndicator ℂ k d) q.conjExponent μ)
    (hkw : eLpNorm (k.map (powSign w)) q.conjExponent μ ≤ 1) (Λ : ℂ → ℂ)
    (hΛ : ∀ d ≠ 0, Λ d = ∫ x, u x * fiberIndicator ℂ k d x ∂μ) :
    ‖∑ d ∈ k.range, powSign w d * Λ d‖ ≤ ‖u‖ := by
  have hd0 {d : ℂ} (hd : powSign w d ≠ 0) : d ≠ 0 := by
    rintro rfl
    exact hd (powSign_zero_right w)
  have h : ∑ d ∈ k.range, powSign w d * Λ d = ∫ x, u x * k.map (powSign w) x ∂μ := by
    rw [integral_mul_map_eq_sum k _ fun d _ hd => (Lp.memLp u).integrable_mul (hk d (hd0 hd))]
    refine Finset.sum_congr rfl fun d _ => ?_
    rcases eq_or_ne d 0 with rfl | hd
    · simp
    · rw [hΛ d hd]
  rw [h]
  exact Lp.norm_integral_mul_le_of_eLpNorm_le_one u hkw

end Pairing

section Reverse

variable (hθ : θ ∈ Ioo (0 : ℝ) 1)
  (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹)
include hθ hp

omit [Fact (1 ≤ p)] in
/-- **The three-lines estimate.** If `v ∈ [L^{p₀}, L^{p₁}]_θ` is the class of `a + b` in the sum,
then `|∫ (a + b) k| ≤ ‖v‖_θ` for every simple `k` in the unit ball of `L^{p'}`. -/
private theorem norm_integral_mul_le_of_le_one
    (v : (lebesgue ℂ ℂ μ p₀ p₁).ComplexMethodSpace θ) (a : Lp ℂ p₀ μ) (b : Lp ℂ p₁ μ)
    (hab : (lebesgue ℂ ℂ μ p₀ p₁).fstToSum a + (lebesgue ℂ ℂ μ p₀ p₁).sndToSum b =
      ComplexMethodSpace.toSum v)
    {k : SimpleFunc α ℂ} (hk : eLpNorm k p.conjExponent μ ≤ 1) :
    ‖∫ x, (a x + b x) * k x ∂μ‖ ≤ ‖v‖ := by
  have hθ' : θ ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hθ
  have hs := inv_conjExponent_eq_of_inv_eq (Fact.out : 1 ≤ p₀) (Fact.out : 1 ≤ p₁) hθ' hp
  have hs₀ : p₀.conjExponent ≠ 0 :=
    (zero_lt_one.trans_le (ENNReal.HolderConjugate.one_le _ p₀)).ne'
  have hs₁ : p₁.conjExponent ≠ 0 :=
    (zero_lt_one.trans_le (ENNReal.HolderConjugate.one_le _ p₁)).ne'
  set Q := exponent (p₀.conjExponent⁻¹).toReal (p₁.conjExponent⁻¹).toReal θ
  -- The analytic family through `k` lies in the unit balls of the dual endpoint spaces on the two
  -- boundary lines; in particular the fibres of `k` lie in both dual spaces.
  have hk₀ (z : ℂ) (hz : z.re = 0) : eLpNorm (k.map (powSign (Q z))) p₀.conjExponent μ ≤ 1 :=
    eLpNorm_map_powSign_exponent_le_one_of_re_eq_zero k hs₀ hs₁ hθ hs hk hz
  have hk₁ (z : ℂ) (hz : z.re = 1) : eLpNorm (k.map (powSign (Q z))) p₁.conjExponent μ ≤ 1 :=
    eLpNorm_map_powSign_exponent_le_one_of_re_eq_one k hs₀ hs₁ hθ hs hk hz
  have hfib₀ (d : ℂ) (hd : d ≠ 0) : MemLp (fiberIndicator ℂ k d) p₀.conjExponent μ :=
    memLp_fiberIndicator k hd (memLp_iff.2 ((hk₀ 0 (by simp)).trans_lt ENNReal.one_lt_top))
  have hfib₁ (d : ℂ) (hd : d ≠ 0) : MemLp (fiberIndicator ℂ k d) p₁.conjExponent μ :=
    memLp_fiberIndicator k hd (memLp_iff.2 ((hk₁ 1 (by simp)).trans_lt ENNReal.one_lt_top))
  set Λ := fiberPairing μ p₀ p₁ k
  refine le_of_forall_gt_imp_ge_of_dense fun r hr => ?_
  -- Choose an admissible function `F` with `F θ = v` and traces of norm less than `r`.
  obtain ⟨g, hg, hgr⟩ := ComplexMethodSpace.norm_lt_iff.1 hr
  set F := (lebesgue ℂ ℂ μ p₀ p₁).stripFunction g
  have hF : (lebesgue ℂ ℂ μ p₀ p₁).IsStripFunction F g :=
    (lebesgue ℂ ℂ μ p₀ p₁).isStripFunction_stripFunction g
  have hgr' : ‖(g : C₀(ℝ, Lp ℂ p₀ μ) × C₀(ℝ, Lp ℂ p₁ μ))‖ < r := by
    rwa [Submodule.norm_coe]
  have hFθ : F θ = ComplexMethodSpace.toSum v := by
    rw [← hg, ComplexMethodSpace.toSum_mk, stripEval_apply]
  set Φ : ℂ → ℂ := fun z => ∑ d ∈ k.range, powSign (Q z) d • Λ d (F z)
  have hΦd : DiffContOnCl ℂ Φ (verticalStrip 0 1) := by
    have hterm (d : ℂ) : DiffContOnCl ℂ (fun z => powSign (Q z) d • Λ d (F z))
        (verticalStrip 0 1) :=
      (differentiable_powSign_exponent _ _ _ d).diffContOnCl.smul
        ((Λ d).differentiable.comp_diffContOnCl hF.diffContOnCl)
    exact ⟨DifferentiableOn.fun_sum fun d _ => (hterm d).differentiableOn,
      continuousOn_finsetSum _ fun d _ => (hterm d).continuousOn⟩
  have hΦb : BddAbove ((norm ∘ Φ) '' verticalClosedStrip 0 1) := by
    refine ⟨∑ d ∈ k.range, Real.exp ((1 + |exponentSlope (p₀.conjExponent⁻¹).toReal
      (p₁.conjExponent⁻¹).toReal θ|) * |Real.log ‖d‖|) * (‖Λ d‖ * ‖g‖), ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d _ => ?_)
    rw [norm_smul]
    exact mul_le_mul
      (norm_powSign_exponent_le (Ioo_subset_Icc_self hθ)
        (TauCeti.Complex.HadamardThreeLines.mem_verticalClosedStrip_iff.1 hz) d)
      (((Λ d).le_opNorm _).trans (mul_le_mul_of_nonneg_left (hF.norm_le hz) (norm_nonneg _)))
      (norm_nonneg _) (Real.exp_pos _).le
  -- On the boundary lines, `Φ` is the pairing of a trace with the analytic family through `k`.
  have hb₀ : ∀ z ∈ re ⁻¹' {(0 : ℝ)}, ‖Φ z‖ ≤ r := by
    intro z hz
    rw [mem_preimage, mem_singleton_iff] at hz
    obtain ⟨t, rfl⟩ : ∃ t : ℝ, z = t * I := ⟨z.im, by apply Complex.ext <;> simp [hz]⟩
    simp only [Φ, smul_eq_mul, hF.apply_mul_I]
    exact (norm_sum_mul_le_of_eLpNorm_le_one k _ _ hfib₀ (hk₀ _ hz) _
      fun d hd => fiberPairing_fstToSum (hfib₀ d hd) (hfib₁ d hd) _).trans
      (((ZeroAtInftyContinuousMap.norm_coe_le_norm _ t).trans (norm_fst_le _)).trans hgr'.le)
  have hb₁ : ∀ z ∈ re ⁻¹' {(1 : ℝ)}, ‖Φ z‖ ≤ r := by
    intro z hz
    rw [mem_preimage, mem_singleton_iff] at hz
    obtain ⟨t, rfl⟩ : ∃ t : ℝ, z = 1 + t * I := ⟨z.im, by apply Complex.ext <;> simp [hz]⟩
    simp only [Φ, smul_eq_mul, hF.apply_one_add_mul_I]
    exact (norm_sum_mul_le_of_eLpNorm_le_one k _ _ hfib₁ (hk₁ _ hz) _
      fun d hd => fiberPairing_sndToSum (hfib₀ d hd) (hfib₁ d hd) _).trans
      (((ZeroAtInftyContinuousMap.norm_coe_le_norm _ t).trans (norm_snd_le _)).trans hgr'.le)
  -- At `θ` the family passes through `k`, and `F θ = a + b`.
  have hΦθ : Φ θ = ∫ x, (a x + b x) * k x ∂μ := by
    have hint (d : ℂ) (hd : d ≠ 0) :
        Integrable (fun x => (a x + b x) * fiberIndicator ℂ k d x) μ := by
      simp_rw [add_mul]
      exact ((Lp.memLp a).integrable_mul (hfib₀ d hd)).add
        ((Lp.memLp b).integrable_mul (hfib₁ d hd))
    have hterm (d : ℂ) : powSign 1 d * Λ d (F θ) =
        powSign 1 d * ∫ x, (a x + b x) * fiberIndicator ℂ k d x ∂μ := by
      rcases eq_or_ne d 0 with rfl | hd
      · rw [powSign_zero_right, zero_mul, zero_mul]
      · have ha : Integrable (fun x => a x * fiberIndicator ℂ k d x) μ :=
          (Lp.memLp a).integrable_mul (hfib₀ d hd)
        have hb : Integrable (fun x => b x * fiberIndicator ℂ k d x) μ :=
          (Lp.memLp b).integrable_mul (hfib₁ d hd)
        rw [hFθ, ← hab, map_add, fiberPairing_fstToSum (hfib₀ d hd) (hfib₁ d hd),
          fiberPairing_sndToSum (hfib₀ d hd) (hfib₁ d hd), ← integral_add ha hb]
        simp_rw [add_mul]
    calc Φ θ = ∑ d ∈ k.range, powSign 1 d * Λ d (F θ) := by
          simp only [Φ, smul_eq_mul, Q, exponent_self]
      _ = ∑ d ∈ k.range, powSign 1 d * ∫ x, (a x + b x) * fiberIndicator ℂ k d x ∂μ :=
          Finset.sum_congr rfl fun d _ => hterm d
      _ = ∫ x, (a x + b x) * k.map (powSign 1) x ∂μ :=
          (integral_mul_map_eq_sum k _ fun d _ hd => hint d (by rintro rfl; simp at hd)).symm
      _ = _ := by rw [SimpleFunc.map_powSign_one]
  have key := norm_le_interp_of_mem_verticalClosedStrip₀₁' Φ
    (z := (θ : ℂ)) (by simpa using hθ') hΦd hΦb hb₀ hb₁
  have hr0 : 0 < r := (norm_nonneg v).trans_lt hr
  rw [hΦθ, ofReal_re, ← Real.rpow_add hr0, sub_add_cancel, Real.rpow_one] at key
  exact key

/-- The bilinear form of the three-lines estimate, for simple `k` of finite `L^{p'}` norm. -/
private theorem enorm_integral_mul_le (v : (lebesgue ℂ ℂ μ p₀ p₁).ComplexMethodSpace θ)
    (a : Lp ℂ p₀ μ) (b : Lp ℂ p₁ μ)
    (hab : (lebesgue ℂ ℂ μ p₀ p₁).fstToSum a + (lebesgue ℂ ℂ μ p₀ p₁).sndToSum b =
      ComplexMethodSpace.toSum v)
    {k : SimpleFunc α ℂ} (hk : eLpNorm k p.conjExponent μ ≠ ∞) :
    ‖∫ x, (a x + b x) * k x ∂μ‖ₑ ≤ ENNReal.ofReal ‖v‖ * eLpNorm k p.conjExponent μ := by
  rcases eq_or_ne (eLpNorm k p.conjExponent μ) 0 with hk0 | hk0
  · have hk0' : ⇑k =ᵐ[μ] 0 :=
      (eLpNorm_eq_zero_iff
        (zero_lt_one.trans_le (ENNReal.HolderConjugate.one_le _ p)).ne').1 hk0
    rw [integral_eq_zero_of_ae (hk0'.mono fun x hx => by simp [hx])]
    simp
  -- Normalize `k`.
  set c := (eLpNorm k p.conjExponent μ).toReal
  have hc : 0 < c := ENNReal.toReal_pos hk0 hk
  have hkc : eLpNorm (((c⁻¹ : ℝ) : ℂ) • k) p.conjExponent μ ≤ 1 :=
    (k.eLpNorm_inv_toReal_smul_eq_one hk0 hk).le
  have key := norm_integral_mul_le_of_le_one hθ hp v a b hab hkc
  have hscale : ∫ x, (a x + b x) * (((c⁻¹ : ℝ) : ℂ) • k) x ∂μ =
      ((c⁻¹ : ℝ) : ℂ) * ∫ x, (a x + b x) * k x ∂μ := by
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hscale, norm_mul, norm_real, Real.norm_of_nonneg (inv_nonneg.2 hc.le),
    inv_mul_le_iff₀ hc] at key
  calc ‖∫ x, (a x + b x) * k x ∂μ‖ₑ = ENNReal.ofReal ‖∫ x, (a x + b x) * k x ∂μ‖ :=
        (ofReal_norm _).symm
    _ ≤ ENNReal.ofReal (c * ‖v‖) := ENNReal.ofReal_le_ofReal key
    _ = ENNReal.ofReal ‖v‖ * eLpNorm k p.conjExponent μ := by
        rw [mul_comm, ENNReal.ofReal_mul (norm_nonneg _), ENNReal.ofReal_toReal hk]

/-- **`[L^{p₀}, L^{p₁}]_θ ⊆ Lᵖ`.** On a σ-finite measure space, let `1 ≤ p₀, p₁ ≤ ∞`,
`0 < θ < 1` and `1 / p = (1 - θ) / p₀ + θ / p₁` with `p < ∞`. Every element `v` of the complex
interpolation space `[L^{p₀}, L^{p₁}]_θ` is a function `f ∈ Lᵖ`, with `‖f‖_p ≤ ‖v‖_θ`. -/
theorem exists_ofLp_eq_sumSpaceEmbed_toSum [SigmaFinite μ] (hpt : p ≠ ∞)
    (v : (lebesgue ℂ ℂ μ p₀ p₁).ComplexMethodSpace θ) :
    ∃ f : Lp ℂ p μ, L1AddLinfty.ofLp f =
        (lebesgue ℂ ℂ μ p₀ p₁).sumSpaceEmbed (ComplexMethodSpace.toSum v) ∧ ‖f‖ ≤ ‖v‖ := by
  obtain ⟨a, b, hab⟩ :=
    (lebesgue ℂ ℂ μ p₀ p₁).exists_fstToSum_add_sndToSum_eq (ComplexMethodSpace.toSum v)
  set h : α → ℂ := fun x => a x + b x
  have hsm : StronglyMeasurable h := (Lp.stronglyMeasurable a).add (Lp.stronglyMeasurable b)
  -- Duality against simple functions bounds `‖h‖_p` by `‖v‖_θ`.
  have hle : eLpNorm h p μ ≤ ENNReal.ofReal ‖v‖ :=
    hsm.aestronglyMeasurable.eLpNorm_le_of_forall_enorm_integral_mul_le_of_ne_top
      (q' := p.conjExponent) hpt fun k hk =>
        enorm_integral_mul_le hθ hp v a b hab hk.eLpNorm_lt_top.ne
  have hmem : MemLp h p μ := memLp_iff.2 (hle.trans_lt ENNReal.ofReal_lt_top)
  refine ⟨hmem.toLp h, ?_, ?_⟩
  · rw [← hab, map_add, sumSpaceEmbed_fstToSum, sumSpaceEmbed_sndToSum, lebesgue_embed₀,
      lebesgue_embed₁]
    apply (l1Linfty ℂ ℂ μ).sumSpace_ext
    rw [map_add, L1AddLinfty.sumSpaceEmbed_ofLp, L1AddLinfty.sumSpaceEmbed_ofLp,
      L1AddLinfty.sumSpaceEmbed_ofLp]
    exact ((L1AddLinfty.lpToAmbient_add_lpToAmbient_eq_iff ℂ).2 hmem.coeFn_toLp.symm).symm
  · rw [Lp.norm_toLp]
    exact ENNReal.toReal_le_of_le_ofReal (norm_nonneg _) hle

end Reverse

/-! ### The isometry `Lᵖ ≃ [L^{p₀}, L^{p₁}]_θ` -/

section Equiv

variable [SigmaFinite μ] (hθ : θ ∈ Ioo (0 : ℝ) 1)
  (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹) (hpt : p ≠ ∞)

include hθ hp hpt

/-- The element of `[L^{p₀}, L^{p₁}]_θ` lying over `f ∈ Lᵖ`. -/
private def toComplexMethodSpace (f : Lp ℂ p μ) : (lebesgue ℂ ℂ μ p₀ p₁).ComplexMethodSpace θ :=
  (exists_sumSpaceEmbed_toSum_eq_ofLp hθ hp hpt f).choose

omit [SigmaFinite μ] in
private theorem sumSpaceEmbed_toSum_toComplexMethodSpace (f : Lp ℂ p μ) :
    (lebesgue ℂ ℂ μ p₀ p₁).sumSpaceEmbed
        (ComplexMethodSpace.toSum (toComplexMethodSpace hθ hp hpt f)) =
      L1AddLinfty.ofLp f :=
  (exists_sumSpaceEmbed_toSum_eq_ofLp hθ hp hpt f).choose_spec.1

private theorem norm_toComplexMethodSpace (f : Lp ℂ p μ) :
    ‖toComplexMethodSpace hθ hp hpt f‖ = ‖f‖ := by
  refine le_antisymm (exists_sumSpaceEmbed_toSum_eq_ofLp hθ hp hpt f).choose_spec.2 ?_
  obtain ⟨f', hf', hf'n⟩ :=
    exists_ofLp_eq_sumSpaceEmbed_toSum hθ hp hpt (toComplexMethodSpace hθ hp hpt f)
  rw [sumSpaceEmbed_toSum_toComplexMethodSpace] at hf'
  rwa [L1AddLinfty.ofLp_injective hf'] at hf'n

/-- The inclusion `Lᵖ → [L^{p₀}, L^{p₁}]_θ` as a linear isometry. -/
private def lpToComplexMethodSpace :
    Lp ℂ p μ →ₗᵢ[ℂ] (lebesgue ℂ ℂ μ p₀ p₁).ComplexMethodSpace θ where
  toFun := toComplexMethodSpace hθ hp hpt
  map_add' f g := by
    apply injective_sumSpaceEmbed_toSum
    simp only [map_add, sumSpaceEmbed_toSum_toComplexMethodSpace]
  map_smul' c f := by
    apply injective_sumSpaceEmbed_toSum
    simp only [map_smul, RingHom.id_apply, sumSpaceEmbed_toSum_toComplexMethodSpace]
  norm_map' := norm_toComplexMethodSpace hθ hp hpt

/-- **Complex interpolation of Lebesgue spaces** (Calderón; Bergh–Löfström, Theorem 5.1.1). On a
σ-finite measure space, let `1 ≤ p₀, p₁ ≤ ∞`, `0 < θ < 1` and `1 / p = (1 - θ) / p₀ + θ / p₁`
with `p < ∞`. Then `[L^{p₀}, L^{p₁}]_θ = Lᵖ` with equal norms: this linear isometric equivalence
lies over the identity of `L¹ + L^∞`
(`TauCeti.CompatibleCouple.sumSpaceEmbed_toSum_lpEquivComplexMethodSpace`). -/
def lpEquivComplexMethodSpace :
    Lp ℂ p μ ≃ₗᵢ[ℂ] (lebesgue ℂ ℂ μ p₀ p₁).ComplexMethodSpace θ :=
  LinearIsometryEquiv.ofSurjective (lpToComplexMethodSpace hθ hp hpt) fun v => by
    obtain ⟨f, hf, -⟩ := exists_ofLp_eq_sumSpaceEmbed_toSum hθ hp hpt v
    exact ⟨f, injective_sumSpaceEmbed_toSum
      ((sumSpaceEmbed_toSum_toComplexMethodSpace hθ hp hpt f).trans hf)⟩

/-- The isometry `Lᵖ ≃ [L^{p₀}, L^{p₁}]_θ` is the identity of `L¹ + L^∞`. -/
@[simp]
theorem sumSpaceEmbed_toSum_lpEquivComplexMethodSpace (f : Lp ℂ p μ) :
    (lebesgue ℂ ℂ μ p₀ p₁).sumSpaceEmbed
        (ComplexMethodSpace.toSum (lpEquivComplexMethodSpace hθ hp hpt f)) =
      L1AddLinfty.ofLp f :=
  sumSpaceEmbed_toSum_toComplexMethodSpace hθ hp hpt f

/-- The inverse isometry `[L^{p₀}, L^{p₁}]_θ ≃ Lᵖ` is the identity of `L¹ + L^∞`. -/
@[simp]
theorem ofLp_lpEquivComplexMethodSpace_symm (v : (lebesgue ℂ ℂ μ p₀ p₁).ComplexMethodSpace θ) :
    L1AddLinfty.ofLp ((lpEquivComplexMethodSpace hθ hp hpt).symm v) =
      (lebesgue ℂ ℂ μ p₀ p₁).sumSpaceEmbed (ComplexMethodSpace.toSum v) := by
  conv_rhs => rw [← (lpEquivComplexMethodSpace hθ hp hpt).apply_symm_apply v]
  rw [sumSpaceEmbed_toSum_lpEquivComplexMethodSpace]

/-- Under the hypotheses of `TauCeti.CompatibleCouple.lpEquivComplexMethodSpace` (a σ-finite
measure space, `0 < θ < 1` and `1 / p = (1 - θ) / p₀ + θ / p₁` with `p < ∞`), an element of
`L^{p₀} + L^{p₁}` lies in `[L^{p₀}, L^{p₁}]_θ` exactly when it is a function in `Lᵖ`. -/
theorem exists_toSum_eq_iff_exists_ofLp_eq {u : (lebesgue ℂ ℂ μ p₀ p₁).SumSpace} :
    (∃ v : (lebesgue ℂ ℂ μ p₀ p₁).ComplexMethodSpace θ, ComplexMethodSpace.toSum v = u) ↔
      ∃ f : Lp ℂ p μ, L1AddLinfty.ofLp f = (lebesgue ℂ ℂ μ p₀ p₁).sumSpaceEmbed u := by
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨_, ofLp_lpEquivComplexMethodSpace_symm hθ hp hpt v⟩
  · rintro ⟨f, hf⟩
    exact ⟨lpEquivComplexMethodSpace hθ hp hpt f, (lebesgue ℂ ℂ μ p₀ p₁).sumSpaceEmbed_injective
      ((sumSpaceEmbed_toSum_lpEquivComplexMethodSpace hθ hp hpt f).trans hf)⟩

end Equiv

end TauCeti.CompatibleCouple
