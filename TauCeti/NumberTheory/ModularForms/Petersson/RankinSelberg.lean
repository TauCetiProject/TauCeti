/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.DiamondOperators
public import TauCeti.NumberTheory.ModularForms.Petersson.FiniteIndex
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import TauCeti.MeasureTheory.Group.FundamentalDomain
import TauCeti.NumberTheory.ModularForms.Cusps.Basic
import TauCeti.NumberTheory.ModularForms.EisensteinSeries.RealAnalytic

/-!
# Elementary Rankin–Selberg unfolding for cusp forms with nebentypus

For a cusp form `f ∈ S_k(Γ₁(N), χ)` of weight `k` and nebentypus `χ : (ZMod N)ˣ →* ℂˣ`, the
weighted squared modulus `|f(τ)|² (Im τ)^k` is invariant under `Γ₀(N)`. Integrating
`|f(τ)|² (Im τ)^{k + s}` against the hyperbolic measure `dx dy / y²` over the vertical strip
`0 ≤ Re τ < 1` and unfolding the strip as a `⟨T⟩`-fundamental domain against the `Γ₀(N)`-coset
tiling of `ℍ` yields the Rankin–Selberg identity
$$\int_{0 \le \operatorname{Re}\tau < 1} |f(\tau)|^2 (\operatorname{Im}\tau)^{k+s}\, d\mu(\tau)
  = \int_{\Gamma_0(N) \backslash \mathbb{H}}
      |f(\tau)|^2 (\operatorname{Im}\tau)^k E_N(\tau, s)\, d\mu(\tau)$$
for `s > 1`, where `E_N(τ, s)` is the real-analytic Eisenstein series at `∞` for `Γ₀(N)`.

By dominated convergence on the standard fundamental domain `𝒟` and the residue
`lim_{s → 1⁺} (s - 1) E_N(τ, s) = 3 / (π [SL₂(ℤ) : Γ₀(N)])`, multiplying by `s - 1` and taking
`s → 1⁺` recovers the index-normalized Petersson norm:
$$\lim_{s \to 1^+} (s - 1)
    \int_{0 \le \operatorname{Re}\tau < 1} |f(\tau)|^2 (\operatorname{Im}\tau)^{k+s}\, d\mu(\tau)
  = \frac{3}{\pi\, [SL_2(\mathbb{Z}) : \Gamma_1(N)\cdot\{\pm I\}]}\, \langle f, f \rangle.$$

On the other hand, by Parseval's identity along horizontal lines `Im τ = y`, the vertical-strip
integral depends only on `k`, `s`, and the sequence `n ↦ |a_n(f)|` of Fourier coefficient norms.
Consequently, any two cusp forms with nebentypus whose `q`-expansion coefficients have the same
absolute values have equal index-normalized Petersson norms — and, at the same level, equal
Petersson norms.

## Main results

* `CuspForm.tendsto_sub_one_mul_setIntegral_norm_sq_mul_im`: the Rankin–Selberg residue formula
  relating the vertical-strip integral of `|f(τ)|² (Im τ)^{k+s}` as `s → 1⁺` to
  `peterssonInnerCosets f f`.
* `CuspForm.inv_index_mul_peterssonInnerCosets_self_eq_of_norm_qExpansion_coeff_eq`: two cusp
  forms with nebentypus (possibly of different levels and characters) whose `q`-expansion
  coefficients have the same norms have the same index-normalized Petersson norm.
* `CuspForm.peterssonInnerCosets_self_eq_of_norm_qExpansion_coeff_eq`: same-level specialization,
  `⟪f, f⟫ = ⟪g, g⟫`.

## References

* [D. Bump, *Automorphic forms and representations*][bump1997], §1.6.
* [H. Iwaniec, *Spectral methods of automorphic forms*][iwaniec2002], Chapter 3.
-/

public section

noncomputable section

open MeasureTheory Filter Topology Real Complex UpperHalfPlane ModularGroup Set
open Matrix.SpecialLinearGroup CongruenceSubgroup TauCeti TauCeti.EisensteinSeries
open scoped MatrixGroups ModularForm NNReal ENNReal Pointwise

namespace CuspForm

/-! ### The vertical strip `{0 ≤ Re τ < 1}` and Parseval's identity -/

private theorem isFundamentalDomain_re_Ico_zero_one :
    MeasureTheory.IsFundamentalDomain pslTSubgroup
      (UpperHalfPlane.re ⁻¹' Set.Ico (0 : ℝ) 1) volume := by
  refine MeasureTheory.IsFundamentalDomain.mk''
    (UpperHalfPlane.continuous_re.measurable measurableSet_Ico).nullMeasurableSet
    ?_ ?_ fun g ↦ (measurePreserving_smul (g : PSL(2, ℤ)) volume).quasiMeasurePreserving
  · refine ae_of_all _ fun τ ↦ ?_
    let n : ℤ := -⌊τ.re⌋
    have hn_mem : ((ModularGroup.T ^ n : SL(2, ℤ)) : PSL(2, ℤ)) ∈ pslTSubgroup :=
      (mem_pslTSubgroup_mk_iff (ModularGroup.T ^ n)).mpr (by simp [ModularGroup.coe_T_zpow])
    refine ⟨⟨((ModularGroup.T ^ n : SL(2, ℤ)) : PSL(2, ℤ)), hn_mem⟩, ?_⟩
    change (((ModularGroup.T ^ n : SL(2, ℤ)) : PSL(2, ℤ)) • τ).re ∈ Set.Ico (0 : ℝ) 1
    rw [UpperHalfPlane.pslMk_smul, ModularGroup.re_T_zpow_smul]
    simp only [n, Int.cast_neg, ← sub_eq_add_neg, Set.mem_Ico]
    exact ⟨Int.fract_nonneg τ.re, Int.fract_lt_one τ.re⟩
  · intro g hg
    obtain ⟨γ, hγ⟩ := QuotientGroup.mk_surjective (g : PSL(2, ℤ))
    have hc0 : γ 1 0 = 0 :=
      (mem_pslTSubgroup_mk_iff γ).mp (by rw [hγ]; exact g.2)
    obtain ⟨n, hn⟩ := ModularGroup.exists_eq_T_zpow_of_c_eq_zero hc0
    have hsmul : ∀ τ : ℍ, (g : PSL(2, ℤ)) • τ = ModularGroup.T ^ n • τ := fun τ ↦ by
      rw [← hγ, UpperHalfPlane.pslMk_smul, hn τ]
    have hn0 : n ≠ 0 := by
      rintro rfl
      apply hg
      ext
      refine eq_of_smul_eq_smul fun τ : ℍ ↦ ?_
      rw [hsmul τ, zpow_zero, one_smul, Subgroup.coe_one, one_smul]
    refine Disjoint.aedisjoint ?_
    rw [Set.disjoint_left]
    rintro w ⟨τ, hτ, rfl⟩ hw
    change ((g : PSL(2, ℤ)) • τ).re ∈ Set.Ico (0 : ℝ) 1 at hw
    rw [hsmul τ, ModularGroup.re_T_zpow_smul] at hw
    have h1 : (-1 : ℝ) < (n : ℝ) := by linarith [hτ.1, hτ.2, hw.1, hw.2]
    have h2 : (n : ℝ) < 1 := by linarith [hτ.1, hτ.2, hw.1, hw.2]
    have h1' : (-1 : ℤ) < n := by exact_mod_cast h1
    have h2' : n < 1 := by exact_mod_cast h2
    omega

private theorem measurable_ofComplex : Measurable UpperHalfPlane.ofComplex := by
  intro s hs
  by_cases hc : Classical.choice inferInstance ∈ s
  · have hpre : UpperHalfPlane.ofComplex ⁻¹' s =
        (UpperHalfPlane.coe '' s) ∪ {w : ℂ | w.im ≤ 0} := by
      ext w
      by_cases hw : 0 < w.im
      · simp only [Set.mem_preimage, Set.mem_union, Set.mem_image, Set.mem_ofPred_eq,
          UpperHalfPlane.ofComplex_apply_of_im_pos hw, not_le.mpr hw, or_false]
        exact ⟨fun h ↦ ⟨⟨w, hw⟩, h, rfl⟩,
          fun ⟨z, hz, hzw⟩ ↦ (UpperHalfPlane.ext hzw : z = ⟨w, hw⟩) ▸ hz⟩
      · have hwle : w.im ≤ 0 := not_lt.mp hw
        simp [UpperHalfPlane.ofComplex_apply_of_im_nonpos hwle, hc, hwle]
    rw [hpre]
    exact (UpperHalfPlane.measurableEmbedding_coe.measurableSet_image.mpr hs).union
      (isClosed_le Complex.continuous_im continuous_const).measurableSet
  · have hpre : UpperHalfPlane.ofComplex ⁻¹' s = UpperHalfPlane.coe '' s := by
      ext w
      by_cases hw : 0 < w.im
      · simp only [Set.mem_preimage, Set.mem_image, UpperHalfPlane.ofComplex_apply_of_im_pos hw]
        exact ⟨fun h ↦ ⟨⟨w, hw⟩, h, rfl⟩,
          fun ⟨z, hz, hzw⟩ ↦ (UpperHalfPlane.ext hzw : z = ⟨w, hw⟩) ▸ hz⟩
      · have hwle : w.im ≤ 0 := not_lt.mp hw
        simp only [Set.mem_preimage, Set.mem_image,
          UpperHalfPlane.ofComplex_apply_of_im_nonpos hwle, hc, false_iff, not_exists, not_and]
        intro z _ hzw
        exact hw (hzw ▸ z.im_pos)
    rw [hpre]
    exact UpperHalfPlane.measurableEmbedding_coe.measurableSet_image.mpr hs

private theorem setLIntegral_re_Ico_eq_parseval {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma1 N).map (mapGL ℝ)) k) (s : ℝ) :
    ∫⁻ τ in UpperHalfPlane.re ⁻¹' Set.Ico (0 : ℝ) 1,
        ENNReal.ofReal (‖f τ‖ ^ 2 * τ.im ^ k * τ.im ^ s) =
      ∫⁻ y in Set.Ioi (0 : ℝ),
        ENNReal.ofReal
          ((∑' n : ℕ, ‖(qExpansion 1 f).coeff n‖ ^ 2 * Real.exp (-(4 * π * n * y))) *
            (y ^ k * y ^ s * (y ^ 2)⁻¹)) := by
  let S : Set ℍ := UpperHalfPlane.re ⁻¹' Set.Ico (0 : ℝ) 1
  have hS_meas : MeasurableSet S := UpperHalfPlane.continuous_re.measurable measurableSet_Ico
  let G₀ : ℍ → ℝ≥0∞ := fun z ↦
    ENNReal.ofReal (‖f z‖ ^ 2 * z.im ^ k * z.im ^ s * (z.im ^ 2)⁻¹)
  let G : ℂ → ℝ≥0∞ := G₀ ∘ UpperHalfPlane.ofComplex
  have hF_cont : Continuous fun τ : ℍ ↦ ‖f τ‖ ^ 2 * τ.im ^ k * τ.im ^ s := by
    refine (((ModularFormClass.continuous f).norm.pow 2).mul ?_).mul
      (UpperHalfPlane.continuous_im.rpow continuous_const fun τ ↦ Or.inl τ.im_pos.ne')
    exact UpperHalfPlane.continuous_im.zpow₀ k fun τ ↦ Or.inl τ.im_pos.ne'
  have hF_meas : Measurable fun τ : ℍ ↦ ENNReal.ofReal (‖f τ‖ ^ 2 * τ.im ^ k * τ.im ^ s) :=
    ENNReal.measurable_ofReal.comp hF_cont.measurable
  have hG₀_meas : Measurable G₀ :=
    ENNReal.measurable_ofReal.comp
      (hF_cont.measurable.mul (UpperHalfPlane.continuous_im.measurable.pow_const 2).inv)
  have hG_meas : Measurable G := hG₀_meas.comp measurable_ofComplex
  have hd_meas : Measurable fun z : ℍ ↦
      (((1 / NNReal.mk z.im z.im_pos.le : ℝ≥0) ^ 2 : ℝ≥0) : ℝ≥0∞) := by
    fun_prop
  have hmp : MeasurePreserving UpperHalfPlane.coe (volume.comap UpperHalfPlane.coe)
      (volume.restrict (.range UpperHalfPlane.coe)) :=
    ⟨UpperHalfPlane.measurable_coe, by rw [UpperHalfPlane.measurableEmbedding_coe.map_comap]⟩
  have hdens : ∀ τ : ℍ,
      (((1 / NNReal.mk τ.im τ.im_pos.le : ℝ≥0) ^ 2 : ℝ≥0) : ℝ≥0∞) *
          ENNReal.ofReal (‖f τ‖ ^ 2 * τ.im ^ k * τ.im ^ s) = G τ := by
    intro τ
    have hnn1 : 0 ≤ (τ.im ^ 2)⁻¹ := by positivity
    have h1 : (((1 / NNReal.mk τ.im τ.im_pos.le : ℝ≥0) ^ 2 : ℝ≥0) : ℝ≥0∞) =
        ENNReal.ofReal ((τ.im ^ 2)⁻¹) := by
      rw [ENNReal.ofReal_eq_coe_nnreal hnn1]
      congr 1
      ext
      simp [one_div, inv_pow]
    rw [h1, ← ENNReal.ofReal_mul hnn1]
    simp only [G, G₀, Function.comp_apply, UpperHalfPlane.ofComplex_apply]
    congr 1
    ring
  have himage : UpperHalfPlane.coe '' S =
      Complex.measurableEquivRealProd ⁻¹' (Set.Ico (0 : ℝ) 1 ×ˢ Set.Ioi (0 : ℝ)) := by
    ext w
    constructor
    · rintro ⟨τ, hτ, rfl⟩
      exact ⟨hτ, τ.im_pos⟩
    · rintro ⟨hre, him⟩
      exact ⟨⟨w, him⟩, hre, rfl⟩
  -- Step 1: pass from hyperbolic measure on `ℍ` to Lebesgue measure on `ℝ × ℝ`
  have hstep1 : ∫⁻ τ in S, ENNReal.ofReal (‖f τ‖ ^ 2 * τ.im ^ k * τ.im ^ s) =
      ∫⁻ y in Set.Ioi (0 : ℝ), ∫⁻ x in Set.Ico (0 : ℝ) 1,
        G (Complex.measurableEquivRealProd.symm (x, y)) := by
    rw [UpperHalfPlane.volume_def,
      setLIntegral_withDensity_eq_setLIntegral_mul _ hd_meas hF_meas hS_meas]
    simp_rw [Pi.mul_apply, hdens]
    rw [hmp.setLIntegral_comp_emb UpperHalfPlane.measurableEmbedding_coe G S,
      Measure.restrict_restrict' UpperHalfPlane.measurableEmbedding_coe.measurableSet_range,
      Set.inter_eq_self_of_subset_left (Set.image_subset_range _ _), himage]
    have hcomp : ∫⁻ w in Complex.measurableEquivRealProd ⁻¹'
          (Set.Ico (0 : ℝ) 1 ×ˢ Set.Ioi (0 : ℝ)), G w =
        ∫⁻ p in Set.Ico (0 : ℝ) 1 ×ˢ Set.Ioi (0 : ℝ),
          G (Complex.measurableEquivRealProd.symm p) := by
      have h := Complex.volume_preserving_equiv_real_prod.setLIntegral_comp_preimage_emb
        Complex.measurableEquivRealProd.measurableEmbedding
        (fun p : ℝ × ℝ ↦ G (Complex.measurableEquivRealProd.symm p))
        (Set.Ico (0 : ℝ) 1 ×ˢ Set.Ioi (0 : ℝ))
      simpa only [MeasurableEquiv.symm_apply_apply] using h
    rw [hcomp, Measure.volume_eq_prod]
    exact setLIntegral_prod_symm _
      (hG_meas.comp Complex.measurableEquivRealProd.symm.measurable).aemeasurable
  rw [hstep1]
  -- Step 2: evaluate each horizontal slice `y > 0` by Parseval's identity
  refine setLIntegral_congr_fun measurableSet_Ioi fun y hy ↦ ?_
  have hy' : 0 < y := Set.mem_Ioi.mp hy
  have hslice : ∀ x : ℝ, G (Complex.measurableEquivRealProd.symm (x, y)) =
      ENNReal.ofReal (‖f ⟨(x : ℂ) + (y : ℂ) * UpperHalfPlane.I, by simpa using hy'⟩‖ ^ 2) *
        ENNReal.ofReal (y ^ k * y ^ s * (y ^ 2)⁻¹) := by
    intro x
    have hxy : Complex.measurableEquivRealProd.symm (x, y) =
        (x : ℂ) + (y : ℂ) * UpperHalfPlane.I := by
      rw [Complex.measurableEquivRealProd_symm_apply]
      apply Complex.ext <;> simp
    have him_xy : 0 < ((x : ℂ) + (y : ℂ) * UpperHalfPlane.I).im := by simpa using hy'
    have hofC : UpperHalfPlane.ofComplex (Complex.measurableEquivRealProd.symm (x, y)) =
        ⟨(x : ℂ) + (y : ℂ) * UpperHalfPlane.I, him_xy⟩ := by
      rw [hxy, UpperHalfPlane.ofComplex_apply_of_im_pos him_xy]
    have him_val : (⟨(x : ℂ) + (y : ℂ) * UpperHalfPlane.I, him_xy⟩ : ℍ).im = y := by simp
    rw [← ENNReal.ofReal_mul (sq_nonneg _)]
    change G₀ (UpperHalfPlane.ofComplex (Complex.measurableEquivRealProd.symm (x, y))) = _
    rw [hofC]
    simp only [G₀, him_val]
    congr 1
    ring
  simp_rw [hslice]
  have hcont_line : Continuous fun x : ℝ ↦
      f ⟨(x : ℂ) + (y : ℂ) * UpperHalfPlane.I, by simpa using hy'⟩ :=
    (ModularFormClass.continuous f).comp
      (continuous_induced_rng.mpr (Complex.continuous_ofReal.add continuous_const))
  have hmeas_line : Measurable fun x : ℝ ↦
      ENNReal.ofReal (‖f ⟨(x : ℂ) + (y : ℂ) * UpperHalfPlane.I, by simpa using hy'⟩‖ ^ 2) :=
    ENNReal.measurable_ofReal.comp (hcont_line.measurable.norm.pow_const 2)
  rw [lintegral_mul_const _ hmeas_line]
  have hint : IntegrableOn
      (fun x : ℝ ↦ ‖f ⟨(x : ℂ) + (y : ℂ) * UpperHalfPlane.I, by simpa using hy'⟩‖ ^ 2)
      (Set.Ioc (0 : ℝ) 1) volume :=
    (hcont_line.norm.pow 2).integrableOn_Ioc
  have hparseval := UpperHalfPlane.hasSum_norm_sq_qExpansion_coeff_mul_exp (f := ⇑f) (h := 1)
    one_pos
    (SlashInvariantFormClass.periodic_comp_ofComplex f (TauCeti.one_mem_strictPeriods_Gamma1_map N))
    (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f) hy'
  simp only [inv_one, one_mul, div_one] at hparseval
  have hIco_eq : ∫⁻ x in Set.Ico (0 : ℝ) 1,
        ENNReal.ofReal (‖f ⟨(x : ℂ) + (y : ℂ) * UpperHalfPlane.I, by simpa using hy'⟩‖ ^ 2) =
      ENNReal.ofReal
        (∑' n : ℕ, ‖(qExpansion 1 f).coeff n‖ ^ 2 * Real.exp (-(4 * π * n * y))) := by
    rw [Measure.restrict_congr_set Ico_ae_eq_Ioc,
      ← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ ↦ sq_nonneg _),
      ← intervalIntegral.integral_of_le zero_le_one, hparseval.tsum_eq]
  rw [hIco_eq, ← ENNReal.ofReal_mul (tsum_nonneg fun n ↦ by positivity)]

/-! ### `Γ₀(N)`-invariance and Rankin–Selberg unfolding -/

private theorem norm_sq_mul_im_zpow_smul_of_mem_cuspFormCharSpace {N : ℕ} {k : ℤ}
    {χ : (ZMod N)ˣ →* ℂˣ} {f : CuspForm ((CongruenceSubgroup.Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ TauCeti.cuspFormCharSpace k χ) {γ : SL(2, ℤ)}
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) (τ : ℍ) :
    ‖f (γ • τ)‖ ^ 2 * (γ • τ).im ^ k = ‖f τ‖ ^ 2 * τ.im ^ k := by
  have hslash : ⇑f ∣[k] γ = (↑(χ ((Gamma0Map N).toHomUnits ⟨γ, hγ⟩)) : ℂ) • ⇑f :=
    (TauCeti.mem_cuspFormCharSpace_iff_nebentypus k χ f).mp hf ⟨γ, hγ⟩
  have hpet := UpperHalfPlane.petersson_slash_SL k ⇑f ⇑f γ τ
  rw [hslash] at hpet
  set c : ℂ := ↑(χ ((Gamma0Map N).toHomUnits ⟨γ, hγ⟩))
  have hc_norm : ‖c‖ = 1 :=
    (((Units.coeHom ℂ).comp χ).isOfFinOrder
      (isOfFinOrder_of_finite ((Gamma0Map N).toHomUnits ⟨γ, hγ⟩))).norm_eq_one
  have hpet_smul : petersson k (c • ⇑f) (c • ⇑f) τ = petersson k ⇑f ⇑f τ := by
    rw [petersson_self_eq_ofReal, petersson_self_eq_ofReal]
    simp only [Pi.smul_apply, smul_eq_mul, Complex.normSq_eq_norm_sq, norm_mul, hc_norm, one_mul]
  rw [hpet_smul, petersson_self_eq_ofReal, petersson_self_eq_ofReal] at hpet
  have hre : Complex.normSq (f (γ • τ)) * (γ • τ).im ^ k = Complex.normSq (f τ) * τ.im ^ k :=
    Complex.ofReal_injective hpet.symm
  simpa only [Complex.normSq_eq_norm_sq] using hre

private theorem norm_sq_mul_im_zpow_psl_smul_of_mem_cuspFormCharSpace {N : ℕ} {k : ℤ}
    {χ : (ZMod N)ˣ →* ℂˣ} {f : CuspForm ((CongruenceSubgroup.Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ TauCeti.cuspFormCharSpace k χ)
    (g : TauCeti.CongruenceSubgroup.Gamma0Projective N) (τ : ℍ) :
    ‖f ((g : PSL(2, ℤ)) • τ)‖ ^ 2 * ((g : PSL(2, ℤ)) • τ).im ^ k = ‖f τ‖ ^ 2 * τ.im ^ k := by
  obtain ⟨γ, hγ_eq, hγ⟩ := (TauCeti.CongruenceSubgroup.mem_Gamma0Projective_iff N g).mp g.2
  rw [← hγ_eq]
  change ‖f (((γ : SL(2, ℤ)) : PSL(2, ℤ)) • τ)‖ ^ 2 *
      (((γ : SL(2, ℤ)) : PSL(2, ℤ)) • τ).im ^ k = ‖f τ‖ ^ 2 * τ.im ^ k
  rw [UpperHalfPlane.pslMk_smul]
  exact norm_sq_mul_im_zpow_smul_of_mem_cuspFormCharSpace hf hγ τ

private theorem setLIntegral_re_Ico_eq_sum_fd {N : ℕ} [NeZero N] {k : ℤ}
    {χ : (ZMod N)ˣ →* ℂˣ} {f : CuspForm ((CongruenceSubgroup.Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ TauCeti.cuspFormCharSpace k χ) {s : ℝ} (hs : 1 < s) :
    ∫⁻ τ in UpperHalfPlane.re ⁻¹' Set.Ico (0 : ℝ) 1,
        ENNReal.ofReal (‖f τ‖ ^ 2 * τ.im ^ k * τ.im ^ s) =
      ∑ r : SL(2, ℤ) ⧸ (CongruenceSubgroup.Gamma0 N).withCenter,
        ∫⁻ τ in fd, ENNReal.ofReal (‖f (((r.out : SL(2, ℤ)))⁻¹ • τ)‖ ^ 2 *
          ((((r.out : SL(2, ℤ)))⁻¹ • τ).im) ^ k *
          realAnalyticEisenstein N (((r.out : SL(2, ℤ)))⁻¹ • τ) s) := by
  let Γ₀P := TauCeti.CongruenceSubgroup.Gamma0Projective N
  let H := pslTSubgroup.subgroupOf Γ₀P
  let D₀ : Set ℍ := ⋃ r : SL(2, ℤ) ⧸ (CongruenceSubgroup.Gamma0 N).withCenter,
    ((r.out : SL(2, ℤ)))⁻¹ • (fdo : Set ℍ)
  have hD₀ : MeasureTheory.IsFundamentalDomain Γ₀P D₀ volume := by
    rw [show Γ₀P = (CongruenceSubgroup.Gamma0 N).map
      (QuotientGroup.mk' (Subgroup.center SL(2, ℤ))) from
      TauCeti.CongruenceSubgroup.Gamma0Projective_def N]
    exact ModularGroup.isFundamentalDomain_iUnion_out_inv_smul_fdo_withCenter
      (CongruenceSubgroup.Gamma0 N)
  have : MeasurableConstSMul Γ₀P ℍ :=
    ⟨fun g ↦ measurable_const_smul (g : PSL(2, ℤ))⟩
  have : SMulInvariantMeasure Γ₀P ℍ volume :=
    ⟨fun g ↦ SMulInvariantMeasure.measure_preimage_smul (g : PSL(2, ℤ))⟩
  have hU_sub : MeasureTheory.IsFundamentalDomain (pslTSubgroup ⊓ Γ₀P : Subgroup PSL(2, ℤ))
      (⋃ q : Γ₀P ⧸ H, ((q.out : Γ₀P))⁻¹ • D₀) volume :=
    (hD₀.subgroup_iUnion_out_inv_smul H).of_subgroupOf
  have hinf : (pslTSubgroup ⊓ Γ₀P : Subgroup PSL(2, ℤ)) = pslTSubgroup :=
    inf_eq_left.mpr (pslTSubgroup_le_Gamma0Projective N)
  have hU : MeasureTheory.IsFundamentalDomain pslTSubgroup
      (⋃ q : Γ₀P ⧸ H, ((q.out : Γ₀P))⁻¹ • D₀) volume := by
    rw [hinf] at hU_sub
    exact hU_sub
  let Φ : ℍ → ℝ := fun τ ↦ ‖f τ‖ ^ 2 * τ.im ^ k
  have hΦ_nonneg : ∀ τ : ℍ, 0 ≤ Φ τ := fun τ ↦
    mul_nonneg (sq_nonneg _) (zpow_nonneg τ.im_pos.le k)
  have hΦ_cont : Continuous Φ :=
    ((ModularFormClass.continuous f).norm.pow 2).mul
      (UpperHalfPlane.continuous_im.zpow₀ k fun τ ↦ Or.inl τ.im_pos.ne')
  have hΦ_meas : Measurable Φ := hΦ_cont.measurable
  -- Step 1: compare the two `⟨T⟩`-fundamental domains
  have hstrip_eq_U :
      ∫⁻ τ in UpperHalfPlane.re ⁻¹' Set.Ico (0 : ℝ) 1, ENNReal.ofReal (Φ τ * τ.im ^ s) =
        ∫⁻ τ in ⋃ q : Γ₀P ⧸ H, ((q.out : Γ₀P))⁻¹ • D₀,
          ENNReal.ofReal (Φ τ * τ.im ^ s) := by
    refine isFundamentalDomain_re_Ico_zero_one.setLIntegral_eq hU _ fun g τ ↦ ?_
    have hg0 : (g : PSL(2, ℤ)) ∈ Γ₀P := pslTSubgroup_le_Gamma0Projective N g.2
    have hΦ_g : Φ ((g : PSL(2, ℤ)) • τ) = Φ τ :=
      norm_sq_mul_im_zpow_psl_smul_of_mem_cuspFormCharSpace hf ⟨g, hg0⟩ τ
    have him_g : ((g : PSL(2, ℤ)) • τ).im = τ.im := im_smul_eq_of_mem_pslTSubgroup g.2 τ
    change ENNReal.ofReal (Φ ((g : PSL(2, ℤ)) • τ) * ((g : PSL(2, ℤ)) • τ).im ^ s) = _
    rw [hΦ_g, him_g]
  -- Step 2: split the union over `Γ₀P ⧸ H` and fold into `E_N(τ, s)`
  have hD₀_open : IsOpen D₀ := isOpen_iUnion fun r ↦ by
    have h : ((r.out : SL(2, ℤ)))⁻¹ • (fdo : Set ℍ) =
        (mapGL ℝ ((r.out : SL(2, ℤ)))⁻¹) • (fdo : Set ℍ) := rfl
    rw [h]
    exact (Homeomorph.smul (mapGL ℝ ((r.out : SL(2, ℤ)))⁻¹)).isOpenMap _ isOpen_fdo
  have hU_eq_D₀ :
      ∫⁻ τ in ⋃ q : Γ₀P ⧸ H, ((q.out : Γ₀P))⁻¹ • D₀,
          ENNReal.ofReal (Φ τ * τ.im ^ s) =
        ∫⁻ τ in D₀, ENNReal.ofReal (Φ τ * realAnalyticEisenstein N τ s) := by
    have hmeas_q : ∀ q : Γ₀P ⧸ H, NullMeasurableSet (((q.out : Γ₀P))⁻¹ • D₀) volume := fun q ↦
      hD₀.nullMeasurableSet_smul ((q.out : Γ₀P)⁻¹)
    have hdisj_q : Pairwise fun q₁ q₂ : Γ₀P ⧸ H ↦
        AEDisjoint volume (((q₁.out : Γ₀P))⁻¹ • D₀) (((q₂.out : Γ₀P))⁻¹ • D₀) := fun q₁ q₂ hne ↦
      hD₀.aedisjoint (inv_injective.ne (Quotient.out_injective.ne hne))
    rw [lintegral_iUnion₀ hmeas_q hdisj_q]
    have hterm : ∀ q : Γ₀P ⧸ H,
        ∫⁻ τ in ((q.out : Γ₀P))⁻¹ • D₀, ENNReal.ofReal (Φ τ * τ.im ^ s) =
          ∫⁻ τ in D₀, ENNReal.ofReal (Φ τ * realAnalyticEisensteinSummand N τ s q) := by
      intro q
      have hset_q : ((q.out : Γ₀P))⁻¹ • D₀ =
          ((((q.out : Γ₀P) : PSL(2, ℤ))⁻¹) • ·) '' D₀ := by
        ext x
        simp [Set.mem_smul_set, Subgroup.smul_def]
      rw [hset_q,
        ← (measurePreserving_smul ((q.out : Γ₀P) : PSL(2, ℤ))⁻¹ volume).setLIntegral_comp_emb
          (measurableEmbedding_const_smul (((q.out : Γ₀P) : PSL(2, ℤ))⁻¹))]
      refine setLIntegral_congr_fun hD₀_open.measurableSet fun τ _ ↦ ?_
      have hΦ_q : Φ (((q.out : Γ₀P) : PSL(2, ℤ))⁻¹ • τ) = Φ τ :=
        norm_sq_mul_im_zpow_psl_smul_of_mem_cuspFormCharSpace hf (q.out : Γ₀P)⁻¹ τ
      rw [hΦ_q, realAnalyticEisensteinSummand_eq_out]
    simp_rw [hterm]
    rw [← lintegral_tsum fun q ↦ ?_]
    · refine setLIntegral_congr_fun hD₀_open.measurableSet fun τ _ ↦ ?_
      have hsumm : Summable fun q ↦ Φ τ * realAnalyticEisensteinSummand N τ s q :=
        (summable_realAnalyticEisensteinSummand N τ hs).mul_left (Φ τ)
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun q ↦ mul_nonneg (hΦ_nonneg τ) (by
        rw [realAnalyticEisensteinSummand_eq_out]
        exact rpow_nonneg (UpperHalfPlane.im_pos _).le s)) hsumm,
        tsum_mul_left, ← realAnalyticEisenstein_def]
    · exact (ENNReal.measurable_ofReal.comp
        (hΦ_meas.mul (continuous_realAnalyticEisensteinSummand N s q).measurable)).aemeasurable
  -- Step 3: decompose `D₀` into its finite `SL(2, ℤ) ⧸ (Gamma0 N).withCenter` translates of `fd`
  have hD₀_eq_sum :
      ∫⁻ τ in D₀, ENNReal.ofReal (Φ τ * realAnalyticEisenstein N τ s) =
        ∑ r : SL(2, ℤ) ⧸ (CongruenceSubgroup.Gamma0 N).withCenter,
          ∫⁻ τ in fd, ENNReal.ofReal (Φ (((r.out : SL(2, ℤ)))⁻¹ • τ) *
            realAnalyticEisenstein N (((r.out : SL(2, ℤ)))⁻¹ • τ) s) := by
    have hmeas_r : ∀ r : SL(2, ℤ) ⧸ (CongruenceSubgroup.Gamma0 N).withCenter,
        MeasurableSet (((r.out : SL(2, ℤ)))⁻¹ • (fdo : Set ℍ)) := fun r ↦ by
      have h : ((r.out : SL(2, ℤ)))⁻¹ • (fdo : Set ℍ) =
          (mapGL ℝ ((r.out : SL(2, ℤ)))⁻¹) • (fdo : Set ℍ) := rfl
      rw [h]
      exact ((Homeomorph.smul (mapGL ℝ ((r.out : SL(2, ℤ)))⁻¹)).isOpenMap _
        isOpen_fdo).measurableSet
    have hdisj_r : Pairwise fun r₁ r₂ : SL(2, ℤ) ⧸ (CongruenceSubgroup.Gamma0 N).withCenter ↦
        Disjoint (((r₁.out : SL(2, ℤ)))⁻¹ • (fdo : Set ℍ))
          (((r₂.out : SL(2, ℤ)))⁻¹ • (fdo : Set ℍ)) := fun r₁ r₂ hne ↦ by
      refine ModularGroup.disjoint_smul_fdo ?_ ?_
      · intro heq
        apply hne
        have hout : r₁.out = r₂.out := by
          have : r₁.out * r₂.out⁻¹ = 1 := by simpa [inv_inv] using heq
          exact mul_inv_eq_one.mp this
        exact Quotient.out_injective hout
      · intro heq
        apply hne
        have hrel : r₁.out⁻¹ * r₂.out ∈ (CongruenceSubgroup.Gamma0 N).withCenter := by
          have h1 : r₁.out * r₂.out⁻¹ = -1 := by simpa [inv_inv] using heq
          have h2 : r₁.out = -r₂.out := by
            have := congrArg (· * r₂.out) h1
            simpa [mul_assoc] using this
          have h3 : r₁.out⁻¹ * r₂.out = -1 := by rw [h2]; simp
          rw [h3, Subgroup.mem_withCenter_iff]
          exact ⟨1, one_mem _, -1, Subgroup.mem_center_iff.mpr fun g ↦ by simp, one_mul _⟩
        rw [← QuotientGroup.out_eq' r₁, ← QuotientGroup.out_eq' r₂, QuotientGroup.eq]
        exact hrel
    rw [lintegral_iUnion hmeas_r hdisj_r, tsum_fintype]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    have hsmul_set : ((r.out : SL(2, ℤ)))⁻¹ • (fdo : Set ℍ) =
        ((mapGL ℝ ((r.out : SL(2, ℤ)))⁻¹) • ·) '' (fdo : Set ℍ) := rfl
    rw [hsmul_set,
      ← (measurePreserving_smul (mapGL ℝ ((r.out : SL(2, ℤ)))⁻¹) volume).setLIntegral_comp_emb
        (measurableEmbedding_const_smul (mapGL ℝ ((r.out : SL(2, ℤ)))⁻¹)),
      Measure.restrict_congr_set ModularGroup.fd_ae_eq_fdo.symm]
    rfl
  exact hstrip_eq_U.trans (hU_eq_D₀.trans hD₀_eq_sum)

/-! ### Uniform domination on `𝒟` and passage to `s → 1⁺` -/

private theorem exists_bound_norm_sq_mul_im_zpow_mul_poly_fd {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma1 N).map (mapGL ℝ)) k) (γ : SL(2, ℤ)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ τ ∈ fd,
      ‖f (γ • τ)‖ ^ 2 * (γ • τ).im ^ k * (6 * π + 36 + 4 * τ.im ^ 2) ≤ M := by
  let Γ : Subgroup (GL (Fin 2) ℝ) := (CongruenceSubgroup.Gamma1 N).map (mapGL ℝ)
  have : ((ConjAct.toConjAct (mapGL ℝ γ)⁻¹) • Γ).IsArithmetic := by
    have h := Subgroup.IsArithmetic.conj Γ (mapGL ℚ γ)⁻¹
    have hmap : Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) ((mapGL ℚ γ)⁻¹) =
        (mapGL ℝ γ)⁻¹ := by
      rw [map_inv, show Rat.castHom ℝ = algebraMap ℚ ℝ from rfl, map_mapGL]
    rwa [hmap] at h
  let fγ := CuspForm.translate f (mapGL ℝ γ)
  obtain ⟨a, ha, hexp⟩ :=
    (CuspFormClass.zero_at_infty fγ).petersson_exp_decay_left k
      ((ConjAct.toConjAct (mapGL ℝ γ)⁻¹) • Γ) fγ
  have hpet_eq : ∀ τ : ℍ, ‖petersson k ⇑fγ ⇑fγ τ‖ = ‖f (γ • τ)‖ ^ 2 * (γ • τ).im ^ k := by
    intro τ
    have h1 : petersson k ⇑fγ ⇑fγ τ = petersson k ⇑f ⇑f (γ • τ) := by
      have hcoe : (⇑fγ : ℍ → ℂ) = ⇑f ∣[k] γ := CuspForm.coe_translate f (mapGL ℝ γ)
      rw [hcoe]
      exact UpperHalfPlane.petersson_slash_SL k ⇑f ⇑f γ τ
    rw [h1, petersson_self_eq_ofReal, Complex.norm_real, Real.norm_of_nonneg (by
      exact mul_nonneg (Complex.normSq_nonneg _) (zpow_nonneg (UpperHalfPlane.im_pos _).le k)),
      Complex.normSq_eq_norm_sq]
  have hpoly_o : (fun y : ℝ ↦ Real.exp (-a * y) * (6 * π + 36 + 4 * y ^ 2)) =O[atTop]
      fun _ : ℝ ↦ (1 : ℝ) := by
    have h2 : Tendsto (fun y : ℝ ↦ y ^ 2 / Real.exp (a * y)) atTop (𝓝 0) :=
      (isLittleO_pow_exp_pos_mul_atTop 2 ha).tendsto_div_nhds_zero
    have h0 : Tendsto (fun y : ℝ ↦ Real.exp (-a * y) * (6 * π + 36 + 4 * y ^ 2)) atTop (𝓝 0) := by
      refine squeeze_zero_norm' ?_ (h2.const_mul (6 * π + 40) |>.trans (by simp))
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
      rw [Real.norm_of_nonneg (by positivity), neg_mul, Real.exp_neg, inv_mul_eq_div]
      have hpoly : 6 * π + 36 + 4 * y ^ 2 ≤ (6 * π + 40) * y ^ 2 := by
        have hy2 : 1 ≤ y ^ 2 := by nlinarith
        nlinarith [Real.pi_pos]
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right hpoly (Real.exp_pos _).le
    exact h0.isBigO_one ℝ
  have hbigO : (fun τ : ℍ ↦ ‖f (γ • τ)‖ ^ 2 * (γ • τ).im ^ k * (6 * π + 36 + 4 * τ.im ^ 2))
      =O[atImInfty] fun τ : ℍ ↦ τ.im ^ (0 : ℝ) := by
    have h1 : (fun τ : ℍ ↦ ‖f (γ • τ)‖ ^ 2 * (γ • τ).im ^ k) =O[atImInfty]
        fun τ : ℍ ↦ Real.exp (-a * τ.im) := by
      simpa only [hpet_eq] using hexp.norm_left
    have h2 : (fun τ : ℍ ↦ ‖f (γ • τ)‖ ^ 2 * (γ • τ).im ^ k * (6 * π + 36 + 4 * τ.im ^ 2))
        =O[atImInfty] fun τ : ℍ ↦ Real.exp (-a * τ.im) * (6 * π + 36 + 4 * τ.im ^ 2) :=
      h1.mul (Asymptotics.isBigO_refl _ _)
    have h3 : (fun τ : ℍ ↦ Real.exp (-a * τ.im) * (6 * π + 36 + 4 * τ.im ^ 2))
        =O[atImInfty] fun _ : ℍ ↦ (1 : ℝ) :=
      hpoly_o.comp_tendsto tendsto_comap
    simpa only [Real.rpow_zero] using h2.trans h3
  have hcont : Continuous fun τ : ℍ ↦
      ‖f (γ • τ)‖ ^ 2 * (γ • τ).im ^ k * (6 * π + 36 + 4 * τ.im ^ 2) := by
    have hsmul : Continuous fun τ : ℍ ↦ γ • τ := by
      simp only [MulAction.compHom_smul_def]
      exact continuous_const_smul (mapGL ℝ γ)
    refine ((((ModularFormClass.continuous f).comp hsmul).norm.pow 2).mul ?_).mul (by fun_prop)
    exact (UpperHalfPlane.continuous_im.comp hsmul).zpow₀ k fun τ ↦
      Or.inl (UpperHalfPlane.im_pos _).ne'
  obtain ⟨F, hF⟩ := ModularGroup.exists_bound_fundamental_domain_of_isBigO hcont hbigO
  refine ⟨max F 0, le_max_right _ _, fun τ hτ ↦ ?_⟩
  have h := hF τ hτ
  rw [Real.rpow_zero, mul_one, Real.norm_of_nonneg (by
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (zpow_nonneg (UpperHalfPlane.im_pos _).le k))
      (by positivity))] at h
  exact h.trans (le_max_left _ _)

private theorem sub_one_mul_realAnalyticEisenstein_le_of_mem_fd (N : ℕ) (γ : SL(2, ℤ))
    {τ : ℍ} (hτ : τ ∈ fd) {s : ℝ} (hs1 : 1 < s) (hs2 : s ≤ 2) :
    (s - 1) * realAnalyticEisenstein N (γ • τ) s ≤ 6 * π + 36 + 4 * τ.im ^ 2 := by
  have hs0 : 0 ≤ s - 1 := by linarith
  have h1 : realAnalyticEisenstein N (γ • τ) s ≤ realAnalyticEisenstein 1 (γ • τ) s :=
    realAnalyticEisenstein_le_one N (γ • τ) hs1
  have h2 : realAnalyticEisenstein 1 (γ • τ) s = realAnalyticEisenstein 1 τ s :=
    realAnalyticEisenstein_smul 1 (by simp) τ s
  have h3 : realAnalyticEisenstein 1 τ s ≤ realAnalyticEpstein τ s :=
    realAnalyticEisenstein_one_le_realAnalyticEpstein τ hs1
  have him : (1 / 2 : ℝ) ≤ τ.im := by
    have h34 := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hτ
    nlinarith [UpperHalfPlane.im_pos τ]
  calc (s - 1) * realAnalyticEisenstein N (γ • τ) s
      ≤ (s - 1) * realAnalyticEpstein τ s :=
        mul_le_mul_of_nonneg_left (h1.trans (h2.le.trans h3)) hs0
    _ ≤ 6 * π + 36 + 4 * τ.im ^ 2 := sub_one_mul_realAnalyticEpstein_le τ him hs1 hs2

private theorem integrableOn_fd_mul_realAnalyticEisenstein {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma1 N).map (mapGL ℝ)) k) (γ : SL(2, ℤ))
    {s : ℝ} (hs1 : 1 < s) (hs2 : s ≤ 2) :
    IntegrableOn
      (fun τ : ℍ ↦ ‖f (γ • τ)‖ ^ 2 * (γ • τ).im ^ k * realAnalyticEisenstein N (γ • τ) s)
      fd volume := by
  obtain ⟨M, _, hM⟩ := exists_bound_norm_sq_mul_im_zpow_mul_poly_fd f γ
  have hsmul : Continuous fun τ : ℍ ↦ γ • τ := by
    simp only [MulAction.compHom_smul_def]
    exact continuous_const_smul (mapGL ℝ γ)
  have hcont_phi : Continuous fun τ : ℍ ↦ ‖f (γ • τ)‖ ^ 2 * (γ • τ).im ^ k :=
    (((ModularFormClass.continuous f).comp hsmul).norm.pow 2).mul
      ((UpperHalfPlane.continuous_im.comp hsmul).zpow₀ k fun τ ↦
        Or.inl (UpperHalfPlane.im_pos _).ne')
  have hmeas : Measurable fun τ : ℍ ↦
      ‖f (γ • τ)‖ ^ 2 * (γ • τ).im ^ k * realAnalyticEisenstein N (γ • τ) s :=
    hcont_phi.measurable.mul ((measurable_realAnalyticEisenstein N s).comp hsmul.measurable)
  refine IntegrableOn.of_bound ModularGroup.volume_fd_lt_top hmeas.aestronglyMeasurable.restrict
    (M / (s - 1)) ?_
  filter_upwards [ae_restrict_mem isClosed_fd.measurableSet] with τ hτ
  have hnn : 0 ≤ ‖f (γ • τ)‖ ^ 2 * (γ • τ).im ^ k * realAnalyticEisenstein N (γ • τ) s :=
    mul_nonneg (mul_nonneg (sq_nonneg _) (zpow_nonneg (UpperHalfPlane.im_pos _).le k))
      (realAnalyticEisenstein_nonneg N _ s)
  rw [Real.norm_of_nonneg hnn, le_div_iff₀ (sub_pos.mpr hs1)]
  calc ‖f (γ • τ)‖ ^ 2 * (γ • τ).im ^ k * realAnalyticEisenstein N (γ • τ) s * (s - 1)
      = ‖f (γ • τ)‖ ^ 2 * (γ • τ).im ^ k * ((s - 1) * realAnalyticEisenstein N (γ • τ) s) := by
        ring
    _ ≤ ‖f (γ • τ)‖ ^ 2 * (γ • τ).im ^ k * (6 * π + 36 + 4 * τ.im ^ 2) :=
        mul_le_mul_of_nonneg_left (sub_one_mul_realAnalyticEisenstein_le_of_mem_fd N γ hτ hs1 hs2)
          (mul_nonneg (sq_nonneg _) (zpow_nonneg (UpperHalfPlane.im_pos _).le k))
    _ ≤ M := hM τ hτ

private theorem tendsto_sub_one_mul_setIntegral_fd {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma1 N).map (mapGL ℝ)) k) (γ : SL(2, ℤ)) :
    Tendsto
      (fun s : ℝ ↦ (s - 1) * ∫ τ in fd,
        ‖f (γ • τ)‖ ^ 2 * (γ • τ).im ^ k * realAnalyticEisenstein N (γ • τ) s)
      (𝓝[>] 1)
      (𝓝 (3 / (π * ((CongruenceSubgroup.Gamma0 N).index : ℝ)) *
        ∫ τ in fd, ‖f (γ • τ)‖ ^ 2 * (γ • τ).im ^ k)) := by
  obtain ⟨M, _, hM⟩ := exists_bound_norm_sq_mul_im_zpow_mul_poly_fd f γ
  have hsmul : Continuous fun τ : ℍ ↦ γ • τ := by
    simp only [MulAction.compHom_smul_def]
    exact continuous_const_smul (mapGL ℝ γ)
  have hcont_phi : Continuous fun τ : ℍ ↦ ‖f (γ • τ)‖ ^ 2 * (γ • τ).im ^ k :=
    (((ModularFormClass.continuous f).comp hsmul).norm.pow 2).mul
      ((UpperHalfPlane.continuous_im.comp hsmul).zpow₀ k fun τ ↦
        Or.inl (UpperHalfPlane.im_pos _).ne')
  have : IsFiniteMeasure (volume.restrict (fd : Set ℍ)) :=
    ⟨by simpa using ModularGroup.volume_fd_lt_top⟩
  have hdct : Tendsto
      (fun s : ℝ ↦ ∫ τ in fd,
        (s - 1) * (‖f (γ • τ)‖ ^ 2 * (γ • τ).im ^ k * realAnalyticEisenstein N (γ • τ) s))
      (𝓝[>] 1)
      (𝓝 (∫ τ in fd,
        ‖f (γ • τ)‖ ^ 2 * (γ • τ).im ^ k *
          (3 / (π * ((CongruenceSubgroup.Gamma0 N).index : ℝ))))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ ↦ M) ?_ ?_
      (integrable_const M) ?_
    · filter_upwards [Ioc_mem_nhdsGT (one_lt_two)] with s _
      have hmeas : Measurable fun τ : ℍ ↦
          (s - 1) * (‖f (γ • τ)‖ ^ 2 * (γ • τ).im ^ k * realAnalyticEisenstein N (γ • τ) s) :=
        measurable_const.mul
          (hcont_phi.measurable.mul ((measurable_realAnalyticEisenstein N s).comp hsmul.measurable))
      exact hmeas.aestronglyMeasurable
    · filter_upwards [Ioc_mem_nhdsGT (one_lt_two)] with s ⟨hs1, hs2⟩
      filter_upwards [ae_restrict_mem isClosed_fd.measurableSet] with τ hτ
      have hnn : 0 ≤ (s - 1) * (‖f (γ • τ)‖ ^ 2 * (γ • τ).im ^ k *
          realAnalyticEisenstein N (γ • τ) s) :=
        mul_nonneg (sub_nonneg.mpr hs1.le)
          (mul_nonneg (mul_nonneg (sq_nonneg _) (zpow_nonneg (UpperHalfPlane.im_pos _).le k))
            (realAnalyticEisenstein_nonneg N _ s))
      rw [Real.norm_of_nonneg hnn]
      calc (s - 1) * (‖f (γ • τ)‖ ^ 2 * (γ • τ).im ^ k * realAnalyticEisenstein N (γ • τ) s)
          = ‖f (γ • τ)‖ ^ 2 * (γ • τ).im ^ k * ((s - 1) * realAnalyticEisenstein N (γ • τ) s) := by
            ring
        _ ≤ ‖f (γ • τ)‖ ^ 2 * (γ • τ).im ^ k * (6 * π + 36 + 4 * τ.im ^ 2) :=
            mul_le_mul_of_nonneg_left
              (sub_one_mul_realAnalyticEisenstein_le_of_mem_fd N γ hτ hs1 hs2)
              (mul_nonneg (sq_nonneg _) (zpow_nonneg (UpperHalfPlane.im_pos _).le k))
        _ ≤ M := hM τ hτ
    · refine ae_of_all _ fun τ ↦ ?_
      have heq : (fun s : ℝ ↦ (s - 1) * (‖f (γ • τ)‖ ^ 2 * (γ • τ).im ^ k *
            realAnalyticEisenstein N (γ • τ) s)) =
          fun s : ℝ ↦ ‖f (γ • τ)‖ ^ 2 * (γ • τ).im ^ k *
            ((s - 1) * realAnalyticEisenstein N (γ • τ) s) := by
        ext s; ring
      rw [heq]
      exact (tendsto_sub_one_mul_realAnalyticEisenstein N (γ • τ)).const_mul _
  simp only [integral_const_mul, integral_mul_const] at hdct
  rwa [mul_comm] at hdct

private theorem integrableOn_re_Ico_and_eq_sum_fd {N : ℕ} [NeZero N] {k : ℤ}
    {χ : (ZMod N)ˣ →* ℂˣ} {f : CuspForm ((CongruenceSubgroup.Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ TauCeti.cuspFormCharSpace k χ) {s : ℝ} (hs1 : 1 < s) (hs2 : s ≤ 2) :
    IntegrableOn (fun τ : ℍ ↦ ‖f τ‖ ^ 2 * τ.im ^ k * τ.im ^ s)
        (UpperHalfPlane.re ⁻¹' Set.Ico (0 : ℝ) 1) volume ∧
      (∫ τ in UpperHalfPlane.re ⁻¹' Set.Ico (0 : ℝ) 1, ‖f τ‖ ^ 2 * τ.im ^ k * τ.im ^ s) =
        ∑ r : SL(2, ℤ) ⧸ (CongruenceSubgroup.Gamma0 N).withCenter,
          ∫ τ in fd, ‖f (((r.out : SL(2, ℤ)))⁻¹ • τ)‖ ^ 2 *
            ((((r.out : SL(2, ℤ)))⁻¹ • τ).im) ^ k *
            realAnalyticEisenstein N (((r.out : SL(2, ℤ)))⁻¹ • τ) s := by
  have hunfold := setLIntegral_re_Ico_eq_sum_fd hf hs1
  have hfd_int : ∀ r : SL(2, ℤ) ⧸ (CongruenceSubgroup.Gamma0 N).withCenter,
      IntegrableOn (fun τ : ℍ ↦ ‖f (((r.out : SL(2, ℤ)))⁻¹ • τ)‖ ^ 2 *
        ((((r.out : SL(2, ℤ)))⁻¹ • τ).im) ^ k *
        realAnalyticEisenstein N (((r.out : SL(2, ℤ)))⁻¹ • τ) s) fd volume :=
    fun r ↦ integrableOn_fd_mul_realAnalyticEisenstein f ((r.out : SL(2, ℤ)))⁻¹ hs1 hs2
  have hfd_eq : ∀ r : SL(2, ℤ) ⧸ (CongruenceSubgroup.Gamma0 N).withCenter,
      ∫⁻ τ in fd, ENNReal.ofReal (‖f (((r.out : SL(2, ℤ)))⁻¹ • τ)‖ ^ 2 *
          ((((r.out : SL(2, ℤ)))⁻¹ • τ).im) ^ k *
          realAnalyticEisenstein N (((r.out : SL(2, ℤ)))⁻¹ • τ) s) =
        ENNReal.ofReal (∫ τ in fd, ‖f (((r.out : SL(2, ℤ)))⁻¹ • τ)‖ ^ 2 *
          ((((r.out : SL(2, ℤ)))⁻¹ • τ).im) ^ k *
          realAnalyticEisenstein N (((r.out : SL(2, ℤ)))⁻¹ • τ) s) := fun r ↦
    (ofReal_integral_eq_lintegral_ofReal (hfd_int r) (ae_of_all _ fun τ ↦
      mul_nonneg (mul_nonneg (sq_nonneg _) (zpow_nonneg (UpperHalfPlane.im_pos _).le k))
        (realAnalyticEisenstein_nonneg N _ s))).symm
  have hsum_eq :
      ∫⁻ τ in UpperHalfPlane.re ⁻¹' Set.Ico (0 : ℝ) 1,
          ENNReal.ofReal (‖f τ‖ ^ 2 * τ.im ^ k * τ.im ^ s) =
        ENNReal.ofReal (∑ r : SL(2, ℤ) ⧸ (CongruenceSubgroup.Gamma0 N).withCenter,
          ∫ τ in fd, ‖f (((r.out : SL(2, ℤ)))⁻¹ • τ)‖ ^ 2 *
            ((((r.out : SL(2, ℤ)))⁻¹ • τ).im) ^ k *
            realAnalyticEisenstein N (((r.out : SL(2, ℤ)))⁻¹ • τ) s) := by
    rw [hunfold]
    simp_rw [hfd_eq]
    rw [← ENNReal.ofReal_sum_of_nonneg fun r _ ↦ setIntegral_nonneg isClosed_fd.measurableSet
      fun τ _ ↦ mul_nonneg (mul_nonneg (sq_nonneg _) (zpow_nonneg (UpperHalfPlane.im_pos _).le k))
        (realAnalyticEisenstein_nonneg N _ s)]
  have hstrip_int : IntegrableOn (fun τ : ℍ ↦ ‖f τ‖ ^ 2 * τ.im ^ k * τ.im ^ s)
      (UpperHalfPlane.re ⁻¹' Set.Ico (0 : ℝ) 1) volume := by
    have hcont : Continuous fun τ : ℍ ↦ ‖f τ‖ ^ 2 * τ.im ^ k * τ.im ^ s := by
      refine (((ModularFormClass.continuous f).norm.pow 2).mul ?_).mul
        (UpperHalfPlane.continuous_im.rpow continuous_const fun τ ↦ Or.inl τ.im_pos.ne')
      exact UpperHalfPlane.continuous_im.zpow₀ k fun τ ↦ Or.inl τ.im_pos.ne'
    refine ⟨hcont.aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    have heq : ∫⁻ τ in UpperHalfPlane.re ⁻¹' Set.Ico (0 : ℝ) 1,
          ‖‖f τ‖ ^ 2 * τ.im ^ k * τ.im ^ s‖ₑ =
        ∫⁻ τ in UpperHalfPlane.re ⁻¹' Set.Ico (0 : ℝ) 1,
          ENNReal.ofReal (‖f τ‖ ^ 2 * τ.im ^ k * τ.im ^ s) := by
      refine lintegral_congr fun τ ↦ ?_
      rw [Real.eNorm_eq_ofReal (mul_nonneg
        (mul_nonneg (sq_nonneg _) (zpow_nonneg τ.im_pos.le k)) (rpow_nonneg τ.im_pos.le s))]
    rw [heq, hsum_eq]
    exact ENNReal.ofReal_lt_top
  refine ⟨hstrip_int, ?_⟩
  have hofReal : ENNReal.ofReal
      (∫ τ in UpperHalfPlane.re ⁻¹' Set.Ico (0 : ℝ) 1, ‖f τ‖ ^ 2 * τ.im ^ k * τ.im ^ s) =
      ENNReal.ofReal (∑ r : SL(2, ℤ) ⧸ (CongruenceSubgroup.Gamma0 N).withCenter,
        ∫ τ in fd, ‖f (((r.out : SL(2, ℤ)))⁻¹ • τ)‖ ^ 2 *
          ((((r.out : SL(2, ℤ)))⁻¹ • τ).im) ^ k *
          realAnalyticEisenstein N (((r.out : SL(2, ℤ)))⁻¹ • τ) s) := by
    rw [ofReal_integral_eq_lintegral_ofReal hstrip_int (ae_of_all _ fun τ ↦
      mul_nonneg (mul_nonneg (sq_nonneg _) (zpow_nonneg τ.im_pos.le k))
        (rpow_nonneg τ.im_pos.le s)), hsum_eq]
  have hnn1 : 0 ≤ ∫ τ in UpperHalfPlane.re ⁻¹' Set.Ico (0 : ℝ) 1,
      ‖f τ‖ ^ 2 * τ.im ^ k * τ.im ^ s :=
    setIntegral_nonneg (UpperHalfPlane.continuous_re.measurable measurableSet_Ico) fun τ _ ↦
      mul_nonneg (mul_nonneg (sq_nonneg _) (zpow_nonneg τ.im_pos.le k))
        (rpow_nonneg τ.im_pos.le s)
  have hnn2 : 0 ≤ ∑ r : SL(2, ℤ) ⧸ (CongruenceSubgroup.Gamma0 N).withCenter,
      ∫ τ in fd, ‖f (((r.out : SL(2, ℤ)))⁻¹ • τ)‖ ^ 2 *
        ((((r.out : SL(2, ℤ)))⁻¹ • τ).im) ^ k *
        realAnalyticEisenstein N (((r.out : SL(2, ℤ)))⁻¹ • τ) s :=
    Finset.sum_nonneg fun r _ ↦ setIntegral_nonneg isClosed_fd.measurableSet fun τ _ ↦
      mul_nonneg (mul_nonneg (sq_nonneg _) (zpow_nonneg (UpperHalfPlane.im_pos _).le k))
        (realAnalyticEisenstein_nonneg N _ s)
  exact (ENNReal.ofReal_eq_ofReal_iff hnn1 hnn2).mp hofReal

/-! ### Index bridge from `Γ₀(N)` cosets to `peterssonInnerCosets` -/

private theorem inv_index_Gamma0_mul_sum_fd_eq_inv_index_Gamma1 {N : ℕ} [NeZero N] {k : ℤ}
    {χ : (ZMod N)ˣ →* ℂˣ} {f : CuspForm ((CongruenceSubgroup.Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ TauCeti.cuspFormCharSpace k χ) :
    ((CongruenceSubgroup.Gamma0 N).index : ℝ)⁻¹ *
        ∑ r : SL(2, ℤ) ⧸ (CongruenceSubgroup.Gamma0 N).withCenter,
          ∫ τ in fd, ‖f (((r.out : SL(2, ℤ)))⁻¹ • τ)‖ ^ 2 *
            ((((r.out : SL(2, ℤ)))⁻¹ • τ).im) ^ k =
      ((CongruenceSubgroup.Gamma1 N).withCenter.index : ℝ)⁻¹ *
        (CuspForm.peterssonInnerCosets f f).re := by
  let H₁ := (CongruenceSubgroup.Gamma1 N).withCenter
  let H₀ := (CongruenceSubgroup.Gamma0 N).withCenter
  have hH₀_eq : H₀ = CongruenceSubgroup.Gamma0 N :=
    Subgroup.withCenter_eq_self_iff.mpr (TauCeti.CongruenceSubgroup.center_le_Gamma0 N)
  have hle : H₁ ≤ H₀ := by
    rw [hH₀_eq]
    exact CongruenceSubgroup.withCenter_le_Gamma0 (CongruenceSubgroup.Gamma1_in_Gamma0 N)
  let : Fintype (H₀ ⧸ H₁.subgroupOf H₀) := Fintype.ofFinite _
  -- Rewrite `(peterssonInnerCosets f f).re` as a sum of real `fd` integrals over `SL(2, ℤ) ⧸ H₁`
  have hre : (CuspForm.peterssonInnerCosets f f).re =
      ∑ q : SL(2, ℤ) ⧸ H₁, ∫ τ in fd,
        ‖f (((q.out : SL(2, ℤ)))⁻¹ • τ)‖ ^ 2 * ((((q.out : SL(2, ℤ)))⁻¹ • τ).im) ^ k := by
    rw [CuspForm.peterssonInnerCosets_def, Complex.re_sum]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    rw [UpperHalfPlane.peterssonInner_self_eq_ofReal, Complex.ofReal_re]
    refine setIntegral_congr_fun isClosed_fd.measurableSet fun τ _ ↦ ?_
    have h := UpperHalfPlane.petersson_slash_SL k ⇑f ⇑f (q.out)⁻¹ τ
    rw [UpperHalfPlane.petersson_self_eq_ofReal, UpperHalfPlane.petersson_self_eq_ofReal] at h
    have h' := Complex.ofReal_injective h
    simpa only [Complex.normSq_eq_norm_sq] using h'
  -- Reindex `SL(2, ℤ) ⧸ H₁` by `(SL(2, ℤ) ⧸ H₀) × (H₀ ⧸ H₁.subgroupOf H₀)`
  have hkey : ∀ (r : SL(2, ℤ) ⧸ H₀) (i : H₀ ⧸ H₁.subgroupOf H₀),
      (∫ τ in fd,
        ‖f (((((Subgroup.quotientEquivProdOfLE hle).symm (r, i)).out : SL(2, ℤ)))⁻¹ • τ)‖ ^ 2 *
          ((((((Subgroup.quotientEquivProdOfLE hle).symm (r, i)).out : SL(2, ℤ)))⁻¹ • τ).im) ^ k) =
      ∫ τ in fd,
        ‖f (((r.out : SL(2, ℤ)))⁻¹ • τ)‖ ^ 2 * ((((r.out : SL(2, ℤ)))⁻¹ • τ).im) ^ k := by
    intro r i
    induction i using QuotientGroup.induction_on with
    | H γ =>
      let q : SL(2, ℤ) ⧸ H₁ := QuotientGroup.mk (r.out * (γ : SL(2, ℤ)))
      have hsymm : (Subgroup.quotientEquivProdOfLE hle).symm (r, QuotientGroup.mk γ) = q := rfl
      rw [hsymm]
      have hrel : (r.out * (γ : SL(2, ℤ)))⁻¹ * q.out ∈ H₁ := by
        have h := QuotientGroup.out_eq' q
        exact QuotientGroup.eq.mp h.symm
      have hmem0 : (q.out)⁻¹ * r.out ∈ CongruenceSubgroup.Gamma0 N := by
        have h1 : (q.out)⁻¹ * (r.out * (γ : SL(2, ℤ))) ∈ H₀ :=
          hle (by simpa [mul_inv_rev, mul_assoc] using H₁.inv_mem hrel)
        have h2 : ((q.out)⁻¹ * (r.out * (γ : SL(2, ℤ)))) * (γ : SL(2, ℤ))⁻¹ ∈ H₀ :=
          H₀.mul_mem h1 (H₀.inv_mem γ.2)
        have h3 : (q.out)⁻¹ * r.out ∈ H₀ := by simpa [mul_assoc] using h2
        exact hH₀_eq.le h3
      refine setIntegral_congr_fun isClosed_fd.measurableSet fun τ _ ↦ ?_
      have hmul : ((q.out : SL(2, ℤ)))⁻¹ • τ =
          (((q.out : SL(2, ℤ)))⁻¹ * r.out) • (((r.out : SL(2, ℤ)))⁻¹ • τ) := by
        rw [← mul_smul, mul_assoc, mul_inv_cancel, mul_one]
      rw [hmul]
      exact norm_sq_mul_im_zpow_smul_of_mem_cuspFormCharSpace hf hmem0 _
  have hprod_sum : (CuspForm.peterssonInnerCosets f f).re =
      (H₁.relIndex H₀ : ℝ) *
        ∑ r : SL(2, ℤ) ⧸ H₀, ∫ τ in fd,
          ‖f (((r.out : SL(2, ℤ)))⁻¹ • τ)‖ ^ 2 * ((((r.out : SL(2, ℤ)))⁻¹ • τ).im) ^ k := by
    rw [hre, ← (Subgroup.quotientEquivProdOfLE hle).symm.sum_comp, Fintype.sum_prod_type]
    simp only [hkey, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]
    rw [Subgroup.relIndex, Subgroup.index_eq_card, Nat.card_eq_fintype_card]
  have hidx_mul : (H₁.relIndex H₀ : ℝ) * ((CongruenceSubgroup.Gamma0 N).index : ℝ) =
      (H₁.index : ℝ) := by
    have hnat : H₁.relIndex H₀ * H₀.index = H₁.index := Subgroup.relIndex_mul_index hle
    rw [show H₀.index = (CongruenceSubgroup.Gamma0 N).index from congrArg Subgroup.index hH₀_eq]
      at hnat
    exact_mod_cast hnat
  have hrel_ne : (H₁.relIndex H₀ : ℝ) ≠ 0 := by
    have hH₁_fi : H₁.FiniteIndex :=
      Subgroup.finiteIndex_of_le (CongruenceSubgroup.Gamma1 N).le_withCenter
    have hH₁_ne : H₁.index ≠ 0 := Subgroup.index_ne_zero
    intro h0
    have h0' : H₁.relIndex H₀ = 0 := by exact_mod_cast h0
    have hnat : H₁.relIndex H₀ * H₀.index = H₁.index := Subgroup.relIndex_mul_index hle
    rw [h0', zero_mul] at hnat
    exact hH₁_ne hnat.symm
  rw [hprod_sum, ← hidx_mul, mul_inv_rev]
  field_simp [hrel_ne]
  rfl

/-! ### Main Rankin–Selberg residue theorem and Petersson norm equality -/

/-- **Rankin–Selberg residue formula for cusp forms with nebentypus**: for
`f ∈ S_k(Γ₁(N), χ)` (`N ≠ 0`),
$$\lim_{s \to 1^+} (s - 1) \int_{0 \le \operatorname{Re}\tau < 1}
    |f(\tau)|^2 (\operatorname{Im}\tau)^{k + s}\, d\mu(\tau)
  = \frac{3}{\pi\, [SL_2(\mathbb{Z}) : \Gamma_1(N)\cdot\{\pm I\}]}
    \operatorname{Re}\langle f, f \rangle.$$
Since `peterssonInnerCosets f f` is real (`peterssonInnerCosets_self_im`), its real part
determines `peterssonInnerCosets f f`. -/
theorem tendsto_sub_one_mul_setIntegral_norm_sq_mul_im {N : ℕ} [NeZero N] {k : ℤ}
    {χ : (ZMod N)ˣ →* ℂˣ} {f : CuspForm ((CongruenceSubgroup.Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ TauCeti.cuspFormCharSpace k χ) :
    Tendsto
      (fun s : ℝ ↦ (s - 1) *
        ∫ τ in UpperHalfPlane.re ⁻¹' Set.Ico (0 : ℝ) 1, ‖f τ‖ ^ 2 * τ.im ^ k * τ.im ^ s)
      (𝓝[>] 1)
      (𝓝 (3 / (π * ((CongruenceSubgroup.Gamma1 N).withCenter.index : ℝ)) *
        (CuspForm.peterssonInnerCosets f f).re)) := by
  have hsum_tendsto : Tendsto
      (fun s : ℝ ↦ ∑ r : SL(2, ℤ) ⧸ (CongruenceSubgroup.Gamma0 N).withCenter,
        (s - 1) * ∫ τ in fd, ‖f (((r.out : SL(2, ℤ)))⁻¹ • τ)‖ ^ 2 *
          ((((r.out : SL(2, ℤ)))⁻¹ • τ).im) ^ k *
          realAnalyticEisenstein N (((r.out : SL(2, ℤ)))⁻¹ • τ) s)
      (𝓝[>] 1)
      (𝓝 (∑ r : SL(2, ℤ) ⧸ (CongruenceSubgroup.Gamma0 N).withCenter,
        3 / (π * ((CongruenceSubgroup.Gamma0 N).index : ℝ)) *
          ∫ τ in fd, ‖f (((r.out : SL(2, ℤ)))⁻¹ • τ)‖ ^ 2 *
            ((((r.out : SL(2, ℤ)))⁻¹ • τ).im) ^ k)) :=
    tendsto_finsetSum _ fun r _ ↦ tendsto_sub_one_mul_setIntegral_fd f ((r.out : SL(2, ℤ)))⁻¹
  have hlim : (∑ r : SL(2, ℤ) ⧸ (CongruenceSubgroup.Gamma0 N).withCenter,
        3 / (π * ((CongruenceSubgroup.Gamma0 N).index : ℝ)) *
          ∫ τ in fd, ‖f (((r.out : SL(2, ℤ)))⁻¹ • τ)‖ ^ 2 *
            ((((r.out : SL(2, ℤ)))⁻¹ • τ).im) ^ k) =
      3 / (π * ((CongruenceSubgroup.Gamma1 N).withCenter.index : ℝ)) *
        (CuspForm.peterssonInnerCosets f f).re := by
    rw [← Finset.mul_sum]
    calc 3 / (π * ((CongruenceSubgroup.Gamma0 N).index : ℝ)) *
            ∑ r : SL(2, ℤ) ⧸ (CongruenceSubgroup.Gamma0 N).withCenter,
              ∫ τ in fd, ‖f (((r.out : SL(2, ℤ)))⁻¹ • τ)‖ ^ 2 *
                ((((r.out : SL(2, ℤ)))⁻¹ • τ).im) ^ k
        = (3 / π) * (((CongruenceSubgroup.Gamma0 N).index : ℝ)⁻¹ *
            ∑ r : SL(2, ℤ) ⧸ (CongruenceSubgroup.Gamma0 N).withCenter,
              ∫ τ in fd, ‖f (((r.out : SL(2, ℤ)))⁻¹ • τ)‖ ^ 2 *
                ((((r.out : SL(2, ℤ)))⁻¹ • τ).im) ^ k) := by ring
      _ = (3 / π) * (((CongruenceSubgroup.Gamma1 N).withCenter.index : ℝ)⁻¹ *
            (CuspForm.peterssonInnerCosets f f).re) := by
          rw [inv_index_Gamma0_mul_sum_fd_eq_inv_index_Gamma1 hf]
      _ = 3 / (π * ((CongruenceSubgroup.Gamma1 N).withCenter.index : ℝ)) *
            (CuspForm.peterssonInnerCosets f f).re := by ring
  rw [hlim] at hsum_tendsto
  refine hsum_tendsto.congr' ?_
  filter_upwards [Ioc_mem_nhdsGT (one_lt_two)] with s ⟨hs1, hs2⟩
  rw [← Finset.mul_sum, (integrableOn_re_Ico_and_eq_sum_fd hf hs1 hs2).2]

/-- **Equal Fourier coefficient norms imply equal index-normalized Petersson norms.** If
`f ∈ S_k(Γ₁(N₁), χ₁)` and `g ∈ S_k(Γ₁(N₂), χ₂)` are cusp forms with nebentypus (at possibly
different levels and characters) satisfying `‖a_n(f)‖ = ‖a_n(g)‖` for all `n : ℕ`, then
`[SL₂(ℤ) : Γ₁(N₁)·{±I}]⁻¹ · ⟪f, f⟫ = [SL₂(ℤ) : Γ₁(N₂)·{±I}]⁻¹ · ⟪g, g⟫`. -/
theorem inv_index_mul_peterssonInnerCosets_self_eq_of_norm_qExpansion_coeff_eq
    {N₁ N₂ : ℕ} [NeZero N₁] [NeZero N₂] {k : ℤ}
    {χ₁ : (ZMod N₁)ˣ →* ℂˣ} {χ₂ : (ZMod N₂)ˣ →* ℂˣ}
    {f : CuspForm ((CongruenceSubgroup.Gamma1 N₁).map (mapGL ℝ)) k}
    {g : CuspForm ((CongruenceSubgroup.Gamma1 N₂).map (mapGL ℝ)) k}
    (hf : f ∈ TauCeti.cuspFormCharSpace k χ₁) (hg : g ∈ TauCeti.cuspFormCharSpace k χ₂)
    (hcoeff : ∀ n : ℕ, ‖(qExpansion 1 f).coeff n‖ = ‖(qExpansion 1 g).coeff n‖) :
    ((CongruenceSubgroup.Gamma1 N₁).withCenter.index : ℂ)⁻¹ *
        CuspForm.peterssonInnerCosets f f =
      ((CongruenceSubgroup.Gamma1 N₂).withCenter.index : ℂ)⁻¹ *
        CuspForm.peterssonInnerCosets g g := by
  have ht1 := tendsto_sub_one_mul_setIntegral_norm_sq_mul_im hf
  have ht2 := tendsto_sub_one_mul_setIntegral_norm_sq_mul_im hg
  have hev : (fun s : ℝ ↦ (s - 1) *
        ∫ τ in UpperHalfPlane.re ⁻¹' Set.Ico (0 : ℝ) 1, ‖f τ‖ ^ 2 * τ.im ^ k * τ.im ^ s) =ᶠ[𝓝[>] 1]
      fun s : ℝ ↦ (s - 1) *
        ∫ τ in UpperHalfPlane.re ⁻¹' Set.Ico (0 : ℝ) 1, ‖g τ‖ ^ 2 * τ.im ^ k * τ.im ^ s := by
    filter_upwards [Ioc_mem_nhdsGT (one_lt_two)] with s ⟨hs1, hs2⟩
    congr 1
    have hlint : ∫⁻ τ in UpperHalfPlane.re ⁻¹' Set.Ico (0 : ℝ) 1,
          ENNReal.ofReal (‖f τ‖ ^ 2 * τ.im ^ k * τ.im ^ s) =
        ∫⁻ τ in UpperHalfPlane.re ⁻¹' Set.Ico (0 : ℝ) 1,
          ENNReal.ofReal (‖g τ‖ ^ 2 * τ.im ^ k * τ.im ^ s) := by
      rw [setLIntegral_re_Ico_eq_parseval f s, setLIntegral_re_Ico_eq_parseval g s]
      simp_rw [hcoeff]
    have h1 := (integrableOn_re_Ico_and_eq_sum_fd hf hs1 hs2).1
    have h2 := (integrableOn_re_Ico_and_eq_sum_fd hg hs1 hs2).1
    have hofReal : ENNReal.ofReal
          (∫ τ in UpperHalfPlane.re ⁻¹' Set.Ico (0 : ℝ) 1, ‖f τ‖ ^ 2 * τ.im ^ k * τ.im ^ s) =
        ENNReal.ofReal
          (∫ τ in UpperHalfPlane.re ⁻¹' Set.Ico (0 : ℝ) 1, ‖g τ‖ ^ 2 * τ.im ^ k * τ.im ^ s) := by
      rw [ofReal_integral_eq_lintegral_ofReal h1 (ae_of_all _ fun τ ↦
          mul_nonneg (mul_nonneg (sq_nonneg _) (zpow_nonneg τ.im_pos.le k))
            (rpow_nonneg τ.im_pos.le s)),
        ofReal_integral_eq_lintegral_ofReal h2 (ae_of_all _ fun τ ↦
          mul_nonneg (mul_nonneg (sq_nonneg _) (zpow_nonneg τ.im_pos.le k))
            (rpow_nonneg τ.im_pos.le s)),
        hlint]
    have hnn : ∀ {M : ℕ} (h : CuspForm ((CongruenceSubgroup.Gamma1 M).map (mapGL ℝ)) k),
        0 ≤ ∫ τ in UpperHalfPlane.re ⁻¹' Set.Ico (0 : ℝ) 1, ‖h τ‖ ^ 2 * τ.im ^ k * τ.im ^ s :=
      fun h ↦ setIntegral_nonneg (UpperHalfPlane.continuous_re.measurable measurableSet_Ico)
        fun τ _ ↦ mul_nonneg (mul_nonneg (sq_nonneg _) (zpow_nonneg τ.im_pos.le k))
          (rpow_nonneg τ.im_pos.le s)
    exact (ENNReal.ofReal_eq_ofReal_iff (hnn f) (hnn g)).mp hofReal
  have hlim_eq := tendsto_nhds_unique (ht1.congr' hev) ht2
  have hre_eq : ((CongruenceSubgroup.Gamma1 N₁).withCenter.index : ℝ)⁻¹ *
        (CuspForm.peterssonInnerCosets f f).re =
      ((CongruenceSubgroup.Gamma1 N₂).withCenter.index : ℝ)⁻¹ *
        (CuspForm.peterssonInnerCosets g g).re := by
    have h3pi : (3 / π : ℝ) ≠ 0 := div_ne_zero three_ne_zero Real.pi_pos.ne'
    apply mul_left_cancel₀ h3pi
    calc (3 / π) * (((CongruenceSubgroup.Gamma1 N₁).withCenter.index : ℝ)⁻¹ *
            (CuspForm.peterssonInnerCosets f f).re)
        = 3 / (π * ((CongruenceSubgroup.Gamma1 N₁).withCenter.index : ℝ)) *
            (CuspForm.peterssonInnerCosets f f).re := by ring
      _ = 3 / (π * ((CongruenceSubgroup.Gamma1 N₂).withCenter.index : ℝ)) *
            (CuspForm.peterssonInnerCosets g g).re := hlim_eq
      _ = (3 / π) * (((CongruenceSubgroup.Gamma1 N₂).withCenter.index : ℝ)⁻¹ *
            (CuspForm.peterssonInnerCosets g g).re) := by ring
  apply Complex.ext
  · simpa [Complex.mul_re] using hre_eq
  · simp [Complex.mul_im, CuspForm.peterssonInnerCosets_self_im]

/-- **Equal Fourier coefficient norms at the same level imply equal Petersson norms.** If
`f ∈ S_k(Γ₁(N), χ₁)` and `g ∈ S_k(Γ₁(N), χ₂)` satisfy `‖a_n(f)‖ = ‖a_n(g)‖` for all `n : ℕ`, then
`⟪f, f⟫ = ⟪g, g⟫`. -/
theorem peterssonInnerCosets_self_eq_of_norm_qExpansion_coeff_eq
    {N : ℕ} [NeZero N] {k : ℤ} {χ₁ χ₂ : (ZMod N)ˣ →* ℂˣ}
    {f g : CuspForm ((CongruenceSubgroup.Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ TauCeti.cuspFormCharSpace k χ₁) (hg : g ∈ TauCeti.cuspFormCharSpace k χ₂)
    (hcoeff : ∀ n : ℕ, ‖(qExpansion 1 f).coeff n‖ = ‖(qExpansion 1 g).coeff n‖) :
    CuspForm.peterssonInnerCosets f f = CuspForm.peterssonInnerCosets g g := by
  have h := inv_index_mul_peterssonInnerCosets_self_eq_of_norm_qExpansion_coeff_eq hf hg hcoeff
  have hfi : (CongruenceSubgroup.Gamma1 N).withCenter.FiniteIndex :=
    Subgroup.finiteIndex_of_le (CongruenceSubgroup.Gamma1 N).le_withCenter
  have hne : (((CongruenceSubgroup.Gamma1 N).withCenter.index : ℂ))⁻¹ ≠ 0 :=
    inv_ne_zero (Nat.cast_ne_zero.mpr Subgroup.index_ne_zero)
  exact mul_left_cancel₀ hne h

end CuspForm
