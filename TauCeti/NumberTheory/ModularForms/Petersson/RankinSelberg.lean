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

private abbrev vStrip : Set ℍ := UpperHalfPlane.re ⁻¹' Set.Ico (0 : ℝ) 1

private abbrev G0QuotSL (N : ℕ) := SL(2, ℤ) ⧸ (CongruenceSubgroup.Gamma0 N).withCenter

private abbrev weight {N : ℕ} {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma1 N).map (mapGL ℝ)) k) (τ : ℍ) : ℝ :=
  ‖f τ‖ ^ 2 * τ.im ^ k

private theorem weight_nonneg {N : ℕ} {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma1 N).map (mapGL ℝ)) k) (τ : ℍ) :
    0 ≤ weight f τ :=
  mul_nonneg (sq_nonneg _) (zpow_nonneg τ.im_pos.le k)

private theorem continuous_weight {N : ℕ} {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma1 N).map (mapGL ℝ)) k) : Continuous (weight f) :=
  ((ModularFormClass.continuous f).norm.pow 2).mul
    (UpperHalfPlane.continuous_im.zpow₀ k fun τ ↦ Or.inl τ.im_pos.ne')

private theorem continuous_smul_SL (γ : SL(2, ℤ)) : Continuous fun τ : ℍ ↦ γ • τ := by
  simp only [MulAction.compHom_smul_def]
  exact continuous_const_smul (mapGL ℝ γ)

private theorem continuous_weight_smul {N : ℕ} {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma1 N).map (mapGL ℝ)) k) (γ : SL(2, ℤ)) :
    Continuous fun τ : ℍ ↦ weight f (γ • τ) :=
  (continuous_weight f).comp (continuous_smul_SL γ)

/-! ### The vertical strip `{0 ≤ Re τ < 1}` and Parseval's identity -/

private theorem isFundamentalDomain_re_Ico_zero_one :
    MeasureTheory.IsFundamentalDomain pslTSubgroup vStrip volume := by
  refine MeasureTheory.IsFundamentalDomain.mk''
    (UpperHalfPlane.continuous_re.measurable measurableSet_Ico).nullMeasurableSet
    (ae_of_all _ fun τ ↦ ?_) (fun g hg ↦ ?_)
    fun g ↦ (measurePreserving_smul (g : PSL(2, ℤ)) volume).quasiMeasurePreserving
  · refine ⟨⟨((ModularGroup.T ^ (-⌊τ.re⌋) : SL(2, ℤ)) : PSL(2, ℤ)),
      (mem_pslTSubgroup_mk_iff _).mpr (by simp [ModularGroup.coe_T_zpow])⟩, ?_⟩
    change (((ModularGroup.T ^ (-⌊τ.re⌋) : SL(2, ℤ)) : PSL(2, ℤ)) • τ).re ∈ Set.Ico (0 : ℝ) 1
    rw [UpperHalfPlane.pslMk_smul, ModularGroup.re_T_zpow_smul, Int.cast_neg, ← sub_eq_add_neg]
    exact ⟨Int.fract_nonneg τ.re, Int.fract_lt_one τ.re⟩
  · obtain ⟨γ, hγ⟩ := QuotientGroup.mk_surjective (g : PSL(2, ℤ))
    obtain ⟨n, hn⟩ := ModularGroup.exists_eq_T_zpow_of_c_eq_zero
      ((mem_pslTSubgroup_mk_iff γ).mp (by rw [hγ]; exact g.2))
    have hsmul (τ : ℍ) : (g : PSL(2, ℤ)) • τ = ModularGroup.T ^ n • τ := by
      rw [← hγ, UpperHalfPlane.pslMk_smul, hn τ]
    have hn0 : n ≠ 0 := by
      rintro rfl; exact hg (Subtype.ext (eq_of_smul_eq_smul fun τ : ℍ ↦ by simp [hsmul τ]))
    refine Disjoint.aedisjoint (Set.disjoint_left.mpr ?_)
    rintro _ ⟨τ, hτ, rfl⟩ hw
    change ((g : PSL(2, ℤ)) • τ).re ∈ Set.Ico (0 : ℝ) 1 at hw
    rw [hsmul τ, ModularGroup.re_T_zpow_smul] at hw
    have h1 : (-1 : ℤ) < n := by exact_mod_cast (by linarith [hτ.2, hw.1] : (-1 : ℝ) < n)
    have h2 : n < 1 := by exact_mod_cast (by linarith [hτ.1, hw.2] : (n : ℝ) < 1)
    omega

private theorem measurable_ofComplex : Measurable UpperHalfPlane.ofComplex := by
  classical
  intro s hs
  have hpre : UpperHalfPlane.ofComplex ⁻¹' s = UpperHalfPlane.coe '' s ∪
      if Classical.choice inferInstance ∈ s then {w : ℂ | w.im ≤ 0} else ∅ := by
    ext w; by_cases hw : 0 < w.im
    · simp only [mem_preimage, mem_union, mem_image, UpperHalfPlane.ofComplex_apply_of_im_pos hw]
      have hnm : w ∉ if Classical.choice inferInstance ∈ s then {w : ℂ | w.im ≤ 0} else ∅ := by
        split_ifs <;> simp [not_le.mpr hw]
      exact ⟨fun h ↦ Or.inl ⟨⟨w, hw⟩, h, rfl⟩, fun h ↦ h.elim
        (fun ⟨z, hz, hzw⟩ ↦ (UpperHalfPlane.ext hzw : z = ⟨w, hw⟩) ▸ hz) (absurd · hnm)⟩
    · have hni : w ∉ UpperHalfPlane.coe '' s := fun ⟨z, _, hzw⟩ ↦ hw (hzw ▸ z.im_pos)
      simp only [mem_preimage, mem_union, hni, false_or,
        UpperHalfPlane.ofComplex_apply_of_im_nonpos (not_lt.mp hw)]
      by_cases hc : Classical.choice inferInstance ∈ s <;> simp [hc, not_lt.mp hw]
  rw [hpre]
  exact (UpperHalfPlane.measurableEmbedding_coe.measurableSet_image.mpr hs).union (by
    split_ifs; exacts [(isClosed_le Complex.continuous_im continuous_const).measurableSet, .empty])

private theorem setLIntegral_re_Ico_eq_parseval {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma1 N).map (mapGL ℝ)) k) (s : ℝ) :
    ∫⁻ τ in vStrip, ENNReal.ofReal (weight f τ * τ.im ^ s) =
      ∫⁻ y in Set.Ioi (0 : ℝ), ENNReal.ofReal
        ((∑' n : ℕ, ‖(qExpansion 1 f).coeff n‖ ^ 2 * Real.exp (-(4 * π * n * y))) *
          (y ^ k * y ^ s * (y ^ 2)⁻¹)) := by
  let G₀ : ℍ → ℝ≥0∞ := fun z ↦ ENNReal.ofReal (weight f z * z.im ^ s * (z.im ^ 2)⁻¹)
  let G : ℂ → ℝ≥0∞ := G₀ ∘ UpperHalfPlane.ofComplex
  have hF_cont : Continuous fun τ : ℍ ↦ weight f τ * τ.im ^ s := (continuous_weight f).mul
    (UpperHalfPlane.continuous_im.rpow continuous_const fun τ ↦ Or.inl τ.im_pos.ne')
  have hG_meas : Measurable G := (ENNReal.measurable_ofReal.comp
    (hF_cont.measurable.mul (UpperHalfPlane.continuous_im.measurable.pow_const 2).inv)).comp
    measurable_ofComplex
  have hd_meas : Measurable fun z : ℍ ↦
      (((1 / NNReal.mk z.im z.im_pos.le : ℝ≥0) ^ 2 : ℝ≥0) : ℝ≥0∞) := by fun_prop
  have hF_meas : Measurable fun τ : ℍ ↦ ENNReal.ofReal (weight f τ * τ.im ^ s) :=
    ENNReal.measurable_ofReal.comp hF_cont.measurable
  have hstep1 : ∫⁻ τ in vStrip, ENNReal.ofReal (weight f τ * τ.im ^ s) =
      ∫⁻ y in Set.Ioi (0 : ℝ), ∫⁻ x in Set.Ico (0 : ℝ) 1,
        G (Complex.measurableEquivRealProd.symm (x, y)) := by
    have hmp : MeasurePreserving UpperHalfPlane.coe (volume.comap UpperHalfPlane.coe)
        (volume.restrict (.range UpperHalfPlane.coe)) :=
      ⟨UpperHalfPlane.measurable_coe, by rw [UpperHalfPlane.measurableEmbedding_coe.map_comap]⟩
    rw [UpperHalfPlane.volume_def, setLIntegral_withDensity_eq_setLIntegral_mul _ hd_meas hF_meas
      (UpperHalfPlane.continuous_re.measurable measurableSet_Ico)]
    simp_rw [Pi.mul_apply, show ∀ τ : ℍ,
        (((1 / NNReal.mk τ.im τ.im_pos.le : ℝ≥0) ^ 2 : ℝ≥0) : ℝ≥0∞) *
          ENNReal.ofReal (weight f τ * τ.im ^ s) = G τ from fun τ ↦ by
      have hnn1 : 0 ≤ (τ.im ^ 2)⁻¹ := by positivity
      rw [show (((1 / NNReal.mk τ.im τ.im_pos.le : ℝ≥0) ^ 2 : ℝ≥0) : ℝ≥0∞) =
          ENNReal.ofReal ((τ.im ^ 2)⁻¹) by
            rw [ENNReal.ofReal_eq_coe_nnreal hnn1]; congr 1; ext; simp [one_div, inv_pow],
        ← ENNReal.ofReal_mul hnn1]
      simp only [G, G₀, Function.comp_apply, UpperHalfPlane.ofComplex_apply]; congr 1; ring]
    rw [hmp.setLIntegral_comp_emb UpperHalfPlane.measurableEmbedding_coe G vStrip,
      Measure.restrict_restrict' UpperHalfPlane.measurableEmbedding_coe.measurableSet_range,
      Set.inter_eq_self_of_subset_left (Set.image_subset_range _ _),
      show UpperHalfPlane.coe '' vStrip =
          Complex.measurableEquivRealProd ⁻¹' (Set.Ico (0 : ℝ) 1 ×ˢ Set.Ioi (0 : ℝ)) by
        ext w; exact ⟨fun ⟨τ, hτ, h⟩ ↦ h ▸ ⟨hτ, τ.im_pos⟩, fun ⟨hre, him⟩ ↦ ⟨⟨w, him⟩, hre, rfl⟩⟩]
    have hcomp := Complex.volume_preserving_equiv_real_prod.setLIntegral_comp_preimage_emb
      Complex.measurableEquivRealProd.measurableEmbedding
      (fun p : ℝ × ℝ ↦ G (Complex.measurableEquivRealProd.symm p))
      (Set.Ico (0 : ℝ) 1 ×ˢ Set.Ioi (0 : ℝ))
    simp only [MeasurableEquiv.symm_apply_apply] at hcomp
    rw [hcomp, Measure.volume_eq_prod]
    exact setLIntegral_prod_symm _
      (hG_meas.comp Complex.measurableEquivRealProd.symm.measurable).aemeasurable
  rw [hstep1]
  refine setLIntegral_congr_fun measurableSet_Ioi fun y hy ↦ ?_
  have hy' : 0 < y := Set.mem_Ioi.mp hy
  let pt (x : ℝ) : ℍ := ⟨(x : ℂ) + (y : ℂ) * UpperHalfPlane.I, by simpa using hy'⟩
  simp_rw [show ∀ x : ℝ, G (Complex.measurableEquivRealProd.symm (x, y)) =
      ENNReal.ofReal (‖f (pt x)‖ ^ 2) * ENNReal.ofReal (y ^ k * y ^ s * (y ^ 2)⁻¹) from fun x ↦ by
    have hxy : Complex.measurableEquivRealProd.symm (x, y) = (pt x : ℂ) := by
      rw [Complex.measurableEquivRealProd_symm_apply]; apply Complex.ext <;> simp [pt]
    rw [← ENNReal.ofReal_mul (sq_nonneg _)]
    change G₀ (UpperHalfPlane.ofComplex (Complex.measurableEquivRealProd.symm (x, y))) = _
    rw [hxy, UpperHalfPlane.ofComplex_apply]
    simp only [G₀, weight, show (pt x).im = y by simp [pt]]; congr 1; ring]
  have hcont_line : Continuous fun x : ℝ ↦ f (pt x) := (ModularFormClass.continuous f).comp
    (continuous_induced_rng.mpr (Complex.continuous_ofReal.add continuous_const))
  have hmeas_line : Measurable fun x : ℝ ↦ ENNReal.ofReal (‖f (pt x)‖ ^ 2) :=
    ENNReal.measurable_ofReal.comp (hcont_line.measurable.norm.pow_const 2)
  rw [lintegral_mul_const _ hmeas_line]
  have hparseval := UpperHalfPlane.hasSum_norm_sq_qExpansion_coeff_mul_exp (f := ⇑f) (h := 1)
    one_pos (SlashInvariantFormClass.periodic_comp_ofComplex f
      (TauCeti.one_mem_strictPeriods_Gamma1_map N))
    (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f) hy'
  simp only [inv_one, one_mul, div_one] at hparseval
  have hint : IntegrableOn (fun x : ℝ ↦ ‖f (pt x)‖ ^ 2) (Set.Ioc (0 : ℝ) 1) volume :=
    (hcont_line.norm.pow 2).integrableOn_Ioc
  rw [Measure.restrict_congr_set Ico_ae_eq_Ioc,
    ← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ ↦ sq_nonneg _),
    ← intervalIntegral.integral_of_le zero_le_one, ← hparseval.tsum_eq,
    ← ENNReal.ofReal_mul (tsum_nonneg fun n ↦ by positivity)]

/-! ### `Γ₀(N)`-invariance and Rankin–Selberg unfolding -/

private theorem weight_smul_of_mem_cuspFormCharSpace {N : ℕ} {k : ℤ}
    {χ : (ZMod N)ˣ →* ℂˣ} {f : CuspForm ((CongruenceSubgroup.Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ TauCeti.cuspFormCharSpace k χ) {γ : SL(2, ℤ)}
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) (τ : ℍ) :
    weight f (γ • τ) = weight f τ := by
  have hslash : ⇑f ∣[k] γ = (↑(χ ((Gamma0Map N).toHomUnits ⟨γ, hγ⟩)) : ℂ) • ⇑f :=
    (TauCeti.mem_cuspFormCharSpace_iff_nebentypus k χ f).mp hf ⟨γ, hγ⟩
  have hpet := UpperHalfPlane.petersson_slash_SL k ⇑f ⇑f γ τ
  rw [hslash, petersson_self_eq_ofReal, petersson_self_eq_ofReal] at hpet
  have hc_norm : ‖(↑(χ ((Gamma0Map N).toHomUnits ⟨γ, hγ⟩)) : ℂ)‖ = 1 :=
    (((Units.coeHom ℂ).comp χ).isOfFinOrder
      (isOfFinOrder_of_finite ((Gamma0Map N).toHomUnits ⟨γ, hγ⟩))).norm_eq_one
  simpa only [Pi.smul_apply, smul_eq_mul, Complex.normSq_eq_norm_sq, norm_mul, hc_norm,
    one_mul] using Complex.ofReal_injective hpet.symm

private theorem weight_psl_smul_of_mem_cuspFormCharSpace {N : ℕ} {k : ℤ}
    {χ : (ZMod N)ˣ →* ℂˣ} {f : CuspForm ((CongruenceSubgroup.Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ TauCeti.cuspFormCharSpace k χ)
    (g : TauCeti.CongruenceSubgroup.Gamma0Projective N) (τ : ℍ) :
    weight f ((g : PSL(2, ℤ)) • τ) = weight f τ := by
  obtain ⟨γ, hγ_eq, hγ⟩ := (TauCeti.CongruenceSubgroup.mem_Gamma0Projective_iff N g).mp g.2
  rw [← hγ_eq]
  change weight f (((γ : SL(2, ℤ)) : PSL(2, ℤ)) • τ) = weight f τ
  rw [UpperHalfPlane.pslMk_smul]
  exact weight_smul_of_mem_cuspFormCharSpace hf hγ τ

private theorem setLIntegral_re_Ico_eq_sum_fd {N : ℕ} [NeZero N] {k : ℤ}
    {χ : (ZMod N)ˣ →* ℂˣ} {f : CuspForm ((CongruenceSubgroup.Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ TauCeti.cuspFormCharSpace k χ) {s : ℝ} (hs : 1 < s) :
    ∫⁻ τ in vStrip, ENNReal.ofReal (weight f τ * τ.im ^ s) =
      ∑ r : G0QuotSL N, ∫⁻ τ in fd,
        ENNReal.ofReal (weight f (r.out⁻¹ • τ) * realAnalyticEisenstein N (r.out⁻¹ • τ) s) := by
  let Γ₀P := TauCeti.CongruenceSubgroup.Gamma0Projective N
  let H := pslTSubgroup.subgroupOf Γ₀P
  let D₀ : Set ℍ := ⋃ r : G0QuotSL N, r.out⁻¹ • (fdo : Set ℍ)
  have hD₀ : MeasureTheory.IsFundamentalDomain Γ₀P D₀ volume := by
    rw [show Γ₀P = (CongruenceSubgroup.Gamma0 N).map
      (QuotientGroup.mk' (Subgroup.center SL(2, ℤ))) from
      TauCeti.CongruenceSubgroup.Gamma0Projective_def N]
    exact ModularGroup.isFundamentalDomain_iUnion_out_inv_smul_fdo_withCenter
      (CongruenceSubgroup.Gamma0 N)
  have : MeasurableConstSMul Γ₀P ℍ := ⟨fun g ↦ measurable_const_smul (g : PSL(2, ℤ))⟩
  have : SMulInvariantMeasure Γ₀P ℍ volume :=
    ⟨fun g ↦ SMulInvariantMeasure.measure_preimage_smul (g : PSL(2, ℤ))⟩
  have hU : MeasureTheory.IsFundamentalDomain pslTSubgroup
      (⋃ q : Γ₀P ⧸ H, ((q.out : Γ₀P))⁻¹ • D₀) volume := by
    have h := (hD₀.subgroup_iUnion_out_inv_smul H).of_subgroupOf
    rwa [inf_eq_left.mpr (pslTSubgroup_le_Gamma0Projective N)] at h
  have hD₀_open : IsOpen D₀ := isOpen_iUnion fun r ↦
    (Homeomorph.smul (mapGL ℝ r.out⁻¹)).isOpenMap _ isOpen_fdo
  rw [isFundamentalDomain_re_Ico_zero_one.setLIntegral_eq hU _ fun g τ ↦ by
      change ENNReal.ofReal (weight f ((g : PSL(2, ℤ)) • τ) * ((g : PSL(2, ℤ)) • τ).im ^ s) = _
      rw [weight_psl_smul_of_mem_cuspFormCharSpace hf ⟨g, pslTSubgroup_le_Gamma0Projective N g.2⟩ τ,
        im_smul_eq_of_mem_pslTSubgroup g.2 τ]]
  have hmeas_q : ∀ q : Γ₀P ⧸ H, NullMeasurableSet (((q.out : Γ₀P))⁻¹ • D₀) volume := fun q ↦
    hD₀.nullMeasurableSet_smul ((q.out : Γ₀P)⁻¹)
  have hdisj_q : Pairwise fun q₁ q₂ : Γ₀P ⧸ H ↦
      AEDisjoint volume (((q₁.out : Γ₀P))⁻¹ • D₀) (((q₂.out : Γ₀P))⁻¹ • D₀) := fun q₁ q₂ hne ↦
    hD₀.aedisjoint (inv_injective.ne (Quotient.out_injective.ne hne))
  rw [lintegral_iUnion₀ hmeas_q hdisj_q]
  simp_rw [show ∀ q : Γ₀P ⧸ H,
      ∫⁻ τ in ((q.out : Γ₀P))⁻¹ • D₀, ENNReal.ofReal (weight f τ * τ.im ^ s) =
        ∫⁻ τ in D₀, ENNReal.ofReal (weight f τ * realAnalyticEisensteinSummand N τ s q) from
    fun q ↦ by
      rw [show ((q.out : Γ₀P))⁻¹ • D₀ = ((((q.out : Γ₀P) : PSL(2, ℤ))⁻¹) • ·) '' D₀ by
            ext x; simp [Set.mem_smul_set, Subgroup.smul_def],
        ← (measurePreserving_smul ((q.out : Γ₀P) : PSL(2, ℤ))⁻¹ volume).setLIntegral_comp_emb
          (measurableEmbedding_const_smul (((q.out : Γ₀P) : PSL(2, ℤ))⁻¹))]
      refine setLIntegral_congr_fun hD₀_open.measurableSet fun τ _ ↦ ?_
      have hΦ_q : weight f (((q.out : Γ₀P) : PSL(2, ℤ))⁻¹ • τ) = weight f τ :=
        weight_psl_smul_of_mem_cuspFormCharSpace hf (q.out : Γ₀P)⁻¹ τ
      rw [hΦ_q, realAnalyticEisensteinSummand_eq_out]]
  rw [← lintegral_tsum (f := fun q τ ↦
    ENNReal.ofReal (weight f τ * realAnalyticEisensteinSummand N τ s q)) fun q ↦
      (ENNReal.measurable_ofReal.comp ((continuous_weight f).measurable.mul
        (continuous_realAnalyticEisensteinSummand N s q).measurable)).aemeasurable]
  rw [show ∫⁻ τ in D₀, ∑' q, ENNReal.ofReal (weight f τ * realAnalyticEisensteinSummand N τ s q) =
      ∫⁻ τ in D₀, ENNReal.ofReal (weight f τ * realAnalyticEisenstein N τ s) from
    setLIntegral_congr_fun hD₀_open.measurableSet fun τ _ ↦ by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun q ↦ mul_nonneg (weight_nonneg f τ) (by
        rw [realAnalyticEisensteinSummand_eq_out]; exact rpow_nonneg (im_pos _).le s))
        ((summable_realAnalyticEisensteinSummand N τ hs).mul_left _),
        tsum_mul_left, ← realAnalyticEisenstein_def]]
  have hmeas_r : ∀ r : G0QuotSL N, MeasurableSet (r.out⁻¹ • (fdo : Set ℍ)) := fun r ↦
    ((Homeomorph.smul (mapGL ℝ r.out⁻¹)).isOpenMap _ isOpen_fdo).measurableSet
  have hdisj_r : Pairwise fun r₁ r₂ : G0QuotSL N ↦
      Disjoint (r₁.out⁻¹ • (fdo : Set ℍ)) (r₂.out⁻¹ • (fdo : Set ℍ)) := fun r₁ r₂ hne ↦ by
    refine ModularGroup.disjoint_smul_fdo (fun heq ↦ hne ?_) (fun heq ↦ hne ?_)
    · exact Quotient.out_injective (mul_inv_eq_one.mp (by simpa [inv_inv] using heq))
    · have h1 : r₁.out * r₂.out⁻¹ = -1 := by simpa [inv_inv] using heq
      have h2 : r₁.out = -r₂.out := by simpa [mul_assoc] using congrArg (· * r₂.out) h1
      rw [← QuotientGroup.out_eq' r₁, ← QuotientGroup.out_eq' r₂, QuotientGroup.eq,
        show r₁.out⁻¹ * r₂.out = -1 by rw [h2]; simp, Subgroup.mem_withCenter_iff]
      exact ⟨1, one_mem _, -1, Subgroup.mem_center_iff.mpr fun _ ↦ by simp, one_mul _⟩
  rw [lintegral_iUnion hmeas_r hdisj_r, tsum_fintype]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  rw [show r.out⁻¹ • (fdo : Set ℍ) = ((mapGL ℝ r.out⁻¹) • ·) '' (fdo : Set ℍ) from rfl,
    ← (measurePreserving_smul (mapGL ℝ r.out⁻¹) volume).setLIntegral_comp_emb
      (measurableEmbedding_const_smul (mapGL ℝ r.out⁻¹)),
    Measure.restrict_congr_set ModularGroup.fd_ae_eq_fdo.symm]
  rfl

/-! ### Uniform domination on `𝒟` and passage to `s → 1⁺` -/

private theorem measurable_weight_mul_eisenstein {N : ℕ} {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma1 N).map (mapGL ℝ)) k) (γ : SL(2, ℤ)) (s : ℝ) :
    Measurable fun τ : ℍ ↦ weight f (γ • τ) * realAnalyticEisenstein N (γ • τ) s :=
  (continuous_weight_smul f γ).measurable.mul
    ((measurable_realAnalyticEisenstein N s).comp (continuous_smul_SL γ).measurable)

private theorem exists_fd_bound_eisenstein {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma1 N).map (mapGL ℝ)) k) (γ : SL(2, ℤ)) :
    ∃ M : ℝ, ∀ {s : ℝ}, 1 < s → s ≤ 2 → ∀ τ ∈ fd,
      (s - 1) * (weight f (γ • τ) * realAnalyticEisenstein N (γ • τ) s) ≤ M := by
  let Γ : Subgroup (GL (Fin 2) ℝ) := (CongruenceSubgroup.Gamma1 N).map (mapGL ℝ)
  have : ((ConjAct.toConjAct (mapGL ℝ γ)⁻¹) • Γ).IsArithmetic := by
    have h := Subgroup.IsArithmetic.conj Γ (mapGL ℚ γ)⁻¹
    rwa [show Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) ((mapGL ℚ γ)⁻¹) = (mapGL ℝ γ)⁻¹ by
      rw [map_inv, show Rat.castHom ℝ = algebraMap ℚ ℝ from rfl, map_mapGL]] at h
  let fγ := CuspForm.translate f (mapGL ℝ γ)
  obtain ⟨a, ha, hexp⟩ := (CuspFormClass.zero_at_infty fγ).petersson_exp_decay_left k
    ((ConjAct.toConjAct (mapGL ℝ γ)⁻¹) • Γ) fγ
  have hpet_eq (τ : ℍ) : ‖petersson k ⇑fγ ⇑fγ τ‖ = weight f (γ • τ) := by
    have h1 : petersson k ⇑fγ ⇑fγ τ = petersson k ⇑f ⇑f (γ • τ) := by
      rw [show (⇑fγ : ℍ → ℂ) = ⇑f ∣[k] γ from CuspForm.coe_translate f (mapGL ℝ γ)]
      exact UpperHalfPlane.petersson_slash_SL k ⇑f ⇑f γ τ
    rw [h1, petersson_self_eq_ofReal, Complex.norm_real, Real.norm_of_nonneg
      (mul_nonneg (Complex.normSq_nonneg _) (zpow_nonneg (UpperHalfPlane.im_pos _).le k)),
      Complex.normSq_eq_norm_sq]
  have hpoly_o : (fun y : ℝ ↦ Real.exp (-a * y) * (6 * π + 36 + 4 * y ^ 2)) =O[atTop]
      fun _ : ℝ ↦ (1 : ℝ) :=
    (squeeze_zero_norm' (by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
      rw [Real.norm_of_nonneg (by positivity), neg_mul, Real.exp_neg, inv_mul_eq_div,
        ← mul_div_assoc]
      exact div_le_div_of_nonneg_right
        (by have hy2 : 1 ≤ y ^ 2 := (by nlinarith); nlinarith [Real.pi_pos]) (Real.exp_pos _).le)
      (((isLittleO_pow_exp_pos_mul_atTop 2 ha).tendsto_div_nhds_zero.const_mul
        (6 * π + 40)).trans (by simp))).isBigO_one ℝ
  have hbigO : (fun τ : ℍ ↦ weight f (γ • τ) * (6 * π + 36 + 4 * τ.im ^ 2))
      =O[atImInfty] fun τ : ℍ ↦ τ.im ^ (0 : ℝ) := by
    have h1 : (fun τ : ℍ ↦ weight f (γ • τ)) =O[atImInfty] fun τ : ℍ ↦ Real.exp (-a * τ.im) := by
      simpa only [hpet_eq] using hexp.norm_left
    have h2 : (fun τ : ℍ ↦ weight f (γ • τ) * (6 * π + 36 + 4 * τ.im ^ 2))
        =O[atImInfty] fun τ : ℍ ↦ Real.exp (-a * τ.im) * (6 * π + 36 + 4 * τ.im ^ 2) :=
      h1.mul (Asymptotics.isBigO_refl _ _)
    have h3 : (fun τ : ℍ ↦ Real.exp (-a * τ.im) * (6 * π + 36 + 4 * τ.im ^ 2))
        =O[atImInfty] fun _ : ℍ ↦ (1 : ℝ) := hpoly_o.comp_tendsto tendsto_comap
    simpa only [Real.rpow_zero] using h2.trans h3
  have hcont : Continuous fun τ : ℍ ↦ weight f (γ • τ) * (6 * π + 36 + 4 * τ.im ^ 2) :=
    (continuous_weight_smul f γ).mul (by fun_prop)
  obtain ⟨F, hF⟩ := ModularGroup.exists_bound_fundamental_domain_of_isBigO hcont hbigO
  refine ⟨max F 0, fun {s} hs1 hs2 τ hτ ↦ ?_⟩
  have hbound : weight f (γ • τ) * (6 * π + 36 + 4 * τ.im ^ 2) ≤ max F 0 := by
    have h := hF τ hτ
    rw [Real.rpow_zero, mul_one,
      Real.norm_of_nonneg (mul_nonneg (weight_nonneg f _) (by positivity))] at h
    exact h.trans (le_max_left _ _)
  have him : (1 / 2 : ℝ) ≤ τ.im := by
    have := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hτ
    nlinarith [UpperHalfPlane.im_pos τ]
  have heis : (s - 1) * realAnalyticEisenstein N (γ • τ) s ≤ 6 * π + 36 + 4 * τ.im ^ 2 :=
    (mul_le_mul_of_nonneg_left ((realAnalyticEisenstein_le_one N (γ • τ) hs1).trans
      ((realAnalyticEisenstein_smul 1 (by simp) τ s).le.trans
        (realAnalyticEisenstein_one_le_realAnalyticEpstein τ hs1))) (by linarith)).trans
      (sub_one_mul_realAnalyticEpstein_le τ him hs1 hs2)
  calc (s - 1) * (weight f (γ • τ) * realAnalyticEisenstein N (γ • τ) s)
      = weight f (γ • τ) * ((s - 1) * realAnalyticEisenstein N (γ • τ) s) := by ring
    _ ≤ weight f (γ • τ) * (6 * π + 36 + 4 * τ.im ^ 2) :=
        mul_le_mul_of_nonneg_left heis (weight_nonneg f _)
    _ ≤ max F 0 := hbound

private theorem integrableOn_fd_mul_realAnalyticEisenstein {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma1 N).map (mapGL ℝ)) k) (γ : SL(2, ℤ))
    {s : ℝ} (hs1 : 1 < s) (hs2 : s ≤ 2) :
    IntegrableOn (fun τ : ℍ ↦ weight f (γ • τ) * realAnalyticEisenstein N (γ • τ) s) fd volume := by
  obtain ⟨M, hM⟩ := exists_fd_bound_eisenstein f γ
  refine IntegrableOn.of_bound ModularGroup.volume_fd_lt_top
    (measurable_weight_mul_eisenstein f γ s).aestronglyMeasurable.restrict (M / (s - 1)) ?_
  filter_upwards [ae_restrict_mem isClosed_fd.measurableSet] with τ hτ
  rw [Real.norm_of_nonneg (mul_nonneg (weight_nonneg f _) (realAnalyticEisenstein_nonneg N _ s)),
    le_div_iff₀ (sub_pos.mpr hs1), mul_comm]
  exact hM hs1 hs2 τ hτ

private theorem tendsto_sub_one_mul_setIntegral_fd {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((CongruenceSubgroup.Gamma1 N).map (mapGL ℝ)) k) (γ : SL(2, ℤ)) :
    Tendsto
      (fun s : ℝ ↦ (s - 1) * ∫ τ in fd, weight f (γ • τ) * realAnalyticEisenstein N (γ • τ) s)
      (𝓝[>] 1)
      (𝓝 (3 / (π * ((CongruenceSubgroup.Gamma0 N).index : ℝ)) * ∫ τ in fd, weight f (γ • τ))) := by
  obtain ⟨M, hM⟩ := exists_fd_bound_eisenstein f γ
  have : IsFiniteMeasure (volume.restrict (fd : Set ℍ)) :=
    ⟨by simpa using ModularGroup.volume_fd_lt_top⟩
  have hdct : Tendsto
      (fun s : ℝ ↦ ∫ τ in fd, (s - 1) * (weight f (γ • τ) * realAnalyticEisenstein N (γ • τ) s))
      (𝓝[>] 1)
      (𝓝 (∫ τ in fd, weight f (γ • τ) *
        (3 / (π * ((CongruenceSubgroup.Gamma0 N).index : ℝ))))) :=
    tendsto_integral_filter_of_dominated_convergence (fun _ ↦ M)
      (by filter_upwards [Ioc_mem_nhdsGT one_lt_two] with s _
          exact ((measurable_weight_mul_eisenstein f γ s).const_mul _).aestronglyMeasurable)
      (by filter_upwards [Ioc_mem_nhdsGT one_lt_two] with s ⟨hs1, hs2⟩
          filter_upwards [ae_restrict_mem isClosed_fd.measurableSet] with τ hτ
          rw [Real.norm_of_nonneg (mul_nonneg (sub_nonneg.mpr hs1.le)
            (mul_nonneg (weight_nonneg f _) (realAnalyticEisenstein_nonneg N _ s)))]
          exact hM hs1 hs2 τ hτ)
      (integrable_const M)
      (ae_of_all _ fun τ ↦ by
        rw [show (fun s : ℝ ↦ (s - 1) * (weight f (γ • τ) * realAnalyticEisenstein N (γ • τ) s)) =
            fun s : ℝ ↦ weight f (γ • τ) * ((s - 1) * realAnalyticEisenstein N (γ • τ) s) by
          ext s; ring]
        exact (tendsto_sub_one_mul_realAnalyticEisenstein N (γ • τ)).const_mul _)
  simp only [integral_const_mul, integral_mul_const] at hdct
  rwa [mul_comm] at hdct

private theorem integrableOn_re_Ico_and_eq_sum_fd {N : ℕ} [NeZero N] {k : ℤ}
    {χ : (ZMod N)ˣ →* ℂˣ} {f : CuspForm ((CongruenceSubgroup.Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ TauCeti.cuspFormCharSpace k χ) {s : ℝ} (hs1 : 1 < s) (hs2 : s ≤ 2) :
    IntegrableOn (fun τ : ℍ ↦ weight f τ * τ.im ^ s) vStrip volume ∧
      (∫ τ in vStrip, weight f τ * τ.im ^ s) =
        ∑ r : G0QuotSL N,
          ∫ τ in fd, weight f (r.out⁻¹ • τ) * realAnalyticEisenstein N (r.out⁻¹ • τ) s := by
  have hsum_eq : ∫⁻ τ in vStrip, ENNReal.ofReal (weight f τ * τ.im ^ s) =
      ENNReal.ofReal (∑ r : G0QuotSL N,
        ∫ τ in fd, weight f (r.out⁻¹ • τ) * realAnalyticEisenstein N (r.out⁻¹ • τ) s) := by
    rw [setLIntegral_re_Ico_eq_sum_fd hf hs1]
    simp_rw [← fun r : G0QuotSL N ↦ ofReal_integral_eq_lintegral_ofReal
      (integrableOn_fd_mul_realAnalyticEisenstein f r.out⁻¹ hs1 hs2)
      (ae_of_all _ fun _ ↦ mul_nonneg (weight_nonneg f _) (realAnalyticEisenstein_nonneg N _ s))]
    rw [← ENNReal.ofReal_sum_of_nonneg fun r _ ↦ setIntegral_nonneg isClosed_fd.measurableSet
      fun _ _ ↦ mul_nonneg (weight_nonneg f _) (realAnalyticEisenstein_nonneg N _ s)]
  have hnn (τ : ℍ) : 0 ≤ weight f τ * τ.im ^ s :=
    mul_nonneg (weight_nonneg f τ) (rpow_nonneg τ.im_pos.le s)
  have hstrip_int : IntegrableOn (fun τ : ℍ ↦ weight f τ * τ.im ^ s) vStrip volume :=
    ⟨((continuous_weight f).mul (UpperHalfPlane.continuous_im.rpow continuous_const
      fun τ ↦ Or.inl τ.im_pos.ne')).aestronglyMeasurable, by
      rw [HasFiniteIntegral, lintegral_congr fun τ ↦ Real.eNorm_eq_ofReal (hnn τ), hsum_eq]
      exact ENNReal.ofReal_lt_top⟩
  refine ⟨hstrip_int, (ENNReal.ofReal_eq_ofReal_iff
    (setIntegral_nonneg (UpperHalfPlane.continuous_re.measurable measurableSet_Ico) fun τ _ ↦ hnn τ)
    (Finset.sum_nonneg fun _ _ ↦ setIntegral_nonneg isClosed_fd.measurableSet fun _ _ ↦
      mul_nonneg (weight_nonneg f _) (realAnalyticEisenstein_nonneg N _ s))).mp ?_⟩
  rw [ofReal_integral_eq_lintegral_ofReal hstrip_int (ae_of_all _ hnn), hsum_eq]

/-! ### Index bridge from `Γ₀(N)` cosets to `peterssonInnerCosets` -/

private theorem inv_index_Gamma0_mul_sum_fd_eq_inv_index_Gamma1 {N : ℕ} [NeZero N] {k : ℤ}
    {χ : (ZMod N)ˣ →* ℂˣ} {f : CuspForm ((CongruenceSubgroup.Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ TauCeti.cuspFormCharSpace k χ) :
    ((CongruenceSubgroup.Gamma0 N).index : ℝ)⁻¹ *
        ∑ r : G0QuotSL N, ∫ τ in fd, weight f (r.out⁻¹ • τ) =
      ((CongruenceSubgroup.Gamma1 N).withCenter.index : ℝ)⁻¹ *
        (CuspForm.peterssonInnerCosets f f).re := by
  let H₁ := (CongruenceSubgroup.Gamma1 N).withCenter
  let H₀ := (CongruenceSubgroup.Gamma0 N).withCenter
  have hH₀_eq : H₀ = CongruenceSubgroup.Gamma0 N :=
    Subgroup.withCenter_eq_self_iff.mpr (TauCeti.CongruenceSubgroup.center_le_Gamma0 N)
  have hle : H₁ ≤ H₀ := hH₀_eq ▸
    CongruenceSubgroup.withCenter_le_Gamma0 (CongruenceSubgroup.Gamma1_in_Gamma0 N)
  let : Fintype (H₀ ⧸ H₁.subgroupOf H₀) := Fintype.ofFinite _
  have hre : (CuspForm.peterssonInnerCosets f f).re =
      ∑ q : SL(2, ℤ) ⧸ H₁, ∫ τ in fd, weight f (q.out⁻¹ • τ) := by
    rw [CuspForm.peterssonInnerCosets_def, Complex.re_sum]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    rw [UpperHalfPlane.peterssonInner_self_eq_ofReal, Complex.ofReal_re]
    refine setIntegral_congr_fun isClosed_fd.measurableSet fun τ _ ↦ ?_
    have h := UpperHalfPlane.petersson_slash_SL k ⇑f ⇑f q.out⁻¹ τ
    rw [UpperHalfPlane.petersson_self_eq_ofReal, UpperHalfPlane.petersson_self_eq_ofReal] at h
    simpa only [Complex.normSq_eq_norm_sq] using Complex.ofReal_injective h
  have hkey (r : SL(2, ℤ) ⧸ H₀) (i : H₀ ⧸ H₁.subgroupOf H₀) :
      (∫ τ in fd, weight f (((Subgroup.quotientEquivProdOfLE hle).symm (r, i)).out⁻¹ • τ)) =
      ∫ τ in fd, weight f (r.out⁻¹ • τ) := by
    induction i using QuotientGroup.induction_on with
    | H γ =>
      let q : SL(2, ℤ) ⧸ H₁ := QuotientGroup.mk (r.out * (γ : SL(2, ℤ)))
      change (∫ τ in fd, weight f (q.out⁻¹ • τ)) = _
      have hrel : (r.out * (γ : SL(2, ℤ)))⁻¹ * q.out ∈ H₁ :=
        QuotientGroup.eq.mp (QuotientGroup.out_eq' q).symm
      have hmem0 : q.out⁻¹ * r.out ∈ CongruenceSubgroup.Gamma0 N := by
        have h1 : q.out⁻¹ * (r.out * (γ : SL(2, ℤ))) ∈ H₀ :=
          hle (by simpa [mul_inv_rev, mul_assoc] using H₁.inv_mem hrel)
        exact hH₀_eq.le (by simpa [mul_assoc] using H₀.mul_mem h1 (H₀.inv_mem γ.2))
      refine setIntegral_congr_fun isClosed_fd.measurableSet fun τ _ ↦ ?_
      rw [show q.out⁻¹ • τ = (q.out⁻¹ * r.out) • (r.out⁻¹ • τ) by
        rw [← mul_smul, mul_assoc, mul_inv_cancel, mul_one]]
      exact weight_smul_of_mem_cuspFormCharSpace hf hmem0 _
  have hprod_sum : (CuspForm.peterssonInnerCosets f f).re =
      (H₁.relIndex H₀ : ℝ) * ∑ r : SL(2, ℤ) ⧸ H₀, ∫ τ in fd, weight f (r.out⁻¹ • τ) := by
    rw [hre, ← (Subgroup.quotientEquivProdOfLE hle).symm.sum_comp, Fintype.sum_prod_type]
    simp only [hkey, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]
    rw [Subgroup.relIndex, Subgroup.index_eq_card, Nat.card_eq_fintype_card]
  have hidx_mul : (H₁.relIndex H₀ : ℝ) * ((CongruenceSubgroup.Gamma0 N).index : ℝ) =
      (H₁.index : ℝ) := by
    exact_mod_cast (hH₀_eq ▸ Subgroup.relIndex_mul_index hle :
      H₁.relIndex H₀ * (CongruenceSubgroup.Gamma0 N).index = H₁.index)
  have hrel_ne : (H₁.relIndex H₀ : ℝ) ≠ 0 := by
    have : H₁.FiniteIndex := Subgroup.finiteIndex_of_le (CongruenceSubgroup.Gamma1 N).le_withCenter
    exact fun h0 ↦ Subgroup.index_ne_zero (by
      have h0' : H₁.relIndex H₀ = 0 := by exact_mod_cast h0
      simpa [h0'] using (Subgroup.relIndex_mul_index hle).symm)
  rw [hprod_sum, ← hidx_mul, mul_inv_rev]; field_simp [hrel_ne]; rfl

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
  have hsum := tendsto_finsetSum (Finset.univ : Finset (G0QuotSL N))
    fun r _ ↦ tendsto_sub_one_mul_setIntegral_fd f r.out⁻¹
  rw [show (∑ r : G0QuotSL N, 3 / (π * ((CongruenceSubgroup.Gamma0 N).index : ℝ)) *
        ∫ τ in fd, weight f (r.out⁻¹ • τ)) =
      3 / (π * ((CongruenceSubgroup.Gamma1 N).withCenter.index : ℝ)) *
        (CuspForm.peterssonInnerCosets f f).re by
    rw [← Finset.mul_sum, div_mul_eq_div_div, div_eq_mul_inv (3 / π), mul_assoc,
      inv_index_Gamma0_mul_sum_fd_eq_inv_index_Gamma1 hf]; ring] at hsum
  refine hsum.congr' ?_
  filter_upwards [Ioc_mem_nhdsGT one_lt_two] with s ⟨hs1, hs2⟩
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
  have hev : (fun s : ℝ ↦ (s - 1) * ∫ τ in vStrip, weight f τ * τ.im ^ s) =ᶠ[𝓝[>] 1]
      fun s : ℝ ↦ (s - 1) * ∫ τ in vStrip, weight g τ * τ.im ^ s := by
    filter_upwards [Ioc_mem_nhdsGT one_lt_two] with s ⟨hs1, hs2⟩
    congr 1
    have hnn {M : ℕ} (h : CuspForm ((CongruenceSubgroup.Gamma1 M).map (mapGL ℝ)) k) (τ : ℍ) :
        0 ≤ weight h τ * τ.im ^ s := mul_nonneg (weight_nonneg h τ) (rpow_nonneg τ.im_pos.le s)
    refine (ENNReal.ofReal_eq_ofReal_iff
      (setIntegral_nonneg (UpperHalfPlane.continuous_re.measurable measurableSet_Ico)
        fun τ _ ↦ hnn f τ)
      (setIntegral_nonneg (UpperHalfPlane.continuous_re.measurable measurableSet_Ico)
        fun τ _ ↦ hnn g τ)).mp ?_
    rw [ofReal_integral_eq_lintegral_ofReal (integrableOn_re_Ico_and_eq_sum_fd hf hs1 hs2).1
        (ae_of_all _ (hnn f)),
      ofReal_integral_eq_lintegral_ofReal (integrableOn_re_Ico_and_eq_sum_fd hg hs1 hs2).1
        (ae_of_all _ (hnn g)),
      setLIntegral_re_Ico_eq_parseval f s, setLIntegral_re_Ico_eq_parseval g s]
    simp_rw [hcoeff]
  have hlim_eq := tendsto_nhds_unique
    ((tendsto_sub_one_mul_setIntegral_norm_sq_mul_im hf).congr' hev)
    (tendsto_sub_one_mul_setIntegral_norm_sq_mul_im hg)
  have hre_eq : ((CongruenceSubgroup.Gamma1 N₁).withCenter.index : ℝ)⁻¹ *
        (CuspForm.peterssonInnerCosets f f).re =
      ((CongruenceSubgroup.Gamma1 N₂).withCenter.index : ℝ)⁻¹ *
        (CuspForm.peterssonInnerCosets g g).re :=
    mul_left_cancel₀ (div_ne_zero three_ne_zero Real.pi_pos.ne') (by
      have h1 : (3 / π) * (((CongruenceSubgroup.Gamma1 N₁).withCenter.index : ℝ)⁻¹ *
          (CuspForm.peterssonInnerCosets f f).re) =
        3 / (π * ((CongruenceSubgroup.Gamma1 N₁).withCenter.index : ℝ)) *
          (CuspForm.peterssonInnerCosets f f).re := by ring
      rw [h1, hlim_eq]; ring)
  exact Complex.ext (by simpa [Complex.mul_re] using hre_eq)
    (by simp [Complex.mul_im, CuspForm.peterssonInnerCosets_self_im])

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
  have : (CongruenceSubgroup.Gamma1 N).withCenter.FiniteIndex :=
    Subgroup.finiteIndex_of_le (CongruenceSubgroup.Gamma1 N).le_withCenter
  exact mul_left_cancel₀ (inv_ne_zero (Nat.cast_ne_zero.mpr Subgroup.index_ne_zero)) h

end CuspForm
