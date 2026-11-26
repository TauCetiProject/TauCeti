/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Sobolev.End.Model
public import TauCeti.Analysis.Sobolev.Cylinder.Parametrix
import TauCeti.MeasureTheory.Function.Holder
import TauCeti.MeasureTheory.Function.LpSeminorm.Comp

/-!
# The end contribution to a right parametrix of an operator on the pair of pants

Let `D` be a first-order operator on the pair of pants `S = ℂ ∖ {0, 1}`, realized on
`W^{1,2}_0(S, V)` through an essentially bounded coefficient field `M` on the conformal jets of the
cylindrical weight, such as the linearized Floer operator
`TauCeti.SymplecticForm.floerConformalSobolevOperator` of a pair of pants. The linearized Floer
operator of a pair of pants has finite-dimensional kernel and closed range
(`TauCeti.SymplecticForm.finiteDimensional_ker_floerConformalSobolevOperator_pairOfPants`,
`TauCeti.SymplecticForm.isClosed_range_floerConformalSobolevOperator_pairOfPants`); the finiteness
of its cokernel follows from a right parametrix `P`, an operator with `D P - 1` compact
(`ContinuousLinearMap.cofg_range_of_isCompactOperator_comp_sub_one`). Such a parametrix is spliced
from inverses of model operators on the cylinder. This file constructs what one end contributes:
an inverse of the end model of `D`, transferred to `S` along the end chart with a cutoff living far
out on the end, inverts `D` there up to a compact operator and an operator of small norm. The
splicing of end inverses through cutoffs, with compact cutoff-commutator terms, follows the
parametrix of the two-ended cylinder
(`TauCeti.CylinderSobolev.isFredholm_jetOperator_comp_subtypeL_of_isInvertible`).

* **Splitting off the cutoff.** The jet coefficient of the transfer along the end chart `φ'_q`
  with a cutoff `β` (`TauCeti.Floer.endTransferCoeff`) is `β(φ'_q)` times the jet coefficient with
  the cutoff `1`, plus a term that only reads the value of a jet and involves the derivative of `β`
  (`TauCeti.Floer.endTransferCoeff_apply_eq_smul_add`, in
  `TauCeti.Geometry.Symplectic.Floer.PairOfPants.Sobolev.Transfer`).
* **The abstract end piece.** Let the first-order operator on the cylinder with an essentially
  bounded coefficient field `G` have a right inverse `Q`, and let `M` read along `φ'_q` with the
  cutoff `1` be within `ε` of `G` beyond a height `T₀`. For a cutoff `β` bounded by `B`, vanishing
  below `T₀` and with derivative supported in a compact range of heights, `D` applied to the
  transfer of `Q h` is, through the `L²` isometry `TauCeti.Floer.positiveEndChartLp`,
  `β(φ'_q) h + K h + E h` with `K` compact and `‖E‖ ≤ B ε ‖Q‖`
  (`TauCeti.Floer.exists_isCompactOperator_positiveEndChartLp_symm_jetOperator_endTransfer_ae_eq`).
  Read along the chart, the coefficient field of `D` applied to the transfer splits as `β(φ'_q) G`,
  the cutoff term, which only reads values and vanishes outside a compact range of heights, so is
  compact by Rellich's theorem
  (`TauCeti.CylinderSobolev.isCompactOperator_jetOperator_comp_subtypeL_of_tendsto_zero`), and
  `β(φ'_q)` times the difference with the model, which is at most `B ε`.
* **The linearized operator of a pair of pants.** Far out on an end, the coefficient field of the
  linearized Floer operator read along the end chart is close to the stationary cylinder operator
  at the asymptotic orbit followed by the rotation `r⁻¹ (a + b J_q(t, x(t)))` of the chart
  (`eventually_forall_norm_floerConformalJetCoeff_comp_endTransferCoeff_sub_lt`, in the namespace
  `TauCeti.SymplecticForm`).
  When the stationary operator is invertible, the inverse rotation followed by its inverse is a
  right inverse of this model, and the abstract end piece applies with `ε` as small as desired
  (`exists_forall_exists_isCompactOperator_jetOperator_floerConformalJetCoeff_endTransfer`, in the
  namespace `TauCeti.SymplecticForm`).

The contribution of the compact part of `S`, and the assembly of the three ends and the core into a
right parametrix, are not treated here.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 3.1
  and Appendix B, on real Cauchy–Riemann operators on surfaces with cylindrical ends.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the Fredholm theory of the pair-of-pants operator through its cylindrical
  ends.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2, on parametrices spliced from inverses of the end models.
-/

public section

noncomputable section

open Set Function Filter MeasureTheory Real TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped ENNReal Topology

namespace TauCeti.Floer

open StripSobolev

section Cutoff

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The part of the jet coefficient of the transfer along an end chart that comes from the
derivative of the cutoff: at `w = φ'_q(ζ)` with conformal scale `r`, the jet `(x, y, z)` goes to
`(0, r ∂sβ(w) x, r ∂tβ(w) x)`. -/
private def endTransferCutoffCoeff (q : Puncture) (β : ℝ × ℝ → ℝ) (ζ : ℝ × ℝ) :
    V × V × V →L[ℝ] V × V × V :=
  (positiveEndChartScale q ζ * fderiv ℝ β (positiveEndChart q ζ) (1, 0)) •
      ((ContinuousLinearMap.inr ℝ V (V × V)).comp (ContinuousLinearMap.inl ℝ V V)).comp
        (ContinuousLinearMap.fst ℝ V (V × V)) +
    (positiveEndChartScale q ζ * fderiv ℝ β (positiveEndChart q ζ) (0, 1)) •
      ((ContinuousLinearMap.inr ℝ V (V × V)).comp (ContinuousLinearMap.inr ℝ V V)).comp
        (ContinuousLinearMap.fst ℝ V (V × V))

private theorem endTransferCutoffCoeff_apply (q : Puncture) (β : ℝ × ℝ → ℝ) (ζ : ℝ × ℝ)
    (v : V × V × V) :
    endTransferCutoffCoeff q β ζ v =
      (0, (positiveEndChartScale q ζ * fderiv ℝ β (positiveEndChart q ζ) (1, 0)) • v.1,
        (positiveEndChartScale q ζ * fderiv ℝ β (positiveEndChart q ζ) (0, 1)) • v.1) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp [endTransferCutoffCoeff]

private theorem endTransferCoeff_eq_smul_add (q : Puncture) (β : ℝ × ℝ → ℝ) (ζ : ℝ × ℝ) :
    endTransferCoeff (V := V) q β ζ =
      β (positiveEndChart q ζ) • endTransferCoeff q (fun _ ↦ 1) ζ +
        endTransferCutoffCoeff q β ζ := by
  refine ContinuousLinearMap.ext fun v ↦ ?_
  rw [endTransferCoeff_apply_eq_smul_add, add_apply,
    smul_apply, endTransferCutoffCoeff_apply]

private theorem continuous_endTransferCutoffCoeff (q : Puncture) {β : ℝ × ℝ → ℝ}
    (hβ : ContDiff ℝ 1 β) : Continuous (endTransferCutoffCoeff (V := V) q β) := by
  have hφ := (contDiff_positiveEndChart q 0).continuous
  have hdβ : Continuous fun ζ ↦ fderiv ℝ β (positiveEndChart q ζ) :=
    (hβ.continuous_fderiv one_ne_zero).comp hφ
  have hr := continuous_positiveEndChartScale q
  unfold endTransferCutoffCoeff
  refine ((hr.mul ?_).smul continuous_const).add ((hr.mul ?_).smul continuous_const)
  · exact (ContinuousLinearMap.apply ℝ ℝ ((1, 0) : ℝ × ℝ)).continuous.comp hdβ
  · exact (ContinuousLinearMap.apply ℝ ℝ ((0, 1) : ℝ × ℝ)).continuous.comp hdβ

private theorem norm_endTransferCutoffCoeff_le (q : Puncture) (β : ℝ × ℝ → ℝ) (ζ : ℝ × ℝ) :
    ‖endTransferCutoffCoeff (V := V) q β ζ‖ ≤
      2 * (positiveEndChartScale q ζ * ‖fderiv ℝ β (positiveEndChart q ζ)‖) := by
  set r := positiveEndChartScale q ζ
  have hr : 0 < r := positiveEndChartScale_pos q ζ
  have hd (e : ℝ × ℝ) (he : ‖e‖ = 1) :
      |r * fderiv ℝ β (positiveEndChart q ζ) e| ≤ r * ‖fderiv ℝ β (positiveEndChart q ζ)‖ := by
    rw [abs_mul, abs_of_pos hr]
    gcongr
    simpa [he] using (fderiv ℝ β (positiveEndChart q ζ)).le_opNorm e
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v ↦ ?_
  -- Each nonzero component is a coefficient of size at most `r ‖dβ‖` times `v.1`, and
  -- `‖v.1‖ ≤ ‖v‖`; the factor `2` is slack.
  have hcomp (e : ℝ × ℝ) (he : ‖e‖ = 1) :
      |r * fderiv ℝ β (positiveEndChart q ζ) e| * ‖v.1‖ ≤
        2 * (r * ‖fderiv ℝ β (positiveEndChart q ζ)‖) * ‖v‖ :=
    calc |r * fderiv ℝ β (positiveEndChart q ζ) e| * ‖v.1‖
        ≤ (r * ‖fderiv ℝ β (positiveEndChart q ζ)‖) * ‖v‖ :=
          mul_le_mul (hd e he) (norm_fst_le v) (norm_nonneg _) (by positivity)
      _ ≤ 2 * (r * ‖fderiv ℝ β (positiveEndChart q ζ)‖) * ‖v‖ :=
          mul_le_mul_of_nonneg_right (le_mul_of_one_le_left (by positivity) one_le_two)
            (norm_nonneg _)
  rw [endTransferCutoffCoeff_apply, Prod.norm_def, Prod.norm_def, norm_zero, norm_smul,
    norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
  exact max_le (by positivity) (max_le (hcomp (1, 0) (by simp [Prod.norm_def]))
    (hcomp (0, 1) (by simp [Prod.norm_def])))

end Cutoff

section Parametrix

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]

omit [CompleteSpace W] in
/-- Read along the end chart, the part of the coefficient field coming from the derivative of the
cutoff is essentially bounded. -/
private theorem memLp_comp_endTransferCutoffCoeff (q : Puncture)
    {M : ℝ × ℝ → V × V × V →L[ℝ] W} (hM : MemLp M ∞ (volume.restrict thricePuncturedSphereReal))
    {β : ℝ × ℝ → ℝ} (hβ : ContDiff ℝ 1 β) {B : ℝ}
    (hB : ∀ z, Complex.equivRealProdCLM.symm z ≠ q.endCenter →
      ‖Complex.equivRealProdCLM.symm z - q.endCenter‖ * ‖fderiv ℝ β z‖ ≤ B) :
    MemLp (fun ζ ↦ (M (positiveEndChart q ζ)).comp (endTransferCutoffCoeff q β ζ)) ∞
      stripMeasure := by
  have hcut : MemLp (endTransferCutoffCoeff (V := V) q β) ∞ stripMeasure := by
    refine memLp_top_of_bound (continuous_endTransferCutoffCoeff q hβ).aestronglyMeasurable
      (2 * (2 * π * B)) (ae_of_all _ fun ζ ↦ ?_)
    refine (norm_endTransferCutoffCoeff_le q β ζ).trans ?_
    have h := hB _ (equivRealProdCLM_symm_positiveEndChart_ne_endCenter q ζ)
    rw [positiveEndChartScale_apply]
    nlinarith [Real.pi_pos]
  exact (hM.comp_quasiMeasurePreserving_top (quasiMeasurePreserving_positiveEndChart q)).clm_comp
    ∞ hcut

/-- Read along the end chart, the part of the coefficient field coming from the derivative of the
cutoff gives a compact operator on `W^{1,2}` of the cylinder when the derivative of the cutoff
vanishes outside a compact range of heights: it only reads the value of a jet. -/
private theorem isCompactOperator_jetOperator_comp_endTransferCutoffCoeff (q : Puncture)
    {M : ℝ × ℝ → V × V × V →L[ℝ] W} (hM : MemLp M ∞ (volume.restrict thricePuncturedSphereReal))
    {β : ℝ × ℝ → ℝ} (hβ : ContDiff ℝ 1 β) {B : ℝ}
    (hB : ∀ z, Complex.equivRealProdCLM.symm z ≠ q.endCenter →
      ‖Complex.equivRealProdCLM.symm z - q.endCenter‖ * ‖fderiv ℝ β z‖ ≤ B)
    {T₀ T₁ : ℝ}
    (hdβ : ∀ ζ : ℝ × ℝ, ζ.1 ≤ T₀ ∨ T₁ ≤ ζ.1 → fderiv ℝ β (positiveEndChart q ζ) = 0) :
    IsCompactOperator ((jetOperator stripMeasure fun ζ ↦
      (M (positiveEndChart q ζ)).comp (endTransferCutoffCoeff q β ζ)).comp
        (CylinderSobolev.H1 V).subtypeL) :=
  CylinderSobolev.isCompactOperator_jetOperator_comp_subtypeL_of_eq_zero_of_le_or_le
    (memLp_comp_endTransferCutoffCoeff q hM hβ hB)
    (ae_of_all _ fun ζ a b ↦ by simp [endTransferCutoffCoeff_apply, Prod.mk_zero_zero])
    (ae_of_all _ fun ζ (hout : ζ.1 ≤ T₀ ∨ T₁ ≤ ζ.1) ↦ ContinuousLinearMap.ext fun v ↦ by
      simp [endTransferCutoffCoeff_apply, hdβ ζ hout, Prod.mk_zero_zero])

omit [FiniteDimensional ℝ V] [CompleteSpace W] in
/-- Read along the end chart, the coefficient field minus its cutoff part and the cutoff times the
model is the cutoff times the difference of the coefficient field with the cutoff `1` and the
model, so it is at most `B ε` where the cutoff is bounded by `B` and that difference by `ε`. -/
private theorem norm_comp_endTransferCoeff_sub_sub_smul_le (q : Puncture)
    (M : ℝ × ℝ → V × V × V →L[ℝ] W) (G : ℝ × ℝ → V × V × V →L[ℝ] W) (β : ℝ × ℝ → ℝ)
    (ζ : ℝ × ℝ) {B ε : ℝ} (hB : |β (positiveEndChart q ζ)| ≤ B)
    (hMG : β (positiveEndChart q ζ) ≠ 0 →
      ‖(M (positiveEndChart q ζ)).comp (endTransferCoeff q (fun _ ↦ 1) ζ) - G ζ‖ ≤ ε)
    (hBε : 0 ≤ B * ε) :
    ‖(M (positiveEndChart q ζ)).comp (endTransferCoeff q β ζ) -
        (M (positiveEndChart q ζ)).comp (endTransferCutoffCoeff q β ζ) -
          β (positiveEndChart q ζ) • G ζ‖ ≤ B * ε := by
  rw [endTransferCoeff_eq_smul_add q β ζ, ContinuousLinearMap.comp_add,
    ContinuousLinearMap.comp_smul, add_sub_cancel_right]
  rw [← smul_sub (A := V × V × V →L[ℝ] W), norm_smul, Real.norm_eq_abs]
  by_cases h : β (positiveEndChart q ζ) = 0
  · rwa [h, abs_zero, zero_mul]
  · exact mul_le_mul hB (hMG h) (norm_nonneg _) ((abs_nonneg _).trans hB)

omit [FiniteDimensional ℝ V] [CompleteSpace W] in
/-- If `Q` is a right inverse of the first-order operator with coefficient field `G`, then the
first-order operator with coefficient field `b G + C + E` applied to `Q h` is `b h` plus the
operators of `C` and `E` applied to `Q h`. -/
private theorem jetOperator_smul_add_add_ae_eq {G C E : ℝ × ℝ → V × V × V →L[ℝ] W}
    {b : ℝ × ℝ → ℝ} (hb : MemLp b ∞ stripMeasure) (hG : MemLp G ∞ stripMeasure)
    (hC : MemLp C ∞ stripMeasure) (hE : MemLp E ∞ stripMeasure)
    {Q : Lp W 2 stripMeasure →L[ℝ] CylinderSobolev.H1 V}
    (hQ : ∀ h, jetOperator stripMeasure G (Q h) = h) (h : Lp W 2 stripMeasure) :
    (jetOperator stripMeasure ((fun ζ ↦ b ζ • G ζ) + C + E) (Q h) : ℝ × ℝ → W) =ᵐ[stripMeasure]
      fun ζ ↦ b ζ • h ζ + jetOperator stripMeasure C (Q h) ζ +
        jetOperator stripMeasure E (Q h) ζ := by
  have hbG : MemLp (fun ζ ↦ b ζ • G ζ) ∞ stripMeasure := hb.smul hG
  rw [jetOperator_add (hbG.add hC) hE, jetOperator_add hbG hC]
  filter_upwards [Lp.coeFn_add (jetOperator stripMeasure (fun ζ ↦ b ζ • G ζ) (Q h) +
      jetOperator stripMeasure C (Q h)) (jetOperator stripMeasure E (Q h)),
    Lp.coeFn_add (jetOperator stripMeasure (fun ζ ↦ b ζ • G ζ) (Q h))
      (jetOperator stripMeasure C (Q h)),
    coeFn_jetOperator_smul hb hG (Q h)] with ζ h₁ h₂ h₃
  rw [add_apply, add_apply, h₁, Pi.add_apply, h₂, Pi.add_apply, h₃, hQ h]

/-- **The end contribution to a right parametrix.** Let `D` be a first-order operator on the pair
of pants `S` with an essentially bounded coefficient field `M` on conformal jets, and let the
first-order operator on the cylinder with an essentially bounded coefficient field `G` have a right
inverse `Q : L²(ℝ × S¹, W) → W^{1,2}(ℝ × S¹, V)`. Let `β` be a cutoff on the plane as in
`endTransfer_mem_H1`, bounded by `B`, vanishing on the part `s ≤ T₀` of the band of the end
chart `φ'_q` of the end `q`, and with derivative vanishing there and beyond a height `T₁`. If,
beyond `T₀`, the coefficient field of `D` read along `φ'_q` is within `ε` of `G`, then

`D (β · (Q h ∘ ψ)) = φ'_q-transfer of (β(φ'_q) h + K h + E h)`

for a compact operator `K` and an operator `E` of norm at most `B ε ‖Q‖`, on `L²` of the strip;
here `ψ` is the inverse of the chart, and both sides are compared through the `L²` isometry
`positiveEndChartLp`. So the transfer of `Q` inverts `D` on the end, up to a compact operator
and an operator that is small when the cutoff lives far out. -/
theorem exists_isCompactOperator_positiveEndChartLp_symm_jetOperator_endTransfer_ae_eq
    (q : Puncture)
    {M : ℝ × ℝ → V × V × V →L[ℝ] W} (hM : MemLp M ∞ (volume.restrict thricePuncturedSphereReal))
    {G : ℝ × ℝ → V × V × V →L[ℝ] W} (hG : MemLp G ∞ stripMeasure)
    {Q : Lp W 2 stripMeasure →L[ℝ] CylinderSobolev.H1 V}
    (hQ : ∀ h, jetOperator stripMeasure G (Q h) = h)
    {β : ℝ × ℝ → ℝ} (hβ : ContDiff ℝ 1 β)
    (hβS : ∀ z ∈ tsupport β, Complex.equivRealProdCLM.symm z ≠ q.endCenter →
      z ∈ thricePuncturedSphereReal)
    {B : ℝ} (hB : ∀ z, Complex.equivRealProdCLM.symm z ≠ q.endCenter →
      |β z| ≤ B ∧ ‖Complex.equivRealProdCLM.symm z - q.endCenter‖ *
        (√(cylindricalWeight z) * |β z|) ≤ B ∧
        ‖Complex.equivRealProdCLM.symm z - q.endCenter‖ * ‖fderiv ℝ β z‖ ≤ B)
    {T₀ T₁ : ℝ} (hβ₀ : ∀ ζ : ℝ × ℝ, ζ.1 ≤ T₀ → β (positiveEndChart q ζ) = 0)
    (hdβ : ∀ ζ : ℝ × ℝ, ζ.1 ≤ T₀ ∨ T₁ ≤ ζ.1 → fderiv ℝ β (positiveEndChart q ζ) = 0)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hMG : ∀ᵐ ζ ∂stripMeasure, T₀ < ζ.1 →
      ‖(M (positiveEndChart q ζ)).comp (endTransferCoeff q (fun _ ↦ 1) ζ) - G ζ‖ ≤ ε) :
    ∃ K E : Lp W 2 stripMeasure →L[ℝ] Lp W 2 stripMeasure, IsCompactOperator K ∧
      ‖E‖ ≤ B * ε * ‖Q‖ ∧ ∀ h, ((positiveEndChartLp q).symm (jetOperator
        (volume.restrict thricePuncturedSphereReal) M (endTransfer q β (Q h))) :
          ℝ × ℝ → W) =ᵐ[stripMeasure] fun ζ ↦ β (positiveEndChart q ζ) • h ζ + K h ζ + E h ζ := by
  have hB0 : 0 ≤ B :=
    (abs_nonneg _).trans (hB _ (equivRealProdCLM_symm_positiveEndChart_ne_endCenter q 0)).1
  have hT := memLp_endTransferCoeff (V := V) q hβ hβS hB
  have hN : MemLp (fun ζ ↦ (M (positiveEndChart q ζ)).comp (endTransferCoeff q β ζ)) ∞
      stripMeasure :=
    (hM.comp_quasiMeasurePreserving_top (quasiMeasurePreserving_positiveEndChart q)).clm_comp ∞ hT
  have hC := memLp_comp_endTransferCutoffCoeff q hM hβ fun z hz ↦ (hB z hz).2.2
  have hβφ := memLp_comp_positiveEndChart q hβ.continuous fun z hz ↦ (hB z hz).1
  -- Read along the chart, the coefficient field of `D` applied to the transfer is the cutoff times
  -- the model, plus the cutoff part `C`, plus the rest `E'`, which is small.
  obtain ⟨E', hE'⟩ : ∃ E' : ℝ × ℝ → V × V × V →L[ℝ] W, E' = fun ζ ↦
      (M (positiveEndChart q ζ)).comp (endTransferCoeff q β ζ) -
        (M (positiveEndChart q ζ)).comp (endTransferCutoffCoeff q β ζ) -
          β (positiveEndChart q ζ) • G ζ := ⟨_, rfl⟩
  have hE'm : MemLp E' ∞ stripMeasure := hE' ▸ (hN.sub hC).sub (hβφ.smul hG)
  have hE'b : ∀ᵐ ζ ∂stripMeasure, ‖E' ζ‖ ≤ B * ε := by
    filter_upwards [hMG] with ζ hζ
    rw [hE']
    refine norm_comp_endTransferCoeff_sub_sub_smul_le q M G β ζ
      (hB _ (equivRealProdCLM_symm_positiveEndChart_ne_endCenter q ζ)).1 (fun h ↦ hζ ?_)
      (by positivity)
    exact lt_of_not_ge fun h' ↦ h (hβ₀ ζ h')
  have hsplit : (fun ζ ↦ (M (positiveEndChart q ζ)).comp (endTransferCoeff q β ζ)) =
      ((fun ζ ↦ β (positiveEndChart q ζ) • G ζ) +
        fun ζ ↦ (M (positiveEndChart q ζ)).comp (endTransferCutoffCoeff q β ζ)) + E' := by
    funext ζ
    simp only [Pi.add_apply, hE']
    abel
  refine ⟨((jetOperator stripMeasure fun ζ ↦
    (M (positiveEndChart q ζ)).comp (endTransferCutoffCoeff q β ζ)).comp
      (CylinderSobolev.H1 V).subtypeL).comp Q,
    ((jetOperator stripMeasure E').comp (CylinderSobolev.H1 V).subtypeL).comp Q,
    (isCompactOperator_jetOperator_comp_endTransferCutoffCoeff q hM hβ
      (fun z hz ↦ (hB z hz).2.2) hdβ).comp_clm Q,
    ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h ↦ ?_, fun h ↦ ?_⟩
  · calc ‖jetOperator stripMeasure E' (Q h)‖
        ≤ B * ε * ‖(Q h : Lp (V × V × V) 2 stripMeasure)‖ :=
          norm_jetOperator_apply_le hE'm hE'b _
      _ ≤ B * ε * (‖Q‖ * ‖h‖) := by
        rw [Submodule.norm_coe]
        gcongr
        exact Q.le_opNorm h
      _ = B * ε * ‖Q‖ * ‖h‖ := by ring
  rw [jetOperator_endTransfer q hT hM, LinearIsometryEquiv.symm_apply_apply, hsplit]
  exact jetOperator_smul_add_add_ae_eq hβφ hG hC hE'm hQ h

end Parametrix

section Rotation

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- The rotation `r⁻¹ (a + σ b L_t)` at `ζ = (s, t)`, for the conformal scale `r` and
`(a, b) = dφ'_q(ζ)(1, 0)` of the end chart and a sign `σ`: for `σ = 1` it is the rotation by which
the linearized operator of a pair of pants read along the end chart differs from its end model, and
for `σ = -1` it is its inverse. -/
private def endRotation (q : Puncture) (L : ℝ → AlmostComplexStructure V) (σ : ℝ) (ζ : ℝ × ℝ) :
    V →L[ℝ] V :=
  (positiveEndChartScale q ζ)⁻¹ •
    ((fderiv ℝ (positiveEndChart q) ζ (1, 0)).1 • ContinuousLinearMap.id ℝ V +
      (σ * (fderiv ℝ (positiveEndChart q) ζ (1, 0)).2) • (L ζ.2).toLinearMap.toContinuousLinearMap)

private theorem endRotation_one (q : Puncture) (L : ℝ → AlmostComplexStructure V) (ζ : ℝ × ℝ) :
    endRotation q L 1 ζ = (positiveEndChartScale q ζ)⁻¹ •
      ((fderiv ℝ (positiveEndChart q) ζ (1, 0)).1 • ContinuousLinearMap.id ℝ V +
        (fderiv ℝ (positiveEndChart q) ζ (1, 0)).2 •
          (L ζ.2).toLinearMap.toContinuousLinearMap) := by
  rw [endRotation, one_mul]

private theorem endRotation_apply (q : Puncture) (L : ℝ → AlmostComplexStructure V) (σ : ℝ)
    (ζ : ℝ × ℝ) (v : V) :
    endRotation q L σ ζ v = (positiveEndChartScale q ζ)⁻¹ •
      ((fderiv ℝ (positiveEndChart q) ζ (1, 0)).1 • v +
        (σ * (fderiv ℝ (positiveEndChart q) ζ (1, 0)).2) • L ζ.2 v) := by
  simp [endRotation]

private theorem endRotation_one_apply_endRotation_neg_one (q : Puncture)
    (L : ℝ → AlmostComplexStructure V) (ζ : ℝ × ℝ) (v : V) :
    endRotation q L 1 ζ (endRotation q L (-1) ζ v) = v := by
  have hr := positiveEndChartScale_pos q ζ
  have hdet := sq_positiveEndChartScale_eq_sq_add_sq q ζ
  set r := positiveEndChartScale q ζ
  set a := (fderiv ℝ (positiveEndChart q) ζ (1, 0)).1
  set b := (fderiv ℝ (positiveEndChart q) ζ (1, 0)).2
  -- `(a + b J) (a - b J) = a² + b² = r²`.
  have hs : r⁻¹ * r⁻¹ * (a ^ 2 + b ^ 2) = 1 := by
    rw [← hdet]
    field_simp
  rw [endRotation_apply, endRotation_apply, map_smul, map_add, map_smul, map_smul,
    (L ζ.2).apply_apply]
  linear_combination (norm := module) hs • v

private theorem continuous_endRotation (q : Puncture) {L : ℝ → AlmostComplexStructure V}
    (hL : Continuous fun t ↦ (L t).toLinearMap.toContinuousLinearMap) (σ : ℝ) :
    Continuous (endRotation q L σ) := by
  have hd := (contDiff_positiveEndChart q 1).continuous_fderiv one_ne_zero
  have ha : Continuous fun ζ ↦ fderiv ℝ (positiveEndChart q) ζ (1, 0) :=
    (ContinuousLinearMap.apply ℝ (ℝ × ℝ) ((1, 0) : ℝ × ℝ)).continuous.comp hd
  have hr := continuous_positiveEndChartScale q
  refine ((hr.inv₀ fun ζ ↦ (positiveEndChartScale_pos q ζ).ne').smul
    ((continuous_fst.comp ha).smul continuous_const |>.add
      ((continuous_const.mul (continuous_snd.comp ha)).smul (hL.comp continuous_snd))))

private theorem norm_endRotation_le (q : Puncture) (L : ℝ → AlmostComplexStructure V) {σ : ℝ}
    (hσ : |σ| ≤ 1) (ζ : ℝ × ℝ) :
    ‖endRotation q L σ ζ‖ ≤ 1 + ‖(L ζ.2).toLinearMap.toContinuousLinearMap‖ := by
  have hr := positiveEndChartScale_pos q ζ
  have ha := abs_fst_fderiv_positiveEndChart_le q ζ
  have hb := abs_snd_fderiv_positiveEndChart_le q ζ
  rw [endRotation, norm_smul, norm_inv, Real.norm_of_nonneg hr.le, inv_mul_le_iff₀ hr]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
  have hid := ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := V)
  have hσb : |σ| * |(fderiv ℝ (positiveEndChart q) ζ (1, 0)).2| ≤ positiveEndChartScale q ζ :=
    (mul_le_of_le_one_left (abs_nonneg _) hσ).trans hb
  -- The identity term is at most `r · 1` and the `L` term at most `r ‖L‖`.
  rw [mul_add, mul_one]
  exact add_le_add ((mul_le_of_le_one_right (abs_nonneg _) hid).trans ha)
    (mul_le_mul_of_nonneg_right hσb (norm_nonneg _))

private theorem memLp_endRotation (q : Puncture) {L : ℝ → AlmostComplexStructure V}
    (hL : Continuous fun t ↦ (L t).toLinearMap.toContinuousLinearMap) {σ : ℝ} (hσ : |σ| ≤ 1) :
    MemLp (endRotation q L σ) ∞ stripMeasure := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc (0 : ℝ) 1)
    hL.continuousOn
  exact memLp_top_of_bound (continuous_endRotation q hL σ).aestronglyMeasurable (1 + C)
    (ae_restrict_of_forall_mem (MeasurableSet.univ.prod measurableSet_Icc) fun ζ hζ ↦
      (norm_endRotation_le q L hσ ζ).trans (by linarith [hC ζ.2 hζ.2]))

/-- The coefficient field of the stationary cylinder operator `∂s + L_t (∂t - S_t)` followed by the
rotation `r⁻¹ (a + b L_t)` of the end chart is essentially bounded. -/
private theorem memLp_endRotation_comp_stationaryJetCoeff (q : Puncture)
    {L : ℝ → AlmostComplexStructure V}
    (hL : Continuous fun t ↦ (L t).toLinearMap.toContinuousLinearMap) {S : ℝ → V →L[ℝ] V}
    (hS : Continuous S) :
    MemLp (fun ζ ↦ (endRotation q L 1 ζ).comp (stationaryJetCoeff L S ζ)) ∞ stripMeasure :=
  (memLp_endRotation q hL (by norm_num)).clm_comp ∞ (memLp_stationaryJetCoeff hL hS)

/-- When the stationary cylinder operator `∂s + L_t (∂t - S_t)` is invertible on `W^{1,2}`, the
inverse rotation followed by its inverse is a right inverse of the stationary operator followed by
the rotation `r⁻¹ (a + b L_t)` of the end chart. -/
private theorem exists_forall_jetOperator_endRotation_comp_stationaryJetCoeff_eq (q : Puncture)
    {L : ℝ → AlmostComplexStructure V}
    (hL : Continuous fun t ↦ (L t).toLinearMap.toContinuousLinearMap) {S : ℝ → V →L[ℝ] V}
    (hS : Continuous S) (hD : (stationarySobolevOperator L S).IsInvertible) :
    ∃ Q : Lp V 2 stripMeasure →L[ℝ] CylinderSobolev.H1 V, ∀ h, jetOperator stripMeasure
      (fun ζ ↦ (endRotation q L 1 ζ).comp (stationaryJetCoeff L S ζ)) (Q h) = h := by
  have hstat := memLp_stationaryJetCoeff hL hS
  have hG := memLp_endRotation_comp_stationaryJetCoeff q hL hS
  have hR := memLp_endRotation q hL (σ := -1) (by norm_num)
  refine ⟨(stationarySobolevOperator L S).inverse.comp
    (Lp.operatorMultiplication 2 (hR.toLp (endRotation q L (-1)))), fun h ↦ Lp.ext ?_⟩
  -- The stationary operator applied to `Q h` is the inverse rotation applied to `h`.
  have hinv := hD.self_apply_inverse
    (Lp.operatorMultiplication 2 (hR.toLp (endRotation q L (-1))) h)
  nth_rewrite 1 [stationarySobolevOperator_def] at hinv
  filter_upwards [coeFn_jetOperator hG _, coeFn_jetOperator hstat _,
    Lp.operatorMultiplication_ae (hR.toLp (endRotation q L (-1))) h, hR.coeFn_toLp]
    with ζ h₁ h₂ h₃ h₄
  rw [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply] at hinv
  rw [h₁, ContinuousLinearMap.comp_apply, ← h₂, ContinuousLinearMap.comp_apply, hinv, h₃, h₄,
    endRotation_one_apply_endRotation_neg_one]

end Rotation

end TauCeti.Floer

namespace TauCeti.SymplecticForm

open Floer StripSobolev

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {H : Puncture → ℝ → V → ℝ}

/-- **The end contribution to a right parametrix of the linearized operator of a pair of pants.**
Let `(J, K_s, K_t)` be Floer data on the pair of pants `S` which beyond a height `T` of the end `q`,
read in the positive end chart `φ'_q`, are the structures `J_q(t)` of a `C¹` family and the
pair-of-pants perturbation of period-one Hamiltonians `H_q` with `H_q` jointly `C²`, with
essentially bounded coefficient field `M` on conformal jets along `u`, and let `u` be
differentiable and solve the Floer equation there. Let the loops of `u ∘ φ'_q` converge uniformly to
a continuous loop `x`, with slice defect tending uniformly to zero, and let the stationary cylinder
operator `∂s + J_q(t, x(t)) (∂t - dX_{H'_q(t)}(x(t)))` be invertible on `W^{1,2}(ℝ × S¹, V)`, as it
is at a nondegenerate orbit for compatible structures
(`isInvertible_floerSobolevOperator_of_isNondegenerateFixedPt_of_compatible`).

Then there is a bounded operator `Q : L²(ℝ × S¹, V) → W^{1,2}(ℝ × S¹, V)` such that for every
`ε > 0` and every cutoff `β` living far enough out on the end `q` (vanishing, with its derivative,
on the part `s ≤ T₀` of the band of `φ'_q`, with derivative vanishing beyond some height `T₁`, and
bounded by `B` as in `TauCeti.Floer.endTransfer_mem_H1`), the linearized operator `D_u` applied to
the transfer `β · (Q h ∘ ψ)` along the end chart is the transfer by the `L²` isometry
`TauCeti.Floer.positiveEndChartLp` of `β(φ'_q) h + K h + E h`, with `K` compact and `‖E‖ ≤ B ε`. -/
theorem exists_forall_exists_isCompactOperator_jetOperator_floerConformalJetCoeff_endTransfer
    (ω : SymplecticForm V) (hH : ∀ q, Periodic (H q) 1) {q : Puncture}
    (hHs : ContDiff ℝ 2 (uncurry (H q)))
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {Jq : ℝ → V → AlmostComplexStructure V}
    (hJq : ContDiff ℝ 1 fun p : ℝ × V ↦ (Jq p.1 p.2).toLinearMap.toContinuousLinearMap)
    {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V} {T : ℝ}
    (hJend : ∀ ζ : ℝ × ℝ, T ≤ ζ.1 → J (positiveEndChart q ζ) = Jq ζ.2)
    (hKend : ∀ ζ : ℝ × ℝ, T ≤ ζ.1 →
      Ks (positiveEndChart q ζ) = (fun x ↦ pairOfPantsPerturbation H
        (Complex.equivRealProdCLM.symm (positiveEndChart q ζ)) x 1) ∧
      Kt (positiveEndChart q ζ) = fun x ↦ pairOfPantsPerturbation H
        (Complex.equivRealProdCLM.symm (positiveEndChart q ζ)) x Complex.I)
    (hu : ∀ ζ : ℝ × ℝ, T ≤ ζ.1 → DifferentiableAt ℝ u (positiveEndChart q ζ))
    (hfl : ∀ ζ : ℝ × ℝ, T ≤ ζ.1 → IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (J (positiveEndChart q ζ) (u (positiveEndChart q ζ)))
      (ω.perturbedFDeriv Ks Kt u (positiveEndChart q ζ) : ℝ × ℝ →ₗ[ℝ] V))
    (hM : MemLp (ω.floerConformalJetCoeff cylindricalWeight
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u) ∞
        (volume.restrict thricePuncturedSphereReal))
    {x : ℝ → V} (hxc : Continuous x)
    (hux : TendstoUniformlyOn (fun s t ↦ u (positiveEndChart q (s, t))) x atTop (Icc 0 1))
    (hδ : TendstoUniformlyOn (fun s t ↦ sliceDefect
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) (u ∘ positiveEndChart q)
        (s, t)) 0 atTop (Icc 0 1))
    (hD : ContinuousLinearMap.IsInvertible (stationarySobolevOperator (fun t ↦ Jq t (x t))
      fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) (x t))) :
    ∃ Q : Lp V 2 stripMeasure →L[ℝ] CylinderSobolev.H1 V, ∀ ε > 0, ∃ T₀ : ℝ,
      ∀ {β : ℝ × ℝ → ℝ} {B T₁ : ℝ}, ContDiff ℝ 1 β →
        (∀ z ∈ tsupport β, Complex.equivRealProdCLM.symm z ≠ q.endCenter →
          z ∈ thricePuncturedSphereReal) →
        (∀ z, Complex.equivRealProdCLM.symm z ≠ q.endCenter →
          |β z| ≤ B ∧ ‖Complex.equivRealProdCLM.symm z - q.endCenter‖ *
            (√(cylindricalWeight z) * |β z|) ≤ B ∧
            ‖Complex.equivRealProdCLM.symm z - q.endCenter‖ * ‖fderiv ℝ β z‖ ≤ B) →
        (∀ ζ : ℝ × ℝ, ζ.1 ≤ T₀ → β (positiveEndChart q ζ) = 0) →
        (∀ ζ : ℝ × ℝ, ζ.1 ≤ T₀ ∨ T₁ ≤ ζ.1 → fderiv ℝ β (positiveEndChart q ζ) = 0) →
        ∃ K E : Lp V 2 stripMeasure →L[ℝ] Lp V 2 stripMeasure, IsCompactOperator K ∧
          ‖E‖ ≤ B * ε ∧ ∀ h, ((positiveEndChartLp q).symm (jetOperator
            (volume.restrict thricePuncturedSphereReal) (ω.floerConformalJetCoeff cylindricalWeight
              (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u)
                (endTransfer q β (Q h))) : ℝ × ℝ → V) =ᵐ[stripMeasure]
            fun ζ ↦ β (positiveEndChart q ζ) • h ζ + K h ζ + E h ζ := by
  set Jx : ℝ → AlmostComplexStructure V := fun t ↦ Jq t (x t)
  set S : ℝ → V →L[ℝ] V :=
    fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) (x t)
  have hJx : Continuous fun t ↦ (Jx t).toLinearMap.toContinuousLinearMap :=
    hJq.continuous.comp (continuous_id.prodMk hxc)
  have hS : Continuous S := (continuous_fderiv_slice_right
    (f := fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t))
    (ω.contDiff_hamiltonianVectorField_uncurry (n := 1)
      (contDiff_uncurry_positiveEndHamiltonian hHs))).comp (continuous_id.prodMk hxc)
  -- The end model, the stationary cylinder operator followed by the rotation of the chart, has a
  -- right inverse.
  have hG := memLp_endRotation_comp_stationaryJetCoeff q hJx hS
  obtain ⟨Q, hQ⟩ := exists_forall_jetOperator_endRotation_comp_stationaryJetCoeff_eq q hJx hS hD
  refine ⟨Q, fun ε hε ↦ ?_⟩
  -- Far out on the end, the operator read along the chart is close to the end model.
  set ε' := ε / (‖Q‖ + 1)
  have hε' : 0 < ε' := by positivity
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.1
    (ω.eventually_forall_norm_floerConformalJetCoeff_comp_endTransferCoeff_sub_lt hH hHs hJq
      hJend hKend hu hfl (β := fun _ ↦ 1) (fun _ _ ↦ ⟨rfl, by simp⟩) hxc hux hδ hε')
  refine ⟨T₀, fun {β B T₁} hβ hβS hB hβ₀ hdβ ↦ ?_⟩
  have hMG : ∀ᵐ ζ ∂stripMeasure, T₀ < ζ.1 →
      ‖(ω.floerConformalJetCoeff cylindricalWeight
          (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u
          (positiveEndChart q ζ)).comp (endTransferCoeff q (fun _ ↦ 1) ζ) -
        (endRotation q Jx 1 ζ).comp (stationaryJetCoeff Jx S ζ)‖ ≤ ε' :=
    ae_restrict_of_forall_mem (MeasurableSet.univ.prod measurableSet_Icc) fun ζ hζ hT ↦ by
      rw [endRotation_one]
      simpa only [endModelCoeff_def, endModelRotation_def] using (hT₀ ζ.1 hT.le ζ.2 hζ.2).le
  obtain ⟨K, E, hK, hE, hid⟩ :=
    exists_isCompactOperator_positiveEndChartLp_symm_jetOperator_endTransfer_ae_eq q hM hG hQ
      hβ hβS hB hβ₀ hdβ hε'.le hMG
  refine ⟨K, E, hK, hE.trans ?_, hid⟩
  have hB0 : 0 ≤ B :=
    (abs_nonneg _).trans (hB _ (equivRealProdCLM_symm_positiveEndChart_ne_endCenter q 0)).1
  have hQε : ε' * ‖Q‖ ≤ ε := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [norm_nonneg Q]
  calc B * ε' * ‖Q‖ = B * (ε' * ‖Q‖) := by ring
    _ ≤ B * ε := by gcongr

end TauCeti.SymplecticForm
