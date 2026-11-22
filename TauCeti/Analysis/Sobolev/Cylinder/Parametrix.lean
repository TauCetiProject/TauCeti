/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Cylinder
public import Mathlib.Analysis.Normed.Operator.Fredholm.Basic
import TauCeti.Analysis.Fredholm.CompactPerturbation
import TauCeti.Analysis.Normed.Operator.Compact.Interpolation
import TauCeti.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.MeasureTheory.Function.Lp.Multiplication

/-!
# Fredholm operators on the cylinder with invertible models at the ends

Let `D ξ = M (ξ, ∂s ξ, ∂t ξ)` be a first-order operator on the cylinder `ℝ × S¹` with an
essentially bounded coefficient field `M`, realized from `W^{1,2}(ℝ × S¹, V)` to `L²(ℝ × S¹, W)`
by `TauCeti.jetOperator stripMeasure`. This file proves that `D` is Fredholm as soon as it is
asymptotic, as `s → -∞` and as `s → +∞`, to operators `Dneg` and `Dpos` with the same principal
part which are invertible
(`TauCeti.CylinderSobolev.isFredholm_jetOperator_comp_subtypeL_of_isInvertible`).
The invertibility of `Dneg` and `Dpos` is a hypothesis. The result is designed to apply to the
linearized Floer operator `∂s + J₀ ∂t + S(s, t)` along a Floer trajectory, written in a unitary
frame as a `jetOperator`, with models the stationary cylinder operators `∂s + J₀ (∂t - S±(t))` at
the two asymptotic orbits, once their invertibility on `W^{1,2}` is supplied; neither step is
carried out in this file.

The proof constructs a two-sided parametrix modulo compact operators, so that Atkinson's theorem
(`ContinuousLinearMap.IsFredholm.of_isCompactOperator_comp_sub_one`) applies. It uses no
regularity theory for weak solutions of the adjoint equation.

* **Cutoffs in `s`.** Multiplication by a `C²` function `β(s)` with `β` and `β'` bounded acts on
  jets through the coefficient field `TauCeti.StripSobolev.cutoffCoeff`,
  `(ξ, ξ_s, ξ_t) ↦ (β ξ, β ξ_s + β' ξ, β ξ_t)`, and preserves `W^{1,2}`
  (`TauCeti.CylinderSobolev.jetOperator_cutoffCoeff_mem_H1`).
* **Compact zeroth-order operators.** A coefficient field that acts on the value of a jet only and
  tends to zero as `|s| → ∞` gives a compact operator on `W^{1,2}`
  (`TauCeti.CylinderSobolev.isCompactOperator_jetOperator_comp_subtypeL_of_tendsto_zero`): over
  each compact piece `[-R, R] × S¹` this is Rellich's theorem
  (`TauCeti.CylinderSobolev.isCompactOperator_restrictValue_comp_subtypeL`), the remainder is small
  in operator norm, and compact operators form a closed set.
* **The parametrix.** Choose smooth cutoffs `γneg + γpos = 1` in `s`, with `γneg` vanishing for
  `s ≥ 1` and `γpos` for `s ≤ 0`, and cutoffs `βneg`, `βpos` equal to one on the supports of
  `γneg`, `γpos`. For `Q = βneg Dneg⁻¹ γneg + βpos Dpos⁻¹ γpos`, the remainders `D Q - 1` and
  `Q D - 1` are sums of zeroth-order operators composed with bounded ones. Each zeroth-order
  operator is the error of commuting `D` with a cutoff `β`: since `D` and a model `D'` with
  coefficient field `M'` have equal principal parts,
  `D (β ξ) = β D' ξ + β (M - M') (ξ, 0, 0) + β' M' (0, ξ, 0)`. Its coefficient tends to zero as
  `|s| → ∞`, because `M - Mneg` does at `-∞`, `M - Mpos` does at `+∞`, `β'` vanishes far out, and
  each cutoff vanishes at the end opposite to its model. So both remainders are compact.

## Main results

* `TauCeti.CylinderSobolev.isFredholm_jetOperator_comp_subtypeL_of_isInvertible`: a first-order
  operator on the cylinder with the principal part of, and asymptotic to, invertible models at
  both ends is Fredholm on `W^{1,2}`.
* `TauCeti.CylinderSobolev.isCompactOperator_jetOperator_comp_subtypeL_of_tendsto_zero`:
  zeroth-order operators with coefficients vanishing at infinity are compact on `W^{1,2}`.
* `TauCeti.CylinderSobolev.jetOperator_cutoffCoeff_mem_H1`: multiplication by a cutoff in `s`
  preserves `W^{1,2}`.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2, on the Fredholm theory of `∂s + J₀ ∂t + S(s, t)` on the
  cylinder.
* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc. 27
  (1995), 1–33.
* F. V. Atkinson, *The normal solubility of linear equations in normed spaces*, Mat. Sbornik
  N.S. 28 (70) (1951), 3–14.
-/

public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace TauCeti.CylinderSobolev

open StripSobolev

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-! ### Multiplication by a function of `s` -/

section Cutoff

/-- Multiplying a test section by a `C²` function of `s` gives a test section. -/
theorem smul_fst_mem_testSection {β : ℝ → ℝ} (hβ : ContDiff ℝ 2 β) {ξ : ℝ × ℝ → V}
    (hξ : ξ ∈ testSection V) : (fun z ↦ β z.1 • ξ z) ∈ testSection V := by
  obtain ⟨hξ2, hξp, R, hR⟩ := mem_testSection_iff.1 hξ
  exact mem_testSection_iff.2 ⟨(hβ.comp contDiff_fst).smul hξ2, fun s t ↦ by simp [hξp],
    R, fun s t hs ↦ by simp [hR s t hs]⟩

/-- **Multiplication by a function of `s` preserves `W^{1,2}`.** For a `C²` function `β` with `β`
and `β'` bounded, the operator of the coefficient field `cutoffCoeff V β`, which multiplies a
section by `β(s)`, maps `H1 V` into itself. -/
theorem jetOperator_cutoffCoeff_mem_H1 {β : ℝ → ℝ} (hβ : ContDiff ℝ 2 β) {B : ℝ}
    (hβB : ∀ s, |β s| ≤ B) (hβ'B : ∀ s, |deriv β s| ≤ B) {f : Lp (V × V × V) 2 stripMeasure}
    (hf : f ∈ H1 V) : jetOperator stripMeasure (cutoffCoeff V β) f ∈ H1 V := by
  have hN := memLp_cutoffCoeff (V := V) (hβ.of_le one_le_two) hβB hβ'B
  refine jetClosure_subset_of_isClosed
    (s := jetOperator stripMeasure (cutoffCoeff V β) ⁻¹'
      (H1 V : Set (Lp (V × V × V) 2 stripMeasure)))
    ((isClosed_jetClosure _).preimage (jetOperator stripMeasure _).continuous) ?_ hf
  rintro _ ⟨ξ, rfl⟩
  have hmem := smul_fst_mem_testSection hβ ξ.property
  have hξd : Differentiable ℝ (ξ : ℝ × ℝ → V) :=
    (mem_testSection_iff.1 ξ.property).1.differentiable (by norm_num)
  have heq : jetOperator stripMeasure (cutoffCoeff V β) (jetLp (testSection V) ξ) =
      jetLp (testSection V) ⟨_, hmem⟩ := by
    refine Lp.ext ?_
    filter_upwards [jetOperator_jetLp_ae_eq hN ξ,
      coeFn_jetLp (S := testSection V) ⟨_, hmem⟩] with z h₁ h₂
    rw [h₁, h₂, jet_smul_fst_eq_cutoffCoeff ((hβ.differentiable (by norm_num)) _) (hξd z)]
  simp only [Set.mem_preimage, SetLike.mem_coe, heq]
  exact jetLp_mem_jetClosure _

/-- Multiplication by a `C²` function `β(s)` with `β` and `β'` bounded, as an operator on
`H1 V`: the operator of the coefficient field `cutoffCoeff V β`, restricted to `H1 V`
(`TauCeti.CylinderSobolev.coe_cutoffL`). -/
def cutoffL {β : ℝ → ℝ} (hβ : ContDiff ℝ 2 β) {B : ℝ} (hβB : ∀ s, |β s| ≤ B)
    (hβ'B : ∀ s, |deriv β s| ≤ B) : H1 V →L[ℝ] H1 V :=
  ((jetOperator stripMeasure (cutoffCoeff V β)).comp (H1 V).subtypeL).codRestrict (H1 V) fun x ↦
    jetOperator_cutoffCoeff_mem_H1 hβ hβB hβ'B x.property

/-- As an `L²` jet, `cutoffL` is the operator of the coefficient field `cutoffCoeff V β`. -/
@[simp]
theorem coe_cutoffL {β : ℝ → ℝ} (hβ : ContDiff ℝ 2 β) {B : ℝ} (hβB : ∀ s, |β s| ≤ B)
    (hβ'B : ∀ s, |deriv β s| ≤ B) (x : H1 V) :
    (cutoffL hβ hβB hβ'B x : Lp (V × V × V) 2 stripMeasure) =
      jetOperator stripMeasure (cutoffCoeff V β) (x : Lp (V × V × V) 2 stripMeasure) :=
  (rfl)

/-- Multiplication by `β(s)` with `|β| ≤ B` and `|β'| ≤ B` has norm at most `2 B` on `H1 V`. -/
theorem norm_cutoffL_apply_le {β : ℝ → ℝ} (hβ : ContDiff ℝ 2 β) {B : ℝ} (hβB : ∀ s, |β s| ≤ B)
    (hβ'B : ∀ s, |deriv β s| ≤ B) (x : H1 V) : ‖cutoffL hβ hβB hβ'B x‖ ≤ (B + B) * ‖x‖ := by
  have hb : ∀ᵐ z ∂stripMeasure, ‖cutoffCoeff V β z‖ ≤ B + B :=
    ae_of_all _ fun z ↦ (norm_cutoffCoeff_le β z).trans (add_le_add (hβB _) (hβ'B _))
  have h := norm_jetOperator_apply_le (memLp_cutoffCoeff (hβ.of_le one_le_two) hβB hβ'B) hb
    (x : Lp (V × V × V) 2 stripMeasure)
  rwa [← coe_cutoffL hβ hβB hβ'B] at h

end Cutoff

/-! ### Zeroth-order operators with small or compactly supported coefficients -/

section Operator

/-- A coefficient field acting on values only and vanishing for `|s| > R` is controlled by the
value on `[-R, R] × [0, 1]`. -/
private theorem norm_jetOperator_le_mul_norm_restrictValue {G : ℝ × ℝ → V × V × V →L[ℝ] W}
    (hG : MemLp G ∞ stripMeasure) (hval : ∀ᵐ z ∂stripMeasure, ∀ a b : V, G z (0, a, b) = 0)
    {R : ℝ} (hR : ∀ᵐ z ∂stripMeasure, R < |z.1| → G z = 0) {C : ℝ} (hC₀ : 0 ≤ C)
    (hC : ∀ᵐ z ∂stripMeasure, ‖G z‖ ≤ C) (f : Lp (V × V × V) 2 stripMeasure) :
    ‖jetOperator stripMeasure G f‖ ≤ C * ‖restrictValue R f‖ := by
  set rect : Set (ℝ × ℝ) := Icc (-R) R ×ˢ Icc (0 : ℝ) 1
  have hrect : MeasurableSet rect := measurableSet_Icc.prod measurableSet_Icc
  have hae : (jetOperator stripMeasure G f : ℝ × ℝ → W) =ᵐ[stripMeasure]
      rect.indicator fun z ↦ G z ((f z).1, 0, 0) := by
    filter_upwards [coeFn_jetOperator hG f, hval, hR,
      ae_restrict_mem (MeasurableSet.univ.prod measurableSet_Icc)] with z h₁ h₂ h₃ h₄
    rw [h₁]
    by_cases hz : z ∈ rect
    · rw [indicator_of_mem hz]
      calc G z (f z) = G z (((f z).1, 0, 0) + (0, (f z).2.1, (f z).2.2)) := by
            congr 1
            ext <;> simp
        _ = G z ((f z).1, 0, 0) := by rw [map_add, h₂, add_zero]
    · have hlt : R < |z.1| := by
        by_contra h
        exact hz ⟨abs_le.1 (not_lt.1 h), h₄.2⟩
      rw [indicator_of_notMem hz, h₃ hlt, zero_apply]
  have hle : eLpNorm (fun z ↦ G z ((f z).1, 0, 0)) 2 (stripMeasure.restrict rect) ≤
      ENNReal.ofReal C * eLpNorm (restrictValue R f) 2 (stripMeasure.restrict rect) := by
    have hmeas : AEStronglyMeasurable (fun z ↦ G z ((f z).1, 0, 0)) stripMeasure :=
      (ContinuousLinearMap.id ℝ (V × V × V →L[ℝ] W)).aestronglyMeasurable_comp₂
        hG.aestronglyMeasurable ((continuous_fst.prodMk continuous_const).comp_aestronglyMeasurable
          (Lp.aestronglyMeasurable f))
    refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul hmeas.restrict ?_ 2
    filter_upwards [ae_restrict_of_ae hC, coeFn_restrictValue R f] with z h₁ h₂
    rw [h₂]
    calc ‖G z ((f z).1, 0, 0)‖ ≤ ‖G z‖ * ‖((f z).1, (0 : V), (0 : V))‖ := (G z).le_opNorm _
      _ ≤ C * ‖(f z).1‖ := by
        rw [show ‖((f z).1, (0 : V), (0 : V))‖ = ‖(f z).1‖ by simp [Prod.norm_def]]
        exact mul_le_mul_of_nonneg_right h₁ (norm_nonneg _)
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae hae,
    eLpNorm_indicator_eq_eLpNorm_restrict hrect.nullMeasurableSet]
  calc _ ≤ (ENNReal.ofReal C * eLpNorm (restrictValue R f) 2 (stripMeasure.restrict rect)).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_ne_top _)) hle
    _ = _ := by rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC₀]

/-- A coefficient field acting on values only and vanishing for `|s| > R` gives a compact
operator on `H1 V`: it is controlled by the value on the compact piece `[-R, R] × S¹`, which is
compact by Rellich's theorem. -/
private theorem isCompactOperator_jetOperator_comp_subtypeL_of_eq_zero [FiniteDimensional ℝ V]
    [CompleteSpace W]
    {G : ℝ × ℝ → V × V × V →L[ℝ] W} (hG : MemLp G ∞ stripMeasure)
    (hval : ∀ᵐ z ∂stripMeasure, ∀ a b : V, G z (0, a, b) = 0) {R : ℝ}
    (hR : ∀ᵐ z ∂stripMeasure, R < |z.1| → G z = 0) :
    IsCompactOperator ((jetOperator stripMeasure G).comp (H1 V).subtypeL) := by
  have hC := ae_le_lpNorm_exponent_top hG
  have hT₀ := isCompactOperator_restrictValue_comp_subtypeL (V := V) R
  exact IsCompactOperator.of_norm_le_mul_norm
    (T₀ := ((restrictValue (V := V) R).comp (H1 V).subtypeL).toLinearMap) hT₀
    (T := ((jetOperator stripMeasure G).comp (H1 V).subtypeL).toLinearMap) fun x ↦
      norm_jetOperator_le_mul_norm_restrictValue hG hval hR lpNorm_nonneg hC x

/-- A coefficient field acting on values only with `‖G z‖ ≤ ε` for `|s| > R` gives an operator on
`H1 V` within `ε` of a compact one: the part of `G` over `[-R, R] × S¹`. -/
private theorem exists_isCompactOperator_norm_jetOperator_comp_subtypeL_sub_le
    [FiniteDimensional ℝ V]
    [CompleteSpace W] {G : ℝ × ℝ → V × V × V →L[ℝ] W} (hG : MemLp G ∞ stripMeasure)
    (hval : ∀ᵐ z ∂stripMeasure, ∀ a b : V, G z (0, a, b) = 0) {ε R : ℝ} (hε : 0 ≤ ε)
    (hR : ∀ᵐ z ∂stripMeasure, R < |z.1| → ‖G z‖ ≤ ε) :
    ∃ K : H1 V →L[ℝ] Lp W 2 stripMeasure, IsCompactOperator K ∧
      ‖(jetOperator stripMeasure G).comp (H1 V).subtypeL - K‖ ≤ ε := by
  set s : Set (ℝ × ℝ) := {z | |z.1| ≤ R}
  have hs : MeasurableSet s := measurableSet_le (continuous_abs.measurable.comp measurable_fst)
    measurable_const
  have hGn : MemLp (s.indicator G) ∞ stripMeasure := hG.indicator hs.nullMeasurableSet
  have hGf : MemLp (sᶜ.indicator G) ∞ stripMeasure := hG.indicator hs.compl.nullMeasurableSet
  have hsplit : jetOperator stripMeasure G =
      jetOperator stripMeasure (s.indicator G) + jetOperator stripMeasure (sᶜ.indicator G) := by
    rw [← jetOperator_add hGn hGf, indicator_self_add_compl]
  refine ⟨(jetOperator stripMeasure (s.indicator G)).comp (H1 V).subtypeL,
    isCompactOperator_jetOperator_comp_subtypeL_of_eq_zero hGn ?_ (R := R) ?_, ?_⟩
  · filter_upwards [hval] with z hz a b
    by_cases h : z ∈ s
    · rw [indicator_of_mem h, hz]
    · rw [indicator_of_notMem h, zero_apply]
  · exact ae_of_all _ fun z hz ↦ indicator_of_notMem (not_le.2 hz) _
  · have hcancel (A B : H1 V →L[ℝ] Lp W 2 stripMeasure) : A + B - A = B := add_sub_cancel_left A B
    rw [hsplit, ContinuousLinearMap.add_comp, hcancel]
    have hbound : ∀ᵐ z ∂stripMeasure, ‖sᶜ.indicator G z‖ ≤ ε := by
      filter_upwards [hR] with z hz
      by_cases h : z ∈ s
      · rw [indicator_of_notMem (notMem_compl_iff.2 h), norm_zero]
        exact hε
      · rw [indicator_of_mem (mem_compl h)]
        exact hz (not_le.1 h)
    exact ContinuousLinearMap.opNorm_le_bound _ hε fun x ↦
      norm_jetOperator_apply_le hGf hbound (x : Lp (V × V × V) 2 stripMeasure)

/-- **Zeroth-order operators with coefficients vanishing at infinity are compact on `W^{1,2}`.**
If the coefficient field `G` acts on values only, `G z (0, a, b) = 0`, and tends to zero as
`|s| → ∞`, in the sense that for every `ε > 0` there is `R` with `‖G z‖ ≤ ε` for `|s| > R`, then
the operator `ξ ↦ (z ↦ G z (ξ z))`, that is `(jetOperator stripMeasure G).comp (H1 V).subtypeL`,
is compact from `H1 V` to `L²`. -/
theorem isCompactOperator_jetOperator_comp_subtypeL_of_tendsto_zero [FiniteDimensional ℝ V]
    [CompleteSpace W]
    {G : ℝ × ℝ → V × V × V →L[ℝ] W} (hG : MemLp G ∞ stripMeasure)
    (hval : ∀ᵐ z ∂stripMeasure, ∀ a b : V, G z (0, a, b) = 0)
    (hlim : ∀ ε > 0, ∃ R, ∀ᵐ z ∂stripMeasure, R < |z.1| → ‖G z‖ ≤ ε) :
    IsCompactOperator ((jetOperator stripMeasure G).comp (H1 V).subtypeL) := by
  refine isClosed_setOfPred_isCompactOperator.closure_subset
    (Metric.mem_closure_iff.2 fun ε hε ↦ ?_)
  obtain ⟨R, hR⟩ := hlim (ε / 2) (half_pos hε)
  obtain ⟨K, hK, hnorm⟩ :=
    exists_isCompactOperator_norm_jetOperator_comp_subtypeL_sub_le hG hval (half_pos hε).le hR
  exact ⟨K, hK, by rw [dist_eq_norm]; linarith⟩

end Operator

/-! ### The parametrix of an operator with invertible models at the ends -/

section Parametrix

/-- The projection `(a, b, c) ↦ (a, 0, 0)` onto the value slot of a jet. -/
private def valueProj : V × V × V →L[ℝ] V × V × V :=
  (ContinuousLinearMap.inl ℝ V (V × V)).comp (ContinuousLinearMap.fst ℝ V (V × V))

variable (V) in
/-- The zeroth-order error `v ↦ a (L - L') (v₁, 0, 0) + b L' (0, v₁, 0)` produced by commuting a
cutoff with an operator `L` whose principal part agrees with that of `L'`. -/
private def errCoeff (a b : ℝ) (L L' : V × V × V →L[ℝ] W) : V × V × V →L[ℝ] W :=
  (a • (L - L') + b • L'.comp (sSlot V)).comp valueProj

private theorem errCoeff_apply (a b : ℝ) (L L' : V × V × V →L[ℝ] W) (v : V × V × V) :
    errCoeff V a b L L' v = a • (L (v.1, 0, 0) - L' (v.1, 0, 0)) + b • L' (0, v.1, 0) := by
  simp [errCoeff, valueProj, Prod.mk_zero_zero]

private theorem errCoeff_apply_zero_fst (a b : ℝ) (L L' : V × V × V →L[ℝ] W) (x y : V) :
    errCoeff V a b L L' (0, x, y) = 0 := by
  simp [errCoeff_apply, Prod.mk_zero_zero]

private theorem norm_errCoeff_le (a b : ℝ) (L L' : V × V × V →L[ℝ] W) :
    ‖errCoeff V a b L L'‖ ≤ |a| * ‖L - L'‖ + |b| * ‖L'‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v ↦ ?_
  have h₁ : ‖((v.1, 0, 0) : V × V × V)‖ ≤ ‖v‖ := by simp [Prod.norm_def]
  have h₂ : ‖((0, v.1, 0) : V × V × V)‖ ≤ ‖v‖ := by simp [Prod.norm_def]
  rw [errCoeff_apply, ← sub_apply]
  calc _ ≤ |a| * (‖L - L'‖ * ‖v‖) + |b| * (‖L'‖ * ‖v‖) := by
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;>
          rw [norm_smul, Real.norm_eq_abs] <;> gcongr
        · exact ((L - L').le_opNorm _).trans (by gcongr)
        · exact (L'.le_opNorm _).trans (by gcongr)
    _ = _ := by ring

private theorem continuous_errCoeff :
    Continuous fun p : ℝ × ℝ × (V × V × V →L[ℝ] W) × (V × V × V →L[ℝ] W) ↦
      errCoeff V p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  unfold errCoeff
  fun_prop

/-- The error coefficient field of a cutoff `χ(s)` with coefficient `b(s)` is essentially bounded
when `χ` and `b` are bounded and continuous. -/
private theorem memLp_errCoeff {χ b : ℝ → ℝ} (hχ : Continuous χ) (hb : Continuous b) {B : ℝ}
    (hχB : ∀ s, |χ s| ≤ B) (hbB : ∀ s, |b s| ≤ B) {M M' : ℝ × ℝ → V × V × V →L[ℝ] W}
    (hM : MemLp M ∞ stripMeasure) (hM' : MemLp M' ∞ stripMeasure) :
    MemLp (fun z ↦ errCoeff V (χ z.1) (b z.1) (M z) (M' z)) ∞ stripMeasure := by
  have hB : 0 ≤ B := (abs_nonneg _).trans (hχB 0)
  refine memLp_top_of_bound (continuous_errCoeff.comp_aestronglyMeasurable
    ((hχ.comp continuous_fst).aestronglyMeasurable.prodMk
      ((hb.comp continuous_fst).aestronglyMeasurable.prodMk
        (hM.aestronglyMeasurable.prodMk hM'.aestronglyMeasurable))))
    (B * (lpNorm M ∞ stripMeasure + lpNorm M' ∞ stripMeasure) + B * lpNorm M' ∞ stripMeasure) ?_
  filter_upwards [ae_le_lpNorm_exponent_top hM, ae_le_lpNorm_exponent_top hM'] with z h h'
  refine (norm_errCoeff_le _ _ _ _).trans (add_le_add ?_ ?_)
  · exact mul_le_mul (hχB _) ((norm_sub_le _ _).trans (add_le_add h h')) (norm_nonneg _) hB
  · exact mul_le_mul (hbB _) h' (norm_nonneg _) hB

/-- If `L` and `L'` agree on `(0, a, b)`, they differ only through the value. -/
private theorem apply_eq_add_sub_apply {L L' : V × V × V →L[ℝ] W}
    (h : ∀ a b : V, L (0, a, b) = L' (0, a, b)) (v : V × V × V) :
    L v = L' v + (L (v.1, 0, 0) - L' (v.1, 0, 0)) := by
  have hv : v = (v.1, 0, 0) + (0, v.2.1, v.2.2) := by ext <;> simp
  have e₁ : L v = L (v.1, 0, 0) + L (0, v.2.1, v.2.2) := by rw [← map_add, ← hv]
  have e₂ : L' v = L' (v.1, 0, 0) + L' (0, v.2.1, v.2.2) := by rw [← map_add, ← hv]
  rw [e₁, e₂, h]
  abel

/-- **Commuting an operator past a cutoff.** If `L` and `L'` agree on `(0, a, b)`, then
`L (β ξ) = β L' ξ + errCoeff`. -/
private theorem apply_cutoffCoeff {L L' : V × V × V →L[ℝ] W}
    (h : ∀ a b : V, L (0, a, b) = L' (0, a, b)) (β : ℝ → ℝ) (z : ℝ × ℝ) (v : V × V × V) :
    L (cutoffCoeff V β z v) = β z.1 • L' v + errCoeff V (β z.1) (deriv β z.1) L L' v := by
  simp only [cutoffCoeff_def, add_apply, smul_apply,
    ContinuousLinearMap.id_apply, sSlot_apply, map_add, map_smul]
  rw [apply_eq_add_sub_apply h v, h, errCoeff_apply, smul_add]
  abel

/-- **Commuting a cutoff past an operator.** If `L` and `L'` agree on `(0, a, b)`, then
`γ L ξ = L' (γ ξ) + errCoeff`. -/
private theorem smul_apply_eq {L L' : V × V × V →L[ℝ] W}
    (h : ∀ a b : V, L (0, a, b) = L' (0, a, b)) (γ : ℝ → ℝ) (z : ℝ × ℝ) (v : V × V × V) :
    γ z.1 • L v = L' (cutoffCoeff V γ z v) + errCoeff V (γ z.1) (-deriv γ z.1) L L' v := by
  rw [apply_cutoffCoeff (fun _ _ ↦ rfl), apply_eq_add_sub_apply h v, errCoeff_apply,
    errCoeff_apply, sub_self, smul_zero, zero_add, smul_add, neg_smul]
  abel

private theorem memLp_comp_fst {γ : ℝ → ℝ} (hγ : Continuous γ) {B : ℝ} (hγB : ∀ s, |γ s| ≤ B) :
    MemLp (fun z : ℝ × ℝ ↦ γ z.1) ∞ stripMeasure :=
  memLp_top_of_bound (hγ.comp continuous_fst).aestronglyMeasurable B
    (ae_of_all _ fun z ↦ by simpa using hγB z.1)

/-- Multiplication by a bounded continuous function `γ(s)`, as an operator on `L²`. -/
private def mulL {γ : ℝ → ℝ} (hγ : Continuous γ) {B : ℝ} (hγB : ∀ s, |γ s| ≤ B) :
    Lp W 2 stripMeasure →L[ℝ] Lp W 2 stripMeasure :=
  Lp.multiplicationOperator ((memLp_comp_fst hγ hγB).toLp _)

private theorem mulL_ae {γ : ℝ → ℝ} (hγ : Continuous γ) {B : ℝ} (hγB : ∀ s, |γ s| ≤ B)
    (η : Lp W 2 stripMeasure) :
    (mulL hγ hγB η : ℝ × ℝ → W) =ᵐ[stripMeasure] fun z ↦ γ z.1 • η z := by
  unfold mulL
  filter_upwards [Lp.multiplicationOperator_ae ((memLp_comp_fst hγ hγB).toLp _) η,
    (memLp_comp_fst hγ hγB).coeFn_toLp] with z h₁ h₂
  rw [h₁, h₂]

variable {M M' : ℝ × ℝ → V × V × V →L[ℝ] W} {β γ : ℝ → ℝ} {B : ℝ}

/-- `D (β ξ) = β D' ξ + errCoeff ξ` on `H1 V`, for `D` and `D'` with equal principal parts. -/
private theorem jetOperator_cutoffL_ae (hM : MemLp M ∞ stripMeasure)
    (hM' : MemLp M' ∞ stripMeasure)
    (hp : ∀ᵐ z ∂stripMeasure, ∀ a b : V, M z (0, a, b) = M' z (0, a, b))
    (hβ : ContDiff ℝ 2 β) (hβB : ∀ s, |β s| ≤ B) (hβ'B : ∀ s, |deriv β s| ≤ B) (y : H1 V) :
    (jetOperator stripMeasure M (cutoffL hβ hβB hβ'B y : Lp (V × V × V) 2 stripMeasure) : ℝ × ℝ → W)
      =ᵐ[stripMeasure] fun z ↦
        β z.1 • jetOperator stripMeasure M' (y : Lp (V × V × V) 2 stripMeasure) z +
        jetOperator stripMeasure (fun z ↦ errCoeff V (β z.1) (deriv β z.1) (M z) (M' z))
          (y : Lp (V × V × V) 2 stripMeasure) z := by
  have hE := memLp_errCoeff hβ.continuous (hβ.continuous_deriv (by norm_num)) hβB hβ'B hM hM'
  filter_upwards [coeFn_jetOperator hM (cutoffL hβ hβB hβ'B y : Lp (V × V × V) 2 stripMeasure),
    coeFn_jetOperator (memLp_cutoffCoeff (hβ.of_le one_le_two) hβB hβ'B)
      (y : Lp (V × V × V) 2 stripMeasure),
    coeFn_jetOperator hM' (y : Lp (V × V × V) 2 stripMeasure),
    coeFn_jetOperator hE (y : Lp (V × V × V) 2 stripMeasure), hp] with z h₁ h₂ h₃ h₄ h₅
  rw [h₁, coe_cutoffL, h₂, h₃, h₄, apply_cutoffCoeff h₅]

/-- `γ D ξ = D' (γ ξ) + errCoeff ξ` on `H1 V`, for `D` and `D'` with equal principal parts. -/
private theorem smul_jetOperator_ae (hM : MemLp M ∞ stripMeasure)
    (hM' : MemLp M' ∞ stripMeasure)
    (hp : ∀ᵐ z ∂stripMeasure, ∀ a b : V, M z (0, a, b) = M' z (0, a, b))
    (hγ : ContDiff ℝ 2 γ) (hγB : ∀ s, |γ s| ≤ B) (hγ'B : ∀ s, |deriv γ s| ≤ B) (x : H1 V) :
    (fun z ↦ γ z.1 • jetOperator stripMeasure M (x : Lp (V × V × V) 2 stripMeasure) z)
      =ᵐ[stripMeasure]
      fun z ↦
        jetOperator stripMeasure M' (cutoffL hγ hγB hγ'B x : Lp (V × V × V) 2 stripMeasure) z +
        jetOperator stripMeasure (fun z ↦ errCoeff V (γ z.1) (-deriv γ z.1) (M z) (M' z))
          (x : Lp (V × V × V) 2 stripMeasure) z := by
  have hE := memLp_errCoeff (b := fun s ↦ -deriv γ s) hγ.continuous
    (hγ.continuous_deriv (by norm_num)).neg hγB
    (fun s ↦ by simpa using hγ'B s) hM hM'
  filter_upwards [coeFn_jetOperator hM (x : Lp (V × V × V) 2 stripMeasure),
    coeFn_jetOperator hM' (cutoffL hγ hγB hγ'B x : Lp (V × V × V) 2 stripMeasure),
    coeFn_jetOperator (memLp_cutoffCoeff (hγ.of_le one_le_two) hγB hγ'B)
      (x : Lp (V × V × V) 2 stripMeasure),
    coeFn_jetOperator hE (x : Lp (V × V × V) 2 stripMeasure), hp] with z h₁ h₂ h₃ h₄ h₅
  rw [h₁, h₂, coe_cutoffL, h₃, h₄, smul_apply_eq h₅]

variable {Mneg Mpos : ℝ × ℝ → V × V × V →L[ℝ] W} {βneg βpos γneg γpos : ℝ → ℝ}

/-- **The right parametrix identity.** With `Q = βneg Qneg γneg + βpos Qpos γpos` built from
right inverses `Qneg`, `Qpos` of the models, `D Q - 1` is the sum of the zeroth-order errors of
commuting `D` past the cutoffs `βneg`, `βpos`. -/
private theorem comp_parametrix_sub_one (hM : MemLp M ∞ stripMeasure)
    (hMneg : MemLp Mneg ∞ stripMeasure) (hMpos : MemLp Mpos ∞ stripMeasure)
    (hpneg : ∀ᵐ z ∂stripMeasure, ∀ a b : V, M z (0, a, b) = Mneg z (0, a, b))
    (hppos : ∀ᵐ z ∂stripMeasure, ∀ a b : V, M z (0, a, b) = Mpos z (0, a, b))
    {Qneg Qpos : Lp W 2 stripMeasure →L[ℝ] H1 V}
    (hQneg : ∀ η, jetOperator stripMeasure Mneg (Qneg η : Lp (V × V × V) 2 stripMeasure) = η)
    (hQpos : ∀ η, jetOperator stripMeasure Mpos (Qpos η : Lp (V × V × V) 2 stripMeasure) = η)
    (hβneg : ContDiff ℝ 2 βneg) (hβnegB : ∀ s, |βneg s| ≤ B) (hβneg'B : ∀ s, |deriv βneg s| ≤ B)
    (hβpos : ContDiff ℝ 2 βpos) (hβposB : ∀ s, |βpos s| ≤ B) (hβpos'B : ∀ s, |deriv βpos s| ≤ B)
    (hγneg : Continuous γneg) (hγnegB : ∀ s, |γneg s| ≤ B) (hγpos : Continuous γpos)
    (hγposB : ∀ s, |γpos s| ≤ B) (hneg : βneg * γneg = γneg) (hpos : βpos * γpos = γpos)
    (h : γneg + γpos = 1) :
    (jetOperator stripMeasure M).comp (H1 V).subtypeL ∘L
        (cutoffL hβneg hβnegB hβneg'B ∘L Qneg ∘L mulL hγneg hγnegB +
          cutoffL hβpos hβposB hβpos'B ∘L Qpos ∘L mulL hγpos hγposB) - 1 =
      (jetOperator stripMeasure fun z ↦
          errCoeff V (βneg z.1) (deriv βneg z.1) (M z) (Mneg z)).comp
          (H1 V).subtypeL ∘L Qneg ∘L mulL hγneg hγnegB +
        (jetOperator stripMeasure fun z ↦
            errCoeff V (βpos z.1) (deriv βpos z.1) (M z) (Mpos z)).comp
          (H1 V).subtypeL ∘L Qpos ∘L mulL hγpos hγposB := by
  ext1 η
  simp only [sub_apply, add_apply, ContinuousLinearMap.comp_apply, one_apply_eq_self,
    Submodule.subtypeL_apply, map_add]
  have eneg :=
    jetOperator_cutoffL_ae hM hMneg hpneg hβneg hβnegB hβneg'B (Qneg (mulL hγneg hγnegB η))
  have epos :=
    jetOperator_cutoffL_ae hM hMpos hppos hβpos hβposB hβpos'B (Qpos (mulL hγpos hγposB η))
  rw [hQneg] at eneg
  rw [hQpos] at epos
  set A := jetOperator stripMeasure M (cutoffL hβneg hβnegB hβneg'B (Qneg (mulL hγneg hγnegB η)) :
    Lp (V × V × V) 2 stripMeasure)
  set A' := jetOperator stripMeasure M (cutoffL hβpos hβposB hβpos'B (Qpos (mulL hγpos hγposB η)) :
    Lp (V × V × V) 2 stripMeasure)
  set E := jetOperator stripMeasure (fun z ↦ errCoeff V (βneg z.1) (deriv βneg z.1) (M z) (Mneg z))
    (Qneg (mulL hγneg hγnegB η) : Lp (V × V × V) 2 stripMeasure)
  set E' := jetOperator stripMeasure (fun z ↦ errCoeff V (βpos z.1) (deriv βpos z.1) (M z) (Mpos z))
    (Qpos (mulL hγpos hγposB η) : Lp (V × V × V) 2 stripMeasure)
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_sub (A + A') η, Lp.coeFn_add A A', Lp.coeFn_add E E', eneg, epos,
    mulL_ae hγneg hγnegB η, mulL_ae hγpos hγposB η] with z h₁ h₂ h₃ h₄ h₅ h₆ h₇
  rw [h₁, Pi.sub_apply, h₂, Pi.add_apply, h₃, Pi.add_apply, h₄, h₅, h₆, h₇, smul_smul,
    ← Pi.mul_apply βneg, hneg, smul_smul, ← Pi.mul_apply βpos, hpos]
  have hη : γneg z.1 • η z + γpos z.1 • η z = η z := by
    rw [← add_smul, ← Pi.add_apply γneg, h, Pi.one_apply, one_smul]
  calc _ = (γneg z.1 • η z + γpos z.1 • η z) - η z + (E z + E' z) := by abel
    _ = _ := by rw [hη, sub_self, zero_add]

/-- Composing two cutoff operators on `H1 V` with `β γ = γ` gives the second one. -/
private theorem cutoffL_cutoffL (hβ : ContDiff ℝ 2 β) (hβB : ∀ s, |β s| ≤ B)
    (hβ'B : ∀ s, |deriv β s| ≤ B) (hγ : ContDiff ℝ 2 γ) (hγB : ∀ s, |γ s| ≤ B)
    (hγ'B : ∀ s, |deriv γ s| ≤ B) (h : β * γ = γ) (x : H1 V) :
    cutoffL hβ hβB hβ'B (cutoffL hγ hγB hγ'B x) = cutoffL hγ hγB hγ'B x := by
  refine Subtype.ext (Lp.ext ?_)
  rw [coe_cutoffL, coe_cutoffL]
  filter_upwards [coeFn_jetOperator (memLp_cutoffCoeff (hβ.of_le one_le_two) hβB hβ'B)
      (jetOperator stripMeasure (cutoffCoeff V γ) (x : Lp (V × V × V) 2 stripMeasure)),
    coeFn_jetOperator (memLp_cutoffCoeff (hγ.of_le one_le_two) hγB hγ'B)
      (x : Lp (V × V × V) 2 stripMeasure)]
    with z h₁ h₂
  rw [h₁, h₂, ← ContinuousLinearMap.comp_apply, cutoffCoeff_comp_cutoffCoeff
    (hβ.differentiable (by norm_num) _) (hγ.differentiable (by norm_num) _), h]

/-- Two cutoff operators on `H1 V` with `γ₁ + γ₂ = 1` add up to the identity. -/
private theorem cutoffL_add_cutoffL {γ₁ γ₂ : ℝ → ℝ} (hγ₁ : ContDiff ℝ 2 γ₁) (hγ₁B : ∀ s, |γ₁ s| ≤ B)
    (hγ₁'B : ∀ s, |deriv γ₁ s| ≤ B) (hγ₂ : ContDiff ℝ 2 γ₂) (hγ₂B : ∀ s, |γ₂ s| ≤ B)
    (hγ₂'B : ∀ s, |deriv γ₂ s| ≤ B) (h : γ₁ + γ₂ = 1) (x : H1 V) :
    cutoffL hγ₁ hγ₁B hγ₁'B x + cutoffL hγ₂ hγ₂B hγ₂'B x = x := by
  refine Subtype.ext (Lp.ext ?_)
  rw [Submodule.coe_add, coe_cutoffL, coe_cutoffL]
  filter_upwards [Lp.coeFn_add
      (jetOperator stripMeasure (cutoffCoeff V γ₁) (x : Lp (V × V × V) 2 stripMeasure))
      (jetOperator stripMeasure (cutoffCoeff V γ₂) (x : Lp (V × V × V) 2 stripMeasure)),
    coeFn_jetOperator (memLp_cutoffCoeff (hγ₁.of_le one_le_two) hγ₁B hγ₁'B)
      (x : Lp (V × V × V) 2 stripMeasure),
    coeFn_jetOperator (memLp_cutoffCoeff (hγ₂.of_le one_le_two) hγ₂B hγ₂'B)
      (x : Lp (V × V × V) 2 stripMeasure)]
    with z h₁ h₂ h₃
  rw [h₁, Pi.add_apply, h₂, h₃, ← add_apply, cutoffCoeff_add_cutoffCoeff
    (hγ₁.differentiable (by norm_num) _) (hγ₂.differentiable (by norm_num) _), h, cutoffCoeff_one,
    ContinuousLinearMap.id_apply]

/-- `γ D x = D' (γ x) + errCoeff x` as elements of `L²`. -/
private theorem mulL_jetOperator (hM : MemLp M ∞ stripMeasure) (hM' : MemLp M' ∞ stripMeasure)
    (hp : ∀ᵐ z ∂stripMeasure, ∀ a b : V, M z (0, a, b) = M' z (0, a, b))
    (hγ : ContDiff ℝ 2 γ) (hγB : ∀ s, |γ s| ≤ B) (hγ'B : ∀ s, |deriv γ s| ≤ B) (x : H1 V) :
    mulL hγ.continuous hγB (jetOperator stripMeasure M (x : Lp (V × V × V) 2 stripMeasure)) =
      jetOperator stripMeasure M' (cutoffL hγ hγB hγ'B x : Lp (V × V × V) 2 stripMeasure) +
        jetOperator stripMeasure (fun z ↦ errCoeff V (γ z.1) (-deriv γ z.1) (M z) (M' z))
          (x : Lp (V × V × V) 2 stripMeasure) := by
  refine Lp.ext ?_
  filter_upwards [mulL_ae hγ.continuous hγB
      (jetOperator stripMeasure M (x : Lp (V × V × V) 2 stripMeasure)),
    smul_jetOperator_ae hM hM' hp hγ hγB hγ'B x, Lp.coeFn_add
      (jetOperator stripMeasure M' (cutoffL hγ hγB hγ'B x : Lp (V × V × V) 2 stripMeasure))
      (jetOperator stripMeasure (fun z ↦ errCoeff V (γ z.1) (-deriv γ z.1) (M z) (M' z))
        (x : Lp (V × V × V) 2 stripMeasure))] with z h₁ h₂ h₃
  rw [h₁, h₂, h₃, Pi.add_apply]

/-- **The left parametrix identity.** With `Q = βneg Qneg γneg + βpos Qpos γpos` built from left
inverses `Qneg`, `Qpos` of the models, `Q D - 1` is the image under `βneg Qneg` and `βpos Qpos` of
the zeroth-order errors of commuting the cutoffs `γneg`, `γpos` past `D`. -/
private theorem parametrix_comp_sub_one (hM : MemLp M ∞ stripMeasure)
    (hMneg : MemLp Mneg ∞ stripMeasure) (hMpos : MemLp Mpos ∞ stripMeasure)
    (hpneg : ∀ᵐ z ∂stripMeasure, ∀ a b : V, M z (0, a, b) = Mneg z (0, a, b))
    (hppos : ∀ᵐ z ∂stripMeasure, ∀ a b : V, M z (0, a, b) = Mpos z (0, a, b))
    {Qneg Qpos : Lp W 2 stripMeasure →L[ℝ] H1 V}
    (hQneg : ∀ x : H1 V,
      Qneg (jetOperator stripMeasure Mneg (x : Lp (V × V × V) 2 stripMeasure)) = x)
    (hQpos : ∀ x : H1 V,
      Qpos (jetOperator stripMeasure Mpos (x : Lp (V × V × V) 2 stripMeasure)) = x)
    (hβneg : ContDiff ℝ 2 βneg) (hβnegB : ∀ s, |βneg s| ≤ B) (hβneg'B : ∀ s, |deriv βneg s| ≤ B)
    (hβpos : ContDiff ℝ 2 βpos) (hβposB : ∀ s, |βpos s| ≤ B) (hβpos'B : ∀ s, |deriv βpos s| ≤ B)
    (hγneg : ContDiff ℝ 2 γneg) (hγnegB : ∀ s, |γneg s| ≤ B) (hγneg'B : ∀ s, |deriv γneg s| ≤ B)
    (hγpos : ContDiff ℝ 2 γpos) (hγposB : ∀ s, |γpos s| ≤ B) (hγpos'B : ∀ s, |deriv γpos s| ≤ B)
    (hneg : βneg * γneg = γneg) (hpos : βpos * γpos = γpos) (h : γneg + γpos = 1) :
    (cutoffL hβneg hβnegB hβneg'B ∘L Qneg ∘L mulL hγneg.continuous hγnegB +
          cutoffL hβpos hβposB hβpos'B ∘L Qpos ∘L mulL hγpos.continuous hγposB) ∘L
        (jetOperator stripMeasure M).comp (H1 V).subtypeL - 1 =
      cutoffL hβneg hβnegB hβneg'B ∘L Qneg ∘L
          (jetOperator stripMeasure fun z ↦
              errCoeff V (γneg z.1) (-deriv γneg z.1) (M z) (Mneg z)).comp
            (H1 V).subtypeL +
        cutoffL hβpos hβposB hβpos'B ∘L Qpos ∘L
          (jetOperator stripMeasure fun z ↦
              errCoeff V (γpos z.1) (-deriv γpos z.1) (M z) (Mpos z)).comp
            (H1 V).subtypeL := by
  ext1 x
  simp only [sub_apply, add_apply, ContinuousLinearMap.comp_apply, one_apply_eq_self,
    Submodule.subtypeL_apply]
  rw [mulL_jetOperator hM hMneg hpneg hγneg hγnegB hγneg'B x,
    mulL_jetOperator hM hMpos hppos hγpos hγposB hγpos'B x]
  simp only [map_add, hQneg, hQpos]
  rw [cutoffL_cutoffL hβneg hβnegB hβneg'B hγneg hγnegB hγneg'B hneg,
    cutoffL_cutoffL hβpos hβposB hβpos'B hγpos hγposB hγpos'B hpos]
  have hx := cutoffL_add_cutoffL hγneg hγnegB hγneg'B hγpos hγposB hγpos'B h x
  calc _ = (cutoffL hγneg hγnegB hγneg'B x + cutoffL hγpos hγposB hγpos'B x) - x +
        (cutoffL hβneg hβnegB hβneg'B (Qneg (jetOperator stripMeasure (fun z ↦
            errCoeff V (γneg z.1) (-deriv γneg z.1) (M z) (Mneg z))
              (x : Lp (V × V × V) 2 stripMeasure))) +
          cutoffL hβpos hβposB hβpos'B (Qpos (jetOperator stripMeasure (fun z ↦
            errCoeff V (γpos z.1) (-deriv γpos z.1) (M z) (Mpos z))
              (x : Lp (V × V × V) 2 stripMeasure)))) := by abel
    _ = _ := by rw [hx, sub_self, zero_add]

/-- An error coefficient field whose cutoff `χ` is bounded by one, whose second coefficient `b`
vanishes for `|s| > 2`, and for which `χ = 0` or `‖M - M'‖ ≤ ε` far out, tends to zero as
`|s| → ∞`. -/
private theorem tendsto_errCoeff {χ b : ℝ → ℝ} (hχ : ∀ s, |χ s| ≤ 1)
    (hb : ∀ s, 2 < |s| → b s = 0)
    (hsmall : ∀ ε > 0, ∃ R, ∀ᵐ z ∂stripMeasure, R < |z.1| → χ z.1 = 0 ∨ ‖M z - M' z‖ ≤ ε) :
    ∀ ε > 0, ∃ R, ∀ᵐ z ∂stripMeasure, R < |z.1| →
      ‖errCoeff V (χ z.1) (b z.1) (M z) (M' z)‖ ≤ ε := by
  intro ε hε
  obtain ⟨R, hR⟩ := hsmall ε hε
  refine ⟨max R 2, ?_⟩
  filter_upwards [hR] with z hz hzR
  refine (norm_errCoeff_le _ _ _ _).trans ?_
  rw [hb _ ((le_max_right _ _).trans_lt hzR), abs_zero, zero_mul, add_zero]
  rcases hz ((le_max_left _ _).trans_lt hzR) with h | h
  · rw [h, abs_zero, zero_mul]
    exact hε.le
  · exact (mul_le_of_le_one_left (norm_nonneg _) (hχ _)).trans h

/-! #### The cutoffs -/

/-- The rising step `s ↦ ψ (s + c)`, for `ψ` the smooth transition function: `0` for `s ≤ -c`
and `1` for `s ≥ 1 - c`. -/
private def stepUp (c s : ℝ) : ℝ := Real.smoothTransition (s + c)

/-- The falling step `s ↦ 1 - ψ (s + c)`. -/
private def stepDown (c s : ℝ) : ℝ := 1 - stepUp c s

/-- A common bound for the steps and their derivatives. -/
private def stepBound : ℝ := max 1 (⨆ s, deriv Real.smoothTransition s)

private theorem contDiff_stepUp (c : ℝ) : ContDiff ℝ 2 (stepUp c) :=
  Real.smoothTransition.contDiff.comp (contDiff_id.add contDiff_const)

private theorem contDiff_stepDown (c : ℝ) : ContDiff ℝ 2 (stepDown c) :=
  contDiff_const.sub (contDiff_stepUp c)

private theorem deriv_stepUp (c s : ℝ) :
    deriv (stepUp c) s = deriv Real.smoothTransition (s + c) :=
  deriv_comp_add_const _ _ _

private theorem deriv_stepDown (c s : ℝ) :
    deriv (stepDown c) s = -deriv Real.smoothTransition (s + c) := by
  unfold stepDown
  rw [deriv_const_sub, deriv_stepUp]

private theorem abs_deriv_smoothTransition_le (x : ℝ) :
    |deriv Real.smoothTransition x| ≤ stepBound := by
  rw [abs_of_nonneg (Real.smoothTransition.deriv_nonneg x)]
  exact (Real.smoothTransition.deriv_le_iSup x).trans (le_max_right _ _)

private theorem abs_stepUp_le_one (c s : ℝ) : |stepUp c s| ≤ 1 :=
  Real.smoothTransition.abs_le_one _

private theorem abs_stepDown_le_one (c s : ℝ) : |stepDown c s| ≤ 1 := by
  unfold stepDown stepUp
  exact abs_le.2 ⟨by linarith [Real.smoothTransition.le_one (s + c)],
    by linarith [Real.smoothTransition.nonneg (s + c)]⟩

private theorem abs_stepUp_le (c s : ℝ) : |stepUp c s| ≤ stepBound :=
  (abs_stepUp_le_one c s).trans (le_max_left _ _)

private theorem abs_stepDown_le (c s : ℝ) : |stepDown c s| ≤ stepBound :=
  (abs_stepDown_le_one c s).trans (le_max_left _ _)

private theorem abs_deriv_stepUp_le (c s : ℝ) : |deriv (stepUp c) s| ≤ stepBound := by
  rw [deriv_stepUp]
  exact abs_deriv_smoothTransition_le _

private theorem abs_deriv_stepDown_le (c s : ℝ) : |deriv (stepDown c) s| ≤ stepBound := by
  rw [deriv_stepDown, abs_neg]
  exact abs_deriv_smoothTransition_le _

/-- The derivative of a step shifted by at most one vanishes for `|s| > 2`. -/
private theorem deriv_smoothTransition_add_eq_zero {c s : ℝ} (hc : |c| ≤ 1) (hs : 2 < |s|) :
    deriv Real.smoothTransition (s + c) = 0 := by
  obtain ⟨hc₁, hc₂⟩ := abs_le.1 hc
  rcases lt_abs.1 hs with hs | hs
  · exact Real.smoothTransition.deriv_of_one_le (by linarith)
  · exact Real.smoothTransition.deriv_of_nonpos (by linarith)

/-- The falling step `stepDown (-1)` is `1` wherever `stepDown 0` is not `0`. -/
private theorem stepDown_mul_stepDown : stepDown (-1) * stepDown 0 = stepDown 0 := by
  funext s
  simp only [Pi.mul_apply, stepDown, stepUp, add_zero]
  rcases le_total s 1 with hs | hs
  · rw [Real.smoothTransition.zero_of_nonpos (show s + -1 ≤ 0 by linarith)]
    ring
  · rw [Real.smoothTransition.one_of_one_le hs]
    ring

/-- The rising step `stepUp 1` is `1` wherever `stepUp 0` is not `0`. -/
private theorem stepUp_mul_stepUp : stepUp 1 * stepUp 0 = stepUp 0 := by
  funext s
  simp only [Pi.mul_apply, stepUp, add_zero]
  rcases le_total 0 s with hs | hs
  · rw [Real.smoothTransition.one_of_one_le (show 1 ≤ s + 1 by linarith)]
    ring
  · rw [Real.smoothTransition.zero_of_nonpos hs]
    ring

private theorem stepDown_add_stepUp : stepDown 0 + stepUp 0 = 1 := by
  funext s
  simp [stepDown, stepUp]

private theorem stepDown_eq_zero {c s : ℝ} (hc : |c| ≤ 1) (hs : 2 < s) : stepDown c s = 0 := by
  rw [stepDown, stepUp, Real.smoothTransition.one_of_one_le (by linarith [(abs_le.1 hc).1]),
    sub_self]

private theorem stepUp_eq_zero {c s : ℝ} (hc : |c| ≤ 1) (hs : s < -2) : stepUp c s = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith [(abs_le.1 hc).2])

private theorem deriv_stepDown_eq_zero {c s : ℝ} (hc : |c| ≤ 1) (hs : 2 < |s|) :
    deriv (stepDown c) s = 0 := by
  rw [deriv_stepDown, deriv_smoothTransition_add_eq_zero hc hs, neg_zero]

private theorem deriv_stepUp_eq_zero {c s : ℝ} (hc : |c| ≤ 1) (hs : 2 < |s|) :
    deriv (stepUp c) s = 0 := by
  rw [deriv_stepUp, deriv_smoothTransition_add_eq_zero hc hs]

/-- Near `s = -∞` the model is close to `M`; near `s = +∞` the cutoff vanishes. -/
private theorem small_of_neg {χ : ℝ → ℝ} (hχ : ∀ s, 2 < s → χ s = 0)
    (hlim : ∀ ε > 0, ∃ R, ∀ᵐ z ∂stripMeasure, z.1 < -R → ‖M z - M' z‖ ≤ ε) :
    ∀ ε > 0, ∃ R, ∀ᵐ z ∂stripMeasure, R < |z.1| → χ z.1 = 0 ∨ ‖M z - M' z‖ ≤ ε := by
  intro ε hε
  obtain ⟨R, hR⟩ := hlim ε hε
  refine ⟨max R 2, ?_⟩
  filter_upwards [hR] with z hz hzR
  rcases lt_abs.1 hzR with h | h
  · exact Or.inl (hχ _ ((le_max_right _ _).trans_lt h))
  · exact Or.inr (hz (by linarith [le_max_left R 2]))

/-- Near `s = +∞` the model is close to `M`; near `s = -∞` the cutoff vanishes. -/
private theorem small_of_pos {χ : ℝ → ℝ} (hχ : ∀ s, s < -2 → χ s = 0)
    (hlim : ∀ ε > 0, ∃ R, ∀ᵐ z ∂stripMeasure, R < z.1 → ‖M z - M' z‖ ≤ ε) :
    ∀ ε > 0, ∃ R, ∀ᵐ z ∂stripMeasure, R < |z.1| → χ z.1 = 0 ∨ ‖M z - M' z‖ ≤ ε := by
  intro ε hε
  obtain ⟨R, hR⟩ := hlim ε hε
  refine ⟨max R 2, ?_⟩
  filter_upwards [hR] with z hz hzR
  rcases lt_abs.1 hzR with h | h
  · exact Or.inr (hz ((le_max_left _ _).trans_lt h))
  · exact Or.inl (hχ _ (by linarith [le_max_right R 2]))

/-- The operators of the error coefficient fields of the steps are compact. -/
private theorem isCompactOperator_errCoeff [FiniteDimensional ℝ V] [CompleteSpace W]
    {χ b : ℝ → ℝ} (hχ : Continuous χ) (hb : Continuous b) (hχ1 : ∀ s, |χ s| ≤ 1)
    (hbB : ∀ s, |b s| ≤ stepBound) (hb0 : ∀ s, 2 < |s| → b s = 0)
    (hM : MemLp M ∞ stripMeasure) (hM' : MemLp M' ∞ stripMeasure)
    (hsmall : ∀ ε > 0, ∃ R, ∀ᵐ z ∂stripMeasure, R < |z.1| → χ z.1 = 0 ∨ ‖M z - M' z‖ ≤ ε) :
    IsCompactOperator
      ((jetOperator stripMeasure fun z ↦ errCoeff V (χ z.1) (b z.1) (M z) (M' z)).comp
      (H1 V).subtypeL) :=
  isCompactOperator_jetOperator_comp_subtypeL_of_tendsto_zero
    (memLp_errCoeff hχ hb (fun s ↦ (hχ1 s).trans (le_max_left _ _)) hbB hM hM')
    (ae_of_all _ fun _ a b ↦ errCoeff_apply_zero_fst _ _ _ _ a b)
    (tendsto_errCoeff hχ1 hb0 hsmall)

/-- The errors of commuting an operator asymptotic to `M'` at `-∞` with the falling steps, in
either direction, are compact. -/
private theorem isCompactOperator_errCoeff_stepDown [FiniteDimensional ℝ V] [CompleteSpace W]
    (hM : MemLp M ∞ stripMeasure) (hM' : MemLp M' ∞ stripMeasure)
    (hlim : ∀ ε > 0, ∃ R, ∀ᵐ z ∂stripMeasure, z.1 < -R → ‖M z - M' z‖ ≤ ε) {c : ℝ}
    (hc : |c| ≤ 1) :
    IsCompactOperator ((jetOperator stripMeasure fun z ↦
        errCoeff V (stepDown c z.1) (deriv (stepDown c) z.1)
        (M z) (M' z)).comp (H1 V).subtypeL) ∧
      IsCompactOperator ((jetOperator stripMeasure fun z ↦ errCoeff V (stepDown c z.1)
        (-deriv (stepDown c) z.1) (M z) (M' z)).comp (H1 V).subtypeL) := by
  have hsmall := small_of_neg (fun s hs ↦ stepDown_eq_zero hc hs) hlim
  have hd := (contDiff_stepDown c).continuous_deriv (by norm_num)
  exact ⟨isCompactOperator_errCoeff (contDiff_stepDown c).continuous hd (abs_stepDown_le_one c)
      (abs_deriv_stepDown_le c) (fun s hs ↦ deriv_stepDown_eq_zero hc hs) hM hM' hsmall,
    isCompactOperator_errCoeff (b := fun s ↦ -deriv (stepDown c) s)
      (contDiff_stepDown c).continuous hd.neg (abs_stepDown_le_one c)
      (fun s ↦ by rw [abs_neg]; exact abs_deriv_stepDown_le c s)
      (fun s hs ↦ by rw [deriv_stepDown_eq_zero hc hs, neg_zero]) hM hM' hsmall⟩

/-- The errors of commuting an operator asymptotic to `M'` at `+∞` with the rising steps, in
either direction, are compact. -/
private theorem isCompactOperator_errCoeff_stepUp [FiniteDimensional ℝ V] [CompleteSpace W]
    (hM : MemLp M ∞ stripMeasure) (hM' : MemLp M' ∞ stripMeasure)
    (hlim : ∀ ε > 0, ∃ R, ∀ᵐ z ∂stripMeasure, R < z.1 → ‖M z - M' z‖ ≤ ε) {c : ℝ}
    (hc : |c| ≤ 1) :
    IsCompactOperator ((jetOperator stripMeasure fun z ↦
        errCoeff V (stepUp c z.1) (deriv (stepUp c) z.1)
        (M z) (M' z)).comp (H1 V).subtypeL) ∧
      IsCompactOperator ((jetOperator stripMeasure fun z ↦ errCoeff V (stepUp c z.1)
        (-deriv (stepUp c) z.1) (M z) (M' z)).comp (H1 V).subtypeL) := by
  have hsmall := small_of_pos (fun s hs ↦ stepUp_eq_zero hc hs) hlim
  have hd := (contDiff_stepUp c).continuous_deriv (by norm_num)
  exact ⟨isCompactOperator_errCoeff (contDiff_stepUp c).continuous hd (abs_stepUp_le_one c)
      (abs_deriv_stepUp_le c) (fun s hs ↦ deriv_stepUp_eq_zero hc hs) hM hM' hsmall,
    isCompactOperator_errCoeff (b := fun s ↦ -deriv (stepUp c) s)
      (contDiff_stepUp c).continuous hd.neg (abs_stepUp_le_one c)
      (fun s ↦ by rw [abs_neg]; exact abs_deriv_stepUp_le c s)
      (fun s hs ↦ by rw [deriv_stepUp_eq_zero hc hs, neg_zero]) hM hM' hsmall⟩

end Parametrix

/-- **Fredholm property on the cylinder from invertible models at the ends.** Let `M` be an
essentially bounded coefficient field on the cylinder, with first-order operator
`D ξ = M (ξ, ∂s ξ, ∂t ξ)` on `W^{1,2}(ℝ × S¹, V)`, and let `Mneg` and `Mpos` be essentially
bounded coefficient fields whose operators `Dneg` and `Dpos` are invertible from
`W^{1,2}(ℝ × S¹, V)` onto `L²(ℝ × S¹, W)`. Suppose that `M` has the same principal part as
`Mneg` and `Mpos`, `M z (0, a, b) = Mneg z (0, a, b) = Mpos z (0, a, b)`, and that `M` is
asymptotic to `Mneg` as `s → -∞` and to `Mpos` as `s → +∞`: for every `ε > 0` there is `R` with
`‖M z - Mneg z‖ ≤ ε` for `s < -R` and `‖M z - Mpos z‖ ≤ ε` for `s > R`. Then `D` is Fredholm.

The theorem applies to the linearized Floer operator `∂s + J₀ ∂t + S(s, t)` along a trajectory
once it is written as a `jetOperator` in a unitary frame and the stationary cylinder operators at
the two asymptotic orbits are shown to be invertible on `W^{1,2}`. -/
theorem isFredholm_jetOperator_comp_subtypeL_of_isInvertible [FiniteDimensional ℝ V]
    [CompleteSpace W] {M Mneg Mpos : ℝ × ℝ → V × V × V →L[ℝ] W} (hM : MemLp M ∞ stripMeasure)
    (hMneg : MemLp Mneg ∞ stripMeasure) (hMpos : MemLp Mpos ∞ stripMeasure)
    (hDneg : ((jetOperator stripMeasure Mneg).comp (H1 V).subtypeL).IsInvertible)
    (hDpos : ((jetOperator stripMeasure Mpos).comp (H1 V).subtypeL).IsInvertible)
    (hpneg : ∀ᵐ z ∂stripMeasure, ∀ a b : V, M z (0, a, b) = Mneg z (0, a, b))
    (hppos : ∀ᵐ z ∂stripMeasure, ∀ a b : V, M z (0, a, b) = Mpos z (0, a, b))
    (hlimneg : ∀ ε > 0, ∃ R, ∀ᵐ z ∂stripMeasure, z.1 < -R → ‖M z - Mneg z‖ ≤ ε)
    (hlimpos : ∀ ε > 0, ∃ R, ∀ᵐ z ∂stripMeasure, R < z.1 → ‖M z - Mpos z‖ ≤ ε) :
    ((jetOperator stripMeasure M).comp (H1 V).subtypeL).IsFredholm := by
  have hc₀ : |(0 : ℝ)| ≤ 1 := by norm_num
  have hc₁ : |(1 : ℝ)| ≤ 1 := by norm_num
  have hc₂ : |(-1 : ℝ)| ≤ 1 := by norm_num
  set D := (jetOperator stripMeasure M).comp (H1 V).subtypeL
  set Qneg := ((jetOperator stripMeasure Mneg).comp (H1 V).subtypeL).inverse
  set Qpos := ((jetOperator stripMeasure Mpos).comp (H1 V).subtypeL).inverse
  -- The cutoffs: `γneg + γpos = 1`, and `βneg`, `βpos` are one on the supports of `γneg`, `γpos`.
  set βneg := cutoffL (V := V) (contDiff_stepDown (-1)) (abs_stepDown_le (-1))
    (abs_deriv_stepDown_le (-1))
  set βpos := cutoffL (V := V) (contDiff_stepUp 1) (abs_stepUp_le 1) (abs_deriv_stepUp_le 1)
  set γneg := mulL (W := W) (contDiff_stepDown 0).continuous (abs_stepDown_le 0)
  set γpos := mulL (W := W) (contDiff_stepUp 0).continuous (abs_stepUp_le 0)
  have hleft : (βneg ∘L Qneg ∘L γneg + βpos ∘L Qpos ∘L γpos) ∘L D - 1 = _ :=
    parametrix_comp_sub_one hM hMneg hMpos hpneg hppos (Qneg := Qneg) (Qpos := Qpos)
      (fun x ↦ hDneg.inverse_apply_self x) (fun x ↦ hDpos.inverse_apply_self x)
      (contDiff_stepDown (-1)) (abs_stepDown_le (-1)) (abs_deriv_stepDown_le (-1))
      (contDiff_stepUp 1) (abs_stepUp_le 1) (abs_deriv_stepUp_le 1)
      (contDiff_stepDown 0) (abs_stepDown_le 0) (abs_deriv_stepDown_le 0)
      (contDiff_stepUp 0) (abs_stepUp_le 0) (abs_deriv_stepUp_le 0)
      stepDown_mul_stepDown stepUp_mul_stepUp stepDown_add_stepUp
  have hright : D ∘L (βneg ∘L Qneg ∘L γneg + βpos ∘L Qpos ∘L γpos) - 1 = _ :=
    comp_parametrix_sub_one hM hMneg hMpos hpneg hppos (Qneg := Qneg) (Qpos := Qpos)
      (fun η ↦ hDneg.self_apply_inverse η) (fun η ↦ hDpos.self_apply_inverse η)
      (contDiff_stepDown (-1)) (abs_stepDown_le (-1)) (abs_deriv_stepDown_le (-1))
      (contDiff_stepUp 1) (abs_stepUp_le 1) (abs_deriv_stepUp_le 1)
      (contDiff_stepDown 0).continuous (abs_stepDown_le 0)
      (contDiff_stepUp 0).continuous (abs_stepUp_le 0)
      stepDown_mul_stepDown stepUp_mul_stepUp stepDown_add_stepUp
  have hKneg := (isCompactOperator_errCoeff_stepDown hM hMneg hlimneg hc₀).2
  have hKpos := (isCompactOperator_errCoeff_stepUp hM hMpos hlimpos hc₀).2
  have hK'neg := (isCompactOperator_errCoeff_stepDown hM hMneg hlimneg hc₂).1
  have hK'pos := (isCompactOperator_errCoeff_stepUp hM hMpos hlimpos hc₁).1
  refine ContinuousLinearMap.IsFredholm.of_isCompactOperator_comp_sub_one
    (S := βneg ∘L Qneg ∘L γneg + βpos ∘L Qpos ∘L γpos) ?_ ?_
  · -- `Q D - 1` is the image of the compact errors of commuting `γneg`, `γpos` past `D`.
    rw [hleft, FunLike.coe_add]
    exact ((hKneg.clm_comp Qneg).clm_comp βneg).add ((hKpos.clm_comp Qpos).clm_comp βpos)
  · -- `D Q - 1` is the sum of the compact errors of commuting `D` past `βneg`, `βpos`.
    rw [hright, FunLike.coe_add]
    exact (hK'neg.comp_clm (Qneg ∘L γneg)).add (hK'pos.comp_clm (Qpos ∘L γpos))

end TauCeti.CylinderSobolev
