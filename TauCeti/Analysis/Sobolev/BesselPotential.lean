/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.WeakDeriv.TemperedDistribution
public import TauCeti.Analysis.Sobolev.W1p.Basic
public import Mathlib.Analysis.Distribution.Sobolev
import TauCeti.Analysis.Distribution.SchwartzSpace.Deriv
import TauCeti.Analysis.Distribution.Sobolev
import TauCeti.MeasureTheory.Function.Lp.CastMeasure

/-!
# First-order Bessel-potential and weak-derivative Sobolev spaces agree

This file proves that the Fourier-theoretic and weak-derivative definitions of first-order
`L²` Sobolev regularity on the whole space agree. A real `L²` function lies in Mathlib's
Bessel-potential space `H^{1,2}` exactly when it is the value component of an element of
`W^{1,2}`.

Real representatives of the directional distributional derivatives connect Mathlib's complex
Bessel-potential interface to the real weak-gradient interface. Their values along a finite basis
determine an `E`-valued weak gradient. Conversely, the components of a weak gradient are `L²`
distributional derivatives, so `TemperedDistribution.memSobolev_add_one_iff` places the function
in `H^{1,2}`.

## Main declarations

* `MeasureTheory.Lp.exists_real_lp_lineDeriv_of_memSobolev_zero`: an order-zero Bessel-potential
  representative of a derivative of a real `Lᵖ` function may be chosen real.
* `MeasureTheory.Lp.exists_real_l2_lineDeriv_of_memSobolev_one`: every directional derivative of a
  real `H^{1,2}` function has a real `L²` representative.
* `MeasureTheory.Lp.exists_w1p_value_eq_of_memSobolev_one`: a real `L²` function whose associated
  tempered distribution lies in `H^{1,2}` belongs to weak-derivative `W^{1,2}`.
* `MeasureTheory.Lp.memSobolev_one_of_w1p_value_eq`: conversely, the value component of an element
  of `W^{1,2}` lies in `H^{1,2}`.
* `MeasureTheory.Lp.memSobolev_one_iff_exists_w1p_value_eq`: the two spaces agree.

## References

* L. C. Evans, *Partial Differential Equations*, Chapter 5, §5.8.
* M. Taylor, *Partial Differential Equations I*, Chapter 4.
-/

public section

noncomputable section

namespace MeasureTheory.Lp

open Module TauCeti TemperedDistribution TopologicalSpace
open scoped ENNReal LineDeriv SchwartzMap

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E]

/-- If the derivative in direction `v` of the tempered distribution associated to a real `Lᵖ`
function has Bessel-potential order zero, then it is represented by a real `Lᵖ` function.

This real representative makes the derivative available to the real weak-gradient interface. -/
theorem exists_real_lp_lineDeriv_of_memSobolev_zero {p : ENNReal} [Fact (1 ≤ p)]
    (u : Lp ℝ p (volume : Measure E)) (v : E)
    (h : MemSobolev 0 p
      (∂_{v} (Lp.toTemperedDistribution (Complex.ofRealCLM.compLp u)))) :
    ∃ u' : Lp ℝ p (volume : Measure E),
      ∂_{v} (Lp.toTemperedDistribution (Complex.ofRealCLM.compLp u)) =
        Lp.toTemperedDistribution (Complex.ofRealCLM.compLp u') := by
  obtain ⟨z, hz⟩ := memSobolev_zero_iff.mp h
  let u' : Lp ℝ p (volume : Measure E) := Complex.reCLM.compLp z
  refine ⟨u', ?_⟩
  apply temperedDistribution_ext_real
  intro phi hphi
  have hderiv : ∀ x, ∂_{v} (phi.postcompCLM Complex.ofRealCLM) x =
      Complex.ofReal (lineDeriv ℝ (phi : E → ℝ) x v) := by
    intro x
    simp only [lineDerivOp_postcompCLM, SchwartzMap.postcompCLM_apply,
      Complex.ofRealCLM_apply, SchwartzMap.lineDerivOp_apply]
  have hzphi := congrArg
    (fun T : TemperedDistribution E ℂ => T (phi.postcompCLM Complex.ofRealCLM)) hz
  have hleft : ∂_{v} (Lp.toTemperedDistribution (Complex.ofRealCLM.compLp u))
      (phi.postcompCLM Complex.ofRealCLM) =
      Complex.ofReal (∫ x, -(lineDeriv ℝ (phi : E → ℝ) x v) * u x) := by
    simp only [TemperedDistribution.lineDerivOp_apply_apply,
      Lp.toTemperedDistribution_apply, neg_apply, hderiv]
    rw [← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards [Complex.ofRealCLM.coeFn_compLp u] with x hx
    simp [hx]
  have hright : Lp.toTemperedDistribution (Complex.ofRealCLM.compLp u')
      (phi.postcompCLM Complex.ofRealCLM) =
      Complex.ofReal (∫ x, (phi : E → ℝ) x * u' x) := by
    simp only [Lp.toTemperedDistribution_apply, SchwartzMap.postcompCLM_apply,
      Complex.ofRealCLM_apply]
    rw [← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards [Complex.ofRealCLM.coeFn_compLp u'] with x hx
    simp [hx]
  rw [hleft, hright]
  apply congrArg Complex.ofReal
  have hzphi_re := congrArg Complex.re hzphi
  rw [hleft] at hzphi_re
  simp only [Complex.ofReal_re] at hzphi_re
  calc
    ∫ x, -(lineDeriv ℝ (phi : E → ℝ) x v) * u x =
        (Lp.toTemperedDistribution z (phi.postcompCLM Complex.ofRealCLM)).re := hzphi_re
    _ = ∫ x, (phi : E → ℝ) x * u' x := by
      simp only [Lp.toTemperedDistribution_apply, SchwartzMap.postcompCLM_apply,
        Complex.ofRealCLM_apply]
      let _ : ENNReal.HolderConjugate p (ENNReal.conjExponent p) :=
        ENNReal.HolderConjugate.conjExponent Fact.out
      have hint : Integrable (fun x => (phi x : ℂ) * z x) volume :=
        ((phi.postcompCLM Complex.ofRealCLM).memLp (ENNReal.conjExponent p)).integrable_mul
          (Lp.memLp z)
      simp only [smul_eq_mul]
      -- `Complex.re` is definitionally `RCLike.re` here; expose the latter spelling expected by
      -- `integral_re` before moving the real-part map through the integral.
      change RCLike.re (∫ x, (phi x : ℂ) * z x) = _
      rw [← integral_re hint]
      apply integral_congr_ae
      filter_upwards [Complex.reCLM.coeFn_compLp z] with x hx
      simp [u', hx]

/-- Every directional derivative of a real `H^{1,2}` function has a real `L²` representative.
This is the directional weak-derivative half of the inclusion `H^{1,2} ⊆ W^{1,2}`. -/
theorem exists_real_l2_lineDeriv_of_memSobolev_one
    (u : Lp ℝ 2 (volume : Measure E))
    (h : MemSobolev 1 2 (Lp.toTemperedDistribution (Complex.ofRealCLM.compLp u))) (v : E) :
    ∃ u' : Lp ℝ 2 (volume : Measure E),
      ∂_{v} (Lp.toTemperedDistribution (Complex.ofRealCLM.compLp u)) =
        Lp.toTemperedDistribution (Complex.ofRealCLM.compLp u') :=
  exists_real_lp_lineDeriv_of_memSobolev_zero u v (by simpa using h.lineDerivOp (m := v))

/-- A real `L²` function whose associated tempered distribution belongs to the
Bessel-potential space `H^{1,2}` is the value component of a weak-derivative Sobolev function in
`W^{1,2}(ℝⁿ)`. -/
theorem exists_w1p_value_eq_of_memSobolev_one
    (u : Lp ℝ 2 (volume : Measure E))
    (h : MemSobolev 1 2 (Lp.toTemperedDistribution (Complex.ofRealCLM.compLp u))) :
    ∃ w : W1p volume ⊤ 2, (W1p.value w : E → ℝ) =ᵐ[volume] u := by
  have hvolume : (volume : Measure E) = volume.restrict ((⊤ : Opens E) : Set E) := by simp
  let uTop : Lp ℝ 2 (volume.restrict ((⊤ : Opens E) : Set E)) :=
    castLpₗᵢ (𝕜 := ℝ) hvolume u
  let b := stdOrthonormalBasis ℝ E
  choose u' hu' using fun i => exists_real_l2_lineDeriv_of_memSobolev_one u h (b i)
  let g : Lp E 2 (volume : Measure E) :=
    ∑ i, (ContinuousLinearMap.toSpanSingleton ℝ (b i)).compLp (u' i)
  let gTop : Lp E 2 (volume.restrict ((⊤ : Opens E) : Set E)) :=
    castLpₗᵢ (𝕜 := ℝ) hvolume g
  have hg_apply : ∀ i, (fun x => innerSL ℝ (gTop x) (b i)) =ᵐ[volume] u' i := by
    intro i
    filter_upwards [Lp.coeFn_finsetSum Finset.univ
      (fun j => (ContinuousLinearMap.toSpanSingleton ℝ (b j)).compLp (u' j)),
      ae_all_iff.mpr fun j => (ContinuousLinearMap.toSpanSingleton ℝ (b j)).coeFn_compLp (u' j)]
      with x hsum hcomp
    rw [coeFn_castLpₗᵢ hvolume g x, hsum]
    simp only [Finset.sum_apply]
    rw [innerSL_apply_apply, sum_inner]
    calc
      ∑ j, inner ℝ (((ContinuousLinearMap.toSpanSingleton ℝ (b j)).compLp (u' j)) x)
          (b i) = ∑ j, u' j x * inner ℝ (b j) (b i) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hcomp j, ContinuousLinearMap.toSpanSingleton_apply, inner_smul_left]
        simp
      _ = u' i x := by simp [OrthonormalBasis.inner_eq_ite]
  have hline : ∀ i, HasWeakLineDerivOn volume ⊤ uTop
      (fun x => innerSL ℝ (gTop x) (b i)) (b i) := by
    intro i
    have hi : HasWeakLineDerivOn volume ⊤ u (u' i) (b i) :=
      (hasWeakLineDerivOn_iff_lineDerivOp_toTemperedDistribution_ofReal_eq
        u (u' i) (b i)).mpr (hu' i)
    exact (hi.congr_ae (by
      exact .of_forall fun x => (coeFn_castLpₗᵢ hvolume u x).symm)).congr_ae_deriv
      (by simpa only [Opens.coe_top, Measure.restrict_univ] using (hg_apply i).symm)
  have huTopLocally : LocallyIntegrable (uTop : E → ℝ) volume :=
    ((Lp.memLp u).locallyIntegrable (by norm_num)).congr
      (.of_forall fun x => (coeFn_castLpₗᵢ hvolume u x).symm)
  have huTop : LocallyIntegrableOn (uTop : E → ℝ) ⊤ volume :=
    huTopLocally.locallyIntegrableOn _
  have hweak : HasWeakFDerivOn volume ⊤ uTop (fun x => innerSL ℝ (gTop x)) :=
    b.toBasis.hasWeakFDerivOn_of_forall huTop hline
  refine ⟨W1p.mk uTop gTop hweak, ?_⟩
  rw [W1p.value_mk]
  exact .of_forall fun x => coeFn_castLpₗᵢ hvolume u x

/-- If a real `L²` function is the value component of a weak-derivative Sobolev function in
`W^{1,2}(ℝⁿ)`, then its associated tempered distribution belongs to the Bessel-potential space
`H^{1,2}`. -/
theorem memSobolev_one_of_w1p_value_eq (u : Lp ℝ 2 (volume : Measure E))
    (w : W1p volume ⊤ 2) (hw : (W1p.value w : E → ℝ) =ᵐ[volume] u) :
    MemSobolev 1 2 (Lp.toTemperedDistribution (Complex.ofRealCLM.compLp u)) := by
  have hvolume : (volume : Measure E).restrict ((⊤ : Opens E) : Set E) = volume := by simp
  rw [show (1 : ℝ) = 0 + 1 by norm_num, memSobolev_add_one_iff]
  refine ⟨memSobolev_zero_iff.mpr ⟨_, rfl⟩, fun v => ?_⟩
  let g : Lp ℝ 2 (volume : Measure E) :=
    castLpₗᵢ (𝕜 := ℝ) hvolume ((innerSL ℝ v).compLp (W1p.gradient w))
  have hline : HasWeakLineDerivOn volume ⊤ u g v := by
    refine (((W1p.hasWeakFDerivOn w).hasWeakLineDerivOn v).congr_ae ?_).congr_ae_deriv ?_
    · simpa using hw
    · filter_upwards [(innerSL ℝ v).coeFn_compLp (W1p.gradient w)] with x hx
      rw [coeFn_castLpₗᵢ hvolume, hx, innerSL_apply_apply, innerSL_apply_apply, real_inner_comm]
  rw [(hasWeakLineDerivOn_iff_lineDerivOp_toTemperedDistribution_ofReal_eq u g v).mp hline]
  exact memSobolev_zero_iff.mpr ⟨_, rfl⟩

/-- A real `L²` function lies in the Bessel-potential space `H^{1,2}` exactly when it is the
value component of a weak-derivative Sobolev function in `W^{1,2}(ℝⁿ)`. -/
theorem memSobolev_one_iff_exists_w1p_value_eq (u : Lp ℝ 2 (volume : Measure E)) :
    MemSobolev 1 2 (Lp.toTemperedDistribution (Complex.ofRealCLM.compLp u)) ↔
      ∃ w : W1p volume ⊤ 2, (W1p.value w : E → ℝ) =ᵐ[volume] u :=
  ⟨exists_w1p_value_eq_of_memSobolev_one u, fun ⟨w, hw⟩ => memSobolev_one_of_w1p_value_eq u w hw⟩

end MeasureTheory.Lp
