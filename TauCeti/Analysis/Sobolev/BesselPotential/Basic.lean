/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.WeakDeriv.TemperedDistribution
public import TauCeti.Analysis.Sobolev.Wkp.Basic
public import Mathlib.Analysis.Distribution.Sobolev
import TauCeti.Analysis.Distribution.SchwartzSpace.Deriv
import TauCeti.Analysis.Distribution.Sobolev
import TauCeti.Analysis.Sobolev.Wkp.LineDeriv
import TauCeti.MeasureTheory.Function.Lp.CastMeasure

/-!
# Bessel-potential and weak-derivative Sobolev spaces agree

This file proves that the Fourier-theoretic and weak-derivative definitions of integer-order
`L²` Sobolev regularity on the whole space agree: for every natural number `k`, a real `L²`
function lies in Mathlib's Bessel-potential space `H^{k,2}(ℝⁿ)` exactly when it is the value of an
element of the weak-derivative Sobolev space `W^{k,2}(ℝⁿ)`.

Both scales are described by first derivatives. A tempered distribution lies in `H^{k+1,2}` when it
lies in `L²` and its directional derivatives lie in `H^{k,2}`
(`TemperedDistribution.memSobolev_natCast_add_one_iff`), and a function lies in `W^{k+1,2}` when
its directional weak derivatives lie in `W^{k,2}`
(`TauCeti.Wkp.exists_value_eq_iff_forall_exists_hasWeakLineDerivOn`). On the whole space, weak
derivatives are tempered-distributional derivatives
(`TauCeti.hasWeakLineDerivOn_iff_lineDerivOp_toTemperedDistribution_ofReal_eq`), and an `L²`
derivative of a real function has a real representative. Induction on `k` then matches the two
descriptions.

## Main declarations

* `MeasureTheory.Lp.exists_real_lp_lineDeriv_of_memSobolev_zero`: an order-zero Bessel-potential
  representative of a derivative of a real `Lᵖ` function may be chosen real.
* `MeasureTheory.Lp.memSobolev_natCast_iff_exists_wkp_value_eq`: `H^{k,2}(ℝⁿ) = W^{k,2}(ℝⁿ)` for
  every natural `k`.

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
  intro phi _
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

/-- **Weak-derivative and Bessel-potential Sobolev spaces agree.** At every natural order `k`, a
real `L²` function lies in Mathlib's Bessel-potential space `H^{k,2}(ℝⁿ)` exactly when it is the
value of an element of the weak-derivative Sobolev space `W^{k,2}(ℝⁿ)`. -/
theorem memSobolev_natCast_iff_exists_wkp_value_eq (k : ℕ) (u : Lp ℝ 2 (volume : Measure E)) :
    MemSobolev k 2 (Lp.toTemperedDistribution (Complex.ofRealCLM.compLp u)) ↔
      ∃ w : Wkp volume ⊤ 2 k, (Wkp.value k w : E → ℝ) =ᵐ[volume] u := by
  have hvolume : (volume : Measure E) = volume.restrict ((⊤ : Opens E) : Set E) := by simp
  induction k generalizing u with
  | zero =>
      simp only [CharP.cast_eq_zero]
      exact ⟨fun _ => ⟨castLpₗᵢ (𝕜 := ℝ) hvolume u, .of_forall fun x => by
          rw [Wkp.value_zero]
          exact coeFn_castLpₗᵢ _ _ x⟩,
        fun _ => memSobolev_zero_iff.mpr ⟨_, rfl⟩⟩
  | succ k ih =>
      -- Both sides are characterised by the directional derivatives of `u`: Bessel-potential
      -- regularity by `memSobolev_natCast_add_one_iff`, weak regularity by
      -- `Wkp.exists_value_eq_iff_forall_exists_hasWeakLineDerivOn`. The two notions of derivative
      -- agree by `hasWeakLineDerivOn_iff_lineDerivOp_toTemperedDistribution_ofReal_eq`.
      set uTop : Lp ℝ 2 (volume.restrict ((⊤ : Opens E) : Set E)) :=
        castLpₗᵢ (𝕜 := ℝ) hvolume u
      have hcoe : ∀ x, uTop x = u x := coeFn_castLpₗᵢ hvolume u
      have hvalue : (∃ w : Wkp volume ⊤ 2 (k + 1), (Wkp.value (k + 1) w : E → ℝ) =ᵐ[volume] u) ↔
          ∃ w : Wkp volume ⊤ 2 (k + 1), Wkp.value (k + 1) w = uTop := by
        refine exists_congr fun w => ⟨fun h => Lp.ext ?_, fun h => ?_⟩
        · exact Filter.EventuallyEq.trans (ae_restrict_of_ae h) (.of_forall fun x => (hcoe x).symm)
        · rw [h]
          exact .of_forall hcoe
      rw [Nat.cast_succ, TemperedDistribution.memSobolev_natCast_add_one_iff, hvalue,
        Wkp.exists_value_eq_iff_forall_exists_hasWeakLineDerivOn]
      refine ⟨fun h v => ?_, fun h => ⟨memSobolev_zero_iff.mpr ⟨_, rfl⟩, fun v => ?_⟩⟩
      · -- an `H^k` derivative is an `L²` function, hence by induction the value of a `W^{k,2}`
        -- function
        obtain ⟨u', hu'⟩ :=
          exists_real_lp_lineDeriv_of_memSobolev_zero u v ((h.2 v).mono (Nat.cast_nonneg k))
        obtain ⟨d, hd⟩ := (ih u').mp (hu' ▸ h.2 v)
        refine ⟨d, ?_⟩
        have hline := (hasWeakLineDerivOn_iff_lineDerivOp_toTemperedDistribution_ofReal_eq
          u u' v).mpr hu'
        exact (hline.congr_ae (.of_forall fun x => (hcoe x).symm)).congr_ae_deriv
          (by simpa only [Opens.coe_top, Measure.restrict_univ] using hd.symm)
      · obtain ⟨d, hd⟩ := h v
        set u' : Lp ℝ 2 (volume : Measure E) := castLpₗᵢ (𝕜 := ℝ) hvolume.symm (Wkp.value k d)
        have hline : HasWeakLineDerivOn volume ⊤ u u' v :=
          (hd.congr_ae (.of_forall hcoe)).congr_ae_deriv
            (.of_forall fun x => (coeFn_castLpₗᵢ hvolume.symm _ x).symm)
        rw [(hasWeakLineDerivOn_iff_lineDerivOp_toTemperedDistribution_ofReal_eq u u' v).mp hline]
        exact (ih u').mpr ⟨d, .of_forall fun x => (coeFn_castLpₗᵢ hvolume.symm _ x).symm⟩

end MeasureTheory.Lp
