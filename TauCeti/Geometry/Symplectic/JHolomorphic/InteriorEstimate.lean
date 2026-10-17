/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.Energy.CompactSupport
public import TauCeti.Analysis.Calculus.FDeriv.Smul
import TauCeti.Geometry.Symplectic.CompatibleMetric

/-!
# Interior estimates for a perturbed Cauchy–Riemann operator

For `D_A u = ∂s u + A(z) ∂t u`, small uniform perturbations of a constant compatible complex
structure preserve the homogeneous `L²` estimate. Applying this to a compactly supported cutoff
times `u` gives an interior estimate for arbitrary maps, with an error involving only `u` and
the cutoff derivative. No differentiability of the coefficient field is needed.

The norm is the caller's norm: the hypothesis identifying the associated metric with the inner
product makes the constant complex structure an isometry without installing a new norm instance.
The coefficient field need not itself square to minus one. The directional energy controls the
full differential: for the product norm on the source, its operator norm squared is at most twice
the sum of the squared norms in the two coordinate directions.

The freezing and cutoff argument follows D. McDuff and D. Salamon, *J-holomorphic Curves and
Symplectic Topology*, 2nd ed., AMS Colloquium Publications **52**, 2012, Appendix B.
-/

public section

open MeasureTheory
open scoped RealInnerProductSpace

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]
variable {ω : SymplecticForm V} {J : AlmostComplexStructure V}

variable {u : ℝ × ℝ → V} {A : ℝ × ℝ → V →L[ℝ] V}

/-- A coefficient field within one half of a constant compatible complex structure preserves
the homogeneous `L²` derivative estimate for compactly supported `C²` maps. The constant `4`
is for the squared norms and the normalization `D_A u = ∂s u + A ∂t u`. -/
theorem integral_norm_partialDeriv_sq_le_of_close_complexStructure
    (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) (hA : ContinuousOn A (tsupport u))
    (hu : ContDiff ℝ 2 u) (hc : HasCompactSupport u)
    (hclose : ∀ z ∈ tsupport u, ∀ v, ‖A z v - J v‖ ≤ (1 / 2 : ℝ) * ‖v‖) :
    ∫ z, (‖fderiv ℝ u z stdComplexLineReal‖ ^ 2 +
        ‖fderiv ℝ u z stdComplexLineImag‖ ^ 2) ≤
      4 * ∫ z, ‖fderiv ℝ u z stdComplexLineReal +
        A z (fderiv ℝ u z stdComplexLineImag)‖ ^ 2 := by
  let : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  let s := fun z => fderiv ℝ u z stdComplexLineReal
  let t := fun z => fderiv ℝ u z stdComplexLineImag
  let D := fun z => s z + A z (t z)
  have hs : Continuous s := (hu.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have ht : Continuous t := (hu.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hsc : HasCompactSupport s := hc.fderiv_apply ℝ _
  have htc : HasCompactSupport t := hc.fderiv_apply ℝ _
  -- Fixing the continuity expressions explicitly prevents norm/power elaboration loops.
  -- Integrability needs the coefficients only on the derivative support.
  have hDsub : Function.support (fun z => ‖D z‖ ^ 2) ⊆ tsupport u := fun z hz => by
    contrapose! hz
    simp [Function.mem_support, D, s, t, fderiv_of_notMem_tsupport ℝ hz]
  have hDi : Integrable (fun z => ‖D z‖ ^ 2) volume :=
    (integrableOn_iff_integrable_of_support_subset hDsub).mp <|
      (show ContinuousOn (fun z => ‖D z‖ ^ 2) (tsupport u) from
        (hs.continuousOn.add (hA.clm_apply ht.continuousOn)).norm.pow 2)
        |>.integrableOn_compact' hc (isClosed_tsupport _).measurableSet
  have hti : Integrable (fun z => ‖t z‖ ^ 2) volume :=
    (show Continuous (fun z => ‖t z‖ ^ 2) from ht.norm.pow 2).integrable_of_hasCompactSupport
      (htc.comp_left (g := fun v : V => ‖v‖ ^ 2) (by simp))
  have hsi : Integrable (fun z => ‖s z‖ ^ 2) volume :=
    (show Continuous (fun z => ‖s z‖ ^ 2) from hs.norm.pow 2).integrable_of_hasCompactSupport
      (hsc.comp_left (g := fun v : V => ‖v‖ ^ 2) (by simp))
  have hfixed : Integrable (fun z => ‖s z + J (t z)‖ ^ 2) volume :=
    (show Continuous (fun z => ‖s z + J (t z)‖ ^ 2) from
      (hs.add (J.toLinearMap.continuous_of_finiteDimensional.comp ht)).norm.pow 2)
      |>.integrable_of_hasCompactSupport
        ((hsc.add (htc.comp_left (g := fun v => J v) (by simp))).comp_left
          (g := fun v : V => ‖v‖ ^ 2) (by simp))
  -- Reuse the constant-structure energy identity in the caller's metric.
  have hidentity : ∫ z, (‖s z‖ ^ 2 + ‖t z‖ ^ 2) =
      ∫ z, ‖s z + J (t z)‖ ^ 2 := by
    have h := ω.integral_stdComplexLineEnergyDensity_eq_integral_associatedBilinForm
      (μ := volume) (ω.invariant_of_apply_apply_eq_inner hg) hu hc
    simp only [SymplecticForm.stdComplexLineEnergyDensity_def,
      SymplecticForm.associatedBilinForm_apply, hg, real_inner_self_eq_norm_sq] at h
    exact h
  -- Absorb the small perturbation of the principal part into the derivative energy.
  have hbound (z : ℝ × ℝ) :
      ‖s z + J (t z)‖ ^ 2 ≤ 2 * ‖D z‖ ^ 2 + (1 / 2 : ℝ) * ‖t z‖ ^ 2 := by
    have hpert : ‖A z (t z) - J (t z)‖ ≤ (1 / 2 : ℝ) * ‖t z‖ := by
      by_cases hz : z ∈ tsupport u
      · exact hclose z hz _
      · simp [t, fderiv_of_notMem_tsupport ℝ hz]
    have hnorm : ‖s z + J (t z)‖ ≤ ‖D z‖ + (1 / 2 : ℝ) * ‖t z‖ := by
      calc
        ‖s z + J (t z)‖ = ‖D z - (A z (t z) - J (t z))‖ := by congr 1; simp only [D]; abel
        _ ≤ ‖D z‖ + ‖A z (t z) - J (t z)‖ := norm_sub_le _ _
        _ ≤ _ := add_le_add_right hpert _
    have hsq := mul_self_le_mul_self (norm_nonneg _) hnorm
    nlinarith only [hsq, add_sq_le (a := ‖D z‖) (b := (1 / 2 : ℝ) * ‖t z‖)]
  have hle := integral_mono hfixed
    ((hDi.const_mul 2).add (hti.const_mul (1 / 2 : ℝ))) hbound
  simp only [Pi.add_apply] at hle
  rw [← hidentity, integral_add hsi hti, integral_add (hDi.const_mul 2)
    (hti.const_mul (1 / 2 : ℝ)), integral_const_mul, integral_const_mul] at hle
  have hspos : 0 ≤ ∫ z, ‖s z‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  dsimp [s, t, D] at hle hspos ⊢
  rw [integral_add hsi hti]
  linarith

omit [FiniteDimensional ℝ V] in
private lemma cutoff_defect_density_le {χ : ℝ × ℝ → ℝ}
    (hu : ContDiff ℝ 2 u) (hχ : ContDiff ℝ 2 χ) (z : ℝ × ℝ)
    (hAnorm : ‖A z (u z)‖ ≤ 2 * ‖u z‖) :
    ‖fderiv ℝ (χ • u) z stdComplexLineReal +
      A z (fderiv ℝ (χ • u) z stdComplexLineImag)‖ ^ 2 ≤
      2 * (χ z ^ 2 * ‖fderiv ℝ u z stdComplexLineReal +
        A z (fderiv ℝ u z stdComplexLineImag)‖ ^ 2) +
      16 * (fderiv ℝ χ z stdComplexLineReal ^ 2 +
        fderiv ℝ χ z stdComplexLineImag ^ 2) * ‖u z‖ ^ 2 := by
  let v := χ • u
  let s := fun z => fderiv ℝ u z stdComplexLineReal
  let t := fun z => fderiv ℝ u z stdComplexLineImag
  let a := fun z => fderiv ℝ χ z stdComplexLineReal
  let b := fun z => fderiv ℝ χ z stdComplexLineImag
  let vs := fun z => fderiv ℝ v z stdComplexLineReal
  let vt := fun z => fderiv ℝ v z stdComplexLineImag
  let W := fun z => χ z ^ 2 * ‖s z + A z (t z)‖ ^ 2
  let G := fun z => (a z ^ 2 + b z ^ 2) * ‖u z‖ ^ 2
  let Dv := fun z => ‖vs z + A z (vt z)‖ ^ 2
  have hderiv (z e : ℝ × ℝ) : fderiv ℝ v z e =
      χ z • fderiv ℝ u z e + fderiv ℝ χ z e • u z := by
    simpa only [add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply, add_comm] using
      congrArg (fun L : (ℝ × ℝ) →L[ℝ] V => L e)
        (fderiv_smul (hχ.differentiable (by norm_num) z) (hu.differentiable (by norm_num) z))
  have heq : vs z + A z (vt z) =
      χ z • (s z + A z (t z)) + (a z • u z + b z • A z (u z)) := by
    dsimp [vs, vt, s, t, a, b]
    rw [hderiv, hderiv]
    simp only [map_add, map_smul, smul_add]
    abel
  have hq : ‖a z • u z + b z • A z (u z)‖ ≤
      |a z| * ‖u z‖ + 2 * |b z| * ‖u z‖ := by
    refine (norm_add_le _ _).trans ?_
    simp only [norm_smul, Real.norm_eq_abs]
    simpa only [mul_assoc, mul_left_comm] using
      add_le_add_right (mul_le_mul_of_nonneg_left hAnorm (abs_nonneg (b z))) _
  have hnorm : ‖vs z + A z (vt z)‖ ≤
      |χ z| * ‖s z + A z (t z)‖ +
        (|a z| * ‖u z‖ + 2 * |b z| * ‖u z‖) := by
    rw [heq]
    exact (norm_add_le _ _).trans (by simpa only [norm_smul, Real.norm_eq_abs] using
      (add_le_add_right hq ‖χ z • (s z + A z (t z))‖))
  have hsq := mul_self_le_mul_self (norm_nonneg _) hnorm
  have hgoal : Dv z ≤ 2 * W z + 16 * G z := by
    dsimp [Dv, W, G]
    nlinarith only [hsq, sq_abs (χ z), sq_abs (a z), sq_abs (b z),
      add_sq_le (a := |a z| * ‖u z‖) (b := 2 * |b z| * ‖u z‖),
      add_sq_le (a := |χ z| * ‖s z + A z (t z)‖)
        (b := |a z| * ‖u z‖ + 2 * |b z| * ‖u z‖)]
  simpa only [mul_assoc] using hgoal

/-- An interior `L²` derivative estimate with a compactly supported `C²` cutoff. The coefficient
field is within one half of a constant compatible complex structure on the cutoff support.
The error term uses only the map values and the cutoff derivative, so setting the cutoff to one
on an interior region controls its derivative energy by the defect and values in a larger region.
The constants are explicit coarse constants for squared norms. -/
theorem integral_cutoff_sq_mul_norm_partialDeriv_sq_le
    {χ : ℝ × ℝ → ℝ} (hg : ∀ v w, ω v (J w) = ⟪v, w⟫)
    (hA : ContinuousOn A (tsupport χ)) (hu : ContDiff ℝ 2 u) (hχ : ContDiff ℝ 2 χ)
    (hc : HasCompactSupport χ)
    (hclose : ∀ z ∈ tsupport χ, ∀ v, ‖A z v - J v‖ ≤ (1 / 2 : ℝ) * ‖v‖) :
    ∫ z, χ z ^ 2 * (‖fderiv ℝ u z stdComplexLineReal‖ ^ 2 +
        ‖fderiv ℝ u z stdComplexLineImag‖ ^ 2) ≤
      16 * (∫ z, χ z ^ 2 * ‖fderiv ℝ u z stdComplexLineReal +
        A z (fderiv ℝ u z stdComplexLineImag)‖ ^ 2) +
      130 * ∫ z, (fderiv ℝ χ z stdComplexLineReal ^ 2 +
        fderiv ℝ χ z stdComplexLineImag ^ 2) * ‖u z‖ ^ 2 := by
  let v := χ • u
  let s := fun z => fderiv ℝ u z stdComplexLineReal
  let t := fun z => fderiv ℝ u z stdComplexLineImag
  let a := fun z => fderiv ℝ χ z stdComplexLineReal
  let b := fun z => fderiv ℝ χ z stdComplexLineImag
  let vs := fun z => fderiv ℝ v z stdComplexLineReal
  let vt := fun z => fderiv ℝ v z stdComplexLineImag
  let E := fun z => χ z ^ 2 * (‖s z‖ ^ 2 + ‖t z‖ ^ 2)
  let W := fun z => χ z ^ 2 * ‖s z + A z (t z)‖ ^ 2
  let G := fun z => (a z ^ 2 + b z ^ 2) * ‖u z‖ ^ 2
  let Ev := fun z => ‖vs z‖ ^ 2 + ‖vt z‖ ^ 2
  let Dv := fun z => ‖vs z + A z (vt z)‖ ^ 2
  have hv : ContDiff ℝ 2 v := hχ.smul hu
  have hvc : HasCompactSupport v := hc.smul_right
  have hdu : Continuous (fderiv ℝ u) := hu.continuous_fderiv (by norm_num)
  have hdχ : Continuous (fderiv ℝ χ) := hχ.continuous_fderiv (by norm_num)
  have hs : Continuous s := hdu.clm_apply continuous_const
  have ht : Continuous t := hdu.clm_apply continuous_const
  have ha : Continuous a := hdχ.clm_apply continuous_const
  have hb : Continuous b := hdχ.clm_apply continuous_const
  have hac : HasCompactSupport a := hc.fderiv_apply ℝ _
  have hbc : HasCompactSupport b := hc.fderiv_apply ℝ _
  have hχsq : HasCompactSupport (fun z => χ z ^ 2) :=
    hc.comp_left (g := fun r : ℝ => r ^ 2) (by simp)
  -- Explicit continuity types prevent the norm/power elaboration loop. All fields are
  -- integrable on the compact cutoff support; coefficients elsewhere are irrelevant.
  have hGi : Integrable G volume :=
    (show Continuous G from ((ha.pow 2).add (hb.pow 2)).mul (hu.continuous.norm.pow 2))
      |>.integrable_of_hasCompactSupport
        (((hac.comp_left (g := fun r : ℝ => r ^ 2) (by simp)).add
          (hbc.comp_left (g := fun r : ℝ => r ^ 2) (by simp))).mul_right)
  have hEi : Integrable E volume :=
    (show Continuous E from (hχ.continuous.pow 2).mul ((hs.norm.pow 2).add (ht.norm.pow 2)))
      |>.integrable_of_hasCompactSupport hχsq.mul_right
  have hWsub : Function.support W ⊆ tsupport χ := fun z hz => by
    contrapose! hz
    simp [Function.mem_support, W, image_eq_zero_of_notMem_tsupport hz]
  have hWi : Integrable W volume :=
    (integrableOn_iff_integrable_of_support_subset hWsub).mp <|
      (show ContinuousOn W (tsupport χ) from
        (hχ.continuous.continuousOn.pow 2).mul
          ((hs.continuousOn.add (hA.clm_apply ht.continuousOn)).norm.pow 2))
        |>.integrableOn_compact' hc (isClosed_tsupport _).measurableSet
  have hdv : Continuous (fderiv ℝ v) := hv.continuous_fderiv (by norm_num)
  have hsv : Continuous vs := hdv.clm_apply continuous_const
  have htv : Continuous vt := hdv.clm_apply continuous_const
  have hsvC : HasCompactSupport vs := hvc.fderiv_apply ℝ _
  have htvC : HasCompactSupport vt := hvc.fderiv_apply ℝ _
  have hEvi : Integrable Ev volume :=
    (show Continuous (fun z => ‖vs z‖ ^ 2) from hsv.norm.pow 2).integrable_of_hasCompactSupport
        (hsvC.comp_left (g := fun x : V => ‖x‖ ^ 2) (by simp)) |>.add
      ((show Continuous (fun z => ‖vt z‖ ^ 2) from htv.norm.pow 2).integrable_of_hasCompactSupport
        (htvC.comp_left (g := fun x : V => ‖x‖ ^ 2) (by simp)))
  have hDvsub : Function.support Dv ⊆ tsupport χ := fun z hz => by
    contrapose! hz
    have hzv : z ∉ tsupport v := fun hzv => hz (tsupport_smul_subset_left χ u hzv)
    simp [Function.mem_support, Dv, vs, vt, fderiv_of_notMem_tsupport ℝ hzv]
  have hDvi : Integrable Dv volume :=
    (integrableOn_iff_integrable_of_support_subset hDvsub).mp <|
      (show ContinuousOn Dv (tsupport χ) from
        (hsv.continuousOn.add (hA.clm_apply htv.continuousOn)).norm.pow 2)
        |>.integrableOn_compact' hc (isClosed_tsupport _).measurableSet
  have hderiv (z e : ℝ × ℝ) : fderiv ℝ v z e =
      χ z • fderiv ℝ u z e + fderiv ℝ χ z e • u z := by
    simpa only [add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply, add_comm] using
      congrArg (fun L : (ℝ × ℝ) →L[ℝ] V => L e)
        (fderiv_smul (hχ.differentiable (by norm_num) z) (hu.differentiable (by norm_num) z))
  have henergy (z : ℝ × ℝ) : E z ≤ 2 * Ev z + 2 * G z := by
    simpa only [mul_assoc] using cutoff_sq_mul_norm_fderiv_sq_le
      (hu.differentiable (by norm_num) z) (hχ.differentiable (by norm_num) z)
      stdComplexLineReal stdComplexLineImag
  have hdefect (z : ℝ × ℝ) : Dv z ≤ 2 * W z + 16 * G z := by
    by_cases hz : z ∈ tsupport χ
    · have hAnorm : ‖A z (u z)‖ ≤ 2 * ‖u z‖ := by
        calc
          ‖A z (u z)‖ ≤ ‖A z (u z) - J (u z)‖ + ‖J (u z)‖ := norm_le_norm_sub_add _ _
          _ ≤ (1 / 2 : ℝ) * ‖u z‖ + ‖u z‖ :=
            add_le_add (hclose z hz _)
              (le_of_eq (ω.norm_apply_eq_norm_of_apply_apply_eq_inner hg _))
          _ ≤ _ := by nlinarith [norm_nonneg (u z)]
      simpa only [mul_assoc] using cutoff_defect_density_le hu hχ z hAnorm
    · have hχzero : χ z = 0 := image_eq_zero_of_notMem_tsupport hz
      have hdχzero : fderiv ℝ χ z = 0 := fderiv_of_notMem_tsupport ℝ hz
      dsimp [Dv, W, G, vs, vt, a, b]
      rw [hderiv, hderiv]
      simp [hχzero, hdχzero]
  -- Integrate the pointwise cutoff bounds, then apply the homogeneous estimate to χ • u.
  have hcompact : (∫ z, Ev z) ≤ 4 * ∫ z, Dv z :=
    integral_norm_partialDeriv_sq_le_of_close_complexStructure hg
      (hA.mono (tsupport_smul_subset_left χ u)) hv hvc
      fun z hz => hclose z (tsupport_smul_subset_left χ u hz)
  have hEbound := integral_mono hEi ((hEvi.const_mul 2).add (hGi.const_mul 2)) henergy
  have hDbound := integral_mono hDvi ((hWi.const_mul 2).add (hGi.const_mul 16)) hdefect
  simp only [Pi.add_apply] at hEbound hDbound
  rw [integral_add (hEvi.const_mul 2) (hGi.const_mul 2), integral_const_mul,
    integral_const_mul] at hEbound
  rw [integral_add (hWi.const_mul 2) (hGi.const_mul 16), integral_const_mul,
    integral_const_mul] at hDbound
  dsimp [E, W, G, s, t, a, b] at hEbound hDbound ⊢
  linarith

end TauCeti

end
