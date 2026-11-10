/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

/-!
# Examples for interior regularity with Sobolev coefficients

Write `z = s + i t` on `ℂ` and `D ξ = ∂_s ξ + J ∂_t ξ + S ξ` for coefficient fields
`J, S : ℂ → (V →L[ℝ] V)`, where `∂_s ξ z = Dξ(z) 1` and `∂_t ξ z = Dξ(z) I`. Interior regularity
for `D` is proved by differentiating the equation: the first derivatives of a solution solve a
system of the same shape whose coefficients involve the derivatives of `J` and `S`. This file
computes that differentiated system, shows that its coupling term cannot be dropped, and shows
that the constant in an interior estimate for `D` must depend on a bound for `S`.

## Main results

* `TauCeti.crOperator_differentiated_system`: for `ξ` that is `C²` near `z`, `J, S`
  differentiable at `z` and `η = ∂_s ξ + J ∂_t ξ + S ξ`, the pair `Ξ = (∂_s ξ, ∂_t ξ)` solves
  at `z` the equation `∂_s Ξ + J₂ ∂_t Ξ + S₂ Ξ = (∂_s η - (∂_s S) ξ, ∂_t η - (∂_t S) ξ)` with
  `J₂ = diag(J, J)` and `S₂ = [[S, ∂_s J], [0, S + ∂_t J]]`.
* `TauCeti.crOperator_differentiated_system_diag_ne`: for a non-constant complex structure `J`
  on `ℝ²`, the plausible wrong coefficient `S₂ = diag(S, S)` gives a false equation.
* `TauCeti.eLpNorm_partialS_expNegRe`: for `J = i`, `S = m` and `m ≥ 0`, the function
  `ξ = e^{-m s}` solves `D ξ = 0` and `‖∂_s ξ‖_{L^q} = m ‖ξ‖_{L^q}` for every measure, in
  particular on every box `K`.
* `TauCeti.exists_lt_eLpNorm_partialT_expIIm`: for `J = i` and `S = m`, the solutions
  `ξ = e^{i m t}` of `D ξ = 0` show that no constant independent of `m` bounds
  `‖∂_t ξ‖_{L^q(K)}` by `‖ξ‖_{L^q(Ω')}` for `K ⊆ Ω'`, so the constant of an interior estimate
  needs a bound on `‖S‖`.

The exponent arithmetic of the bootstrap is checked in `TauCeti.sobolevExponentLadder_four`, and
`J₂² = -1` whenever `J² = -1` is `TauCeti.prodMap_mul_self_eq_neg_one`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Lemma B.4.4 and Proposition B.4.9.
-/

public section

open Complex MeasureTheory
open scoped ENNReal

namespace TauCeti

/-! ### The differentiated system -/

section Differentiated

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **The differentiated system.** For a map `ξ` that is `C²` near `z`, coefficients `J, S`
differentiable at `z` and `η = ∂_s ξ + J ∂_t ξ + S ξ`, the pair `Ξ = (∂_s ξ, ∂_t ξ)` solves
at `z` the equation `∂_s Ξ + J₂ ∂_t Ξ + S₂ Ξ = (∂_s η - (∂_s S) ξ, ∂_t η - (∂_t S) ξ)` with
`J₂ = diag(J, J)` and `S₂ = [[S, ∂_s J], [0, S + ∂_t J]]`. The off-diagonal `∂_s J` and the
`∂_t J` term come from differentiating the coefficient `J`. -/
theorem crOperator_differentiated_system {ξ η : ℂ → V} {Ξ : ℂ → V × V} {J S : ℂ → V →L[ℝ] V}
    {z : ℂ} (hξ : ContDiffAt ℝ 2 ξ z) (hJ : DifferentiableAt ℝ J z)
    (hS : DifferentiableAt ℝ S z)
    (hη : η = fun w => fderiv ℝ ξ w 1 + J w (fderiv ℝ ξ w I) + S w (ξ w))
    (hΞ : Ξ = fun w => (fderiv ℝ ξ w 1, fderiv ℝ ξ w I)) :
    fderiv ℝ Ξ z 1 + (J z).prodMap (J z) (fderiv ℝ Ξ z I) +
        (((S z).coprod (fderiv ℝ J z 1)).prod
          ((0 : V →L[ℝ] V).coprod (S z + fderiv ℝ J z I))) (Ξ z) =
      (fderiv ℝ η z 1 - fderiv ℝ S z 1 (ξ z), fderiv ℝ η z I - fderiv ℝ S z I (ξ z)) := by
  subst hη hΞ
  set D2 := fderiv ℝ (fderiv ℝ ξ) z
  have hsymm : ∀ v w, D2 v w = D2 w v := hξ.isSymmSndFDerivAt (by simp)
  have hDξ : HasFDerivAt (fderiv ℝ ξ) D2 z :=
    ((hξ.fderiv_right (m := 1) le_rfl).differentiableAt one_ne_zero).hasFDerivAt
  have hξz : HasFDerivAt ξ (fderiv ℝ ξ z) z := (hξ.differentiableAt two_ne_zero).hasFDerivAt
  have hJz : HasFDerivAt J (fderiv ℝ J z) z := hJ.hasFDerivAt
  have hSz : HasFDerivAt S (fderiv ℝ S z) z := hS.hasFDerivAt
  have hpart (u : ℂ) : HasFDerivAt (fun w => fderiv ℝ ξ w u) (D2.flip u) z := by
    simpa using hDξ.clm_apply (hasFDerivAt_const u z)
  have hΞd : HasFDerivAt (fun w => (fderiv ℝ ξ w 1, fderiv ℝ ξ w I))
      ((D2.flip 1).prod (D2.flip I)) z := (hpart 1).prodMk (hpart I)
  have hηd : HasFDerivAt (fun w => fderiv ℝ ξ w 1 + J w (fderiv ℝ ξ w I) + S w (ξ w)) _ z :=
    ((hpart 1).add (hJz.clm_apply (hpart I))).add (hSz.clm_apply hξz)
  rw [hΞd.fderiv, hηd.fderiv]
  ext <;> simp [hsymm 1 I] <;> abel

/-- A non-constant complex structure on `ℝ²`: `J (s + i t) (x, y) = (s x - (1 + s²) y, x - s y)`,
the conjugate of the standard one by the shear `(x, y) ↦ (x + s y, y)`. -/
noncomputable def shearComplexStructure (z : ℂ) : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  z.re • (ContinuousLinearMap.fst ℝ ℝ ℝ).prod (-ContinuousLinearMap.snd ℝ ℝ ℝ) +
    (-ContinuousLinearMap.snd ℝ ℝ ℝ).prod (ContinuousLinearMap.fst ℝ ℝ ℝ) +
    z.re ^ 2 • (-ContinuousLinearMap.snd ℝ ℝ ℝ).prod (0 : ℝ × ℝ →L[ℝ] ℝ)

/-- `J (s + i t) (x, y) = (s x - (1 + s²) y, x - s y)`. -/
@[simp]
theorem shearComplexStructure_apply (z : ℂ) (x : ℝ × ℝ) :
    shearComplexStructure z x = (z.re * x.1 - (1 + z.re ^ 2) * x.2, x.1 - z.re * x.2) := by
  ext <;> simp [shearComplexStructure] <;> ring

/-- `TauCeti.shearComplexStructure` is a complex structure: `J² = -1` at every point. -/
theorem shearComplexStructure_mul_self (z : ℂ) :
    shearComplexStructure z * shearComplexStructure z = -1 := by
  refine ContinuousLinearMap.ext fun x => Prod.ext ?_ ?_ <;>
    simp <;> ring

/-- The plausible wrong coefficient `S₂ = diag(S, S)` fails. Take the non-constant complex
structure `J = TauCeti.shearComplexStructure`, `S = 0` and `ξ (s + i t) = (t, 0)`, so that
`η = J ∂_t ξ` and `diag(S, S) = 0`. Then `∂_s Ξ + J₂ ∂_t Ξ ≠ (∂_s η, ∂_t η)` at `0`: the
`∂_s J` entry of `S₂` cannot be dropped. -/
theorem crOperator_differentiated_system_diag_ne {η : ℂ → ℝ × ℝ} {Ξ : ℂ → (ℝ × ℝ) × (ℝ × ℝ)}
    (hη : η = fun w => fderiv ℝ (fun w : ℂ => (w.im, (0 : ℝ))) w 1 +
      shearComplexStructure w (fderiv ℝ (fun w : ℂ => (w.im, (0 : ℝ))) w I))
    (hΞ : Ξ = fun w => (fderiv ℝ (fun w : ℂ => (w.im, (0 : ℝ))) w 1,
      fderiv ℝ (fun w : ℂ => (w.im, (0 : ℝ))) w I)) :
    fderiv ℝ Ξ 0 1 + (shearComplexStructure 0).prodMap (shearComplexStructure 0)
        (fderiv ℝ Ξ 0 I) ≠ (fderiv ℝ η 0 1, fderiv ℝ η 0 I) := by
  have hξ (w : ℂ) : fderiv ℝ (fun w : ℂ => (w.im, (0 : ℝ))) w = imCLM.prod 0 :=
    (imCLM.prod (0 : ℂ →L[ℝ] ℝ)).fderiv
  have hΞ' : Ξ = fun _ => (((0 : ℝ), (0 : ℝ)), ((1 : ℝ), (0 : ℝ))) := by
    funext w
    simp [hΞ, hξ]
  have hη' : η = fun w => (w.re, 1) := by
    funext w
    simp [hη, hξ]
  have hηd : fderiv ℝ η 0 = reCLM.prod 0 := by
    rw [hη']
    simpa using (reCLM.hasFDerivAt (x := 0)).prodMk (hasFDerivAt_const (1 : ℝ) 0) |>.fderiv
  rw [hΞ', hηd]
  intro h
  simpa using congr($h.1.1)

end Differentiated

/-! ### Uniformity -/

/-- The derivative of `ξ = e^{-m s}`: `Dξ(z) v = -m (Re v) ξ(z)`. -/
theorem fderiv_expNegRe_apply (m : ℝ) (z v : ℂ) :
    fderiv ℝ (fun w : ℂ => (Real.exp (-m * w.re) : ℂ)) z v =
      (-m * v.re : ℂ) * (Real.exp (-m * z.re) : ℂ) := by
  have h := ofRealCLM.hasFDerivAt.comp z ((reCLM.hasFDerivAt (x := z)).const_mul (-m)).exp
  simp only [Function.comp_def, ofRealCLM_apply, reCLM_apply] at h
  rw [h.fderiv]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, smul_apply,
    reCLM_apply, ofRealCLM_apply, smul_eq_mul, ofReal_mul, ofReal_neg]
  ring

/-- For `J = i` and `S = m`, the function `ξ = e^{-m s}` solves `∂_s ξ + i ∂_t ξ + m ξ = 0`. -/
theorem crOperator_expNegRe_eq_zero (m : ℝ) (z : ℂ) :
    fderiv ℝ (fun w : ℂ => (Real.exp (-m * w.re) : ℂ)) z 1 +
        I * fderiv ℝ (fun w : ℂ => (Real.exp (-m * w.re) : ℂ)) z I +
        m * (Real.exp (-m * z.re) : ℂ) = 0 := by
  rw [fderiv_expNegRe_apply, fderiv_expNegRe_apply]
  simp

/-- For `ξ = e^{-m s}` with `m ≥ 0`, `‖∂_s ξ‖_{L^q(μ)} = m ‖ξ‖_{L^q(μ)}` for every exponent
`q` and every measure `μ`, for instance Lebesgue measure restricted to a box `K`. Since `ξ`
solves `D ξ = 0` for `J = i` and `S = m`, on a bounded box `K` of positive Lebesgue measure and
for `1 ≤ q < ∞`, where `0 < ‖ξ‖_{L^q(K)} < ∞`, the ratio `‖ξ‖_{W^{1,q}(K)} / ‖ξ‖_{L^q(K)}` is at
least `m`. -/
theorem eLpNorm_partialS_expNegRe {m : ℝ} (hm : 0 ≤ m) (q : ℝ≥0∞) (μ : Measure ℂ) :
    eLpNorm (fun z => fderiv ℝ (fun w : ℂ => (Real.exp (-m * w.re) : ℂ)) z 1) q μ =
      ENNReal.ofReal m * eLpNorm (fun w : ℂ => (Real.exp (-m * w.re) : ℂ)) q μ := by
  have h : (fun z => fderiv ℝ (fun w : ℂ => (Real.exp (-m * w.re) : ℂ)) z 1) =
      (-m : ℂ) • fun w : ℂ => (Real.exp (-m * w.re) : ℂ) := by
    funext z
    rw [fderiv_expNegRe_apply]
    simp
  rw [h, eLpNorm_const_smul]
  simp [← ofReal_norm, abs_of_nonneg hm]

/-- The derivative of `ξ = e^{i m t}`: `Dξ(z) v = i m (Im v) ξ(z)`. -/
theorem fderiv_expIIm_apply (m : ℝ) (z v : ℂ) :
    fderiv ℝ (fun w : ℂ => cexp ((m * w.im : ℝ) * I)) z v =
      (m * v.im : ℂ) * I * cexp ((m * z.im : ℝ) * I) := by
  have h := (((ofRealCLM ∘L (m • imCLM)).hasFDerivAt (x := z)).mul_const I).cexp
  simp only [ContinuousLinearMap.comp_apply, smul_apply, imCLM_apply, ofRealCLM_apply,
    smul_eq_mul] at h
  rw [h.fderiv]
  simp
  ring

/-- For `J = i` and `S = m`, the function `ξ = e^{i m t}` solves `∂_s ξ + i ∂_t ξ + m ξ = 0`. -/
theorem crOperator_expIIm_eq_zero (m : ℝ) (z : ℂ) :
    fderiv ℝ (fun w : ℂ => cexp ((m * w.im : ℝ) * I)) z 1 +
        I * fderiv ℝ (fun w : ℂ => cexp ((m * w.im : ℝ) * I)) z I +
        m * cexp ((m * z.im : ℝ) * I) = 0 := by
  rw [fderiv_expIIm_apply, fderiv_expIIm_apply]
  simp only [one_im, I_im, ofReal_mul, ofReal_one, ofReal_zero, mul_zero, zero_mul, mul_one,
    zero_add]
  linear_combination (m * cexp (m * z.im * I)) * I_sq

/-- **No uniform constant for unbounded `S`.** For `J = i` and `S = m`, the solutions
`ξ = e^{i m t}` of `D ξ = 0` have `|ξ| = 1` and `|∂_t ξ| = |m|`. So for `K ⊆ Ω'` with
`0 < μ K` and `μ Ω' < ∞`, no constant `C` independent of `m` gives
`‖∂_t ξ‖_{L^q(K)} ≤ C ‖ξ‖_{L^q(Ω')}`: the interior estimate's constant must depend on a bound
for `‖S‖`. -/
theorem exists_lt_eLpNorm_partialT_expIIm {q : ℝ≥0∞} (hq : q ≠ 0) {μ : Measure ℂ}
    {K Ω' : Set ℂ} (hK : μ K ≠ 0) (hKΩ : K ⊆ Ω') (hΩ : μ Ω' ≠ ∞) {C : ℝ≥0∞} (hC : C ≠ ∞) :
    ∃ m : ℝ, C * eLpNorm (fun w : ℂ => cexp ((m * w.im : ℝ) * I)) q (μ.restrict Ω') <
      eLpNorm (fun z => fderiv ℝ (fun w : ℂ => cexp ((m * w.im : ℝ) * I)) z I) q
        (μ.restrict K) := by
  have hΩ0 : μ Ω' ≠ 0 := fun h => hK (measure_mono_null hKΩ h)
  have hKtop : μ K ≠ ∞ := ne_top_of_le_ne_top hΩ (measure_mono hKΩ)
  have hq' : 0 ≤ 1 / q.toReal := by positivity
  set A := μ Ω' ^ (1 / q.toReal)
  set B := μ K ^ (1 / q.toReal)
  have hA : A ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hq' hΩ
  have hB0 : B ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hK) hKtop).ne'
  have hB : B ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hq' hKtop
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt (ENNReal.div_lt_top (ENNReal.mul_ne_top hC hA) hB0).ne
  refine ⟨n, ?_⟩
  have hξ (ν : Measure ℂ) (hν : ν ≠ 0) :
      eLpNorm (fun w : ℂ => cexp (((n : ℝ) * w.im : ℝ) * I)) q ν = ν Set.univ ^ (1 / q.toReal) := by
    rw [eLpNorm_congr_norm_ae (g := fun _ : ℂ => (1 : ℂ))
        (by fun_prop : Continuous fun w : ℂ => cexp (((n : ℝ) * w.im : ℝ) * I)).aestronglyMeasurable
        aestronglyMeasurable_const
        (Filter.Eventually.of_forall fun w => by simp only [norm_exp_ofReal_mul_I, norm_one]),
      eLpNorm_const _ hq hν]
    simp
  have hD : (fun z => fderiv ℝ (fun w : ℂ => cexp (((n : ℝ) * w.im : ℝ) * I)) z I) =
      ((n : ℂ) * I) • fun w : ℂ => cexp (((n : ℝ) * w.im : ℝ) * I) := by
    funext z
    rw [fderiv_expIIm_apply]
    simp
  have hnI : ‖(n : ℂ) * I‖ₑ = n := by simp [← ofReal_norm]
  rw [hD, eLpNorm_const_smul, hξ _ (by simpa using hΩ0), hξ _ (by simpa using hK), hnI]
  simp only [Measure.restrict_apply_univ]
  exact (ENNReal.div_lt_iff (.inl hB0) (.inl hB)).mp hn

end TauCeti
