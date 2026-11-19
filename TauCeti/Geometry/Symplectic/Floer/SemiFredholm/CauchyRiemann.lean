/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.AsymptoticOperator
public import TauCeti.Geometry.Symplectic.JHolomorphic.Energy.VaryingStructure
import TauCeti.Analysis.Normed.Group.Basic
import TauCeti.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Geometry.Symplectic.Floer.AsymptoticOperator.Estimate
import TauCeti.MeasureTheory.Integral.Rectangle
import TauCeti.Topology.Instances.Real.TSupport

/-!
# The semi-Fredholm estimate of real Cauchy–Riemann operators on the cylinder

Let `(V, ω)` be a finite-dimensional symplectic vector space. A real Cauchy–Riemann operator on
the cylinder `ℝ × S¹` with values in `V` is a first-order operator

`P ξ = ∂s ξ + J(z) ∂t ξ + A(z) ξ`

with leading coefficient a family `J(z)` of `ω`-compatible complex structures and a zeroth-order
coefficient `A(z)`, both continuous in the domain point `z = (s, t)`. The linearized Floer
operator along a map `u` has this form, with `J(z) = J(z, u z)` and `A` its zeroth-order part
(`TauCeti.SymplecticForm.floerLinearization_eq_add`), and so does its conjugate `D_u - δ` by an
exponential weight (`TauCeti.SymplecticForm.floerLinearization_exp_smul`). The results here use
only the form of `P`, not that `A` comes from a linearization. This file proves the semi-Fredholm
estimate

`∫ (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ C (∫ ‖P ξ‖² + ∫_{[-T, T] × [0, 1]} ‖ξ‖²)`

for every such operator whose coefficients converge, at both ends of the cylinder, to those of
stationary cylinder operators `∂s + J_t (∂t - S_t)` (`TauCeti.Floer.stationaryCylinderOperator`)
with nondegenerate return maps. With Rellich's theorem on the cylinder, such an estimate gives
finite-dimensional kernel and closed range of the extension of `P` to `W^{1,2}`
(`TauCeti.CylinderSobolev.finiteDimensional_ker_jetOperator_comp_subtypeL`).

* `exists_forall_setIntegral_le_mul_setIntegral_cauchyRiemann_add_of_ends` is the patching
  argument: estimates of `P` on the two ends imply the semi-Fredholm estimate. Cut `ξ` into three
  pieces with cutoffs `β(s)` near `+∞`, near `-∞` and on a compact cylinder; since `P` only
  differentiates the cutoffs in `s`, `P (β ξ) = β P ξ + β' ξ`, and on the compact cylinder the
  `L²` estimate for domain-dependent compatible structures
  (`TauCeti.SymplecticForm.exists_forall_setIntegral_norm_fderiv_sq_le_of_periodic`) applies.
* `exists_mem_forall_setIntegral_le_mul_setIntegral_cauchyRiemann_of_tendstoUniformlyOn` is the
  estimate on an end: if `J(s, t) → J₀(t)` and `A(s, t) → -J₀(t) S(t)` uniformly in `t` along a
  filter `l` of `s`, and `S` is a loop of infinitesimally symplectic maps with nondegenerate
  return map, then `P` controls the `W^{1,2}` norm on finite cylinders far out along `l`. Far
  out, `P` differs from the stationary cylinder operator of `(J₀, S)` by at most
  `ε (‖∂t ξ‖ + ‖ξ‖)`, and the stationary estimate
  (`TauCeti.Floer.exists_forall_setIntegral_le_mul_setIntegral_stationaryCylinderOperator`)
  survives such perturbations
  (`TauCeti.Floer.exists_pos_forall_setIntegral_le_mul_setIntegral_of_norm_sub_le`).
  The passage from the norms `ω(·, J₀(t) ·)` of these estimates to the norm of `V` is
  `TauCeti.SymplecticForm.exists_forall_setIntegral_le_mul_mul_setIntegral_norm_sq_of_le`.
* `exists_forall_setIntegral_le_mul_setIntegral_cauchyRiemann_add_of_tendstoUniformlyOn` combines
  the two: the semi-Fredholm estimate of `P` when its coefficients converge at `-∞` and at `+∞`.

Sections are `C²` maps `ξ : ℝ × ℝ → V` of period one in `t` that vanish outside a strip
`(a, b) × ℝ`, and the integrals are over the fundamental domain `[a, b] × [0, 1]`.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2, on the Fredholm property of `∂s + J ∂t + S(s, t)` with
  nondegenerate limits.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 3.1
  and Appendix B, on the semi-Fredholm estimate.
-/

public section

open Filter Set Function MeasureTheory Topology ContinuousLinearMap

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ V] in
/-- The `W^{1,2}` energy over `[a', b'] × [0, 1]` of a map vanishing for `s ∉ (a, b)` is its
energy over `[a, b] × [0, 1]`. -/
private theorem setIntegral_sobolev_eq {ξ : ℝ × ℝ → V} {a b a' b' : ℝ}
    (hξ : ∀ s t, s ∉ Ioo a b → ξ (s, t) = 0) (ha : a' ≤ a) (hb : b ≤ b') :
    ∫ z in Icc a' b' ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
        ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2) =
      ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
        ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2) :=
  setIntegral_Icc_prod_eq_of_forall_fst_notMem_eq_zero measurableSet_Icc ha hb fun z hz ↦ by
    have h := eventuallyEq_zero_of_forall_notMem_Ioo_of_fst_notMem_Icc hξ hz
    simp [h.fderiv_eq, h.eq_of_nhds]

omit [FiniteDimensional ℝ V] in
/-- The `L²` norm of `P ξ` over `[a', b'] × [0, 1]`, for `ξ` vanishing for `s ∉ (a, b)`, is its
norm over `[a, b] × [0, 1]`. -/
private theorem setIntegral_norm_cauchyRiemann_sq_eq {J : ℝ × ℝ → AlmostComplexStructure V}
    {A : ℝ × ℝ → V →L[ℝ] V} {ξ : ℝ × ℝ → V} {a b a' b' : ℝ}
    (hξ : ∀ s t, s ∉ Ioo a b → ξ (s, t) = 0) (ha : a' ≤ a) (hb : b ≤ b') :
    ∫ z in Icc a' b' ×ˢ Icc (0 : ℝ) 1,
        ‖fderiv ℝ ξ z stdComplexLineReal + J z (fderiv ℝ ξ z stdComplexLineImag) + A z (ξ z)‖ ^ 2 =
      ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1,
        ‖fderiv ℝ ξ z stdComplexLineReal + J z (fderiv ℝ ξ z stdComplexLineImag) + A z (ξ z)‖ ^ 2 :=
  setIntegral_Icc_prod_eq_of_forall_fst_notMem_eq_zero measurableSet_Icc ha hb fun z hz ↦ by
    have h := eventuallyEq_zero_of_forall_notMem_Ioo_of_fst_notMem_Icc hξ hz
    simp [h.fderiv_eq, h.eq_of_nhds]

omit [FiniteDimensional ℝ V] in
/-- The `W^{1,2}` energy density of a `C¹` map is continuous. -/
private theorem continuous_sobolev {ξ : ℝ × ℝ → V} (hξ : ContDiff ℝ 1 ξ) :
    Continuous fun z ↦ ‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
      ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2 := by
  have := hξ.continuous_fderiv one_ne_zero
  fun_prop

/-- `P ξ` is continuous for a `C¹` map `ξ` and continuous coefficients. -/
private theorem continuous_cauchyRiemann {J : ℝ × ℝ → AlmostComplexStructure V}
    {A : ℝ × ℝ → V →L[ℝ] V} (hJc : Continuous fun z ↦ (J z).toLinearMap.toContinuousLinearMap)
    (hAc : Continuous A) {ξ : ℝ × ℝ → V} (hξ : ContDiff ℝ 1 ξ) :
    Continuous fun z ↦
      fderiv ℝ ξ z stdComplexLineReal + J z (fderiv ℝ ξ z stdComplexLineImag) + A z (ξ z) := by
  have hdξ (v : ℝ × ℝ) : Continuous fun z ↦ fderiv ℝ ξ z v :=
    (hξ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  exact ((hdξ _).add (hJc.clm_apply (hdξ _))).add (hAc.clm_apply hξ.continuous)

omit [FiniteDimensional ℝ V] in
/-- **Multiplying by a cutoff in `s`.** If `β` has derivative `β'` at `s`, the operator
`P = ∂s + J ∂t + A` sends `β(s) ξ` to `β(s) P ξ + β' ξ` at `z = (s, t)`. -/
private theorem cauchyRiemann_smul_fst (J : ℝ × ℝ → AlmostComplexStructure V)
    (A : ℝ × ℝ → V →L[ℝ] V) {ξ : ℝ × ℝ → V} {z : ℝ × ℝ} {β : ℝ → ℝ} {β' : ℝ}
    (hβ : HasDerivAt β β' z.1) (hξ : DifferentiableAt ℝ ξ z) :
    fderiv ℝ (fun w ↦ β w.1 • ξ w) z stdComplexLineReal +
        J z (fderiv ℝ (fun w ↦ β w.1 • ξ w) z stdComplexLineImag) + A z (β z.1 • ξ z) =
      β z.1 • (fderiv ℝ ξ z stdComplexLineReal + J z (fderiv ℝ ξ z stdComplexLineImag) +
        A z (ξ z)) + β' • ξ z := by
  have hd : HasFDerivAt (fun w : ℝ × ℝ ↦ β w.1 • ξ w) _ z :=
    (hβ.hasFDerivAt.comp z hasFDerivAt_fst).smul hξ.hasFDerivAt
  rw [hd.fderiv]
  simp only [Function.comp_apply, add_apply, smul_apply, smulRight_apply,
    ContinuousLinearMap.comp_apply, coe_fst', stdComplexLineReal_fst, toSpanSingleton_apply,
    smul_eq_mul, one_mul, stdComplexLineImag_fst, zero_mul, zero_smul, add_zero, map_smul,
    smul_add]
  abel

/-- **The `L²` norm of `P` on a cut-off section.** For a cutoff `β(s)` with `|β| ≤ 1`,
`|β'| ≤ M` and `β'` supported in `[-T, T]`, the `L²` norm of `P (β ξ) = β P ξ + β' ξ` is
bounded by those of `P ξ` and of `ξ` over `[-T, T] × [0, 1]`. -/
private theorem setIntegral_norm_cauchyRiemann_smul_sq_le {J : ℝ × ℝ → AlmostComplexStructure V}
    {A : ℝ × ℝ → V →L[ℝ] V} (hJc : Continuous fun z ↦ (J z).toLinearMap.toContinuousLinearMap)
    (hAc : Continuous A) {ξ : ℝ × ℝ → V}
    (hξ : ContDiff ℝ 1 ξ) {a b : ℝ} (hξ₀ : ∀ s t, s ∉ Ioo a b → ξ (s, t) = 0)
    {β β' : ℝ → ℝ} (hβ : ∀ s, HasDerivAt β (β' s) s) (hβ'c : Continuous β')
    (hβ₁ : ∀ s, |β s| ≤ 1) {M T : ℝ} (hM : ∀ s, |β' s| ≤ M)
    (hβT : ∀ s, s < -T ∨ T < s → β' s = 0) {a' b' : ℝ} (ha : a' ≤ a) (hb : b ≤ b')
    (hTa : a' ≤ -T) (hTb : T ≤ b') :
    ∫ z in Icc a' b' ×ˢ Icc (0 : ℝ) 1,
        ‖fderiv ℝ (fun w ↦ β w.1 • ξ w) z stdComplexLineReal +
          J z (fderiv ℝ (fun w ↦ β w.1 • ξ w) z stdComplexLineImag) + A z (β z.1 • ξ z)‖ ^ 2 ≤
      2 * (∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1,
          ‖fderiv ℝ ξ z stdComplexLineReal + J z (fderiv ℝ ξ z stdComplexLineImag) +
            A z (ξ z)‖ ^ 2) +
        2 * M ^ 2 * ∫ z in Icc (-T) T ×ˢ Icc (0 : ℝ) 1, ‖ξ z‖ ^ 2 := by
  set P : ℝ × ℝ → V := fun z ↦
    fderiv ℝ ξ z stdComplexLineReal + J z (fderiv ℝ ξ z stdComplexLineImag) + A z (ξ z) with hP
  have hD (z : ℝ × ℝ) : fderiv ℝ (fun w ↦ β w.1 • ξ w) z stdComplexLineReal +
      J z (fderiv ℝ (fun w ↦ β w.1 • ξ w) z stdComplexLineImag) + A z (β z.1 • ξ z) =
      β z.1 • P z + β' z.1 • ξ z :=
    cauchyRiemann_smul_fst J A (hβ z.1) (hξ.differentiable one_ne_zero z)
  have hDc : Continuous P := continuous_cauchyRiemann hJc hAc hξ
  have hβ'ξ : Continuous fun z : ℝ × ℝ ↦ β' z.1 ^ 2 * ‖ξ z‖ ^ 2 := by
    have := hξ.continuous
    fun_prop
  have hI {f : ℝ × ℝ → ℝ} (hf : Continuous f) (p q : ℝ) :
      IntegrableOn f (Icc p q ×ˢ Icc (0 : ℝ) 1) :=
    hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  simp_rw [hD]
  calc _ ≤ ∫ z in Icc a' b' ×ˢ Icc (0 : ℝ) 1,
        (2 * ‖P z‖ ^ 2 + 2 * (β' z.1 ^ 2 * ‖ξ z‖ ^ 2)) := by
        refine setIntegral_mono_on ?_ ?_ (measurableSet_Icc.prod measurableSet_Icc) fun z _ ↦ ?_
        · refine hI ?_ _ _
          have hβc : Continuous β := continuous_iff_continuousAt.2 fun s ↦ (hβ s).continuousAt
          have := hξ.continuous
          fun_prop
        · exact hI (by fun_prop) _ _
        have h : ‖β z.1 • P z + β' z.1 • ξ z‖ ≤ ‖P z‖ + |β' z.1| * ‖ξ z‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
          gcongr
          exact mul_le_of_le_one_left (norm_nonneg _) (hβ₁ z.1)
        calc _ ≤ (‖P z‖ + |β' z.1| * ‖ξ z‖) ^ 2 := by gcongr
          _ ≤ 2 * (‖P z‖ ^ 2 + (|β' z.1| * ‖ξ z‖) ^ 2) := add_sq_le
          _ = _ := by rw [mul_pow, sq_abs]; ring
    _ = 2 * (∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖P z‖ ^ 2) +
          2 * ∫ z in Icc (-T) T ×ˢ Icc (0 : ℝ) 1, β' z.1 ^ 2 * ‖ξ z‖ ^ 2 := by
        rw [integral_add (hI (by fun_prop) _ _) (hI (by fun_prop) _ _), integral_const_mul,
          integral_const_mul, hP, setIntegral_norm_cauchyRiemann_sq_eq hξ₀ ha hb,
          setIntegral_Icc_prod_eq_of_forall_fst_notMem_eq_zero measurableSet_Icc hTa hTb
            fun z hz ↦ by
              rw [mem_Icc, not_and_or, not_le, not_le] at hz
              simp [hβT z.1 hz]]
    _ ≤ _ := by
        have h : ∫ z in Icc (-T) T ×ˢ Icc (0 : ℝ) 1, β' z.1 ^ 2 * ‖ξ z‖ ^ 2 ≤
            ∫ z in Icc (-T) T ×ˢ Icc (0 : ℝ) 1, M ^ 2 * ‖ξ z‖ ^ 2 := by
          refine setIntegral_mono_on (hI hβ'ξ _ _) (hI (by have := hξ.continuous; fun_prop) _ _)
            (measurableSet_Icc.prod measurableSet_Icc) fun z _ ↦ ?_
          have h₁ : β' z.1 ^ 2 ≤ M ^ 2 := by
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) (hM z.1) 2
          gcongr
        rw [integral_const_mul] at h
        linarith

omit [FiniteDimensional ℝ V] in
/-- **Splitting the `W^{1,2}` energy.** The energy of `ξ = ξp + ξm + ξ₀` over `[p, q] × [0, 1]` is
at most three times the sum of the energies of the three pieces. -/
private theorem setIntegral_sobolev_le_three_mul_add {ξ ξp ξm ξ₀ : ℝ × ℝ → V}
    (hξp : ContDiff ℝ 2 ξp) (hξm : ContDiff ℝ 2 ξm) (hξ₀ : ContDiff ℝ 2 ξ₀)
    (hsplit : ξ = fun w ↦ ξp w + ξm w + ξ₀ w) (p q : ℝ) :
    ∫ z in Icc p q ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
        ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
      3 * ((∫ z in Icc p q ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ ξp z stdComplexLineReal‖ ^ 2 +
          ‖fderiv ℝ ξp z stdComplexLineImag‖ ^ 2 + ‖ξp z‖ ^ 2)) +
        (∫ z in Icc p q ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ ξm z stdComplexLineReal‖ ^ 2 +
          ‖fderiv ℝ ξm z stdComplexLineImag‖ ^ 2 + ‖ξm z‖ ^ 2)) +
        ∫ z in Icc p q ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ ξ₀ z stdComplexLineReal‖ ^ 2 +
          ‖fderiv ℝ ξ₀ z stdComplexLineImag‖ ^ 2 + ‖ξ₀ z‖ ^ 2)) := by
  have hξ : ContDiff ℝ 2 ξ := hsplit ▸ (hξp.add hξm).add hξ₀
  have hI {f : ℝ × ℝ → ℝ} (hf : Continuous f) :
      IntegrableOn f (Icc p q ×ˢ Icc (0 : ℝ) 1) :=
    hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have := hξp.continuous_fderiv two_ne_zero
  have := hξm.continuous_fderiv two_ne_zero
  have := hξ₀.continuous_fderiv two_ne_zero
  have := hξp.continuous
  have := hξm.continuous
  have := hξ₀.continuous
  -- The pointwise splitting of the energy density.
  have hE (z : ℝ × ℝ) :
      ‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 + ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2 ≤
        3 * ((‖fderiv ℝ ξp z stdComplexLineReal‖ ^ 2 + ‖fderiv ℝ ξp z stdComplexLineImag‖ ^ 2 +
            ‖ξp z‖ ^ 2) +
          (‖fderiv ℝ ξm z stdComplexLineReal‖ ^ 2 + ‖fderiv ℝ ξm z stdComplexLineImag‖ ^ 2 +
            ‖ξm z‖ ^ 2) +
          (‖fderiv ℝ ξ₀ z stdComplexLineReal‖ ^ 2 + ‖fderiv ℝ ξ₀ z stdComplexLineImag‖ ^ 2 +
            ‖ξ₀ z‖ ^ 2)) := by
    have dp := hξp.differentiable two_ne_zero z
    have dm := hξm.differentiable two_ne_zero z
    have d₀ := hξ₀.differentiable two_ne_zero z
    have hval : ξ z = ξp z + ξm z + ξ₀ z := congrFun hsplit z
    have hder : fderiv ℝ ξ z = fderiv ℝ ξp z + fderiv ℝ ξm z + fderiv ℝ ξ₀ z := by
      rw [hsplit, fderiv_fun_add (dp.fun_add dm) d₀, fderiv_fun_add dp dm]
    rw [hval, hder]
    simp only [add_apply]
    linarith [norm_add_add_sq_le_three_mul (fderiv ℝ ξp z stdComplexLineReal)
      (fderiv ℝ ξm z stdComplexLineReal) (fderiv ℝ ξ₀ z stdComplexLineReal),
      norm_add_add_sq_le_three_mul (fderiv ℝ ξp z stdComplexLineImag)
      (fderiv ℝ ξm z stdComplexLineImag) (fderiv ℝ ξ₀ z stdComplexLineImag),
      norm_add_add_sq_le_three_mul (ξp z) (ξm z) (ξ₀ z)]
  calc _ ≤ ∫ z in Icc p q ×ˢ Icc (0 : ℝ) 1,
        3 * ((‖fderiv ℝ ξp z stdComplexLineReal‖ ^ 2 +
          ‖fderiv ℝ ξp z stdComplexLineImag‖ ^ 2 + ‖ξp z‖ ^ 2) +
        (‖fderiv ℝ ξm z stdComplexLineReal‖ ^ 2 + ‖fderiv ℝ ξm z stdComplexLineImag‖ ^ 2 +
          ‖ξm z‖ ^ 2) +
        (‖fderiv ℝ ξ₀ z stdComplexLineReal‖ ^ 2 + ‖fderiv ℝ ξ₀ z stdComplexLineImag‖ ^ 2 +
          ‖ξ₀ z‖ ^ 2)) :=
      setIntegral_mono_on (hI (continuous_sobolev (hξ.of_le one_le_two))) (hI (by fun_prop))
        (measurableSet_Icc.prod measurableSet_Icc) fun z _ ↦ hE z
    _ = _ := by
      rw [integral_const_mul, integral_add (hI (by fun_prop))
          (hI (continuous_sobolev (hξ₀.of_le one_le_two))),
        integral_add (hI (continuous_sobolev (hξp.of_le one_le_two)))
          (hI (continuous_sobolev (hξm.of_le one_le_two)))]

/-- **Patching end estimates into the semi-Fredholm estimate.** Let `J(z)` be `ω`-compatible
complex structures and `A(z)` linear maps, both continuous in `z`, and let
`P ξ = ∂s ξ + J(z) ∂t ξ + A(z) ξ`. Suppose that `P` controls the `W^{1,2}` norm on the two ends:
there are constants `Cp`, `Cm` such that every `C²` map `ξ` of period one in `t`, vanishing on two
slices `s = a ≤ b` with `Rp ≤ a`, respectively with `b ≤ Rm`, satisfies
`∫ (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ Cp ∫ ‖P ξ‖²`, respectively `≤ Cm ∫ ‖P ξ‖²`, over
`[a, b] × [0, 1]`. Then there are `C ≥ 0` and `T` such that every `C²` map `ξ` of period one in `t`
vanishing for `s ∉ (a, b)` satisfies

`∫ (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ C (∫ ‖P ξ‖² + ∫_{[-T, T] × [0, 1]} ‖ξ‖²)`

over `[a, b] × [0, 1]`. -/
theorem exists_forall_setIntegral_le_mul_setIntegral_cauchyRiemann_add_of_ends
    (ω : SymplecticForm V) {J : ℝ × ℝ → AlmostComplexStructure V} {A : ℝ × ℝ → V →L[ℝ] V}
    (hJ : ∀ z, ω.Compatible (J z))
    (hJc : Continuous fun z ↦ (J z).toLinearMap.toContinuousLinearMap) (hAc : Continuous A)
    {Cp Cm Rp Rm : ℝ}
    (hp : ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → (∀ s t, ξ (s, t + 1) = ξ (s, t)) →
      ∀ ⦃a b : ℝ⦄, Rp ≤ a → a ≤ b → (∀ t, ξ (a, t) = 0) → (∀ t, ξ (b, t) = 0) →
        ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
          Cp * ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖fderiv ℝ ξ z stdComplexLineReal +
            J z (fderiv ℝ ξ z stdComplexLineImag) + A z (ξ z)‖ ^ 2)
    (hm : ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → (∀ s t, ξ (s, t + 1) = ξ (s, t)) →
      ∀ ⦃a b : ℝ⦄, a ≤ b → b ≤ Rm → (∀ t, ξ (a, t) = 0) → (∀ t, ξ (b, t) = 0) →
        ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
          Cm * ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖fderiv ℝ ξ z stdComplexLineReal +
            J z (fderiv ℝ ξ z stdComplexLineImag) + A z (ξ z)‖ ^ 2) :
    ∃ C, 0 ≤ C ∧ ∃ T, ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → (∀ s t, ξ (s, t + 1) = ξ (s, t)) →
      ∀ ⦃a b : ℝ⦄, a ≤ b → (∀ s t, s ∉ Ioo a b → ξ (s, t) = 0) →
        ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
          C * ((∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖fderiv ℝ ξ z stdComplexLineReal +
            J z (fderiv ℝ ξ z stdComplexLineImag) + A z (ξ z)‖ ^ 2) +
            ∫ z in Icc (-T) T ×ˢ Icc (0 : ℝ) 1, ‖ξ z‖ ^ 2) := by
  set R := max (max Rp (-Rm)) 0
  have hR₀ : 0 ≤ R := le_max_right _ _
  have hRp : Rp ≤ R := (le_max_left _ _).trans (le_max_left _ _)
  have hRm : -R ≤ Rm := by
    have := (le_max_right Rp (-Rm)).trans (le_max_left _ (0 : ℝ))
    linarith
  -- The cutoffs `βp`, `βm`, `β₀`, near `+∞`, near `-∞` and on `[-T, T]`, sum to one.
  obtain ⟨M, βp, βm, β₀, hβsum, hβpR, hβmR, hβ₀T, hβ⟩ := exists_cutoffs_add_add_eq_one hR₀
  set T := R + 1
  obtain ⟨hβpc, hβp1, hβpM, hβpT⟩ := hβ βp (by simp)
  obtain ⟨hβmc, hβm1, hβmM, hβmT⟩ := hβ βm (by simp)
  obtain ⟨hβ₀c, hβ₀1, hβ₀M, hβ₀T'⟩ := hβ β₀ (by simp)
  -- The estimate on the compact cylinder `[-T, T] × [0, 1]`.
  obtain ⟨C₀, hC₀, hcore⟩ := exists_forall_setIntegral_norm_fderiv_sq_le_of_periodic
    (a := -T) (b := T) (by linarith) (fun z _ ↦ hJ z) hJc.continuousOn hAc.continuousOn
  set L := 2 + 2 * M ^ 2
  refine ⟨3 * ((max Cp 0 + max Cm 0) * L + C₀ * (L + 1) + 1), by positivity, T,
    fun ξ hξ hper a b hab hξ₀ ↦ ?_⟩
  have hξ₀' (s t : ℝ) (h : s ≤ a ∨ b ≤ s) : ξ (s, t) = 0 :=
    hξ₀ s t fun h' ↦ by rcases h with h | h <;> linarith [h'.1, h'.2]
  have hI {f : ℝ × ℝ → ℝ} (hf : Continuous f) (p q : ℝ) :
      IntegrableOn f (Icc p q ×ˢ Icc (0 : ℝ) 1) :=
    hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  -- The three pieces of `ξ`.
  set ξp : ℝ × ℝ → V := fun w ↦ βp w.1 • ξ w
  set ξm : ℝ × ℝ → V := fun w ↦ βm w.1 • ξ w
  set ξ₀ : ℝ × ℝ → V := fun w ↦ β₀ w.1 • ξ w
  have hξp : ContDiff ℝ 2 ξp := (hβpc.comp contDiff_fst).smul hξ
  have hξm : ContDiff ℝ 2 ξm := (hβmc.comp contDiff_fst).smul hξ
  have hξ₀c : ContDiff ℝ 2 ξ₀ := (hβ₀c.comp contDiff_fst).smul hξ
  have hsplit : ξ = fun w ↦ ξp w + ξm w + ξ₀ w := funext fun w ↦ by
    simp only [ξp, ξm, ξ₀, ← add_smul, hβsum, one_smul]
  -- Each piece vanishes outside a window: near `+∞`, near `-∞`, and in `[-T, T]`.
  have hvp (s t : ℝ) (hs : s ∉ Ioo (max a R) (max b R)) : ξp (s, t) = 0 := by
    rw [mem_Ioo, not_and_or, not_lt, not_lt] at hs
    simp only [ξp]
    rcases hs with hs | hs
    · rcases le_max_iff.1 hs with h | h
      · rw [hξ₀' s t (Or.inl h), smul_zero]
      · rw [hβpR s h, zero_smul]
    · rw [hξ₀' s t (Or.inr (max_le_iff.1 hs).1), smul_zero]
  have hvm (s t : ℝ) (hs : s ∉ Ioo (min a (-R)) (min b (-R))) : ξm (s, t) = 0 := by
    rw [mem_Ioo, not_and_or, not_lt, not_lt] at hs
    simp only [ξm]
    rcases hs with hs | hs
    · rw [hξ₀' s t (Or.inl (le_min_iff.1 hs).1), smul_zero]
    · rcases min_le_iff.1 hs with h | h
      · rw [hξ₀' s t (Or.inr h), smul_zero]
      · rw [hβmR s h, zero_smul]
  have hv₀ (s t : ℝ) (hs : s ∉ Ioo (-T) T) : ξ₀ (s, t) = 0 := by
    simp only [ξ₀, hβ₀T s hs, zero_smul]
  have hper₀ (s t : ℝ) : ξ₀ (s, t + 1) = ξ₀ (s, t) := by simp only [ξ₀, hper]
  -- The window `[a', b'] ⊇ [a, b] ∪ [-T, T]` carrying all the pieces.
  set a' := min a (-T)
  set b' := max b T
  have hrect : MeasurableSet (Icc a' b' ×ˢ Icc (0 : ℝ) 1) :=
    measurableSet_Icc.prod measurableSet_Icc
  set X := ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖fderiv ℝ ξ z stdComplexLineReal +
    J z (fderiv ℝ ξ z stdComplexLineImag) + A z (ξ z)‖ ^ 2
  set Y := ∫ z in Icc (-T) T ×ˢ Icc (0 : ℝ) 1, ‖ξ z‖ ^ 2
  have hX : 0 ≤ X := setIntegral_nonneg (measurableSet_Icc.prod measurableSet_Icc)
    fun _ _ ↦ sq_nonneg _
  have hY : 0 ≤ Y := setIntegral_nonneg (measurableSet_Icc.prod measurableSet_Icc)
    fun _ _ ↦ sq_nonneg _
  have hcut {β : ℝ → ℝ} (hβc : ContDiff ℝ 2 β) (hβ₁ : ∀ s, |β s| ≤ 1)
      (hβM : ∀ s, |deriv β s| ≤ M) (hβT : ∀ s, s < -T ∨ T < s → deriv β s = 0) :
      ∫ z in Icc a' b' ×ˢ Icc (0 : ℝ) 1,
          ‖fderiv ℝ (fun w ↦ β w.1 • ξ w) z stdComplexLineReal +
            J z (fderiv ℝ (fun w ↦ β w.1 • ξ w) z stdComplexLineImag) +
            A z (β z.1 • ξ z)‖ ^ 2 ≤ L * (X + Y) := by
    have h := setIntegral_norm_cauchyRiemann_smul_sq_le hJc hAc
      (hξ.of_le one_le_two) hξ₀ (fun s ↦ (hβc.differentiable two_ne_zero s).hasDerivAt)
      (hβc.continuous_deriv one_le_two) hβ₁ hβM hβT (min_le_left _ _) (le_max_left _ _)
      (min_le_right _ _) (le_max_right _ _)
    nlinarith [mul_nonneg (sq_nonneg M) hX]
  -- The piece near `+∞`.
  have hPp : ∫ z in Icc a' b' ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ ξp z stdComplexLineReal‖ ^ 2 +
      ‖fderiv ℝ ξp z stdComplexLineImag‖ ^ 2 + ‖ξp z‖ ^ 2) ≤ max Cp 0 * (L * (X + Y)) := by
    rw [setIntegral_sobolev_eq (a' := a') (b' := b') hvp
      ((min_le_left _ _).trans (le_max_left _ _)) (max_le_max le_rfl (by linarith))]
    refine (hp hξp (fun s t ↦ by simp only [ξp, hper]) (hRp.trans (le_max_right _ _))
      (max_le_max hab le_rfl) (fun t ↦ hvp _ t fun h ↦ lt_irrefl _ h.1)
      (fun t ↦ hvp _ t fun h ↦ lt_irrefl _ h.2)).trans ?_
    rw [← setIntegral_norm_cauchyRiemann_sq_eq (a' := a') (b' := b') hvp
      ((min_le_left _ _).trans (le_max_left _ _)) (max_le_max le_rfl (by linarith))]
    exact mul_le_mul (le_max_left _ _) (hcut hβpc hβp1 hβpM hβpT)
      (setIntegral_nonneg hrect fun _ _ ↦ sq_nonneg _) (le_max_right _ _)
  -- The piece near `-∞`.
  have hPm : ∫ z in Icc a' b' ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ ξm z stdComplexLineReal‖ ^ 2 +
      ‖fderiv ℝ ξm z stdComplexLineImag‖ ^ 2 + ‖ξm z‖ ^ 2) ≤ max Cm 0 * (L * (X + Y)) := by
    rw [setIntegral_sobolev_eq (a' := a') (b' := b') hvm (min_le_min le_rfl (by linarith))
      ((min_le_left _ _).trans (le_max_left _ _))]
    refine (hm hξm (fun s t ↦ by simp only [ξm, hper]) (min_le_min hab le_rfl)
      ((min_le_right _ _).trans hRm) (fun t ↦ hvm _ t fun h ↦ lt_irrefl _ h.1)
      (fun t ↦ hvm _ t fun h ↦ lt_irrefl _ h.2)).trans ?_
    rw [← setIntegral_norm_cauchyRiemann_sq_eq (a' := a') (b' := b') hvm
      (min_le_min le_rfl (by linarith)) ((min_le_left _ _).trans (le_max_left _ _))]
    exact mul_le_mul (le_max_left _ _) (hcut hβmc hβm1 hβmM hβmT)
      (setIntegral_nonneg hrect fun _ _ ↦ sq_nonneg _) (le_max_right _ _)
  -- The piece on the compact cylinder `[-T, T] × [0, 1]`.
  have hP₀ : ∫ z in Icc a' b' ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ ξ₀ z stdComplexLineReal‖ ^ 2 +
      ‖fderiv ℝ ξ₀ z stdComplexLineImag‖ ^ 2 + ‖ξ₀ z‖ ^ 2) ≤
        C₀ * (L * (X + Y) + (X + Y)) + (X + Y) := by
    have hξ₀1 : Continuous ξ₀ := hξ₀c.continuous
    have hdξ₀ := hξ₀c.continuous_fderiv two_ne_zero
    have hDξ₀ := continuous_cauchyRiemann hJc hAc (hξ₀c.of_le one_le_two)
    rw [setIntegral_sobolev_eq (a' := a') (b' := b') hv₀ (min_le_right _ _) (le_max_right _ _),
      integral_add (hI (by fun_prop) _ _) (hI (by fun_prop) _ _)]
    have hcore' := hcore hξ₀c (fun s _ ↦ by rw [← zero_add (1 : ℝ), hper₀])
      (fun t ↦ hv₀ _ t fun h ↦ lt_irrefl _ h.1) (fun t ↦ hv₀ _ t fun h ↦ lt_irrefl _ h.2)
    rw [integral_add (hI (f := fun z ↦ ‖fderiv ℝ ξ₀ z stdComplexLineReal +
      J z (fderiv ℝ ξ₀ z stdComplexLineImag) + A z (ξ₀ z)‖ ^ 2) (hDξ₀.norm.pow 2) _ _)
      (hI (by fun_prop) _ _)] at hcore'
    have hD₀ : ∫ z in Icc (-T) T ×ˢ Icc (0 : ℝ) 1, ‖fderiv ℝ ξ₀ z stdComplexLineReal +
        J z (fderiv ℝ ξ₀ z stdComplexLineImag) + A z (ξ₀ z)‖ ^ 2 ≤ L * (X + Y) := by
      rw [← setIntegral_norm_cauchyRiemann_sq_eq (a' := a') (b' := b') hv₀
        (min_le_right a _) (le_max_right b _)]
      exact hcut hβ₀c hβ₀1 hβ₀M hβ₀T'
    have hξ₀Y : ∫ z in Icc (-T) T ×ˢ Icc (0 : ℝ) 1, ‖ξ₀ z‖ ^ 2 ≤ Y := by
      refine setIntegral_mono_on (hI (by fun_prop) _ _)
        (hI (by have := hξ.continuous; fun_prop) _ _)
        (measurableSet_Icc.prod measurableSet_Icc) fun z _ ↦ ?_
      simp only [ξ₀, norm_smul, Real.norm_eq_abs]
      gcongr
      exact mul_le_of_le_one_left (norm_nonneg _) (hβ₀1 z.1)
    have h₁ : C₀ * ((∫ z in Icc (-T) T ×ˢ Icc (0 : ℝ) 1, ‖fderiv ℝ ξ₀ z stdComplexLineReal +
        J z (fderiv ℝ ξ₀ z stdComplexLineImag) + A z (ξ₀ z)‖ ^ 2) +
          ∫ z in Icc (-T) T ×ˢ Icc (0 : ℝ) 1, ‖ξ₀ z‖ ^ 2) ≤ C₀ * (L * (X + Y) + (X + Y)) :=
      mul_le_mul_of_nonneg_left (add_le_add hD₀ (hξ₀Y.trans (by linarith))) hC₀
    linarith
  -- Summing the three pieces.
  have hsum := setIntegral_sobolev_le_three_mul_add hξp hξm hξ₀c hsplit a' b'
  rw [setIntegral_sobolev_eq (a' := a') (b' := b') hξ₀ (min_le_left a _) (le_max_left b _)]
    at hsum
  calc _ ≤ _ := hsum
    _ ≤ 3 * (max Cp 0 * (L * (X + Y)) + max Cm 0 * (L * (X + Y)) +
        (C₀ * (L * (X + Y) + (X + Y)) + (X + Y))) := by gcongr
    _ = _ := by ring


/-- **The estimate on an end.** Let `J₀(t)` be `ω`-compatible complex structures and `S(t)`
infinitesimally symplectic maps, both continuous in `t`, such that the return map
`Ψ(1) = dysonSeriesLeft S 1` of `ζ' = S_t ζ` has `det (1 - Ψ(1)) ≠ 0`. Let `J(z)` be complex
structures and `A(z)` linear maps, both continuous in `z`, with `J(s, t) → J₀(t)` and
`A(s, t) → -J₀(t) S(t)` uniformly for `t ∈ [0, 1]` along a filter `l` of `s`, such as `atTop` for
a positive end or `atBot` for a negative end. Then there are a constant `C ≥ 0` and a set `U ∈ l`
of slices such that every `C²` map `ξ` of period one in `t`, vanishing on the slices `s = a` and
`s = b` with `[a, b] ⊆ U`, satisfies

`∫ (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ C ∫ ‖∂s ξ + J(z) ∂t ξ + A(z) ξ‖²`

over `[a, b] × [0, 1]`. The limit operator is the stationary cylinder operator
`∂s + J₀(t) (∂t - S(t))` of `(J₀, S)`. -/
theorem exists_mem_forall_setIntegral_le_mul_setIntegral_cauchyRiemann_of_tendstoUniformlyOn
    (ω : SymplecticForm V) {J₀ : ℝ → AlmostComplexStructure V} {S : ℝ → V →L[ℝ] V}
    (hJ₀ : ∀ t, ω.Compatible (J₀ t))
    (hJ₀c : Continuous fun t ↦ (J₀ t).toLinearMap.toContinuousLinearMap)
    (hS : ∀ t v w, ω (S t v) w + ω v (S t w) = 0) (hSc : Continuous S)
    (hdet : LinearMap.det ((1 - dysonSeriesLeft S 1 : V →L[ℝ] V) : V →ₗ[ℝ] V) ≠ 0)
    {J : ℝ × ℝ → AlmostComplexStructure V} {A : ℝ × ℝ → V →L[ℝ] V}
    (hJc : Continuous fun z ↦ (J z).toLinearMap.toContinuousLinearMap) (hAc : Continuous A)
    {l : Filter ℝ}
    (hJl : TendstoUniformlyOn (fun s t ↦ (J (s, t)).toLinearMap.toContinuousLinearMap)
      (fun t ↦ (J₀ t).toLinearMap.toContinuousLinearMap) l (Icc 0 1))
    (hAl : TendstoUniformlyOn (fun s t ↦ A (s, t))
      (fun t ↦ -((J₀ t).toLinearMap.toContinuousLinearMap ∘L S t)) l (Icc 0 1)) :
    ∃ C, 0 ≤ C ∧ ∃ U ∈ l, ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ →
      (∀ s t, ξ (s, t + 1) = ξ (s, t)) → ∀ ⦃a b : ℝ⦄, a ≤ b → Icc a b ⊆ U →
      (∀ t, ξ (a, t) = 0) → (∀ t, ξ (b, t) = 0) →
        ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
          C * ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖fderiv ℝ ξ z stdComplexLineReal +
            J z (fderiv ℝ ξ z stdComplexLineImag) + A z (ξ z)‖ ^ 2 := by
  have hJ₀p : Continuous fun p : ℝ × V ↦ J₀ p.1 p.2 :=
    (hJ₀c.comp continuous_fst).clm_apply continuous_snd
  -- The stationary estimate, its stability under small perturbations, and the passage to the
  -- norm of `V`.
  obtain ⟨C₀, hC₀, hest⟩ :=
    Floer.exists_forall_setIntegral_le_mul_setIntegral_stationaryCylinderOperator hJ₀ hJ₀p hS hSc
      hdet
  obtain ⟨ε, hε, C₁, hC₁, hpert⟩ :=
    Floer.exists_pos_forall_setIntegral_le_mul_setIntegral_of_norm_sub_le
      (fun t ↦ (hJ₀ t).tames) hJ₀p hSc hC₀
  obtain ⟨k, hk, hconv⟩ := ω.exists_forall_setIntegral_le_mul_mul_setIntegral_norm_sq_of_le
    (fun t ↦ (hJ₀ t).tames) hJ₀c hSc
  -- Far out along `l`, the coefficients are `ε`-close to their limits.
  refine ⟨k * C₁, by positivity, _, (Metric.tendstoUniformlyOn_iff.1 hJl ε hε).and
    (Metric.tendstoUniformlyOn_iff.1 hAl ε hε), fun ξ hξ hper a b hab hU ha hb ↦ ?_⟩
  have hξ₁ : ContDiff ℝ 1 ξ := hξ.of_le one_le_two
  have hP := (continuous_cauchyRiemann hJc hAc hξ₁).continuousOn
    (s := Icc a b ×ˢ Icc (0 : ℝ) 1)
  refine hconv hξ₁ hP hC₁ (hpert hξ₁ (hest hξ hper hab ha hb) hP ?_)
  rintro ⟨s, t⟩ ⟨hs, ht⟩
  obtain ⟨hJst, hAst⟩ := hU hs
  have hJz := hJst t ht
  have hAz := hAst t ht
  rw [dist_comm, dist_eq_norm] at hJz hAz
  -- `P ξ - D ξ = (J(z) - J₀(t)) ∂t ξ + (A(z) + J₀(t) S(t)) ξ`.
  have hdiff : fderiv ℝ ξ (s, t) stdComplexLineReal +
        J (s, t) (fderiv ℝ ξ (s, t) stdComplexLineImag) + A (s, t) (ξ (s, t)) -
      Floer.stationaryCylinderOperator J₀ S ξ (s, t) =
      ((J (s, t)).toLinearMap.toContinuousLinearMap -
          (J₀ t).toLinearMap.toContinuousLinearMap) (fderiv ℝ ξ (s, t) stdComplexLineImag) +
        (A (s, t) - -((J₀ t).toLinearMap.toContinuousLinearMap ∘L S t)) (ξ (s, t)) := by
    simp only [Floer.stationaryCylinderOperator_def, sub_apply, add_apply,
      LinearMap.coe_toContinuousLinearMap', AlmostComplexStructure.apply_sub, sub_neg_eq_add]
    abel
  rw [hdiff]
  calc _ ≤ ‖(J (s, t)).toLinearMap.toContinuousLinearMap -
          (J₀ t).toLinearMap.toContinuousLinearMap‖ * ‖fderiv ℝ ξ (s, t) stdComplexLineImag‖ +
        ‖A (s, t) - -((J₀ t).toLinearMap.toContinuousLinearMap ∘L S t)‖ * ‖ξ (s, t)‖ :=
        (norm_add_le _ _).trans (add_le_add (le_opNorm _ _) (le_opNorm _ _))
    _ ≤ ε * ‖fderiv ℝ ξ (s, t) stdComplexLineImag‖ + ε * ‖ξ (s, t)‖ := by
        gcongr
    _ = _ := by ring

/-- **The semi-Fredholm estimate of a real Cauchy–Riemann operator with nondegenerate limits.**
Let `J(z)` be `ω`-compatible complex structures and `A(z)` linear maps, both continuous in `z`,
and let `P ξ = ∂s ξ + J(z) ∂t ξ + A(z) ξ`. Suppose that at `-∞` and at `+∞` the coefficients
converge uniformly in `t ∈ [0, 1]` to those of stationary cylinder operators: `J(s, t) → J±(t)` and
`A(s, t) → -J±(t) S±(t)`, for continuous `ω`-compatible `J±` and continuous infinitesimally
symplectic `S±` whose return maps `Ψ±(1) = dysonSeriesLeft S± 1` satisfy
`det (1 - Ψ±(1)) ≠ 0`. Then there are `C ≥ 0` and `T` such that every `C²` map `ξ` of period one
in `t` that vanishes for `s ∉ (a, b)` satisfies

`∫ (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ C (∫ ‖P ξ‖² + ∫_{[-T, T] × [0, 1]} ‖ξ‖²)`

over `[a, b] × [0, 1]`. -/
theorem exists_forall_setIntegral_le_mul_setIntegral_cauchyRiemann_add_of_tendstoUniformlyOn
    (ω : SymplecticForm V) {J : ℝ × ℝ → AlmostComplexStructure V} {A : ℝ × ℝ → V →L[ℝ] V}
    (hJ : ∀ z, ω.Compatible (J z))
    (hJc : Continuous fun z ↦ (J z).toLinearMap.toContinuousLinearMap) (hAc : Continuous A)
    {Jm Jp : ℝ → AlmostComplexStructure V} {Sm Sp : ℝ → V →L[ℝ] V}
    (hJm : ∀ t, ω.Compatible (Jm t))
    (hJmc : Continuous fun t ↦ (Jm t).toLinearMap.toContinuousLinearMap)
    (hSm : ∀ t v w, ω (Sm t v) w + ω v (Sm t w) = 0) (hSmc : Continuous Sm)
    (hdetm : LinearMap.det ((1 - dysonSeriesLeft Sm 1 : V →L[ℝ] V) : V →ₗ[ℝ] V) ≠ 0)
    (hJlm : TendstoUniformlyOn (fun s t ↦ (J (s, t)).toLinearMap.toContinuousLinearMap)
      (fun t ↦ (Jm t).toLinearMap.toContinuousLinearMap) atBot (Icc 0 1))
    (hAlm : TendstoUniformlyOn (fun s t ↦ A (s, t))
      (fun t ↦ -((Jm t).toLinearMap.toContinuousLinearMap ∘L Sm t)) atBot (Icc 0 1))
    (hJp : ∀ t, ω.Compatible (Jp t))
    (hJpc : Continuous fun t ↦ (Jp t).toLinearMap.toContinuousLinearMap)
    (hSp : ∀ t v w, ω (Sp t v) w + ω v (Sp t w) = 0) (hSpc : Continuous Sp)
    (hdetp : LinearMap.det ((1 - dysonSeriesLeft Sp 1 : V →L[ℝ] V) : V →ₗ[ℝ] V) ≠ 0)
    (hJlp : TendstoUniformlyOn (fun s t ↦ (J (s, t)).toLinearMap.toContinuousLinearMap)
      (fun t ↦ (Jp t).toLinearMap.toContinuousLinearMap) atTop (Icc 0 1))
    (hAlp : TendstoUniformlyOn (fun s t ↦ A (s, t))
      (fun t ↦ -((Jp t).toLinearMap.toContinuousLinearMap ∘L Sp t)) atTop (Icc 0 1)) :
    ∃ C, 0 ≤ C ∧ ∃ T, ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → (∀ s t, ξ (s, t + 1) = ξ (s, t)) →
      ∀ ⦃a b : ℝ⦄, a ≤ b → (∀ s t, s ∉ Ioo a b → ξ (s, t) = 0) →
        ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
          C * ((∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖fderiv ℝ ξ z stdComplexLineReal +
            J z (fderiv ℝ ξ z stdComplexLineImag) + A z (ξ z)‖ ^ 2) +
            ∫ z in Icc (-T) T ×ˢ Icc (0 : ℝ) 1, ‖ξ z‖ ^ 2) := by
  obtain ⟨Cp, -, Up, hUp, hp⟩ :=
    ω.exists_mem_forall_setIntegral_le_mul_setIntegral_cauchyRiemann_of_tendstoUniformlyOn hJp
      hJpc hSp hSpc hdetp hJc hAc hJlp hAlp
  obtain ⟨Cm, -, Um, hUm, hm⟩ :=
    ω.exists_mem_forall_setIntegral_le_mul_setIntegral_cauchyRiemann_of_tendstoUniformlyOn hJm
      hJmc hSm hSmc hdetm hJc hAc hJlm hAlm
  obtain ⟨Rp, hRp⟩ := mem_atTop_sets.1 hUp
  obtain ⟨Rm, hRm⟩ := mem_atBot_sets.1 hUm
  exact ω.exists_forall_setIntegral_le_mul_setIntegral_cauchyRiemann_add_of_ends hJ hJc hAc
    (Rp := Rp) (Rm := Rm)
    (fun ξ hξ hper a b ha hab hsa hsb ↦ hp hξ hper hab (fun s hs ↦ hRp s (ha.trans hs.1)) hsa hsb)
    (fun ξ hξ hper a b hab hb hsa hsb ↦ hm hξ hper hab (fun s hs ↦ hRm s (hs.2.trans hb)) hsa hsb)

end TauCeti.SymplecticForm
