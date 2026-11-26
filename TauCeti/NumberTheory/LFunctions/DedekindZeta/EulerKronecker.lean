/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
public import TauCeti.Analysis.Calculus.LogDeriv
public import TauCeti.NumberTheory.LFunctions.DedekindZeta.Completed
import TauCeti.Analysis.Calculus.LogDeriv.Symmetry
import TauCeti.Analysis.Meromorphic.Conj
import TauCeti.NumberTheory.LSeries.Conjugate

/-!
# The Euler–Kronecker constant

Removing the pole of the Dedekind zeta function gives the entire function
`dedekindZetaPoleRemoved K`, equal to `(s - 1) ζ_K(s)` off `1` and to the residue at `1`.
Its logarithmic derivative at `1` is real and equals `NumberField.eulerKroneckerConstant K`.
Thus `ζ_K′/ζ_K` has expansion `-1/(s - 1) + EK(K) + O(s - 1)`. This regular part enters
in the main term of smoothed prime-ideal counts. Over `ℚ` the constant is Euler's constant.

For the normalization, see Y. Ihara, *On the Euler–Kronecker constants of global fields and
primes with small norms*, in Algebraic Geometry and Number Theory (2006), §1.
The rational evaluation uses Mathlib's `deriv_riemannZeta₁_one`.
-/

public section

open Asymptotics Complex ComplexConjugate Filter NumberField Set
open scoped Topology

namespace TauCeti.LFunctions

variable (K : Type*) [Field K] [NumberField K]

/-- The entire extension of `(s - 1) ζ_K(s)` through the simple pole of `ζ_K` at `1`. -/
noncomputable def dedekindZetaPoleRemoved : ℂ → ℂ :=
  toMeromorphicNFOn (fun s ↦ (s - 1) * dedekindZetaC K s) univ

private theorem meromorphic_sub_one_mul_dedekindZetaC :
    Meromorphic (fun s ↦ (s - 1) * dedekindZetaC K s) :=
  (analyticOnNhd_id.sub analyticOnNhd_const).meromorphicOn.fun_mul
    (meromorphic_dedekindZetaC K).meromorphicOn |> meromorphicOn_univ.mp

/-- Off the pole, regularization is ordinary multiplication by `s - 1`. -/
theorem dedekindZetaPoleRemoved_apply_of_ne_one {s : ℂ} (hs : s ≠ 1) :
    dedekindZetaPoleRemoved K s = (s - 1) * dedekindZetaC K s :=
  toMeromorphicNFOn_apply_of_analyticAt (meromorphic_sub_one_mul_dedekindZetaC K)
    ((analyticAt_id.sub analyticAt_const).mul (analyticAt_dedekindZetaC K hs))

/-- The pole-removed Dedekind zeta function is analytic on the whole plane. -/
@[fun_prop]
theorem analyticAt_dedekindZetaPoleRemoved (s : ℂ) :
    AnalyticAt ℂ (dedekindZetaPoleRemoved K) s := by
  by_cases hs : s = 1
  · subst s
    have hmul := meromorphicOrderAt_mul (f := fun s : ℂ ↦ s - 1)
      (analyticAt_id.sub analyticAt_const).meromorphicAt (meromorphic_dedekindZetaC K 1)
    simp only [Pi.mul_def, meromorphicOrderAt_id_sub_const,
      meromorphicOrderAt_dedekindZetaC_one] at hmul
    rw [dedekindZetaPoleRemoved, ← (meromorphicNFOn_toMeromorphicNFOn _ univ
      (mem_univ (1 : ℂ))).meromorphicOrderAt_nonneg_iff_analyticAt,
      meromorphicOrderAt_toMeromorphicNFOn (meromorphic_sub_one_mul_dedekindZetaC K).meromorphicOn
        (mem_univ _), hmul]
    norm_num
  · have han : AnalyticAt ℂ (fun t ↦ (t - 1) * dedekindZetaC K t) s := by
      fun_prop
    refine han.congr ?_
    filter_upwards [isOpen_ne.mem_nhds hs] with t ht
    exact (dedekindZetaPoleRemoved_apply_of_ne_one K ht).symm

/-- At `1` the pole-removed function takes the residue of the Dedekind zeta function. -/
@[simp]
theorem dedekindZetaPoleRemoved_one :
    dedekindZetaPoleRemoved K 1 = dedekindZeta_residue K := by
  have h := (analyticAt_dedekindZetaPoleRemoved K 1).continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds (s := {1}ᶜ))
  apply tendsto_nhds_unique h
  refine (tendsto_sub_one_mul_dedekindZetaC K).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (dedekindZetaPoleRemoved_apply_of_ne_one K hs).symm

/-- The pole-removed zeta function of `ℚ` is Mathlib's entire regularization of `ζ`. -/
@[simp]
theorem dedekindZetaPoleRemoved_rat : dedekindZetaPoleRemoved ℚ = riemannZeta₁ := by
  have heq (s : ℂ) (hs : s ≠ 1) : dedekindZetaPoleRemoved ℚ s = riemannZeta₁ s := by
    rw [dedekindZetaPoleRemoved_apply_of_ne_one _ hs, dedekindZetaC_rat_eq_riemannZeta hs,
      riemannZeta_eq_inv_sub_mul hs, mul_inv_cancel_left₀ (sub_ne_zero.mpr hs)]
  ext s
  obtain rfl | hs := eq_or_ne s 1
  · have h := (analyticAt_dedekindZetaPoleRemoved ℚ 1).continuousAt
    refine ((h.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
      (differentiable_riemannZeta₁ 1).continuousAt).mp ?_).eq_of_nhds
    filter_upwards [self_mem_nhdsWithin] with t ht using heq t ht
  · exact heq s hs

/-- Complex conjugation of the argument conjugates the pole-removed Dedekind zeta function. -/
@[simp]
theorem dedekindZetaPoleRemoved_conj (s : ℂ) :
    dedekindZetaPoleRemoved K (conj s) = conj (dedekindZetaPoleRemoved K s) := by
  have han := analyticAt_dedekindZetaPoleRemoved K
  have hm : Meromorphic (dedekindZetaPoleRemoved K) := fun z ↦ (han z).meromorphicAt
  have heq := eq_of_meromorphic_of_eqOn_halfPlane hm hm.conj_conj (σ := 1) (z := conj s) ?_
    (han _) (analyticAt_conj_conj_iff.mpr (han _))
  · simpa only [Function.comp_apply, conj_conj] using heq
  · intro z hz
    have hz' : 1 < (conj z).re := by simpa only [conj_re] using mem_ofPred.mp hz
    have hne {w : ℂ} (hw : 1 < w.re) : w ≠ 1 := by rintro rfl; simp at hw
    rw [Function.comp_apply, Function.comp_apply,
      dedekindZetaPoleRemoved_apply_of_ne_one K (hne hz),
      dedekindZetaPoleRemoved_apply_of_ne_one K (hne hz'), dedekindZetaC_eq_dedekindZeta K hz,
      dedekindZetaC_eq_dedekindZeta K hz', map_mul, map_sub, map_one, conj_conj]
    congr 1
    simpa only [dedekindZeta, Pi.star_def, Complex.star_def, map_natCast, conj_conj] using
      TauCeti.LSeries.LSeries_star
        (fun n ↦ (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ)) (conj z)

/-- Subtracting the principal part of `ζ_K′/ζ_K` gives the logarithmic derivative of the
pole-removed function as a punctured germ at `1`. -/
theorem logDeriv_dedekindZetaC_add_inv_eventuallyEq :
    (fun s ↦ logDeriv (dedekindZetaC K) s + (s - 1)⁻¹) =ᶠ[𝓝[≠] 1]
      logDeriv (dedekindZetaPoleRemoved K) := by
  have hneq : dedekindZetaPoleRemoved K 1 ≠ 0 := by
    simp [dedekindZeta_residue_ne_zero]
  have hne := (analyticAt_dedekindZetaPoleRemoved K 1).continuousAt.eventually_ne hneq
  have heq : dedekindZetaPoleRemoved K =ᶠ[𝓝[≠] 1] fun s ↦ (s - 1) * dedekindZetaC K s := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact dedekindZetaPoleRemoved_apply_of_ne_one K hs
  filter_upwards [logDeriv_congr_nhdsNE heq, self_mem_nhdsWithin,
    hne.filter_mono nhdsWithin_le_nhds] with s hlog hs hH
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  have hζ : dedekindZetaC K s ≠ 0 := by
    rwa [dedekindZetaPoleRemoved_apply_of_ne_one K hs, mul_ne_zero_iff, and_iff_right hsub] at hH
  rw [hlog, logDeriv_fun_mul (f := fun t ↦ t - 1) s hsub hζ
    (differentiableAt_id.sub_const 1) (analyticAt_dedekindZetaC K hs).differentiableAt,
    logDeriv_apply (· - 1), deriv_sub_const, deriv_id'', one_div, add_comm]

/-- The logarithmic derivative of the pole-removed zeta function is analytic at `1`. -/
@[fun_prop]
theorem analyticAt_logDeriv_dedekindZetaPoleRemoved_one :
    AnalyticAt ℂ (logDeriv (dedekindZetaPoleRemoved K)) 1 :=
  (analyticAt_dedekindZetaPoleRemoved K 1).logDeriv (by simp [dedekindZeta_residue_ne_zero])

end TauCeti.LFunctions

namespace NumberField

open TauCeti.LFunctions

variable (K : Type*) [Field K] [NumberField K]

/-- The real constant term in the Laurent expansion of `ζ_K′/ζ_K` at `1`. -/
noncomputable def eulerKroneckerConstant : ℝ :=
  (logDeriv (dedekindZetaPoleRemoved K) 1).re

/-- The logarithmic derivative of the pole-removed zeta function at `1` is the
Euler–Kronecker constant (with no imaginary part). -/
@[simp]
theorem logDeriv_dedekindZetaPoleRemoved_one :
    logDeriv (dedekindZetaPoleRemoved K) 1 = (eulerKroneckerConstant K : ℂ) := by
  have heq : conj ∘ dedekindZetaPoleRemoved K ∘ conj = dedekindZetaPoleRemoved K := by
    ext z
    simp only [Function.comp_apply, dedekindZetaPoleRemoved_conj, conj_conj]
  have hc := TauCeti.logDeriv_conj_conj (dedekindZetaPoleRemoved K) 1
  rw [heq, map_one] at hc
  simpa only [eulerKroneckerConstant] using (conj_eq_iff_re.mp hc.symm).symm

/-- The constant term of `ζ_K′/ζ_K` at `1` is the limit after adding `1/(s - 1)`. -/
theorem tendsto_logDeriv_dedekindZetaC_add_inv :
    Tendsto (fun s ↦ logDeriv (dedekindZetaC K) s + (s - 1)⁻¹) (𝓝[≠] 1)
      (𝓝 (eulerKroneckerConstant K : ℂ)) := by
  rw [← logDeriv_dedekindZetaPoleRemoved_one K]
  have h := (analyticAt_logDeriv_dedekindZetaPoleRemoved_one K).continuousAt.tendsto
  exact (h.mono_left nhdsWithin_le_nhds).congr'
    (logDeriv_dedekindZetaC_add_inv_eventuallyEq K).symm

/-- The Laurent expansion of `ζ_K′/ζ_K` at `1` has principal part `-1/(s - 1)` and
constant term `EK(K)`, with error of order `s - 1`. -/
theorem isBigO_logDeriv_dedekindZetaC_add_inv_sub :
    (fun s ↦ logDeriv (dedekindZetaC K) s + (s - 1)⁻¹ - (eulerKroneckerConstant K : ℂ))
      =O[𝓝[≠] 1] (· - 1) := by
  rw [← logDeriv_dedekindZetaPoleRemoved_one K]
  have h := (analyticAt_logDeriv_dedekindZetaPoleRemoved_one K).differentiableAt.isBigO_sub
  refine (h.mono nhdsWithin_le_nhds).congr' ?_ EventuallyEq.rfl
  filter_upwards [logDeriv_dedekindZetaC_add_inv_eventuallyEq K] with s hs
  rw [hs]

/-- The Euler–Kronecker constant of `ℚ` is the Euler–Mascheroni constant. -/
@[simp]
theorem eulerKroneckerConstant_rat : eulerKroneckerConstant ℚ = Real.eulerMascheroniConstant := by
  rw [eulerKroneckerConstant, dedekindZetaPoleRemoved_rat, logDeriv_apply, riemannZeta₁_one,
    div_one, deriv_riemannZeta₁_one, ofReal_re]

end NumberField
