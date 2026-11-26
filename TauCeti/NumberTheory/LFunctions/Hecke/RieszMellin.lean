/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finsupp.BigOperators
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.RemainderMellin
public import TauCeti.NumberTheory.LFunctions.Hecke.Conjugate
import TauCeti.Analysis.Meromorphic.Conj
import TauCeti.Topology.ContinuousOn.PuncturedNhds

/-!
# Conjugation of Hecke Riesz Mellin expressions

Taking the inverse ray class character reflects the normalized Mellin expression across the real
axis. Thus an inverse-paired average, the expression that corresponds to the real part of a
Riesz remainder, has conjugation symmetry, as does any finite real-weighted sum of such averages.
The equality includes the canonical values of the individual expressions at poles.

The application to real parts of Riesz remainders follows the normalization in L. Alpöge's
`Deduction.Gm` and `Deduction.Gchi_conj`.
-/

public section

open ComplexConjugate Filter Set Topology

namespace TauCeti.LFunctions

open GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-- Inverting a ray class character and reflecting the argument conjugate the normalized Riesz
Mellin value. No primitivity assumption is needed. -/
@[simp] theorem rieszRemainderMellin_heckeLFunctionC_inv_conj {𝔪 : Modulus K}
    (χ : RayClassCharacter 𝔪) (s : ℂ) :
    rieszRemainderMellin (heckeLFunctionC χ⁻¹) (conj s) =
      conj (rieszRemainderMellin (heckeLFunctionC χ) s) := by
  have horder : meromorphicOrderAt (heckeLFunctionC χ⁻¹) 1 =
      meromorphicOrderAt (heckeLFunctionC χ) 1 := by
    simpa only [map_one] using meromorphicOrderAt_heckeLFunctionC_inv_conj χ 1
  have hlog (z : ℂ) : logDeriv (heckeLFunctionC χ⁻¹) z =
      conj (logDeriv (heckeLFunctionC χ) (conj z)) := by
    simpa only [Complex.conj_conj] using logDeriv_heckeLFunctionC_inv_conj χ (conj z)
  have hconj (z : ℂ) : Tendsto conj (𝓝[≠] z) (𝓝[≠] (conj z)) :=
    Complex.continuous_conj.continuousAt.tendsto_nhdsNE (starRingEnd ℂ).injective
  have hm (η : RayClassCharacter 𝔪) : Meromorphic (heckeLFunctionC η) := fun z ↦
    (meromorphicNFOn_heckeLFunctionC η (mem_univ z)).meromorphicAt
  have hfinite : logDerivFinitePart (heckeLFunctionC χ⁻¹) 1 =
      conj (logDerivFinitePart (heckeLFunctionC χ) 1) := by
    obtain ⟨g, hg, heq⟩ := (hm χ 1).exists_analyticAt_logDeriv_sub_order_div
    have hg' : AnalyticAt ℂ (conj ∘ g ∘ conj) 1 := by
      simpa only [map_one] using hg.conj_conj
    have h₁ : Tendsto conj (𝓝[≠] (1 : ℂ)) (𝓝[≠] (1 : ℂ)) := by
      simpa only [map_one] using hconj 1
    rw [hg.logDerivFinitePart_eq heq, hg'.logDerivFinitePart_eq ?_]
    · simp only [Function.comp_apply, map_one]
    · filter_upwards [h₁.eventually heq] with z hz
      simpa only [Function.comp_apply, horder, hlog, map_sub, map_div₀, map_intCast,
        map_one, Complex.conj_conj] using congrArg (fun w : ℂ ↦ conj w) hz
  have hnf := (meromorphicNFOn_rieszRemainderMellin (heckeLFunctionC χ) (mem_univ s)).conj_conj
  have hnf' := meromorphicNFOn_rieszRemainderMellin (heckeLFunctionC χ⁻¹) (mem_univ (conj s))
  have heq : rieszRemainderMellin (heckeLFunctionC χ⁻¹) =ᶠ[𝓝[≠] (conj s)]
      conj ∘ rieszRemainderMellin (heckeLFunctionC χ) ∘ conj := by
    have hc : Tendsto conj (𝓝[≠] (conj s)) (𝓝[≠] s) := by
      simpa only [Complex.conj_conj] using hconj (conj s)
    filter_upwards [(hm χ⁻¹).rieszRemainderMellin_eventuallyEq (conj s),
      hc.eventually ((hm χ).rieszRemainderMellin_eventuallyEq s)] with z hz hz'
    simp only [Function.comp_apply, hz, hz', horder, hlog, hfinite, map_div₀, map_mul, map_sub,
      map_intCast, map_one, Complex.conj_conj]
  simpa only [Function.comp_apply, Complex.conj_conj] using
    ((hnf'.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds hnf).mp heq).eq_of_nhds

/-- The real-weighted sum of the inverse-paired Hecke Riesz Mellin expressions is invariant
under reflection across the real axis followed by complex conjugation. The support of the
weights need not be closed under inversion. -/
theorem conj_finsupp_sum_rieszRemainderMellin_heckeLFunctionC
    (w : PrimitiveRayClassCharacter K →₀ ℝ) (s : ℂ) :
    conj (w.sum fun ψ c ↦ (c : ℂ) *
      ((rieszRemainderMellin (heckeLFunctionC ψ.character) (conj s) +
        rieszRemainderMellin (heckeLFunctionC ψ⁻¹.character) (conj s)) / 2)) =
      w.sum fun ψ c ↦ (c : ℂ) *
        ((rieszRemainderMellin (heckeLFunctionC ψ.character) s +
          rieszRemainderMellin (heckeLFunctionC ψ⁻¹.character) s) / 2) := by
  rw [Finsupp.sum, map_sum, Finsupp.sum]
  refine Finset.sum_congr rfl fun ψ _ ↦ ?_
  have h := rieszRemainderMellin_heckeLFunctionC_inv_conj ψ.character (conj s)
  rw [Complex.conj_conj] at h
  simp only [PrimitiveRayClassCharacter.character_inv, ← h,
    rieszRemainderMellin_heckeLFunctionC_inv_conj, map_mul, map_div₀, map_add,
    Complex.conj_ofReal, map_ofNat, Complex.conj_conj]
  rw [add_comm]

end TauCeti.LFunctions
