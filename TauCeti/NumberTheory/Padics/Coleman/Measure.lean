/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Basic
public import TauCeti.NumberTheory.Padics.Coleman.RootEvaluation
public import TauCeti.NumberTheory.Padics.Measure.PhiPsi
public import TauCeti.NumberTheory.Padics.Measure.RootTranslation

import TauCeti.NumberTheory.Padics.Coleman.Topology
import TauCeti.NumberTheory.Padics.Measure.Topology.Amice
import TauCeti.RingTheory.Huber.Padic.Basic
import TauCeti.RingTheory.PowerSeries.Basic

/-!
# Coleman operators, `ψ` on `ℤ_p⟦X⟧`, and `p`-adic root translations

This file bridges Coleman's `coord`, `trace`, and `norm` (`Coleman.Basic`, `Coleman.Norm`) to:
1. **Amice-transformed `ℤ_p`-measures on `ℤ_[p]⟦X⟧`**: identifying `coord p ℤ_[p] 0` with
   `TauCeti.psiSeries p`, yielding `τ(F) = p * ψ(F)` and fixed-point/kernel equivalences.
2. **Integral `p`-adic root translations**: specializing the root-of-unity evaluations in
   `TauCeti.NumberTheory.Padics.Coleman.RootEvaluation` to
   `TauCeti.IwasawaAveraging.rootTranslation` on `ℤ_[p]⟦X⟧ → 𝓞_ℂ_[p]⟦X⟧`.

## Main results

* `TauCeti.Coleman.coord_zero_eq_psiSeries`, `TauCeti.Coleman.trace_eq_p_mul_psiSeries`,
  `TauCeti.Coleman.trace_eq_p_mul_self_iff_psiSeries_eq_self`,
  `TauCeti.Coleman.trace_eq_zero_iff_psiSeries_eq_zero`: bridge between `coord`/`trace` and `ψ`.
* `TauCeti.IwasawaAveraging.rootTranslation_frobeniusHom`: `p`-th root translations fix power
  series in the image of `Φ`.
* `IsPrimitiveRoot.sum_rootTranslation_eq_map_frobeniusHom_trace`,
  `IsPrimitiveRoot.prod_rootTranslation`,
  `IsPrimitiveRoot.map_frobeniusHom_eq_prod_rootTranslation_iff`: `rootTranslation` specializations
  of the trace identity, norm product formula, and norm uniqueness characterization.

## References

* R. F. Coleman, *Division Values in Local Fields*, Invent. Math. 53 (1979), §§II, IV (Thm. 4,
  Cor. 5(i), Thm. 11, Cor. 12(ii)).
* J. Coates and R. Sujatha, *Cyclotomic Fields and Zeta Values*, Springer (2006), §§2.2, 3.3.
* R. Sharifi, *Iwasawa Theory*, §5.4 (Lemma 5.4.14).
* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions* (2025), §§3.5,
  10.2–10.3 (Lemmas 10.8–10.11).
-/

public noncomputable section

open PowerSeries
open scoped PowerSeries.WithPiTopology

namespace TauCeti.Coleman

variable {p : ℕ} [Fact p.Prime]

/-- On `ℤ_[p]⟦X⟧`, the zeroth Coleman coordinate equals `TauCeti.psiSeries p`. -/
theorem coord_zero_eq_psiSeries (F : ℤ_[p]⟦X⟧) :
    coord p ℤ_[p] ⟨0, (Fact.out : p.Prime).pos⟩ F = TauCeti.psiSeries p F := by
  have hAdic : IsAdic (Ideal.span {(p : ℤ_[p])}) :=
    PadicInt.maximalIdeal_eq_span_p (p := p) ▸ TauCeti.Huber.PadicInt.isAdic_maximalIdeal
  refine congrFun ((PowerSeries.WithPiTopology.denseRange_toPowerSeries ℤ_[p]).equalizer
    (continuous_coord hAdic _) TauCeti.continuous_psiSeries ?_) F
  funext P
  let Q : Polynomial ℤ_[p] := P.comp (Polynomial.X - 1)
  have hPQ : P = Q.comp (1 + Polynomial.X) := by
    rw [Polynomial.comp_assoc]
    simp [Polynomial.sub_comp]
  have hP : (P : ℤ_[p]⟦X⟧) = ∑ n ∈ Q.support, Q.coeff n • ((1 + X : ℤ_[p]⟦X⟧) ^ n) := by
    conv_lhs => rw [hPQ, Q.as_sum_support_C_mul_X_pow]
    rw [Polynomial.sum_comp, ← Polynomial.coeToPowerSeries.ringHom_apply, map_sum]
    exact Finset.sum_congr rfl fun n _ ↦ by
      simp [Polynomial.coeToPowerSeries.ringHom_apply, PowerSeries.smul_eq_C_mul]
  simp only [Function.comp_apply, hP, map_sum, map_smul]
  refine Finset.sum_congr rfl fun n _ ↦ congrArg _ ?_
  simp only [coord_one_add_X_pow, TauCeti.psiSeries_one_add_X_pow, eq_comm (a := 0),
    Nat.dvd_iff_mod_eq_zero]

/-- **Coleman's trace is `p` times measure `ψ` on `ℤ_[p]⟦X⟧`.** -/
theorem trace_eq_p_mul_psiSeries (F : ℤ_[p]⟦X⟧) :
    trace p ℤ_[p] F = (p : ℤ_[p]⟦X⟧) * TauCeti.psiSeries p F := by
  rw [trace_eq_p_mul_coord_zero, coord_zero_eq_psiSeries]

/-- On `ℤ_[p]⟦X⟧`, `τ(F) = p * F` if and only if `ψ(F) = F`. -/
theorem trace_eq_p_mul_self_iff_psiSeries_eq_self (F : ℤ_[p]⟦X⟧) :
    trace p ℤ_[p] F = (p : ℤ_[p]⟦X⟧) * F ↔ TauCeti.psiSeries p F = F := by
  rw [trace_eq_p_mul_psiSeries,
    mul_right_inj' (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)]

/-- On `ℤ_[p]⟦X⟧`, Coleman's trace vanishes if and only if `ψ` vanishes. -/
theorem trace_eq_zero_iff_psiSeries_eq_zero (F : ℤ_[p]⟦X⟧) :
    trace p ℤ_[p] F = 0 ↔ TauCeti.psiSeries p F = 0 := by
  rw [trace_eq_p_mul_psiSeries, mul_eq_zero,
    or_iff_right (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)]

end TauCeti.Coleman

namespace TauCeti.IwasawaAveraging

open PadicComplex (integralCoefficientMap)

/-- Every `p`-th root translation fixes series in the image of `Φ`, up to `ℤ_[p] → 𝓞_ℂ_[p]`. -/
@[simp]
theorem rootTranslation_frobeniusHom (p : ℕ) [Fact p.Prime] (ζ : 𝓞_ℂ_[p]) (hζ : ζ ^ p = 1)
    (i : ℕ) (g : ℤ_[p]⟦X⟧) :
    rootTranslation p ζ hζ i (Coleman.frobeniusHom p ℤ_[p] g) =
      PowerSeries.map (integralCoefficientMap p) (Coleman.frobeniusHom p ℤ_[p] g) := by
  rw [rootTranslation_eq_eval₂_map, Coleman.map_frobeniusHom,
    Coleman.eval₂_frobeniusHom hζ (PadicComplex.isTopologicallyNilpotent_sub_one p ζ hζ) i,
    ← Coleman.map_frobeniusHom]

end TauCeti.IwasawaAveraging

namespace IsPrimitiveRoot

open TauCeti TauCeti.IwasawaAveraging
open PadicComplex (integralCoefficientMap)

variable {p : ℕ} [Fact p.Prime] {ζ : 𝓞_ℂ_[p]}

/-- **Root-translation sum equals `Φ(τ(F))`** on `ℤ_[p]⟦X⟧ → 𝓞_ℂ_[p]⟦X⟧` (Sharifi, Lemma 5.4.14). -/
theorem sum_rootTranslation_eq_map_frobeniusHom_trace (hζ : IsPrimitiveRoot ζ p) (F : ℤ_[p]⟦X⟧) :
    ∑ i : Fin p, rootTranslation p ζ hζ.pow_eq_one (i : ℕ) F =
      PowerSeries.map (integralCoefficientMap p)
        (Coleman.frobeniusHom p ℤ_[p] (Coleman.trace p ℤ_[p] F)) := by
  simp_rw [rootTranslation_eq_eval₂_map]
  exact hζ.sum_eval₂_map_eq_map_frobeniusHom_trace
    (PadicComplex.isTopologicallyNilpotent_sub_one p ζ hζ.pow_eq_one) (integralCoefficientMap p) F

/-- **Root-translation product equals `Φ(N(F))`** on `ℤ_[p]⟦X⟧` (RJW, Lemmas 10.8–10.11). -/
theorem prod_rootTranslation (hζ : IsPrimitiveRoot ζ p) (F : ℤ_[p]⟦X⟧) :
    ∏ i : Fin p, rootTranslation p ζ hζ.pow_eq_one (i : ℕ) F =
      PowerSeries.map (integralCoefficientMap p)
        (Coleman.frobeniusHom p ℤ_[p] (Coleman.norm p ℤ_[p] F)) := by
  simp_rw [rootTranslation_eq_eval₂_map]
  exact hζ.prod_eval₂_map_eq_map_frobeniusHom_norm
    (PadicComplex.isTopologicallyNilpotent_sub_one p ζ hζ.pow_eq_one) (integralCoefficientMap p) F

/-- **Uniqueness of Coleman's norm on `ℤ_[p]⟦X⟧`** (Sharifi, Lemma 5.4.14; RJW, Lemmas 10.8–11). -/
theorem map_frobeniusHom_eq_prod_rootTranslation_iff (hζ : IsPrimitiveRoot ζ p) (F G : ℤ_[p]⟦X⟧) :
    PowerSeries.map (integralCoefficientMap p) (Coleman.frobeniusHom p ℤ_[p] G) =
        ∏ i : Fin p, rootTranslation p ζ hζ.pow_eq_one (i : ℕ) F ↔
      G = Coleman.norm p ℤ_[p] F := by
  simp_rw [rootTranslation_eq_eval₂_map]
  exact hζ.map_frobeniusHom_eq_prod_eval₂_map_iff
    (PadicComplex.isTopologicallyNilpotent_sub_one p ζ hζ.pow_eq_one)
    (PadicComplex.integralCoefficientMap_injective p) F G

end IsPrimitiveRoot
