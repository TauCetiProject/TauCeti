/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import TauCeti.NumberTheory.Padics.Coleman.Norm
public import TauCeti.NumberTheory.Padics.Measure.PhiPsi
public import TauCeti.NumberTheory.Padics.Measure.RootTranslation

import Mathlib.LinearAlgebra.Vandermonde
import TauCeti.NumberTheory.Padics.Coleman.Limit
import TauCeti.NumberTheory.Padics.Measure.RootAveraging.Integral
import TauCeti.NumberTheory.Padics.Measure.Topology.Amice
import TauCeti.RingTheory.Huber.Padic.Basic

/-!
# Coleman operators, `ψ` on `ℤ_p⟦X⟧`, and root-of-unity products

Over `O = ℤ_[p]`, this file identifies Coleman's zeroth coordinate and trace with the
measure-theoretic operator `TauCeti.psiSeries` on `ℤ_[p]⟦X⟧`, and expresses both the sum and the
product of the `p` root-of-unity translates `F(ζ ^ i * (1 + X) - 1)` in terms of Coleman's trace
and norm.

## Main results

* `TauCeti.Coleman.coord_zero_eq_psiSeries`: the zeroth Coleman coordinate on `ℤ_[p]⟦X⟧` equals
  `TauCeti.psiSeries p`.
* `TauCeti.Coleman.trace_eq_p_mul_psiSeries`: `τ(F) = p * ψ(F)` on `ℤ_[p]⟦X⟧`, so `τ(F) = p * F`
  iff `ψ(F) = F` and `τ(F) = 0` iff `ψ(F) = 0`.
* `IsPrimitiveRoot.sum_rootTranslation_eq_map_frobeniusHom_trace`:
  `∑ i < p, F(ζ ^ i * (1 + X) - 1) = Φ(τ(F))` after coefficient inclusion `ℤ_[p] → 𝓞_ℂ_[p]`.
* `IsPrimitiveRoot.prod_rootTranslation`:
  `∏ i < p, F(ζ ^ i * (1 + X) - 1) = Φ(N(F))` after coefficient inclusion `ℤ_[p] → 𝓞_ℂ_[p]`.

## References

* R. F. Coleman, *Division Values in Local Fields*, Invent. Math. 53 (1979), §II.
* J. Coates and R. Sujatha, *Cyclotomic Fields and Zeta Values*, Springer (2006), §3.3.
* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions* (2025), §3.5.
-/

public noncomputable section

open PowerSeries
open scoped PowerSeries.WithPiTopology

namespace TauCeti.Coleman

variable {p : ℕ} [Fact p.Prime]

/-- `ℤ_[p]` is `(p)`-adically complete, transporting Mathlib's
`IsAdicComplete (maximalIdeal ℤ_[p])`. -/
scoped instance isAdicComplete_padicInt (p : ℕ) [Fact p.Prime] :
    IsAdicComplete (Ideal.span {(p : ℤ_[p])}) ℤ_[p] := by
  rw [← PadicInt.maximalIdeal_eq_span_p]; infer_instance

/-- **Identification of the zeroth Coleman coordinate with measure `ψ`.** On `ℤ_[p]⟦X⟧`, the zeroth
coordinate in the Coleman basis equals `TauCeti.psiSeries p`. -/
theorem coord_zero_eq_psiSeries (F : ℤ_[p]⟦X⟧) :
    coord p ℤ_[p] ⟨0, (Fact.out : p.Prime).pos⟩ F = TauCeti.psiSeries p F := by
  have hAdic : IsAdic (Ideal.span {(p : ℤ_[p])}) :=
    PadicInt.maximalIdeal_eq_span_p (p := p) ▸ TauCeti.Huber.PadicInt.isAdic_maximalIdeal
  refine congrFun ((PowerSeries.WithPiTopology.denseRange_toPowerSeries ℤ_[p]).equalizer
    (continuous_coord hAdic _) TauCeti.continuous_psiSeries ?_) F
  funext P
  let Q : Polynomial ℤ_[p] := P.comp (Polynomial.X - 1)
  have hcomp : Q.comp (1 + Polynomial.X) = P := by
    rw [Polynomial.comp_assoc]
    simp [Polynomial.sub_comp, Polynomial.X_comp, Polynomial.one_comp]
  have hP : (P : ℤ_[p]⟦X⟧) = ∑ n ∈ Q.support, Q.coeff n • ((1 + X : ℤ_[p]⟦X⟧) ^ n) := by
    conv_lhs => rw [← hcomp, Q.as_sum_support_C_mul_X_pow]
    rw [Polynomial.sum_comp, ← Polynomial.coeToPowerSeries.ringHom_apply, map_sum]
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    simp [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.pow_comp, Polynomial.X_comp,
      Polynomial.coeToPowerSeries.ringHom_apply, PowerSeries.smul_eq_C_mul]
  simp only [Function.comp_apply, hP, map_sum, map_smul]
  refine Finset.sum_congr rfl fun n _ ↦ congrArg _ ?_
  rw [coord_one_add_X_pow, TauCeti.psiSeries_one_add_X_pow]
  have hiff : (0 : ℕ) = n % p ↔ p ∣ n := by rw [eq_comm, Nat.dvd_iff_mod_eq_zero]
  simp [hiff]

/-- **Coleman's trace is `p` times measure `ψ` on `ℤ_[p]⟦X⟧`.** -/
theorem trace_eq_p_mul_psiSeries (F : ℤ_[p]⟦X⟧) :
    trace p ℤ_[p] F = (p : ℤ_[p]⟦X⟧) * TauCeti.psiSeries p F := by
  rw [trace_eq_p_mul_coord_zero, coord_zero_eq_psiSeries]

private theorem natCast_prime_ne_zero_padicInt : (p : ℤ_[p]⟦X⟧) ≠ 0 := by
  rw [← map_natCast C, map_ne_zero_iff C C_injective]
  exact Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero

/-- On `ℤ_[p]⟦X⟧`, `τ(F) = p * F` if and only if `ψ(F) = F`. -/
theorem trace_eq_p_mul_iff_psiSeries_eq (F : ℤ_[p]⟦X⟧) :
    trace p ℤ_[p] F = (p : ℤ_[p]⟦X⟧) * F ↔ TauCeti.psiSeries p F = F := by
  rw [trace_eq_p_mul_psiSeries, mul_right_inj' natCast_prime_ne_zero_padicInt]

/-- On `ℤ_[p]⟦X⟧`, Coleman's trace vanishes if and only if `ψ` vanishes. -/
theorem trace_eq_zero_iff_psiSeries_eq_zero (F : ℤ_[p]⟦X⟧) :
    trace p ℤ_[p] F = 0 ↔ TauCeti.psiSeries p F = 0 := by
  rw [trace_eq_p_mul_psiSeries, mul_eq_zero, or_iff_right natCast_prime_ne_zero_padicInt]

end TauCeti.Coleman

namespace IsPrimitiveRoot

open TauCeti TauCeti.IwasawaAveraging
open PadicComplex (integralCoefficientMap)
open scoped TauCeti.Coleman

variable {p : ℕ} [Fact p.Prime] {ζ : 𝓞_ℂ_[p]}

/-- Every `p`-th root translation fixes series in the image of Frobenius substitution `Φ`,
up to the integral coefficient inclusion `ℤ_[p] → 𝓞_ℂ_[p]`. -/
private theorem rootTranslation_frobeniusHom (ζ : 𝓞_ℂ_[p]) (hζ : ζ ^ p = 1) (i : ℕ)
    (g : ℤ_[p]⟦X⟧) :
    rootTranslation p ζ hζ i (Coleman.frobeniusHom p ℤ_[p] g) =
      PowerSeries.map (integralCoefficientMap p) (Coleman.frobeniusHom p ℤ_[p] g) := by
  have hmap : Continuous (PowerSeries.map (integralCoefficientMap p)) :=
    continuous_pi fun d ↦
      (PadicComplex.continuous_integralCoefficientMap p).comp (continuous_apply d)
  refine congrFun ((PowerSeries.WithPiTopology.denseRange_toPowerSeries ℤ_[p]).equalizer
    ((continuous_rootTranslation p ζ hζ i).comp Coleman.continuous_frobeniusHom)
    (hmap.comp Coleman.continuous_frobeniusHom) ?_) g
  funext P
  simp only [Function.comp_apply]
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [Polynomial.coe_add, map_add, hP, hQ]
  | monomial n a =>
    have hX : rootTranslation p ζ hζ i (Coleman.frobeniusHom p ℤ_[p] X) =
        PowerSeries.map (integralCoefficientMap p) (Coleman.frobeniusHom p ℤ_[p] X) := by
      have hζi : (ζ ^ i) ^ p = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]
      rw [Coleman.frobeniusHom_X, map_sub, map_one, rootTranslation_one_add_X_pow, mul_pow,
        ← map_pow, hζi, map_one, one_mul, map_sub, map_pow, map_add, map_one, map_X]
    rw [← Polynomial.C_mul_X_pow_eq_monomial]
    simp only [Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_pow, Polynomial.coe_X,
      map_mul, map_pow, Coleman.frobeniusHom_C, rootTranslation_C, map_C, hX]

/-- **Root-translation sum equals Frobenius of Coleman's trace.** For a primitive `p`-th root of
unity `ζ ∈ 𝓞_ℂ_[p]`, `∑ i < p, F(ζ ^ i * (1 + X) - 1) = Φ(τ(F))`. -/
theorem sum_rootTranslation_eq_map_frobeniusHom_trace (hζ : IsPrimitiveRoot ζ p) (F : ℤ_[p]⟦X⟧) :
    ∑ i : Fin p, rootTranslation p ζ hζ.pow_eq_one (i : ℕ) F =
      PowerSeries.map (integralCoefficientMap p)
        (Coleman.frobeniusHom p ℤ_[p] (Coleman.trace p ℤ_[p] F)) := by
  rw [hζ.sum_rootTranslation, Coleman.trace_eq_p_mul_psiSeries, map_mul, map_natCast, map_mul,
    map_natCast, Coleman.frobeniusHom_apply]

/-- **Root-translation product equals Frobenius of Coleman's norm.** For a primitive `p`-th root
of unity `ζ ∈ 𝓞_ℂ_[p]`, `∏ i < p, F(ζ ^ i * (1 + X) - 1) = Φ(N(F))`. -/
theorem prod_rootTranslation (hζ : IsPrimitiveRoot ζ p) (F : ℤ_[p]⟦X⟧) :
    ∏ i : Fin p, rootTranslation p ζ hζ.pow_eq_one (i : ℕ) F =
      PowerSeries.map (integralCoefficientMap p)
        (Coleman.frobeniusHom p ℤ_[p] (Coleman.norm p ℤ_[p] F)) := by
  let ψ : ℤ_[p]⟦X⟧ →+* PowerSeries 𝓞_ℂ_[p] :=
    (PowerSeries.map (integralCoefficientMap p)).comp (Coleman.frobeniusHom p ℤ_[p]).toRingHom
  let v : Fin p → PowerSeries 𝓞_ℂ_[p] := fun i ↦ C (ζ ^ (i : ℕ)) * (1 + X)
  let V : Matrix (Fin p) (Fin p) (PowerSeries 𝓞_ℂ_[p]) := Matrix.vandermonde v
  let M : Matrix (Fin p) (Fin p) (PowerSeries 𝓞_ℂ_[p]) := (Coleman.leftMulMatrix p ℤ_[p] F).map ψ
  have hmat : Matrix.diagonal
      (fun i : Fin p ↦ rootTranslation p ζ hζ.pow_eq_one (i : ℕ) F) * V = V * M := by
    refine Matrix.ext fun i j ↦ ?_
    rw [Matrix.diagonal_mul, Matrix.mul_apply]
    have hcol := congrArg (rootTranslation p ζ hζ.pow_eq_one (i : ℕ))
      (Coleman.mul_one_add_X_pow_eq_sum_leftMulMatrix (p := p) F j)
    simp only [map_mul, map_sum, rootTranslation_one_add_X_pow,
      rootTranslation_frobeniusHom] at hcol
    simpa only [V, M, Matrix.vandermonde_apply, Matrix.map_apply, RingHom.comp_apply,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, v, ψ, mul_comm (v i ^ _)] using hcol
  have hdet := congrArg Matrix.det hmat
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal] at hdet
  have hV : V.det ≠ 0 := by
    rw [Matrix.det_vandermonde_ne_zero_iff]
    intro i j hij
    have h1X : (1 + X : PowerSeries 𝓞_ℂ_[p]) ≠ 0 := fun h ↦ by
      have h0 := congrArg constantCoeff h; simp at h0
    exact Fin.ext (hζ.injOn_pow (by simp) (by simp) (C_injective (mul_right_cancel₀ h1X hij)))
  have hprod : (∏ i : Fin p, rootTranslation p ζ hζ.pow_eq_one (i : ℕ) F) = M.det :=
    mul_right_cancel₀ hV (by rw [hdet, mul_comm])
  have hMdet : M.det = ψ (Matrix.det (Coleman.leftMulMatrix p ℤ_[p] F)) :=
    (RingHom.map_det ψ (Coleman.leftMulMatrix p ℤ_[p] F)).symm
  rw [hprod, hMdet, ← Coleman.norm_eq_det_leftMulMatrix]
  rfl

end IsPrimitiveRoot
