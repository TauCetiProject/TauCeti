/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Symbol.Classical.Basic
public import TauCeti.Analysis.Pseudodifferential.Symbol.Frequency
public import Mathlib.RingTheory.Binomial
import TauCeti.Algebra.BigOperators.Finset.Range
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Expansion

/-!
# The Bessel weight as a classical symbol

The Bessel weight `⟨ξ / 2π⟩ ^ s = (1 + ‖ξ / 2π‖ ^ 2) ^ (s / 2)` in the angular frequency `ξ` is the
symbol of Mathlib's Bessel potential `(1 - Δ / 4π²) ^ (s / 2)`, the order-`s` isomorphism of the
Sobolev scale (`TauCeti.Symbol.besselPotential`). This file shows that it is a *classical* symbol
of order `s` (`TauCeti.ClassicalSymbol.besselPotential`): at large frequencies the binomial series

`⟨ξ / 2π⟩ ^ s = ∑ₖ (s / 2 choose k) ‖ξ / 2π‖ ^ (s - 2k)`

is an expansion into homogeneous terms of the degrees `s - 2k`, with remainders of the stated
orders (`TauCeti.exists_norm_iteratedFDeriv_one_add_norm_smul_sq_rpow_sub_sum_le`). The term of
degree `s - j` is `(s / 2 choose j / 2) ‖ξ / 2π‖ ^ (s - j)` for even `j` and vanishes for odd `j`
(`TauCeti.ClassicalSymbol.term_besselPotential`). In particular the principal symbol is
`‖ξ / 2π‖ ^ s` (`TauCeti.ClassicalSymbol.principal_besselPotential`), and the Bessel weight is
elliptic (`TauCeti.ClassicalSymbol.isElliptic_besselPotential`). The weights of orders `s` and `t`
compose pointwise to the weight of order `s + t`
(`TauCeti.ClassicalSymbol.besselPotential_comp_besselPotential`).

So the Bessel potentials are elliptic classical pseudodifferential operators of every real order,
whose symbol has no spatial dependence: this is what makes them usable inside the classical
calculus, for instance to compose an elliptic operator with them to change its order without
leaving the classical symbols.

## References

* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture I, (1.4) and (1.17).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Definition 18.1.5.
-/

public section

noncomputable section

open Real Filter Topology
open scoped ContDiff

namespace TauCeti

open HomogeneousSymbol

namespace ClassicalSymbol

variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- The power `(‖ξ / 2π‖ ^ 2) ^ (μ / 2) = ‖ξ / 2π‖ ^ μ` is `(2π)⁻¹ ^ μ ‖ξ‖ ^ μ`. -/
private theorem norm_smul_rpow_eq (ξ : CoordinateSpace n) (μ : ℝ) :
    (‖(2 * π)⁻¹ • ξ‖ ^ 2) ^ (μ / 2) = (2 * π)⁻¹ ^ μ * ‖ξ‖ ^ μ := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), Nat.cast_ofNat,
    mul_div_cancel₀ _ two_ne_zero, norm_smul, Real.norm_of_nonneg (by positivity),
    Real.mul_rpow (by positivity) (norm_nonneg _)]

/-- A smooth real function times the identity of `V` is smooth. -/
private theorem contDiff_ofReal_smul_id {f : CoordinateSpace n → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ fun ξ ↦ ((f ξ : ℝ) : ℂ) • ContinuousLinearMap.id ℂ V :=
  (Complex.ofRealCLM.contDiff.comp hf).smul contDiff_const

variable (n V) in
/-- The homogeneous term of degree `s - j` of the Bessel weight `⟨ξ / 2π⟩ ^ s`: the binomial
term `(s / 2 choose j / 2) ‖ξ / 2π‖ ^ (s - j)` for even `j`, and zero for odd `j`. -/
private def besselPotentialTerm (s : ℝ) (j : ℕ) :
    HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V V (s - j) :=
  if Even j then
    ((Ring.choose (s / 2) (j / 2) * (2 * π)⁻¹ ^ (s - j) : ℝ) : ℂ) •
      normRpow (CoordinateSpace n) (CoordinateSpace n) V (s - j)
  else 0

/-- The first `N` cut-off terms of the Bessel weight are the first `(N + 1) / 2` cut-off terms of
the binomial expansion of `(1 + ‖ξ / 2π‖ ^ 2) ^ (s / 2)`, since the terms of odd index vanish. -/
private theorem sum_smul_coefficient_besselPotentialTerm (χ : FrequencyCutoff (CoordinateSpace n))
    (s : ℝ) (N : ℕ) (p : CoordinateSpace n × CoordinateSpace n) :
    ∑ j ∈ Finset.range N, χ p.2 • (besselPotentialTerm n V s j).coefficient p =
      ((χ p.2 * ∑ k ∈ Finset.range ((N + 1) / 2),
          Ring.choose (s / 2) k * (‖(2 * π)⁻¹ • p.2‖ ^ 2) ^ (s / 2 - k) : ℝ) : ℂ) •
        ContinuousLinearMap.id ℂ V := by
  obtain ⟨x, ξ⟩ := p
  have hj (j : ℕ) : χ ξ • (besselPotentialTerm n V s j).coefficient (x, ξ) =
      if Even j then ((χ ξ * (Ring.choose (s / 2) (j / 2) *
        (‖(2 * π)⁻¹ • ξ‖ ^ 2) ^ (s / 2 - (j / 2 : ℕ))) : ℝ) : ℂ) • ContinuousLinearMap.id ℂ V
      else 0 := by
    rcases eq_or_ne ξ 0 with rfl | hξ
    · simp [FrequencyCutoff.apply_zero]
    split_ifs with he
    · obtain ⟨k, rfl⟩ := he
      have hk : (k + k) / 2 = k := by omega
      have hexp : s / 2 - (k : ℝ) = (s - ((k + k : ℕ) : ℝ)) / 2 := by push_cast; ring
      rw [besselPotentialTerm, ite_eq_left ⟨k, rfl⟩, HomogeneousSymbol.coefficient_smul,
        Pi.smul_apply, coefficient_normRpow_of_ne_zero _ _ _ hξ, hk, hexp, norm_smul_rpow_eq]
      simp only [← Complex.coe_smul, smul_smul]
      congr 1
      push_cast
      ring
    · rw [besselPotentialTerm, ite_eq_right he, HomogeneousSymbol.coefficient_zero, Pi.zero_apply,
        smul_zero]
  simp_rw [hj]
  rw [Finset.sum_range_ite_even (fun k ↦ ((χ ξ * (Ring.choose (s / 2) k *
    (‖(2 * π)⁻¹ • ξ‖ ^ 2) ^ (s / 2 - k)) : ℝ) : ℂ) • ContinuousLinearMap.id ℂ V), ← Finset.sum_smul,
    Finset.mul_sum, Complex.ofReal_sum]

/-- The remainder `⟨ξ / 2π⟩ ^ s - χ(ξ) ∑_{k < K} (s / 2 choose k) ‖ξ / 2π‖ ^ (s - 2k)` of the
binomial expansion of the Bessel weight after `K` terms. -/
private def besselRemainder (χ : FrequencyCutoff (CoordinateSpace n)) (s : ℝ) (K : ℕ)
    (ξ : CoordinateSpace n) : ℝ :=
  (1 + ‖(2 * π)⁻¹ • ξ‖ ^ 2) ^ (s / 2) -
    χ ξ * ∑ k ∈ Finset.range K, Ring.choose (s / 2) k * (‖(2 * π)⁻¹ • ξ‖ ^ 2) ^ (s / 2 - k)

private theorem besselRemainder_eq (χ : FrequencyCutoff (CoordinateSpace n)) (s : ℝ) (K : ℕ) :
    besselRemainder χ s K = fun ξ ↦ (1 + ‖(2 * π)⁻¹ • ξ‖ ^ 2) ^ (s / 2) -
      χ ξ * ∑ k ∈ Finset.range K, Ring.choose (s / 2) k * (‖(2 * π)⁻¹ • ξ‖ ^ 2) ^ (s / 2 - k) :=
  rfl

private theorem contDiff_besselRemainder (χ : FrequencyCutoff (CoordinateSpace n)) (s : ℝ)
    (K : ℕ) : ContDiff ℝ ∞ (besselRemainder χ s K) := by
  rw [besselRemainder_eq]
  exact contDiff_one_add_norm_smul_sq_rpow_sub_sum (by positivity) χ.contDiff
    (χ.eventuallyEq_zero_of_norm_lt_one (by simp)) _ _

/-- The remainder after `(N + 1) / 2 ≥ N / 2` binomial terms satisfies the symbol estimates of
order `s - N`. -/
private theorem exists_norm_iteratedFDeriv_besselRemainder_le
    (χ : FrequencyCutoff (CoordinateSpace n)) (s : ℝ) (N k : ℕ) :
    ∃ C, ∀ ξ, ‖iteratedFDeriv ℝ k (fun ξ ↦ ((besselRemainder χ s ((N + 1) / 2) ξ : ℝ) : ℂ) •
      ContinuousLinearMap.id ℂ V) ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((s - N - k) / 2) := by
  obtain ⟨C, hC⟩ := exists_norm_iteratedFDeriv_one_add_norm_smul_sq_rpow_sub_sum_le
    (E := CoordinateSpace n) (c := (2 * π)⁻¹) (by positivity) χ.contDiff
    (χ.eventuallyEq_zero_of_norm_lt_one (by simp)) ⟨2, fun ξ ↦ χ.apply_eq_one_of_two_le_norm⟩
    (s / 2) ((N + 1) / 2) k
  rw [← besselRemainder_eq] at hC
  have hN : (N : ℝ) ≤ 2 * ((N + 1) / 2 : ℕ) := by
    exact_mod_cast (by omega : N ≤ 2 * ((N + 1) / 2))
  refine ContinuousLinearMap.exists_norm_iteratedFDeriv_comp_left_le
    (Complex.ofRealCLM.smulRight (ContinuousLinearMap.id ℂ V))
    ((contDiff_besselRemainder χ s _).of_le (mod_cast le_top)) ⟨max C 0, fun ξ ↦ (hC ξ).trans ?_⟩
  calc C * (1 + ‖ξ‖ ^ 2) ^ (s / 2 - ((N + 1) / 2 : ℕ) - k / 2)
      ≤ max C 0 * (1 + ‖ξ‖ ^ 2) ^ (s / 2 - ((N + 1) / 2 : ℕ) - k / 2) := by
        gcongr
        exact le_max_left _ _
    _ ≤ max C 0 * (1 + ‖ξ‖ ^ 2) ^ ((s - N - k) / 2) := by
        gcongr
        · exact le_add_of_nonneg_right (by positivity)
        · linarith

/-- The remainder of the Bessel weight after `N` homogeneous terms, as a symbol of order `s - N`:
it is the remainder of its binomial expansion after `(N + 1) / 2` terms. -/
private def besselPotentialRemainder (χ : FrequencyCutoff (CoordinateSpace n)) (s : ℝ) (N : ℕ) :
    Symbol n V V (s - N) :=
  Symbol.ofFrequency
    (fun ξ ↦ ((besselRemainder χ s ((N + 1) / 2) ξ : ℝ) : ℂ) • ContinuousLinearMap.id ℂ V)
    (contDiff_ofReal_smul_id (contDiff_besselRemainder χ s _))
    (exists_norm_iteratedFDeriv_besselRemainder_le χ s N)

/-- **The Bessel weight is a classical symbol.** The Bessel weight `⟨ξ / 2π⟩ ^ s`
(`TauCeti.Symbol.besselPotential`), as a classical symbol of order `s`: its homogeneous term of
degree `s - j` is `(s / 2 choose j / 2) ‖ξ / 2π‖ ^ (s - j)` for even `j` and zero for odd `j`
(`TauCeti.ClassicalSymbol.term_besselPotential`). -/
def besselPotential (s : ℝ) : ClassicalSymbol n V V s where
  toSymbol := Symbol.besselPotential s
  term := besselPotentialTerm n V s
  exists_remainder' := ⟨default, fun N ↦ ⟨besselPotentialRemainder default s N, fun p ↦ by
    rw [besselPotentialRemainder, Symbol.coefficient_ofFrequency,
      Symbol.coefficient_besselPotential, sum_smul_coefficient_besselPotentialTerm, ← sub_smul,
      besselRemainder, Complex.ofReal_sub]⟩⟩

@[simp]
theorem toSymbol_besselPotential (s : ℝ) :
    (besselPotential s : ClassicalSymbol n V V s).toSymbol = Symbol.besselPotential s :=
  (rfl)

/-- The homogeneous terms of the Bessel weight: the term of degree `s - j` is the binomial term
`(s / 2 choose j / 2) ‖ξ / 2π‖ ^ (s - j)` for even `j`, and zero for odd `j`. -/
theorem term_besselPotential (s : ℝ) (j : ℕ) :
    (besselPotential s : ClassicalSymbol n V V s).term j =
      if Even j then
        ((Ring.choose (s / 2) (j / 2) * (2 * π)⁻¹ ^ (s - j) : ℝ) : ℂ) •
          normRpow (CoordinateSpace n) (CoordinateSpace n) V (s - j)
      else 0 :=
  (rfl)

/-- The principal symbol of the Bessel weight `⟨ξ / 2π⟩ ^ s` is `‖ξ / 2π‖ ^ s`. -/
@[simp]
theorem principal_besselPotential (s : ℝ) :
    (besselPotential s : ClassicalSymbol n V V s).principal =
      (((2 * π)⁻¹ ^ s : ℝ) : ℂ) • normRpow (CoordinateSpace n) (CoordinateSpace n) V s :=
  HomogeneousSymbol.ext_of_ne_zero fun x ξ hξ ↦ by
    rw [principal_def, HomogeneousSymbol.coefficient_castDegree, term_besselPotential,
      ite_eq_left Even.zero, HomogeneousSymbol.coefficient_smul, Pi.smul_apply,
      HomogeneousSymbol.coefficient_smul, Pi.smul_apply, coefficient_normRpow_of_ne_zero _ _ _ hξ,
      coefficient_normRpow_of_ne_zero _ _ _ hξ]
    simp

/-- The pointwise composition of the Bessel weights of orders `s` and `t` is the Bessel weight of
order `s + t`. -/
@[simp]
theorem besselPotential_comp_besselPotential (s t : ℝ) :
    (besselPotential s : ClassicalSymbol n V V s).comp (besselPotential t) =
      besselPotential (s + t) :=
  ext <| by
    rw [toSymbol_comp, toSymbol_besselPotential, toSymbol_besselPotential,
      toSymbol_besselPotential, Symbol.besselPotential_comp_besselPotential]

/-- **The Bessel weight is elliptic**, of every real order `s`. -/
theorem isElliptic_besselPotential (s : ℝ) :
    (besselPotential s : ClassicalSymbol n V V s).IsElliptic := by
  refine isElliptic_def.2 <| HomogeneousSymbol.isElliptic_iff.2 fun x ξ hξ ↦ ?_
  have hpos : (0 : ℝ) < (2 * π)⁻¹ ^ s * ‖ξ‖ ^ s := by
    have := norm_pos_iff.2 hξ
    positivity
  rw [principal_besselPotential, HomogeneousSymbol.coefficient_smul, Pi.smul_apply,
    coefficient_normRpow_of_ne_zero _ _ _ hξ, ← Complex.coe_smul (‖ξ‖ ^ s), smul_smul,
    ContinuousLinearMap.isInvertible_smul_iff (by exact_mod_cast hpos.ne')]
  simpa using ContinuousLinearMap.isInvertible_equiv (f := ContinuousLinearEquiv.refl ℂ V)

end ClassicalSymbol

end TauCeti
