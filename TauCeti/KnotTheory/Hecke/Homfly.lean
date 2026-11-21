/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.Jimbo.Trace
public import TauCeti.KnotTheory.Hecke.RegularTrace
public import TauCeti.KnotTheory.Homfly.Reduced

import Mathlib.Tactic.LinearCombination

/-!
# Comparison of Ocneanu braid invariants with Jimbo and HOMFLY invariants

This module compares the regularized and normalized Ocneanu braid-closure invariants
`TauCeti.MarkovBraid.regularHeckeTrace` (`TauCeti.KnotTheory.Hecke.RegularTrace`) and
`TauCeti.MarkovBraid.heckeTrace` (`TauCeti.KnotTheory.Hecke.Trace`) with the library's native Jimbo
and HOMFLY braid invariants:

* **Jimbo weighted and reduced traces:** over every commutative ring `R`, for all `N : ℕ` and
  `q : Rˣ`, `β.jimboTrace q` equals `δ_N * β.regularHeckeTrace q δ_N ((q ^ N)⁻¹)` with no
  invertibility hypotheses (`jimboTrace_eq_mul_regularHeckeTrace`), and over a field with
  `δ_N ≠ 0`, `β.jimboReducedTrace q` equals both `regularHeckeTrace` and the Ocneanu `heckeTrace`
  at `z = q ^ N / δ_N` (`jimboReducedTrace_eq_heckeTrace`).
* **Two-variable HOMFLY polynomial:** for any homomorphism `f : K →+* R` from a field `K` to a
  commutative ring `R` and any units `q u l : Rˣ` with `u = q - q⁻¹`, evaluating `β.reducedHomfly K`
  at `z = u` and `a = l⁻¹` gives `β.regularHeckeTrace q ((l⁻¹ - l) * u⁻¹) l`—including across the
  zero-factor locus `l = ±1` (`eval₂_reducedHomfly_eq_regularHeckeTrace`)—and coincides with the
  Ocneanu `heckeTrace` whenever `(l⁻¹ - l) * u⁻¹ * z = l⁻¹` (`eval₂_reducedHomfly_eq_heckeTrace`).
  More generally, for any normalized Markov trace `τ` with parameter `z` and any `(C, l)` solving
  `C * l * z = 1` and `C * l⁻¹ * (z - (q - q⁻¹)) = 1`, the same specialization of
  `β.reducedHomfly K` is `β.heckeTrace τ C l`
  (`eval₂_reducedHomfly_eq_heckeTrace_of_isMarkovTrace`). In particular, the positive-rank `sl_N`
  HOMFLY specializations in `RatFunc K` are the corresponding normalized Ocneanu traces, which
  uniquely determine `β.reducedHomfly K`.
* **Finite-colour normalization and zero-factor specializations:** with `c * δ_N = 1`, the
  parameters `C = δ_N`, `l = (q ^ N)⁻¹`, and `z = c * q ^ N` satisfy both Markov normalization
  equations without requiring `q - q⁻¹` to be invertible (`isHeckeNormalization_jimbo`); this is
  checked directly on the two-strand unlink and both single-crossing closures. The normalized
  Ocneanu trace then equals `eval₂ (Int.castRingHom R) q (β.jimboReducedLaurent N)`, and evaluates
  in closed form to `(N : R) ^ (β.componentCount - 1)` at `q = 1` and
  `((-1 : R) ^ (N - 1) * (N : R)) ^ (β.componentCount - 1)` at `q = -1`.

## Main results

* `TauCeti.MarkovBraid.jimboTrace_eq_mul_regularHeckeTrace` and
  `TauCeti.MarkovBraid.jimboReducedTrace_eq_heckeTrace`: comparison with the `N`-colour Jimbo braid
  invariants.
* `TauCeti.MarkovBraid.eval₂_reducedHomfly_eq_regularHeckeTrace`,
  `TauCeti.MarkovBraid.eval₂_reducedHomfly_eq_heckeTrace`, and
  `TauCeti.MarkovBraid.eval₂_homfly_eq_mul_heckeTrace`: comparison with `reducedHomfly` and
  `homfly`.
* `TauCeti.isHeckeNormalization_jimbo`,
  `TauCeti.heckeBraidInvariant_ocneanuTrace_mk_eq_mul_jimboTrace`, and
  `TauCeti.heckeBraidInvariant_ocneanuTrace_mk_eq_jimboReducedTrace`: the finite-colour parameters
  satisfy `TauCeti.IsHeckeNormalization`, and the descended invariant is `c * jimboTrace` over
  any commutative ring and `jimboReducedTrace` over a field.
* `TauCeti.MarkovBraid.heckeTrace_ocneanuTrace_eq_eval₂_jimboReducedLaurent`,
  `TauCeti.MarkovBraid.heckeTrace_ocneanuTrace_one_eq_pow_componentCount`, and
  `TauCeti.MarkovBraid.heckeTrace_ocneanuTrace_neg_one_eq_pow_componentCount`: regular comparison
  with `jimboReducedLaurent` and closed-form evaluations at `q = ±1`.
* `TauCeti.MarkovBraid.eval₂_reducedHomfly_eq_heckeTrace_of_isMarkovTrace`,
  `TauCeti.MarkovBraid.eval₂_homfly_eq_mul_heckeTrace_of_isMarkovTrace`, and
  `TauCeti.MarkovBraid.reducedHomfly_eq_of_heckeTrace_ocneanuTrace`: comparison of `reducedHomfly`
  and `homfly` with arbitrary normalized Hecke Markov traces and determination by positive-rank
  Ocneanu traces.

## References

* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*,
  Ann. of Math. 126 (1987), 335–388, Sections 5–6.
* V. G. Turaev, *The Yang-Baxter equation and invariants of links*, Invent. Math. 92 (1988),
  527–553.
-/

public section

open LaurentPolynomial
open scoped BigOperators

namespace TauCeti

open BraidGroup InfiniteTypeAHeckeAlgebra KnotTheory

section JimboComparison

namespace MarkovBraid

/-- **Unconditional comparison of `jimboTrace` with `regularHeckeTrace`.** Over every commutative
ring `R`, for every number of colours `N`, unit `q : Rˣ`, and braid `β`, the writhe-normalized
`N`-colour Jimbo trace equals the quantum dimension `δ_N` times `regularHeckeTrace` at
`C = δ_N` and `l = (q ^ N)⁻¹`. No division by `δ_N` or `q - q⁻¹` is required. -/
theorem jimboTrace_eq_mul_regularHeckeTrace {R : Type*} [CommRing R] (N : ℕ) (β : MarkovBraid)
    (q : Rˣ) :
    β.jimboTrace (N := N) q =
      (∑ a : Fin N, jimboWeight q a) *
        β.regularHeckeTrace q (∑ a : Fin N, jimboWeight q a) ((q ^ N)⁻¹) := by
  rcases β with ⟨n, b⟩
  rw [jimboTrace_def, regularHeckeTrace_def, ← TypeAHeckeAlgebra.jimboWeightedTrace_braidHom,
    TypeAHeckeAlgebra.jimboWeightedTrace_eq_mul_homogenizedOcneanuTrace,
    TypeAHeckeAlgebra.toInfinite_braidHom, inv_inv, inv_zpow', zpow_neg]
  ring

/-- When `c * δ_N = 1`, `jimboTrace` equals `δ_N` times the normalized Ocneanu `heckeTrace` at
Markov parameter `c * q ^ N`. -/
theorem jimboTrace_eq_mul_heckeTrace {R : Type*} [CommRing R] {N : ℕ} {q : Rˣ} {c : R}
    (hc : c * ∑ a : Fin N, jimboWeight q a = 1) (β : MarkovBraid) :
    β.jimboTrace (N := N) q =
      (∑ a : Fin N, jimboWeight q a) *
        β.heckeTrace (ocneanuTrace R q (c * ↑(q ^ N)))
          (∑ a : Fin N, jimboWeight q a) ((q ^ N)⁻¹) := by
  have hz : (∑ a : Fin N, jimboWeight q a) * (c * ↑(q ^ N)) = ↑((q ^ N)⁻¹)⁻¹ := by
    rw [inv_inv, ← mul_assoc, mul_comm _ c, hc, one_mul]
  rw [jimboTrace_eq_mul_regularHeckeTrace, regularHeckeTrace_eq_heckeTrace_of_mul_eq β hz]

/-- Rescaled form of `jimboTrace_eq_mul_heckeTrace`: when `c * δ_N = 1`, multiplying `jimboTrace` by
`c` recovers the normalized Ocneanu `heckeTrace` directly. -/
theorem mul_jimboTrace_eq_heckeTrace {R : Type*} [CommRing R] {N : ℕ} {q : Rˣ} {c : R}
    (hc : c * ∑ a : Fin N, jimboWeight q a = 1) (β : MarkovBraid) :
    c * β.jimboTrace (N := N) q =
      β.heckeTrace (ocneanuTrace R q (c * ↑(q ^ N)))
        (∑ a : Fin N, jimboWeight q a) ((q ^ N)⁻¹) := by
  rw [jimboTrace_eq_mul_heckeTrace hc, ← mul_assoc, hc, one_mul]

/-- Over a field where the `N`-colour quantum dimension `δ_N` is nonzero, `jimboReducedTrace`
coincides with `regularHeckeTrace` at `C = δ_N` and `l = (q ^ N)⁻¹`. -/
theorem jimboReducedTrace_eq_regularHeckeTrace {K : Type*} [Field K] {N : ℕ} (β : MarkovBraid)
    {q : Kˣ} (hδ : (∑ a : Fin N, jimboWeight q a) ≠ 0) :
    β.jimboReducedTrace (N := N) q =
      β.regularHeckeTrace q (∑ a : Fin N, jimboWeight q a) ((q ^ N)⁻¹) := by
  rw [jimboReducedTrace_def, jimboTrace_eq_mul_regularHeckeTrace, mul_div_cancel_left₀ _ hδ]

/-- **Comparison of `jimboReducedTrace` with the Ocneanu `heckeTrace`.** Over a field where the
`N`-colour quantum dimension `δ_N` is nonzero, `jimboReducedTrace` equals the normalized Ocneanu
braid invariant at `z = q ^ N / δ_N`, `C = δ_N`, and `l = (q ^ N)⁻¹`. -/
theorem jimboReducedTrace_eq_heckeTrace {K : Type*} [Field K] {N : ℕ} (β : MarkovBraid)
    {q : Kˣ} (hδ : (∑ a : Fin N, jimboWeight q a) ≠ 0) :
    β.jimboReducedTrace (N := N) q =
      β.heckeTrace (ocneanuTrace K q (↑(q ^ N) / ∑ a : Fin N, jimboWeight q a))
        (∑ a : Fin N, jimboWeight q a) ((q ^ N)⁻¹) := by
  have hz : (∑ a : Fin N, jimboWeight q a) * (↑(q ^ N) / ∑ a : Fin N, jimboWeight q a) =
      ↑((q ^ N)⁻¹)⁻¹ := by
    rw [inv_inv, mul_div_cancel₀ _ hδ]
  rw [jimboReducedTrace_eq_regularHeckeTrace β hδ, regularHeckeTrace_eq_heckeTrace_of_mul_eq β hz]

end MarkovBraid

end JimboComparison

section HomflyComparison

variable {K R : Type*} [Field K] [CommRing R]

namespace MarkovBraid

/-- **Comparison of `reducedHomfly` with `regularHeckeTrace`.** For any ring homomorphism
`f : K →+* R` from a field `K` to a commutative ring `R` and any units `q u l : Rˣ` with
`u = q - q⁻¹`, evaluating `β.reducedHomfly K` at `z = u` and `a = l⁻¹` yields
`β.regularHeckeTrace q ((l⁻¹ - l) * u⁻¹) l`. Because `regularHeckeTrace` requires no inverse of
`C = (l⁻¹ - l) * u⁻¹`, this holds across zero-factor specializations such as `l = ±1`. -/
theorem eval₂_reducedHomfly_eq_regularHeckeTrace (β : MarkovBraid) (f : K →+* R)
    (q u l : Rˣ) (hu : (u : R) = (q : R) - ↑q⁻¹) :
    eval₂ (eval₂ f u) l⁻¹ (β.reducedHomfly K) =
      β.regularHeckeTrace q (((↑l⁻¹ : R) - (l : R)) * ↑u⁻¹) l := by
  let e : LaurentPolynomial (LaurentPolynomial K) →+* R := eval₂ (eval₂ f u) l⁻¹
  have heT1 : e (LaurentPolynomial.T 1) = (↑l⁻¹ : R) := by simp [e]
  have heTneg1 : e (LaurentPolynomial.T (-1)) = (l : R) := by simp [e]
  have hez : e (C (LaurentPolynomial.T 1)) = (u : R) := by simp [e]
  have heU : e (homflyUnknot K) = ((↑l⁻¹ : R) - (l : R)) * ↑u⁻¹ := by
    simp [e]
  have hstab : (((↑l⁻¹ : R) - (l : R)) * ↑u⁻¹) * ((q : R) - ↑q⁻¹) = (↑l⁻¹ : R) - (l : R) := by
    rw [← hu, mul_assoc, Units.inv_mul, mul_one]
  have h := eq_regularHeckeTrace_of_skein hstab
    (F := fun γ ↦ e (γ.reducedHomfly K))
    (fun _ _ h ↦ congrArg e (h.reducedHomfly_eq K))
    (fun n c i ↦ ?_)
    (fun n b ↦ ?_)
    (by simp [e])
  · exact congrFun h β
  · simpa only [one_mul, map_sub, map_mul, heT1, heTneg1, hez, hu] using
      congrArg e (reducedHomfly_skein K (1 : BraidGroup (n + 1)) c i)
  · rw [reducedHomfly_strandIncl, map_mul, heU]

/-- **Comparison of `reducedHomfly` with the Ocneanu `heckeTrace`.** Whenever `z : R` satisfies
`((l⁻¹ - l) * u⁻¹) * z = l⁻¹` (in particular whenever `((l⁻¹ - l) * u⁻¹) * l * z = 1`), evaluating
`β.reducedHomfly K` at `z_HOMFLY = u = q - q⁻¹` and `a = l⁻¹` gives the normalized Ocneanu trace
`β.heckeTrace (ocneanuTrace R q z) ((l⁻¹ - l) * u⁻¹) l`. -/
theorem eval₂_reducedHomfly_eq_heckeTrace (β : MarkovBraid) (f : K →+* R)
    (q u l : Rˣ) (hu : (u : R) = (q : R) - ↑q⁻¹) {z : R}
    (hz : (((↑l⁻¹ : R) - (l : R)) * ↑u⁻¹) * z = ↑l⁻¹) :
    eval₂ (eval₂ f u) l⁻¹ (β.reducedHomfly K) =
      β.heckeTrace (ocneanuTrace R q z) (((↑l⁻¹ : R) - (l : R)) * ↑u⁻¹) l := by
  rw [eval₂_reducedHomfly_eq_regularHeckeTrace β f q u l hu,
    regularHeckeTrace_eq_heckeTrace_of_mul_eq β hz]

/-- Field form of `eval₂_reducedHomfly_eq_heckeTrace`: over a field `L` with `q - q⁻¹ ≠ 0` and
`l⁻¹ - l ≠ 0`, `reducedHomfly` specializes to Jones's Ocneanu braid invariant with Markov parameter
`z = l⁻¹ * (q - q⁻¹) / (l⁻¹ - l)` and unlink factor `C = (l⁻¹ - l) / (q - q⁻¹)`. -/
theorem eval₂_reducedHomfly_eq_heckeTrace_div {L : Type*} [Field L] (β : MarkovBraid)
    (f : K →+* L) {q l : Lˣ} (hq : (q : L) - ↑q⁻¹ ≠ 0) (hl : (↑l⁻¹ : L) - (l : L) ≠ 0) :
    eval₂ (eval₂ f (Units.mk0 ((q : L) - ↑q⁻¹) hq)) l⁻¹ (β.reducedHomfly K) =
      β.heckeTrace
        (ocneanuTrace L q (((↑l⁻¹ : L) * ((q : L) - ↑q⁻¹)) / ((↑l⁻¹ : L) - (l : L))))
        (((↑l⁻¹ : L) - (l : L)) / ((q : L) - ↑q⁻¹)) l := by
  have hC : (((↑l⁻¹ : L) - (l : L)) * ↑(Units.mk0 ((q : L) - ↑q⁻¹) hq)⁻¹) =
      ((↑l⁻¹ : L) - (l : L)) / ((q : L) - ↑q⁻¹) := by
    simp [div_eq_mul_inv]
  have hz : (((↑l⁻¹ : L) - (l : L)) / ((q : L) - ↑q⁻¹)) *
      (((↑l⁻¹ : L) * ((q : L) - ↑q⁻¹)) / ((↑l⁻¹ : L) - (l : L))) = ↑l⁻¹ := by
    field_simp
  rw [eval₂_reducedHomfly_eq_regularHeckeTrace β f q (Units.mk0 ((q : L) - ↑q⁻¹) hq) l rfl,
    hC, regularHeckeTrace_eq_heckeTrace_of_mul_eq β hz]

/-- **Comparison of unreduced `homfly` with `regularHeckeTrace`.** Evaluating `β.homfly K` at
`z_HOMFLY = u = q - q⁻¹` and `a = l⁻¹` gives `((l⁻¹ - l) * u⁻¹)` times `regularHeckeTrace`,
valid across all `l : Rˣ` including `l = ±1`. -/
theorem eval₂_homfly_eq_mul_regularHeckeTrace (β : MarkovBraid) (f : K →+* R)
    (q u l : Rˣ) (hu : (u : R) = (q : R) - ↑q⁻¹) :
    eval₂ (eval₂ f u) l⁻¹ (β.homfly K) =
      (((↑l⁻¹ : R) - (l : R)) * ↑u⁻¹) *
        β.regularHeckeTrace q (((↑l⁻¹ : R) - (l : R)) * ↑u⁻¹) l := by
  rw [← homflyUnknot_mul_reducedHomfly, _root_.map_mul, eval₂_homflyUnknot, inv_inv,
    eval₂_reducedHomfly_eq_regularHeckeTrace β f q u l hu]

/-- **Comparison of unreduced `homfly` with the Ocneanu `heckeTrace`.** When
`((l⁻¹ - l) * u⁻¹) * z = l⁻¹`, evaluating `β.homfly K` at `z_HOMFLY = u = q - q⁻¹` and `a = l⁻¹`
gives `((l⁻¹ - l) * u⁻¹)` times the normalized Ocneanu trace. -/
theorem eval₂_homfly_eq_mul_heckeTrace (β : MarkovBraid) (f : K →+* R)
    (q u l : Rˣ) (hu : (u : R) = (q : R) - ↑q⁻¹) {z : R}
    (hz : (((↑l⁻¹ : R) - (l : R)) * ↑u⁻¹) * z = ↑l⁻¹) :
    eval₂ (eval₂ f u) l⁻¹ (β.homfly K) =
      (((↑l⁻¹ : R) - (l : R)) * ↑u⁻¹) *
        β.heckeTrace (ocneanuTrace R q z) (((↑l⁻¹ : R) - (l : R)) * ↑u⁻¹) l := by
  rw [eval₂_homfly_eq_mul_regularHeckeTrace β f q u l hu,
    regularHeckeTrace_eq_heckeTrace_of_mul_eq β hz]

end MarkovBraid

end HomflyComparison

section FiniteColour

variable {R : Type*} [CommRing R] {q : Rˣ} {N : ℕ} {c : R}

/-- With `δ = ∑ a : Fin N, jimboWeight q a` and `c * δ = 1`, the parameters `C = δ`,
`l = (q ^ N)⁻¹`, and `z = c * q ^ N` satisfy both Hecke Markov normalization equations
`IsHeckeNormalization q (c * q ^ N) δ ((q ^ N)⁻¹)`. No invertibility of `q - q⁻¹` is required. -/
theorem isHeckeNormalization_jimbo (hc : c * ∑ a : Fin N, jimboWeight q a = 1) :
    IsHeckeNormalization q (c * ↑(q ^ N)) (∑ a : Fin N, jimboWeight q a) ((q ^ N)⁻¹) := by
  refine ⟨?_, ?_⟩
  · have hq : (↑((q ^ N)⁻¹ : Rˣ) : R) * ↑(q ^ N) = 1 := Units.inv_mul (q ^ N)
    linear_combination (c * ∑ a : Fin N, jimboWeight q a) * hq + hc
  · rw [inv_inv]
    have hdim := jimboWeight_sum (N := N) q
    have hq : (↑(q ^ N) : R) * ↑((q⁻¹) ^ N) = 1 := by
      rw [inv_pow]
      exact Units.mul_inv (q ^ N)
    linear_combination -((↑(q ^ N) : R)) * hdim + ((↑(q ^ N) : R) ^ 2) * hc + hq

namespace MarkovBraid

/-- Direct check of the finite-colour Ocneanu normalization on the two-strand unlink `⟨1, 1⟩`:
both sides evaluate to the quantum dimension `∑ a : Fin N, jimboWeight q a`. -/
theorem heckeTrace_ocneanuTrace_two_strand_one_eq_mul_jimboTrace
    (hc : c * ∑ a : Fin N, jimboWeight q a = 1) :
    heckeTrace ⟨1, 1⟩ (ocneanuTrace R q (c * ↑(q ^ N)))
        (∑ a : Fin N, jimboWeight q a) ((q ^ N)⁻¹) =
      c * jimboTrace (N := N) ⟨1, 1⟩ q := by
  rw [heckeTrace_one (isMarkovTrace_ocneanuTrace _).map_one, jimboTrace_one, pow_one, pow_two,
    ← mul_assoc, hc, one_mul]

/-- Direct check of the finite-colour Ocneanu normalization on the positive single-crossing
two-strand closure `⟨1, σ₀⟩`: both sides evaluate to `1`. -/
theorem heckeTrace_ocneanuTrace_sigma_two_eq_mul_jimboTrace
    (hc : c * ∑ a : Fin N, jimboWeight q a = 1) :
    heckeTrace ⟨1, BraidGroup.sigma (n := 2) 0⟩ (ocneanuTrace R q (c * ↑(q ^ N)))
        (∑ a : Fin N, jimboWeight q a) ((q ^ N)⁻¹) =
      c * jimboTrace (N := N) ⟨1, BraidGroup.sigma (n := 2) 0⟩ q := by
  have hjimbo : jimboTrace (N := N) ⟨1, BraidGroup.sigma (n := 2) 0⟩ q =
      ∑ a : Fin N, jimboWeight q a := by
    simpa using markovEquiv_sigma_last_one_one.jimboTrace_eq (N := N) q
  rw [heckeTrace_sigma_two (isMarkovTrace_ocneanuTrace _) _ _
      (isHeckeNormalization_jimbo hc).stabilize, hjimbo, hc]

/-- Direct check of the finite-colour Ocneanu normalization on the negative single-crossing
two-strand closure `⟨1, σ₀⁻¹⟩`: both sides evaluate to `1`. -/
theorem heckeTrace_ocneanuTrace_sigma_two_inv_eq_mul_jimboTrace
    (hc : c * ∑ a : Fin N, jimboWeight q a = 1) :
    heckeTrace ⟨1, (BraidGroup.sigma (n := 2) 0)⁻¹⟩ (ocneanuTrace R q (c * ↑(q ^ N)))
        (∑ a : Fin N, jimboWeight q a) ((q ^ N)⁻¹) =
      c * jimboTrace (N := N) ⟨1, (BraidGroup.sigma (n := 2) 0)⁻¹⟩ q := by
  have hjimbo : jimboTrace (N := N) ⟨1, (BraidGroup.sigma (n := 2) 0)⁻¹⟩ q =
      ∑ a : Fin N, jimboWeight q a := by
    simpa using markovEquiv_sigma_last_inv_one_one.jimboTrace_eq (N := N) q
  rw [heckeTrace_sigma_two_inv (isMarkovTrace_ocneanuTrace _) _ _
      (isHeckeNormalization_jimbo hc).stabilizeInv, hjimbo, hc]

end MarkovBraid

/-- On `Quot MarkovEquiv`, `heckeBraidInvariant` of the Ocneanu trace at `c * q ^ N` agrees with
`c * β.jimboTrace q` whenever `c` inverts the `N`-colour quantum dimension, over any commutative
ring. -/
theorem heckeBraidInvariant_ocneanuTrace_mk_eq_mul_jimboTrace (β : MarkovBraid)
    (hc : c * ∑ a : Fin N, jimboWeight q a = 1) :
    heckeBraidInvariant (isMarkovTrace_ocneanuTrace (q := q) (c * ↑(q ^ N)))
        (∑ a : Fin N, jimboWeight q a) ((q ^ N)⁻¹)
        (isHeckeNormalization_jimbo hc).stabilize
        (isHeckeNormalization_jimbo hc).stabilizeInv
        (Quot.mk MarkovEquiv β) =
      c * β.jimboTrace (N := N) q :=
  (heckeBraidInvariant_mk _ _ _ _ _ β).trans (β.mul_jimboTrace_eq_heckeTrace hc).symm

/-- On the quotient `Quot MarkovEquiv`, the descended finite-colour Ocneanu braid invariant agrees
with `MarkovBraid.jimboReducedTrace` whenever `[N]_q ≠ 0`. -/
theorem heckeBraidInvariant_ocneanuTrace_mk_eq_jimboReducedTrace {K : Type*} [Field K]
    (β : MarkovBraid) (q : Kˣ) (hδ : (∑ a : Fin N, jimboWeight q a) ≠ 0) :
    heckeBraidInvariant
        (isMarkovTrace_ocneanuTrace ((∑ a : Fin N, jimboWeight q a)⁻¹ * ↑(q ^ N)))
        (∑ a : Fin N, jimboWeight q a) ((q ^ N)⁻¹)
        (isHeckeNormalization_jimbo (inv_mul_cancel₀ hδ)).stabilize
        (isHeckeNormalization_jimbo (inv_mul_cancel₀ hδ)).stabilizeInv
        (Quot.mk MarkovEquiv β) =
      β.jimboReducedTrace (N := N) q := by
  rw [heckeBraidInvariant_mk, β.jimboReducedTrace_eq_heckeTrace hδ, div_eq_inv_mul]

end FiniteColour

/-! ### Universal regular comparison and zero-factor specializations -/

section ZeroFactorSpecializations

namespace MarkovBraid

/-- Whenever `c` inverts `[N]_q` in `R`, the finite-colour normalized Ocneanu trace agrees with the
specialization at `q` of the universal Laurent polynomial `β.jimboReducedLaurent N`. This requires
no hypothesis on `q - q⁻¹`, so it applies at `q = ±1` whenever `N` is invertible in `R`. -/
theorem heckeTrace_ocneanuTrace_eq_eval₂_jimboReducedLaurent {R : Type*} [CommRing R]
    (β : MarkovBraid) (N : ℕ) {q : Rˣ} {c : R}
    (hc : c * ∑ a : Fin N, jimboWeight q a = 1) :
    β.heckeTrace (ocneanuTrace R q (c * ↑(q ^ N)))
        (∑ a : Fin N, jimboWeight q a) ((q ^ N)⁻¹) =
      eval₂ (Int.castRingHom R) q (β.jimboReducedLaurent N) := by
  rw [← β.mul_jimboTrace_eq_heckeTrace hc, ← β.eval₂_jimboReducedLaurent_mul_sum N q]
  calc
    c * (eval₂ (Int.castRingHom R) q (β.jimboReducedLaurent N) * ∑ a : Fin N, jimboWeight q a) =
      eval₂ (Int.castRingHom R) q (β.jimboReducedLaurent N) *
        (c * ∑ a : Fin N, jimboWeight q a) := by ring
    _ = eval₂ (Int.castRingHom R) q (β.jimboReducedLaurent N) := by rw [hc, mul_one]

/-- At the zero-factor specialization `q = 1` (where `q - q⁻¹ = 0`), when `c * N = 1` in `R`, the
normalized Ocneanu trace with parameter `c`, unlink factor `N`, and unit `1` evaluates in closed
form to `N ^ (β.componentCount - 1)`. -/
theorem heckeTrace_ocneanuTrace_one_eq_pow_componentCount {R : Type*} [CommRing R]
    (β : MarkovBraid) (N : ℕ) {c : R} (hc : c * (N : R) = 1) :
    β.heckeTrace (ocneanuTrace R (1 : Rˣ) c) (N : R) (1 : Rˣ) =
      (N : R) ^ (β.componentCount - 1) := by
  have hpos : (N : R) * ((1 : Rˣ) : R) * c = 1 := by simpa [mul_comm] using hc
  exact β.heckeTrace_eq_pow_componentCount_of_sub_inv_eq_zero (isMarkovTrace_ocneanuTrace c)
    hpos (by simpa using hpos) (by simp)

/-- At the zero-factor specialization `q = -1` (where `q - q⁻¹ = 0`), when
`c * ((-1) ^ (N - 1) * N) = 1` in `R`, the normalized Ocneanu trace evaluates in closed form to
`((-1) ^ (N - 1) * N) ^ (β.componentCount - 1)`. -/
theorem heckeTrace_ocneanuTrace_neg_one_eq_pow_componentCount {R : Type*} [CommRing R]
    (β : MarkovBraid) (N : ℕ) {c : R}
    (hc : c * ((-1 : R) ^ (N - 1) * (N : R)) = 1) :
    β.heckeTrace (ocneanuTrace R (-1 : Rˣ) (c * (-1 : R) ^ N))
        ((-1 : R) ^ (N - 1) * (N : R)) ((-1 : Rˣ) ^ N) =
      ((-1 : R) ^ (N - 1) * (N : R)) ^ (β.componentCount - 1) := by
  have hsq : ((-1 : R) ^ N) * ((-1 : R) ^ N) = 1 := by
    rw [← mul_pow]
    simp
  have hpos : ((-1 : R) ^ (N - 1) * (N : R)) * ↑((-1 : Rˣ) ^ N) * (c * (-1 : R) ^ N) = 1 := by
    simp only [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]
    linear_combination (c * ((-1 : R) ^ (N - 1) * (N : R))) * hsq + hc
  have hε : (↑(((-1 : Rˣ) ^ N)⁻¹) : R) = ↑((-1 : Rˣ) ^ N) := by
    rw [← inv_pow, inv_neg, inv_one]
  exact β.heckeTrace_eq_pow_componentCount_of_sub_inv_eq_zero
    (isMarkovTrace_ocneanuTrace (c * (-1 : R) ^ N)) hpos (by simpa [hε] using hpos) (by simp)

end MarkovBraid

end ZeroFactorSpecializations

/-! ### HOMFLY comparison with arbitrary normalized Hecke Markov traces -/

section HeckeNormalizationComparison

namespace KnotTheory

/-- Under the Markov normalization equations `IsHeckeNormalization q z C l`, when `q - q⁻¹` is a
unit `u : Rˣ`, evaluating `homflyUnknot K` at `a = l⁻¹` and `z = u` produces the split-unknot
factor `C`. -/
theorem eval₂_homflyUnknot_eq_of_isHeckeNormalization (K : Type*) [Field K]
    {R : Type*} [CommRing R] (φ : K →+* R) {q l u : Rˣ} {z C : R}
    (hnorm : IsHeckeNormalization q z C l)
    (hu : (u : R) = (q : R) - ↑q⁻¹) :
    eval₂ (eval₂ φ u) l⁻¹ (homflyUnknot K) = C := by
  rw [eval₂_homflyUnknot, inv_inv, ← hnorm.mul_sub_inv_eq_inv_sub, ← hu, mul_assoc,
    Units.mul_inv, mul_one]

end KnotTheory

namespace MarkovBraid

/-- **Comparison of `reducedHomfly` with any normalized Hecke Markov trace.** Let `τ` be a
normalized Markov trace with parameter `z` on `InfiniteTypeAHeckeAlgebra R q`, let `(C, l)` satisfy
the positive and negative Markov normalization equations, and suppose `q - q⁻¹` is a unit `u : Rˣ`.
Then evaluating `β.reducedHomfly K` at `a = l⁻¹` and `z = u` equals `β.heckeTrace τ C l`. -/
theorem eval₂_reducedHomfly_eq_heckeTrace_of_isMarkovTrace (K : Type*) [Field K]
    {R : Type*} [CommRing R] (β : MarkovBraid) (φ : K →+* R)
    {q l u : Rˣ} {z C : R} {τ : InfiniteTypeAHeckeAlgebra R q →ₗ[R] R}
    (hτ : IsMarkovTrace z τ)
    (hpos : C * (l : R) * z = 1)
    (hneg : C * (↑l⁻¹ : R) * (z - ((q : R) - ↑q⁻¹)) = 1)
    (hu : (u : R) = (q : R) - ↑q⁻¹) :
    eval₂ (eval₂ φ u) l⁻¹ (β.reducedHomfly K) = β.heckeTrace τ C l := by
  have hunknot : eval₂ (eval₂ φ u) l⁻¹ (homflyUnknot K) = C :=
    eval₂_homflyUnknot_eq_of_isHeckeNormalization K φ ⟨hpos, hneg⟩ hu
  refine congrFun (eq_heckeTrace_of_skein hτ hpos hneg
    (F := fun γ ↦ eval₂ (eval₂ φ u) l⁻¹ (γ.reducedHomfly K))
    (fun _ _ h ↦ congrArg _ (h.reducedHomfly_eq K)) ?_ ?_ ?_) β
  · intro m c i
    have hs := congrArg (eval₂ (eval₂ φ u) l⁻¹) (reducedHomfly_skein K 1 c i)
    simpa only [one_mul, map_sub, map_mul, eval₂_T, eval₂_C, zpow_one, zpow_neg_one, inv_inv,
      hu] using hs
  · intro m b
    rw [reducedHomfly_strandIncl, map_mul, hunknot]
  · simp

/-- **Comparison of the unreduced `homfly` polynomial with any normalized Hecke Markov trace.**
Under the hypotheses of `eval₂_reducedHomfly_eq_heckeTrace_of_isMarkovTrace`, evaluating
`β.homfly K` at `a = l⁻¹` and `z = u` equals `C * β.heckeTrace τ C l`. -/
theorem eval₂_homfly_eq_mul_heckeTrace_of_isMarkovTrace (K : Type*) [Field K]
    {R : Type*} [CommRing R] (β : MarkovBraid) (φ : K →+* R)
    {q l u : Rˣ} {z C : R} {τ : InfiniteTypeAHeckeAlgebra R q →ₗ[R] R}
    (hτ : IsMarkovTrace z τ)
    (hpos : C * (l : R) * z = 1)
    (hneg : C * (↑l⁻¹ : R) * (z - ((q : R) - ↑q⁻¹)) = 1)
    (hu : (u : R) = (q : R) - ↑q⁻¹) :
    eval₂ (eval₂ φ u) l⁻¹ (β.homfly K) = C * β.heckeTrace τ C l := by
  rw [← homflyUnknot_mul_reducedHomfly K β, map_mul,
    eval₂_homflyUnknot_eq_of_isHeckeNormalization K φ ⟨hpos, hneg⟩ hu,
    eval₂_reducedHomfly_eq_heckeTrace_of_isMarkovTrace K β φ hτ hpos hneg hu]

/-- Every positive-rank `sl_N` HOMFLY specialization of `β.reducedHomfly K` in `RatFunc K` equals
the corresponding finite-colour normalized Ocneanu trace. -/
theorem homflySpecialization_reducedHomfly_eq_heckeTrace_ocneanuTrace (K : Type*) [Field K]
    (β : MarkovBraid) (N : ℕ) :
    let q : (RatFunc K)ˣ := Units.mk0 (RatFunc.X : RatFunc K) RatFunc.X_ne_zero
    let δ : RatFunc K := ∑ a : Fin (N + 1), jimboWeight q a
    homflySpecialization K (N + 1) (β.reducedHomfly K) =
      β.heckeTrace (ocneanuTrace (RatFunc K) q (δ⁻¹ * ↑(q ^ (N + 1)))) δ ((q ^ (N + 1))⁻¹) := by
  dsimp only
  rw [homflySpecialization_reducedHomfly,
    β.jimboReducedTrace_eq_heckeTrace (jimboWeight_sum_X_ne_zero N), div_eq_inv_mul]

/-- Every positive-rank `sl_N` HOMFLY specialization of the unreduced `β.homfly K` in `RatFunc K`
equals the quantum dimension times the finite-colour normalized Ocneanu trace. -/
theorem homflySpecialization_homfly_eq_mul_heckeTrace_ocneanuTrace (K : Type*) [Field K]
    (β : MarkovBraid) (N : ℕ) :
    let q : (RatFunc K)ˣ := Units.mk0 (RatFunc.X : RatFunc K) RatFunc.X_ne_zero
    let δ : RatFunc K := ∑ a : Fin (N + 1), jimboWeight q a
    homflySpecialization K (N + 1) (β.homfly K) =
      δ * β.heckeTrace (ocneanuTrace (RatFunc K) q (δ⁻¹ * ↑(q ^ (N + 1))))
        δ ((q ^ (N + 1))⁻¹) := by
  dsimp only
  rw [← homflyUnknot_mul_reducedHomfly, map_mul, homflySpecialization_homflyUnknot,
    homflySpecialization_reducedHomfly_eq_heckeTrace_ocneanuTrace]

/-- The positive-rank finite-colour normalized Ocneanu traces uniquely determine the two-variable
reduced HOMFLY polynomial `β.reducedHomfly K`. -/
theorem reducedHomfly_eq_of_heckeTrace_ocneanuTrace (K : Type*) [Field K] {β : MarkovBraid}
    {P : LaurentPolynomial (LaurentPolynomial K)}
    (h : ∀ N : ℕ,
      let q : (RatFunc K)ˣ := Units.mk0 (RatFunc.X : RatFunc K) RatFunc.X_ne_zero
      let δ : RatFunc K := ∑ a : Fin (N + 1), jimboWeight q a
      homflySpecialization K (N + 1) P =
        β.heckeTrace (ocneanuTrace (RatFunc K) q (δ⁻¹ * ↑(q ^ (N + 1))))
          δ ((q ^ (N + 1))⁻¹)) :
    β.reducedHomfly K = P := by
  refine reducedHomfly_eq_of_homflySpecialization_eq K fun N ↦ ?_
  rw [β.jimboReducedTrace_eq_heckeTrace (jimboWeight_sum_X_ne_zero N), div_eq_inv_mul]
  exact h N

end MarkovBraid

end HeckeNormalizationComparison

end TauCeti
