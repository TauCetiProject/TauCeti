/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.Jimbo.Trace
public import TauCeti.KnotTheory.Hecke
public import TauCeti.KnotTheory.Homfly.Reduced
import Mathlib.Tactic.LinearCombination

/-!
# Comparison of the normalized Hecke trace with Jimbo traces and HOMFLY

This file compares the normalized universal Hecke braid trace `MarkovBraid.heckeTrace` and its
Markov-quotient descent `heckeBraidInvariant` with the finite-colour Jimbo braid traces and the
two-variable HOMFLY polynomial `MarkovBraid.homfly` / `MarkovBraid.reducedHomfly`.

1. **Finite-colour Turaev–Jimbo comparison over commutative rings.** Given `N` colours, unit
   parameter `q : Rˣ`, and `c : R` inverting the quantum dimension
   `δ = ∑ a : Fin N, jimboWeight q a`, the choices `C = δ`, `l = (q ^ N)⁻¹`, and
   `z = c * q ^ N` satisfy both Markov normalization equations without requiring `q - q⁻¹` to be
   invertible (`KnotTheory.jimboHeckeNormalization_pos`,
   `KnotTheory.jimboHeckeNormalization_neg`). After checking this normalization directly on the
   two-strand unlink and both single-crossing closures, `heckeTrace_ocneanuTrace_eq_mul_jimboTrace`
   identifies the normalized Ocneanu trace with `c * β.jimboTrace q`, and over a field with
   `[N]_q ≠ 0` with `β.jimboReducedTrace q` (`heckeTrace_ocneanuTrace_eq_jimboReducedTrace`).
2. **Universal regular finite-colour comparison and zero-factor specializations.** For `N ≠ 0`,
   whenever `[N]_q` is invertible in `R` (including at `q = ±1` when `N` is invertible in `R`),
   the normalized Ocneanu trace equals `eval₂ (Int.castRingHom R) q (β.jimboReducedLaurent N)`,
   giving `(N : R) ^ (β.componentCount - 1)` at `q = 1` and
   `((-1 : R) ^ (N - 1) * (N : R)) ^ (β.componentCount - 1)` at `q = -1`. Dually, whenever
   `q - q⁻¹` is a unit `u : Rˣ` (including at quantum roots of unity where `[N]_q = 0`),
   evaluating `β.reducedHomfly K` at `a = q ^ N` and `z = u` agrees with
   `eval₂ (Int.castRingHom R) q (β.jimboReducedLaurent N)` without any nonvanishing hypothesis on
   `[N]_q` (`MarkovBraid.eval₂_reducedHomfly_eq_eval₂_jimboReducedLaurent`).
3. **Two-variable HOMFLY comparison.** For any normalized Markov trace `τ` with parameter `z`,
   solving `C * l * z = 1` and `C * l⁻¹ * (z - (q - q⁻¹)) = 1` over a commutative ring `R` where
   `q - q⁻¹` is a unit `u : Rˣ` identifies the specialization `a ↦ l⁻¹`, `z ↦ u` of
   `β.reducedHomfly K` with `β.heckeTrace τ C l` (`MarkovBraid.eval₂_reducedHomfly_eq_heckeTrace`)
   and of `β.homfly K` with `C * β.heckeTrace τ C l` (`MarkovBraid.eval₂_homfly_eq_mul_heckeTrace`).
   In particular, the positive-rank `sl_N` HOMFLY specializations in `RatFunc K` are the
   corresponding normalized Ocneanu traces, which uniquely determine `β.reducedHomfly K`.

## Main results

* `TauCeti.MarkovBraid.heckeTrace_ocneanuTrace_eq_mul_jimboTrace` and
  `TauCeti.MarkovBraid.heckeTrace_ocneanuTrace_eq_jimboReducedTrace`: comparison of the
  finite-colour normalized Ocneanu trace with `jimboTrace` and `jimboReducedTrace`.
* `TauCeti.MarkovBraid.heckeTrace_ocneanuTrace_eq_eval₂_jimboReducedLaurent`,
  `TauCeti.MarkovBraid.heckeTrace_ocneanuTrace_one_eq_pow_componentCount`, and
  `TauCeti.MarkovBraid.heckeTrace_ocneanuTrace_neg_one_eq_pow_componentCount`: regular comparison
  with `jimboReducedLaurent` and closed-form evaluations at `q = ±1`.
* `TauCeti.MarkovBraid.eval₂_reducedHomfly_eq_eval₂_jimboReducedLaurent`: agreement of the `sl_N`
  specialization of `reducedHomfly` with `jimboReducedLaurent` without `[N]_q ≠ 0` (covering
  quantum roots of unity).
* `TauCeti.MarkovBraid.eval₂_reducedHomfly_eq_heckeTrace`,
  `TauCeti.MarkovBraid.eval₂_homfly_eq_mul_heckeTrace`, and
  `TauCeti.MarkovBraid.reducedHomfly_eq_of_heckeTrace_ocneanuTrace`: comparison of `reducedHomfly`
  and `homfly` with normalized Hecke Markov traces and determination by positive-rank Ocneanu
  traces.

## References

* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*,
  Ann. of Math. 126 (1987), 335–388, Section 6.
* V. G. Turaev, *The Yang-Baxter equation and invariants of links*, Invent. Math.
  92 (1988), 527–553.
-/

public section

namespace TauCeti

open InfiniteTypeAHeckeAlgebra KnotTheory LaurentPolynomial
open scoped BigOperators

section FiniteColour

variable {R : Type*} [CommRing R] {q : Rˣ} {N : ℕ} {c : R}

namespace KnotTheory

/-- With `δ = ∑ a : Fin N, jimboWeight q a` and `c * δ = 1`, the parameters `C = δ`,
`l = (q ^ N)⁻¹`, and `z = c * q ^ N` satisfy the positive Markov normalization equation
`C * l * z = 1`. -/
theorem jimboHeckeNormalization_pos (hc : c * ∑ a : Fin N, jimboWeight q a = 1) :
    (∑ a : Fin N, jimboWeight q a) * (↑((q ^ N)⁻¹ : Rˣ) : R) * (c * ↑(q ^ N)) = 1 := by
  have hq : (↑((q ^ N)⁻¹ : Rˣ) : R) * ↑(q ^ N) = 1 := Units.inv_mul (q ^ N)
  linear_combination (c * ∑ a : Fin N, jimboWeight q a) * hq + hc

/-- With `δ = ∑ a : Fin N, jimboWeight q a` and `c * δ = 1`, the parameters `C = δ`,
`l = (q ^ N)⁻¹`, and `z = c * q ^ N` satisfy the negative Markov normalization equation
`C * l⁻¹ * (z - (q - q⁻¹)) = 1`. No invertibility of `q - q⁻¹` is required. -/
theorem jimboHeckeNormalization_neg (hc : c * ∑ a : Fin N, jimboWeight q a = 1) :
    (∑ a : Fin N, jimboWeight q a) * (↑(((q ^ N)⁻¹ : Rˣ)⁻¹) : R) *
      (c * ↑(q ^ N) - ((q : R) - ↑q⁻¹)) = 1 := by
  rw [inv_inv]
  have hdim := jimboWeight_sum (N := N) q
  have hq : (↑(q ^ N) : R) * ↑((q⁻¹) ^ N) = 1 := by
    rw [inv_pow]
    exact Units.mul_inv (q ^ N)
  linear_combination -((↑(q ^ N) : R)) * hdim + ((↑(q ^ N) : R) ^ 2) * hc + hq

end KnotTheory

namespace MarkovBraid

/-- Direct check of the finite-colour Ocneanu normalization on the two-strand unlink `⟨1, 1⟩`:
both sides evaluate to the quantum dimension `∑ a : Fin N, jimboWeight q a`. -/
theorem heckeTrace_ocneanuTrace_two_strand_one
    (hc : c * ∑ a : Fin N, jimboWeight q a = 1) :
    heckeTrace ⟨1, 1⟩ (ocneanuTrace R q (c * ↑(q ^ N)))
        (∑ a : Fin N, jimboWeight q a) ((q ^ N)⁻¹) =
      c * jimboTrace (N := N) ⟨1, 1⟩ q := by
  rw [heckeTrace_one (isMarkovTrace_ocneanuTrace _).map_one, jimboTrace_one, pow_one, pow_two,
    ← mul_assoc, hc, one_mul]

/-- Direct check of the finite-colour Ocneanu normalization on the positive single-crossing
two-strand closure `⟨1, σ₀⟩`: both sides evaluate to `1`. -/
theorem heckeTrace_ocneanuTrace_sigma_two
    (hc : c * ∑ a : Fin N, jimboWeight q a = 1) :
    heckeTrace ⟨1, BraidGroup.sigma (n := 2) 0⟩ (ocneanuTrace R q (c * ↑(q ^ N)))
        (∑ a : Fin N, jimboWeight q a) ((q ^ N)⁻¹) =
      c * jimboTrace (N := N) ⟨1, BraidGroup.sigma (n := 2) 0⟩ q := by
  have hjimbo : jimboTrace (N := N) ⟨1, BraidGroup.sigma (n := 2) 0⟩ q =
      ∑ a : Fin N, jimboWeight q a := by
    simpa using markovEquiv_sigma_last_one_one.jimboTrace_eq (N := N) q
  rw [heckeTrace_sigma_two (isMarkovTrace_ocneanuTrace _) _ _ (jimboHeckeNormalization_pos hc),
    hjimbo, hc]

/-- Direct check of the finite-colour Ocneanu normalization on the negative single-crossing
two-strand closure `⟨1, σ₀⁻¹⟩`: both sides evaluate to `1`. -/
theorem heckeTrace_ocneanuTrace_sigma_two_inv
    (hc : c * ∑ a : Fin N, jimboWeight q a = 1) :
    heckeTrace ⟨1, (BraidGroup.sigma (n := 2) 0)⁻¹⟩ (ocneanuTrace R q (c * ↑(q ^ N)))
        (∑ a : Fin N, jimboWeight q a) ((q ^ N)⁻¹) =
      c * jimboTrace (N := N) ⟨1, (BraidGroup.sigma (n := 2) 0)⁻¹⟩ q := by
  have hjimbo : jimboTrace (N := N) ⟨1, (BraidGroup.sigma (n := 2) 0)⁻¹⟩ q =
      ∑ a : Fin N, jimboWeight q a := by
    simpa using markovEquiv_sigma_last_inv_one_one.jimboTrace_eq (N := N) q
  rw [heckeTrace_sigma_two_inv (isMarkovTrace_ocneanuTrace _) _ _ (jimboHeckeNormalization_neg hc),
    hjimbo, hc]

/-- **Comparison of the normalized Ocneanu braid trace with the writhe-normalized Jimbo trace.**
Over any commutative ring `R`, when `c` inverts `[N]_q = ∑ a : Fin N, jimboWeight q a`, the
normalized Ocneanu trace with `z = c * q ^ N`, `C = [N]_q`, and `l = (q ^ N)⁻¹` equals
`c * β.jimboTrace q`. -/
theorem heckeTrace_ocneanuTrace_eq_mul_jimboTrace (β : MarkovBraid)
    (hc : c * ∑ a : Fin N, jimboWeight q a = 1) :
    β.heckeTrace (ocneanuTrace R q (c * ↑(q ^ N)))
        (∑ a : Fin N, jimboWeight q a) ((q ^ N)⁻¹) =
      c * β.jimboTrace (N := N) q := by
  rw [heckeTrace_def, jimboTrace_def,
    TypeAHeckeAlgebra.ocneanuTrace_braidHom_eq_mul_jimboWeightedTrace hc]
  generalize Multiplicative.toAdd (ArtinGroup.exponentSum _ β.braid) = e
  have hw : (((q ^ N)⁻¹ : Rˣ) ^ e) = (q ^ N) ^ (-e) := by
    rw [← zpow_neg_one, ← zpow_mul, neg_one_mul]
  have hpow : (∑ a : Fin N, jimboWeight q a) ^ β.predStrands * c ^ (β.predStrands + 1) = c := by
    rw [pow_succ, ← mul_assoc, ← mul_pow, mul_comm (∑ a : Fin N, jimboWeight q a) c, hc,
      one_pow, one_mul]
  rw [hw]
  calc
    (∑ a : Fin N, jimboWeight q a) ^ β.predStrands * ↑((q ^ N) ^ (-e)) *
        (c ^ (β.predStrands + 1) * jimboWeightedTrace (N := N) q β.braid) =
      ((∑ a : Fin N, jimboWeight q a) ^ β.predStrands * c ^ (β.predStrands + 1)) *
        (↑((q ^ N) ^ (-e)) * jimboWeightedTrace (N := N) q β.braid) := by ring
    _ = c * (↑((q ^ N) ^ (-e)) * jimboWeightedTrace (N := N) q β.braid) := by rw [hpow]

/-- Multiplying the finite-colour normalized Ocneanu trace by the quantum dimension recovers the
unreduced writhe-normalized Jimbo trace `β.jimboTrace q`. -/
theorem sum_jimboWeight_mul_heckeTrace_ocneanuTrace (β : MarkovBraid)
    (hc : c * ∑ a : Fin N, jimboWeight q a = 1) :
    (∑ a : Fin N, jimboWeight q a) *
        β.heckeTrace (ocneanuTrace R q (c * ↑(q ^ N)))
          (∑ a : Fin N, jimboWeight q a) ((q ^ N)⁻¹) =
      β.jimboTrace (N := N) q := by
  rw [β.heckeTrace_ocneanuTrace_eq_mul_jimboTrace hc, ← mul_assoc, mul_comm _ c, hc, one_mul]

/-- Over a field with nonzero quantum dimension `[N]_q ≠ 0`, the finite-colour normalized Ocneanu
trace equals the reduced Jimbo trace `β.jimboReducedTrace q`. -/
theorem heckeTrace_ocneanuTrace_eq_jimboReducedTrace {K : Type*} [Field K] (β : MarkovBraid)
    (q : Kˣ) (hδ : (∑ a : Fin N, jimboWeight q a) ≠ 0) :
    β.heckeTrace (ocneanuTrace K q ((∑ a : Fin N, jimboWeight q a)⁻¹ * ↑(q ^ N)))
        (∑ a : Fin N, jimboWeight q a) ((q ^ N)⁻¹) =
      β.jimboReducedTrace (N := N) q := by
  rw [β.heckeTrace_ocneanuTrace_eq_mul_jimboTrace (inv_mul_cancel₀ hδ), jimboReducedTrace_def,
    div_eq_inv_mul]

end MarkovBraid

/-- On the quotient `Quot MarkovEquiv`, the descended finite-colour Ocneanu braid invariant agrees
with `MarkovBraid.jimboReducedTrace` whenever `[N]_q ≠ 0`. -/
theorem heckeBraidInvariant_ocneanuTrace_mk_eq_jimboReducedTrace {K : Type*} [Field K]
    (β : MarkovBraid) (q : Kˣ) (hδ : (∑ a : Fin N, jimboWeight q a) ≠ 0) :
    heckeBraidInvariant
        (isMarkovTrace_ocneanuTrace ((∑ a : Fin N, jimboWeight q a)⁻¹ * ↑(q ^ N)))
        (∑ a : Fin N, jimboWeight q a) ((q ^ N)⁻¹)
        (jimboHeckeNormalization_pos (inv_mul_cancel₀ hδ))
        (jimboHeckeNormalization_neg (inv_mul_cancel₀ hδ))
        (Quot.mk MarkovEquiv β) =
      β.jimboReducedTrace (N := N) q := by
  rw [heckeBraidInvariant_mk, β.heckeTrace_ocneanuTrace_eq_jimboReducedTrace q hδ]

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
  rw [β.heckeTrace_ocneanuTrace_eq_mul_jimboTrace hc, ← β.eval₂_jimboReducedLaurent_mul_sum N q]
  calc
    c * (eval₂ (Int.castRingHom R) q (β.jimboReducedLaurent N) * ∑ a : Fin N, jimboWeight q a) =
      eval₂ (Int.castRingHom R) q (β.jimboReducedLaurent N) *
        (c * ∑ a : Fin N, jimboWeight q a) := by ring
    _ = eval₂ (Int.castRingHom R) q (β.jimboReducedLaurent N) := by rw [hc, mul_one]

/-- At the zero-factor specialization `q = 1` (where `q - q⁻¹ = 0`), when `c * N = 1` in `R`, the
normalized Ocneanu trace with parameter `c`, unlink factor `N`, and unit `1` evaluates in closed
form to `N ^ (β.componentCount - 1)`. -/
theorem heckeTrace_ocneanuTrace_one_eq_pow_componentCount {R : Type*} [CommRing R]
    (β : MarkovBraid) (N : ℕ) [NeZero N] {c : R} (hc : c * (N : R) = 1) :
    β.heckeTrace (ocneanuTrace R (1 : Rˣ) c) (N : R) (1 : Rˣ) =
      (N : R) ^ (β.componentCount - 1) := by
  have hc' : c * ∑ a : Fin N, jimboWeight (1 : Rˣ) a = 1 := by simpa using hc
  simpa using β.heckeTrace_ocneanuTrace_eq_eval₂_jimboReducedLaurent N hc'

/-- At the zero-factor specialization `q = -1` (where `q - q⁻¹ = 0`), when
`c * ((-1) ^ (N - 1) * N) = 1` in `R`, the normalized Ocneanu trace evaluates in closed form to
`((-1) ^ (N - 1) * N) ^ (β.componentCount - 1)`. -/
theorem heckeTrace_ocneanuTrace_neg_one_eq_pow_componentCount {R : Type*} [CommRing R]
    (β : MarkovBraid) (N : ℕ) [NeZero N] {c : R}
    (hc : c * ((-1 : R) ^ (N - 1) * (N : R)) = 1) :
    β.heckeTrace (ocneanuTrace R (-1 : Rˣ) (c * (-1 : R) ^ N))
        ((-1 : R) ^ (N - 1) * (N : R)) ((-1 : Rˣ) ^ N) =
      ((-1 : R) ^ (N - 1) * (N : R)) ^ (β.componentCount - 1) := by
  have hsum : (∑ a : Fin N, jimboWeight (-1 : Rˣ) a) = (-1 : R) ^ (N - 1) * (N : R) := by
    simp [mul_comm (N : R)]
  have hc' : c * ∑ a : Fin N, jimboWeight (-1 : Rˣ) a = 1 := by rwa [hsum]
  have hε : (((-1 : Rˣ) ^ N)⁻¹ : Rˣ) = (-1 : Rˣ) ^ N := Units.ext (by simp [← inv_pow])
  have h := β.heckeTrace_ocneanuTrace_eq_eval₂_jimboReducedLaurent N hc'
  simpa only [hsum, hε, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one,
    eval₂_jimboReducedLaurent_neg_one] using h

end MarkovBraid

/-- Whenever `q - q⁻¹` is a unit `u : Rˣ`, evaluating `homflyUnknot K` at `a = q ^ N` and `z = u`
produces the `N`-colour quantum dimension `∑ a : Fin N, jimboWeight q a`, with no nonvanishing
assumption on that sum. -/
theorem KnotTheory.eval₂_homflyUnknot_pow (K : Type*) [Field K] {R : Type*} [CommRing R]
    (φ : K →+* R) (q u : Rˣ) (hu : (u : R) = (q : R) - ↑q⁻¹) (N : ℕ) :
    eval₂ (eval₂ φ u) (q ^ N) (homflyUnknot K) = ∑ a : Fin N, jimboWeight q a := by
  let Φ : LaurentPolynomial (LaurentPolynomial K) →+* R := eval₂ (eval₂ φ u) (q ^ N)
  have hT : Φ (LaurentPolynomial.T 1 - LaurentPolynomial.T (-1)) =
      ↑(q ^ N) - ↑((q⁻¹) ^ N) := by simp [Φ, inv_pow]
  have hC : Φ (LaurentPolynomial.C (LaurentPolynomial.T (-1))) = ↑u⁻¹ := by simp [Φ]
  change Φ (homflyUnknot K) = _
  rw [homflyUnknot_def, map_mul, hT, hC, ← jimboWeight_sum (N := N) q, ← hu,
    mul_right_comm, Units.mul_inv, one_mul]

namespace MarkovBraid

/-- **Regularity of the `sl_N` HOMFLY specialization at quantum roots of unity.** Whenever
`q - q⁻¹` is a unit `u : Rˣ` (in particular at quantum roots of unity where `[N]_q = 0`),
evaluating `β.reducedHomfly K` at `a = q ^ N` and `z = u` agrees with evaluating the universal
Laurent polynomial `β.jimboReducedLaurent N` at `q`, with no nonvanishing assumption on `[N]_q`. -/
theorem eval₂_reducedHomfly_eq_eval₂_jimboReducedLaurent (K : Type*) [Field K]
    {R : Type*} [CommRing R] (β : MarkovBraid) (φ : K →+* R) (q u : Rˣ)
    (hu : (u : R) = (q : R) - ↑q⁻¹) (N : ℕ) [NeZero N] :
    eval₂ (eval₂ φ u) (q ^ N) (β.reducedHomfly K) =
      eval₂ (Int.castRingHom R) q (β.jimboReducedLaurent N) := by
  let Φ : LaurentPolynomial (LaurentPolynomial K) →+* R := eval₂ (eval₂ φ u) (q ^ N)
  let Ψ : LaurentPolynomial ℤ →+* R := eval₂ (Int.castRingHom R) q
  have hmap : Units.map (Ψ : LaurentPolynomial ℤ →* R) (genericUnit ℤ) = q :=
    Units.ext (by simp [Ψ])
  have hsum : Ψ (∑ a : Fin N, jimboWeight (genericUnit ℤ) a) = ∑ a : Fin N, jimboWeight q a := by
    simp [Ψ, RingHom.map_jimboWeight, hmap]
  refine congrFun (eq_of_skein (q ^ N) ((q : R) - ↑q⁻¹) (∑ a : Fin N, jimboWeight q a)
    (F := fun γ ↦ Φ (γ.reducedHomfly K))
    (G := fun γ ↦ Ψ (γ.jimboReducedLaurent N))
    (fun _ _ h ↦ congrArg Φ (h.reducedHomfly_eq K))
    (fun _ _ h ↦ congrArg Ψ (h.jimboReducedLaurent_eq N)) ?_ ?_ ?_ ?_ ?_) β
  · intro m c i
    have hs := congrArg Φ (reducedHomfly_skein K 1 c i)
    have hT₁ : Φ (LaurentPolynomial.T 1) = ↑(q ^ N) := by simp [Φ]
    have hT₂ : Φ (LaurentPolynomial.T (-1)) = ↑((q ^ N)⁻¹) := by simp [Φ]
    have hC₁ : Φ (LaurentPolynomial.C (LaurentPolynomial.T 1)) = (q : R) - ↑q⁻¹ := by simp [Φ, hu]
    simpa only [one_mul, map_sub, map_mul, smul_eq_mul, hT₁, hT₂, hC₁] using hs
  · intro m c i
    have hs := congrArg Ψ (jimboReducedLaurent_skein N 1 c i)
    have hT₁ : Ψ (LaurentPolynomial.T (N : ℤ)) = ↑(q ^ N) := by simp [Ψ]
    have hT₂ : Ψ (LaurentPolynomial.T (-(N : ℤ))) = ↑((q ^ N)⁻¹) := by simp [Ψ, zpow_neg]
    have hT₀ : Ψ (LaurentPolynomial.T 1 - LaurentPolynomial.T (-1)) = (q : R) - ↑q⁻¹ := by simp [Ψ]
    simpa only [one_mul, map_sub, map_mul, smul_eq_mul, hT₁, hT₂, hT₀] using hs
  · intro m b
    rw [reducedHomfly_strandIncl, map_mul, eval₂_homflyUnknot_pow K φ q u hu N, smul_eq_mul]
  · intro m b
    simp [Ψ, smul_eq_mul, hsum]
  · simp [Φ, Ψ]

end MarkovBraid

end ZeroFactorSpecializations

/-! ### Two-variable HOMFLY comparison with normalized Hecke traces -/

section HomflyComparison

namespace KnotTheory

/-- Under the Markov normalization equations `C * l * z = 1` and
`C * l⁻¹ * (z - (q - q⁻¹)) = 1`, when `q - q⁻¹` is a unit `u : Rˣ`, evaluating `homflyUnknot K` at
`a = l⁻¹` and `z = u` produces the split-unknot factor `C`. -/
theorem eval₂_homflyUnknot_eq_of_heckeNormalization (K : Type*) [Field K]
    {R : Type*} [CommRing R] (φ : K →+* R) {q l u : Rˣ} {z C : R}
    (hpos : C * (l : R) * z = 1)
    (hneg : C * (↑l⁻¹ : R) * (z - ((q : R) - ↑q⁻¹)) = 1)
    (hu : (u : R) = (q : R) - ↑q⁻¹) :
    eval₂ (eval₂ φ u) l⁻¹ (homflyUnknot K) = C := by
  have hdiff : (↑l⁻¹ : R) - (l : R) = C * (u : R) := by
    rw [hu, ← heckeNormalization_mul_sub_inv hpos hneg]
  have hT : eval₂ (eval₂ φ u) l⁻¹
      (LaurentPolynomial.T 1 - LaurentPolynomial.T (-1) :
        LaurentPolynomial (LaurentPolynomial K)) =
      (↑l⁻¹ : R) - (l : R) := by simp
  have hC : eval₂ (eval₂ φ u) l⁻¹
      (LaurentPolynomial.C (LaurentPolynomial.T (-1)) :
        LaurentPolynomial (LaurentPolynomial K)) =
      ↑u⁻¹ := by simp
  rw [homflyUnknot_def, map_mul, hT, hC, hdiff, mul_assoc, Units.mul_inv, mul_one]

end KnotTheory

namespace MarkovBraid

/-- **Comparison of `reducedHomfly` with any normalized Hecke Markov trace.** Let `τ` be a
normalized Markov trace with parameter `z` on `InfiniteTypeAHeckeAlgebra R q`, let `(C, l)` satisfy
the positive and negative Markov normalization equations, and suppose `q - q⁻¹` is a unit `u : Rˣ`.
Then evaluating `β.reducedHomfly K` at `a = l⁻¹` and `z = u` equals `β.heckeTrace τ C l`. -/
theorem eval₂_reducedHomfly_eq_heckeTrace (K : Type*) [Field K]
    {R : Type*} [CommRing R] (β : MarkovBraid) (φ : K →+* R)
    {q l u : Rˣ} {z C : R} {τ : InfiniteTypeAHeckeAlgebra R q →ₗ[R] R}
    (hτ : IsMarkovTrace z τ)
    (hpos : C * (l : R) * z = 1)
    (hneg : C * (↑l⁻¹ : R) * (z - ((q : R) - ↑q⁻¹)) = 1)
    (hu : (u : R) = (q : R) - ↑q⁻¹) :
    eval₂ (eval₂ φ u) l⁻¹ (β.reducedHomfly K) = β.heckeTrace τ C l := by
  let Ψ : LaurentPolynomial (LaurentPolynomial K) →+* R := eval₂ (eval₂ φ u) l⁻¹
  have hunknot : Ψ (homflyUnknot K) = C :=
    eval₂_homflyUnknot_eq_of_heckeNormalization K φ hpos hneg hu
  refine congrFun (eq_heckeTrace_of_skein hτ hpos hneg
    (F := fun γ ↦ Ψ (γ.reducedHomfly K))
    (fun _ _ h ↦ congrArg Ψ (h.reducedHomfly_eq K)) ?_ ?_ ?_) β
  · intro m c i
    have hs := congrArg Ψ (reducedHomfly_skein K 1 c i)
    have hT₁ : Ψ (LaurentPolynomial.T 1) = ↑l⁻¹ := by simp [Ψ]
    have hT₂ : Ψ (LaurentPolynomial.T (-1)) = (l : R) := by simp [Ψ]
    have hC₁ : Ψ (LaurentPolynomial.C (LaurentPolynomial.T 1)) = (q : R) - ↑q⁻¹ := by simp [Ψ, hu]
    simpa only [one_mul, map_sub, map_mul, hT₁, hT₂, hC₁] using hs
  · intro m b
    rw [reducedHomfly_strandIncl, map_mul, hunknot]
  · simp [Ψ]

/-- **Comparison of the unreduced `homfly` polynomial with any normalized Hecke Markov trace.**
Under the hypotheses of `eval₂_reducedHomfly_eq_heckeTrace`, evaluating `β.homfly K` at `a = l⁻¹`
and `z = u` equals `C * β.heckeTrace τ C l`. -/
theorem eval₂_homfly_eq_mul_heckeTrace (K : Type*) [Field K]
    {R : Type*} [CommRing R] (β : MarkovBraid) (φ : K →+* R)
    {q l u : Rˣ} {z C : R} {τ : InfiniteTypeAHeckeAlgebra R q →ₗ[R] R}
    (hτ : IsMarkovTrace z τ)
    (hpos : C * (l : R) * z = 1)
    (hneg : C * (↑l⁻¹ : R) * (z - ((q : R) - ↑q⁻¹)) = 1)
    (hu : (u : R) = (q : R) - ↑q⁻¹) :
    eval₂ (eval₂ φ u) l⁻¹ (β.homfly K) = C * β.heckeTrace τ C l := by
  rw [← homflyUnknot_mul_reducedHomfly K β, map_mul,
    eval₂_homflyUnknot_eq_of_heckeNormalization K φ hpos hneg hu,
    eval₂_reducedHomfly_eq_heckeTrace K β φ hτ hpos hneg hu]

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
    ← β.heckeTrace_ocneanuTrace_eq_jimboReducedTrace _ (jimboWeight_sum_X_ne_zero N)]

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
  rw [← β.heckeTrace_ocneanuTrace_eq_jimboReducedTrace _ (jimboWeight_sum_X_ne_zero N)]
  exact h N

end MarkovBraid

end HomflyComparison

end TauCeti
