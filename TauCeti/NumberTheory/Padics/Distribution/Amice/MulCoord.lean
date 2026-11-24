/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Distribution.Amice.Transform
public import TauCeti.NumberTheory.Padics.Distribution.MulCoord
public import TauCeti.NumberTheory.Padics.Measure.Moments
import Mathlib.Algebra.CharZero.Infinite

/-!
# The Amice transform of multiplication by the coordinate

Multiplication by the coordinate on locally analytic functions,
`TauCeti.LocallyAnalytic.mulCoord`, acts on the locally analytic Mahler terms by the Mahler
recurrence

`x (x choose n) = (n + 1) (x choose (n + 1)) + n (x choose n)`

(`LocallyAnalytic.mulCoord_mahlerTerm`), proved on the stage of level `n + 1`, where Amice's vectors
of degree `n` and `n + 1` are the Mahler terms themselves.

By the Mahler recurrence, the transpose `TauCeti.LocallyAnalyticDistribution.mulCoord`,
`(x μ)(f) = μ(x f)`, acts on the Amice transform as the Mahler derivation `∂ = (1 + T) d/dT`
(`amiceTransform_mulCoord`). On the distribution of a measure, the corresponding identity is
`AbstractMeasure.amiceTransform_weight_id_smul_one`.

## Main results

* `TauCeti.LocallyAnalytic.mulCoord_mahlerTerm`: the Mahler recurrence for locally analytic
  Mahler terms.
* `TauCeti.LocallyAnalyticDistribution.amiceTransform_mulCoord`: `A_{xμ} = ∂ A_μ`.

## References

* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §II.4.
* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*, §3.5.1,
  Lemma 3.29.
-/

public section

open scoped Polynomial

namespace TauCeti

variable {p : ℕ} [hp : Fact p.Prime]

namespace AnalyticStage

variable {h : ℕ} {E : Type*} [NormedAddCommGroup E] [Module ℤ_[p] E] [IsBoundedSMul ℤ_[p] E]
  [IsUltrametricDist E]
  (S : Type*) [Semiring S] [Module S E] [ContinuousConstSMul S E] [SMulCommClass ℤ_[p] S E]

/-- The Mahler recurrence for Amice's polynomials of degrees `n` and `n + 1 < pʰ` on the disc of
`a`: these are `(a + pʰ w choose n)` and its successor, so multiplying by the coordinate
`a + pʰ w` gives `(n + 1) (a + pʰ w choose (n + 1)) + n (a + pʰ w choose n)`. -/
private theorem coord_mul_amicePolynomial {n : ℕ} (hn : n + 1 < p ^ h) (a : ℤ_[p]) :
    (Polynomial.C a + Polynomial.C ((p : ℤ_[p]) ^ h) * Polynomial.X) *
        amicePolynomial p h n a =
      ((n + 1 : ℕ) : ℤ_[p][X]) * amicePolynomial p h (n + 1) a +
        (n : ℤ_[p][X]) * amicePolynomial p h n a := by
  refine Polynomial.funext fun w ↦ ?_
  have hrec := DFunLike.congr_fun (id_mul_mahler (p := p) n) (a + (p : ℤ_[p]) ^ h * w)
  simp only [ContinuousMap.mul_apply, ContinuousMap.id_apply, ContinuousMap.add_apply,
    mahler_apply, nsmul_eq_mul] at hrec
  simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_natCast, eval_amicePolynomial, Nat.div_eq_of_lt hn,
    Nat.div_eq_of_lt (Nat.lt_succ_self n |>.trans hn), Nat.factorial_zero, Nat.cast_one,
    one_mul]
  push_cast at hrec ⊢
  exact hrec

/-- On the stage of a level `h` with `n + 1 < pʰ`, multiplication by the coordinate sends Amice's
vector `e_{h,n} • e = (x choose n) • e` to
`(x choose (n + 1)) • (n + 1) e + (x choose n) • n e`: for such `h` the factors `⌊n / pʰ⌋!` and
`⌊(n + 1) / pʰ⌋!` of Amice's vectors are `1`. -/
private theorem mulCoord_amiceTerm {n : ℕ} (hn : n + 1 < p ^ h) (e : E) :
    mulCoord S (amiceTerm p h n e) =
      amiceTerm p h (n + 1) ((n + 1) • e) + amiceTerm p h n (n • e) := by
  -- Compare the coefficients of both sides of `coord_mul_amicePolynomial`.
  ext ⟨a, k⟩
  have hk := congrArg (fun P : ℤ_[p][X] ↦ P.coeff k) (coord_mul_amicePolynomial hn (a.val : ℤ_[p]))
  rcases k with _ | k <;>
  · simp only [add_mul, mul_assoc, Polynomial.coeff_add, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_mul_zero, Polynomial.coeff_X_mul, Polynomial.coeff_natCast_mul, mul_zero,
      add_zero] at hk
    simp only [mulCoord_apply_zero, mulCoord_apply_succ, FunLike.coe_add, Pi.add_apply,
      amiceTerm_apply, ← Nat.cast_smul_eq_nsmul ℤ_[p], smul_smul, ← add_smul]
    congr 1
    push_cast at hk ⊢
    linear_combination hk

end AnalyticStage

namespace LocallyAnalytic

open AnalyticStage

variable {E : Type*} [NormedAddCommGroup E] [Module ℤ_[p] E] [IsBoundedSMul ℤ_[p] E]
  [IsUltrametricDist E] [CompleteSpace E]
  (S : Type*) [Semiring S] [Module S E] [ContinuousConstSMul S E] [SMulCommClass ℤ_[p] S E]

/-- **The Mahler recurrence.** Multiplication by the coordinate sends the Mahler term
`x ↦ (x choose n) • e` to `(x choose (n + 1)) • (n + 1) e + (x choose n) • n e`. -/
theorem mulCoord_mahlerTerm (e : E) (n : ℕ) :
    mulCoord S (mahlerTerm p S e n) =
      mahlerTerm p S ((n + 1) • e) (n + 1) + mahlerTerm p S (n • e) n := by
  have hn : n + 1 < p ^ (n + 1) := Nat.lt_pow_self hp.out.one_lt
  have hterm (m : ℕ) (hm : m < p ^ (n + 1)) (e' : E) :
      ofStage S (n + 1) (amiceTerm p (n + 1) m e') = mahlerTerm p S e' m := by
    rw [ofStage_amiceTerm, Nat.div_eq_of_lt hm, Nat.factorial_zero, one_smul]
  rw [← hterm n ((Nat.lt_succ_self n).trans hn), mulCoord_ofStage, mulCoord_amiceTerm S hn,
    map_add, hterm _ hn, hterm _ ((Nat.lt_succ_self n).trans hn)]

end LocallyAnalytic

namespace LocallyAnalyticDistribution

open AnalyticStage LocallyAnalytic

variable {K : Type*} [NontriviallyNormedField K] [Algebra ℤ_[p] K]
  [IsBoundedSMul ℤ_[p] K] [IsUltrametricDist K] [CompleteSpace K]

/-- **The Amice transform of `x μ`** is the Mahler derivation `∂ = (1 + T) d/dT` of the Amice
transform of `μ`. -/
@[simp]
theorem amiceTransform_mulCoord (μ : LocallyAnalyticDistribution p K) :
    amiceTransform (mulCoord μ) = PowerSeries.mahlerDerivation K (amiceTransform μ) := by
  ext n
  simp only [coeff_amiceTransform, PowerSeries.coeff_mahlerDerivation, coe_mulCoord_apply,
    mulCoord_mahlerTerm, map_add, ← Nat.cast_smul_eq_nsmul K, mahlerTerm_smul, map_smul]
  push_cast [smul_eq_mul]
  ring

/-- Iterating, multiplication by `x ^ k` acts on the Amice transform as `∂ ^ k`. -/
theorem amiceTransform_iterate_mulCoord (μ : LocallyAnalyticDistribution p K) (k : ℕ) :
    amiceTransform (mulCoord^[k] μ) =
      (PowerSeries.mahlerDerivation K)^[k] (amiceTransform μ) :=
  Function.Semiconj.iterate_right (f := amiceTransform) amiceTransform_mulCoord k μ

end LocallyAnalyticDistribution

end TauCeti
