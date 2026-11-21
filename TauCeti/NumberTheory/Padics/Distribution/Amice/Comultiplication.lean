/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Distribution.Amice.Basis
public import TauCeti.NumberTheory.Padics.Distribution.Comul

/-!
# Comultiplication on Amice's basis vectors

At any analytic stage `h` and degree `n`, the curried stage comultiplication
`TauCeti.AnalyticStage.comulCurried` splits Amice's vector `amiceTerm p h n e` according to
Vandermonde's identity:

`comulCurried S (amiceTerm p h n e) =`
`  ∑_{i + j = n} (⌊n / pʰ⌋! / (⌊i / pʰ⌋! ⌊j / pʰ⌋!)) • amiceTerm p h i (amiceTerm p h j e)`.

For `E = ℤ_p`, this is proved directly from `eval_eval_comulCurried`, `eval_amiceTerm`, and
`Ring.add_choose_eq` via `eval_injective`. Coefficient functoriality along `r ↦ r • e`
(`comulCurried_compLeft` and `compLeft_amiceTerm`) then transfers the identity to arbitrary
complete ultrametric `ℤ_p`-modules `E`, without assuming torsion-freeness or `n < p ^ h`.

## Main results

* `TauCeti.AnalyticStage.comulCurried_amiceTerm`: Vandermonde comultiplication formula for
  `amiceTerm p h n e` at arbitrary stage level `h` and degree `n`.

## References

* Y. Amice, *Interpolation p-adique*, Bull. Soc. Math. France 92 (1964), 117–180.
* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §II.2.
-/

public section

open scoped Nat ZeroAtInfty

namespace TauCeti.AnalyticStage

variable {p : ℕ} [hp : Fact p.Prime] {h : ℕ}
  {E : Type*} [NormedAddCommGroup E] [Module ℤ_[p] E] [IsBoundedSMul ℤ_[p] E]
  [IsUltrametricDist E] [CompleteSpace E]
  (S : Type*) [Semiring S] [Module S E] [ContinuousConstSMul S E] [SMulCommClass ℤ_[p] S E]

private theorem factorial_div_mul_factorial_div_dvd (h : ℕ) {i j n : ℕ} (hij : i + j = n) :
    (i / p ^ h)! * (j / p ^ h)! ∣ (n / p ^ h)! := by
  have hle : i / p ^ h + j / p ^ h ≤ n / p ^ h := by
    rw [Nat.le_div_iff_mul_le (pow_pos hp.out.pos h), add_mul, ← hij]
    exact add_le_add (Nat.div_mul_le_self i (p ^ h)) (Nat.div_mul_le_self j (p ^ h))
  exact (Nat.factorial_mul_factorial_dvd_factorial_add _ _).trans (Nat.factorial_dvd_factorial hle)

private theorem comulCurried_amiceTerm_padicInt (h n : ℕ) :
    comulCurried (p := p) (h := h) ℤ_[p] (amiceTerm p h n (1 : ℤ_[p])) =
      ∑ ij ∈ Finset.antidiagonal n,
        ((n / p ^ h)! / ((ij.1 / p ^ h)! * (ij.2 / p ^ h)!)) •
          amiceTerm p h ij.1 (amiceTerm p h ij.2 (1 : ℤ_[p])) := by
  apply eval_injective ℤ_[p] PadicInt.isSMulRegular_natCast_p.zeroAtInftyContinuousMap
  ext x : 1
  apply eval_injective ℤ_[p] PadicInt.isSMulRegular_natCast_p
  ext y : 1
  simp only [eval_eval_comulCurried, eval_amiceTerm, map_sum, ContinuousMap.coe_sum,
    Finset.sum_apply, PadicInt.mahlerTerm_apply, mahler_apply, Ring.add_choose_eq n
      (Commute.all x y),
    nsmul_eq_mul, smul_eq_mul, mul_one, Finset.sum_mul]
  refine Finset.sum_congr rfl fun ij hij ↦ ?_
  have hdvd := factorial_div_mul_factorial_div_dvd (p := p) h (Finset.mem_antidiagonal.mp hij)
  have hfac : (((n / p ^ h)! / ((ij.1 / p ^ h)! * (ij.2 / p ^ h)!)) : ℤ_[p]) *
      ((ij.1 / p ^ h)! : ℤ_[p]) * ((ij.2 / p ^ h)! : ℤ_[p]) = ((n / p ^ h)! : ℤ_[p]) := by
    rw [mul_assoc, ← Nat.cast_mul, ← Nat.cast_mul, Nat.div_mul_cancel hdvd]
  simp only [map_nsmul, eval_amiceTerm, PadicInt.mahlerTerm_apply, mahler_apply, map_smul,
    ContinuousMap.smul_apply]
  simp only [nsmul_eq_mul, smul_eq_mul, mul_one]
  rw [← hfac]
  ring

/-- **Binomial comultiplication on Amice's vectors.** At any level `h`, curried comultiplication on
Amice's vector `e_{h,n} • e` splits according to Vandermonde's identity into
`∑_{i + j = n} (⌊n / pʰ⌋! / (⌊i / pʰ⌋! ⌊j / pʰ⌋!)) • e_{h,i} • (e_{h,j} • e)`. No
torsion-freeness of `E` or bound `n < p ^ h` is needed. -/
theorem comulCurried_amiceTerm (n : ℕ) (e : E) :
    comulCurried S (amiceTerm p h n e) =
      ∑ ij ∈ Finset.antidiagonal n,
        ((n / p ^ h)! / ((ij.1 / p ^ h)! * (ij.2 / p ^ h)!)) •
          amiceTerm p h ij.1 (amiceTerm p h ij.2 e) := by
  let u := ContinuousLinearMap.toSpanSingleton ℤ_[p] e
  have hu : ∃ C, ∀ r : ℤ_[p], ‖u r‖ ≤ C * ‖r‖ :=
    ContinuousLinearMap.exists_norm_toSpanSingleton_apply_le ℤ_[p] e
  have he : amiceTerm p h n e =
      ZeroAtInftyContinuousMap.compLeft u hu (amiceTerm p h n (1 : ℤ_[p])) := by
    simp [u]
  rw [comulCurried_eq_comulCurried_padicInt S, he, comulCurried_compLeft ℤ_[p] u hu,
    comulCurried_amiceTerm_padicInt, map_sum (ZeroAtInftyContinuousMap.compLeft _ _)]
  refine Finset.sum_congr rfl fun ij _ ↦ ?_
  simp [u]

end TauCeti.AnalyticStage
