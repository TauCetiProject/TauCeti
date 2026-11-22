/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Distribution.Amice.Basis
public import TauCeti.NumberTheory.Padics.Distribution.Comul
import TauCeti.Data.Nat.Factorial.Basic

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
For `n < p ^ h`, where the factorial weight `⌊n / pʰ⌋!` equals `1`, uncurrying yields the
Vandermonde expansion of `comul S (amiceTerm p h n 1)` into outer products `prodMul`
(`TauCeti.AnalyticStage.comul_amiceTerm_of_lt`).

## Main results

* `TauCeti.AnalyticStage.comulCurried_amiceTerm`: Vandermonde comultiplication formula for
  `amiceTerm p h n e` at arbitrary stage level `h` and degree `n`.
* `TauCeti.AnalyticStage.comulCurried_amiceTerm_of_lt`: unweighted Vandermonde expansion of
  `comulCurried` on `amiceTerm p h n e` for `n < p ^ h`.
* `TauCeti.AnalyticStage.comul_amiceTerm_of_lt`: Vandermonde expansion of `comul` on unweighted
  Amice basis vectors `amiceTerm p h n 1` for `n < p ^ h`.

## References

* Y. Amice, *Interpolation p-adique*, Bull. Soc. Math. France 92 (1964), 117–180.
* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §II.2.
-/

public section

open ZeroAtInftyContinuousMap
open scoped Nat ZeroAtInfty

namespace TauCeti.AnalyticStage

section Curried

variable {p : ℕ} [hp : Fact p.Prime] {h : ℕ}
  {E : Type*} [NormedAddCommGroup E] [Module ℤ_[p] E] [IsBoundedSMul ℤ_[p] E]
  [IsUltrametricDist E] [CompleteSpace E]
  (S : Type*) [Semiring S] [Module S E] [ContinuousConstSMul S E] [SMulCommClass ℤ_[p] S E]

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
  have hdvd := Finset.mem_antidiagonal.mp hij ▸
    Nat.factorial_div_mul_factorial_div_dvd (p ^ h) ij.1 ij.2
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
      compLeft u hu (amiceTerm p h n (1 : ℤ_[p])) := by
    simp [u]
  rw [comulCurried_eq_comulCurried_padicInt S, he, comulCurried_compLeft ℤ_[p] u hu,
    comulCurried_amiceTerm_padicInt, map_sum (compLeft _ _)]
  refine Finset.sum_congr rfl fun ij _ ↦ ?_
  simp [u]

/-- **Unweighted binomial comultiplication on Amice's vectors.** When `n < p ^ h`, every
factorial weight in `comulCurried_amiceTerm` equals `1`, so curried comultiplication on
`amiceTerm p h n e` reduces to the unweighted Vandermonde sum. -/
theorem comulCurried_amiceTerm_of_lt {n : ℕ} (hn : n < p ^ h) (e : E) :
    comulCurried S (amiceTerm p h n e) =
      ∑ ij ∈ Finset.antidiagonal n, amiceTerm p h ij.1 (amiceTerm p h ij.2 e) := by
  rw [comulCurried_amiceTerm]
  refine Finset.sum_congr rfl fun ij hij ↦ ?_
  have hi : ij.1 / p ^ h = 0 :=
    Nat.div_eq_of_lt ((Finset.HasAntidiagonal.antidiagonal.fst_le hij).trans_lt hn)
  have hj : ij.2 / p ^ h = 0 :=
    Nat.div_eq_of_lt ((Finset.HasAntidiagonal.antidiagonal.snd_le hij).trans_lt hn)
  simp [Nat.div_eq_of_lt hn, hi, hj]

end Curried

/-- **Vandermonde formula for `comul` on unweighted Amice basis vectors.** When `n < p ^ h`, so
that `⌊n / pʰ⌋! = 1` and `amiceTerm p h n 1` represents `x choose n`, stage comultiplication
expands `amiceTerm p h n 1` into `∑_{i + j = n} prodMul (amiceTerm p h i 1) (amiceTerm p h j 1)`. -/
theorem comul_amiceTerm_of_lt {p : ℕ} [Fact p.Prime] {h n : ℕ}
    {R : Type*} [NormedRing R] [Algebra ℤ_[p] R] [IsBoundedSMul ℤ_[p] R] [IsUltrametricDist R]
    [CompleteSpace R] (S : Type*) [Semiring S] [Module S R] [ContinuousConstSMul S R]
    [SMulCommClass ℤ_[p] S R] (hn : n < p ^ h) :
    comul S (amiceTerm p h n (1 : R)) =
      ∑ ij ∈ Finset.antidiagonal n,
        prodMul (amiceTerm p h ij.1 (1 : R)) (amiceTerm p h ij.2 (1 : R)) := by
  rw [comul_eq_comul_padicInt S, ← comul_eq_comul_padicInt R]
  apply (curryEquiv R R).injective
  rw [curryEquiv_comul, comulCurried_amiceTerm_of_lt R hn, map_sum]
  refine Finset.sum_congr rfl fun ij _ ↦ ?_
  rw [curryEquiv_prodMul_eq_compLeft, compLeft_amiceTerm, ContinuousLinearMap.toSpanSingleton_apply,
    one_smul]

end TauCeti.AnalyticStage
