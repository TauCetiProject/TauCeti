/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Splits
public import TauCeti.RingTheory.Polynomial.DegreeLT
public import TauCeti.RingTheory.PowerSeries.Swap
import Mathlib.Tactic.LinearCombination
import TauCeti.Algebra.Polynomial.Depressed

/-!
# Hensel lifting of coprime factorizations over power series

Let `R` be a commutative ring and `P` a monic polynomial over `R⟦t⟧`. If the reduction of `P`
modulo `t` factors as `g * h` with `g` and `h` monic and coprime in `R[X]`, then `P = G * H` for
unique monic `G` and `H` over `R⟦t⟧` reducing to `g` and `h`. In particular `G` and `H` have the
degrees of `g` and `h`, by `Polynomial.Monic.natDegree_map`. This is the coprime-factor form of
Hensel's lemma for `R⟦t⟧`; for a field `R` it is the factor-splitting step of the Newton–Puiseux
algorithm.

The proof is the classical coefficient recursion. A polynomial over `R⟦t⟧` is rewritten as a power
series in `t` whose coefficients are polynomials over `R`, through the ring homomorphism
`Polynomial.swapPowerSeries : R⟦X⟧[X] →+* R[X]⟦X⟧` (`TauCeti.RingTheory.PowerSeries.Swap`).
Write `G = Σ Gₖ tᵏ` and `H = Σ Hₖ tᵏ` with `G₀ = g` and `H₀ = h`. The coefficient of `tᵏ` in
`G * H = P` reads

`g * Hₖ + h * Gₖ = Pₖ - Σ_{0 < i < k} Gᵢ * H_{k - i}`,

and, `G` and `H` being monic of the degrees of `g` and `h`, the corrections satisfy
`deg Gₖ < deg g` and `deg Hₖ < deg h` for `k ≥ 1`. Writing `u * g + v * h = 1`, Bézout and
division by `g` give the unique solution of this equation within those degree bounds
(`IsCoprime.exists_mem_degreeLT_mul_add_mul_eq`, `IsCoprime.eq_zero_of_mul_add_mul_eq_zero`).
Solving it for `k = 1, 2, ...` produces the factors one power of `t` at a time; uniqueness of
each step gives uniqueness of the factorization.

## Main results

* `PowerSeries.eq_zero_of_mul_add_mul_eq_zero`: if the constant coefficient of `F₂` is monic and
  coprime to that of `F₁`, then `F₂ * B + F₁ * A = 0` over `R[X]⟦t⟧`, with the coefficients of `A`
  of degree below that of the constant coefficient of `F₂`, forces `A = 0` and `B = 0`.
* `Polynomial.Monic.exists_monic_mul_eq_of_isCoprime`: existence of the lifted factorization.
* `Polynomial.Monic.eq_and_eq_of_mul_eq_mul_of_isCoprime`: uniqueness of the lifted
  factorization.
* `Polynomial.Monic.exists_monic_mul_eq_of_nextCoeff_map_eq_zero`: over a field `K`, a monic
  polynomial over `K⟦t⟧` whose reduction is depressed, splits, has invertible degree and is not a
  power of `X` factors into two monic factors of positive degree. This is the degree-lowering
  splitting step of the Newton–Puiseux algorithm, combining the coprime splitting of the reduction
  (`Polynomial.Monic.exists_isCoprime_mul_eq_of_nextCoeff_eq_zero`) with Hensel lifting.

## References

* D. Eisenbud, *Commutative Algebra with a View Toward Algebraic Geometry*, Theorem 7.18, for
  Hensel's lemma over complete local rings by successive approximation.
* H. Mannaa and T. Coquand, *Dynamic Newton–Puiseux Theorem*, arXiv:1304.6770, §1, where the
  factor-lifting form of Hensel's lemma is the splitting step of the Newton–Puiseux algorithm.
-/

public section

noncomputable section

open scoped Polynomial PowerSeries

namespace Polynomial

section Hensel

variable {R : Type*} [CommRing R]

/-- If `F₂ * B + F₁ * A = 0` for power series over `R[X]`, where the constant coefficient `g` of
`F₂` is monic and coprime to that of `F₁` and every coefficient of `A` has degree `< deg g`, then
`A = 0` and `B = 0`: the coefficient recursion of Hensel lifting has unique solutions. -/
theorem _root_.PowerSeries.eq_zero_of_mul_add_mul_eq_zero {g : R[X]} (hg : g.Monic)
    {A B F₁ F₂ : R[X]⟦X⟧}
    (hcop : IsCoprime g (PowerSeries.constantCoeff F₁)) (hF₂ : PowerSeries.constantCoeff F₂ = g)
    (hA : ∀ k, PowerSeries.coeff k A ∈ degreeLT R g.natDegree) (h : F₂ * B + F₁ * A = 0) :
    A = 0 ∧ B = 0 := by
  -- By induction, `tᵏ` divides both `A` and `B` for every `k`.
  have key : ∀ k, PowerSeries.X ^ k ∣ A ∧ PowerSeries.X ^ k ∣ B := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      obtain ⟨⟨A', hA'⟩, ⟨B', hB'⟩⟩ := ih
      have h' : F₂ * B' + F₁ * A' = 0 :=
        PowerSeries.X_pow_mul_cancel (k := k) (by rw [mul_zero, ← h, hA', hB']; ring)
      have hA'₀ : PowerSeries.constantCoeff A' ∈ degreeLT R g.natDegree := by
        simpa [hA', PowerSeries.coeff_X_pow_mul'] using hA k
      have h₀ := congrArg PowerSeries.constantCoeff h'
      rw [map_add, map_mul, map_mul, hF₂, map_zero] at h₀
      obtain ⟨hA'0, hB'0⟩ := hcop.eq_zero_of_mul_add_mul_eq_zero hg hA'₀ h₀
      rw [hA', hB', pow_succ]
      exact ⟨mul_dvd_mul_left _ (PowerSeries.X_dvd_iff.mpr hA'0),
        mul_dvd_mul_left _ (PowerSeries.X_dvd_iff.mpr hB'0)⟩
  constructor <;> refine PowerSeries.ext fun k ↦ ?_ <;> rw [map_zero]
  · exact PowerSeries.X_pow_dvd_iff.mp (key (k + 1)).1 k k.lt_succ_self
  · exact PowerSeries.X_pow_dvd_iff.mp (key (k + 1)).2 k k.lt_succ_self

/-- The successive approximations to the Hensel lift of `p = g * h (mod t)`: the `k`-th pair
agrees with the lifted factors modulo `t ^ (k + 1)`. The correction at step `k + 1` is
`(a c, b c)`, where `c` is the `tᵏ⁺¹`-coefficient of the current error and `a`, `b` solve
`g * b c + h * a c = c`. -/
private def approx (p : R[X]⟦X⟧) (g h : R[X]) (a b : R[X] → R[X]) :
    ℕ → R[X]⟦X⟧ × R[X]⟦X⟧
  | 0 => (PowerSeries.C g, PowerSeries.C h)
  | k + 1 =>
    let S := approx p g h a b k
    let c := PowerSeries.coeff (k + 1) (p - S.1 * S.2)
    (S.1 + PowerSeries.X ^ (k + 1) * PowerSeries.C (a c),
      S.2 + PowerSeries.X ^ (k + 1) * PowerSeries.C (b c))

/-- The coefficients of the approximations stabilize: those of `tʲ` no longer change after step
`j`. -/
private theorem coeff_approx_of_le (p : R[X]⟦X⟧) (g h : R[X]) (a b : R[X] → R[X]) {j k : ℕ}
    (hjk : j ≤ k) :
    PowerSeries.coeff j (approx p g h a b k).1 = PowerSeries.coeff j (approx p g h a b j).1 ∧
      PowerSeries.coeff j (approx p g h a b k).2 = PowerSeries.coeff j (approx p g h a b j).2 := by
  induction k, hjk using Nat.le_induction with
  | base => exact ⟨rfl, rfl⟩
  | succ k hjk ih =>
    simpa [approx, PowerSeries.coeff_X_pow_mul', show ¬k + 1 ≤ j by omega,
      show j ≠ k + 1 by omega] using ih

/-- The invariants of the successive approximations to the Hensel lift of a monic `P` with
`P = g * h (mod t)`: their constant coefficients are `g` and `h`, their higher coefficients have
degree `< deg g` and `< deg h`, and the error vanishes modulo `t ^ (k + 1)`. -/
private theorem approx_spec [Nontrivial R] {P : R⟦X⟧[X]} (hP : P.Monic) {g h : R[X]} (hg : g.Monic)
    (hh : h.Monic) (hPgh : P.map PowerSeries.constantCoeff = g * h) {a b : R[X] → R[X]}
    (ha : ∀ c ∈ degreeLT R (g.natDegree + h.natDegree), a c ∈ degreeLT R g.natDegree)
    (hb : ∀ c ∈ degreeLT R (g.natDegree + h.natDegree), b c ∈ degreeLT R h.natDegree)
    (hab : ∀ c ∈ degreeLT R (g.natDegree + h.natDegree), g * b c + h * a c = c) (k : ℕ) :
    PowerSeries.constantCoeff (approx (swapPowerSeries P) g h a b k).1 = g ∧
      PowerSeries.constantCoeff (approx (swapPowerSeries P) g h a b k).2 = h ∧
      (∀ j, 1 ≤ j →
        PowerSeries.coeff j (approx (swapPowerSeries P) g h a b k).1 ∈ degreeLT R g.natDegree ∧
          PowerSeries.coeff j (approx (swapPowerSeries P) g h a b k).2 ∈
            degreeLT R h.natDegree) ∧
      PowerSeries.X ^ (k + 1) ∣ swapPowerSeries P -
        (approx (swapPowerSeries P) g h a b k).1 * (approx (swapPowerSeries P) g h a b k).2 := by
  have hPdeg : P.natDegree = g.natDegree + h.natDegree := by
    rw [← hP.natDegree_map PowerSeries.constantCoeff, hPgh, hg.natDegree_mul hh]
  set S := approx (swapPowerSeries P) g h a b
  induction k with
  | zero =>
    refine ⟨by simp [S, approx], by simp [S, approx], fun j hj ↦ ?_, ?_⟩
    · simp [S, approx, PowerSeries.coeff_C, show j ≠ 0 by omega]
    · rw [zero_add, pow_one, PowerSeries.X_dvd_iff, map_sub, map_mul,
        constantCoeff_swapPowerSeries, hPgh]
      simp [S, approx]
  | succ k ih =>
    obtain ⟨h₁, h₂, hdeg, E, hE⟩ := ih
    set c := PowerSeries.coeff (k + 1) (swapPowerSeries P - (S k).1 * (S k).2) with hc_def
    -- The error coefficient `c` has degree `< deg g + deg h`, because the current
    -- approximations are monic polynomials of the degrees of `g` and `h`.
    have hc : c ∈ degreeLT R (g.natDegree + h.natDegree) := by
      obtain ⟨G, hG, hGdeg, -, hGS⟩ :=
        exists_monic_swapPowerSeries_eq hg h₁ fun j hj ↦ (hdeg j hj).1
      obtain ⟨H, hH, hHdeg, -, hHS⟩ :=
        exists_monic_swapPowerSeries_eq hh h₂ fun j hj ↦ (hdeg j hj).2
      rw [hc_def, ← hGS, ← hHS, ← map_mul, ← map_sub, ← hPdeg]
      refine coeff_swapPowerSeries_mem_degreeLT (hP.sub_mem_degreeLT (hG.mul hH) ?_) _
      rw [hG.natDegree_mul hH, hGdeg, hHdeg, hPdeg]
    have hS : S (k + 1) = ((S k).1 + PowerSeries.X ^ (k + 1) * PowerSeries.C (a c),
        (S k).2 + PowerSeries.X ^ (k + 1) * PowerSeries.C (b c)) := rfl
    have hcE : PowerSeries.constantCoeff E = c := by
      simp [hc_def, hE, PowerSeries.coeff_X_pow_mul']
    refine ⟨by simp [hS, h₁], by simp [hS, h₂], fun j hj ↦ ?_, ?_⟩
    · simp only [hS, map_add, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_C]
      split_ifs
      · exact ⟨add_mem (hdeg j hj).1 (ha c hc), add_mem (hdeg j hj).2 (hb c hc)⟩
      · simpa using hdeg j hj
      · simpa using hdeg j hj
    · -- The new error is `t ^ (k + 1)` times a series with constant coefficient
      -- `c - (g * b c + h * a c) = 0`.
      have hX : PowerSeries.X ∣ E - (S k).1 * PowerSeries.C (b c) -
          PowerSeries.C (a c) * (S k).2 -
          PowerSeries.X ^ (k + 1) * PowerSeries.C (a c * b c) := by
        rw [PowerSeries.X_dvd_iff]
        simp only [map_sub, map_mul, map_pow, PowerSeries.constantCoeff_X,
          PowerSeries.constantCoeff_C, h₁, h₂, hcE, zero_pow (Nat.succ_ne_zero k), zero_mul,
          sub_zero]
        linear_combination -(hab c hc)
      obtain ⟨E', hE'⟩ := hX
      refine ⟨E', ?_⟩
      rw [hS]
      rw [map_mul] at hE'
      linear_combination hE + PowerSeries.X ^ (k + 1) * hE'

/-- If the error of the `k`-th approximation vanishes modulo `t ^ (k + 1)` for every `k`, then the
limits of the approximations, whose `tʲ`-coefficient is that of the `j`-th approximation, multiply
to `p`. -/
private theorem mk_coeff_approx_mul_mk_coeff_approx (p : R[X]⟦X⟧) (g h : R[X])
    (a b : R[X] → R[X])
    (hp : ∀ k, PowerSeries.X ^ (k + 1) ∣ p - (approx p g h a b k).1 * (approx p g h a b k).2) :
    (PowerSeries.mk fun j ↦ PowerSeries.coeff j (approx p g h a b j).1) *
      (PowerSeries.mk fun j ↦ PowerSeries.coeff j (approx p g h a b j).2) = p := by
  refine PowerSeries.ext fun n ↦ ?_
  have hn := PowerSeries.X_pow_dvd_iff.mp (hp n) n n.lt_succ_self
  rw [map_sub, sub_eq_zero] at hn
  rw [hn, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  have hx' := Finset.mem_antidiagonal.mp hx
  simp only [PowerSeries.coeff_mk, (coeff_approx_of_le p g h a b (show x.1 ≤ n by omega)).1,
    (coeff_approx_of_le p g h a b (show x.2 ≤ n by omega)).2]

/-- A monic polynomial `P` over `R⟦t⟧` whose reduction modulo `t` is a product `g * h` of
coprime polynomials with `g` monic factors as `P = G * H` with `G` and `H` monic and reducing to
`g` and `h`. This is the coprime-factor form of Hensel's lemma over `R⟦t⟧`; `h` is automatically
monic, and the factors are unique by `Polynomial.Monic.eq_and_eq_of_mul_eq_mul_of_isCoprime`. -/
theorem Monic.exists_monic_mul_eq_of_isCoprime {P : R⟦X⟧[X]} (hP : P.Monic) {g h : R[X]}
    (hg : g.Monic) (hgh : IsCoprime g h) (hPgh : P.map PowerSeries.constantCoeff = g * h) :
    ∃ G H : R⟦X⟧[X], G.Monic ∧ H.Monic ∧ G.map PowerSeries.constantCoeff = g ∧
      H.map PowerSeries.constantCoeff = h ∧ G * H = P := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact ⟨P, 1, hP, monic_one, Subsingleton.elim _ _, Subsingleton.elim _ _, mul_one P⟩
  have hh : h.Monic := hg.of_mul_monic_left (hPgh ▸ hP.map _)
  choose! a b ha hb hab using fun c (hc : c ∈ degreeLT R (g.natDegree + h.natDegree)) ↦
    hgh.exists_mem_degreeLT_mul_add_mul_eq hg hc
  have inv := approx_spec hP hg hh hPgh ha hb hab
  set S := approx (swapPowerSeries P) g h a b
  obtain ⟨G, hG, -, hGg, hGS⟩ := exists_monic_swapPowerSeries_eq hg
    (F := PowerSeries.mk fun j ↦ PowerSeries.coeff j (S j).1)
    (by simp [← PowerSeries.coeff_zero_eq_constantCoeff_apply, S, approx])
    fun j hj ↦ by simpa using ((inv j).2.2.1 j hj).1
  obtain ⟨H, hH, -, hHh, hHS⟩ := exists_monic_swapPowerSeries_eq hh
    (F := PowerSeries.mk fun j ↦ PowerSeries.coeff j (S j).2)
    (by simp [← PowerSeries.coeff_zero_eq_constantCoeff_apply, S, approx])
    fun j hj ↦ by simpa using ((inv j).2.2.1 j hj).2
  refine ⟨G, H, hG, hH, hGg, hHh, swapPowerSeries_injective ?_⟩
  rw [map_mul, hGS, hHS, mk_coeff_approx_mul_mk_coeff_approx _ _ _ _ _ fun n ↦ (inv n).2.2.2]

/-- Uniqueness of Hensel lifting over `R⟦t⟧`: if `G * H = G' * H'` with `G` and `G'` monic and
reducing modulo `t` to the same polynomial, coprime to the reduction of `H`, then `G = G'` and
`H = H'`. No monicity of `H` or `H'` is needed. -/
theorem Monic.eq_and_eq_of_mul_eq_mul_of_isCoprime {G G' H H' : R⟦X⟧[X]} (hG : G.Monic)
    (hG' : G'.Monic) (hGG' : G.map PowerSeries.constantCoeff = G'.map PowerSeries.constantCoeff)
    (hcop : IsCoprime (G.map PowerSeries.constantCoeff) (H.map PowerSeries.constantCoeff))
    (h : G * H = G' * H') : G = G' ∧ H = H' := by
  nontriviality R
  have hdeg : G.natDegree = G'.natDegree := by
    rw [← hG.natDegree_map PowerSeries.constantCoeff, hGG', hG'.natDegree_map]
  have hA (k : ℕ) : PowerSeries.coeff k (swapPowerSeries (G - G')) ∈
      degreeLT R (G.map PowerSeries.constantCoeff).natDegree := by
    rw [hG.natDegree_map]
    exact coeff_swapPowerSeries_mem_degreeLT (hG.sub_mem_degreeLT hG' hdeg) k
  have hrel : swapPowerSeries G' * swapPowerSeries (H - H') +
      swapPowerSeries H * swapPowerSeries (G - G') = 0 := by
    rw [← map_mul, ← map_mul, ← map_add, ← map_zero swapPowerSeries]
    congr 1
    linear_combination h
  obtain ⟨hA0, hB0⟩ := PowerSeries.eq_zero_of_mul_add_mul_eq_zero (hG.map _)
    (by rwa [constantCoeff_swapPowerSeries]) (by rw [constantCoeff_swapPowerSeries, hGG']) hA hrel
  rw [← map_zero swapPowerSeries] at hA0 hB0
  exact ⟨sub_eq_zero.mp (swapPowerSeries_injective hA0),
    sub_eq_zero.mp (swapPowerSeries_injective hB0)⟩

end Hensel

section Splitting

variable {K : Type*} [Field K]

/-- A monic polynomial `P` over `K⟦t⟧` whose reduction modulo `t` has vanishing subleading
coefficient, splits, has invertible degree and is not `X ^ P.natDegree` factors as `P = G * H` with
`G` and `H` monic of positive degree. This is the splitting step of the Newton–Puiseux algorithm:
the reduction splits into coprime monic factors of positive degree
(`Polynomial.Monic.exists_isCoprime_mul_eq_of_nextCoeff_eq_zero`), and Hensel's lemma lifts them.
In particular both factors have degree less than that of `P`, by `Polynomial.Monic.natDegree_mul`.
-/
theorem Monic.exists_monic_mul_eq_of_nextCoeff_map_eq_zero {P : K⟦X⟧[X]} (hP : P.Monic)
    (hs : (P.map PowerSeries.constantCoeff).Splits) (hm : (P.natDegree : K) ≠ 0)
    (hnext : (P.map PowerSeries.constantCoeff).nextCoeff = 0)
    (hX : P.map PowerSeries.constantCoeff ≠ X ^ P.natDegree) :
    ∃ G H : K⟦X⟧[X], G.Monic ∧ H.Monic ∧ G * H = P ∧ 0 < G.natDegree ∧ 0 < H.natDegree := by
  have hdeg := hP.natDegree_map PowerSeries.constantCoeff
  obtain ⟨g, h, hg, -, hgh, hprod, hg0, hh0⟩ :=
    (hP.map PowerSeries.constantCoeff).exists_isCoprime_mul_eq_of_nextCoeff_eq_zero hs
      (by rwa [hdeg]) hnext (by rwa [hdeg])
  obtain ⟨G, H, hG, hH, hGg, hHh, hGH⟩ := hP.exists_monic_mul_eq_of_isCoprime hg hgh hprod.symm
  exact ⟨G, H, hG, hH, hGH, by rwa [← hG.natDegree_map PowerSeries.constantCoeff, hGg],
    by rwa [← hH.natDegree_map PowerSeries.constantCoeff, hHh]⟩

end Splitting

end Polynomial
