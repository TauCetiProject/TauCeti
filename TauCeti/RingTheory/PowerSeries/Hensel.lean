/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.PowerSeries.Inverse
public import TauCeti.RingTheory.Henselian.Basic
public import TauCeti.RingTheory.Polynomial.DegreeLT
public import TauCeti.RingTheory.PowerSeries.Swap
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.Tactic.LinearCombination
import TauCeti.Algebra.Polynomial.Depressed
import TauCeti.Algebra.Polynomial.Derivative
import TauCeti.Algebra.Polynomial.RingDivision
import TauCeti.RingTheory.PowerSeries.Basic
import TauCeti.RingTheory.PowerSeries.Ideal

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
division by `g` give the unique solution of this equation within those degree bounds:
`Gₖ = (v * c) %ₘ g` and `Hₖ = u * c + h * ((v * c) /ₘ g)`, where `c` is the right-hand side
(`Polynomial.Monic.mul_add_mul_eq_iff`). Solving it for `k = 1, 2, ...` produces the factors one
power of `t` at a time, and the limit of these approximations is the factorization. Conversely
every such factorization satisfies the recursion, so its coefficients up to `tⁿ` depend only on
those of `P`, and the factorization is unique.

For a linear factor `g = X - a` this specializes to the simple-root form of Hensel's lemma. If
`a` is a root of the reduction `p` at which `p'` is a unit, then `X - a` is coprime to
`p /ₘ (X - a)`, so the factor lift splits off `X - α` with `α ≡ a (mod t)`. A simple root of the
reduction lifts to exactly one root of `P` even when `P` is not monic: the pair `(R⟦t⟧, (t))` is
Henselian by `IsAdicComplete.henselianRing`, so Hensel's lemma with uniqueness
(`Polynomial.existsUnique_isRoot_sub_mem`) applies directly. Its coefficients obey Newton's
recursion `αₖ * p'(a) = -[tᵏ] P(α mod tᵏ)`, which holds for every root of `P`.

## Main results

* `Polynomial.Monic.exists_monic_mul_eq_of_isCoprime`: existence of the lifted factorization.
* `Polynomial.Monic.coeff_swapPowerSeries_eq_and_eq_of_mul_eq`: the coefficient recursion,
  computing the `tᵏ`-coefficients of the factors by Bézout and division from those of lower order.
* `Polynomial.Monic.coeff_swapPowerSeries_eq_and_eq_of_coeff_mul_eq`: the factors modulo `tⁿ⁺¹`
  depend only on the product modulo `tⁿ⁺¹`.
* `Polynomial.Monic.eq_and_eq_of_mul_eq_mul_of_isCoprime`: uniqueness of the lifted
  factorization.
* `Polynomial.Monic.exists_X_sub_C_mul_eq_of_isUnit_eval_derivative`: the degree-one case, which
  splits off `X - α` with `α` lifting a simple root `a` of the reduction.
* `Polynomial.existsUnique_isRoot_constantCoeff_eq`: a simple root of the reduction lifts to
  exactly one root of `P`, for any polynomial `P` over `R⟦t⟧`, monic or not.
* `Polynomial.IsRoot.coeff_mul_eval_derivative_eq_neg_coeff_eval_trunc`: Newton's recursion for
  the coefficients of a root.
* `Polynomial.Monic.exists_monic_mul_eq_of_nextCoeff_map_eq_zero`: over a field `K`, a monic
  polynomial over `K⟦t⟧` whose reduction is depressed, splits, has invertible degree and is not a
  power of `X` factors into two monic factors of positive degree. This is the degree-lowering
  splitting step of the Newton–Puiseux algorithm, combining the coprime splitting of the reduction
  (`Polynomial.Monic.exists_isCoprime_mul_eq_of_nextCoeff_eq_zero`) with Hensel lifting.
* `PowerSeries.henselianLocalRing`: over a field `K`, `K⟦t⟧` is a Henselian local ring, being
  complete for its maximal ideal `(t)`.
* `PowerSeries.exists_pow_eq_of_constantCoeff_eq_pow` and `PowerSeries.exists_pow_eq_of_isUnit`:
  a unit of `K⟦t⟧` whose constant coefficient is a nonzero `n`-th power, with `n` invertible in
  `K`, is an `n`-th power; over an algebraically closed field every unit of `K⟦t⟧` has an `n`-th
  root for every `n` invertible in `K`.

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

/-- **The coefficient recursion of Hensel lifting.** Let `G * H = P` over `R⟦t⟧` with `G` monic,
and let `u * g + v * h = 1` be a Bézout relation between the reductions `g` and `h` of `G` and `H`
modulo `t`. For `k ≠ 0` write `Gᵢ`, `Hᵢ` and `Pᵢ` for the `tⁱ`-coefficients and put
`c = Pₖ - Σ_{0 < i < k} Gᵢ * H_{k - i}`. Then `Gₖ` is the remainder of `v * c` on division by
`g`, and `Hₖ = u * c + h * ((v * c) /ₘ g)`. So the factors are determined one power of `t` at a
time by `P`, the reductions and the Bézout coefficients. -/
theorem Monic.coeff_swapPowerSeries_eq_and_eq_of_mul_eq {G H P : R⟦X⟧[X]} (hG : G.Monic)
    (hGH : G * H = P) {u v : R[X]}
    (huv : u * G.map PowerSeries.constantCoeff + v * H.map PowerSeries.constantCoeff = 1) {k : ℕ}
    (hk : k ≠ 0) :
    let c := PowerSeries.coeff k (swapPowerSeries P) - ∑ i ∈ Finset.Ioo 0 k,
      PowerSeries.coeff i (swapPowerSeries G) * PowerSeries.coeff (k - i) (swapPowerSeries H)
    PowerSeries.coeff k (swapPowerSeries G) = (v * c) %ₘ G.map PowerSeries.constantCoeff ∧
      PowerSeries.coeff k (swapPowerSeries H) =
        u * c + H.map PowerSeries.constantCoeff * ((v * c) /ₘ G.map PowerSeries.constantCoeff) := by
  intro c
  nontriviality R
  have ha := hG.natDegree_map (PowerSeries.constantCoeff (R := R)) ▸
    hG.coeff_swapPowerSeries_mem_degreeLT_of_ne_zero hk
  refine ((hG.map _).mul_add_mul_eq_iff huv ha).mp ?_
  -- Split the `tᵏ`-coefficient of `G * H` into its two end terms and the terms `0 < i < k`.
  have hsplit : PowerSeries.coeff k (swapPowerSeries P) =
      G.map PowerSeries.constantCoeff * PowerSeries.coeff k (swapPowerSeries H) +
        H.map PowerSeries.constantCoeff * PowerSeries.coeff k (swapPowerSeries G) +
        ∑ i ∈ Finset.Ioo 0 k, PowerSeries.coeff i (swapPowerSeries G) *
          PowerSeries.coeff (k - i) (swapPowerSeries H) := by
    rw [← hGH, map_mul, PowerSeries.coeff_mul_of_ne_zero _ _ hk, constantCoeff_swapPowerSeries,
      constantCoeff_swapPowerSeries, mul_comm (PowerSeries.coeff k _)]
  simp only [c, hsplit, add_sub_cancel_right]

/-- **The lifted factors modulo `tⁿ⁺¹` depend only on the product modulo `tⁿ⁺¹`.** Let `G` and
`G'` be monic over `R⟦t⟧` with the same reduction modulo `t`, coprime to the reduction of `H`.
If `G * H` and `G' * H'` have the same `tⁱ`-coefficients for `i ≤ n`, then so have `G` and `G'`,
and `H` and `H'`. Letting `n` grow recovers
`Polynomial.Monic.eq_and_eq_of_mul_eq_mul_of_isCoprime`. -/
theorem Monic.coeff_swapPowerSeries_eq_and_eq_of_coeff_mul_eq {G G' H H' : R⟦X⟧[X]}
    (hG : G.Monic) (hG' : G'.Monic)
    (hGG' : G.map PowerSeries.constantCoeff = G'.map PowerSeries.constantCoeff)
    (hcop : IsCoprime (G.map PowerSeries.constantCoeff) (H.map PowerSeries.constantCoeff))
    {n : ℕ} (h : ∀ i ≤ n, PowerSeries.coeff i (swapPowerSeries (G * H)) =
      PowerSeries.coeff i (swapPowerSeries (G' * H'))) {i : ℕ} (hi : i ≤ n) :
    PowerSeries.coeff i (swapPowerSeries G) = PowerSeries.coeff i (swapPowerSeries G') ∧
      PowerSeries.coeff i (swapPowerSeries H) = PowerSeries.coeff i (swapPowerSeries H') := by
  obtain ⟨u, v, huv⟩ := hcop
  -- The reductions of `H` and `H'` agree, since `g * h = g * h'` with `g` monic.
  have hHH' : H.map PowerSeries.constantCoeff = H'.map PowerSeries.constantCoeff := by
    have h₀ := h 0 (Nat.zero_le n)
    simp only [PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_swapPowerSeries,
      Polynomial.map_mul, ← hGG'] at h₀
    exact (hG.map _).isRegular.left h₀
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    rcases eq_or_ne i 0 with rfl | hi0
    · simp only [PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_swapPowerSeries]
      exact ⟨hGG', hHH'⟩
    obtain ⟨hG₁, hH₁⟩ := hG.coeff_swapPowerSeries_eq_and_eq_of_mul_eq rfl huv hi0
    obtain ⟨hG₂, hH₂⟩ := hG'.coeff_swapPowerSeries_eq_and_eq_of_mul_eq (H := H') rfl (u := u)
      (v := v) (by rwa [← hGG', ← hHH']) hi0
    -- The error terms agree: they involve `P` up to `tⁱ` and the factors below `tⁱ`.
    have hc : PowerSeries.coeff i (swapPowerSeries (G * H)) - ∑ j ∈ Finset.Ioo 0 i,
        PowerSeries.coeff j (swapPowerSeries G) * PowerSeries.coeff (i - j) (swapPowerSeries H) =
        PowerSeries.coeff i (swapPowerSeries (G' * H')) - ∑ j ∈ Finset.Ioo 0 i,
        PowerSeries.coeff j (swapPowerSeries G') *
          PowerSeries.coeff (i - j) (swapPowerSeries H') := by
      rw [h i hi]
      congr 1
      refine Finset.sum_congr rfl fun j hj ↦ ?_
      obtain ⟨hj0, hji⟩ := Finset.mem_Ioo.mp hj
      rw [(ih j hji (hji.le.trans hi)).1, (ih (i - j) (by omega) (by omega)).2]
    rw [hG₁, hH₁, hG₂, hH₂, hc, hGG', hHH']
    exact ⟨rfl, rfl⟩

/-- Uniqueness of Hensel lifting over `R⟦t⟧`: if `G * H = G' * H'` with `G` and `G'` monic and
reducing modulo `t` to the same polynomial, coprime to the reduction of `H`, then `G = G'` and
`H = H'`. No monicity of `H` or `H'` is needed. -/
theorem Monic.eq_and_eq_of_mul_eq_mul_of_isCoprime {G G' H H' : R⟦X⟧[X]} (hG : G.Monic)
    (hG' : G'.Monic) (hGG' : G.map PowerSeries.constantCoeff = G'.map PowerSeries.constantCoeff)
    (hcop : IsCoprime (G.map PowerSeries.constantCoeff) (H.map PowerSeries.constantCoeff))
    (h : G * H = G' * H') : G = G' ∧ H = H' := by
  have hcoeff (i : ℕ) := hG.coeff_swapPowerSeries_eq_and_eq_of_coeff_mul_eq hG' hGG' hcop
    (fun j _ ↦ by rw [h]) le_rfl (i := i)
  exact ⟨swapPowerSeries_injective (PowerSeries.ext fun i ↦ (hcoeff i).1),
    swapPowerSeries_injective (PowerSeries.ext fun i ↦ (hcoeff i).2)⟩

end Hensel

section SimpleRoot

variable {R : Type*} [CommRing R]

/-- **The degree-one case of coprime-factor Hensel lifting over `R⟦t⟧`.** Let `P` be monic over
`R⟦t⟧` and let `a` be a simple root of its reduction `p` modulo `t`: `p (a) = 0` and `p' (a)` is a
unit. Then `p = (X - a) * (p /ₘ (X - a))` with coprime factors, and lifting this factorization
gives `P = (X - α) * H` with `α` of constant coefficient `a` and `H` monic reducing to
`p /ₘ (X - a)`. In particular `α` is a root of `P` lifting `a`. -/
theorem Monic.exists_X_sub_C_mul_eq_of_isUnit_eval_derivative {P : R⟦X⟧[X]} (hP : P.Monic)
    {a : R} (hroot : (P.map PowerSeries.constantCoeff).IsRoot a)
    (hunit : IsUnit ((P.map PowerSeries.constantCoeff).derivative.eval a)) :
    ∃ (α : R⟦X⟧) (H : R⟦X⟧[X]), PowerSeries.constantCoeff α = a ∧ H.Monic ∧
      H.map PowerSeries.constantCoeff = P.map PowerSeries.constantCoeff /ₘ (X - C a) ∧
      (X - C α) * H = P := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact ⟨0, 1, Subsingleton.elim _ _, monic_one, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  obtain ⟨G, H, hG, hH, hGa, hHq, hGH⟩ := hP.exists_monic_mul_eq_of_isCoprime (monic_X_sub_C a)
    (by simpa using hunit)
    (mul_divByMonic_eq_iff_isRoot.mpr hroot).symm
  -- The monic lift `G` of `X - a` has degree one, so it is `X - α` with `α = -G.coeff 0`.
  have hGα : G = X - C (-G.coeff 0) := by
    rw [map_neg, sub_neg_eq_add]
    exact hG.eq_X_add_C (by rw [← hG.natDegree_map PowerSeries.constantCoeff, hGa,
      natDegree_X_sub_C])
  refine ⟨-G.coeff 0, H, ?_, hH, hHq, hGα ▸ hGH⟩
  have h₀ := congrArg (fun p : R[X] ↦ p.coeff 0) hGa
  simp only [coeff_map, coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub] at h₀
  rw [map_neg, h₀, neg_neg]

/-- **Simple roots lift uniquely over `R⟦t⟧`.** If `a` is a simple root of the reduction modulo
`t` of a polynomial `P` over `R⟦t⟧`, then `P` has exactly one root with constant coefficient `a`.
`P` need not be monic. This is `Polynomial.existsUnique_isRoot_sub_mem` for the Henselian pair
`(R⟦t⟧, (t))`, read through `PowerSeries.constantCoeff`. -/
theorem existsUnique_isRoot_constantCoeff_eq (P : R⟦X⟧[X]) {a : R}
    (hroot : (P.map PowerSeries.constantCoeff).IsRoot a)
    (hunit : IsUnit ((P.map PowerSeries.constantCoeff).derivative.eval a)) :
    ∃! α : R⟦X⟧, P.IsRoot α ∧ PowerSeries.constantCoeff α = a := by
  have hmem {φ : R⟦X⟧} : φ ∈ Ideal.span {PowerSeries.X} ↔ PowerSeries.constantCoeff φ = 0 := by
    rw [← PowerSeries.ker_constantCoeff, RingHom.mem_ker]
  simpa [hmem, sub_eq_zero] using P.existsUnique_isRoot_sub_mem (J := Ideal.span {PowerSeries.X})
    (a₀ := PowerSeries.C a) (by simpa [hmem, ← eval_map_apply] using hroot)
    ((PowerSeries.isUnit_iff_constantCoeff.mpr (by simpa [← eval_map_apply] using hunit)).map _)

/-- **Newton's recursion for the coefficients of a root over `R⟦t⟧`.** Let `α` be a root of a
polynomial `P` over `R⟦t⟧`, and let `p` be the reduction of `P` modulo `t` and `a` the constant
coefficient of `α`. For `k ≠ 0` the `tᵏ`-coefficient `αₖ` of `α` satisfies
`αₖ * p'(a) = -[tᵏ] P(α mod tᵏ)`, where `α mod tᵏ` is the truncation `PowerSeries.trunc k α`.

When `p'(a)` is a unit this determines `α` from `a` one coefficient at a time, as in Newton's
method for the simple-root form of Hensel's lemma. So the unique root lifting a simple root `a`
(`Polynomial.existsUnique_isRoot_constantCoeff_eq`) has the coefficients of Newton's recursion. -/
theorem IsRoot.coeff_mul_eval_derivative_eq_neg_coeff_eval_trunc {P : R⟦X⟧[X]} {α : R⟦X⟧}
    (hα : P.IsRoot α) {k : ℕ} (hk : k ≠ 0) :
    PowerSeries.coeff k α *
        (P.map PowerSeries.constantCoeff).derivative.eval (PowerSeries.constantCoeff α) =
      -PowerSeries.coeff k (P.eval (PowerSeries.trunc k α : R⟦X⟧)) := by
  set x : R⟦X⟧ := (PowerSeries.trunc k α : R⟦X⟧)
  -- The tail `α - x` is `tᵏ * w`, with `w` of constant coefficient `αₖ`.
  obtain ⟨w, hw⟩ : PowerSeries.X ^ k ∣ α - x := PowerSeries.X_pow_dvd_iff.mpr fun i hi ↦ by
    simp [x, Polynomial.coeff_coe, PowerSeries.coeff_trunc, hi]
  have hw₀ : PowerSeries.constantCoeff w = PowerSeries.coeff k α := by
    have := congrArg (PowerSeries.coeff k) hw
    simpa [x, PowerSeries.coeff_X_pow_mul', Polynomial.coeff_coe, PowerSeries.coeff_trunc] using
      this.symm
  have hx₀ : PowerSeries.constantCoeff x = PowerSeries.constantCoeff α := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp [x, Polynomial.coeff_coe, PowerSeries.coeff_trunc, Nat.pos_of_ne_zero hk]
  -- Expand `P (x + tᵏ w)` to first order; the remainder is divisible by `t ^ (2 * k)`.
  obtain ⟨K, hK⟩ := P.binomExpansion x (α - x)
  rw [add_sub_cancel, hα.eq_zero, hw] at hK
  have hK' : P.eval x + PowerSeries.X ^ k * (P.derivative.eval x * w +
      PowerSeries.X ^ k * (K * w ^ 2)) = 0 := by
    linear_combination -hK
  have hcoeff := congrArg (PowerSeries.coeff k) hK'
  simp [PowerSeries.coeff_X_pow_mul', zero_pow hk, hw₀] at hcoeff
  rw [derivative_map, ← hx₀, eval_map_apply]
  linear_combination hcoeff

end SimpleRoot

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

namespace PowerSeries

variable {K : Type*} [Field K]

/-- **Hensel's lemma for `K⟦t⟧`.** Over a field `K`, the power series ring `K⟦t⟧` is a Henselian
local ring: it is complete for its maximal ideal `(t)`, so this is Mathlib's
`IsAdicComplete.henselianRing` at the maximal ideal, read through
`TauCeti.IsAdicComplete.henselianLocalRing`. -/
instance henselianLocalRing : HenselianLocalRing K⟦X⟧ :=
  have : IsAdicComplete (IsLocalRing.maximalIdeal K⟦X⟧) K⟦X⟧ := by
    rw [maximalIdeal_eq_span_X]
    infer_instance
  TauCeti.IsAdicComplete.henselianLocalRing _

/-- **`n`-th roots of units in `K⟦t⟧`.** If `n` is invertible in `K` and the constant
coefficient of `u` is `c ^ n` for some `c ≠ 0`, then `u` has an `n`-th root with constant
coefficient `c`, by Hensel's lemma applied to `X ^ n - u` at the approximate root `c`. -/
theorem exists_pow_eq_of_constantCoeff_eq_pow {n : ℕ} (hn : (n : K) ≠ 0) {u : K⟦X⟧} {c : K}
    (hc : c ≠ 0) (hu : constantCoeff u = c ^ n) :
    ∃ v : K⟦X⟧, v ^ n = u ∧ constantCoeff v = c := by
  have hres {x y : K⟦X⟧} :
      IsLocalRing.residue K⟦X⟧ x = IsLocalRing.residue K⟦X⟧ y ↔
        constantCoeff x = constantCoeff y := by
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, ← ker_coeff_eq_max_ideal,
      RingHom.mem_ker, map_sub, sub_eq_zero]
  obtain ⟨v, hv, hvc⟩ := TauCeti.HenselianLocalRing.exists_pow_eq_of_residue_pow_eq
    (x₀ := C c) (u := u)
    (by rw [isUnit_iff_constantCoeff, map_natCast]; exact hn.isUnit)
    (by rw [isUnit_iff_constantCoeff, constantCoeff_C]; exact hc.isUnit)
    (by rw [← map_pow, hres, map_pow, constantCoeff_C, hu])
  exact ⟨v, hv, by rwa [hres, constantCoeff_C] at hvc⟩

/-- Over an algebraically closed field `K`, every unit of `K⟦t⟧` has an `n`-th root for every `n`
invertible in `K`. -/
theorem exists_pow_eq_of_isUnit [IsAlgClosed K] {n : ℕ} (hn : (n : K) ≠ 0) {u : K⟦X⟧}
    (hu : IsUnit u) : ∃ v : K⟦X⟧, v ^ n = u := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hn Nat.cast_zero
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (constantCoeff u) (Nat.pos_of_ne_zero hn0)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow hn0] at hc
    exact (isUnit_iff_constantCoeff.mp hu).ne_zero hc.symm
  obtain ⟨v, hv, -⟩ := exists_pow_eq_of_constantCoeff_eq_pow hn hc0 hc.symm
  exact ⟨v, hv⟩

end PowerSeries
