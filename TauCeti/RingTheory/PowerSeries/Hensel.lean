/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Basic
public import TauCeti.RingTheory.Polynomial.DegreeLT
import Mathlib.Tactic.LinearCombination

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
`Polynomial.swapPowerSeries : R⟦X⟧[X] →+* R[X]⟦X⟧`. Write `G = Σ Gₖ tᵏ` and `H = Σ Hₖ tᵏ` with
`G₀ = g` and `H₀ = h`. The coefficient of `tᵏ` in `G * H = P` reads

`g * Hₖ + h * Gₖ = Pₖ - Σ_{0 < i < k} Gᵢ * H_{k - i}`,

and, `G` and `H` being monic of the degrees of `g` and `h`, the corrections satisfy
`deg Gₖ < deg g` and `deg Hₖ < deg h` for `k ≥ 1`. Writing `u * g + v * h = 1`, Bézout and
division by `g` give the unique solution of this equation within those degree bounds
(`IsCoprime.exists_mem_degreeLT_mul_add_mul_eq`, `IsCoprime.eq_zero_of_mul_add_mul_eq_zero`).
Solving it for `k = 1, 2, ...` produces the factors one power of `t` at a time; uniqueness of
each step gives uniqueness of the factorization.

## Main definitions

* `Polynomial.swapPowerSeries`: the ring homomorphism `R⟦X⟧[X] →+* R[X]⟦X⟧` exchanging the
  polynomial variable with the power-series variable.

## Main results

* `Polynomial.coeff_coeff_swapPowerSeries`: the coefficient of `Xⁱ` in the `tᵏ`-coefficient of
  `swapPowerSeries Q` is the `tᵏ`-coefficient of the coefficient of `Xⁱ` in `Q`.
* `Polynomial.swapPowerSeries_injective`: `swapPowerSeries` is injective.
* `Polynomial.Monic.exists_monic_mul_eq_of_isCoprime`: existence of the lifted factorization.
* `Polynomial.Monic.eq_and_eq_of_mul_eq_mul_of_isCoprime`: uniqueness of the lifted
  factorization.

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

section swapPowerSeries

variable {R : Type*} [CommSemiring R]

/-- The ring homomorphism `R⟦X⟧[X] →+* R[X]⟦X⟧` exchanging the two variables: a polynomial in
`X` whose coefficients are power series in `t` is sent to the power series in `t` whose
coefficients are polynomials in `X`. -/
def swapPowerSeries : R⟦X⟧[X] →+* R[X]⟦X⟧ :=
  eval₂RingHom (PowerSeries.map C) (PowerSeries.C X)

/-- The coefficient of `Xⁱ` in the `tᵏ`-coefficient of `swapPowerSeries Q` is the
`tᵏ`-coefficient of the coefficient of `Xⁱ` in `Q`. -/
@[simp]
theorem coeff_coeff_swapPowerSeries (Q : R⟦X⟧[X]) (k i : ℕ) :
    (PowerSeries.coeff k (swapPowerSeries Q)).coeff i = PowerSeries.coeff k (Q.coeff i) := by
  induction Q using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a =>
    simp only [swapPowerSeries, coe_eval₂RingHom, eval₂_monomial, ← map_pow,
      PowerSeries.coeff_mul_C, PowerSeries.coeff_map, coeff_C_mul_X_pow, coeff_monomial]
    split_ifs <;> simp_all

/-- The constant coefficient of `swapPowerSeries Q` is the reduction of `Q` modulo `t`. -/
@[simp]
theorem constantCoeff_swapPowerSeries (Q : R⟦X⟧[X]) :
    PowerSeries.constantCoeff (swapPowerSeries Q) = Q.map PowerSeries.constantCoeff := by
  ext i
  rw [coeff_map, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_coeff_swapPowerSeries]

/-- A polynomial over `R⟦t⟧` is determined by its image under `swapPowerSeries`. -/
theorem swapPowerSeries_injective : Function.Injective (swapPowerSeries (R := R)) := by
  intro P Q h
  ext i k
  rw [← coeff_coeff_swapPowerSeries, h, coeff_coeff_swapPowerSeries]

/-- If `Q` has degree `< n`, then so does every coefficient of `swapPowerSeries Q`. -/
theorem coeff_swapPowerSeries_mem_degreeLT {Q : R⟦X⟧[X]} {n : ℕ} (hQ : Q ∈ degreeLT R⟦X⟧ n)
    (k : ℕ) : PowerSeries.coeff k (swapPowerSeries Q) ∈ degreeLT R n := by
  rw [mem_degreeLT, degree_lt_iff_coeff_zero] at hQ ⊢
  intro i hi
  simp [hQ i hi]

end swapPowerSeries

section Hensel

variable {R : Type*} [CommRing R]

/-- The difference of two monic polynomials of the same degree `n` has degree `< n`. -/
private theorem sub_mem_degreeLT_of_monic {S : Type*} [CommRing S] [Nontrivial S] {P Q : S[X]}
    (hP : P.Monic) (hQ : Q.Monic) (hPQ : P.natDegree = Q.natDegree) :
    P - Q ∈ degreeLT S P.natDegree := by
  rw [mem_degreeLT, ← degree_eq_natDegree hP.ne_zero]
  refine degree_sub_lt_left ?_ hP.ne_zero (by rw [hP.leadingCoeff, hQ.leadingCoeff])
  rw [degree_eq_natDegree hP.ne_zero, degree_eq_natDegree hQ.ne_zero, hPQ]

/-- A power series `F` over `R[X]` whose constant coefficient is monic of degree `d` and whose
other coefficients have degree `< d` comes from a monic polynomial over `R⟦X⟧`. -/
private theorem exists_monic_swapPowerSeries_eq {g : R[X]} (hg : g.Monic) {F : R[X]⟦X⟧}
    (hF₀ : PowerSeries.constantCoeff F = g)
    (hF : ∀ k, 1 ≤ k → PowerSeries.coeff k F ∈ degreeLT R g.natDegree) :
    ∃ G : R⟦X⟧[X], G.Monic ∧ swapPowerSeries G = F := by
  let a : ℕ → R⟦X⟧ := fun i ↦ PowerSeries.mk fun k ↦ (PowerSeries.coeff k F).coeff i
  have hdeg : (∑ i : Fin g.natDegree, C (a i) * X ^ (i : ℕ)).degree < (g.natDegree : WithBot ℕ) :=
    degree_sum_fin_lt _
  refine ⟨X ^ g.natDegree + ∑ i : Fin g.natDegree, C (a i) * X ^ (i : ℕ),
    monic_X_pow_add hdeg, ?_⟩
  ext k i
  rw [coeff_coeff_swapPowerSeries, coeff_add, coeff_X_pow]
  have hFk : (PowerSeries.coeff k F).coeff g.natDegree = if k = 0 then 1 else 0 := by
    split_ifs with hk
    · rw [hk, PowerSeries.coeff_zero_eq_constantCoeff_apply, hF₀, hg.coeff_natDegree]
    · exact coeff_eq_zero_of_degree_lt (mem_degreeLT.mp (hF k (Nat.one_le_iff_ne_zero.mpr hk)))
  rcases lt_trichotomy i g.natDegree with hi | rfl | hi
  · rw [ite_eq_right hi.ne, zero_add, finsetSum_coeff,
      Finset.sum_eq_single ⟨i, hi⟩ (fun j _ hj ↦ ?_) (by simp)]
    · simp [a]
    · rw [coeff_C_mul_X_pow, ite_eq_right (fun h ↦ hj (Fin.ext h.symm))]
  · rw [ite_eq_left rfl, coeff_eq_zero_of_degree_lt hdeg, add_zero, hFk, PowerSeries.coeff_one]
  · rw [ite_eq_right hi.ne', zero_add,
      coeff_eq_zero_of_degree_lt (hdeg.trans (by exact_mod_cast hi)), map_zero]
    rcases eq_or_ne k 0 with rfl | hk
    · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hF₀, coeff_eq_zero_of_natDegree_lt hi]
    · exact (coeff_eq_zero_of_degree_lt ((mem_degreeLT.mp
        (hF k (Nat.one_le_iff_ne_zero.mpr hk))).trans (by exact_mod_cast hi))).symm

/-- If `F₂ * B + F₁ * A = 0` for power series over `R[X]`, where the constant coefficient `g` of
`F₂` is monic and coprime to that of `F₁` and every coefficient of `A` has degree `< deg g`, then
`A = 0` and `B = 0`: the coefficient recursion of Hensel lifting has unique solutions. -/
private theorem eq_zero_of_mul_add_mul_eq_zero {g : R[X]} (hg : g.Monic) {A B F₁ F₂ : R[X]⟦X⟧}
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

/-- A monic polynomial `P` over `R⟦t⟧` whose reduction modulo `t` is a product `g * h` of
coprime monic polynomials factors as `P = G * H` with `G` and `H` monic and reducing to `g` and
`h`. This is the coprime-factor form of Hensel's lemma over `R⟦t⟧`; the factors are unique by
`Polynomial.Monic.eq_and_eq_of_mul_eq_mul_of_isCoprime`. -/
theorem Monic.exists_monic_mul_eq_of_isCoprime {P : R⟦X⟧[X]} (hP : P.Monic) {g h : R[X]}
    (hg : g.Monic) (hh : h.Monic) (hgh : IsCoprime g h)
    (hPgh : P.map PowerSeries.constantCoeff = g * h) :
    ∃ G H : R⟦X⟧[X], G.Monic ∧ H.Monic ∧ G.map PowerSeries.constantCoeff = g ∧
      H.map PowerSeries.constantCoeff = h ∧ G * H = P := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact ⟨P, 1, hP, monic_one, Subsingleton.elim _ _, Subsingleton.elim _ _, mul_one P⟩
  choose! a b ha hb hab using fun c (hc : c ∈ degreeLT R (g.natDegree + h.natDegree)) ↦
    hgh.exists_mem_degreeLT_mul_add_mul_eq hg hc
  have hPdeg : P.natDegree = g.natDegree + h.natDegree := by
    rw [← hP.natDegree_map PowerSeries.constantCoeff, hPgh, hg.natDegree_mul hh]
  -- A power series with the shape of a lifted factor comes from a monic polynomial of the same
  -- degree.
  have realize {f : R[X]} (hf : f.Monic) {F : R[X]⟦X⟧} (hF₀ : PowerSeries.constantCoeff F = f)
      (hF : ∀ k, 1 ≤ k → PowerSeries.coeff k F ∈ degreeLT R f.natDegree) :
      ∃ G : R⟦X⟧[X], G.Monic ∧ G.natDegree = f.natDegree ∧
        G.map PowerSeries.constantCoeff = f ∧ swapPowerSeries G = F := by
    obtain ⟨G, hG, rfl⟩ := exists_monic_swapPowerSeries_eq hf hF₀ hF
    rw [constantCoeff_swapPowerSeries] at hF₀
    exact ⟨G, hG, by rw [← hF₀, hG.natDegree_map], hF₀, rfl⟩
  set S := approx (swapPowerSeries P) g h a b
  -- The invariants of the approximations: the constant coefficients are `g` and `h`, the higher
  -- coefficients satisfy the degree bounds, and the error vanishes modulo `t ^ (k + 1)`.
  have inv : ∀ k, PowerSeries.constantCoeff (S k).1 = g ∧ PowerSeries.constantCoeff (S k).2 = h ∧
      (∀ j, 1 ≤ j → PowerSeries.coeff j (S k).1 ∈ degreeLT R g.natDegree ∧
        PowerSeries.coeff j (S k).2 ∈ degreeLT R h.natDegree) ∧
      PowerSeries.X ^ (k + 1) ∣ swapPowerSeries P - (S k).1 * (S k).2 := by
    intro k
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
        obtain ⟨G, hG, hGdeg, -, hGS⟩ := realize hg h₁ fun j hj ↦ (hdeg j hj).1
        obtain ⟨H, hH, hHdeg, -, hHS⟩ := realize hh h₂ fun j hj ↦ (hdeg j hj).2
        rw [hc_def, ← hGS, ← hHS, ← map_mul, ← map_sub, ← hPdeg]
        refine coeff_swapPowerSeries_mem_degreeLT (sub_mem_degreeLT_of_monic hP (hG.mul hH) ?_) _
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
        rw [hS, map_mul] at *
        linear_combination hE + PowerSeries.X ^ (k + 1) * hE'
  have stab {j k : ℕ} (hjk : j ≤ k) :
      PowerSeries.coeff j (S k).1 = PowerSeries.coeff j (S j).1 ∧
        PowerSeries.coeff j (S k).2 = PowerSeries.coeff j (S j).2 :=
    coeff_approx_of_le _ _ _ _ _ hjk
  let G' : R[X]⟦X⟧ := PowerSeries.mk fun j ↦ PowerSeries.coeff j (S j).1
  let H' : R[X]⟦X⟧ := PowerSeries.mk fun j ↦ PowerSeries.coeff j (S j).2
  have hGH' : G' * H' = swapPowerSeries P := by
    refine PowerSeries.ext fun n ↦ ?_
    have hn := PowerSeries.X_pow_dvd_iff.mp (inv n).2.2.2 n n.lt_succ_self
    rw [map_sub, sub_eq_zero] at hn
    rw [hn, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
    refine Finset.sum_congr rfl fun x hx ↦ ?_
    have hx' := Finset.mem_antidiagonal.mp hx
    simp only [G', H', PowerSeries.coeff_mk, (stab (show x.1 ≤ n by omega)).1,
      (stab (show x.2 ≤ n by omega)).2]
  obtain ⟨G, hG, -, hGg, hGS⟩ := realize hg (F := G') (by
    simp [G', ← PowerSeries.coeff_zero_eq_constantCoeff_apply, S, approx])
    fun j hj ↦ by simpa [G'] using ((inv j).2.2.1 j hj).1
  obtain ⟨H, hH, -, hHh, hHS⟩ := realize hh (F := H') (by
    simp [H', ← PowerSeries.coeff_zero_eq_constantCoeff_apply, S, approx])
    fun j hj ↦ by simpa [H'] using ((inv j).2.2.1 j hj).2
  exact ⟨G, H, hG, hH, hGg, hHh, swapPowerSeries_injective (by rw [map_mul, hGS, hHS, hGH'])⟩

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
    exact coeff_swapPowerSeries_mem_degreeLT (sub_mem_degreeLT_of_monic hG hG' hdeg) k
  have hrel : swapPowerSeries G' * swapPowerSeries (H - H') +
      swapPowerSeries H * swapPowerSeries (G - G') = 0 := by
    rw [← map_mul, ← map_mul, ← map_add, ← map_zero swapPowerSeries]
    congr 1
    linear_combination h
  obtain ⟨hA0, hB0⟩ := eq_zero_of_mul_add_mul_eq_zero (hG.map _)
    (by rwa [constantCoeff_swapPowerSeries]) (by rw [constantCoeff_swapPowerSeries, hGG']) hA hrel
  rw [← map_zero swapPowerSeries] at hA0 hB0
  exact ⟨sub_eq_zero.mp (swapPowerSeries_injective hA0),
    sub_eq_zero.mp (swapPowerSeries_injective hB0)⟩

end Hensel

end Polynomial
