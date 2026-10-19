/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Trunc
public import TauCeti.RingTheory.PowerSeries.Entire.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.LinearCombination
import TauCeti.RingTheory.PowerSeries.Weierstrass.Division

/-!
# Division of entire power series by monic polynomials

Let `p` be a monic polynomial of degree `d` over a complete normed commutative ring `R`, and let
`∑ bₖ Xᵏ` be the inverse of its reverse `Xᵈ p(1/X)`, a power series with constant coefficient
`1`. For an entire series `f = ∑ aₙ Xⁿ`, the series

```text
q = ∑ₙ (∑ₖ a_{n+d+k} bₖ) Xⁿ
```

converges coefficientwise, is again entire, and satisfies `f = p * q + r` for a polynomial `r` of
degree less than `d`. The coefficients `bₖ` grow at most geometrically, which is what makes the
inner sums converge however fast the radius of `f` is tested. Over an ultrametric ring with
`‖1‖ = 1`, a monic polynomial is distinguished of its degree at every large radius, so the
Weierstrass division estimate makes `q` and `r` unique among divisions with entire quotient. In
particular they agree with ordinary polynomial division when `f` is a polynomial.

This is the division of entire series by polynomials used in the Fredholm theory of compact
operators, whose Fredholm determinants are entire series.

## Main definitions

* `PowerSeries.divByMonic`: the quotient `q` above, given by the explicit coefficient formula.
* `PowerSeries.modByMonic`: the remainder `f - p * q`, truncated to a polynomial of degree less
  than `d`.

## Main results

* `PowerSeries.norm_coeff_invOfUnit_coe_le`: the inverse of a polynomial with invertible constant
  coefficient has geometrically bounded coefficients.
* `PowerSeries.hasSum_coeff_divByMonic`: for entire `f`, the coefficients of `q` are the sums
  `∑ₖ a_{n+d+k} bₖ`.
* `PowerSeries.IsEntire.divByMonic`: the quotient of an entire series is entire.
* `PowerSeries.IsEntire.modByMonic_add_divByMonic`: the division identity `r + p * q = f`.
* `PowerSeries.divByMonic_modByMonic_unique`: over an ultrametric ring with `‖1‖ = 1`, a division
  with entire quotient and remainder of degree less than `d` is this one.
* `PowerSeries.IsEntire.modByMonic_eq_zero_iff`: the remainder vanishes exactly when `p` divides
  `f` with entire quotient.
* `PowerSeries.divByMonic_coe` and `PowerSeries.modByMonic_coe`: on polynomials, these are
  `Polynomial.divByMonic` and `Polynomial.modByMonic`.

## References

* R. F. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. 127 (1997),
  Appendix A3.
-/

public section

namespace PowerSeries

open Filter Finset
open scoped Topology

section NormedRing

variable {R : Type*} [NormedRing R]

/-- **Geometric growth of the inverse of a polynomial.** If the constant coefficient of a
polynomial `p` is a unit `u`, the coefficients of the power series inverse of `p` are bounded by
`‖u⁻¹‖ * (1 + ‖u⁻¹‖ * ∑ᵢ ‖pᵢ‖) ^ k`. -/
theorem norm_coeff_invOfUnit_coe_le (p : Polynomial R) (u : Rˣ) (k : ℕ) :
    ‖coeff k (invOfUnit (p : R⟦X⟧) u)‖ ≤
      ‖(↑u⁻¹ : R)‖ * (1 + ‖(↑u⁻¹ : R)‖ * ∑ i ∈ p.support, ‖p.coeff i‖) ^ k := by
  set A := ‖(↑u⁻¹ : R)‖
  set s := ∑ i ∈ p.support, ‖p.coeff i‖
  have hA : 0 ≤ A := norm_nonneg _
  have hs : 0 ≤ s := sum_nonneg fun _ _ ↦ norm_nonneg _
  have hC : 1 ≤ 1 + A * s := le_add_of_nonneg_right (mul_nonneg hA hs)
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [coeff_invOfUnit, A]
  rw [coeff_invOfUnit, ite_eq_right hk.ne', neg_mul, norm_neg]
  simp only [Polynomial.coeff_coe]
  -- Each term of the recursion is bounded by `‖pᵢ‖ * A * C ^ (k - 1)`.
  have hterm (x : ℕ × ℕ) : ‖if x.2 < k then p.coeff x.1 * coeff x.2 (invOfUnit (p : R⟦X⟧) u)
      else 0‖ ≤ ‖p.coeff x.1‖ * (A * (1 + A * s) ^ (k - 1)) := by
    split_ifs with hx
    · refine (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
      exact (ih x.2 hx).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hC (by omega)) hA)
    · rw [norm_zero]
      positivity
  have hsupp : ∑ x ∈ antidiagonal k, ‖p.coeff x.1‖ ≤ s := by
    rw [Nat.sum_antidiagonal_eq_sum_range_succ_mk, ← sum_filter_of_ne (p := (· ∈ p.support))
      fun i _ hi ↦ Polynomial.mem_support_iff.mpr fun h ↦ hi (by simp [h])]
    exact sum_le_sum_of_subset_of_nonneg (fun _ hi ↦ (mem_filter.mp hi).2)
      fun _ _ _ ↦ norm_nonneg _
  calc ‖(↑u⁻¹ : R) * ∑ x ∈ antidiagonal k, if x.2 < k then
          p.coeff x.1 * coeff x.2 (invOfUnit (p : R⟦X⟧) u) else 0‖
      ≤ A * ∑ x ∈ antidiagonal k, ‖p.coeff x.1‖ * (A * (1 + A * s) ^ (k - 1)) :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left
          ((norm_sum_le _ _).trans (sum_le_sum fun x _ ↦ hterm x)) hA)
    _ ≤ A * (s * (A * (1 + A * s) ^ (k - 1))) := by
        rw [← sum_mul]
        gcongr
    _ = A * (A * s) * (1 + A * s) ^ (k - 1) := by ring
    _ ≤ A * (1 + A * s) * (1 + A * s) ^ (k - 1) := by gcongr; linarith
    _ = A * (1 + A * s) ^ k := by
        rw [mul_assoc, ← pow_succ', Nat.sub_add_cancel hk]

end NormedRing

section TopologicalRing

variable {R : Type*} [CommRing R] [TopologicalSpace R]

/-- The quotient of a power series `f` on division by a monic polynomial `p` of degree `d`: its
coefficient in degree `n` is `∑ₖ a_{n+d+k} bₖ`, where `aₘ` are the coefficients of `f` and `bₖ`
those of the inverse of the reverse of `p`. For entire `f` these sums converge
(`PowerSeries.hasSum_coeff_divByMonic`) and give the quotient of a division with polynomial
remainder (`PowerSeries.IsEntire.modByMonic_add_divByMonic`). Otherwise the value is not
meaningful. -/
noncomputable def divByMonic (f : R⟦X⟧) (p : Polynomial R) : R⟦X⟧ :=
  mk fun n ↦ ∑' k, coeff (n + p.natDegree + k) f * coeff k (invOfUnit (p.reverse : R⟦X⟧) 1)

/-- The remainder of a power series `f` on division by a monic polynomial `p`: the polynomial of
degree less than `natDegree p` given by the coefficients of `f - p * f.divByMonic p` in those
degrees. For entire `f`, `f - p * f.divByMonic p` is this polynomial
(`PowerSeries.IsEntire.modByMonic_add_divByMonic`). -/
noncomputable def modByMonic (f : R⟦X⟧) (p : Polynomial R) : Polynomial R :=
  trunc p.natDegree (f - (p : R⟦X⟧) * f.divByMonic p)

variable {p : Polynomial R}

/-- The coefficients of `f.divByMonic p`, as the defining sums. -/
theorem coeff_divByMonic (f : R⟦X⟧) (p : Polynomial R) (n : ℕ) :
    coeff n (f.divByMonic p) =
      ∑' k, coeff (n + p.natDegree + k) f * coeff k (invOfUnit (p.reverse : R⟦X⟧) 1) := by
  rw [divByMonic, coeff_mk]

/-- The coefficients of `f.modByMonic p` are those of `f - p * f.divByMonic p` in degrees less
than `natDegree p`. -/
theorem coeff_modByMonic (f : R⟦X⟧) (p : Polynomial R) (n : ℕ) :
    (f.modByMonic p).coeff n =
      if n < p.natDegree then coeff n (f - (p : R⟦X⟧) * f.divByMonic p) else 0 := by
  rw [modByMonic, coeff_trunc]

/-- The remainder has degree less than the divisor. -/
theorem degree_modByMonic_lt (f : R⟦X⟧) (hp : p ≠ 0) : (f.modByMonic p).degree < p.degree := by
  rw [Polynomial.degree_eq_natDegree hp]
  exact degree_trunc_lt _ _

/-- Division by the polynomial `1` returns the series itself. -/
@[simp]
theorem divByMonic_one (f : R⟦X⟧) : f.divByMonic 1 = f := by
  have hinv : invOfUnit (1 : R⟦X⟧) 1 = 1 := by simpa using mul_invOfUnit (1 : R⟦X⟧) 1 (by simp)
  ext n
  rw [coeff_divByMonic, Polynomial.natDegree_one, ← Polynomial.C_1, Polynomial.reverse_C,
    Polynomial.C_1, Polynomial.coe_one,
    hinv, tsum_eq_single 0 fun k hk ↦ by simp [coeff_one, hk]]
  simp

/-- Division by the polynomial `1` leaves no remainder. -/
@[simp]
theorem modByMonic_one (f : R⟦X⟧) : f.modByMonic 1 = 0 := by
  ext n
  simp [coeff_modByMonic]

end TopologicalRing

section NormedCommRing

variable {R : Type*} [NormedCommRing R] {f : R⟦X⟧} {p : Polynomial R}

/-- The terms of the sum defining a coefficient of `f.divByMonic p` are geometrically small
when `f` is bounded at a radius `s` that is large compared with the growth of the inverse of the
reverse of `p`. -/
private theorem norm_coeff_mul_coeff_le {b : ℕ → R} {s M A C : ℝ} (hs : 1 ≤ s) (hCs : 2 * C ≤ s)
    (hA : 0 ≤ A) (hC0 : 0 ≤ C) (hM : ∀ m, ‖coeff m f‖ * s ^ m ≤ M) (hb : ∀ k, ‖b k‖ ≤ A * C ^ k)
    (d n k : ℕ) :
    ‖coeff (n + d + k) f * b k‖ ≤ M * A * (s ^ n)⁻¹ * (1 / 2) ^ k := by
  have hs0 : 0 < s := zero_lt_one.trans_le hs
  have hM0 : 0 ≤ M := (by positivity : 0 ≤ ‖coeff 0 f‖ * s ^ 0).trans (hM 0)
  have hC : C ≤ s / 2 := by linarith
  calc ‖coeff (n + d + k) f * b k‖ ≤ ‖coeff (n + d + k) f‖ * (A * (s / 2) ^ k) :=
        (norm_mul_le _ _).trans (by gcongr; exact (hb k).trans (by gcongr))
    _ = ‖coeff (n + d + k) f‖ * s ^ (n + d + k) * A * (s ^ n)⁻¹ * (1 / 2) ^ k * (s ^ d)⁻¹ := by
        field_simp
        ring
    _ ≤ M * A * (s ^ n)⁻¹ * (1 / 2) ^ k * 1 := by
        gcongr
        · exact hM _
        · exact inv_le_one_of_one_le₀ (one_le_pow₀ hs)
    _ = M * A * (s ^ n)⁻¹ * (1 / 2) ^ k := mul_one _

/-- For entire `f`, the terms of the sums defining the coefficients of `f.divByMonic p` are
bounded by `K * (s ^ n)⁻¹ * (1 / 2) ^ k` for some radius `s` exceeding a given `r`. -/
private theorem exists_norm_coeff_mul_coeff_le (hf : f.IsEntire) (p : Polynomial R) (r : ℝ) :
    ∃ K s : ℝ, |r| < s ∧ ∀ n k, ‖coeff (n + p.natDegree + k) f *
      coeff k (invOfUnit (p.reverse : R⟦X⟧) 1)‖ ≤ K * (s ^ n)⁻¹ * (1 / 2) ^ k := by
  set A := ‖(↑(1 : Rˣ)⁻¹ : R)‖
  set C := 1 + A * ∑ i ∈ p.reverse.support, ‖p.reverse.coeff i‖
  have hC : 1 ≤ C := le_add_of_nonneg_right (mul_nonneg (norm_nonneg _)
    (sum_nonneg fun _ _ ↦ norm_nonneg _))
  set s := 2 * (C + |r|)
  obtain ⟨M, hM⟩ := ((isRestricted_iff' s f).mp (hf.isRestricted s)).bddAbove_range
  refine ⟨M * A, s, by dsimp [s]; linarith [abs_nonneg r], fun n k ↦ ?_⟩
  exact norm_coeff_mul_coeff_le (by dsimp [s]; linarith [abs_nonneg r])
    (by dsimp [s]; linarith [abs_nonneg r]) (norm_nonneg _) (by linarith) (fun m ↦ hM ⟨m, rfl⟩)
    (norm_coeff_invOfUnit_coe_le p.reverse 1) p.natDegree n k

/-- The quotient of an entire series on division by a polynomial is entire. -/
theorem IsEntire.divByMonic (hf : f.IsEntire) (p : Polynomial R) : (f.divByMonic p).IsEntire := by
  rw [isEntire_iff]
  intro r
  rw [← isRestricted_abs_iff, isRestricted_iff']
  obtain ⟨K, s, hrs, hK⟩ := exists_norm_coeff_mul_coeff_le hf p r
  have hs : 0 < s := (abs_nonneg r).trans_lt hrs
  have hcoeff (n : ℕ) : ‖coeff n (f.divByMonic p)‖ ≤ K * (s ^ n)⁻¹ * 2 := by
    rw [coeff_divByMonic]
    exact tsum_of_norm_bounded (hasSum_geometric_two.mul_left _) (hK n)
  have hupper : Tendsto (fun n : ℕ ↦ (|r| / s) ^ n * (2 * K)) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
      ((div_lt_one hs).mpr hrs)).mul_const (2 * K)
  refine squeeze_zero (fun n ↦ by positivity) (fun n ↦ ?_) hupper
  calc ‖coeff n (f.divByMonic p)‖ * |r| ^ n ≤ K * (s ^ n)⁻¹ * 2 * |r| ^ n := by
        gcongr
        exact hcoeff n
    _ = (|r| / s) ^ n * (2 * K) := by
        rw [div_pow]
        ring

/-- Coefficients of the product of a polynomial and a power series, expanded along the
monomials of the polynomial. -/
private theorem coeff_coe_mul_eq_sum (p : Polynomial R) (g : R⟦X⟧) {N : ℕ} (hN : p.natDegree < N)
    (n : ℕ) : coeff n ((p : R⟦X⟧) * g) = ∑ i ∈ range N, p.coeff i * coeff n (X ^ i * g) := by
  rw [← Polynomial.eval₂_C_X_eq_coe, Polynomial.eval₂_eq_sum_range' _ hN, sum_mul, map_sum]
  simp [mul_assoc, coeff_C_mul]

variable [CompleteSpace R]

/-- **The coefficient formula for entire division.** For an entire series `f`, the sums defining
the coefficients of `f.divByMonic p` converge. -/
theorem hasSum_coeff_divByMonic (hf : f.IsEntire) (p : Polynomial R) (n : ℕ) :
    HasSum (fun k ↦ coeff (n + p.natDegree + k) f * coeff k (invOfUnit (p.reverse : R⟦X⟧) 1))
      (coeff n (f.divByMonic p)) := by
  obtain ⟨K, s, -, hK⟩ := exists_norm_coeff_mul_coeff_le hf p 0
  rw [coeff_divByMonic]
  exact (Summable.of_norm_bounded (summable_geometric_two.mul_left (K * (s ^ n)⁻¹))
    (hK n)).hasSum

/-- In every degree at least `natDegree p`, the product `p * f.divByMonic p` has the same
coefficient as `f`. -/
private theorem IsEntire.coeff_coe_mul_divByMonic (hf : f.IsEntire) (hp : p.Monic) {m : ℕ}
    (hm : p.natDegree ≤ m) : coeff m ((p : R⟦X⟧) * f.divByMonic p) = coeff m f := by
  set G := invOfUnit (p.reverse : R⟦X⟧) 1
  -- Shifting the inverse by `Xᵗ` shifts the defining sum.
  have hshift (t : ℕ) : HasSum (fun l ↦ coeff (m + l) f * coeff l (X ^ t * G))
      (coeff (m - p.natDegree + t) (f.divByMonic p)) := by
    rw [← hasSum_nat_add_iff' t]
    have hzero : ∑ i ∈ range t, coeff (m + i) f * coeff i (X ^ t * G) = 0 :=
      sum_eq_zero fun i hi ↦ by
        rw [coeff_X_pow_mul', ite_eq_right (by simpa using hi), mul_zero]
    rw [hzero, sub_zero]
    convert hasSum_coeff_divByMonic hf p (m - p.natDegree + t) using 2 with l
    rw [coeff_X_pow_mul', ite_eq_left (Nat.le_add_left t l), Nat.add_sub_cancel,
      show m - p.natDegree + t + p.natDegree + l = m + (l + t) by omega]
  have hrev : ((p.reverse : R⟦X⟧) * G) = 1 :=
    mul_invOfUnit _ _ (by simp [Polynomial.coeff_zero_reverse, hp.leadingCoeff])
  have hsum := hasSum_sum (s := range (p.natDegree + 1)) fun t _ ↦
    (hshift t).mul_left (p.reverse.coeff t)
  have hfun : (fun l ↦ ∑ t ∈ range (p.natDegree + 1), p.reverse.coeff t *
      (coeff (m + l) f * coeff l (X ^ t * G))) = fun l ↦ coeff (m + l) f * coeff l (1 : R⟦X⟧) := by
    ext l
    rw [← hrev, coeff_coe_mul_eq_sum _ _ (Nat.lt_succ_of_le (p.reverse_natDegree_le)), mul_sum]
    exact sum_congr rfl fun t _ ↦ by ring
  rw [hfun] at hsum
  have hone : HasSum (fun l ↦ coeff (m + l) f * coeff l (1 : R⟦X⟧)) (coeff m f) := by
    convert hasSum_single (f := fun l ↦ coeff (m + l) f * coeff l (1 : R⟦X⟧)) 0
      fun l hl ↦ by simp [coeff_one, hl] using 1
    simp [coeff_one]
  rw [hone.unique hsum, coeff_coe_mul_eq_sum _ _ (Nat.lt_succ_self _),
    ← sum_range_reflect]
  refine sum_congr rfl fun t ht ↦ ?_
  have htd : t ≤ p.natDegree := Nat.lt_succ_iff.mp (mem_range.mp ht)
  rw [Polynomial.coeff_reverse, Polynomial.revAt_le htd, coeff_X_pow_mul', ite_eq_left (by omega)]
  rw [show p.natDegree.succ - 1 - t = p.natDegree - t by omega,
    show m - (p.natDegree - t) = m - p.natDegree + t by omega]

/-- **Division of an entire series by a monic polynomial.** An entire series `f` is
`r + p * q`, with `q = f.divByMonic p` entire and `r = f.modByMonic p` of degree less than `p`. -/
theorem IsEntire.modByMonic_add_divByMonic (hf : f.IsEntire) (hp : p.Monic) :
    (f.modByMonic p : R⟦X⟧) + p * f.divByMonic p = f := by
  ext m
  rw [map_add, Polynomial.coeff_coe, coeff_modByMonic]
  split_ifs with hm
  · rw [map_sub, sub_add_cancel]
  · rw [zero_add, hf.coeff_coe_mul_divByMonic hp (not_lt.mp hm)]

section Ultrametric

variable [IsUltrametricDist R] [NormOneClass R]

/-- **Uniqueness of entire division.** Over an ultrametric ring with `‖1‖ = 1`, if
`f = r + p * q` with `q` entire and `r` of degree less than the monic polynomial `p`, then `q`
and `r` are the quotient and remainder of `f` on division by `p`. -/
theorem divByMonic_modByMonic_unique (q : R⟦X⟧) (r : Polynomial R) (hp : p.Monic)
    (hq : q.IsEntire) (h : (r : R⟦X⟧) + p * q = f ∧ r.degree < p.degree) :
    f.divByMonic p = q ∧ f.modByMonic p = r := by
  obtain ⟨rfl, hr⟩ := h
  have hf : ((r : R⟦X⟧) + p * q).IsEntire := (isEntire_coe r).add ((isEntire_coe p).mul hq)
  -- `p` is distinguished of its degree at a radius bounding all its coefficients.
  set c := 1 + ∑ i ∈ p.support, ‖p.coeff i‖
  have hc (i : ℕ) : ‖p.coeff i‖ ≤ c := by
    by_cases hi : i ∈ p.support
    · exact (single_le_sum (fun j _ ↦ norm_nonneg (p.coeff j)) hi).trans (le_add_of_nonneg_left
        zero_le_one)
    · rw [Polynomial.notMem_support_iff.mp hi, norm_zero]
      exact add_nonneg zero_le_one (sum_nonneg fun _ _ ↦ norm_nonneg _)
  have : Nontrivial R := NormOneClass.nontrivial
  have hdist := hp.isDistinguished hc
  have hc0 : 0 < c := by positivity
  have hrem (r' : Polynomial R) (hr' : r'.degree < p.degree) :
      ∀ m, p.natDegree ≤ m → coeff m (r' : R⟦X⟧) = 0 := fun m hm ↦ by
    rw [Polynomial.coeff_coe]
    exact Polynomial.coeff_eq_zero_of_degree_lt
      (hr'.trans_le (Polynomial.degree_le_natDegree.trans (by exact_mod_cast hm)))
  have hmul : ∀ x, ‖x * coeff p.natDegree (p : R⟦X⟧)‖ = ‖x‖ * ‖coeff p.natDegree (p : R⟦X⟧)‖ := by
    simp [hp.coeff_natDegree]
  have hdiv := hf.modByMonic_add_divByMonic hp
  obtain ⟨hq', hr'⟩ := TauCeti.PowerSeries.IsDistinguished.eq_and_eq_of_mul_add_eq_mul_add hdist
    hc0 hmul ((hf.divByMonic p).isRestricted c) (hq.isRestricted c)
    (hrem _ (degree_modByMonic_lt _ hp.ne_zero)) (hrem r hr) (by linear_combination hdiv)
  exact ⟨hq', Polynomial.coe_inj.mp hr'⟩

/-- An entire series leaves no remainder on division by a monic polynomial `p` exactly when it
is `p` times an entire series. -/
theorem IsEntire.modByMonic_eq_zero_iff (hf : f.IsEntire) (hp : p.Monic) :
    f.modByMonic p = 0 ↔ ∃ q : R⟦X⟧, q.IsEntire ∧ f = p * q := by
  refine ⟨fun h ↦ ⟨f.divByMonic p, hf.divByMonic p, ?_⟩, fun ⟨q, hq, hfq⟩ ↦ ?_⟩
  · simpa [h] using (hf.modByMonic_add_divByMonic hp).symm
  · have : Nontrivial R := NormOneClass.nontrivial
    refine (divByMonic_modByMonic_unique q 0 hp hq ⟨by simp [hfq], ?_⟩).2
    rw [Polynomial.degree_zero, bot_lt_iff_ne_bot, Ne, Polynomial.degree_eq_bot]
    exact hp.ne_zero

/-- On a polynomial, the quotient of entire division is the quotient of polynomial division. -/
@[simp]
theorem divByMonic_coe (g : Polynomial R) (hp : p.Monic) :
    (g : R⟦X⟧).divByMonic p = (g /ₘ p : Polynomial R) := by
  have : Nontrivial R := NormOneClass.nontrivial
  refine (divByMonic_modByMonic_unique _ (g %ₘ p) hp (isEntire_coe _) ⟨?_,
    Polynomial.degree_modByMonic_lt g hp⟩).1
  rw [← Polynomial.coe_mul, ← Polynomial.coe_add, Polynomial.modByMonic_add_div g p]

/-- On a polynomial, the remainder of entire division is the remainder of polynomial division. -/
@[simp]
theorem modByMonic_coe (g : Polynomial R) (hp : p.Monic) :
    (g : R⟦X⟧).modByMonic p = g %ₘ p := by
  have : Nontrivial R := NormOneClass.nontrivial
  refine (divByMonic_modByMonic_unique (g /ₘ p : Polynomial R) _ hp (isEntire_coe _) ⟨?_,
    Polynomial.degree_modByMonic_lt g hp⟩).2
  rw [← Polynomial.coe_mul, ← Polynomial.coe_add, Polynomial.modByMonic_add_div g p]

end Ultrametric

end NormedCommRing

end PowerSeries
