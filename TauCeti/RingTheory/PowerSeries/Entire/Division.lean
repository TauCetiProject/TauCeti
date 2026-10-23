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
public import TauCeti.RingTheory.PowerSeries.Entire.Eval
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.LinearCombination
import TauCeti.RingTheory.PowerSeries.Inverse
import TauCeti.RingTheory.PowerSeries.Trunc
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
inner sums converge however fast the radius of `f` is tested
(`PowerSeries.norm_coeff_invOfUnit_coe_le`). When `f` is a polynomial, `q` and `r` are the
quotient and remainder of ordinary polynomial division. Over an ultrametric ring with `‖1‖ = 1`,
a monic polynomial is distinguished of its degree at every large radius, so the Weierstrass
division estimate makes `q` and `r` unique among divisions with entire quotient.

This is the division of entire series by polynomials used in the Fredholm theory of compact
operators, whose Fredholm determinants are entire series.

## Main definitions

* `PowerSeries.divByMonic`: the quotient `q` above, given by the explicit coefficient formula.
* `PowerSeries.modByMonic`: the remainder `f - p * q`, truncated to a polynomial of degree less
  than `d`.

## Main results

* `PowerSeries.hasSum_coeff_divByMonic`: for entire `f`, the coefficients of `q` are the sums
  `∑ₖ a_{n+d+k} bₖ`.
* `PowerSeries.IsEntire.divByMonic`: the quotient of an entire series is entire.
* `PowerSeries.IsEntire.modByMonic_add_divByMonic`: the division identity `r + p * q = f`.
* `PowerSeries.IsEntire.add_divByMonic` and `PowerSeries.IsEntire.smul_divByMonic`, with their
  `modByMonic` companions: on entire series, quotient and remainder are additive and
  `R`-linear.
* `PowerSeries.divByMonic_coe` and `PowerSeries.modByMonic_coe`: on polynomials, these are
  `Polynomial.divByMonic` and `Polynomial.modByMonic`.
* `PowerSeries.divByMonic_modByMonic_unique`: over an ultrametric ring with `‖1‖ = 1`, a division
  with entire quotient and remainder of degree less than `d` is this one.
* `PowerSeries.IsEntire.coe_mul_divByMonic_cancel_left`: over an ultrametric ring with
  `‖1‖ = 1`, dividing `p * q` by `p` returns `q` for entire `q`.
* `PowerSeries.IsEntire.evalAt_eq_zero_iff`: the factor theorem; an entire series vanishes at
  `a` exactly when it is `X - a` times an entire series.
* `PowerSeries.IsEntire.exists_eq_X_sub_C_pow_mul`: if the Hasse derivatives of order less than
  `h` of an entire series vanish at `a`, then it is `(X - a)ʰ` times an entire series.
* `PowerSeries.IsEntire.modByMonic_eq_zero_iff`: over an ultrametric ring with `‖1‖ = 1`, the
  remainder vanishes exactly when `p` divides `f` with entire quotient.

## References

* R. F. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. 127 (1997),
  Appendix A3.
-/

public section

namespace PowerSeries

open Filter Finset
open scoped Topology

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

/-- The quotient of `0` is `0`. -/
@[simp]
theorem zero_divByMonic (p : Polynomial R) : (0 : R⟦X⟧).divByMonic p = 0 := by
  ext n
  simp [coeff_divByMonic]

/-- The remainder of `0` is `0`. -/
@[simp]
theorem zero_modByMonic (p : Polynomial R) : (0 : R⟦X⟧).modByMonic p = 0 := by
  simp [modByMonic]

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

/-- On entire series, the quotient is additive. -/
theorem IsEntire.add_divByMonic {g : R⟦X⟧} (hf : f.IsEntire) (hg : g.IsEntire)
    (p : Polynomial R) : (f + g).divByMonic p = f.divByMonic p + g.divByMonic p := by
  ext n
  rw [map_add, coeff_divByMonic]
  simp_rw [map_add, add_mul]
  exact ((hasSum_coeff_divByMonic hf p n).add (hasSum_coeff_divByMonic hg p n)).tsum_eq

/-- On entire series, the remainder is additive. -/
theorem IsEntire.add_modByMonic {g : R⟦X⟧} (hf : f.IsEntire) (hg : g.IsEntire)
    (p : Polynomial R) : (f + g).modByMonic p = f.modByMonic p + g.modByMonic p := by
  rw [modByMonic, modByMonic, modByMonic, hf.add_divByMonic hg, ← map_add]
  congr 1
  ring

/-- On entire series, the quotient commutes with scalar multiplication. -/
theorem IsEntire.smul_divByMonic (hf : f.IsEntire) (a : R) (p : Polynomial R) :
    (a • f).divByMonic p = a • f.divByMonic p := by
  ext n
  rw [coeff_smul, coeff_divByMonic]
  simp_rw [coeff_smul, smul_eq_mul, mul_assoc]
  exact ((hasSum_coeff_divByMonic hf p n).mul_left a).tsum_eq

/-- On entire series, the remainder commutes with scalar multiplication. -/
theorem IsEntire.smul_modByMonic (hf : f.IsEntire) (a : R) (p : Polynomial R) :
    (a • f).modByMonic p = a • f.modByMonic p := by
  rw [modByMonic, modByMonic, hf.smul_divByMonic, ← map_smul, mul_smul_comm, smul_sub]

/-- On a polynomial, entire division is polynomial division: the quotient vanishes past the
degree of the polynomial, so the division identity is one of polynomials. -/
private theorem divByMonic_coe_and_modByMonic_coe (g : Polynomial R) (hp : p.Monic) :
    (g : R⟦X⟧).divByMonic p = (g /ₘ p : Polynomial R) ∧ (g : R⟦X⟧).modByMonic p = g %ₘ p := by
  nontriviality R
  set q := (g : R⟦X⟧).divByMonic p
  have hq : q = (trunc (g.natDegree + 1) q : R⟦X⟧) := by
    ext n
    rw [Polynomial.coeff_coe, coeff_trunc]
    split_ifs with hn
    · rfl
    rw [coeff_divByMonic]
    refine (tsum_congr fun k ↦ ?_).trans tsum_zero
    rw [Polynomial.coeff_coe, Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
  have hdiv : ((g : R⟦X⟧).modByMonic p : R⟦X⟧) + p * q = g :=
    (isEntire_coe g).modByMonic_add_divByMonic hp
  rw [hq, ← Polynomial.coe_mul, ← Polynomial.coe_add, Polynomial.coe_inj] at hdiv
  obtain ⟨h₁, h₂⟩ := Polynomial.div_modByMonic_unique _ _ hp
    ⟨hdiv, degree_modByMonic_lt _ hp.ne_zero⟩
  exact ⟨hq.trans (by rw [h₁]), h₂.symm⟩

/-- On a polynomial, the quotient of entire division is the quotient of polynomial division. -/
@[simp]
theorem divByMonic_coe (g : Polynomial R) (hp : p.Monic) :
    (g : R⟦X⟧).divByMonic p = (g /ₘ p : Polynomial R) :=
  (divByMonic_coe_and_modByMonic_coe g hp).1

/-- On a polynomial, the remainder of entire division is the remainder of polynomial division. -/
@[simp]
theorem modByMonic_coe (g : Polynomial R) (hp : p.Monic) :
    (g : R⟦X⟧).modByMonic p = g %ₘ p :=
  (divByMonic_coe_and_modByMonic_coe g hp).2

/-- A polynomial of degree less than `p` has quotient `0` on division by `p`. -/
theorem divByMonic_coe_of_degree_lt {g : Polynomial R} (hp : p.Monic)
    (hg : g.degree < p.degree) : (g : R⟦X⟧).divByMonic p = 0 := by
  rw [divByMonic_coe g hp, (Polynomial.div_modByMonic_unique 0 g hp ⟨by simp, hg⟩).1,
    Polynomial.coe_zero]

/-- A polynomial of degree less than `p` is its own remainder on division by `p`. -/
theorem modByMonic_coe_of_degree_lt {g : Polynomial R} (hp : p.Monic)
    (hg : g.degree < p.degree) : (g : R⟦X⟧).modByMonic p = g := by
  rw [modByMonic_coe g hp, (Polynomial.div_modByMonic_unique 0 g hp ⟨by simp, hg⟩).2]

/-- **Factor theorem for entire series.** An entire series vanishes at `a` exactly when it is
`X - a` times an entire series. -/
theorem IsEntire.evalAt_eq_zero_iff (hf : f.IsEntire) {a : R} :
    f.evalAt a = 0 ↔ ∃ q : R⟦X⟧, q.IsEntire ∧ f = (X - C a) * q := by
  refine ⟨fun ha ↦ ⟨f.divByMonic (Polynomial.X - Polynomial.C a), hf.divByMonic _, ?_⟩, ?_⟩
  · nontriviality R
    have hp := Polynomial.monic_X_sub_C a
    have hdiv := hf.modByMonic_add_divByMonic hp
    -- the remainder `r` has degree less than `1`, and its value at `a` is `f(a) = 0`
    set r := f.modByMonic (Polynomial.X - Polynomial.C a)
    have hr : r = Polynomial.C (r.coeff 0) := Polynomial.eq_C_of_degree_le_zero <|
      Nat.WithBot.lt_one_iff_le_zero.mp
        ((degree_modByMonic_lt f hp.ne_zero).trans_le (Polynomial.degree_X_sub_C_le a))
    have h0 : r.coeff 0 = 0 := by
      have := congrArg (evalAt · a) hdiv
      rw [(isEntire_coe r).evalAt_add ((isEntire_coe _).mul (hf.divByMonic _)),
        (isEntire_coe _).evalAt_mul (hf.divByMonic _), evalAt_coe, evalAt_coe, hr] at this
      simpa [ha] using this
    rw [hr, h0] at hdiv
    simpa using hdiv.symm
  · rintro ⟨q, hq, rfl⟩
    rw [(isEntire_X.sub (isEntire_C a)).evalAt_mul hq, isEntire_X.evalAt_sub (isEntire_C a)]
    simp

/-- If the Hasse derivatives of order less than `h` of an entire series `f` vanish at `a`, then
`f = (X - a)ʰ g` for an entire series `g`. -/
theorem IsEntire.exists_eq_X_sub_C_pow_mul (hf : f.IsEntire)
    {a : R} {h : ℕ} (hzero : ∀ j < h, (PowerSeries.hasseDeriv j f).evalAt a = 0) :
    ∃ g : R⟦X⟧, g.IsEntire ∧ f = (X - C a) ^ h * g := by
  induction h with
  | zero => exact ⟨f, hf, by simp⟩
  | succ h ih =>
    obtain ⟨g, hg, rfl⟩ := ih fun j hj ↦ hzero j (by omega)
    have hga : g.evalAt a = 0 := by
      simpa [hg.evalAt_hasseDeriv_X_sub_C_pow_mul, hasseDeriv_zero] using hzero h h.lt_succ_self
    obtain ⟨q, hq, rfl⟩ := (hg.evalAt_eq_zero_iff).mp hga
    exact ⟨q, hq, by ring⟩

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
  have : Nontrivial R := NormOneClass.nontrivial
  have hdist := hp.isDistinguished_one_add_sum_norm_coeff
  set c := 1 + ∑ i ∈ p.support, ‖p.coeff i‖
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

/-- Dividing `p * q` by `p`, for entire `q`, gives quotient `q` and remainder `0`. -/
private theorem IsEntire.coe_mul_divByMonic_and_modByMonic {q : R⟦X⟧} (hq : q.IsEntire)
    (hp : p.Monic) :
    ((p : R⟦X⟧) * q).divByMonic p = q ∧ ((p : R⟦X⟧) * q).modByMonic p = 0 := by
  have : Nontrivial R := NormOneClass.nontrivial
  refine divByMonic_modByMonic_unique q 0 hp hq ⟨by simp, ?_⟩
  rw [Polynomial.degree_zero, bot_lt_iff_ne_bot, Ne, Polynomial.degree_eq_bot]
  exact hp.ne_zero

/-- Over an ultrametric ring with `‖1‖ = 1`, dividing `p * q` by the monic polynomial `p`, for
entire `q`, returns `q`. -/
theorem IsEntire.coe_mul_divByMonic_cancel_left {q : R⟦X⟧} (hq : q.IsEntire) (hp : p.Monic) :
    ((p : R⟦X⟧) * q).divByMonic p = q :=
  (hq.coe_mul_divByMonic_and_modByMonic hp).1

/-- Over an ultrametric ring with `‖1‖ = 1`, `p * q` leaves no remainder on division by the
monic polynomial `p`, for entire `q`. -/
theorem IsEntire.coe_mul_modByMonic {q : R⟦X⟧} (hq : q.IsEntire) (hp : p.Monic) :
    ((p : R⟦X⟧) * q).modByMonic p = 0 :=
  (hq.coe_mul_divByMonic_and_modByMonic hp).2

/-- Over an ultrametric ring with `‖1‖ = 1`, an entire series leaves no remainder on division by
a monic polynomial `p` exactly when it is `p` times an entire series. -/
theorem IsEntire.modByMonic_eq_zero_iff (hf : f.IsEntire) (hp : p.Monic) :
    f.modByMonic p = 0 ↔ ∃ q : R⟦X⟧, q.IsEntire ∧ f = p * q := by
  refine ⟨fun h ↦ ⟨f.divByMonic p, hf.divByMonic p, ?_⟩, fun ⟨q, hq, hfq⟩ ↦ ?_⟩
  · simpa [h] using (hf.modByMonic_add_divByMonic hp).symm
  · rw [hfq]
    exact hq.coe_mul_modByMonic hp

end Ultrametric

end NormedCommRing

end PowerSeries
