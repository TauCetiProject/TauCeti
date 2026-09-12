/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.SymmDiff
public import Mathlib.Data.Nat.Factorization.Basic

/-!
# Exact divisors of a natural number

`Q` is an **exact divisor** of `N` when `Q ∣ N` and `Q` is coprime to the complementary divisor
`N / Q`; equivalently, `N = Q · M` with `Q` and `M` sharing no prime. Such a `Q` collects the
full power of each prime it contains, so the exact divisors of `N` are exactly the products of
the maximal prime powers `p ^ (N.factorization p)`, and they form a Boolean algebra under the
subsets of `N.primeFactors`. The notion is also called a *unitary* or *Hall* divisor.

The classical notation is `Q ‖ N`, which cannot be used here: `‖ ‖` is norm notation, and in the
same corner of the library `p ^ r ‖ n` means exact `p`-adic divisibility — that `r` is the full
exponent of `p`, a statement about the pair `(p, r)` rather than about the single number `p ^ r`.
The notation introduced instead is `Q ∥ N`, with the parallel bars `∥` in place of the double
vertical line `‖`; it is scoped, so it never competes with the `∥` of `AffineSubspace.Parallel`.

## Main definitions

* `TauCeti.Nat.IsExactDivisor`: the predicate itself.
* `TauCeti.Nat.ExactDivisor`: the exact divisors of a fixed `N`, bundled as a commutative group
  whose multiplication is symmetric difference.

## Notation

* `Q ∥ N` for `TauCeti.Nat.IsExactDivisor Q N`, in the `TauCeti.ExactDivisor` scope.

## Main results

* `TauCeti.Nat.isExactDivisor_iff`: the predicate unfolded to its two conditions.
* `TauCeti.Nat.IsExactDivisor.div`: for `N ≠ 0` the complementary divisor `N / Q` is exact too.
* `TauCeti.Nat.IsExactDivisor.ne_zero`: an exact divisor is nonzero. There is no exact divisor
  `0`, because `Nat.Coprime 0 0` is false.
* `TauCeti.Nat.isExactDivisor_one`, `TauCeti.Nat.isExactDivisor_self`: `1` and (for `N ≠ 0`) `N`
  itself.
* `TauCeti.Nat.IsExactDivisor.mul`: coprime exact divisors multiply to an exact divisor, so the
  exact divisors of `N` are closed under coprime products.
* `TauCeti.Nat.isExactDivisor_iff_factorization`: exactness read on the factorization — at every
  prime the exponent of `Q` is either `0` or the full exponent of `N`.
* `TauCeti.Nat.IsExactDivisor.gcd`, `TauCeti.Nat.IsExactDivisor.div_gcd`,
  `TauCeti.Nat.IsExactDivisor.coprime_div_gcd`: the Boolean-algebra structure, in the form the
  Atkin–Lehner group law needs — `gcd Q R` and `Q / gcd Q R` are again exact divisors, and the
  second is coprime to `R`.
* `TauCeti.Nat.IsExactDivisor.mul_div_gcd_sq`: `Q * R / gcd (Q, R) ^ 2` — the symmetric
  difference of `Q` and `R` — is an exact divisor too.
* `TauCeti.Nat.ExactDivisor.val_mul`: multiplication in the bundled group has underlying value
  `Q * R / gcd (Q, R) ^ 2`.
-/

public section

open scoped symmDiff

namespace TauCeti

namespace Nat

variable {N Q R : ℕ}

/-- `Q` is an **exact divisor** of `N`: it divides `N` and is coprime to the complementary
divisor `N / Q`. Written `Q ‖ N` in the literature and `Q ∥ N` here; see the module docstring for
the change of bars. -/
structure IsExactDivisor (Q N : ℕ) : Prop where
  /-- An exact divisor is a divisor. -/
  dvd : Q ∣ N
  /-- An exact divisor is coprime to its complementary divisor. -/
  coprime : Nat.Coprime Q (N / Q)

@[inherit_doc TauCeti.Nat.IsExactDivisor]
scoped[TauCeti.ExactDivisor] infix:50 " ∥ " => TauCeti.Nat.IsExactDivisor

/-- **An exact divisor is nonzero.** `0` is only a divisor of `0`, whose complementary divisor is
again `0`, and `Nat.Coprime 0 0` is false. -/
theorem IsExactDivisor.ne_zero (h : IsExactDivisor Q N) : Q ≠ 0 := by
  rintro rfl
  simpa using h.coprime

/-- An exact divisor is positive. -/
theorem IsExactDivisor.pos (h : IsExactDivisor Q N) : 0 < Q :=
  Nat.pos_of_ne_zero h.ne_zero

/-- The defining conditions of an exact divisor, as a rewrite rule. -/
@[simp]
theorem isExactDivisor_iff : IsExactDivisor Q N ↔ Q ∣ N ∧ Nat.Coprime Q (N / Q) :=
  ⟨fun h ↦ ⟨h.dvd, h.coprime⟩, fun h ↦ ⟨h.1, h.2⟩⟩

/-- **The complementary divisor is exact.** For `N ≠ 0`, `N / Q` is again an exact divisor of `N`,
whose own complement is `Q` again (`Nat.div_div_self`). At `N = 0` this fails: `1` is an exact
divisor of `0`, but `0 / 1 = 0` is not. -/
theorem IsExactDivisor.div (h : IsExactDivisor Q N) (hN : N ≠ 0) : IsExactDivisor (N / Q) N :=
  ⟨Nat.div_dvd_of_dvd h.dvd, by rw [Nat.div_div_self h.dvd hN]; exact h.coprime.symm⟩

/-- `1` is an exact divisor of every `N`. -/
theorem isExactDivisor_one : IsExactDivisor 1 N :=
  ⟨one_dvd N, Nat.coprime_one_left _⟩

/-- A nonzero `N` is an exact divisor of itself: the complementary divisor is `1`. This is the
case of the Fricke operator inside the Atkin–Lehner family. -/
theorem isExactDivisor_self (hN : N ≠ 0) : IsExactDivisor N N :=
  ⟨dvd_rfl, by rw [Nat.div_self (Nat.pos_of_ne_zero hN)]; exact Nat.coprime_one_right _⟩

/-- **Coprime exact divisors multiply.** The exact divisors of `N` are therefore closed under
coprime products, which is how the family generated by the maximal prime powers of `N` is built
up. -/
theorem IsExactDivisor.mul (hQ : IsExactDivisor Q N) (hR : IsExactDivisor R N)
    (hQR : Nat.Coprime Q R) : IsExactDivisor (Q * R) N := by
  have hdvd : Q * R ∣ N := Nat.Coprime.mul_dvd_of_dvd_of_dvd hQR hQ.dvd hR.dvd
  obtain ⟨M, hM⟩ := hdvd
  have hQ0 : 0 < Q := hQ.pos
  have hR0 : 0 < R := hR.pos
  have e1 : N / (Q * R) = M := by
    rw [hM]; exact Nat.mul_div_cancel_left _ (Nat.mul_pos hQ0 hR0)
  have e2 : N / Q = R * M := by
    rw [hM, mul_assoc]; exact Nat.mul_div_cancel_left _ hQ0
  have e3 : N / R = Q * M := by
    rw [hM, mul_comm Q R, mul_assoc]; exact Nat.mul_div_cancel_left _ hR0
  refine ⟨⟨M, hM⟩, ?_⟩
  rw [e1]
  refine Nat.coprime_mul_iff_left.mpr ⟨?_, ?_⟩
  · exact Nat.Coprime.coprime_dvd_right (e2 ▸ Dvd.intro_left R rfl) hQ.coprime
  · exact Nat.Coprime.coprime_dvd_right (e3 ▸ Dvd.intro_left Q rfl) hR.coprime

/-! ### The Boolean-algebra structure -/

/-- **The only exact divisor of `0` is `1`.** The complementary divisor of `Q` in `0` is `0`
again, and `Nat.Coprime Q 0` says `Q = 1`. This is what lets the closure properties below carry
no `N ≠ 0` hypothesis. -/
theorem isExactDivisor_zero_iff : IsExactDivisor Q 0 ↔ Q = 1 :=
  ⟨fun h ↦ by simpa using h.coprime, fun h ↦ h ▸ isExactDivisor_one⟩

/-- **Exactness, read on the factorization.** For `N ≠ 0`, a divisor `Q` of `N` is exact exactly
when at every prime its exponent is either `0` or the full exponent of `N`. In this form the
closure properties below become statements about the exponents of `gcd` and of a quotient, namely
about `min` and truncated subtraction. -/
theorem isExactDivisor_iff_factorization (hN : N ≠ 0) :
    IsExactDivisor Q N ↔
      Q ∣ N ∧ ∀ p, Q.factorization p = 0 ∨ Q.factorization p = N.factorization p := by
  constructor
  · intro h
    obtain ⟨m, hm⟩ := h.dvd
    have hQ0 : Q ≠ 0 := h.ne_zero
    have hm0 : m ≠ 0 := by rintro rfl; exact hN (by simpa using hm)
    have hdiv : N / Q = m := by rw [hm]; exact Nat.mul_div_cancel_left _ h.pos
    have hcop : Nat.Coprime Q m := hdiv ▸ h.coprime
    have hfac : N.factorization = Q.factorization + m.factorization := by
      rw [hm]; exact Nat.factorization_mul hQ0 hm0
    refine ⟨h.dvd, fun p ↦ ?_⟩
    rcases eq_or_ne (Q.factorization p) 0 with h0 | h0
    · exact Or.inl h0
    refine Or.inr ?_
    have hp : p ∈ Q.primeFactors := by
      rw [← Nat.support_factorization]; exact Finsupp.mem_support_iff.mpr h0
    have hpm : p ∉ m.primeFactors := Finset.disjoint_left.mp hcop.disjoint_primeFactors hp
    rw [← Nat.support_factorization] at hpm
    rw [hfac, Finsupp.add_apply, Finsupp.notMem_support_iff.mp hpm, add_zero]
  · rintro ⟨hQN, hf⟩
    have hQ0 : Q ≠ 0 := by rintro rfl; exact hN (zero_dvd_iff.mp hQN)
    obtain ⟨m, hm⟩ := hQN
    have hm0 : m ≠ 0 := by rintro rfl; exact hN (by simpa using hm)
    have hdiv : N / Q = m := by
      rw [hm]; exact Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hQ0)
    have hfac : ∀ p, N.factorization p = Q.factorization p + m.factorization p := fun p ↦ by
      rw [hm, Nat.factorization_mul hQ0 hm0, Finsupp.add_apply]
    refine ⟨⟨m, hm⟩, ?_⟩
    rw [hdiv, ← Nat.disjoint_primeFactors hQ0 hm0, Finset.disjoint_left]
    intro p hpQ hpm
    rw [← Nat.support_factorization] at hpQ hpm
    have h1 := Finsupp.mem_support_iff.mp hpQ
    have h2 := Finsupp.mem_support_iff.mp hpm
    have h3 := hfac p
    rcases hf p with h0 | h0
    · exact h1 h0
    · omega

/-- **Exact divisors are closed under `gcd`.** At each prime the exponent of `gcd Q R` is the
minimum of two exponents each of which is `0` or the full exponent of `N`. -/
theorem IsExactDivisor.gcd (hQ : IsExactDivisor Q N) (hR : IsExactDivisor R N) :
    IsExactDivisor (Nat.gcd Q R) N := by
  have hQ0 : Q ≠ 0 := hQ.ne_zero
  have hR0 : R ≠ 0 := hR.ne_zero
  rcases eq_or_ne N 0 with rfl | hN
  · rw [isExactDivisor_zero_iff] at hQ hR ⊢
    rw [hQ, hR, Nat.gcd_self]
  rw [isExactDivisor_iff_factorization hN] at hQ hR ⊢
  refine ⟨(Nat.gcd_dvd_left Q R).trans hQ.1, fun p ↦ ?_⟩
  rw [Nat.factorization_gcd hQ0 hR0, Finsupp.inf_apply]
  rcases hQ.2 p with h1 | h1 <;> rcases hR.2 p with h2 | h2 <;> omega

/-- **The quotient of an exact divisor by a `gcd` with another one is exact.** At each prime the
exponent of `Q / gcd Q R` is `0` unless `Q` carries the full exponent of `N` there and `R` carries
none, in which case it is again that full exponent. -/
theorem IsExactDivisor.div_gcd (hQ : IsExactDivisor Q N) (hR : IsExactDivisor R N) :
    IsExactDivisor (Q / Nat.gcd Q R) N := by
  have hQ0 : Q ≠ 0 := hQ.ne_zero
  have hR0 : R ≠ 0 := hR.ne_zero
  rcases eq_or_ne N 0 with rfl | hN
  · rw [isExactDivisor_zero_iff] at hQ hR ⊢
    rw [hQ, hR, Nat.gcd_self, Nat.div_self Nat.one_pos]
  rw [isExactDivisor_iff_factorization hN] at hQ hR ⊢
  refine ⟨(Nat.div_dvd_of_dvd (Nat.gcd_dvd_left Q R)).trans hQ.1, fun p ↦ ?_⟩
  rw [Nat.factorization_div (Nat.gcd_dvd_left Q R), Finsupp.tsub_apply,
    Nat.factorization_gcd hQ0 hR0, Finsupp.inf_apply]
  rcases hQ.2 p with h1 | h1 <;> rcases hR.2 p with h2 | h2 <;> omega

/-- **`Q / gcd Q R` is coprime to `R`.** A prime dividing the quotient carries the full exponent
of `N` in `Q` and none of it in `R`; this is the step where the exactness of *both* divisors is
used, and it fails for divisors in general (`Q = 4`, `R = 2`). -/
theorem IsExactDivisor.coprime_div_gcd (hQ : IsExactDivisor Q N) (hR : IsExactDivisor R N) :
    Nat.Coprime (Q / Nat.gcd Q R) R := by
  have hQ0 : Q ≠ 0 := hQ.ne_zero
  have hR0 : R ≠ 0 := hR.ne_zero
  have hg0 : 0 < Nat.gcd Q R := Nat.gcd_pos_of_pos_left R hQ.pos
  have hq0 : Q / Nat.gcd Q R ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd hQ.pos (Nat.gcd_dvd_left Q R)) hg0).ne'
  rcases eq_or_ne N 0 with rfl | hN
  · rw [isExactDivisor_zero_iff] at hQ hR
    rw [hQ, hR, Nat.gcd_self, Nat.div_self Nat.one_pos]
    exact Nat.coprime_one_left 1
  rw [isExactDivisor_iff_factorization hN] at hQ hR
  rw [← Nat.disjoint_primeFactors hq0 hR0, Finset.disjoint_left]
  intro p hpq hpR
  rw [← Nat.support_factorization] at hpq hpR
  have h1 := Finsupp.mem_support_iff.mp hpq
  have h2 := Finsupp.mem_support_iff.mp hpR
  rw [Nat.factorization_div (Nat.gcd_dvd_left Q R), Finsupp.tsub_apply,
    Nat.factorization_gcd hQ0 hR0, Finsupp.inf_apply] at h1
  rcases hQ.2 p with hq | hq <;> rcases hR.2 p with hr | hr <;> omega

/-- **The symmetric difference of two exact divisors is exact.** `Q * R / gcd (Q, R) ^ 2` is the
product of the coprime exact divisors `Q / gcd (Q, R)` and `R / gcd (Q, R)`; under the
identification of exact divisors with subsets of `N.primeFactors` it is the symmetric difference,
which is why it is the composition law of the Atkin–Lehner family. -/
theorem IsExactDivisor.mul_div_gcd_sq (hQ : IsExactDivisor Q N) (hR : IsExactDivisor R N) :
    IsExactDivisor (Q * R / Nat.gcd Q R ^ 2) N := by
  have hcop : Nat.Coprime (Q / Nat.gcd Q R) (R / Nat.gcd Q R) :=
    (hQ.coprime_div_gcd hR).coprime_dvd_right (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right Q R))
  have hRdiv : IsExactDivisor (R / Nat.gcd Q R) N := by
    rw [Nat.gcd_comm]; exact hR.div_gcd hQ
  rw [sq, ← Nat.div_mul_div_comm (Nat.gcd_dvd_left Q R) (Nat.gcd_dvd_right Q R)]
  exact (hQ.div_gcd hR).mul hRdiv hcop

/-! ### The exact-divisor group -/

/-- **The exact divisors of `N`, bundled as a group.** Multiplication is symmetric difference:
the value of `Q * R` is `Q R / gcd(Q, R)²`. Every element is its own inverse, and the identity is
the exact divisor `1`. -/
structure ExactDivisor (N : ℕ) where
  /-- The underlying natural-number divisor. -/
  val : ℕ
  /-- The underlying value is an exact divisor of `N`. -/
  property : IsExactDivisor val N

namespace ExactDivisor

/-- Two exact divisors are equal when their underlying natural numbers are equal. -/
@[ext]
theorem ext {Q R : ExactDivisor N} (h : Q.val = R.val) : Q = R := by
  cases Q
  cases R
  simp_all

instance : CoeOut (ExactDivisor N) ℕ := ⟨ExactDivisor.val⟩

instance : One (ExactDivisor N) := ⟨⟨1, isExactDivisor_one⟩⟩

/-- Multiplication of exact divisors is symmetric difference, with underlying value
`Q * R / gcd(Q, R) ^ 2`. -/
instance : Mul (ExactDivisor N) where
  mul Q R := ⟨Q.val * R.val / Nat.gcd Q.val R.val ^ 2, Q.property.mul_div_gcd_sq R.property⟩

/-- Inversion is the identity because every exact divisor is self-inverse under symmetric
difference. -/
instance : Inv (ExactDivisor N) := ⟨id⟩

/-- The identity exact divisor has underlying value `1`. -/
@[simp]
theorem val_one : (1 : ExactDivisor N).val = 1 := rfl

/-- **Multiplication of exact divisors is symmetric difference:** its underlying value is
`Q R / gcd(Q, R)²`. -/
@[simp]
theorem val_mul (Q R : ExactDivisor N) :
    (Q * R).val = Q.val * R.val / Nat.gcd Q.val R.val ^ 2 := rfl

/-- Every exact divisor is its own inverse. -/
@[simp]
theorem val_inv (Q : ExactDivisor N) : Q⁻¹.val = Q.val := rfl

/-- An exact divisor of `N` is determined by the set of primes dividing it. -/
theorem primeFactors_injective :
    Function.Injective (fun Q : ExactDivisor N ↦ Q.val.primeFactors) := by
  intro Q R hQR
  apply ext
  rcases eq_or_ne N 0 with rfl | hN
  · rw [isExactDivisor_zero_iff.mp Q.property, isExactDivisor_zero_iff.mp R.property]
  apply Nat.eq_of_factorization_eq Q.property.ne_zero R.property.ne_zero
  have hQ := (isExactDivisor_iff_factorization hN).mp Q.property
  have hR := (isExactDivisor_iff_factorization hN).mp R.property
  intro p
  have hs : Q.val.factorization.support = R.val.factorization.support := by
    simpa only [Nat.support_factorization] using hQR
  have hp : (Q.val.factorization p ≠ 0) = (R.val.factorization p ≠ 0) := by
    simpa only [Finsupp.mem_support_iff] using congrArg (p ∈ ·) hs
  by_cases hpN : N.factorization p = 0
  · rcases hQ.2 p with hQp | hQp <;> rcases hR.2 p with hRp | hRp <;>
      simp [hQp, hRp, hpN]
  rcases hQ.2 p with hQp | hQp <;> rcases hR.2 p with hRp | hRp <;>
    simp [hQp, hRp, hpN] at hp ⊢

/-- Prime factors turn exact-divisor multiplication into symmetric difference. -/
theorem primeFactors_mul (Q R : ExactDivisor N) :
    (Q * R).val.primeFactors = Q.val.primeFactors ∆ R.val.primeFactors := by
  rw [val_mul]
  ext p
  rcases eq_or_ne N 0 with rfl | hN
  · have hQ := isExactDivisor_zero_iff.mp Q.property
    have hR := isExactDivisor_zero_iff.mp R.property
    simp [hQ, hR]
  have hQ0 := Q.property.ne_zero
  have hR0 := R.property.ne_zero
  have hQg0 : Q.val / Nat.gcd Q.val R.val ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd Q.property.pos (Nat.gcd_dvd_left Q.val R.val))
      (Nat.gcd_pos_of_pos_left R.val Q.property.pos)).ne'
  have hRg0 : R.val / Nat.gcd Q.val R.val ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd R.property.pos (Nat.gcd_dvd_right Q.val R.val))
      (Nat.gcd_pos_of_pos_left R.val Q.property.pos)).ne'
  rw [← Nat.support_factorization, ← Nat.support_factorization,
    ← Nat.support_factorization, Finset.mem_symmDiff, Finsupp.mem_support_iff,
    Finsupp.mem_support_iff, Finsupp.mem_support_iff]
  rw [sq, ← Nat.div_mul_div_comm (Nat.gcd_dvd_left Q.val R.val)
      (Nat.gcd_dvd_right Q.val R.val), Nat.factorization_mul hQg0 hRg0, Finsupp.add_apply,
    Nat.factorization_div (Nat.gcd_dvd_left Q.val R.val), Finsupp.tsub_apply,
    Nat.factorization_div (Nat.gcd_dvd_right Q.val R.val), Finsupp.tsub_apply,
    Nat.factorization_gcd hQ0 hR0, Finsupp.inf_apply]
  have hQ := (isExactDivisor_iff_factorization hN).mp Q.property
  have hR := (isExactDivisor_iff_factorization hN).mp R.property
  rcases hQ.2 p with hQp | hQp <;> rcases hR.2 p with hRp | hRp <;>
    simp only [hQp, hRp] <;> omega

/-- Exact divisors form a Boolean commutative group under symmetric-difference multiplication;
the identity is `1` and every element is its own inverse. -/
instance : CommGroup (ExactDivisor N) where
  one := 1
  mul := (· * ·)
  inv := id
  mul_assoc Q R S := primeFactors_injective <| by
    dsimp only
    rw [primeFactors_mul, primeFactors_mul, primeFactors_mul, primeFactors_mul, symmDiff_assoc]
  one_mul Q := primeFactors_injective <| by
    dsimp only
    rw [primeFactors_mul, val_one]
    simp
  mul_one Q := primeFactors_injective <| by
    dsimp only
    rw [primeFactors_mul, val_one]
    simp
  inv_mul_cancel Q := primeFactors_injective <| by
    dsimp only [id]
    rw [primeFactors_mul, val_one]
    simp
  mul_comm Q R := primeFactors_injective <| by
    dsimp only
    rw [primeFactors_mul, primeFactors_mul, symmDiff_comm]

end ExactDivisor

end Nat

end TauCeti
