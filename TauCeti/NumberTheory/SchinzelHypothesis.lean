/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Data.Fin.VecNotation
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum.Prime
import TauCeti.Algebra.Polynomial.MapZMod

/-!
# Bouniakowsky polynomials, Schinzel tuples and Schinzel's Hypothesis (H)

An integer polynomial `f` is a *Bouniakowsky polynomial* if its leading coefficient is positive
and it has no fixed prime divisor: for every prime `p` there is an integer `n` with `p ∤ f(n)`.
A family `F` of integer polynomials is a *Schinzel tuple* if every leading coefficient is positive
and for every prime `p` there is one integer `n` with `p ∤ F i (n)` for all `i`; equivalently, the
product of the `F i` has no fixed prime divisor. These are the obvious necessary conditions for
the polynomials to take prime values simultaneously at infinitely many natural numbers.

Bouniakowsky's conjecture asserts that an irreducible Bouniakowsky polynomial takes prime values at
infinitely many natural numbers, and Schinzel's Hypothesis (H) asserts the same for every finite
Schinzel tuple of irreducible polynomials, simultaneously. Both are stated here as propositions.
They are not proved and are not assumed anywhere.

The local conditions depend only on residues: `p ∣ f(n)` exactly when `f`, reduced modulo `p`,
vanishes at the class of `n` (`Polynomial.eval_map_intCastRingHom_zmod_eq_zero_iff`).

## Main definitions

* `TauCeti.IsBouniakowskyPolynomial f`: positive leading coefficient and no fixed prime divisor.
* `TauCeti.IsSchinzelTuple F`: positive leading coefficients and, for each prime, a common
  argument at which no value is divisible by it.
* `TauCeti.BouniakowskyAdmissible f`, `TauCeti.SchinzelAdmissible F`: the same, with every
  polynomial irreducible.
* `TauCeti.primeArguments F`: the set of natural numbers at which every `F i` takes a positive
  prime value.
* `TauCeti.BouniakowskyConjecture`, `TauCeti.SchinzelHypothesisH`: the two conjectures.

## Main results

* `TauCeti.isBouniakowskyPolynomial_iff_exists_eval_map_ne_zero`,
  `TauCeti.isSchinzelTuple_iff_exists_eval_map_ne_zero`: the local condition in terms of the
  reductions modulo `p`.
* `TauCeti.isBouniakowskyPolynomial_iff_exists_nat_lt`, `TauCeti.isSchinzelTuple_iff_exists_nat_lt`:
  at each prime `p` the local condition is a finite check over the arguments `0, …, p - 1`.
* `TauCeti.BouniakowskyAdmissible.natDegree_pos`: an admissible polynomial is not constant.
* `TauCeti.isSchinzelTuple_iff_prod`: the shared local condition is the local condition for the
  product.
* `TauCeti.schinzelAdmissible_iff_of_unique`: a one-entry tuple is Schinzel-admissible exactly
  when its entry is Bouniakowsky-admissible.
* `TauCeti.SchinzelHypothesisH.bouniakowskyConjecture`: Hypothesis (H) implies Bouniakowsky's
  conjecture.

## References

* A. N. Skorobogatov and E. Sofos, *Schinzel Hypothesis on average and rational points*,
  Invent. Math. 231 (2023), 673–739, §1, pp. 674–675, where a Bouniakowsky polynomial is defined
  by the condition that its reduction modulo `ℓ` is not a multiple of `t ^ ℓ - t`, that is, does
  not vanish identically on `𝔽_ℓ`.
-/

public section

open Polynomial

namespace TauCeti

variable {ι : Type*} {f : ℤ[X]} {F : ι → ℤ[X]}

/-! ### The local condition -/

/-- A common argument avoiding divisibility by `p ≠ 0` in every entry of a family can be taken
among the natural numbers below `p`. -/
theorem exists_nat_lt_forall_not_dvd_eval_iff (F : ι → ℤ[X]) {p : ℕ} (hp : p ≠ 0) :
    (∃ n < p, ∀ i, ¬(p : ℤ) ∣ (F i).eval (n : ℤ)) ↔ ∃ n : ℤ, ∀ i, ¬(p : ℤ) ∣ (F i).eval n := by
  refine ⟨fun ⟨n, _, hn⟩ ↦ ⟨n, hn⟩, fun ⟨n, hn⟩ ↦ ?_⟩
  have hp0 : (0 : ℤ) < p := mod_cast Nat.pos_of_ne_zero hp
  refine ⟨(n % p).toNat, ?_, fun i ↦ ?_⟩
  · have hlt := Int.emod_lt_of_pos n hp0
    omega
  · rw [Int.toNat_of_nonneg (Int.emod_nonneg n hp0.ne'), dvd_eval_emod_iff]
    exact hn i

/-! ### Bouniakowsky polynomials -/

/-- An integer polynomial is a Bouniakowsky polynomial if its leading coefficient is positive and
for every prime `p` some integer value `f(n)` is not divisible by `p`. -/
def IsBouniakowskyPolynomial (f : ℤ[X]) : Prop :=
  0 < f.leadingCoeff ∧ ∀ p : ℕ, p.Prime → ∃ n : ℤ, ¬(p : ℤ) ∣ f.eval n

/-- The defining property of a Bouniakowsky polynomial. -/
theorem isBouniakowskyPolynomial_def (f : ℤ[X]) :
    IsBouniakowskyPolynomial f ↔
      0 < f.leadingCoeff ∧ ∀ p : ℕ, p.Prime → ∃ n : ℤ, ¬(p : ℤ) ∣ f.eval n :=
  Iff.rfl

/-- A polynomial is a Bouniakowsky polynomial exactly when its leading coefficient is positive
and, for every prime `p`, its reduction modulo `p` does not vanish identically on `ZMod p`. -/
theorem isBouniakowskyPolynomial_iff_exists_eval_map_ne_zero :
    IsBouniakowskyPolynomial f ↔ 0 < f.leadingCoeff ∧ ∀ p : ℕ, p.Prime →
      ∃ a : ZMod p, (f.map (Int.castRingHom (ZMod p))).eval a ≠ 0 := by
  refine and_congr_right fun _ ↦ forall₂_congr fun p _ ↦ ⟨?_, ?_⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, fun h ↦ hn ((eval_map_intCastRingHom_zmod_eq_zero_iff f n).1 h)⟩
  · rintro ⟨a, ha⟩
    obtain ⟨n, rfl⟩ := ZMod.intCast_surjective a
    exact ⟨n, fun h ↦ ha ((eval_map_intCastRingHom_zmod_eq_zero_iff f n).2 h)⟩

/-- The local condition of a Bouniakowsky polynomial is a finite check at each prime: an argument
avoiding divisibility by `p` can be taken among the natural numbers below `p`. -/
theorem isBouniakowskyPolynomial_iff_exists_nat_lt :
    IsBouniakowskyPolynomial f ↔ 0 < f.leadingCoeff ∧ ∀ p : ℕ, p.Prime →
      ∃ n < p, ¬(p : ℤ) ∣ f.eval (n : ℤ) := by
  refine and_congr_right fun _ ↦ forall₂_congr fun p hp ↦ ?_
  simpa only [forall_const] using
    (exists_nat_lt_forall_not_dvd_eval_iff (fun _ : Unit ↦ f) hp.ne_zero).symm

/-- An integer polynomial is Bouniakowsky-admissible if it is an irreducible Bouniakowsky
polynomial. -/
def BouniakowskyAdmissible (f : ℤ[X]) : Prop :=
  Irreducible f ∧ IsBouniakowskyPolynomial f

/-- The defining property of a Bouniakowsky-admissible polynomial. -/
theorem bouniakowskyAdmissible_def (f : ℤ[X]) :
    BouniakowskyAdmissible f ↔ Irreducible f ∧ IsBouniakowskyPolynomial f :=
  Iff.rfl

/-- A Bouniakowsky-admissible polynomial is not constant: an irreducible constant is, up to
sign, a prime, which divides every value. -/
theorem BouniakowskyAdmissible.natDegree_pos (hf : BouniakowskyAdmissible f) :
    0 < f.natDegree := by
  by_contra hdeg
  obtain ⟨c, rfl⟩ : ∃ c, f = C c := ⟨_, eq_C_of_natDegree_eq_zero (by omega)⟩
  obtain ⟨hirr, hlead, hloc⟩ := hf
  rw [leadingCoeff_C] at hlead
  have hc1 : c.natAbs ≠ 1 := by
    intro h1
    obtain rfl : c = 1 := by omega
    exact hirr.not_isUnit (isUnit_C.2 isUnit_one)
  obtain ⟨p, hp, hpc⟩ := Nat.exists_prime_and_dvd hc1
  obtain ⟨n, hn⟩ := hloc p hp
  exact hn (by rw [eval_C]; exact Int.natCast_dvd.2 hpc)

/-! ### Schinzel tuples -/

/-- A family of integer polynomials is a Schinzel tuple if every leading coefficient is positive
and for every prime `p` there is one integer `n` such that no value `F i (n)` is divisible by
`p`. -/
def IsSchinzelTuple (F : ι → ℤ[X]) : Prop :=
  (∀ i, 0 < (F i).leadingCoeff) ∧
    ∀ p : ℕ, p.Prime → ∃ n : ℤ, ∀ i, ¬(p : ℤ) ∣ (F i).eval n

/-- The defining property of a Schinzel tuple. -/
theorem isSchinzelTuple_def (F : ι → ℤ[X]) :
    IsSchinzelTuple F ↔ (∀ i, 0 < (F i).leadingCoeff) ∧
      ∀ p : ℕ, p.Prime → ∃ n : ℤ, ∀ i, ¬(p : ℤ) ∣ (F i).eval n :=
  Iff.rfl

/-- A family is a Schinzel tuple exactly when every leading coefficient is positive and, for every
prime `p`, some residue class modulo `p` is a root of none of the reductions modulo `p`. -/
theorem isSchinzelTuple_iff_exists_eval_map_ne_zero :
    IsSchinzelTuple F ↔ (∀ i, 0 < (F i).leadingCoeff) ∧ ∀ p : ℕ, p.Prime →
      ∃ a : ZMod p, ∀ i, ((F i).map (Int.castRingHom (ZMod p))).eval a ≠ 0 := by
  refine and_congr_right fun _ ↦ forall₂_congr fun p _ ↦ ⟨?_, ?_⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, fun i h ↦ hn i ((eval_map_intCastRingHom_zmod_eq_zero_iff (F i) n).1 h)⟩
  · rintro ⟨a, ha⟩
    obtain ⟨n, rfl⟩ := ZMod.intCast_surjective a
    exact ⟨n, fun i h ↦ ha i ((eval_map_intCastRingHom_zmod_eq_zero_iff (F i) n).2 h)⟩

/-- The local condition of a Schinzel tuple is a finite check at each prime: a common argument
avoiding divisibility by `p` can be taken among the natural numbers below `p`. -/
theorem isSchinzelTuple_iff_exists_nat_lt :
    IsSchinzelTuple F ↔ (∀ i, 0 < (F i).leadingCoeff) ∧ ∀ p : ℕ, p.Prime →
      ∃ n < p, ∀ i, ¬(p : ℤ) ∣ (F i).eval (n : ℤ) :=
  and_congr_right fun _ ↦ forall₂_congr fun _ hp ↦
    (exists_nat_lt_forall_not_dvd_eval_iff F hp.ne_zero).symm

/-- **The shared local condition is the local condition for the product.** A finite family is a
Schinzel tuple exactly when every leading coefficient is positive and, for every prime `p`, some
value of the product of the family is not divisible by `p`. -/
theorem isSchinzelTuple_iff_prod [Fintype ι] :
    IsSchinzelTuple F ↔ (∀ i, 0 < (F i).leadingCoeff) ∧
      ∀ p : ℕ, p.Prime → ∃ n : ℤ, ¬(p : ℤ) ∣ (∏ i, F i).eval n := by
  refine and_congr_right fun _ ↦ forall₂_congr fun p hp ↦ exists_congr fun n ↦ ?_
  rw [eval_prod]
  constructor
  · intro h hdvd
    obtain ⟨i, -, hi⟩ := Prime.exists_mem_finset_dvd (Nat.prime_iff_prime_int.1 hp) hdvd
    exact h i hi
  · intro h i hi
    exact h (hi.trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)))

/-- A member of a Schinzel tuple is a Bouniakowsky polynomial. -/
theorem IsSchinzelTuple.isBouniakowskyPolynomial (hF : IsSchinzelTuple F) (i : ι) :
    IsBouniakowskyPolynomial (F i) :=
  ⟨hF.1 i, fun p hp ↦ (hF.2 p hp).imp fun _ hn ↦ hn i⟩

/-- A one-entry family is a Schinzel tuple exactly when its entry is a Bouniakowsky polynomial. -/
theorem isSchinzelTuple_iff_of_unique [Unique ι] :
    IsSchinzelTuple F ↔ IsBouniakowskyPolynomial (F default) := by
  simp only [isSchinzelTuple_def, isBouniakowskyPolynomial_def, Unique.forall_iff]

/-- The empty family is a Schinzel tuple. -/
theorem isSchinzelTuple_of_isEmpty [IsEmpty ι] (F : ι → ℤ[X]) : IsSchinzelTuple F :=
  ⟨isEmptyElim, fun _ _ ↦ ⟨0, isEmptyElim⟩⟩

/-- A family of integer polynomials is Schinzel-admissible if it is a Schinzel tuple of
irreducible polynomials. -/
def SchinzelAdmissible (F : ι → ℤ[X]) : Prop :=
  (∀ i, Irreducible (F i)) ∧ IsSchinzelTuple F

/-- The defining property of a Schinzel-admissible family. -/
theorem schinzelAdmissible_def (F : ι → ℤ[X]) :
    SchinzelAdmissible F ↔ (∀ i, Irreducible (F i)) ∧ IsSchinzelTuple F :=
  Iff.rfl

/-- A member of a Schinzel-admissible family is Bouniakowsky-admissible. -/
theorem SchinzelAdmissible.bouniakowskyAdmissible (hF : SchinzelAdmissible F) (i : ι) :
    BouniakowskyAdmissible (F i) :=
  ⟨hF.1 i, hF.2.isBouniakowskyPolynomial i⟩

/-- A one-entry family is Schinzel-admissible exactly when its entry is
Bouniakowsky-admissible. -/
theorem schinzelAdmissible_iff_of_unique [Unique ι] :
    SchinzelAdmissible F ↔ BouniakowskyAdmissible (F default) := by
  simp only [schinzelAdmissible_def, bouniakowskyAdmissible_def, Unique.forall_iff,
    isSchinzelTuple_iff_of_unique]

/-- The empty family is Schinzel-admissible. -/
theorem schinzelAdmissible_of_isEmpty [IsEmpty ι] (F : ι → ℤ[X]) : SchinzelAdmissible F :=
  ⟨isEmptyElim, isSchinzelTuple_of_isEmpty F⟩

/-! ### Prime values and the conjectures -/

/-- The set of natural numbers `n` at which every polynomial of the family takes a positive prime
value. -/
def primeArguments (F : ι → ℤ[X]) : Set ℕ :=
  {n | ∀ i, 0 < (F i).eval (n : ℤ) ∧ ((F i).eval (n : ℤ)).natAbs.Prime}

/-- Membership in `primeArguments F`. -/
@[simp]
theorem mem_primeArguments {n : ℕ} :
    n ∈ primeArguments F ↔ ∀ i, 0 < (F i).eval (n : ℤ) ∧ ((F i).eval (n : ℤ)).natAbs.Prime :=
  Iff.rfl

/-- For the empty family the condition is vacuous: every natural number is a prime argument. -/
@[simp]
theorem primeArguments_of_isEmpty [IsEmpty ι] (F : ι → ℤ[X]) : primeArguments F = Set.univ := by
  ext n
  simp

/-- **Bouniakowsky's conjecture**: every irreducible Bouniakowsky polynomial takes a positive
prime value at infinitely many natural numbers. This is the statement of the conjecture, not a
theorem. -/
def BouniakowskyConjecture : Prop :=
  ∀ f : ℤ[X], BouniakowskyAdmissible f →
    {n : ℕ | 0 < f.eval (n : ℤ) ∧ (f.eval (n : ℤ)).natAbs.Prime}.Infinite

/-- The statement of Bouniakowsky's conjecture. -/
theorem bouniakowskyConjecture_def :
    BouniakowskyConjecture ↔ ∀ f : ℤ[X], BouniakowskyAdmissible f →
      {n : ℕ | 0 < f.eval (n : ℤ) ∧ (f.eval (n : ℤ)).natAbs.Prime}.Infinite :=
  Iff.rfl

/-- **Schinzel's Hypothesis (H)**: for every finite Schinzel tuple of irreducible polynomials
there are infinitely many natural numbers at which all of them take positive prime values. This is
the statement of the hypothesis, not a theorem. -/
def SchinzelHypothesisH : Prop :=
  ∀ (k : ℕ) (F : Fin k → ℤ[X]), SchinzelAdmissible F → (primeArguments F).Infinite

/-- The statement of Schinzel's Hypothesis (H). -/
theorem schinzelHypothesisH_def :
    SchinzelHypothesisH ↔
      ∀ (k : ℕ) (F : Fin k → ℤ[X]), SchinzelAdmissible F → (primeArguments F).Infinite :=
  Iff.rfl

/-- Schinzel's Hypothesis (H) implies Bouniakowsky's conjecture: apply it to the one-entry
tuple. -/
theorem SchinzelHypothesisH.bouniakowskyConjecture (h : SchinzelHypothesisH) :
    BouniakowskyConjecture := by
  intro f hf
  have h1 := h 1 (fun _ ↦ f) (schinzelAdmissible_iff_of_unique.2 hf)
  refine h1.mono fun n hn ↦ ?_
  exact hn 0

/-! ### Examples -/

/-- `X + 1` is Bouniakowsky-admissible: it is irreducible and its value at `0` is `1`. -/
example : BouniakowskyAdmissible (X + C 1 : ℤ[X]) := by
  refine ⟨(monic_X_add_C 1).irreducible_of_degree_eq_one (degree_X_add_C 1), ?_,
    fun p hp ↦ ⟨0, fun h ↦ ?_⟩⟩
  · rw [leadingCoeff_X_add_C]
    exact one_pos
  · have h1 : (p : ℤ) ∣ ((1 : ℕ) : ℤ) := by simpa using h
    exact hp.ne_one (Nat.dvd_one.1 (Int.natCast_dvd_natCast.1 h1))

/-- Every value of `X ^ 2 + X + 2` is even, so it is not a Bouniakowsky polynomial; in
particular it is not Bouniakowsky-admissible. -/
example : ¬IsBouniakowskyPolynomial (X ^ 2 + X + C 2 : ℤ[X]) := by
  rintro ⟨-, h⟩
  obtain ⟨n, hn⟩ := h 2 Nat.prime_two
  obtain ⟨k, hk⟩ := Int.even_mul_succ_self n
  refine hn ⟨k + 1, ?_⟩
  simp only [eval_add, eval_pow, eval_X, eval_C, Nat.cast_ofNat]
  linear_combination hk

/-- `X` and `X + 1` are each Bouniakowsky-admissible, but the pair is not a Schinzel tuple: one
of `n`, `n + 1` is always even. Admissibility of each entry is not enough. -/
example : BouniakowskyAdmissible (X : ℤ[X]) ∧ BouniakowskyAdmissible (X + C 1 : ℤ[X]) ∧
    ¬SchinzelAdmissible ![(X : ℤ[X]), X + C 1] := by
  have h1 {p : ℕ} (hp : p.Prime) : ¬(p : ℤ) ∣ 1 := fun h ↦
    hp.ne_one (Nat.dvd_one.1 (Int.natCast_dvd_natCast.1 (by simpa using h)))
  refine ⟨⟨irreducible_X, by simp, fun p hp ↦ ⟨1, by simpa using h1 hp⟩⟩,
    ⟨(monic_X_add_C 1).irreducible_of_degree_eq_one (degree_X_add_C 1), ?_,
      fun p hp ↦ ⟨0, by simpa using h1 hp⟩⟩, ?_⟩
  · rw [leadingCoeff_X_add_C]
    exact one_pos
  · rintro ⟨-, -, h⟩
    obtain ⟨n, hn⟩ := h 2 Nat.prime_two
    have h0 := hn 0
    have h1 := hn 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, eval_X, eval_add, eval_C,
      Nat.cast_ofNat] at h0 h1
    omega

/-- The empty tuple is Schinzel-admissible, and every natural number is a prime argument for
it. -/
example : SchinzelAdmissible (![] : Fin 0 → ℤ[X]) ∧
    primeArguments (![] : Fin 0 → ℤ[X]) = Set.univ :=
  ⟨schinzelAdmissible_of_isEmpty _, primeArguments_of_isEmpty _⟩

/-- `X * (X + 2)` is a Bouniakowsky polynomial (its values at `1` and `2` are `3` and `8`), but
it is reducible, so it is not Bouniakowsky-admissible. -/
example : IsBouniakowskyPolynomial (X * (X + C 2) : ℤ[X]) ∧
    ¬BouniakowskyAdmissible (X * (X + C 2) : ℤ[X]) := by
  refine ⟨⟨?_, fun p hp ↦ ?_⟩, fun h ↦ ?_⟩
  · rw [leadingCoeff_mul, leadingCoeff_X, leadingCoeff_X_add_C, one_mul]
    exact one_pos
  · rcases eq_or_ne p 3 with rfl | hp3
    · exact ⟨2, by norm_num⟩
    · refine ⟨1, fun h ↦ hp3 ?_⟩
      have h3 : (p : ℤ) ∣ ((3 : ℕ) : ℤ) := by
        simpa only [eval_mul, eval_X, eval_add, eval_C, one_mul, Nat.cast_ofNat,
          show (1 : ℤ) + 2 = 3 by norm_num] using h
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (Int.natCast_dvd_natCast.1 h3)
  · rcases h.1.isUnit_or_isUnit rfl with hX | hX2
    · exact not_isUnit_X hX
    · have hdeg := degree_eq_zero_of_isUnit hX2
      rw [degree_X_add_C] at hdeg
      exact one_ne_zero hdeg

end TauCeti
