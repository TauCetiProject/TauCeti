/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.SAGBI.Completion

/-!
# The Robbiano–Sweedler infinite SAGBI completion counterexample

This file constructs the classic counterexample of Robbiano and Sweedler showing that a finitely
generated subalgebra of a polynomial ring in finitely many variables need not admit a finite SAGBI
basis, and that certified SAGBI completion can run forever without terminating.

Over every nontrivial commutative ring without zero divisors, the three-generator subalgebra
`R[X 0 + X 1, X 0 * X 1, X 0 * X 1 ^ 2]` of `MvPolynomial (Fin 2) R` is finitely generated, yet its
monoid of leading exponents for the lexicographic order is not finitely generated. Over a field,
its `lex`-initial algebra is therefore not finitely generated, no finite subset is a `lex`-SAGBI
basis, and no finite stage of `MonomialOrder.sagbiCompletionFamily` is a `lex`-SAGBI basis.

The second part of the file constructs the explicit infinite one-relation-at-a-time toric-binomial
subduction chain `TauCeti.robbianoSweedlerStage`: over a nontrivial commutative ring, the toric
binomial `TauCeti.robbianoSweedlerBinomial R n` at stage `n` subducts with zero expression and
irreducible remainder `X 0 * X 1 ^ (n + 3)`, and over a field adjoining its monic normalization
strictly enlarges the leading-term subalgebra at every step.

## Main definitions and results

* `TauCeti.robbianoSweedlerGen` and `TauCeti.robbianoSweedlerSubalgebra`: the three generators
  `X 0 + X 1`, `X 0 * X 1`, `X 0 * X 1 ^ 2` and the subalgebra they generate in
  `MvPolynomial (Fin 2) R`.
* `TauCeti.fg_robbianoSweedlerSubalgebra`, `TauCeti.not_fg_leadingExponents_robbianoSweedler`,
  `TauCeti.not_fg_initialAlgebra_robbianoSweedler`, and
  `TauCeti.not_isSAGBIBasis_finset_robbianoSweedler`: the subalgebra is finitely generated, while
  its `lex`-leading exponent monoid (over a nontrivial domain) and `lex`-initial algebra (over a
  field) are not, so over a field it has no finite `lex`-SAGBI basis.
* `TauCeti.robbianoSweedlerStage`, `TauCeti.robbianoSweedlerBinomial`,
  `TauCeti.isSubduction_robbianoSweedlerStage`, and
  `TauCeti.adjoin_leadingTerm_robbianoSweedlerStage_lt`: explicit infinite sequence of nonzero
  toric-binomial subduction-remainder steps on `TauCeti.robbianoSweedlerSubalgebra`.
* `TauCeti.not_isSAGBIBasis_sagbiCompletionFamily_robbianoSweedler`: over a field, no finite stage
  of batch SAGBI completion starting from `TauCeti.robbianoSweedlerGen k` is a `lex`-SAGBI basis.

## References

* L. Robbiano, M. Sweedler, *Subalgebra bases*, in *Commutative Algebra (Salvador, 1988)*,
  Lecture Notes in Mathematics 1430, Springer, 1990, 61–87, Example 1.20 and Example 4.11.
* D. Kapur, K. Madlener, *A completion procedure for computing a canonical basis for a
  k-subalgebra*, in *Computers and Mathematics*, Springer, 1989, 1–11.
* B. Sturmfels, *Gröbner Bases and Convex Polytopes*, University Lecture Series 8, AMS, 1996,
  Chapter 11.
-/

public section

open MvPolynomial MonomialOrder

namespace TauCeti

section RobbianoSweedler

/-- The three generators `X 0 + X 1`, `X 0 * X 1`, `X 0 * X 1 ^ 2` of the Robbiano–Sweedler
subalgebra of `MvPolynomial (Fin 2) R`. -/
noncomputable def robbianoSweedlerGen (R : Type*) [CommSemiring R] :
    Fin 3 → MvPolynomial (Fin 2) R :=
  ![X 0 + X 1, X 0 * X 1, X 0 * X 1 ^ 2]

/-- The `0`-th Robbiano–Sweedler generator is `X 0 + X 1`. -/
@[simp]
theorem robbianoSweedlerGen_zero (R : Type*) [CommSemiring R] :
    robbianoSweedlerGen R 0 = X 0 + X 1 :=
  (rfl)

/-- The `1`-st Robbiano–Sweedler generator is `X 0 * X 1`. -/
@[simp]
theorem robbianoSweedlerGen_one (R : Type*) [CommSemiring R] :
    robbianoSweedlerGen R 1 = X 0 * X 1 :=
  (rfl)

/-- The `2`-nd Robbiano–Sweedler generator is `X 0 * X 1 ^ 2`. -/
@[simp]
theorem robbianoSweedlerGen_two (R : Type*) [CommSemiring R] :
    robbianoSweedlerGen R 2 = X 0 * X 1 ^ 2 :=
  (rfl)

/-- The Robbiano–Sweedler subalgebra `R[X 0 + X 1, X 0 * X 1, X 0 * X 1 ^ 2]` of
`MvPolynomial (Fin 2) R`. It is finitely generated as an `R`-algebra
(`TauCeti.fg_robbianoSweedlerSubalgebra`); over a nontrivial commutative ring without zero
divisors, its `lex`-leading exponent monoid is not finitely generated
(`TauCeti.not_fg_leadingExponents_robbianoSweedler`), and over a field its `lex`-initial algebra
is not finitely generated (`TauCeti.not_fg_initialAlgebra_robbianoSweedler`). -/
noncomputable def robbianoSweedlerSubalgebra (R : Type*) [CommSemiring R] :
    Subalgebra R (MvPolynomial (Fin 2) R) :=
  Algebra.adjoin R (Set.range (robbianoSweedlerGen R))

/-- Unfolding lemma for `TauCeti.robbianoSweedlerSubalgebra`. -/
theorem robbianoSweedlerSubalgebra_def (R : Type*) [CommSemiring R] :
    robbianoSweedlerSubalgebra R = Algebra.adjoin R (Set.range (robbianoSweedlerGen R)) :=
  (rfl)

/-- The Robbiano–Sweedler subalgebra is finitely generated as an `R`-algebra. -/
theorem fg_robbianoSweedlerSubalgebra (R : Type*) [CommSemiring R] :
    (robbianoSweedlerSubalgebra R).FG :=
  Subalgebra.fg_def.2 ⟨Set.range (robbianoSweedlerGen R), Set.finite_range _, rfl⟩

section CommSemiring

variable {R : Type*} [CommSemiring R]

/-- Specializing `(X 0, X 1)` to `(X 0, 0)` and to `(0, X 0)` agrees on every element of
`robbianoSweedlerSubalgebra R`, since the three generators map to `(X 0, 0, 0)` under both
algebra endomorphisms. -/
theorem aeval_X_zero_eq_aeval_zero_X_of_mem_robbianoSweedlerSubalgebra
    {f : MvPolynomial (Fin 2) R} (hf : f ∈ robbianoSweedlerSubalgebra R) :
    aeval ![X 0, (0 : MvPolynomial (Fin 2) R)] f =
      aeval ![(0 : MvPolynomial (Fin 2) R), X 0] f := by
  have hle : robbianoSweedlerSubalgebra R ≤
      AlgHom.equalizer (aeval ![X 0, (0 : MvPolynomial (Fin 2) R)])
        (aeval ![(0 : MvPolynomial (Fin 2) R), X 0]) := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨i, rfl⟩
    fin_cases i <;> simp
  exact hle hf

/-- No nonconstant pure polynomial in `X 1` belongs to `robbianoSweedlerSubalgebra R`: every
element whose `lex`-leading exponent vanishes at `0` has `lex`-degree `0`. -/
theorem degree_eq_zero_of_mem_robbianoSweedlerSubalgebra {f : MvPolynomial (Fin 2) R}
    (hf : f ∈ robbianoSweedlerSubalgebra R) (h0 : (lex.degree f) 0 = 0) :
    lex.degree f = 0 := by
  have hrange : Set.range (fun _ : Unit ↦ (1 : Fin 2)) = Set.Ici (1 : Fin 2) := by
    ext i
    fin_cases i <;> simp
  have hsupp : ↑(lex.degree f).support ⊆ Set.range (fun _ : Unit ↦ (1 : Fin 2)) := by
    intro i hi
    fin_cases i
    · exact absurd h0 (Finsupp.mem_support_iff.1 hi)
    · exact ⟨(), rfl⟩
  obtain ⟨p, rfl⟩ := lex.exists_rename_eq_of_coe_support_degree_subset
    (fun _ _ hab hb ↦ by
      rw [hrange] at hb ⊢
      exact coe_support_subset_of_lex_le (IsUpperSet.Ici 1) hab hb) hsupp
  have heq := aeval_X_zero_eq_aeval_zero_X_of_mem_robbianoSweedlerSubalgebra hf
  rw [aeval_rename, aeval_rename] at heq
  have hleft : (![X 0, (0 : MvPolynomial (Fin 2) R)] ∘ fun _ : Unit ↦ (1 : Fin 2)) =
      fun _ ↦ 0 := funext fun _ ↦ by simp
  have hright : (![(0 : MvPolynomial (Fin 2) R), X 0] ∘ fun _ : Unit ↦ (1 : Fin 2)) =
      X ∘ fun _ : Unit ↦ (0 : Fin 2) := funext fun _ ↦ by simp
  rw [hleft, hright, aeval_zero', algebraMap_eq, ← rename_eq_aeval,
    ← rename_C (fun _ : Unit ↦ (0 : Fin 2))] at heq
  have hp : p = C (constantCoeff p) := (rename_injective _ (fun _ _ _ ↦ rfl) heq).symm
  rw [hp, rename_C, degree_C]

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R]

/-- The fundamental cancellation relation in `MvPolynomial (Fin 2) R` driving infinite SAGBI
completion on `robbianoSweedlerSubalgebra R`:
`(X 0 + X 1) * (X 0 * X 1 ^ (n + 1)) - (X 0 * X 1) * (X 0 * X 1 ^ n) = X 0 * X 1 ^ (n + 2)`. -/
theorem robbianoSweedler_step_identity (n : ℕ) :
    ((X 0 + X 1) * (X 0 * X 1 ^ (n + 1)) -
      (X 0 * X 1) * (X 0 * X 1 ^ n) : MvPolynomial (Fin 2) R) =
    X 0 * X 1 ^ (n + 2) := by
  ring

/-- Every monomial `X 0 * X 1 ^ (n + 1)` (`n : ℕ`) belongs to `robbianoSweedlerSubalgebra R`. -/
theorem mul_X_one_pow_mem_robbianoSweedlerSubalgebra (n : ℕ) :
    (X 0 * X 1 ^ (n + 1) : MvPolynomial (Fin 2) R) ∈ robbianoSweedlerSubalgebra R := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    match n with
    | 0 =>
      rw [robbianoSweedlerSubalgebra_def, pow_one]
      exact Algebra.subset_adjoin ⟨1, rfl⟩
    | 1 =>
      rw [robbianoSweedlerSubalgebra_def]
      exact Algebra.subset_adjoin ⟨2, rfl⟩
    | m + 2 =>
      rw [← robbianoSweedler_step_identity (R := R) (m + 1)]
      have hg0 : (X 0 + X 1 : MvPolynomial (Fin 2) R) ∈ robbianoSweedlerSubalgebra R := by
        rw [robbianoSweedlerSubalgebra_def]
        exact Algebra.subset_adjoin ⟨0, rfl⟩
      have hg1 : (X 0 * X 1 : MvPolynomial (Fin 2) R) ∈ robbianoSweedlerSubalgebra R := by
        rw [robbianoSweedlerSubalgebra_def]
        exact Algebra.subset_adjoin ⟨1, rfl⟩
      exact sub_mem (mul_mem hg0 (ih (m + 1) (by omega))) (mul_mem hg1 (ih m (by omega)))

section NoZeroDivisors

variable [NoZeroDivisors R] [Nontrivial R]

/-- For every `n : ℕ`, the exponent `(1, n + 1)` is a `lex`-leading exponent of
`robbianoSweedlerSubalgebra R`. -/
theorem single_add_single_mem_leadingExponents_robbianoSweedler (n : ℕ) :
    Finsupp.single (0 : Fin 2) 1 + Finsupp.single 1 (n + 1) ∈
      lex.leadingExponents (robbianoSweedlerSubalgebra R) := by
  classical
  have hmon : (X 0 * X 1 ^ (n + 1) : MvPolynomial (Fin 2) R) =
      monomial (Finsupp.single 0 1 + Finsupp.single 1 (n + 1)) 1 := by
    rw [monomial_add_single, ← X]
  refine mem_leadingExponents_iff.2
    ⟨X 0 * X 1 ^ (n + 1), mul_X_one_pow_mem_robbianoSweedlerSubalgebra n, ?_, ?_⟩
  · rw [hmon]
    exact monomial_eq_zero.not.2 one_ne_zero
  · rw [hmon, degree_monomial]
    simp

/-- Every nonzero `lex`-leading exponent `a` of `robbianoSweedlerSubalgebra R` has `1 ≤ a 0`. -/
theorem pos_apply_zero_of_mem_leadingExponents_robbianoSweedler {a : Fin 2 →₀ ℕ}
    (ha : a ∈ lex.leadingExponents (robbianoSweedlerSubalgebra R)) (ha0 : a ≠ 0) :
    0 < a 0 := by
  obtain ⟨f, hf, -, rfl⟩ := mem_leadingExponents_iff.1 ha
  exact Nat.pos_of_ne_zero fun h0 ↦
    ha0 (degree_eq_zero_of_mem_robbianoSweedlerSubalgebra hf h0)

/-- The additive submonoid of exponents `x : Fin 2 →₀ ℕ` satisfying `x 1 ≤ M * x 0`. -/
private def slopeSubmonoid (M : ℕ) : AddSubmonoid (Fin 2 →₀ ℕ) where
  carrier := {x | x 1 ≤ M * x 0}
  zero_mem' := by simp
  add_mem' {x y} hx hy := by
    simp only [Set.mem_ofPred_eq, Finsupp.coe_add, Pi.add_apply, mul_add] at hx hy ⊢
    omega

private theorem mem_slopeSubmonoid_iff {M : ℕ} {x : Fin 2 →₀ ℕ} :
    x ∈ slopeSubmonoid M ↔ x 1 ≤ M * x 0 :=
  Iff.rfl

/-- The monoid of `lex`-leading exponents of `robbianoSweedlerSubalgebra R` is not finitely
generated, even though `robbianoSweedlerSubalgebra R` is generated as an `R`-algebra by three
polynomials. -/
theorem not_fg_leadingExponents_robbianoSweedler :
    ¬ (lex.leadingExponents (robbianoSweedlerSubalgebra R)).FG := by
  intro hfg
  obtain ⟨S, hS⟩ := AddSubmonoid.isAddFG_iff.1 hfg
  set M := S.sup fun s ↦ s 1
  -- Every generator `s ∈ S` satisfies `s 1 ≤ M * s 0`, so `AddSubmonoid.closure S` lies in
  -- `slopeSubmonoid M`, contradicting `(1, M + 1)`.
  have hbound : AddSubmonoid.closure (S : Set (Fin 2 →₀ ℕ)) ≤ slopeSubmonoid M := by
    refine AddSubmonoid.closure_le.2 fun s hs ↦ mem_slopeSubmonoid_iff.2 ?_
    have hs' : s ∈ lex.leadingExponents (robbianoSweedlerSubalgebra R) :=
      hS ▸ AddSubmonoid.subset_closure hs
    rcases eq_or_ne s 0 with rfl | hs0
    · simp
    · calc
        s 1 ≤ M := Finset.le_sup (f := fun t : Fin 2 →₀ ℕ ↦ t 1) hs
        _ ≤ M * s 0 := Nat.le_mul_of_pos_right M
          (pos_apply_zero_of_mem_leadingExponents_robbianoSweedler hs' hs0)
  have hmem : Finsupp.single (0 : Fin 2) 1 + Finsupp.single 1 (M + 1) ∈
      AddSubmonoid.closure (S : Set (Fin 2 →₀ ℕ)) := by
    rw [hS]
    exact single_add_single_mem_leadingExponents_robbianoSweedler M
  have hle := mem_slopeSubmonoid_iff.1 (hbound hmem)
  simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne Fin.zero_ne_one, Finsupp.single_eq_of_ne Fin.zero_ne_one.symm,
    add_zero, zero_add, mul_one] at hle
  omega

end NoZeroDivisors

end CommRing

section Field

variable (k : Type*) [Field k]

/-- Over a field, the `lex`-initial algebra of `robbianoSweedlerSubalgebra k` is not finitely
generated as a `k`-algebra. -/
theorem not_fg_initialAlgebra_robbianoSweedler :
    ¬ (lex.initialAlgebra (robbianoSweedlerSubalgebra k)).FG :=
  lex.fg_initialAlgebra_iff_fg_leadingExponents.not.2 not_fg_leadingExponents_robbianoSweedler

/-- Over a field, no finite subset is a `lex`-SAGBI basis of `robbianoSweedlerSubalgebra k`. -/
theorem not_isSAGBIBasis_finset_robbianoSweedler (B : Finset (MvPolynomial (Fin 2) k)) :
    ¬ lex.IsSAGBIBasis (B : Set (MvPolynomial (Fin 2) k)) (robbianoSweedlerSubalgebra k) :=
  fun hB ↦ not_fg_leadingExponents_robbianoSweedler (hB.fg_leadingExponents B.finite_toSet)

end Field

end RobbianoSweedler

section RobbianoSweedlerInfinite

/-- The explicit polynomial family `Fin (n + 3) → MvPolynomial (Fin 2) R` whose index `0` entry is
`X 0 + X 1` and whose index `i > 0` entry is `X 0 * X 1 ^ (i : ℕ)`. Over a nontrivial commutative
ring (in particular, a field), this family lies in `robbianoSweedlerSubalgebra R` and realizes
stage `n` of one-relation-at-a-time `lex`-SAGBI completion
(`TauCeti.isSubduction_robbianoSweedlerStage`, `TauCeti.range_robbianoSweedlerStage_succ`). -/
noncomputable def robbianoSweedlerStage (R : Type*) [CommSemiring R] (n : ℕ) (i : Fin (n + 3)) :
    MvPolynomial (Fin 2) R :=
  if (i : ℕ) = 0 then X 0 + X 1 else X 0 * X 1 ^ (i : ℕ)

/-- Unfolding lemma for `TauCeti.robbianoSweedlerStage`. -/
theorem robbianoSweedlerStage_def (R : Type*) [CommSemiring R] (n : ℕ) (i : Fin (n + 3)) :
    robbianoSweedlerStage R n i =
      if (i : ℕ) = 0 then X 0 + X 1 else X 0 * X 1 ^ (i : ℕ) :=
  (rfl)

/-- The `0`-th entry of `robbianoSweedlerStage R n` is `X 0 + X 1`. -/
@[simp]
theorem robbianoSweedlerStage_apply_zero (R : Type*) [CommSemiring R] (n : ℕ) :
    robbianoSweedlerStage R n 0 = X 0 + X 1 := by
  simp [robbianoSweedlerStage_def]

/-- For every nonzero index `i`, the `i`-th entry of `robbianoSweedlerStage R n` is
`X 0 * X 1 ^ (i : ℕ)`. -/
@[simp]
theorem robbianoSweedlerStage_apply_of_ne_zero (R : Type*) [CommSemiring R] (n : ℕ)
    {i : Fin (n + 3)} (hi : i ≠ 0) :
    robbianoSweedlerStage R n i = X 0 * X 1 ^ (i : ℕ) := by
  simp [robbianoSweedlerStage_def, hi]

/-- Extending `robbianoSweedlerStage R` from stage `n` to stage `n + 1` preserves all entries
inherited along `Fin.castSucc`. -/
@[simp]
theorem robbianoSweedlerStage_succ_castSucc (R : Type*) [CommSemiring R] (n : ℕ)
    (i : Fin (n + 3)) :
    robbianoSweedlerStage R (n + 1) i.castSucc = robbianoSweedlerStage R n i := by
  simp [robbianoSweedlerStage_def]

/-- Stage `0` of `robbianoSweedlerStage R` coincides with the initial generator family
`robbianoSweedlerGen R`. -/
@[simp]
theorem robbianoSweedlerStage_zero_eq (R : Type*) [CommSemiring R] :
    robbianoSweedlerStage R 0 = robbianoSweedlerGen R := by
  funext i
  fin_cases i <;> simp

/-- Every generator at stage `n` of `robbianoSweedlerStage R` is `lex`-monic over any commutative
semiring. -/
theorem monic_robbianoSweedlerStage {R : Type*} [CommSemiring R]
    (n : ℕ) (i : Fin (n + 3)) : lex.Monic (robbianoSweedlerStage R n i) := by
  by_cases hi : i = 0
  · subst hi
    rw [robbianoSweedlerStage_apply_zero]
    nontriviality R
    exact lex.monic_X.add_of_lt (by
      rw [lex.degree_X, lex.degree_X, lex_lt_iff, Finsupp.Lex.single_lt_iff]
      exact zero_lt_one)
  · rw [robbianoSweedlerStage_apply_of_ne_zero R n hi]
    exact lex.monic_X.mul lex.monic_X.pow

/-- All three initial generators of `robbianoSweedlerGen R` are `lex`-monic over any commutative
semiring. -/
theorem monic_robbianoSweedlerGen {R : Type*} [CommSemiring R] (i : Fin 3) :
    lex.Monic (robbianoSweedlerGen R i) := by
  rw [← robbianoSweedlerStage_zero_eq]
  exact monic_robbianoSweedlerStage 0 i

/-- The `lex`-leading exponent of the `i`-th generator of `robbianoSweedlerStage R n` is `(1, i)`.
-/
theorem degree_robbianoSweedlerStage {R : Type*} [CommSemiring R] [Nontrivial R]
    (n : ℕ) (i : Fin (n + 3)) :
    lex.degree (robbianoSweedlerStage R n i) =
      Finsupp.single 0 1 + Finsupp.single 1 (i : ℕ) := by
  classical
  by_cases hi : i = 0
  · subst hi
    simp only [robbianoSweedlerStage_apply_zero, Fin.val_zero, Finsupp.single_zero, add_zero]
    rw [lex.degree_add_of_lt (by
      rw [lex.degree_X, lex.degree_X, lex_lt_iff, Finsupp.Lex.single_lt_iff]
      exact zero_lt_one), lex.degree_X]
  · rw [robbianoSweedlerStage_apply_of_ne_zero R n hi]
    have hmon : (X 0 * X 1 ^ (i : ℕ) : MvPolynomial (Fin 2) R) =
        monomial (Finsupp.single 0 1 + Finsupp.single 1 (i : ℕ)) 1 := by
      rw [monomial_add_single, ← X]
    rw [hmon, degree_monomial, ite_eq_right one_ne_zero]

/-- The toric binomial `Y 0 * Y (n + 2) - Y 1 * Y (n + 1)` at stage `n` of
`robbianoSweedlerStage`. -/
noncomputable def robbianoSweedlerBinomial (R : Type*) [CommRing R] (n : ℕ) :
    MvPolynomial (Fin (n + 3)) R :=
  monomial (Finsupp.single 0 1 + Finsupp.single ⟨n + 2, by omega⟩ 1) 1 -
    monomial (Finsupp.single ⟨1, by omega⟩ 1 + Finsupp.single ⟨n + 1, by omega⟩ 1) 1

/-- Unfolding lemma for `TauCeti.robbianoSweedlerBinomial`. -/
theorem robbianoSweedlerBinomial_def (R : Type*) [CommRing R] (n : ℕ) :
    robbianoSweedlerBinomial R n =
      monomial (Finsupp.single 0 1 + Finsupp.single ⟨n + 2, by omega⟩ 1) 1 -
        monomial (Finsupp.single ⟨1, by omega⟩ 1 + Finsupp.single ⟨n + 1, by omega⟩ 1) 1 :=
  (rfl)

/-- `robbianoSweedlerBinomial R n` belongs to the toric ideal of the leading exponents of
`robbianoSweedlerStage R n` (both monomials have common leading exponent `(2, n + 2)`). -/
theorem robbianoSweedlerBinomial_mem_toricIdeal {R : Type*} [CommRing R] [Nontrivial R] (n : ℕ) :
    robbianoSweedlerBinomial R n ∈
      TauCeti.toricIdeal R (fun i ↦ lex.degree (robbianoSweedlerStage R n i)) := by
  rw [robbianoSweedlerBinomial_def]
  refine TauCeti.monomial_sub_monomial_mem_toricIdeal ?_
  simp only [map_add, Finsupp.linearCombination_single, one_smul, degree_robbianoSweedlerStage]
  ext d
  fin_cases d <;> simp; omega

/-- Evaluating `robbianoSweedlerBinomial R n` at `robbianoSweedlerStage R n` yields the next
monomial `X 0 * X 1 ^ (n + 3)`. -/
theorem aeval_robbianoSweedlerStage_binomial {R : Type*} [CommRing R] (n : ℕ) :
    aeval (robbianoSweedlerStage R n) (robbianoSweedlerBinomial R n) =
      (X 0 * X 1 ^ (n + 3) : MvPolynomial (Fin 2) R) := by
  have hmul (a b : Fin (n + 3)) :
      aeval (robbianoSweedlerStage R n)
        (monomial (Finsupp.single a 1 + Finsupp.single b 1) (1 : R)) =
        robbianoSweedlerStage R n a * robbianoSweedlerStage R n b := by
    rw [monomial_add_single, ← X, pow_one, map_mul, aeval_X, aeval_X]
  rw [robbianoSweedlerBinomial_def, map_sub, hmul, hmul]
  simpa using robbianoSweedler_step_identity (R := R) (n + 1)

/-- At every stage `n` over a nontrivial commutative ring, the toric binomial
`robbianoSweedlerBinomial R n` subducts with zero quotient expression `Q = 0` and nonzero
irreducible remainder `X 0 * X 1 ^ (n + 3)`. -/
theorem isSubduction_robbianoSweedlerStage {R : Type*} [CommRing R] [Nontrivial R] (n : ℕ) :
    lex.IsSubduction (robbianoSweedlerStage R n)
      (aeval (robbianoSweedlerStage R n) (robbianoSweedlerBinomial R n))
      0 (X 0 * X 1 ^ (n + 3)) := by
  have hbound : AddSubmonoid.closure
      (Set.range (lex.degree ∘ robbianoSweedlerStage R n)) ≤ slopeSubmonoid (n + 2) := by
    refine AddSubmonoid.closure_le.2 ?_
    rintro _ ⟨i, rfl⟩
    simp only [Function.comp_apply, degree_robbianoSweedlerStage, SetLike.mem_coe,
      mem_slopeSubmonoid_iff, Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne Fin.zero_ne_one, Finsupp.single_eq_of_ne Fin.zero_ne_one.symm,
      add_zero, zero_add, mul_one]
    omega
  refine ⟨by simp [aeval_robbianoSweedlerStage_binomial], by simp, fun a ha hmem ↦ ?_,
    by simp [aeval_robbianoSweedlerStage_binomial]⟩
  have hmon : (X 0 * X 1 ^ (n + 3) : MvPolynomial (Fin 2) R) =
      monomial (Finsupp.single 0 1 + Finsupp.single 1 (n + 3)) 1 := by
    rw [monomial_add_single, ← X]
  rw [hmon] at ha
  have ha' := Finset.mem_singleton.1 (support_monomial_subset ha)
  have hle := mem_slopeSubmonoid_iff.1 (hbound hmem)
  rw [ha'] at hle
  simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne Fin.zero_ne_one, Finsupp.single_eq_of_ne Fin.zero_ne_one.symm,
    add_zero, zero_add, mul_one] at hle
  omega

section Field

variable {k : Type*} [Field k]

/-- No stage of batch SAGBI completion starting from `robbianoSweedlerGen k` is a `lex`-SAGBI
basis of `robbianoSweedlerSubalgebra k`: without finite generation of the initial algebra,
certified completion runs forever even on a three-generator subalgebra of `k[X 0, X 1]`. -/
theorem not_isSAGBIBasis_sagbiCompletionFamily_robbianoSweedler (n : ℕ) :
    ¬ lex.IsSAGBIBasis (Set.range (lex.sagbiCompletionFamily (robbianoSweedlerGen k) n))
      (robbianoSweedlerSubalgebra k) := by
  intro hB
  exact not_fg_leadingExponents_robbianoSweedler (hB.fg_leadingExponents (Set.finite_range _))

/-- Stage `n + 1` of `robbianoSweedlerStage k` is obtained from stage `n` by adjoining the monic
normalization of the nonzero remainder `X 0 * X 1 ^ (n + 3)`. -/
theorem range_robbianoSweedlerStage_succ (n : ℕ) :
    Set.range (robbianoSweedlerStage k (n + 1)) =
      insert (lex.monicNormalize (X 0 * X 1 ^ (n + 3)))
        (Set.range (robbianoSweedlerStage k n)) := by
  have hinit : Fin.init (robbianoSweedlerStage k (n + 1)) = robbianoSweedlerStage k n :=
    funext (robbianoSweedlerStage_succ_castSucc k n)
  have hlast : robbianoSweedlerStage k (n + 1) (Fin.last (n + 3)) = X 0 * X 1 ^ (n + 3) := by
    simp
  rw [← Fin.snoc_init_self (robbianoSweedlerStage k (n + 1)), hinit, hlast, Fin.range_snoc,
    (lex.monic_X.mul lex.monic_X.pow).monicNormalize_eq]

/-- The leading-term subalgebras of `robbianoSweedlerStage k n` form an infinite strictly
ascending chain of completion steps inside `lex.initialAlgebra (robbianoSweedlerSubalgebra k)`. -/
theorem adjoin_leadingTerm_robbianoSweedlerStage_lt (n : ℕ) :
    Algebra.adjoin k (lex.leadingTerm '' Set.range (robbianoSweedlerStage k n)) <
      Algebra.adjoin k (lex.leadingTerm '' Set.range (robbianoSweedlerStage k (n + 1))) := by
  rw [range_robbianoSweedlerStage_succ]
  exact (isSubduction_robbianoSweedlerStage (R := k) n).adjoin_leadingTerm_lt
    (lex.monic_X.mul lex.monic_X.pow).ne_zero

end Field

end RobbianoSweedlerInfinite

end TauCeti
