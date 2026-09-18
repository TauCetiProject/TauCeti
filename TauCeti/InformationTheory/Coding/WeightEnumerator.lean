/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import TauCeti.InformationTheory.Coding.DirectSum
public import TauCeti.InformationTheory.Coding.Equivalence
public import TauCeti.InformationTheory.Coding.MinimumDistance

/-!
# Weight distributions and weight enumerators

For a set of words `C` on a finite coordinate type `ι` of size `n`, the *weight distribution*
`A_w(C)` counts the words of Hamming weight `w`, and the *homogeneous weight enumerator* is

  `W_C(X, Y) = ∑_w A_w(C) X^(n-w) Y^w`,

which for finite `C` equals the sum over codewords `∑_{c ∈ C} X^(n - wt c) Y^(wt c)`. It is
a homogeneous polynomial of degree `n` with integer coefficients, with the variables `0, 1` of
`MvPolynomial (Fin 2) ℤ` playing the roles of `X, Y`. Its one-variable specialization at `X = 1`
is the *weight polynomial* `∑_w A_w(C) Y^w`.

These invariants carry the Hamming data of a finite code in the form used by the MacWilliams
identity `#C · W_{C⊥}(X, Y) = W_C(X + (q - 1) Y, X - Y)`: they are unchanged by monomial
equivalence and recover the cardinality and minimum distance of a finite additive code, and the
homogeneous weight enumerator is multiplicative under direct sums.

## Main definitions

* `Set.weightDistribution C w`: the number of words of `C` of Hamming weight `w`.
* `Set.weightEnumerator C`: the homogeneous weight enumerator `W_C(X, Y)`.
* `Set.weightPolynomial C`: the one-variable weight enumerator `W_C(1, Y)`.

## Main statements

* `Set.weightEnumerator_eq_sum`: `W_C` is the sum over codewords of `X^(n - wt c) Y^(wt c)`.
* `Set.coeff_weightEnumerator`, `Set.coeff_weightPolynomial`: the coefficients are the weight
  distribution.
* `Set.isHomogeneous_weightEnumerator`, `Set.eval_one_weightEnumerator`: `W_C` is homogeneous of
  degree `n`, and `W_C(1, 1) = #C`.
* `Set.hammingMinDist_eq_sInf_weightDistribution`: the minimum distance of a finite additive
  code is its least positive weight with nonzero multiplicity.
* `TauCeti.IsMonomialEquivalent.weightEnumerator_eq`: monomially equivalent codes have the same
  weight enumerator.
* `Submodule.weightEnumerator_directSum`: the weight enumerator of a direct sum is the product of
  the weight enumerators.

## References

W. C. Huffman and V. Pless, *Fundamentals of Error-Correcting Codes*, Cambridge University
Press (2003), §7.2; F. J. MacWilliams and N. J. A. Sloane, *The Theory of Error-Correcting
Codes*, North-Holland (1977), Chapter 5, §2.
-/

public section

open MvPolynomial Finset

namespace Set

variable {ι : Type*} {β : ι → Type*} [Fintype ι] [∀ i, Zero (β i)] [∀ i, DecidableEq (β i)]
  {C : Set (∀ i, β i)}

/-! ### The weight distribution -/

/-- The weight distribution of a set of words: the number of words of Hamming weight `w`.
It is meaningful for finite sets of words; for an infinite fibre `Nat.card` is zero. -/
noncomputable def weightDistribution (C : Set (∀ i, β i)) (w : ℕ) : ℕ :=
  Nat.card {x : ∀ i, β i // x ∈ C ∧ hammingNorm x = w}

theorem weightDistribution_def (C : Set (∀ i, β i)) (w : ℕ) :
    C.weightDistribution w = Nat.card {x : ∀ i, β i // x ∈ C ∧ hammingNorm x = w} := (rfl)

/-- For a finite set of words, the weight distribution counts a finite filter. -/
theorem weightDistribution_eq_card_filter (hC : C.Finite) (w : ℕ) :
    C.weightDistribution w = #{x ∈ hC.toFinset | hammingNorm x = w} := by
  refine (Nat.card_eq_card_finite_toFinset
    (hC.subset (t := {x | x ∈ C ∧ hammingNorm x = w}) fun _ hx ↦ hx.1)).trans ?_
  congr 1
  ext x
  simp

/-- There are no words of weight greater than the length. -/
theorem weightDistribution_eq_zero_of_card_lt {w : ℕ} (hw : Fintype.card ι < w) :
    C.weightDistribution w = 0 := by
  rw [weightDistribution_def, Nat.card_eq_zero]
  exact .inl ⟨fun x ↦ (hammingNorm_le_card_fintype.trans_lt hw).ne x.2.2⟩

/-- A set of words containing the zero word has exactly one word of weight zero. -/
@[simp]
theorem weightDistribution_zero (h : 0 ∈ C) : C.weightDistribution 0 = 1 := by
  rw [weightDistribution_def, Nat.card_eq_one_iff_exists]
  refine ⟨⟨0, h, hammingNorm_zero⟩, fun x ↦ Subtype.ext ?_⟩
  exact hammingNorm_eq_zero.mp x.2.2

/-- In a finite set of words, a weight occurs exactly when some word has that weight. -/
theorem weightDistribution_ne_zero_iff (hC : C.Finite) {w : ℕ} :
    C.weightDistribution w ≠ 0 ↔ ∃ x ∈ C, hammingNorm x = w := by
  rw [weightDistribution_eq_card_filter hC, Ne, Finset.card_eq_zero, ← Ne,
    ← Finset.nonempty_iff_ne_empty]
  simp [Finset.Nonempty]

/-- The weight distribution of a finite set of words sums to its cardinality. -/
theorem sum_weightDistribution (hC : C.Finite) :
    ∑ w ∈ Finset.range (Fintype.card ι + 1), C.weightDistribution w = Nat.card C := by
  rw [Nat.card_eq_card_finite_toFinset hC,
    card_eq_sum_card_fiberwise (f := hammingNorm) (t := Finset.range (Fintype.card ι + 1))
      fun x _ ↦ mem_range_succ_iff.mpr hammingNorm_le_card_fintype]
  exact sum_congr rfl fun w _ ↦ weightDistribution_eq_card_filter hC w

/-! ### The homogeneous weight enumerator -/

/-- The homogeneous Hamming weight enumerator `W_C(X, Y) = ∑_w A_w(C) X^(n-w) Y^w`, where `n`
is the length, `A_w(C)` is the weight distribution, and the variables `0, 1` are `X, Y`. -/
noncomputable def weightEnumerator (C : Set (∀ i, β i)) : MvPolynomial (Fin 2) ℤ :=
  ∑ w ∈ Finset.range (Fintype.card ι + 1),
    MvPolynomial.C (C.weightDistribution w : ℤ) * X 0 ^ (Fintype.card ι - w) * X 1 ^ w

theorem weightEnumerator_def (C : Set (∀ i, β i)) :
    C.weightEnumerator = ∑ w ∈ Finset.range (Fintype.card ι + 1),
      MvPolynomial.C (C.weightDistribution w : ℤ) * X 0 ^ (Fintype.card ι - w) * X 1 ^ w :=
  (rfl)

/-- The weight enumerator of a finite set of words is the sum over its words `c` of
`X^(n - wt c) Y^(wt c)`. -/
theorem weightEnumerator_eq_sum (hC : C.Finite) :
    C.weightEnumerator =
      ∑ c ∈ hC.toFinset, X 0 ^ (Fintype.card ι - hammingNorm c) * X 1 ^ hammingNorm c := by
  rw [weightEnumerator_def, ← sum_fiberwise_of_maps_to (g := hammingNorm)
    (t := Finset.range (Fintype.card ι + 1))
    fun x _ ↦ mem_range_succ_iff.mpr hammingNorm_le_card_fintype]
  refine sum_congr rfl fun w _ ↦ ?_
  rw [sum_congr rfl fun c hc ↦ by rw [(mem_filter.mp hc).2], sum_const, nsmul_eq_mul,
    weightDistribution_eq_card_filter hC, map_natCast, mul_assoc]

/-- The monomial form of the weight enumerator. -/
theorem weightEnumerator_eq_sum_monomial (C : Set (∀ i, β i)) :
    C.weightEnumerator = ∑ w ∈ Finset.range (Fintype.card ι + 1),
      monomial (Finsupp.single 0 (Fintype.card ι - w) + Finsupp.single 1 w)
        (C.weightDistribution w : ℤ) := by
  refine sum_congr rfl fun w _ ↦ ?_
  rw [X_pow_eq_monomial, X_pow_eq_monomial, C_mul_monomial, monomial_mul_monomial, mul_one,
    mul_one]

/-- The coefficients of the weight enumerator are the weight distribution: the coefficient of
`X^a Y^b` is `A_b(C)` when `a + b` is the length, and zero otherwise. -/
@[simp]
theorem coeff_weightEnumerator (C : Set (∀ i, β i)) (d : Fin 2 →₀ ℕ) :
    C.weightEnumerator.coeff d =
      if d 0 + d 1 = Fintype.card ι then (C.weightDistribution (d 1) : ℤ) else 0 := by
  rw [weightEnumerator_eq_sum_monomial, coeff_sum]
  simp_rw [coeff_monomial]
  have key : ∀ w ∈ Finset.range (Fintype.card ι + 1),
      (Finsupp.single 0 (Fintype.card ι - w) + Finsupp.single 1 w = d ↔
        d 1 = w ∧ d 0 + d 1 = Fintype.card ι) := by
    intro w hw
    have hw := mem_range_succ_iff.mp hw
    constructor
    · rintro rfl
      simpa using Nat.sub_add_cancel hw
    · rintro ⟨h1, h0⟩
      ext i
      fin_cases i <;> simp <;> omega
  rw [sum_congr rfl fun w hw ↦ if_congr (key w hw) rfl rfl]
  split_ifs with hd
  · simp only [hd, and_true]
    rw [sum_ite_eq, ite_eq_left_iff]
    exact fun h ↦ absurd (mem_range_succ_iff.mpr (by omega)) h
  · simp [hd]

/-- The weight enumerator is homogeneous of degree the length. -/
theorem isHomogeneous_weightEnumerator (C : Set (∀ i, β i)) :
    C.weightEnumerator.IsHomogeneous (Fintype.card ι) := by
  refine IsHomogeneous.sum _ _ _ fun w hw ↦ ?_
  have h := (isHomogeneous_C_mul_X_pow (C.weightDistribution w : ℤ) (0 : Fin 2)
    (Fintype.card ι - w)).mul (isHomogeneous_X_pow (1 : Fin 2) w)
  rw [Nat.sub_add_cancel (mem_range_succ_iff.mp hw)] at h
  exact h

/-- The weight enumerator of a finite set of words evaluates to its cardinality at
`X = Y = 1`. -/
@[simp]
theorem eval_one_weightEnumerator (hC : C.Finite) :
    eval 1 C.weightEnumerator = Nat.card C := by
  simp [weightEnumerator_def, ← sum_weightDistribution hC]

/-! ### The one-variable weight enumerator -/

/-- The one-variable weight enumerator `∑_w A_w(C) Y^w`, the specialization of the homogeneous
weight enumerator at `X = 1`. -/
noncomputable def weightPolynomial (C : Set (∀ i, β i)) : Polynomial ℤ :=
  ∑ w ∈ Finset.range (Fintype.card ι + 1), Polynomial.monomial w (C.weightDistribution w : ℤ)

theorem weightPolynomial_def (C : Set (∀ i, β i)) :
    C.weightPolynomial =
      ∑ w ∈ Finset.range (Fintype.card ι + 1), Polynomial.monomial w (C.weightDistribution w : ℤ) :=
  (rfl)

/-- The coefficients of the one-variable weight enumerator are the weight distribution. -/
@[simp]
theorem coeff_weightPolynomial (C : Set (∀ i, β i)) (w : ℕ) :
    C.weightPolynomial.coeff w = C.weightDistribution w := by
  rw [weightPolynomial_def, Polynomial.finsetSum_coeff]
  simp_rw [Polynomial.coeff_monomial]
  rw [sum_ite_eq', ite_eq_left_iff]
  intro hw
  rw [weightDistribution_eq_zero_of_card_lt (by simpa [Nat.lt_succ_iff] using hw),
    Nat.cast_zero]

/-- The one-variable weight enumerator is the homogeneous one evaluated at `X = 1`. -/
theorem aeval_weightEnumerator (C : Set (∀ i, β i)) :
    aeval ![1, Polynomial.X] C.weightEnumerator = C.weightPolynomial := by
  simp only [weightEnumerator_def, weightPolynomial_def, map_sum]
  refine sum_congr rfl fun w _ ↦ ?_
  simp [← Polynomial.C_mul_X_pow_eq_monomial]

/-- The one-variable weight enumerator of a finite set of words evaluates to its cardinality at
`Y = 1`. -/
@[simp]
theorem eval_one_weightPolynomial (hC : C.Finite) :
    C.weightPolynomial.eval 1 = Nat.card C := by
  simp [weightPolynomial_def, Polynomial.eval_finsetSum, ← sum_weightDistribution hC]

/-! ### Recovering the minimum distance -/

/-- The minimum distance of a finite additive code is the least positive weight occurring in
its weight distribution; both sides are zero for the zero code. -/
theorem hammingMinDist_eq_sInf_weightDistribution {β : ι → Type*} [∀ i, AddGroup (β i)]
    [∀ i, DecidableEq (β i)] {E : AddSubgroup (∀ i, β i)} (hE : (E : Set (∀ i, β i)).Finite) :
    hammingMinDist (E : Set (∀ i, β i)) =
      sInf {w | 0 < w ∧ (E : Set (∀ i, β i)).weightDistribution w ≠ 0} := by
  rw [hammingMinDist_eq_sInf_hammingNorm]
  congr 1
  ext w
  simp only [mem_ofPred_eq, weightDistribution_ne_zero_iff hE, SetLike.mem_coe]
  constructor
  · rintro ⟨x, hx, hx0, rfl⟩
    exact ⟨hammingNorm_pos_iff.mpr hx0, x, hx, rfl⟩
  · rintro ⟨hw, x, hx, rfl⟩
    exact ⟨x, hx, hammingNorm_pos_iff.mp hw, rfl⟩

end Set

/-! ### Monomial equivalence and direct sums -/

namespace TauCeti

variable {ι κ R : Type*} [Fintype ι] [Fintype κ] [DecidableEq R]

section PermutationEquivalence

variable [Semiring R] {C : Submodule R (ι → R)} {D : Submodule R (κ → R)}

/-- Permutation-equivalent codes have the same weight distribution. -/
theorem IsPermutationEquivalent.weightDistribution_eq (h : IsPermutationEquivalent C D)
    (w : ℕ) :
    (C : Set (ι → R)).weightDistribution w = (D : Set (κ → R)).weightDistribution w := by
  obtain ⟨e, rfl⟩ := isPermutationEquivalent_iff.mp h
  refine Nat.card_congr
    (Equiv.subtypeEquiv (LinearEquiv.funCongrLeft R R e.symm).toEquiv fun x ↦ ?_)
  simp only [SetLike.mem_coe, LinearEquiv.coe_toEquiv, Submodule.mem_map_equiv,
    LinearEquiv.funCongrLeft_symm, Equiv.symm_symm, LinearEquiv.funCongrLeft_apply]
  have hinv : LinearMap.funLeft R R e (LinearMap.funLeft R R e.symm x) = x :=
    funext fun i ↦ congrArg x (e.symm_apply_apply i)
  have hx : LinearMap.funLeft R R e.symm x = x ∘ e.symm := by
    ext i
    simp
  rw [hinv, hx, Equiv.hammingNorm_comp]

/-- Permutation-equivalent codes have the same weight enumerator. -/
theorem IsPermutationEquivalent.weightEnumerator_eq (h : IsPermutationEquivalent C D) :
    (C : Set (ι → R)).weightEnumerator = (D : Set (κ → R)).weightEnumerator := by
  have hcard : Fintype.card ι = Fintype.card κ := by
    obtain ⟨e, -⟩ := isPermutationEquivalent_iff.mp h
    exact Fintype.card_congr e
  simp_rw [Set.weightEnumerator_def, hcard, h.weightDistribution_eq]

end PermutationEquivalence

section MonomialEquivalence

variable [CommSemiring R] {C : Submodule R (ι → R)} {D : Submodule R (κ → R)}

/-- Monomially equivalent codes have the same weight distribution. -/
theorem IsMonomialEquivalent.weightDistribution_eq (h : IsMonomialEquivalent C D) (w : ℕ) :
    (C : Set (ι → R)).weightDistribution w = (D : Set (κ → R)).weightDistribution w := by
  obtain ⟨u, e, rfl⟩ := isMonomialEquivalent_iff.mp h
  exact Nat.card_congr (Equiv.subtypeEquiv (monomialEquiv u e).toEquiv fun x ↦ by simp)

/-- Monomially equivalent codes have the same weight enumerator. -/
theorem IsMonomialEquivalent.weightEnumerator_eq (h : IsMonomialEquivalent C D) :
    (C : Set (ι → R)).weightEnumerator = (D : Set (κ → R)).weightEnumerator := by
  have hcard : Fintype.card ι = Fintype.card κ := by
    obtain ⟨_, e, -⟩ := isMonomialEquivalent_iff.mp h
    exact Fintype.card_congr e
  simp_rw [Set.weightEnumerator_def, hcard, h.weightDistribution_eq]

end MonomialEquivalence

end TauCeti

namespace Submodule

variable {ι κ R : Type*} [Fintype ι] [Fintype κ] [Semiring R] [DecidableEq R] [Finite R]

/-- The weight enumerator of a direct sum of codes is the product of their weight
enumerators. -/
theorem weightEnumerator_directSum (C : Submodule R (ι → R)) (D : Submodule R (κ → R)) :
    (directSum C D : Set (ι ⊕ κ → R)).weightEnumerator =
      (C : Set (ι → R)).weightEnumerator * (D : Set (κ → R)).weightEnumerator := by
  classical
  let _ := Fintype.ofFinite C
  let _ := Fintype.ofFinite D
  let _ := Fintype.ofFinite (directSum C D)
  rw [Set.weightEnumerator_eq_sum (Set.toFinite _), Set.weightEnumerator_eq_sum (Set.toFinite _),
    Set.weightEnumerator_eq_sum (Set.toFinite _),
    sum_subtype _ (p := (· ∈ directSum C D)) fun _ ↦ Set.Finite.mem_toFinset _,
    sum_subtype _ (p := (· ∈ C)) fun _ ↦ Set.Finite.mem_toFinset _,
    sum_subtype _ (p := (· ∈ D)) fun _ ↦ Set.Finite.mem_toFinset _, Fintype.sum_mul_sum,
    ← Fintype.sum_prod_type',
    ← (directSumEquivProd C D).symm.toEquiv.sum_comp]
  refine Fintype.sum_congr _ _ fun ⟨x, y⟩ ↦ ?_
  have ha : hammingNorm x.1 ≤ Fintype.card ι := hammingNorm_le_card_fintype
  have hb : hammingNorm y.1 ≤ Fintype.card κ := hammingNorm_le_card_fintype
  have hsub : Fintype.card ι + Fintype.card κ - (hammingNorm x.1 + hammingNorm y.1) =
      (Fintype.card ι - hammingNorm x.1) + (Fintype.card κ - hammingNorm y.1) := by
    omega
  rw [LinearEquiv.coe_toEquiv, hammingNorm_directSumEquivProd_symm, Fintype.card_sum, hsub]
  ring

end Submodule
