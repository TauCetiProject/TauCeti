/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import TauCeti.RingTheory.MvPolynomial.HasseDeriv.WeightedHomogeneous

/-!
# Multihomogeneous polynomials

Split the variables of a polynomial ring into blocks: the variables are `X (h, i)` for a block
index `h : κ` and a position `i : ι` inside the block. A polynomial `P` is *multihomogeneous of
multidegree `d : κ → ℕ`* when every monomial occurring in `P` has degree exactly `d h` in the
variables of block `h`, for every `h`. Equivalently, `P` is weighted homogeneous of weight `d h`
for the indicator weight of every block, which is how the block-homogeneous calculus of
`TauCeti.RingTheory.MvPolynomial.HasseDeriv.WeightedHomogeneous` and
`TauCeti.RingTheory.MvPolynomial.BlockHomogenize` already phrases it; the predicate
`MvPolynomial.IsMultiHomogeneous` names that conjunction.

Multihomogeneous polynomials are the auxiliary polynomials of Schmidt's proof of the Subspace
Theorem: one block of `card ι` variables for each of the `m` points the polynomial is evaluated
at. The monomials of multidegree `d` are the products over the blocks of monomials of degree
`d h` in one block, and their number `∏ h, (card ι + d h - 1).choose (d h)` is the number of
unknowns available to Siegel's lemma when the polynomial is constructed. Hasse derivatives
lower the multidegree by the block degrees of the derivative order, which is what lets the
conditions of the construction be imposed on derivatives.

## Main definitions

* `MvPolynomial.IsMultiHomogeneous d P`: `P` is homogeneous of degree `d h` in block `h`, for every
  block `h`.
* `MvPolynomial.multiMons d`: the finite set of exponent vectors of multidegree `d`.

## Main results

* `MvPolynomial.isMultiHomogeneous_iff`: the characterization by the monomials occurring in `P`,
  and `MvPolynomial.isMultiHomogeneous_iff_support_subset`, the same through `multiMons`.
* `MvPolynomial.card_multiMons`: `multiMons d` has `∏ h, (card ι + d h - 1).choose (d h)`
  elements.
* `MvPolynomial.IsMultiHomogeneous.mul`, `.pow`, `.prod`, `.add`, `.sum`: multidegrees add
  under products and are preserved by sums.
* `MvPolynomial.IsMultiHomogeneous.isHomogeneous`: a multihomogeneous polynomial is homogeneous of
  total degree `∑ h, d h`, and `MvPolynomial.IsMultiHomogeneous.degreeOf_le` bounds the degree in
  each variable of block `h` by `d h`.
* `MvPolynomial.IsMultiHomogeneous.hasseDeriv`: the Hasse derivative of order `I` is
  multihomogeneous of multidegree `fun h ↦ d h - ∑ i, I (h, i)`, and
  `MvPolynomial.IsMultiHomogeneous.sum_le_of_hasseDeriv_ne_zero`: if it is nonzero, then
  `∑ i, I (h, i) ≤ d h` for every block.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press
  (2006), §7.5.14 and Lemma 7.5.15.
* W. M. Schmidt, *Diophantine Approximation*, Lecture Notes in Mathematics 785, Springer (1980),
  Chapter VI.
-/

public section

open Finset

namespace MvPolynomial

variable {R κ ι : Type*} [CommSemiring R] [DecidableEq κ]

/-- A polynomial in the variables `X (h, i)`, grouped into blocks indexed by `h : κ`, is
*multihomogeneous of multidegree `d`* if it is homogeneous of degree `d h` in the variables
`X (h, i)` of block `h`, for every block `h`. -/
def IsMultiHomogeneous (d : κ → ℕ) (P : MvPolynomial (κ × ι) R) : Prop :=
  ∀ h, P.IsWeightedHomogeneous (fun p : κ × ι ↦ if p.1 = h then 1 else 0) (d h)

variable {d e : κ → ℕ} {P Q : MvPolynomial (κ × ι) R}

theorem isMultiHomogeneous_iff_forall_isWeightedHomogeneous :
    IsMultiHomogeneous d P ↔
      ∀ h, P.IsWeightedHomogeneous (fun p : κ × ι ↦ if p.1 = h then 1 else 0) (d h) :=
  Iff.rfl

/-- A multihomogeneous polynomial is homogeneous of degree `d h` in block `h`. -/
theorem IsMultiHomogeneous.isWeightedHomogeneous (hP : IsMultiHomogeneous d P) (h : κ) :
    P.IsWeightedHomogeneous (fun p : κ × ι ↦ if p.1 = h then 1 else 0) (d h) :=
  hP h

section Fintype

variable [Fintype ι]

/-- `P` is multihomogeneous of multidegree `d` if and only if every monomial occurring in `P` has
degree `d h` in the variables of block `h`. -/
theorem isMultiHomogeneous_iff :
    IsMultiHomogeneous d P ↔ ∀ n, P.coeff n ≠ 0 → ∀ h, ∑ i, n (h, i) = d h := by
  simp only [isMultiHomogeneous_iff_forall_isWeightedHomogeneous, IsWeightedHomogeneous,
    Finsupp.weight_ite_fst_eq_sum]
  exact ⟨fun H n hn h ↦ H h hn, fun H h n hn ↦ H n hn h⟩

/-- A coefficient of a multihomogeneous polynomial vanishes at every exponent vector whose
degree in some block `h` differs from `d h`. -/
theorem IsMultiHomogeneous.coeff_eq_zero (hP : IsMultiHomogeneous d P) {n : κ × ι →₀ ℕ} {h : κ}
    (hn : ∑ i, n (h, i) ≠ d h) : P.coeff n = 0 := by
  by_contra hc
  exact hn (isMultiHomogeneous_iff.mp hP n hc h)

end Fintype

/-- The degree of a multihomogeneous polynomial in a variable of block `h` is at most `d h`. -/
theorem IsMultiHomogeneous.degreeOf_le (hP : IsMultiHomogeneous d P) (h : κ) (i : ι) :
    degreeOf (h, i) P ≤ d h := by
  rw [degreeOf_le_iff]
  intro n hn
  rw [← hP h (mem_support_iff.mp hn)]
  exact Finsupp.le_weight _ (by simp) n

/-- A multihomogeneous polynomial of multidegree `d` is homogeneous of total degree `∑ h, d h`. -/
theorem IsMultiHomogeneous.isHomogeneous [Fintype κ] [Finite ι] (hP : IsMultiHomogeneous d P) :
    P.IsHomogeneous (∑ h, d h) := by
  have := Fintype.ofFinite ι
  intro n hn
  rw [Pi.one_def, ← Finsupp.degree_eq_weight_one, Finsupp.degree_eq_sum, Fintype.sum_prod_type]
  exact sum_congr rfl fun h _ ↦ isMultiHomogeneous_iff.mp hP n hn h

theorem isMultiHomogeneous_zero (d : κ → ℕ) : IsMultiHomogeneous d (0 : MvPolynomial (κ × ι) R) :=
  fun _ ↦ isWeightedHomogeneous_zero _ _ _

/-- A constant is multihomogeneous of multidegree `0`. -/
theorem isMultiHomogeneous_C (r : R) : IsMultiHomogeneous 0 (C r : MvPolynomial (κ × ι) R) :=
  fun _ ↦ isWeightedHomogeneous_C _ r

theorem isMultiHomogeneous_one : IsMultiHomogeneous 0 (1 : MvPolynomial (κ × ι) R) :=
  fun _ ↦ isWeightedHomogeneous_one R _

/-- The variable `X (h, i)` is multihomogeneous of multidegree `Pi.single h 1`: degree one in its
own block and zero in every other block. -/
theorem isMultiHomogeneous_X (h : κ) (i : ι) :
    IsMultiHomogeneous (Pi.single h 1) (X (h, i) : MvPolynomial (κ × ι) R) := by
  intro h'
  convert isWeightedHomogeneous_X R (fun p : κ × ι ↦ if p.1 = h' then 1 else 0) (h, i) using 1
  simp [Pi.single_apply, eq_comm]

/-- A monomial is multihomogeneous of multidegree `d` when its exponent vector has degree `d h`
in every block `h`. -/
theorem isMultiHomogeneous_monomial [Fintype ι] {n : κ × ι →₀ ℕ} (hn : ∀ h, ∑ i, n (h, i) = d h)
    (r : R) : IsMultiHomogeneous d (monomial n r) :=
  fun h ↦ isWeightedHomogeneous_monomial _ _ _ (by rw [Finsupp.weight_ite_fst_eq_sum, hn])

theorem IsMultiHomogeneous.add (hP : IsMultiHomogeneous d P) (hQ : IsMultiHomogeneous d Q) :
    IsMultiHomogeneous d (P + Q) :=
  fun h ↦ (hP h).add (hQ h)

theorem IsMultiHomogeneous.sum {α : Type*} (s : Finset α) (φ : α → MvPolynomial (κ × ι) R)
    (hφ : ∀ a ∈ s, IsMultiHomogeneous d (φ a)) : IsMultiHomogeneous d (∑ a ∈ s, φ a) :=
  fun h ↦ IsWeightedHomogeneous.sum s φ (d h) fun a ha ↦ hφ a ha h

/-- Multidegrees add under products. -/
theorem IsMultiHomogeneous.mul (hP : IsMultiHomogeneous d P) (hQ : IsMultiHomogeneous e Q) :
    IsMultiHomogeneous (d + e) (P * Q) :=
  fun h ↦ (hP h).mul (hQ h)

theorem IsMultiHomogeneous.C_mul (hP : IsMultiHomogeneous d P) (r : R) :
    IsMultiHomogeneous d (C r * P) :=
  fun h ↦ (hP h).C_mul r

theorem IsMultiHomogeneous.pow (hP : IsMultiHomogeneous d P) (k : ℕ) :
    IsMultiHomogeneous (k • d) (P ^ k) :=
  fun h ↦ (hP h).pow k

theorem IsMultiHomogeneous.prod {α : Type*} (s : Finset α) (φ : α → MvPolynomial (κ × ι) R)
    (d : α → κ → ℕ) (hφ : ∀ a ∈ s, IsMultiHomogeneous (d a) (φ a)) :
    IsMultiHomogeneous (∑ a ∈ s, d a) (∏ a ∈ s, φ a) := by
  intro h
  simpa only [Finset.sum_apply] using
    IsWeightedHomogeneous.prod s φ (fun a ↦ d a h) fun a ha ↦ hφ a ha h

/-- The multidegree of a nonzero multihomogeneous polynomial is unique. -/
theorem IsMultiHomogeneous.inj_right (hP₀ : P ≠ 0) (hd : IsMultiHomogeneous d P)
    (he : IsMultiHomogeneous e P) : d = e :=
  funext fun h ↦ (hd h).inj_right hP₀ (he h)

section Ring

variable {R : Type*} [CommRing R] {P Q : MvPolynomial (κ × ι) R}

theorem IsMultiHomogeneous.neg (hP : IsMultiHomogeneous d P) : IsMultiHomogeneous d (-P) :=
  fun h ↦ (hP h).neg

theorem IsMultiHomogeneous.sub (hP : IsMultiHomogeneous d P) (hQ : IsMultiHomogeneous d Q) :
    IsMultiHomogeneous d (P - Q) :=
  fun h ↦ (hP h).sub (hQ h)

end Ring

section HasseDeriv

variable [Fintype ι]

/-- The Hasse derivative of order `I` of a multihomogeneous polynomial of multidegree `d` is
multihomogeneous of the residual multidegree `fun h ↦ d h - ∑ i, I (h, i)`. -/
theorem IsMultiHomogeneous.hasseDeriv (hP : IsMultiHomogeneous d P) (I : κ × ι →₀ ℕ) :
    IsMultiHomogeneous (fun h ↦ d h - ∑ i, I (h, i)) (MvPolynomial.hasseDeriv I P) :=
  fun h ↦ (hP h).hasseDeriv_sub_sum I

/-- A nonzero Hasse derivative of order `I` of a multihomogeneous polynomial of multidegree `d`
has order `∑ i, I (h, i) ≤ d h` in every block `h`. -/
theorem IsMultiHomogeneous.sum_le_of_hasseDeriv_ne_zero (hP : IsMultiHomogeneous d P)
    {I : κ × ι →₀ ℕ} (hI : MvPolynomial.hasseDeriv I P ≠ 0) (h : κ) : ∑ i, I (h, i) ≤ d h :=
  (hP h).sum_le_of_hasseDeriv_ne_zero hI

end HasseDeriv

section multiMons

variable [Fintype κ] [Fintype ι] [DecidableEq ι]

omit [DecidableEq κ] [DecidableEq ι] in
/-- The exponent vector on `κ × ι` assembled from one exponent vector on `ι` for each block. -/
private noncomputable def blockExponent : (κ → ι →₀ ℕ) ↪ (κ × ι →₀ ℕ) where
  toFun f := Finsupp.equivFunOnFinite.symm fun p ↦ f p.1 p.2
  inj' f g hfg := funext fun h ↦ Finsupp.ext fun i ↦ by
    simpa using DFunLike.congr_fun hfg (h, i)

omit [DecidableEq κ] [DecidableEq ι] in
private theorem blockExponent_apply (f : κ → ι →₀ ℕ) (p : κ × ι) :
    blockExponent f p = f p.1 p.2 :=
  rfl

variable (ι) in
/-- The exponent vectors of multidegree `d`: those of degree `d h` in block `h`, for every `h`.
These index the monomials of a multihomogeneous polynomial of multidegree `d`. -/
noncomputable def multiMons (d : κ → ℕ) : Finset (κ × ι →₀ ℕ) :=
  (Fintype.piFinset fun h ↦ (univ : Finset ι).finsuppAntidiag (d h)).map blockExponent

@[simp]
theorem mem_multiMons {n : κ × ι →₀ ℕ} : n ∈ multiMons ι d ↔ ∀ h, ∑ i, n (h, i) = d h := by
  simp only [multiMons, mem_map, Fintype.mem_piFinset, mem_finsuppAntidiag, subset_univ,
    and_true]
  constructor
  · rintro ⟨f, hf, rfl⟩ h
    simpa [blockExponent_apply] using hf h
  · intro hn
    refine ⟨fun h ↦ Finsupp.equivFunOnFinite.symm fun i ↦ n (h, i), fun h ↦ ?_, ?_⟩
    · simpa using hn h
    · ext p
      simp [blockExponent_apply]

/-- There are `∏ h, (card ι + d h - 1).choose (d h)` exponent vectors of multidegree `d`: a
monomial of degree `d h` in the `card ι` variables of each block `h`. When `ι` is nonempty the
factors equal `(d h + card ι - 1).choose (card ι - 1)`. -/
theorem card_multiMons (d : κ → ℕ) :
    #(multiMons ι d) = ∏ h, (Fintype.card ι + d h - 1).choose (d h) := by
  simp [multiMons, Fintype.card_piFinset, card_finsuppAntidiag_nat_eq_choose]

/-- `P` is multihomogeneous of multidegree `d` if and only if all its monomials have
multidegree `d`. -/
theorem isMultiHomogeneous_iff_support_subset :
    IsMultiHomogeneous d P ↔ P.support ⊆ multiMons ι d := by
  simp only [isMultiHomogeneous_iff, subset_iff, mem_support_iff, mem_multiMons]

end multiMons

/-! ### Examples -/

/-- `X (0, 0) * X (1, 0) ^ 2 + X (0, 1) * X (1, 0) * X (1, 1)`, in two blocks of two variables, is
multihomogeneous of multidegree `(1, 2)`. -/
example : IsMultiHomogeneous ![1, 2]
    (X (0, 0) * X (1, 0) ^ 2 + X (0, 1) * X (1, 0) * X (1, 1) :
      MvPolynomial (Fin 2 × Fin 2) ℤ) := by
  have h₁ : IsMultiHomogeneous (Pi.single 0 1 + 2 • Pi.single 1 1)
      (X (0, 0) * X (1, 0) ^ 2 : MvPolynomial (Fin 2 × Fin 2) ℤ) :=
    (isMultiHomogeneous_X 0 0).mul ((isMultiHomogeneous_X 1 0).pow 2)
  have h₂ : IsMultiHomogeneous (Pi.single 0 1 + Pi.single 1 1 + Pi.single 1 1)
      (X (0, 1) * X (1, 0) * X (1, 1) : MvPolynomial (Fin 2 × Fin 2) ℤ) :=
    ((isMultiHomogeneous_X 0 1).mul (isMultiHomogeneous_X 1 0)).mul (isMultiHomogeneous_X 1 1)
  have e₁ : (Pi.single 0 1 + 2 • Pi.single 1 1 : Fin 2 → ℕ) = ![1, 2] := by
    ext j; fin_cases j <;> rfl
  have e₂ : (Pi.single 0 1 + Pi.single 1 1 + Pi.single 1 1 : Fin 2 → ℕ) = ![1, 2] := by
    ext j; fin_cases j <;> rfl
  exact (e₁ ▸ h₁).add (e₂ ▸ h₂)

/-- `X (0, 0) + X (1, 0)` is homogeneous of degree one but not multihomogeneous: its two
monomials lie in different blocks. -/
example (d : Fin 2 → ℕ) :
    ¬ IsMultiHomogeneous d (X (0, 0) + X (1, 0) : MvPolynomial (Fin 2 × Fin 1) ℤ) := by
  intro hP
  have h₀ := isMultiHomogeneous_iff.mp hP (Finsupp.single (0, 0) 1) (by
    simp [coeff_X, Finsupp.single_eq_single_iff])
  have h₁ := isMultiHomogeneous_iff.mp hP (Finsupp.single (1, 0) 1) (by
    simp [coeff_X, Finsupp.single_eq_single_iff])
  have := (h₀ 0).trans (h₁ 0).symm
  simp [Finsupp.single_apply] at this

/-- With two blocks of three variables, there are `3 * 6 = 18` monomials of multidegree
`(1, 2)`. -/
example : #(multiMons (Fin 3) ![1, 2]) = 18 := by
  simp [card_multiMons, Fin.prod_univ_two, Nat.choose]

end MvPolynomial
