/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import TauCeti.RingTheory.MvPolynomial.HasseDeriv.WeightedHomogeneous

import TauCeti.Algebra.MvPolynomial.Monomial

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

For two-variable blocks (`ι = Fin 2`), `MvPolynomial.blockDehomogenize` sets `X (h, 0) ↦ 1` and
`X (h, 1) ↦ X h`, recovering an affine polynomial in `MvPolynomial κ R` without losing
coefficients or nonvanishing when `P` is multihomogeneous.

## Main definitions

* `MvPolynomial.IsMultiHomogeneous d P`: `P` is homogeneous of degree `d h` in block `h`, for every
  block `h`.
* `MvPolynomial.multiMons d`: the finite set of exponent vectors of multidegree `d`.
* `MvPolynomial.blockDehomogenize`: the `R`-algebra homomorphism
  `MvPolynomial (κ × Fin 2) R →ₐ[R] MvPolynomial κ R` setting `X (h, 0) ↦ 1` and `X (h, 1) ↦ X h`.

## Main results

* `MvPolynomial.isMultiHomogeneous_iff`: the characterization by the monomials occurring in `P`,
  and `MvPolynomial.isMultiHomogeneous_iff_support_subset`, the same through `multiMons`.
* `MvPolynomial.isMultiHomogeneous_rename_iff`: blockwise injective renaming preserves and reflects
  `IsMultiHomogeneous`.
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
* `MvPolynomial.coeff_blockDehomogenize_of_isMultiHomogeneous`,
  `MvPolynomial.mem_support_blockDehomogenize_iff_of_isMultiHomogeneous`,
  `MvPolynomial.blockDehomogenize_ne_zero_of_isMultiHomogeneous`, and
  `MvPolynomial.degreeOf_blockDehomogenize_le`: coefficient preservation, support projection,
  nonvanishing, and partial-degree bounds under `blockDehomogenize`.

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
theorem IsMultiHomogeneous.isHomogeneous [Fintype κ] (hP : IsMultiHomogeneous d P) :
    P.IsHomogeneous (∑ h, d h) := by
  intro n hn
  rw [← sum_congr rfl fun h _ ↦ hP h hn]
  simp only [Finsupp.weight_apply, Finsupp.sum, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Pi.one_apply]
  rw [sum_comm]
  simp

@[simp]
theorem isMultiHomogeneous_zero (d : κ → ℕ) : IsMultiHomogeneous d (0 : MvPolynomial (κ × ι) R) :=
  fun _ ↦ isWeightedHomogeneous_zero _ _ _

/-- A constant is multihomogeneous of multidegree `0`. -/
@[simp]
theorem isMultiHomogeneous_C (r : R) : IsMultiHomogeneous 0 (C r : MvPolynomial (κ × ι) R) :=
  fun _ ↦ isWeightedHomogeneous_C _ r

@[simp]
theorem isMultiHomogeneous_one : IsMultiHomogeneous 0 (1 : MvPolynomial (κ × ι) R) :=
  fun _ ↦ isWeightedHomogeneous_one R _

/-- The variable `X (h, i)` is multihomogeneous of multidegree `Pi.single h 1`: degree one in its
own block and zero in every other block. -/
@[simp]
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

variable (ι) in
/-- The exponent vectors of multidegree `d`: those of degree `d h` in block `h`, for every `h`.
These index the monomials of a multihomogeneous polynomial of multidegree `d`. -/
noncomputable def multiMons (d : κ → ℕ) : Finset (κ × ι →₀ ℕ) :=
  (Fintype.piFinset fun h ↦ (univ : Finset ι).finsuppAntidiag (d h)).map
    (Finsupp.equivFunOnFinite.symm.trans Finsupp.curryEquiv.symm).toEmbedding

@[simp]
theorem mem_multiMons {n : κ × ι →₀ ℕ} : n ∈ multiMons ι d ↔ ∀ h, ∑ i, n (h, i) = d h := by
  simp only [multiMons, mem_map, Fintype.mem_piFinset, mem_finsuppAntidiag, subset_univ,
    and_true]
  constructor
  · rintro ⟨f, hf, rfl⟩ h
    simpa [Finsupp.uncurry_apply] using hf h
  · intro hn
    exact ⟨n.curry, hn, by simp⟩

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

/-- Blockwise injective renaming preserves and reflects multihomogeneity of a given
multidegree. -/
theorem isMultiHomogeneous_rename_iff {ι' : Type*} {f : κ → ι' → ι}
    (hf : ∀ h, Function.Injective (f h)) (Q : MvPolynomial (κ × ι') R) :
    IsMultiHomogeneous d (rename (fun p : κ × ι' ↦ (p.1, f p.1 p.2)) Q) ↔
      IsMultiHomogeneous d Q := by
  classical
  let F : κ × ι' → κ × ι := fun p ↦ (p.1, f p.1 p.2)
  have hF : Function.Injective F := fun ⟨h₁, j₁⟩ ⟨h₂, j₂⟩ heq ↦ by
    rcases Prod.ext_iff.mp heq with ⟨rfl, hj⟩
    exact Prod.ext rfl (hf _ hj)
  have hweight (h : κ) (n : κ × ι' →₀ ℕ) :
      Finsupp.weight (fun p : κ × ι ↦ if p.1 = h then 1 else 0) (n.mapDomain F) =
        Finsupp.weight (fun p : κ × ι' ↦ if p.1 = h then 1 else 0) n := by
    simp only [Finsupp.weight_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    exact Finsupp.sum_mapDomain_index (fun _ ↦ by simp) (fun _ _ _ ↦ by split_ifs <;> rfl)
  constructor
  · intro H h n hn
    have hn' : (rename F Q).coeff (n.mapDomain F) ≠ 0 := by
      rwa [coeff_rename_mapDomain F hF]
    rw [← hweight h n]
    exact H h hn'
  · intro H h m hm
    have hm_mem : m ∈ (rename F Q).support := mem_support_iff.mpr hm
    rw [support_rename_of_injective hF] at hm_mem
    rcases Finset.mem_image.mp hm_mem with ⟨n, hn, rfl⟩
    rw [hweight h n]
    exact H h (mem_support_iff.mp hn)

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

namespace MvPolynomial

section BlockDehomogenize

variable {R S κ : Type*} [CommSemiring R] [CommSemiring S]

/-- Blockwise dehomogenization on two-variable blocks: sets `X (h, 0) ↦ 1` and `X (h, 1) ↦ X h`. -/
noncomputable def blockDehomogenize : MvPolynomial (κ × Fin 2) R →ₐ[R] MvPolynomial κ R :=
  aeval fun p ↦ if p.2 = 0 then 1 else X p.1

/-- `blockDehomogenize` unfolds to `aeval (fun p ↦ if p.2 = 0 then 1 else X p.1)`. -/
theorem blockDehomogenize_eq_aeval :
    blockDehomogenize (R := R) (κ := κ) = aeval fun p ↦ if p.2 = 0 then 1 else X p.1 := (rfl)

/-- `blockDehomogenize` specializes the `0`-th variable in each block to `1`. -/
@[simp]
theorem blockDehomogenize_X_zero (h : κ) :
    blockDehomogenize (R := R) (X (h, (0 : Fin 2))) = 1 := by
  simp [blockDehomogenize]

/-- `blockDehomogenize` sends the `1`-st variable in block `h` to `X h`. -/
@[simp]
theorem blockDehomogenize_X_one (h : κ) :
    blockDehomogenize (R := R) (X (h, (1 : Fin 2))) = X h := by
  simp [blockDehomogenize]

/-- Placing an affine polynomial into coordinate `1` of each block and applying `blockDehomogenize`
recovers the original polynomial. -/
@[simp]
theorem blockDehomogenize_rename_one (P : MvPolynomial κ R) :
    blockDehomogenize (rename (fun h : κ ↦ (h, (1 : Fin 2))) P) = P := by
  rw [blockDehomogenize, aeval_rename]
  exact aeval_X_left_apply P

/-- Evaluating `blockDehomogenize P` in an `R`-algebra evaluates `P` with coordinate `0` of each
block set to `1`. -/
@[simp]
theorem aeval_blockDehomogenize [Algebra R S] (P : MvPolynomial (κ × Fin 2) R) (a : κ → S) :
    aeval a (blockDehomogenize P) = aeval (fun p : κ × Fin 2 ↦ if p.2 = 0 then 1 else a p.1) P := by
  have h : (aeval a).comp (blockDehomogenize (R := R)) =
      aeval (fun p : κ × Fin 2 ↦ if p.2 = 0 then 1 else a p.1) := by
    ext ⟨b, i⟩
    fin_cases i <;> simp
  exact AlgHom.congr_fun h P

/-- Evaluating `blockDehomogenize P` at `a : κ → R` evaluates `P` with coordinate `0` of each
block set to `1`. -/
@[simp]
theorem eval_blockDehomogenize (P : MvPolynomial (κ × Fin 2) R) (a : κ → R) :
    eval a (blockDehomogenize P) = eval (fun p : κ × Fin 2 ↦ if p.2 = 0 then 1 else a p.1) P :=
  aeval_blockDehomogenize P a

/-- Mapping coefficients along a ring homomorphism commutes with `blockDehomogenize`. -/
@[simp]
theorem map_blockDehomogenize (f : R →+* S) (P : MvPolynomial (κ × Fin 2) R) :
    map f (blockDehomogenize P) = blockDehomogenize (map f P) := by
  induction P using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p w hp =>
    rcases w with ⟨h, i⟩
    fin_cases i <;> simp [hp]

/-- Dehomogenizing a monomial on two-variable blocks drops the `(·, 0)` exponents and retains the
`(·, 1)` exponents via `Finsupp.comapDomain`. -/
theorem blockDehomogenize_monomial (n : κ × Fin 2 →₀ ℕ) (c : R) :
    blockDehomogenize (monomial n c) =
      monomial (n.comapDomain (·, 1) (Prod.mk_left_injective 1).injOn) c := by
  let pairEquiv : κ ⊕ κ ≃ κ × Fin 2 :=
    { toFun := Sum.elim (·, 0) (·, 1)
      invFun p := if p.2 = 0 then .inl p.1 else .inr p.1
      left_inv x := by cases x <;> rfl
      right_inv := fun ⟨_, i⟩ ↦ by fin_cases i <;> rfl }
  let u : κ ⊕ κ →₀ ℕ := n.equivMapDomain pairEquiv.symm
  have hn : n = u.mapDomain pairEquiv := by
    ext p
    simp [u, Finsupp.mapDomain_equiv_apply]
  have hblock (Q : MvPolynomial (κ ⊕ κ) R) :
      blockDehomogenize (rename pairEquiv Q) =
        eval₂ (algebraMap R _) (Sum.elim (fun _ ↦ 1) X) Q := by
    rw [blockDehomogenize, aeval_rename, aeval_def]
    congr 1
    ext x
    cases x <;> rfl
  have hcomap : u.comapDomain Sum.inr Sum.inr_injective.injOn =
      n.comapDomain (·, 1) (Prod.mk_left_injective 1).injOn := by
    ext h
    simp [u, pairEquiv]
  conv_lhs =>
    rw [hn, ← rename_monomial, hblock, ← Finsupp.comapDomain_sumElim_comapDomain u,
      eval₂_monomial_sumElim_of_eq_one _ _ (fun _ ↦ rfl), hcomap]
  simp [monomial_eq, algebraMap_eq]

private theorem eq_of_block_sum_eq_of_snd_eq {e : κ → ℕ} {n₁ n₂ : κ × Fin 2 →₀ ℕ}
    (h₁ : ∀ h, n₁ (h, 0) + n₁ (h, 1) = e h) (h₂ : ∀ h, n₂ (h, 0) + n₂ (h, 1) = e h)
    (hsnd : ∀ h, n₁ (h, 1) = n₂ (h, 1)) : n₁ = n₂ := by
  ext ⟨h, i⟩
  rcases Fin.exists_fin_two.mp ⟨i, rfl⟩ with rfl | rfl
  · have := h₁ h; have := h₂ h; have := hsnd h; omega
  · exact hsnd h

/-- For a multihomogeneous polynomial `P` of multidegree `e` and any exponent `n` with block sums
`e`, the coefficient of `blockDehomogenize P` at the `(·, 1)`-projection of `n` is `P.coeff n`. -/
theorem coeff_blockDehomogenize_of_isMultiHomogeneous [DecidableEq κ] {e : κ → ℕ}
    {P : MvPolynomial (κ × Fin 2) R} (hP : IsMultiHomogeneous e P) {n : κ × Fin 2 →₀ ℕ}
    (hn : ∀ h, n (h, 0) + n (h, 1) = e h) :
    (blockDehomogenize P).coeff (n.comapDomain (·, 1) (Prod.mk_left_injective 1).injOn) =
      P.coeff n := by
  classical
  conv_lhs => rw [P.as_sum, map_sum, coeff_sum]
  simp_rw [blockDehomogenize_monomial, coeff_monomial]
  rw [Finset.sum_eq_single n]
  · simp
  · intro n' hn' hne
    refine ite_eq_right_iff.mpr fun hcomap ↦ (hne ?_).elim
    refine eq_of_block_sum_eq_of_snd_eq
      (fun h ↦ by
        simpa [Fin.sum_univ_two] using isMultiHomogeneous_iff.mp hP n' (mem_support_iff.mp hn') h)
      hn fun h ↦ ?_
    simpa [Finsupp.comapDomain_apply] using DFunLike.congr_fun hcomap h
  · intro hn_not
    simp [notMem_support_iff.mp hn_not]

/-- If `m h` exceeds the block degree `e h` in some block `h`, the `m`-coefficient of
`blockDehomogenize P` vanishes. -/
theorem coeff_blockDehomogenize_eq_zero_of_lt [DecidableEq κ] {e : κ → ℕ}
    {P : MvPolynomial (κ × Fin 2) R} (hP : IsMultiHomogeneous e P) {m : κ →₀ ℕ} {h : κ}
    (hm : e h < m h) : (blockDehomogenize P).coeff m = 0 := by
  classical
  conv_lhs => rw [P.as_sum, map_sum, coeff_sum]
  refine Finset.sum_eq_zero fun n hn ↦ ?_
  rw [blockDehomogenize_monomial, coeff_monomial, ite_eq_right_iff]
  intro hcomap
  have hn1 : n (h, 1) = m h := by
    simpa [Finsupp.comapDomain_apply] using DFunLike.congr_fun hcomap h
  have hnsum : n (h, 0) + n (h, 1) = e h := by
    simpa [Fin.sum_univ_two] using isMultiHomogeneous_iff.mp hP n (mem_support_iff.mp hn) h
  omega

/-- An exponent `m` lies in the support of `blockDehomogenize P` (for multihomogeneous `P`) if and
only if it is the `(·, 1)`-projection of an exponent in `P.support`. -/
theorem mem_support_blockDehomogenize_iff_of_isMultiHomogeneous [DecidableEq κ]
    {e : κ → ℕ} {P : MvPolynomial (κ × Fin 2) R} (hP : IsMultiHomogeneous e P) {m : κ →₀ ℕ} :
    m ∈ (blockDehomogenize P).support ↔ ∃ n ∈ P.support, ∀ h, n (h, 1) = m h := by
  classical
  constructor
  · intro hm
    rw [mem_support_iff] at hm
    conv at hm => lhs; rw [P.as_sum, map_sum, coeff_sum]
    obtain ⟨n, hn, hnc⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
    rw [blockDehomogenize_monomial, coeff_monomial] at hnc
    have hcomap : n.comapDomain (·, 1) (Prod.mk_left_injective 1).injOn = m := by
      by_contra hne
      simp [hne] at hnc
    exact ⟨n, hn, fun h ↦ by
      simpa [Finsupp.comapDomain_apply] using DFunLike.congr_fun hcomap h⟩
  · rintro ⟨n, hn, hnm⟩
    have hm_eq : m = n.comapDomain (·, 1) (Prod.mk_left_injective 1).injOn := by
      ext h
      simp [hnm h]
    have hnsum (h : κ) : n (h, 0) + n (h, 1) = e h := by
      simpa [Fin.sum_univ_two] using isMultiHomogeneous_iff.mp hP n (mem_support_iff.mp hn) h
    rw [mem_support_iff, hm_eq, coeff_blockDehomogenize_of_isMultiHomogeneous hP hnsum]
    exact mem_support_iff.mp hn

/-- Dehomogenizing a nonzero multihomogeneous polynomial remains nonzero. -/
theorem blockDehomogenize_ne_zero_of_isMultiHomogeneous [DecidableEq κ] {e : κ → ℕ}
    {P : MvPolynomial (κ × Fin 2) R} (hP : IsMultiHomogeneous e P) (hP0 : P ≠ 0) :
    blockDehomogenize P ≠ 0 := by
  classical
  obtain ⟨n, hn⟩ := support_nonempty.mpr hP0
  refine support_nonempty.mp ⟨n.comapDomain (·, 1) (Prod.mk_left_injective 1).injOn, ?_⟩
  exact (mem_support_blockDehomogenize_iff_of_isMultiHomogeneous hP).mpr
    ⟨n, hn, fun h ↦ by simp⟩

/-- The partial degree in block `h` of `blockDehomogenize P` is at most the multidegree `e h`. -/
theorem degreeOf_blockDehomogenize_le [DecidableEq κ] {e : κ → ℕ}
    {P : MvPolynomial (κ × Fin 2) R} (hP : IsMultiHomogeneous e P) (h : κ) :
    (blockDehomogenize P).degreeOf h ≤ e h := by
  refine degreeOf_le_iff.mpr fun m hm ↦ ?_
  by_contra! hlt
  exact mem_support_iff.mp hm (coeff_blockDehomogenize_eq_zero_of_lt hP hlt)

end BlockDehomogenize

end MvPolynomial
