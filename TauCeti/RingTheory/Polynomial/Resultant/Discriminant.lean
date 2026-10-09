/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CubicDiscriminant
public import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Tactic.NormDet
import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.FieldTheory.Separable
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.RingTheory.Discriminant
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
import TauCeti.RingTheory.Polynomial.Resultant.Basic
import TauCeti.RingTheory.Polynomial.Roots

/-!
# The discriminant of a polynomial as a product over pairs of roots

Mathlib defines `Polynomial.discr f` as the determinant of `f.sylvesterDeriv`, corrected by the
sign `(-1) ^ (n * (n - 1) / 2)` with `n = f.natDegree`. The division-free relation is that the
resultant of `f` and `f.derivative` equals this sign times `f.leadingCoeff * f.discr`
(`Polynomial.resultant_deriv`). What that definition does not say is what the discriminant
measures. This file proves the classical root-product formula

`(∏ i, (X - C (r i))).discr = ∏ i, ∏ j ∈ Ioi i, (r i - r j) ^ 2`

for a family of roots `r : Fin n → R` over an arbitrary commutative ring, together with the
consequences that read the formula: base change, and the criterion for a monic polynomial to be
separable. It also gives the coefficient formula for the discriminant of a monic quartic. The
depressed specialization of that formula is used to compare a quartic with its cubic resolvent.

## Main results

* `Polynomial.discr_prod_X_sub_C`, `Polynomial.discr_prod_X_sub_C_eq_sq`: the root-product
  formula, in its squared-product form and in the form `discr = δ ^ 2` for the Vandermonde-like
  product `δ = ∏_{i < j} (rᵢ - rⱼ)`. The second is the shape the discriminant test for
  containment in the alternating group is stated with, since a Galois automorphism permutes the
  roots and multiplies `δ` by the sign of that permutation.
* `Polynomial.Monic.discr_eq_prod_roots_sub_sq`: the same formula for a monic polynomial,
  written against a numbering `r : Fin f.natDegree → L` of its root multiset over an extension.
* `TauCeti.discrSqrt`, `TauCeti.discrSqrt_ne_zero`, `Polynomial.Monic.discrSqrt_sq`: the product
  of the differences of a numbering of the distinct roots, its nonvanishing, and the fact that
  its square is the discriminant for a monic separable polynomial.
* `Polynomial.Monic.prod_roots_eval_derivative`: the product of the derivative over the root
  multiset, which is the discriminant up to the same sign. This is the shape in which the
  discriminant of a minimal polynomial is a norm.
* `Polynomial.Monic.discr_mul`: the product formula for discriminants, with the square of the
  resultant as its cross term.
* `Polynomial.discr_prod_of_monic`: the same formula for a finite product of monic polynomials,
  with the pairwise resultants as cross terms.
* `Polynomial.discr_X_pow_sub_C`: the discriminant of a binomial `X ^ n - C a`.
* `TauCeti.discr_X_pow_five_add_C_mul_X_add_C`: the discriminant of `X⁵ + aX + b`.
* `TauCeti.not_isSquare_discr_X_pow_five_sub_C`: the discriminant `3125a⁴` of a pure quintic
  `X ^ 5 - C a` over `ℚ` with `a ≠ 0` is not a square.
* `TauCeti.discr_C_mul`, `TauCeti.isSquare_discr_iff_mem_range`: the scaling law and
  square-root criterion for a not-necessarily-monic polynomial. Scaling holds over an integral
  domain; the square-root criterion uses a base field and a domain containing the roots.
* `Polynomial.discr_map_of_natDegree_eq`, `Polynomial.Monic.discr_map`: base change whenever the
  degree is preserved, with monicity as a convenient sufficient condition.
* `Polynomial.Monic.isUnit_discr_iff`, `Polynomial.Monic.discr_ne_zero_iff`,
  `Polynomial.Monic.discr_ne_zero_iff_separable_map`: a monic polynomial is separable exactly
  when its discriminant is a unit; over a field that reads `discr f ≠ 0`, and over a domain the
  correct statement passes to the fraction field.
* `Polynomial.Monic.squarefree_of_discr_ne_zero`: over a domain, a monic polynomial with nonzero
  discriminant is squarefree.
* `Polynomial.discr_ne_zero_iff`: over a field, a nonzero polynomial that need not be monic is
  separable exactly when its discriminant is nonzero.
* `Polynomial.separable_map_iff_map_discr_ne_zero`,
  `Polynomial.Monic.separable_map_zmod_iff_not_dvd_discr`: the same criterion read along a ring
  homomorphism into a field, and its specialization to reduction of an integral polynomial modulo
  a prime.
* `Cubic.toPoly_discr`: the two discriminants of a cubic with nonzero leading coefficient agree,
  so that `Cubic.discr` and `Polynomial.discr` may be used interchangeably in degree three.
* `Polynomial.Monic.discr_of_natDegree_eq_four`, `TauCeti.discr_depressedQuartic`: the
  coefficient formula for a monic quartic and its depressed specialization, used to compare
  quartic and resolvent discriminants.
* `Algebra.discr_powerBasis_eq_minpoly_discr`: the algebra discriminant of a power basis agrees
  with the polynomial discriminant of the minimal polynomial of its generator.
## Implementation notes

The root-product formula is a universal polynomial identity, so it is stated over an arbitrary
commutative ring and proved by base change from `MvPolynomial (Fin n) ℤ`, which is a domain and
over which the roots are the variables themselves.

The separability criterion is *not* a universal identity, and the failure is recorded here:
`Polynomial.not_separable_X_pow_two_sub_one` shows that `X ^ 2 - 1` over `ℤ` has nonzero
discriminant `4` and is not `Polynomial.Separable`. Over a domain the criterion is therefore
formulated after passage to a fraction field.

The sign bookkeeping — folding the off-diagonal product over ordered pairs into a product over
unordered pairs, and evaluating `∑ i, #(Ioi i)` as `n * (n - 1) / 2` — follows the corresponding
step of `Algebra.discr_powerBasis_eq_prod''` in `Mathlib/RingTheory/Discriminant.lean`, and
reuses the same lemma `Finset.prod_prod_Ioi_mul_eq_prod_prod_off_diag`. No Mathlib code is
vendored.

## References

* H. Cohen, *A Course in Computational Algebraic Number Theory*, §3.3.2 and §6.3.
* S. Lang, *Algebra*, third edition, Chapter IV, §8.
-/

public section

open Finset Polynomial TauCeti

namespace Polynomial

variable {R S : Type*} [CommRing R] [CommRing S]

namespace Monic

variable {R : Type*} [CommRing R]

/-- For a monic polynomial, the resultant of `f` and `f.derivative`, taken at the degree bounds
`f.natDegree` and `f.natDegree - 1` that the Sylvester matrix of the discriminant uses, is the
discriminant up to the sign `(-1) ^ (n * (n - 1) / 2)`.

This is the monic case of `Polynomial.resultant_deriv`: the leading coefficient of that lemma is
`1`, and its positive-degree hypothesis is unnecessary, the constant polynomial `1` being
covered. -/
theorem resultant_deriv {f : R[X]} (hf : f.Monic) :
    f.resultant f.derivative f.natDegree (f.natDegree - 1) =
      (-1) ^ (f.natDegree * (f.natDegree - 1) / 2) * f.discr := by
  rcases Nat.eq_zero_or_pos f.natDegree with h | h
  · obtain rfl := eq_one_of_monic_natDegree_zero hf h
    have h1 : (1 : R[X]).discr = 1 := by simpa using discr_C (R := R) 1
    simp [h1]
  · rw [Polynomial.resultant_deriv (natDegree_pos_iff_degree_pos.mp h), hf.leadingCoeff,
      mul_one]

end Monic

/-- **The discriminant of a binomial.** Over any commutative ring,
`discr (X ^ n - C a) = (-1) ^ (n (n - 1) / 2) · nⁿ · (-a) ^ (n - 1)`; for `n = 0` both sides
are `1`. -/
@[simp] theorem discr_X_pow_sub_C (a : R) (n : ℕ) :
    (X ^ n - C a).discr = (-1) ^ (n * (n - 1) / 2) * (n : R) ^ n * (-a) ^ (n - 1) := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [pow_zero, ← C_1, ← C_sub, discr_C]
    simp
  nontriviality R
  have hf : (X ^ n - C a).Monic := monic_X_pow_sub_C a hn
  have h := hf.resultant_deriv
  rw [natDegree_X_pow_sub_C, derivative_sub, derivative_X_pow, derivative_C, sub_zero,
    resultant_C_mul_right, resultant_X_pow_right _ _ _ natDegree_X_pow_sub_C.le,
    coeff_sub, coeff_X_pow, coeff_C_zero, (Nat.even_mul_pred_self n).neg_one_pow, one_mul] at h
  simp only [Ne.symm hn, ↓reduceIte, zero_sub] at h
  -- The sign `(-1) ^ (n (n - 1) / 2)` squares to `1`, so it can be moved across the identity.
  have hsq : ((-1 : R) ^ (n * (n - 1) / 2)) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  calc (X ^ n - C a).discr
      = ((-1 : R) ^ (n * (n - 1) / 2)) ^ 2 * (X ^ n - C a).discr := by rw [hsq, one_mul]
    _ = (-1) ^ (n * (n - 1) / 2) * ((-1) ^ (n * (n - 1) / 2) * (X ^ n - C a).discr) := by ring
    _ = _ := by rw [← h]; ring

end Polynomial

namespace TauCeti

/-- The discriminant `3125a⁴` of a pure quintic `X⁵ - a` over `ℚ`, with `a ≠ 0`, is not a
square in `ℚ`. -/
theorem not_isSquare_discr_X_pow_five_sub_C {a : ℚ} (ha : a ≠ 0) :
    ¬ IsSquare (X ^ 5 - C a : ℚ[X]).discr := by
  rw [discr_X_pow_sub_C]
  rintro ⟨r, hr⟩
  have h5 : IsSquare (5 : ℚ) := ⟨r / (25 * a ^ 2), by
    rw [div_mul_div_comm, eq_div_iff (by positivity)]
    linear_combination hr⟩
  exact absurd h5 (by norm_num)

end TauCeti

namespace Polynomial

section Reindex

variable {R S : Type*} [Semiring R] [Semiring S]

/-- Mapping coefficients preserves `sylvesterDeriv` after transporting its degree-dependent
indices. -/
theorem sylvesterDeriv_map {f : R[X]} (φ : R →+* S)
    (hdeg : (f.map φ).natDegree = f.natDegree) :
    Matrix.reindex (finCongr (by rw [hdeg])) (finCongr (by rw [hdeg]))
      (f.map φ).sylvesterDeriv = φ.mapMatrix f.sylvesterDeriv := by
  classical
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, RingHom.mapMatrix_apply,
    Matrix.map_apply, sylvesterDeriv, hdeg]
  by_cases hzero : f.natDegree = 0
  · simp [hzero]
  · simp [hzero, hdeg, Matrix.updateRow_apply, Fin.ext_iff, sylvester, derivative_map,
      Fin.addCases, apply_ite φ]

end Reindex

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Base change of the discriminant along a ring morphism that preserves the degree. -/
theorem discr_map_of_natDegree_eq {f : R[X]} (φ : R →+* S)
    (hdeg : (f.map φ).natDegree = f.natDegree) :
    (f.map φ).discr = φ f.discr := by
  classical
  simp only [discr, hdeg, map_mul, map_pow, map_neg, map_one]
  congr 1
  rw [RingHom.map_det]
  let e : Fin ((f.map φ).natDegree - 1 + (f.map φ).natDegree) ≃
      Fin (f.natDegree - 1 + f.natDegree) := finCongr (by rw [hdeg])
  rw [← Matrix.det_reindex_self e]
  congr 1
  exact sylvesterDeriv_map φ hdeg

namespace Monic

/-- Base change of the discriminant along a ring morphism, for a monic polynomial. Monicity
ensures that the degree is preserved. -/
@[simp]
theorem discr_map {f : R[X]} (hf : f.Monic) (φ : R →+* S) :
    (f.map φ).discr = φ f.discr := by
  nontriviality S
  exact discr_map_of_natDegree_eq φ (hf.natDegree_map φ)

/-- The discriminant of a product of monic polynomials is the product of their discriminants and
the square of their resultant. -/
theorem discr_mul {f g : R[X]} (hf : f.Monic) (hg : g.Monic) :
    (f * g).discr = f.discr * g.discr * (f.resultant g) ^ 2 := by
  -- A monic factor of degree zero is `1`, and both sides are then the discriminant of the other
  -- factor; the argument below needs both degrees positive.
  by_cases hf0 : f.natDegree = 0
  · obtain rfl := eq_one_of_monic_natDegree_zero hf hf0
    have h1 : (1 : R[X]).discr = 1 := by simpa using discr_C (R := R) 1
    simp [h1]
  by_cases hg0 : g.natDegree = 0
  · obtain rfl := eq_one_of_monic_natDegree_zero hg hg0
    have h1 : (1 : R[X]).discr = 1 := by simpa using discr_C (R := R) 1
    simp [h1]
  -- All resultants against `(f * g).derivative` are taken at the single degree bound `d`, which
  -- is the degree bound `Polynomial.discr` uses for `f * g`; the next block records that every
  -- polynomial the argument feeds to a resultant stays inside that bound.
  let d := f.natDegree + g.natDegree - 1
  have hdeg : (f * g).natDegree = f.natDegree + g.natDegree := hf.natDegree_mul hg
  have hderiv : (f * g).derivative.natDegree ≤ d := by
    dsimp only [d]
    rw [← hdeg]
    exact natDegree_derivative_le _
  have hpf : g.derivative.natDegree + f.natDegree ≤ d := by
    have := natDegree_derivative_le g
    dsimp only [d]
    omega
  have hpg : f.derivative.natDegree + g.natDegree ≤ d := by
    have := natDegree_derivative_le f
    dsimp only [d]
    omega
  have hpf' : f.natDegree + g.derivative.natDegree ≤ d := by omega
  have hmul_f : (f.derivative * g).natDegree ≤ d := natDegree_mul_le.trans hpg
  have hmul_g : (f * g.derivative).natDegree ≤ d := natDegree_mul_le.trans hpf'
  -- Step 1: expand `(f * g)' = f' * g + f * g'`. Against `f` the second summand is a multiple of
  -- `f`, so it drops out of the resultant, leaving `res(f, f') * res(f, g)`; against `g` the
  -- first summand drops out symmetrically.
  have hresf : f.resultant (f * g).derivative f.natDegree d =
      f.resultant f.derivative * f.resultant g := by
    rw [derivative_mul, resultant_add_mul_right _ _ _ _ _ hpf le_rfl,
      hf.resultant_of_le hmul_f,
      ← hf.resultant_of_le natDegree_mul_le,
      resultant_mul_right _ _ _ _ le_rfl]
  have hresg : g.resultant (f * g).derivative g.natDegree d =
      g.resultant f * g.resultant g.derivative := by
    rw [derivative_mul, mul_comm f.derivative g, add_comm,
      resultant_add_mul_right _ _ _ _ _ hpg le_rfl,
      hg.resultant_of_le hmul_g,
      ← hg.resultant_of_le natDegree_mul_le,
      resultant_mul_right _ _ _ _ le_rfl]
  -- Step 2: multiplicativity of the resultant in its left argument turns
  -- `res(f * g, (f * g)')` into the product of the two resultants just computed.
  have hmul := resultant_mul_left f g (f * g).derivative d hderiv
  rw [hresf, hresg] at hmul
  -- Step 3: read each resultant of a polynomial against its own derivative as a discriminant,
  -- and swap the arguments of the crossed resultant `res(g, f)`.
  have hfd : f.resultant f.derivative =
      (-1) ^ (f.natDegree * (f.natDegree - 1) / 2) * f.discr := by
    rw [← hf.resultant_of_le (natDegree_derivative_le f),
      hf.resultant_deriv]
  have hgd : g.resultant g.derivative =
      (-1) ^ (g.natDegree * (g.natDegree - 1) / 2) * g.discr := by
    rw [← hg.resultant_of_le (natDegree_derivative_le g),
      hg.resultant_deriv]
  have hcomm : g.resultant f = (-1) ^ (g.natDegree * f.natDegree) * f.resultant g :=
    resultant_comm g f g.natDegree f.natDegree
  -- Step 4: the same reading on the left-hand side produces the sign
  -- `(-1) ^ ((m + n) * (m + n - 1) / 2)`. The triangular number of a sum splits as the two
  -- triangular numbers plus the cross term `m * n` — Vandermonde's identity `Nat.add_choose_eq`
  -- at `k = 2` — so that sign is the two signs collected in Step 3 together with `(-1) ^ (m * n)`
  -- from `hcomm`. All of them cancel, being units.
  have htriangle : ∀ m n : ℕ,
      (m + n) * (m + n - 1) / 2 = m * (m - 1) / 2 + n * (n - 1) / 2 + m * n := by
    intro m n
    have h := Nat.add_choose_eq m n 2
    simp [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
      Nat.choose_two_right] at h
    omega
  have hdisc := (hf.mul hg).resultant_deriv
  rw [hdeg] at hdisc
  dsimp only [d] at hmul
  rw [hmul, hfd, hgd, hcomm,
    htriangle, pow_add, pow_add] at hdisc
  ring_nf at hdisc
  have hu : IsUnit (((-1 : R) ^ (f.natDegree * g.natDegree)) *
      (-1) ^ (f.natDegree * (f.natDegree - 1) / 2) *
      (-1) ^ (g.natDegree * (g.natDegree - 1) / 2)) :=
    ((isUnit_one.neg.pow _).mul (isUnit_one.neg.pow _)).mul (isUnit_one.neg.pow _)
  apply hu.mul_right_injective
  ring_nf
  convert hdisc.symm using 1
  all_goals ring

end Monic

/-- The discriminant of a finite product of monic polynomials is the product of their
discriminants and the square of the product of their pairwise resultants. This is
`Polynomial.Monic.discr_mul` iterated; the pairs are taken once each, ordered by the index. -/
theorem discr_prod_of_monic {ι : Type*} [LinearOrder ι] (s : Finset ι) (f : ι → R[X])
    (hf : ∀ i ∈ s, (f i).Monic) :
    (∏ i ∈ s, f i).discr =
      (∏ i ∈ s, (f i).discr) * (∏ j ∈ s, ∏ i ∈ s with i < j, (f i).resultant (f j)) ^ 2 := by
  nontriviality R
  induction s using Finset.induction_on_max with
  | empty => simpa using discr_C (R := R) 1
  | insert m s hm ih =>
    -- Split off the largest index `m`: its resultants with the earlier factors are exactly the
    -- new pairs, and no earlier pair involves it.
    have hms : m ∉ s := fun h ↦ (hm m h).false
    have hf' : ∀ i ∈ s, (f i).Monic := fun i hi ↦ hf i (mem_insert_of_mem hi)
    have hP : (∏ i ∈ s, f i).Monic := monic_prod_of_monic _ _ hf'
    rw [prod_insert hms, mul_comm, hP.discr_mul (hf m (mem_insert_self m s)), ih hf',
      resultant_prod_left s f (f m) _
        (by rw [prod_eq_one fun i hi ↦ (hf' i hi).leadingCoeff]; exact one_ne_zero) le_rfl,
      prod_insert hms, prod_insert hms]
    have hnew : ∏ i ∈ insert m s with i < m, (f i).resultant (f m) =
        ∏ i ∈ s, (f i).resultant (f m) := by
      rw [filter_insert, filter_true_of_mem hm]
      simp
    have hold : ∀ j ∈ s, ∏ i ∈ insert m s with i < j, (f i).resultant (f j) =
        ∏ i ∈ s with i < j, (f i).resultant (f j) := fun j hj ↦ by
      rw [filter_insert]
      simp [not_lt.mpr (hm j hj).le]
    rw [hnew, prod_congr rfl hold]
    ring

namespace Monic

/-! ### The root-product formula -/

/-- For a monic polynomial that splits, the product of the derivative over the root multiset is
the discriminant, up to the sign `(-1) ^ (n * (n - 1) / 2)`. After base change and identification
of the roots with conjugates, this yields the corresponding norm formula. -/
theorem prod_roots_eval_derivative [IsDomain R] {f : R[X]} (hf : f.Monic)
    (hs : f.Splits) : (f.roots.map fun a ↦ eval a f.derivative).prod =
      (-1) ^ (f.natDegree * (f.natDegree - 1) / 2) * f.discr := by
  have key := resultant_eq_prod_eval f f.derivative (f.natDegree - 1)
    (natDegree_derivative_le f) hs
  rwa [hf.resultant_deriv, hf.leadingCoeff, one_pow, one_mul, eq_comm] at key

end Monic

/-- The root-product formula over an integral domain, where the resultant of `f` and its
derivative may be evaluated over the roots of `f`. -/
private theorem discr_prod_X_sub_C_of_isDomain [IsDomain R] {n : ℕ} (r : Fin n → R) :
    (∏ i, (X - C (r i))).discr = ∏ i, ∏ j ∈ Ioi i, (r i - r j) ^ 2 := by
  classical
  set f : R[X] := ∏ i, (X - C (r i)) with hfdef
  have hmon : f.Monic := monic_prod_X_sub_C r univ
  have hdeg : f.natDegree = n := by simp [hfdef]
  have hsplits : f.Splits := Splits.prod fun i _ ↦ Splits.X_sub_C (r i)
  -- Rewrite `f` as a product over the multiset of roots, the shape Mathlib's root lemmas take.
  have hfms : f = (Multiset.map (fun a ↦ X - C a) (univ.val.map r)).prod := by
    rw [hfdef, Finset.prod_eq_multiset_prod, Multiset.map_map]
    rfl
  have hroots : f.roots = univ.val.map r := by
    rw [hfms, roots_multiset_prod_X_sub_C]
  -- The derivative of `f` at the root `r i` is the product of the other root differences; this
  -- is `Polynomial.eval_multiset_prod_X_sub_C_derivative`, after erasing the index `i` rather
  -- than one occurrence of the value `r i`.
  have hderiv : ∀ i, eval (r i) f.derivative = ∏ j ∈ univ.erase i, (r i - r j) := by
    intro i
    have hmem : r i ∈ univ.val.map r :=
      Multiset.mem_map_of_mem r (Finset.mem_val.mpr (mem_univ i))
    have herase : (univ.val.map r).erase (r i) = (univ.erase i).val.map r := by
      rw [Finset.erase_val]
      conv_lhs => rw [← Multiset.cons_erase (Finset.mem_val.mpr (mem_univ i))]
      rw [Multiset.map_cons, Multiset.erase_cons_head]
    rw [hfms, eval_multiset_prod_X_sub_C_derivative hmem, herase, Finset.prod_eq_multiset_prod,
      Multiset.map_map]
    rfl
  -- Evaluate the derivative of `f` over the roots of `f`.
  have key := hmon.prod_roots_eval_derivative hsplits
  rw [hroots, Multiset.map_map, ← Finset.prod_eq_multiset_prod, eq_comm] at key
  simp only [Function.comp_apply, hderiv, ← Finset.compl_singleton] at key
  -- Fold the off-diagonal product into a product over unordered pairs.
  rw [← Finset.prod_prod_Ioi_mul_eq_prod_prod_off_diag fun a b ↦ r b - r a] at key
  have hsign : ∀ i : Fin n, ∀ j ∈ Ioi i, (r i - r j) * (r j - r i) = -1 * (r i - r j) ^ 2 :=
    fun i j _ ↦ by ring
  rw [Finset.prod_congr rfl fun i _ ↦ Finset.prod_congr rfl (hsign i), hdeg] at key
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow_eq_pow_sum] at key
  have hcard : ∑ i : Fin n, #(Ioi i) = n * (n - 1) / 2 := by
    simp only [Fin.card_Ioi, Fin.sum_univ_eq_sum_range fun i ↦ n - 1 - i]
    rw [Finset.sum_range_reflect (fun i ↦ i) n, Finset.sum_range_id]
  rw [hcard] at key
  exact ((isUnit_one.neg.pow (n * (n - 1) / 2)).mul_right_injective key)

/-- **The root-product formula for the discriminant.** The discriminant of a product of linear
factors is the square of the Vandermonde-like product of the differences of the roots. This is a
universal polynomial identity, so it holds over any commutative ring, with the roots repeated
according to multiplicity. -/
theorem discr_prod_X_sub_C {n : ℕ} (r : Fin n → R) :
    (∏ i, (X - C (r i))).discr = ∏ i, ∏ j ∈ Ioi i, (r i - r j) ^ 2 := by
  set φ : MvPolynomial (Fin n) ℤ →+* R := MvPolynomial.eval₂Hom (Int.castRingHom R) r with hφ
  have hmon : (∏ i, (X - C (MvPolynomial.X i : MvPolynomial (Fin n) ℤ))).Monic :=
    monic_prod_X_sub_C _ _
  have hmap : (∏ i, (X - C (MvPolynomial.X i : MvPolynomial (Fin n) ℤ))).map φ =
      ∏ i, (X - C (r i)) := by
    simp [Polynomial.map_prod, hφ]
  have key := hmon.discr_map φ
  rw [hmap] at key
  rw [key, discr_prod_X_sub_C_of_isDomain]
  simp only [map_prod, map_pow, map_sub, hφ, MvPolynomial.eval₂Hom_X']

/-- The root-product formula, in the form `discr f = δ ^ 2` for the product `δ` of the differences
of the roots taken over pairs `i < j`. This is the form the discriminant test for containment in
the alternating group reads: a permutation of the roots multiplies `δ` by its sign. -/
theorem discr_prod_X_sub_C_eq_sq {n : ℕ} (r : Fin n → R) :
    (∏ i, (X - C (r i))).discr = (∏ i, ∏ j ∈ Ioi i, (r i - r j)) ^ 2 := by
  rw [discr_prod_X_sub_C, ← Finset.prod_pow]
  exact Finset.prod_congr rfl fun i _ ↦ Finset.prod_pow _ 2 _

namespace Monic

/-- The root-product formula for a monic polynomial that splits after base change, written against
a numbering `r : Fin n → L` of the root multiset with arbitrary cardinality `n`. The complete
numbering, by `Fin f.natDegree`, is `Polynomial.Monic.discr_eq_prod_roots_sub_sq`. -/
private theorem discr_eq_prod_roots_sub_sq_of_splits {L : Type*}
    [CommRing L] [IsDomain L] [Algebra R L] {f : R[X]} (hf : f.Monic)
    (hs : (f.map (algebraMap R L)).Splits) {n : ℕ} {r : Fin n → L}
    (hr : (f.map (algebraMap R L)).roots = univ.val.map r) :
    algebraMap R L f.discr = ∏ i, ∏ j ∈ Ioi i, (r i - r j) ^ 2 := by
  have hfeq : f.map (algebraMap R L) = ∏ i, (X - C (r i)) := by
    rw [hs.eq_prod_roots_of_monic (hf.map _), hr, Finset.prod_eq_multiset_prod, Multiset.map_map]
    rfl
  rw [← hf.discr_map, hfeq, discr_prod_X_sub_C]

/-- **The root-product formula for a monic polynomial.** Number the roots of a monic `f` over an
extension `L`, with multiplicity, as `r : Fin f.natDegree → L`. Then the discriminant of `f` is
the square of the Vandermonde-like product of the differences of the roots. Numbering the whole
root multiset by `Fin f.natDegree` already says that `f` splits over `L`, so no splitting
hypothesis appears. -/
theorem discr_eq_prod_roots_sub_sq {L : Type*} [CommRing L] [IsDomain L]
    [Algebra R L] {f : R[X]} (hf : f.Monic) {r : Fin f.natDegree → L}
    (hr : (f.map (algebraMap R L)).roots = univ.val.map r) :
    algebraMap R L f.discr = ∏ i, ∏ j ∈ Ioi i, (r i - r j) ^ 2 := by
  have hcard : (f.map (algebraMap R L)).roots.card = (f.map (algebraMap R L)).natDegree := by
    rw [hr, hf.natDegree_map]
    simp
  exact hf.discr_eq_prod_roots_sub_sq_of_splits (splits_iff_card_roots.mpr hcard) hr

end Monic

end Polynomial

/-! ### The square root of the discriminant -/

namespace TauCeti

section DiscrSqrt

section Domain

variable {F : Type*} [CommRing F] {E : Type*} [CommRing E] [IsDomain E] [Algebra F E] {f : F[X]}

/-- The product `∏_{i < j} (rᵢ - rⱼ)` of the differences of the roots of `f` in `E`, taken along a
numbering `e` of the root set.

For monic separable `f` this is a square root of the discriminant, by
`Polynomial.Monic.discrSqrt_sq`. It is only *a* square root: `TauCeti.discrSqrt_trans` shows that
changing the numbering by an odd permutation changes the sign. The root set carries no order, so
the numbering is an explicit argument and is never fixed globally. -/
def discrSqrt (e : Fin f.natDegree ≃ f.rootSet E) : E :=
  ∏ i, ∏ j ∈ Ioi i, ((e i : E) - (e j : E))

/-- The unfolding equation for the square root of the discriminant. -/
theorem discrSqrt_def (e : Fin f.natDegree ≃ f.rootSet E) :
    discrSqrt e = ∏ i, ∏ j ∈ Ioi i, ((e i : E) - (e j : E)) := (rfl)

/-- Renumbering the roots by a permutation `π` multiplies the product of the root differences by
the sign of `π`. This is the alternating behaviour that makes the discriminant test work. -/
@[simp]
theorem discrSqrt_trans (e : Fin f.natDegree ≃ f.rootSet E) (π : Equiv.Perm (Fin f.natDegree)) :
    discrSqrt (π.trans e) = Equiv.Perm.sign π • discrSqrt e := by
  have h := π.prod_Ioi_comp_eq_sign_mul_prod
    (f := fun i j ↦ ((e i : E) - (e j : E))) fun i j ↦ (neg_sub _ _).symm
  simp only [discrSqrt_def, Equiv.trans_apply, h, Units.smul_def, zsmul_eq_mul]

/-- The product of the differences of a numbering of distinct roots is nonzero. -/
theorem discrSqrt_ne_zero (e : Fin f.natDegree ≃ f.rootSet E) :
    discrSqrt e ≠ 0 := by
  rw [discrSqrt_def]
  refine Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun j hj => ?_
  rw [sub_ne_zero]
  intro hij
  have : e i = e j := Subtype.ext hij
  exact (Finset.mem_Ioi.mp hj).ne (e.injective this)

end Domain

section Nonmonic

variable {F : Type*} [CommRing F] [IsDomain F] {f : F[X]}

/-- Over an integral domain, scaling a polynomial of degree `n` by a nonzero constant `a`
scales its discriminant by `a ^ (2 * n - 2)`. -/
theorem discr_C_mul (a : F) (ha : a ≠ 0) :
    (C a * f).discr = a ^ (2 * f.natDegree - 2) * f.discr := by
  by_cases hdeg : f.natDegree = 0
  · rw [eq_C_of_natDegree_eq_zero hdeg]
    rw [← C_mul, discr_C]
    simp
  have hf0 : f ≠ 0 := by
    rintro rfl
    simp at hdeg
  have hpos : 0 < f.degree :=
    natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hdeg)
  have hscaleddeg : (C a * f).natDegree = f.natDegree := natDegree_C_mul ha
  have hscaledpos : 0 < (C a * f).degree := by
    rw [degree_C_mul ha]
    exact hpos
  have hfres := resultant_deriv hpos
  have hscaledres := resultant_deriv hscaledpos
  rw [derivative_C_mul, resultant_C_mul_left, resultant_C_mul_right,
    hscaleddeg, hfres, leadingCoeff_mul, leadingCoeff_C] at hscaledres
  apply mul_left_cancel₀ (a := a * f.leadingCoeff)
    (mul_ne_zero ha (leadingCoeff_ne_zero.mpr hf0))
  calc
    a * f.leadingCoeff * (C a * f).discr =
        a ^ (f.natDegree - 1) * a ^ f.natDegree *
          (f.leadingCoeff * f.discr) := by
            apply mul_left_cancel₀ (a := (-1 : F) ^ (f.natDegree * (f.natDegree - 1) / 2))
              (pow_ne_zero _ (by simp))
            simpa only [mul_assoc, mul_left_comm, mul_comm] using hscaledres.symm
    _ = a * f.leadingCoeff *
        (a ^ (2 * f.natDegree - 2) * f.discr) := by
          rw [← pow_add]
          have hn : f.natDegree - 1 + f.natDegree = 1 + (2 * f.natDegree - 2) := by omega
          rw [hn, pow_add, pow_one]
          ring

end Nonmonic

section NonmonicField

variable {F : Type*} [Field F] {f : F[X]}

/-- For a separable polynomial, the discriminant is a square in the base field exactly when the
product of the root differences in an extension domain comes from the base field. This is the
nonmonic analogue of `Polynomial.Monic.isSquare_discr_iff_mem_range`. -/
theorem isSquare_discr_iff_mem_range {E : Type*} [CommRing E] [IsDomain E] [Algebra F E]
    (hsep : f.Separable) (e : Fin f.natDegree ≃ f.rootSet E) :
    IsSquare f.discr ↔ discrSqrt e ∈ Set.range (algebraMap F E) := by
  have hf0 : f ≠ 0 := hsep.ne_zero
  have hlc : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hf0
  have hlcE : algebraMap F E f.leadingCoeff ≠ 0 :=
    (map_eq_zero_iff _ (algebraMap F E).injective).not.mpr hlc
  let p : E[X] := ∏ i, (X - C (e i : E))
  have hfmapdeg : (f.map (algebraMap F E)).natDegree = f.natDegree :=
    natDegree_map_eq_of_injective (algebraMap F E).injective f
  have hroots := hsep.roots_map_eq_map_numbering e
  have hrootsCard : (f.map (algebraMap F E)).roots.card =
      (f.map (algebraMap F E)).natDegree := by
    rw [hroots, hfmapdeg]
    simp
  have hsplits : (f.map (algebraMap F E)).Splits :=
    splits_iff_card_roots.mpr hrootsCard
  have hfac : f.map (algebraMap F E) = C (algebraMap F E f.leadingCoeff) * p := by
    calc
      f.map (algebraMap F E) = C (f.map (algebraMap F E)).leadingCoeff *
          ((f.map (algebraMap F E)).roots.map (X - C ·)).prod := hsplits.eq_prod_roots
      _ = C (algebraMap F E f.leadingCoeff) *
          ((univ.val.map fun i ↦ (e i : E)).map (X - C ·)).prod := by
            rw [leadingCoeff_map_of_injective (algebraMap F E).injective, hroots]
      _ = C (algebraMap F E f.leadingCoeff) * ∏ i, (X - C (e i : E)) := by
            rw [Multiset.map_map, ← Finset.prod_eq_multiset_prod]
            rfl
      _ = C (algebraMap F E f.leadingCoeff) * p := rfl
  have hpdeg : p.natDegree = f.natDegree := by
    rw [← hfmapdeg, hfac, natDegree_C_mul hlcE]
  have hdiscr : algebraMap F E f.discr =
      (algebraMap F E f.leadingCoeff) ^ (2 * f.natDegree - 2) * discrSqrt e ^ 2 := by
    rw [← discr_map_of_natDegree_eq (algebraMap F E) hfmapdeg, hfac,
      discr_C_mul _ hlcE, hpdeg, discr_prod_X_sub_C_eq_sq, discrSqrt_def]
  have hexp : 2 * f.natDegree - 2 = 2 * (f.natDegree - 1) := by omega
  rw [hexp, mul_comm 2, pow_mul] at hdiscr
  set d : E := algebraMap F E f.leadingCoeff ^ (f.natDegree - 1) with hd_def
  simp only [pow_two] at hdiscr
  have hd : d ≠ 0 := pow_ne_zero _ hlcE
  constructor
  · rintro ⟨c, hc⟩
    have hs : discrSqrt e * discrSqrt e =
        algebraMap F E (f.leadingCoeff⁻¹ ^ (f.natDegree - 1) * c) *
          algebraMap F E (f.leadingCoeff⁻¹ ^ (f.natDegree - 1) * c) := by
      apply mul_left_cancel₀ (a := d * d) (mul_ne_zero hd hd)
      calc
        d * d * (discrSqrt e * discrSqrt e) = algebraMap F E (c * c) := by
          rw [← hc, hdiscr]
        _ = _ := by
          simp only [hd_def, ← map_pow, ← map_mul]
          congr 1
          rw [inv_pow]
          field_simp
    rcases mul_self_eq_mul_self_iff.mp hs with hs | hs
    · exact ⟨_, hs.symm⟩
    · exact ⟨-_, by rw [map_neg, ← hs]⟩
  · rintro ⟨c, hc⟩
    refine ⟨f.leadingCoeff ^ (f.natDegree - 1) * c, (algebraMap F E).injective ?_⟩
    simp only [map_mul, map_pow]
    rw [← hd_def]
    rw [hc, hdiscr]
    ring

end NonmonicField

end DiscrSqrt

end TauCeti

namespace Polynomial.Monic

section Domain

variable {F : Type*} [CommRing F] {E : Type*} [CommRing E] [IsDomain E] [Algebra F E] {f : F[X]}

/-- The defining property: the square of the product of the root differences is the discriminant.
-/
@[simp]
theorem discrSqrt_sq (hf : f.Monic) (hsep : f.Separable)
    (e : Fin f.natDegree ≃ f.rootSet E) :
    discrSqrt e ^ 2 = algebraMap F E f.discr := by
  rw [hf.discr_eq_prod_roots_sub_sq (hsep.roots_map_eq_map_numbering e), discrSqrt_def,
    ← Finset.prod_pow]
  exact Finset.prod_congr rfl fun i _ ↦ (Finset.prod_pow _ _ _).symm

end Domain

section Field

variable {F : Type*} [Field F] {E : Type*} [CommRing E] [IsDomain E] [Algebra F E] {f : F[X]}

/-- The discriminant is a square in the base field exactly when the product of the root
differences already comes from the base field. No Galois hypothesis is involved: this is the
elementary half of the discriminant test, and it is the reading of
`Polynomial.Monic.discrSqrt_sq` in both directions. -/
theorem isSquare_discr_iff_mem_range (hf : f.Monic) (hsep : f.Separable)
    (e : Fin f.natDegree ≃ f.rootSet E) :
    IsSquare f.discr ↔ discrSqrt e ∈ Set.range (algebraMap F E) := by
  constructor
  · rintro ⟨c, hc⟩
    have hsq : discrSqrt e * discrSqrt e = algebraMap F E c * algebraMap F E c := by
      rw [← map_mul, ← hc, ← sq, hf.discrSqrt_sq hsep]
    rcases mul_self_eq_mul_self_iff.mp hsq with h | h
    · exact ⟨c, h.symm⟩
    · exact ⟨-c, by rw [map_neg, ← h]⟩
  · rintro ⟨c, hc⟩
    refine ⟨c, (algebraMap F E).injective ?_⟩
    rw [map_mul, hc, ← sq, hf.discrSqrt_sq hsep]

end Field

end Polynomial.Monic

/-! ### Separability -/

namespace Polynomial

variable {R : Type*} [CommRing R]

namespace Monic

/-- A monic polynomial is separable exactly when its discriminant is a unit. This is the
ring-level form of the criterion; over a field it reads `f.discr ≠ 0`. -/
@[simp]
theorem isUnit_discr_iff {f : R[X]} (hf : f.Monic) :
    IsUnit f.discr ↔ f.Separable := by
  -- Separability is coprimality of `f` with `f.derivative`, which
  -- `Polynomial.isUnit_resultant_iff_isCoprime` reads as a unit resultant; the discriminant
  -- differs from that resultant by the unit sign.
  rw [separable_def, ← isUnit_resultant_iff_isCoprime hf,
    ← hf.resultant_of_le (natDegree_derivative_le f),
    hf.resultant_deriv,
    IsUnit.mul_iff]
  simp [isUnit_one.neg.pow]

/-- Over a field, a monic polynomial is separable exactly when its discriminant is nonzero.

⚠ The field hypothesis is not decoration: `Polynomial.not_separable_X_pow_two_sub_one` records a
monic polynomial over `ℤ` with nonzero discriminant that is not separable. -/
@[simp]
theorem discr_ne_zero_iff {K : Type*} [Field K] {f : K[X]}
    (hf : f.Monic) : f.discr ≠ 0 ↔ f.Separable := by
  rw [← hf.isUnit_discr_iff, isUnit_iff_ne_zero]

end Monic

/-- Over a field, a nonzero polynomial is separable exactly when its discriminant is nonzero.

The hypothesis `f ≠ 0` cannot be dropped: the zero polynomial has discriminant `1` but is not
separable. -/
theorem discr_ne_zero_iff {K : Type*} [Field K] {f : K[X]} (hf : f ≠ 0) :
    f.discr ≠ 0 ↔ f.Separable := by
  have hc : f.leadingCoeff⁻¹ ≠ 0 := inv_ne_zero (leadingCoeff_ne_zero.mpr hf)
  have hmonic : (C f.leadingCoeff⁻¹ * f).Monic := by
    rw [mul_comm]
    exact monic_mul_leadingCoeff_inv hf
  rw [← mul_ne_zero_iff_left (pow_ne_zero (2 * f.natDegree - 2) hc), ← discr_C_mul _ hc,
    hmonic.discr_ne_zero_iff]
  exact ⟨fun h ↦ h.of_mul_right, Separable.unit_mul (isUnit_C.mpr hc.isUnit)⟩

/-- A degree-preserving specialization into a field is separable exactly when the formal
discriminant specializes to a nonzero value. The leading coefficient may be any nonzero value. -/
@[simp]
theorem separable_map_iff_map_discr_ne_zero {K : Type*} [Field K]
    (f : R[X]) (φ : R →+* K) (hlc : φ f.leadingCoeff ≠ 0) :
    (f.map φ).Separable ↔ φ f.discr ≠ 0 := by
  have hn : f.map φ ≠ 0 := leadingCoeff_ne_zero.mp <| by
    rwa [leadingCoeff_map_of_leadingCoeff_ne_zero φ hlc]
  rw [← discr_ne_zero_iff hn,
    discr_map_of_natDegree_eq φ (natDegree_map_of_leadingCoeff_ne_zero φ hlc)]

namespace Monic

/-- Over a domain, the discriminant of a monic polynomial is nonzero exactly when the polynomial
becomes separable over the fraction field: over a domain the separability criterion is the one
formulated after passage to a fraction field. -/
@[simp]
theorem discr_ne_zero_iff_separable_map (K : Type*) [Field K]
    [Algebra R K] [IsFractionRing R K] {f : R[X]} (hf : f.Monic) :
    f.discr ≠ 0 ↔ (f.map (algebraMap R K)).Separable := by
  rw [f.separable_map_iff_map_discr_ne_zero _ (by simp [hf.leadingCoeff]), map_ne_zero_iff _
    (FaithfulSMul.algebraMap_injective R K)]

/-- A monic polynomial over a domain with nonzero discriminant is squarefree. The discriminant
makes it separable over the fraction field, hence squarefree there; a square factor over the
domain is then constant, and divides the leading coefficient `1`. -/
theorem squarefree_of_discr_ne_zero [IsDomain R] {f : R[X]} (hf : f.Monic) (hd : f.discr ≠ 0) :
    Squarefree f := by
  have hsep := (hf.discr_ne_zero_iff_separable_map (FractionRing R)).mp hd
  intro g hg
  obtain ⟨h, hh⟩ := hg
  have hu : IsUnit (g.map (algebraMap R (FractionRing R))) :=
    hsep.squarefree _ ⟨h.map (algebraMap R (FractionRing R)), by
      rw [hh]; simp only [Polynomial.map_mul]⟩
  have hg0 : g.natDegree = 0 := by
    rw [← natDegree_map_eq_of_injective (FaithfulSMul.algebraMap_injective R (FractionRing R))]
    exact natDegree_eq_zero_of_isUnit hu
  -- `Polynomial.Monic.natDegree_eq_zero` would shadow the constant-polynomial characterization.
  obtain ⟨a, rfl⟩ := Polynomial.natDegree_eq_zero.mp hg0
  have hlc := congrArg Polynomial.leadingCoeff hh
  rw [hf.leadingCoeff, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_C, mul_assoc] at hlc
  exact isUnit_C.mpr (IsUnit.of_mul_eq_one _ hlc.symm)

/-- A monic integral polynomial has separable reduction modulo a prime exactly when that prime
does not divide its discriminant. -/
-- Tagged `@[simp high]` rather than `@[simp]`: at the default priority the general
-- The general specialization criterion rewrites this left-hand side first, so the prime
-- divisibility form would not be the simp normal form.
@[simp high]
theorem separable_map_zmod_iff_not_dvd_discr {f : ℤ[X]} (hf : f.Monic)
    (p : ℕ) [Fact p.Prime] :
    (f.map (Int.castRingHom (ZMod p))).Separable ↔ ¬ (p : ℤ) ∣ f.discr := by
  rw [f.separable_map_iff_map_discr_ne_zero _ (by simp [hf.leadingCoeff]),
    Int.coe_castRingHom, ne_eq,
    ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- The discriminant of a monic integral polynomial is a square in `ℚ` exactly when it is a square
in `ℤ`. -/
theorem isSquare_discr_map_rat_iff {f : ℤ[X]} (hf : f.Monic) :
    IsSquare (f.map (Int.castRingHom ℚ)).discr ↔ IsSquare f.discr := by
  rw [hf.discr_map, eq_intCast, Rat.isSquare_intCast_iff]

end Monic

end Polynomial

/-! ### The discriminant of a power basis -/

namespace Algebra

/-- For a finite field extension with a power basis, the algebra discriminant of the power basis
is the polynomial discriminant of the minimal polynomial of its generator. Separability is not
needed: without it both sides vanish, the left because the trace form is identically zero and the
right because the minimal polynomial is inseparable. -/
theorem discr_powerBasis_eq_minpoly_discr {K L : Type*} [Field K] [Field L]
    [Algebra K L] (pb : PowerBasis K L) :
    Algebra.discr K pb.basis = (minpoly K pb.gen).discr := by
  let _ := pb.finite
  classical
  let E := AlgebraicClosure L
  let := fun a b : E ↦ Classical.propDecidable (Eq a b)
  have hs : ((minpoly K pb.gen).map (algebraMap K E)).Splits := IsAlgClosed.splits _
  -- A power basis is separable over `K` exactly when the whole extension is, since the number of
  -- embeddings of `L` into an algebraic closure is then the degree of the minimal polynomial.
  have hsep_of : IsSeparable K pb.gen → Algebra.IsSeparable K L := fun h ↦ by
    rw [← Field.finSepDegree_eq_finrank_iff,
      Field.finSepDegree_eq_of_isAlgClosed (F := K) (E := L) (K := E),
      AlgHom.natCard_of_powerBasis pb h hs, PowerBasis.finrank pb]
  by_cases hsepL : Algebra.IsSeparable K L
  case neg =>
    -- The inseparable case: the trace form vanishes identically, and so does the discriminant of
    -- the minimal polynomial, which is monic and not separable.
    have hzero : Algebra.traceMatrix K pb.basis = 0 := by
      ext i j
      simp [Algebra.traceMatrix_apply, Algebra.traceForm_apply,
        Algebra.trace_eq_zero_of_not_isSeparable hsepL]
    have hminpoly : ¬ (minpoly K pb.gen).Separable := fun h ↦ hsepL (hsep_of h)
    have : Nonempty (Fin pb.dim) := ⟨⟨0, pb.dim_pos⟩⟩
    rw [Algebra.discr_def, hzero, Matrix.det_zero,
      eq_comm, ← not_ne_iff, (minpoly.monic pb.isIntegral_gen).discr_ne_zero_iff]
    exact hminpoly
  have e : Fin pb.dim ≃ (L →ₐ[K] E) := by
    refine Fintype.equivOfCardEq ?_
    rw [Fintype.card_fin, AlgHom.card]
    exact (PowerBasis.finrank pb).symm
  let r : Fin pb.dim → E := fun i ↦ e i pb.gen
  have hrmem : ∀ i, r i ∈ (minpoly K pb.gen).aroots E := by
    intro i
    rw [mem_roots, IsRoot.def, eval_map_algebraMap, aeval_algHom_apply]
    repeat' simp [minpoly.ne_zero pb.isIntegral_gen]
  have hrnodup : (univ.val.map r).Nodup := by
    rw [Multiset.nodup_map_iff_of_injective]
    · exact univ.nodup
    · intro i j hij
      exact e.injective (pb.algHom_ext hij)
  have hr : ((minpoly K pb.gen).map (algebraMap K E)).roots = univ.val.map r := by
    have hle : univ.val.map r ≤ ((minpoly K pb.gen).map (algebraMap K E)).roots :=
      (Multiset.le_iff_subset hrnodup).2 (by
        intro x hx
        obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hx
        exact hrmem i)
    have hcardroots : ((minpoly K pb.gen).map (algebraMap K E)).roots.card = pb.dim := by
      rw [← hs.natDegree_eq_card_roots,
        (minpoly.monic pb.isIntegral_gen).natDegree_map (algebraMap K E),
        pb.natDegree_minpoly]
    exact (Multiset.eq_of_le_of_card_le hle (by simp [hcardroots])).symm
  apply (algebraMap K E).injective
  rw [Algebra.discr_powerBasis_eq_prod K E pb e,
    (minpoly.monic pb.isIntegral_gen).discr_eq_prod_roots_sub_sq_of_splits hs hr]
  apply Finset.prod_congr rfl
  intro i _
  apply Finset.prod_congr rfl
  intro j _
  dsimp only [r]
  ring

end Algebra

/-! ### The failure of the separability criterion over a ring -/

namespace Polynomial

/-- The discriminant of `X ^ 2 - 1` over `ℤ` is `4`. -/
theorem discr_X_pow_two_sub_one : (X ^ 2 - 1 : ℤ[X]).discr = 4 := by
  rw [discr_of_degree_eq_two (by compute_degree!)]
  simp [coeff_one]

/-- `X ^ 2 - 1` is not separable over `ℤ`, although its discriminant `4` is nonzero. This is why
`Polynomial.Monic.discr_ne_zero_iff` is stated over a field, and why the version over a domain
passes to the fraction field. -/
theorem not_separable_X_pow_two_sub_one : ¬ (X ^ 2 - 1 : ℤ[X]).Separable := by
  -- A coprimality witness for `X ^ 2 - 1` and `2 * X`, evaluated at `1`, would give `2 ∣ 1`.
  rw [separable_def']
  rintro ⟨a, b, hab⟩
  have := congrArg (eval 1) hab
  simp at this
  omega

end Polynomial

/-! ### Comparison with the discriminant of a cubic -/

namespace Cubic

variable {R : Type*} [CommRing R]

/-- For a cubic with nonzero leading coefficient, the discriminant in the sense of `Cubic.discr`
is the discriminant of the associated degree-three polynomial. The two conventions agree on the
nose, with no normalization to monic and no sign. -/
@[simp]
theorem toPoly_discr {P : Cubic R} (ha : P.a ≠ 0) : P.toPoly.discr = P.discr := by
  rw [discr_of_degree_eq_three (P.degree_of_a_ne_zero ha), P.coeff_eq_a, P.coeff_eq_b,
    P.coeff_eq_c, P.coeff_eq_d, Cubic.discr]

end Cubic

/-! ### The discriminant of a monic quartic -/

namespace Polynomial

variable {R : Type*} [CommRing R]

/-- The Sylvester matrix used by the discriminant of a quartic, after identifying its
degree-dependent index type with `Fin 7`.

The statement and proof are adapted from Mathlib's private lemma
`Polynomial.sylvesterDeriv_of_natDegree_eq_three` in
`Mathlib/RingTheory/Polynomial/Resultant/Basic.lean`, which does the same for a cubic. -/
private theorem sylvesterDeriv_of_natDegree_eq_four {f : R[X]}
    (hf : f.natDegree = 4) :
    f.sylvesterDeriv.reindex (finCongr (by omega)) (finCongr (by omega)) =
      !![f.coeff 0, 0, 0, 1 * f.coeff 1, 0, 0, 0;
         f.coeff 1, f.coeff 0, 0, 2 * f.coeff 2, 1 * f.coeff 1, 0, 0;
         f.coeff 2, f.coeff 1, f.coeff 0, 3 * f.coeff 3, 2 * f.coeff 2, 1 * f.coeff 1, 0;
         f.coeff 3, f.coeff 2, f.coeff 1, 4 * f.coeff 4, 3 * f.coeff 3, 2 * f.coeff 2,
           1 * f.coeff 1;
         f.coeff 4, f.coeff 3, f.coeff 2, 0, 4 * f.coeff 4, 3 * f.coeff 3, 2 * f.coeff 2;
         0, f.coeff 4, f.coeff 3, 0, 0, 4 * f.coeff 4, 3 * f.coeff 3;
         0, 0, 1, 0, 0, 0, 4] := by
  ext ⟨i, hi⟩ ⟨j, hj⟩
  simp only [Polynomial.sylvesterDeriv, hf, OfNat.ofNat_ne_zero, ↓reduceDIte,
    Polynomial.sylvester, Fin.addCases, Nat.add_one_sub_one, Fin.val_castLT,
    Fin.val_subNat, Fin.val_cast, Polynomial.coeff_derivative, eq_rec_constant, dite_eq_ite,
    Nat.reduceMul, Nat.reduceSub, Nat.cast_ofNat, Matrix.reindex_apply, finCongr_symm,
    Matrix.submatrix_apply, finCongr_apply, Fin.cast_mk, Matrix.updateRow_apply, Fin.mk.injEq,
    Matrix.of_apply, one_mul, Matrix.cons_val', Matrix.cons_val_fin_one]
  have hi' : i ∈ Finset.range 7 := Finset.mem_range.mpr hi
  have hj' : j ∈ Finset.range 7 := Finset.mem_range.mpr hj
  fin_cases hi' <;>
  · simp only [Fin.isValue, Fin.mk_one, Fin.reduceFinMk, Fin.zero_eta,
      Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val,
      Nat.reduceEqDiff, OfNat.one_ne_ofNat, ↓reduceIte]
    fin_cases hj' <;>
      simp [mul_comm, (by norm_num : (1 : R) + 1 = 2),
        (by norm_num : (2 : R) + 1 = 3),
        (by norm_num : (3 : R) + 1 = 4)]

namespace Monic

/-- The discriminant of a monic quartic, expressed in terms of its coefficients. -/
theorem discr_of_natDegree_eq_four {f : R[X]} (hmonic : f.Monic)
    (hf : f.natDegree = 4) :
    f.discr =
      256 * f.coeff 0 ^ 3 - 192 * f.coeff 3 * f.coeff 1 * f.coeff 0 ^ 2 -
        128 * f.coeff 2 ^ 2 * f.coeff 0 ^ 2 + 144 * f.coeff 2 * f.coeff 1 ^ 2 * f.coeff 0 -
        27 * f.coeff 1 ^ 4 + 144 * f.coeff 3 ^ 2 * f.coeff 2 * f.coeff 0 ^ 2 -
        6 * f.coeff 3 ^ 2 * f.coeff 1 ^ 2 * f.coeff 0 -
        80 * f.coeff 3 * f.coeff 2 ^ 2 * f.coeff 1 * f.coeff 0 +
        18 * f.coeff 3 * f.coeff 2 * f.coeff 1 ^ 3 + 16 * f.coeff 2 ^ 4 * f.coeff 0 -
        4 * f.coeff 2 ^ 3 * f.coeff 1 ^ 2 - 27 * f.coeff 3 ^ 4 * f.coeff 0 ^ 2 +
        18 * f.coeff 3 ^ 3 * f.coeff 2 * f.coeff 1 * f.coeff 0 -
        4 * f.coeff 3 ^ 3 * f.coeff 1 ^ 3 -
        4 * f.coeff 3 ^ 2 * f.coeff 2 ^ 3 * f.coeff 0 +
        f.coeff 3 ^ 2 * f.coeff 2 ^ 2 * f.coeff 1 ^ 2 := by
  nontriviality R
  let e : Fin (f.natDegree - 1 + f.natDegree) ≃ Fin 7 := finCongr (by omega)
  rw [Polynomial.discr, ← Matrix.det_reindex_self e,
    sylvesterDeriv_of_natDegree_eq_four hf, hf]
  norm_num
  have hc4 : f.coeff 4 = 1 := by
    rw [← hf, hmonic.coeff_natDegree]
  eval_det
  rw [hc4]
  ring

end Monic

end Polynomial

namespace TauCeti

variable {R : Type*} [CommRing R]

/-- The discriminant of the depressed quartic `X⁴ + pX² + qX + r`. -/
theorem discr_depressedQuartic (p q r : R) :
    (X ^ 4 + C p * X ^ 2 + C q * X + C r : R[X]).discr =
      256 * r ^ 3 - 128 * p ^ 2 * r ^ 2 + 144 * p * q ^ 2 * r - 27 * q ^ 4 +
        16 * p ^ 4 * r - 4 * p ^ 3 * q ^ 2 := by
  nontriviality R
  let f : R[X] := X ^ 4 + C p * X ^ 2 + C q * X + C r
  have hf : f.natDegree = 4 := by
    dsimp only [f]
    compute_degree <;> norm_num
  have hmonic : f.Monic := by
    dsimp only [f]
    have hdeg : degree (C p * X ^ 2 + C q * X + C r : R[X]) < 4 := by
      compute_degree
      norm_num
    simpa only [add_assoc] using monic_X_pow_add hdeg
  rw [hmonic.discr_of_natDegree_eq_four hf]
  simp [f]

/-- The discriminant of the quintic trinomial `X⁵ + aX + b`, over any commutative ring. -/
@[simp] theorem discr_X_pow_five_add_C_mul_X_add_C (a b : R) :
    (X ^ 5 + C a * X + C b).discr = 256 * a ^ 5 + 3125 * b ^ 4 := by
  nontriviality R
  let f : R[X] := X ^ 5 + C a * X + C b
  have hf : f.natDegree = 5 := by dsimp [f]; compute_degree!
  let e : Fin (f.natDegree - 1 + f.natDegree) ≃ Fin 9 := finCongr (by omega)
  have hmat : f.sylvesterDeriv.reindex e e =
      !![b, 0, 0, 0, a, 0, 0, 0, 0;
         a, b, 0, 0, 0, a, 0, 0, 0;
         0, a, b, 0, 0, 0, a, 0, 0;
         0, 0, a, b, 0, 0, 0, a, 0;
         0, 0, 0, a, 5, 0, 0, 0, a;
         1, 0, 0, 0, 0, 5, 0, 0, 0;
         0, 1, 0, 0, 0, 0, 5, 0, 0;
         0, 0, 1, 0, 0, 0, 0, 5, 0;
         0, 0, 0, 1, 0, 0, 0, 0, 5] := by
    ext ⟨i, hi⟩ ⟨j, hj⟩
    simp only [sylvesterDeriv, hf, OfNat.ofNat_ne_zero, ↓reduceDIte, sylvester, Fin.addCases,
      Nat.add_one_sub_one, Fin.val_castLT, Fin.val_subNat, Fin.val_cast, coeff_derivative,
      eq_rec_constant, dite_eq_ite, Nat.reduceMul, Nat.reduceSub, Nat.cast_ofNat,
      Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.updateRow_apply, Matrix.of_apply,
      e, finCongr_symm, finCongr_apply, Fin.cast_mk, Fin.mk.injEq,
      Matrix.cons_val', Matrix.cons_val_fin_one]
    have hi' : i ∈ Finset.range 9 := Finset.mem_range.mpr hi
    have hj' : j ∈ Finset.range 9 := Finset.mem_range.mpr hj
    fin_cases hi' <;>
    · simp only [Fin.isValue, Fin.mk_one, Fin.reduceFinMk, Fin.zero_eta,
        Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val,
        Nat.reduceEqDiff, OfNat.one_ne_ofNat, ↓reduceIte]
      fin_cases hj' <;>
      · simp only [f, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C,
          Nat.reduceAdd, Nat.reduceSub, Nat.reduceEqDiff, ↓reduceIte,
          zero_add, add_zero, zero_mul, mul_zero, mul_one, one_mul]
        norm_num [Set.mem_Icc, Matrix.cons_val]
  -- Fold the local polynomial abbreviation to use the matrix identity.
  change f.discr = _
  rw [discr, ← Matrix.det_reindex_self e, hmat, hf]
  norm_num
  eval_det
  ring

end TauCeti
