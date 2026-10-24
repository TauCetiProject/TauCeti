/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Weighted homogeneity under substitution and evaluation

Give the variable `i` the weight `w i`, and substitute for it a polynomial that is weighted
homogeneous of weight `w i` for weights `v` on the target variables. A weighted homogeneous
polynomial of weight `m` then becomes weighted homogeneous of weight `m` for the weights `v`. The
homogeneous case is `v = 1`: substituting polynomials homogeneous of degree `w i` turns a weighted
homogeneous polynomial of weight `m` into a homogeneous polynomial of degree `m`. In this case,
when the substitution is injective, the converse holds: a polynomial whose substitution is
homogeneous of degree `m` is itself weighted homogeneous of weight `m`.

The motivating substitution sends the variable `i` of `MvPolynomial (Fin n) R` to the elementary
symmetric polynomial `eᵢ₊₁`, which is homogeneous of degree `i + 1`
(`MvPolynomial.isHomogeneous_esymm`). By the fundamental theorem of symmetric polynomials it is
injective, so the expression of a homogeneous symmetric polynomial in the elementary symmetric
polynomials is weighted homogeneous for the weights `i + 1`. The coefficients of a product
`∏ (X - C Ψ)` of linear factors with homogeneous constant terms of a common degree `m` supply
such symmetric polynomials (`MvPolynomial.isHomogeneous_coeff_prod_X_sub_C`).

More generally, evaluating a weighted homogeneous polynomial of weight `m` at elements of the
graded pieces of weights `w i` of any graded algebra lands in its graded piece of weight `m`.
Conversely, the weighted homogeneous components of a polynomial over `R` are read off from the
substitution `X i ↦ X i * T ^ w i` into polynomials in an auxiliary variable `T`: the coefficient
of `T ^ n` is the component of weight `n`. This detects homogeneity of an ideal from its stability
under such substitutions, as for the ideal of relations of the Lazard ring.

Evaluating at a point is the substitution of constants. A weighted homogeneous polynomial of
nonzero weight vanishes wherever its variables of nonzero weight vanish, and the value of one of
weight zero (for canonically ordered weights) ignores the variables of nonzero weight. With the
indicator weight of a block `b` of variables `X_{b,l}`, so that weighted homogeneity is
homogeneity in block `b`: a polynomial that does not vanish at a point with zero block `b` has
degree zero in block `b`, and the blocks of degree zero can be replaced simultaneously by
arbitrary vectors without changing the value.

## Main results

* `MvPolynomial.IsWeightedHomogeneous.aeval_mem`: evaluation at elements of graded pieces of the
  weights of the variables preserves weighted homogeneity.
* `MvPolynomial.IsWeightedHomogeneous.aeval`: substituting polynomials that are weighted
  homogeneous of the weights of the variables preserves weighted homogeneity.
* `MvPolynomial.isWeightedHomogeneous_of_isHomogeneous_aeval`: the converse of the homogeneous
  case, for an injective substitution.
* `MvPolynomial.coeff_aeval_C_X_mul_X_pow`: the coefficient of `T ^ n` in the substitution
  `X i ↦ X i * T ^ w i` is the weighted homogeneous component of weight `n`.
* `MvPolynomial.IsWeightedHomogeneous.eval₂_eq_zero`: a polynomial of nonzero weight vanishes at
  a point whose coordinates of nonzero weight vanish.
* `MvPolynomial.IsWeightedHomogeneous.eq_zero_of_eval₂_ne_zero`: the block form, a nonzero value
  at a point with zero block `b` forces degree zero in block `b`.
* `MvPolynomial.IsWeightedHomogeneous.eval₂_congr`: the value of a polynomial of weight zero only
  depends on the coordinates of weight zero.
* `MvPolynomial.eval₂_congr_of_block_isWeightedHomogeneous_zero`: the block form, replacing all
  blocks of degree zero simultaneously preserves the value.

## References

* J.-H. Evertse, *An improvement of the quantitative subspace theorem*, Compositio Math. 101
  (1996), §7, Lemma 26, for the block forms.
-/

public section

namespace MvPolynomial

variable {σ τ R : Type*}

section CommSemiring

variable [CommSemiring R]

/-- Evaluating a polynomial that is weighted homogeneous of weight `m` at elements `g i` of the
graded pieces `𝒜 (w i)` of a graded algebra gives an element of `𝒜 m`. -/
theorem IsWeightedHomogeneous.aeval_mem {M A S : Type*} [AddCommMonoid M] [CommSemiring A]
    [Algebra R A] [SetLike S A] [AddSubmonoidClass S A] [SMulMemClass S R A] {𝒜 : M → S}
    [SetLike.GradedMonoid 𝒜] {w : σ → M} {φ : MvPolynomial σ R} {m : M}
    (hφ : φ.IsWeightedHomogeneous w m) {g : σ → A} (hg : ∀ i, g i ∈ 𝒜 (w i)) :
    MvPolynomial.aeval g φ ∈ 𝒜 m := by
  induction hφ using IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add p q _ _ ihp ihq => simpa using add_mem ihp ihq
  | monomial d r hr =>
    -- Write the weight of `d` as `0 + ∑ i, d i • w i` and `algebraMap R A r` as `r • 1`, matching
    -- the product of `r • 1 ∈ 𝒜 0` with `∏ i, g i ^ d i ∈ 𝒜 (∑ i, d i • w i)`.
    rw [aeval_monomial, ← hr, Finsupp.weight_apply, Finsupp.sum, ← zero_add (∑ _ ∈ _, _),
      Algebra.algebraMap_eq_smul_one]
    exact SetLike.mul_mem_graded (SMulMemClass.smul_mem r SetLike.GradedOne.one_mem)
      (SetLike.prod_pow_mem_graded 𝒜 w g d fun i _ ↦ hg i)

/-- Substituting, for each variable `i`, a polynomial that is weighted homogeneous of weight
`w i` for the weights `v` into a polynomial that is weighted homogeneous of weight `m` for the
weights `w` gives a polynomial that is weighted homogeneous of weight `m` for the weights `v`. -/
theorem IsWeightedHomogeneous.aeval {M : Type*} [AddCommMonoid M] {w : σ → M} {v : τ → M}
    {φ : MvPolynomial σ R} {m : M} (hφ : φ.IsWeightedHomogeneous w m) {g : σ → MvPolynomial τ R}
    (hg : ∀ i, (g i).IsWeightedHomogeneous v (w i)) :
    (MvPolynomial.aeval g φ).IsWeightedHomogeneous v m :=
  have := WeightedHomogeneousSubmodule.gradedMonoid (R := R) (w := v)
  hφ.aeval_mem (𝒜 := weightedHomogeneousSubmodule R v) hg

/-- **Weighted homogeneous components as coefficients.** Substituting `X i * T ^ w i` for each
variable `X i` turns a polynomial into a polynomial in `T` whose coefficient of `Tⁿ` is its
weighted homogeneous component of weight `n`. -/
theorem coeff_aeval_C_X_mul_X_pow (w : σ → ℕ) (φ : MvPolynomial σ R) (n : ℕ) :
    (MvPolynomial.aeval (fun i ↦ Polynomial.C (X i) * Polynomial.X ^ w i) φ).coeff n =
      weightedHomogeneousComponent w n φ := by
  classical
  induction φ using MvPolynomial.induction_on' with
  | monomial d r =>
    -- Each factor `(X i * T ^ w i) ^ d i` contributes `T ^ (d i * w i)`.
    have h : MvPolynomial.aeval (fun i ↦ Polynomial.C (X i) * Polynomial.X ^ w i) (monomial d r) =
        Polynomial.C (monomial d r) * Polynomial.X ^ Finsupp.weight w d := by
      rw [aeval_monomial, monomial_eq]
      simp only [Finsupp.prod, Finsupp.weight_apply, Finsupp.sum, mul_pow, Finset.prod_mul_distrib,
        ← pow_mul', Finset.prod_pow_eq_pow_sum, map_mul, map_prod, map_pow,
        Polynomial.algebraMap_apply, algebraMap_eq, smul_eq_mul]
      ring
    rw [h, Polynomial.coeff_C_mul_X_pow, weightedHomogeneousComponent_of_mem
      (isWeightedHomogeneous_monomial w d r rfl)]
  | add p q hp hq => simp [hp, hq]

/-- **Weighted homogeneity from homogeneity of a substitution.** If `g i` is homogeneous of
degree `w i` for every variable `i` and substitution of the `g i` is injective, then a polynomial
whose substitution is homogeneous of degree `m` is weighted homogeneous of weight `m`. -/
theorem isWeightedHomogeneous_of_isHomogeneous_aeval {w : σ → ℕ} {g : σ → MvPolynomial τ R}
    (hg : ∀ i, (g i).IsHomogeneous (w i)) (hinj : Function.Injective (aeval (R := R) g))
    {φ : MvPolynomial σ R} {m : ℕ} (h : (aeval g φ).IsHomogeneous m) :
    φ.IsWeightedHomogeneous w m := by
  classical
  -- The substitution of the weight-`n` component of `φ` is homogeneous of degree `n`, so the
  -- degree-`m` part of the substitution of `φ` is the substitution of its weight-`m` component.
  set s := (weightedHomogeneousComponent_finsupp (w := w) φ).toFinset
  have hsum : ∑ n ∈ s, weightedHomogeneousComponent w n φ = φ := by
    rw [← finsum_eq_sum _ (weightedHomogeneousComponent_finsupp φ),
      sum_weightedHomogeneousComponent]
  have hcomp (n : ℕ) : (aeval g (weightedHomogeneousComponent w n φ)).IsHomogeneous n :=
    (weightedHomogeneousComponent_isWeightedHomogeneous n φ).aeval hg
  have key : aeval g φ = aeval g (weightedHomogeneousComponent w m φ) := by
    calc aeval g φ = homogeneousComponent m (aeval g φ) := (homogeneousComponent_eq_self h).symm
      _ = ∑ n ∈ s, homogeneousComponent m (aeval g (weightedHomogeneousComponent w n φ)) := by
        conv_lhs => rw [← hsum]
        rw [map_sum, map_sum]
      _ = homogeneousComponent m (aeval g (weightedHomogeneousComponent w m φ)) := by
        refine Finset.sum_eq_single m (fun n _ hn => ?_) fun hm => ?_
        · simp [homogeneousComponent_of_mem (hcomp n), hn.symm]
        · have hzero : weightedHomogeneousComponent w m φ = 0 := by
            by_contra hne
            exact hm ((Set.Finite.mem_toFinset _).mpr hne)
          rw [hzero, map_zero, map_zero]
      _ = aeval g (weightedHomogeneousComponent w m φ) := homogeneousComponent_eq_self (hcomp m)
  rw [hinj key]
  exact weightedHomogeneousComponent_isWeightedHomogeneous m φ

section Eval

variable {S M : Type*} [CommSemiring S] [AddCommMonoid M] {w : σ → M} {φ : MvPolynomial σ R}

/-- A weighted homogeneous polynomial of nonzero weight vanishes at every point whose
coordinates of nonzero weight vanish: each of its monomials involves a variable of nonzero
weight. -/
theorem IsWeightedHomogeneous.eval₂_eq_zero {m : M} (hφ : φ.IsWeightedHomogeneous w m)
    (hm : m ≠ 0) (f : R →+* S) {g : σ → S} (hg : ∀ i, w i ≠ 0 → g i = 0) :
    eval₂ f g φ = 0 := by
  refine eval₂Hom_eq_zero f g φ fun c hc ↦ ?_
  -- The monomial `X^c` has weight `m ≠ 0`, so it involves a variable of nonzero weight.
  obtain ⟨i, hi, hwi⟩ : ∃ i ∈ c.support, w i ≠ 0 := by
    by_contra! h
    refine hm ?_
    rw [← hφ hc, Finsupp.weight_apply, Finsupp.sum]
    exact Finset.sum_eq_zero fun i hi ↦ by rw [h i hi, smul_zero]
  exact ⟨i, hi, hg i hwi⟩

/-- If `F` is homogeneous of degree `d` in the variables `X_{b,l}` of block `b` and does not
vanish at a point whose block-`b` coordinates all vanish, then `d = 0`. -/
theorem IsWeightedHomogeneous.eq_zero_of_eval₂_ne_zero {ι κ : Type*} [DecidableEq ι]
    {F : MvPolynomial (ι × κ) R} {b : ι} {d : ℕ}
    (hF : F.IsWeightedHomogeneous (fun p : ι × κ ↦ if p.1 = b then 1 else 0) d) (f : R →+* S)
    {g : ι × κ → S} (hg : ∀ l, g (b, l) = 0) (h : eval₂ f g F ≠ 0) : d = 0 := by
  by_contra hd
  refine h (hF.eval₂_eq_zero hd f fun p hp ↦ ?_)
  obtain ⟨i, l⟩ := p
  obtain rfl : i = b := by simpa using hp
  exact hg l

variable [PartialOrder M] [IsOrderedAddMonoid M] [CanonicallyOrderedAdd M]

/-- Only variables of weight zero occur in a weighted homogeneous polynomial of weight zero, for
canonically ordered weights. -/
theorem IsWeightedHomogeneous.apply_eq_zero_of_coeff_ne_zero (hφ : φ.IsWeightedHomogeneous w 0)
    {c : σ →₀ ℕ} (hc : φ.coeff c ≠ 0) {i : σ} (hi : c i ≠ 0) : w i = 0 :=
  nonpos_iff_eq_zero.mp (hφ hc ▸ Finsupp.le_weight_of_ne_zero' w hi)

/-- The value of a weighted homogeneous polynomial of weight zero only depends on the
coordinates of weight zero, for canonically ordered weights. -/
theorem IsWeightedHomogeneous.eval₂_congr (hφ : φ.IsWeightedHomogeneous w 0) (f : R →+* S)
    {g₁ g₂ : σ → S} (h : ∀ i, w i = 0 → g₁ i = g₂ i) : eval₂ f g₁ φ = eval₂ f g₂ φ :=
  MvPolynomial.eval₂_congr _ _ _ fun hi hc ↦
    h _ (hφ.apply_eq_zero_of_coeff_ne_zero hc (Finsupp.mem_support_iff.mp hi))

end Eval

/-- If `F` is homogeneous of degree `0` in each block `b ∈ Z` of variables `X_{b,l}`, its value
does not change when the coordinates of all the blocks in `Z` are replaced simultaneously by
arbitrary values. -/
theorem eval₂_congr_of_block_isWeightedHomogeneous_zero {S ι κ : Type*} [CommSemiring S]
    [DecidableEq ι] {F : MvPolynomial (ι × κ) R} {Z : Set ι}
    (hF : ∀ b ∈ Z, F.IsWeightedHomogeneous (fun p : ι × κ ↦ if p.1 = b then 1 else 0) 0)
    (f : R →+* S) {g₁ g₂ : ι × κ → S} (h : ∀ p : ι × κ, p.1 ∉ Z → g₁ p = g₂ p) :
    eval₂ f g₁ F = eval₂ f g₂ F :=
  MvPolynomial.eval₂_congr _ _ _ fun {p} {_} hi hc ↦ h p fun hp ↦ by
    simpa using (hF p.1 hp).apply_eq_zero_of_coeff_ne_zero hc (Finsupp.mem_support_iff.mp hi)

end CommSemiring

end MvPolynomial
