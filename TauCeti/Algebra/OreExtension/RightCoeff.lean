/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.OreExtension.Degree

/-!
# Right coefficients of Ore polynomials

An Ore extension `R[X; σ, δ]` is built on left coefficients `∑ aᵢ Xⁱ`, and these form a basis
for every `σ`. This file treats expansions with coefficients on the right, `∑ Xⁱ * C bᵢ`.

The top coefficient of `Xⁿ * C b` is `σⁿ b`, so right expansions are unique as soon as `σ` is
injective. If `σ` is also surjective, the rewriting rule `C (σ a) * X = X * C a - C (δ a)`
moves every coefficient to the right, so every Ore polynomial has a right expansion. Hence for
bijective `σ` the monomials `Xⁿ` are a basis of `R[X; σ, δ]` as a right `R`-module.

This right-module structure is right multiplication by constants. It differs from the
coefficientwise action of `Rᵐᵒᵖ` given by the generic `OreExtension.module` instance, so no
`Rᵐᵒᵖ`-module instance is used. Instead the basis is recorded as the `k`-linear equivalence
`rightCoeffLinearEquiv` with sequences of right coefficients, together with
`rightCoeffLinearEquiv_mul_C`, which says that it turns right multiplication by `C r` into
right multiplication of every coefficient by `r`.

## Main definitions

* `TauCeti.OreExtension.ofRightCoeff`: the `k`-linear map `b ↦ ∑ n, Xⁿ * C (b n)`.
* `TauCeti.OreExtension.rightCoeffLinearEquiv`: for bijective `σ`, the right coefficients of an
  Ore polynomial, as a `k`-linear equivalence with `ℕ →₀ R`.

## Main statements

* `TauCeti.OreExtension.coeff_ofRightCoeff_of_forall_le`: the coefficient of a right expansion
  at an upper bound of its support.
* `TauCeti.OreExtension.natDegree_ofRightCoeff` and `leadingCoeff_ofRightCoeff`: for injective
  `σ`, the degree and leading coefficient of a right expansion.
* `TauCeti.OreExtension.ofRightCoeff_injective`: right expansions are unique when `σ` is
  injective.
* `TauCeti.OreExtension.ofRightCoeff_surjective`: right expansions exist when `σ` is
  surjective.
* `TauCeti.OreExtension.rightCoeffLinearEquiv_mul_C`: right coefficients are right `R`-linear.

## References

* K. R. Goodearl and R. B. Warfield, Jr., *An Introduction to Noncommutative Noetherian Rings*,
  second edition, Chapter 2, for skew polynomial rings `R[X; σ, δ]` and their right monomial
  basis when `σ` is an automorphism.
-/

public noncomputable section

open MulOpposite

namespace TauCeti.OreExtension

section Semiring

variable {k R : Type*} [CommSemiring k] [Semiring R] [Algebra k R]
  {σ : R →ₐ[k] R} {δ : SigmaDerivation σ}

/-- The Ore polynomial `∑ n, Xⁿ * C (b n)` with right coefficients `b`. -/
def ofRightCoeff : (ℕ →₀ R) →ₗ[k] OreExtension σ δ :=
  Finsupp.lsum k fun n => LinearMap.mulLeft k (X ^ n) ∘ₗ C

@[simp]
theorem ofRightCoeff_single (n : ℕ) (b : R) :
    ofRightCoeff (σ := σ) (δ := δ) (Finsupp.single n b) = X ^ n * C b := by
  simp [ofRightCoeff]

theorem ofRightCoeff_apply (b : ℕ →₀ R) :
    ofRightCoeff (σ := σ) (δ := δ) b = b.sum fun n a => X ^ n * C a := by
  simp [ofRightCoeff, Finsupp.lsum_apply, Function.comp_def]

/-- Right multiplication by a constant multiplies every right coefficient on the right. -/
@[simp]
theorem ofRightCoeff_op_smul (r : R) (b : ℕ →₀ R) :
    ofRightCoeff (σ := σ) (δ := δ) (op r • b) = ofRightCoeff b * C r := by
  induction b using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [smul_add, map_add, map_add, hf, hg, add_mul]
  | single n a => simp [mul_assoc]

/-- Left multiplication by the variable shifts the right coefficients. -/
theorem X_mul_ofRightCoeff (b : ℕ →₀ R) :
    X * ofRightCoeff (σ := σ) (δ := δ) b = ofRightCoeff (b.mapDomain Nat.succ) := by
  induction b using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, mul_add, hf, hg, Finsupp.mapDomain_add, map_add]
  | single n a => simp [pow_succ', mul_assoc]

/-- At an upper bound `N` of the support of `b`, only the right coefficient `b N` contributes
to the coefficient of `Xᴺ`, twisted by `σᴺ`. -/
theorem coeff_ofRightCoeff_of_forall_le {b : ℕ →₀ R} {N : ℕ} (h : ∀ n ∈ b.support, n ≤ N) :
    coeff (ofRightCoeff (σ := σ) (δ := δ) b) N = (σ : R → R)^[N] (b N) := by
  rw [ofRightCoeff_apply, Finsupp.sum, finsetSum_coeff]
  refine (Finset.sum_eq_single N (fun n hn hnN => ?_) fun hN => ?_).trans
    (coeff_X_pow_mul_C_self N (b N))
  · exact coeff_eq_zero_of_natDegree_lt
      ((natDegree_X_pow_mul_C_le n (b n)).trans_lt (lt_of_le_of_ne (h n hn) hnN))
  · simp [Finsupp.notMem_support_iff.mp hN]

/-- For injective `σ`, the degree of a right expansion is the largest index of a nonzero right
coefficient. -/
theorem natDegree_ofRightCoeff (hσ : Function.Injective σ) (b : ℕ →₀ R) :
    natDegree (ofRightCoeff (σ := σ) (δ := δ) b) = b.support.sup id := by
  refine le_antisymm (natDegree_le_iff.mpr fun i hi => ?_) (Finset.sup_le fun n hn => ?_)
  · have hb : b i = 0 :=
      Finsupp.notMem_support_iff.mp fun h => (Finset.le_sup (f := id) h).not_gt hi
    rw [coeff_ofRightCoeff_of_forall_le fun n hn => (Finset.le_sup (f := id) hn).trans hi.le, hb,
      iterate_map_zero]
  · obtain ⟨N, hN, hsup⟩ := Finset.exists_mem_eq_sup b.support ⟨n, hn⟩ id
    refine (Finset.le_sup (f := id) hn).trans (hsup ▸ le_natDegree_of_ne_zero ?_)
    rw [coeff_ofRightCoeff_of_forall_le fun m hm => hsup ▸ Finset.le_sup (f := id) hm]
    exact fun h => Finsupp.mem_support_iff.mp hN
      ((hσ.iterate _).eq_iff.mp (h.trans (iterate_map_zero σ _).symm))

/-- For injective `σ`, the leading coefficient of a right expansion is the top right coefficient,
twisted by `σ` to the power of the degree. -/
theorem leadingCoeff_ofRightCoeff (hσ : Function.Injective σ) (b : ℕ →₀ R) :
    leadingCoeff (ofRightCoeff (σ := σ) (δ := δ) b) =
      (σ : R → R)^[b.support.sup id] (b (b.support.sup id)) := by
  rw [leadingCoeff_def, natDegree_ofRightCoeff hσ]
  exact coeff_ofRightCoeff_of_forall_le fun n hn => Finset.le_sup (f := id) hn

end Semiring

section Ring

variable {k R : Type*} [CommSemiring k] [Ring R] [Algebra k R]
  {σ : R →ₐ[k] R} {δ : SigmaDerivation σ}

/-- Right expansions of Ore polynomials are unique when `σ` is injective. -/
theorem ofRightCoeff_injective (hσ : Function.Injective σ) :
    Function.Injective (ofRightCoeff (σ := σ) (δ := δ)) := by
  refine (injective_iff_map_eq_zero _).mpr fun b hb => ?_
  by_contra hne
  have hs : b.support.Nonempty := Finsupp.support_nonempty_iff.mpr hne
  have htop := coeff_ofRightCoeff_of_forall_le (σ := σ) (δ := δ) (N := b.support.max' hs)
    fun n hn => b.support.le_max' n hn
  rw [hb, coeff_zero] at htop
  exact Finsupp.mem_support_iff.mp (b.support.max'_mem hs)
    ((hσ.iterate _).eq_iff.mp (htop.symm.trans (iterate_map_zero σ _).symm))

/-- If `σ` is surjective, then `C a * Xⁿ * C b` has a right expansion, by moving `C a` past
the powers of `X` with `C (σ a') * X = X * C a' - C (δ a')`. -/
private theorem C_mul_X_pow_mul_C_mem_range (hσ : Function.Surjective σ) (n : ℕ) (a b : R) :
    C a * (X ^ n * C b) ∈ LinearMap.range (ofRightCoeff (σ := σ) (δ := δ)) := by
  induction n generalizing a with
  | zero => exact ⟨Finsupp.single 0 (a * b), by simp⟩
  | succ n ih =>
    obtain ⟨a', rfl⟩ := hσ a
    have hC : (C (σ a') : OreExtension σ δ) * X = X * C a' - C (δ a') := by
      rw [X_mul_C (σ := σ) (δ := δ) a', add_sub_cancel_right]
    rw [pow_succ', mul_assoc, ← mul_assoc, hC, sub_mul, mul_assoc]
    obtain ⟨c, hc⟩ := ih a'
    obtain ⟨d, hd⟩ := ih (δ a')
    exact ⟨c.mapDomain Nat.succ - d, by rw [map_sub, ← X_mul_ofRightCoeff, hc, hd]⟩

/-- Every Ore polynomial has a right expansion when `σ` is surjective. -/
theorem ofRightCoeff_surjective (hσ : Function.Surjective σ) :
    Function.Surjective (ofRightCoeff (σ := σ) (δ := δ)) := by
  intro p
  rw [← LinearMap.mem_range, ← sum_monomial_eq p]
  refine Submodule.sum_mem _ fun n _ => ?_
  simpa [mul_assoc] using C_mul_X_pow_mul_C_mem_range hσ n (coeff p n) 1

/-- For bijective `σ`, the right coefficients of an Ore polynomial: the unique `b` with
`p = ∑ n, Xⁿ * C (b n)`. This is the right monomial basis of `R[X; σ, δ]` as a right `R`-module;
see `rightCoeffLinearEquiv_mul_C` for its right `R`-linearity. -/
def rightCoeffLinearEquiv (hσ : Function.Bijective σ) : OreExtension σ δ ≃ₗ[k] (ℕ →₀ R) :=
  (LinearEquiv.ofBijective ofRightCoeff
    ⟨ofRightCoeff_injective hσ.injective, ofRightCoeff_surjective hσ.surjective⟩).symm

variable (hσ : Function.Bijective σ)

@[simp]
theorem rightCoeffLinearEquiv_symm_apply (b : ℕ →₀ R) :
    (rightCoeffLinearEquiv (δ := δ) hσ).symm b = ofRightCoeff b := (rfl)

/-- Every Ore polynomial is the sum of its right-coefficient monomials. -/
@[simp]
theorem ofRightCoeff_rightCoeffLinearEquiv (p : OreExtension σ δ) :
    ofRightCoeff (rightCoeffLinearEquiv hσ p) = p :=
  (rightCoeffLinearEquiv hσ).symm_apply_apply p

@[simp]
theorem rightCoeffLinearEquiv_ofRightCoeff (b : ℕ →₀ R) :
    rightCoeffLinearEquiv (δ := δ) hσ (ofRightCoeff b) = b :=
  (rightCoeffLinearEquiv hσ).apply_symm_apply b

@[simp]
theorem rightCoeffLinearEquiv_C (b : R) :
    rightCoeffLinearEquiv (δ := δ) hσ (C b) = Finsupp.single 0 b := by
  rw [← rightCoeffLinearEquiv_ofRightCoeff hσ (Finsupp.single 0 b), ofRightCoeff_single, pow_zero,
    one_mul]

@[simp]
theorem rightCoeffLinearEquiv_X_pow (n : ℕ) :
    rightCoeffLinearEquiv (δ := δ) hσ (X ^ n) = Finsupp.single n 1 := by
  rw [← rightCoeffLinearEquiv_ofRightCoeff hσ (Finsupp.single n 1), ofRightCoeff_single, C_one,
    mul_one]

@[simp]
theorem rightCoeffLinearEquiv_X :
    rightCoeffLinearEquiv (δ := δ) hσ X = Finsupp.single 1 1 := by
  simpa using rightCoeffLinearEquiv_X_pow (δ := δ) hσ 1

/-- Right coefficients turn right multiplication by `C r` into right multiplication of every
coefficient by `r`. -/
@[simp]
theorem rightCoeffLinearEquiv_mul_C (p : OreExtension σ δ) (r : R) :
    rightCoeffLinearEquiv hσ (p * C r) = op r • rightCoeffLinearEquiv hσ p := by
  conv_lhs => rw [← ofRightCoeff_rightCoeffLinearEquiv hσ p, ← ofRightCoeff_op_smul]
  exact rightCoeffLinearEquiv_ofRightCoeff hσ _

end Ring

end TauCeti.OreExtension
