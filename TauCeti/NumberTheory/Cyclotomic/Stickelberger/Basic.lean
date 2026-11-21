/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import TauCeti.Algebra.MonoidAlgebra.Augmentation
public import TauCeti.NumberTheory.DirichletCharacter.GeneralizedBernoulli

/-!
# The rational Stickelberger element

For a conductor `m`, identify `Gal(ℚ(ζ_m)/ℚ)` with `(ZMod m)ˣ` through `σ_a(ζ_m) = ζ_m ^ a`. The
rational Stickelberger element is the element

`θ_m = ∑_{a ∈ (ZMod m)ˣ} (a₀ / m) [a⁻¹]`

of the rational group ring `ℚ[(ZMod m)ˣ]`, where `a₀ ∈ {0, …, m - 1}` is the least nonnegative
representative of `a` and `[g]` is the basis element of `g`. The elements of `ℤ[G] θ_m` with
integral coefficients annihilate the ideal class group of `ℚ(ζ_m)` (Stickelberger's theorem), and
evaluating `θ_m` at a nontrivial Dirichlet character `χ` modulo `m` gives the first generalized
Bernoulli number `B_{1, χ⁻¹}` at modulus `m`, which is how Bernoulli numbers enter the arithmetic
of cyclotomic class groups.

The basis inverse matters: the coefficient of `θ_m` at `[b]` is the representative of `b⁻¹`
divided by `m`. At `m = 5` the coefficients at `[3]` and `[2]` are `2 / 5` and `3 / 5`.

## Main definitions

* `TauCeti.stickelberger m`: the rational Stickelberger element `θ_m`.

## Main results

* `TauCeti.coeff_stickelberger`: the coefficient of `θ_m` at `[b]` is `(b⁻¹)₀ / m`.
* `TauCeti.stickelberger_one`: at `m = 1` the finite-sum formula gives zero.
* `TauCeti.one_add_single_neg_one_mul_stickelberger`: for `1 < m`, with `c = [-1]` the class of
  complex conjugation, `(1 + c) θ_m` is the norm element `∑_a [a]`.
* `TauCeti.augmentation_stickelberger`: for `1 < m`, the augmentation of `θ_m` is `φ(m) / 2`.
* `TauCeti.lift_stickelberger`: the evaluation of `θ_m` at a homomorphism `f` from `(ZMod m)ˣ`
  is `∑_a (a₀ / m) f(a⁻¹)`.
* `TauCeti.lift_stickelberger_eq_generalizedBernoulli`: evaluating `θ_m` at a nontrivial Dirichlet
  character `χ` modulo `m` with values in a domain gives the generalized Bernoulli number
  `B_{1, χ⁻¹}` at modulus `m`.

## References

* R. Sharifi, *Iwasawa theory* (lecture notes), Definition 4.5.1(a) and Theorem 4.5.7.
* L. C. Washington, *Introduction to Cyclotomic Fields*, §6.2.
* C. Birkbeck, AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0), module
  `BernoulliRegular.Stickelberger` of the `FltRegularBernoulli` project, at commit
  `c3bc9bfafaf32cf281da174a7ec287c1e56acc99`: the prime-conductor element
  `BernoulliRegular.stickelbergerElement p`, with the same inverse-indexed basis. The code here
  is not copied from it: `stickelberger` is stated for every modulus, with the coefficient inside
  `single`, and its proofs are separate. It was checked against that source: at a prime `m = p`,
  `stickelberger p` and `stickelbergerElement p` have the same coefficients.
-/

public section

open MonoidAlgebra

namespace TauCeti

variable (m : ℕ) [NeZero m]

/-- The **rational Stickelberger element** `θ_m = ∑_a (a₀ / m) [a⁻¹]` of `ℚ[(ZMod m)ˣ]`, where `a₀`
is the least nonnegative representative of the unit residue `a`. The basis element is indexed by
the inverse of `a`. -/
noncomputable def stickelberger : MonoidAlgebra ℚ (ZMod m)ˣ :=
  ∑ a : (ZMod m)ˣ, single a⁻¹ (((a : ZMod m).val : ℚ) / m)

/-- The defining finite sum of the rational Stickelberger element. -/
theorem stickelberger_def :
    stickelberger m = ∑ a : (ZMod m)ˣ, single a⁻¹ (((a : ZMod m).val : ℚ) / m) :=
  (rfl)

/-- The coefficient of `θ_m` at `[b]` is the least nonnegative representative of `b⁻¹`, divided
by `m`. -/
@[simp]
theorem coeff_stickelberger (b : (ZMod m)ˣ) :
    (stickelberger m).coeff b = (((b⁻¹ : (ZMod m)ˣ) : ZMod m).val : ℚ) / m := by
  classical
  simp [stickelberger_def, coeff_sum, coeff_single, Finsupp.single_apply, inv_eq_iff_eq_inv]

/-- At conductor one the unique unit has representative `0`, so `θ_1 = 0`. -/
@[simp]
theorem stickelberger_one : stickelberger 1 = 0 := by
  refine Finset.sum_eq_zero fun a _ ↦ ?_
  rw [Nat.lt_one_iff.1 (ZMod.val_lt (a : ZMod 1))]
  simp

variable {m}

/-- **Conjugation formula.** For `1 < m`, write `c = [-1]` for the class of complex conjugation.
Then `(1 + c) θ_m` is the norm element `∑_a [a]` of the group ring. At `m = 2` the conjugation is
trivial and this reads `2 θ_2 = [1]`. -/
theorem one_add_single_neg_one_mul_stickelberger (hm : 1 < m) :
    (1 + single (-1) 1) * stickelberger m = ∑ a : (ZMod m)ˣ, single a 1 := by
  classical
  have : Fact (1 < m) := ⟨hm⟩
  ext b
  -- The representatives of the unit `b⁻¹` and of its negative add up to `m`.
  simp [add_mul, coeff_sum, coeff_single, Finsupp.single_apply, coeff_single_mul_apply,
    ← add_div, -ZMod.natCast_val, ZMod.neg_val, Units.ne_zero, Nat.cast_sub (ZMod.val_lt _).le]

/-- For `1 < m`, the augmentation of `θ_m` is `φ(m) / 2`. At `m = 1` the element `θ_1` is zero,
so the formula, which would give `1 / 2`, does not extend there. -/
theorem augmentation_stickelberger (hm : 1 < m) :
    augmentation ℚ (ZMod m)ˣ (stickelberger m) = (m.totient : ℚ) / 2 := by
  have h := congrArg (augmentation ℚ (ZMod m)ˣ) (one_add_single_neg_one_mul_stickelberger hm)
  rw [map_mul, map_add, map_one, augmentation_single, map_sum] at h
  simp only [augmentation_single, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    ZMod.card_units_eq_totient] at h
  rw [eq_div_iff two_ne_zero, ← h]
  ring

variable (m)

/-- The evaluation of `θ_m` at a homomorphism `f : (ZMod m)ˣ →* R` into a `ℚ`-algebra is the
weighted sum `∑_a (a₀ / m) f(a⁻¹)`. -/
theorem lift_stickelberger {R : Type*} [Semiring R] [Algebra ℚ R] (f : (ZMod m)ˣ →* R) :
    lift ℚ R (ZMod m)ˣ f (stickelberger m) =
      ∑ a : (ZMod m)ˣ, algebraMap ℚ R (((a : ZMod m).val : ℚ) / m) * f a⁻¹ := by
  simp [stickelberger_def, Algebra.smul_def]

/-- **Bernoulli evaluation of the Stickelberger element.** Let `χ` be a nontrivial Dirichlet
character modulo `m` with values in a domain `R` of characteristic zero. Evaluating `θ_m` at `χ`
gives the first generalized Bernoulli number of the inverse character at modulus `m`:
`χ(θ_m) = m⁻¹ ∑_a a₀ χ⁻¹(a) = B_{1, χ⁻¹}`. -/
theorem lift_stickelberger_eq_generalizedBernoulli {R : Type*} [CommRing R] [Algebra ℚ R]
    [IsDomain R] {χ : DirichletCharacter R m} (hχ : χ ≠ 1) :
    lift ℚ R (ZMod m)ˣ ((χ : ZMod m →* R).comp (Units.coeHom (ZMod m))) (stickelberger m) =
      χ⁻¹.generalizedBernoulli 1 := by
  rw [DirichletCharacter.generalizedBernoulli_one_of_ne_one (inv_ne_one.2 hχ), lift_stickelberger]
  symm
  -- The character `χ⁻¹` vanishes off the units, so its sum over `ZMod m` is a sum over the units.
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map ⟨Units.val, Units.val_injective⟩))
    fun a _ ha ↦ ?_, Finset.sum_map]
  · refine Finset.sum_congr rfl fun a _ ↦ ?_
    simp [MulChar.inv_apply, mul_comm]
  · have ha' : ¬ IsUnit a := fun ⟨u, hu⟩ ↦ ha (by simp [← hu])
    simp [MulChar.map_nonunit _ (show ¬ IsUnit a from ha')]

end TauCeti
