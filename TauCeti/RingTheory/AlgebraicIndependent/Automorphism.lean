/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.Basic

/-!
# Algebra endomorphisms, orbits of algebraic elements, and eigenvector independence

Let `A` be a commutative integral domain that is a faithful algebra over a commutative ring `R`,
and let `σ : A →ₐ[R] A` be an `R`-algebra endomorphism. This file proves two general criteria
linking the dynamics of `σ` to algebraicity and algebraic independence over `R`:

1. **Finite orbits of algebraic elements.** Every element `x : A` algebraic over `R` satisfies a
   nonzero polynomial over `R`, whose root set in the domain `A` is finite and `σ`-invariant.
   Consequently the iterates `(σ ^ n) x` repeat (`IsAlgebraic.exists_pow_apply_eq_of_algHom`), and
   if `σ` is an `R`-algebra automorphism (`A ≃ₐ[R] A`), some positive iterate fixes `x`
   (`IsAlgebraic.exists_pow_apply_eq_self_of_algEquiv`). Equivalently, an element with no
   nontrivial fixing power of `σ` is transcendental over `R`.

2. **Algebraic independence of multiplicatively independent eigenvectors.** Suppose `(yᵢ)` is a
   family of nonzero elements of `A` satisfying `σ (yᵢ) = algebraMap R A (uᵢ) * yᵢ` for scalars
   `uᵢ : R`. If the monomial-eigenvalue map `d ↦ ∏ᵢ uᵢ ^ (d i)` on finitely supported exponent
   tuples `ι →₀ ℕ` is injective, then `(yᵢ)` is algebraically independent over `R`
   (`TauCeti.algebraicIndependent_of_algHom_eigenvectors`): distinct monomials in the `yᵢ` lie in
   distinct `σ`-eigenspaces, so applying `σ - μ(d₀)` annihilates one monomial at a time.

## Main results

* `IsAlgebraic.exists_pow_apply_eq_of_algHom`: iterates of an `R`-algebra endomorphism on an
  algebraic element of a domain eventually collide.
* `IsAlgebraic.exists_pow_apply_eq_self_of_algEquiv`: every algebraic element of a domain is fixed
  by some positive power of any `R`-algebra automorphism.
* `TauCeti.transcendental_of_forall_pow_algEquiv_ne_self`: an element moved by every positive
  power of an `R`-algebra automorphism is transcendental over `R`.
* `TauCeti.algebraicIndependent_of_algHom_eigenvectors`: nonzero `σ`-eigenvectors whose eigenvalues
  have injective monomial products are algebraically independent over `R`.
-/

public section

namespace IsAlgebraic

variable {R A : Type*} [CommRing R] [CommRing A] [IsDomain A] [Algebra R A] [FaithfulSMul R A]

private theorem pow_algHom_mem_rootSet {p : Polynomial R} (hp0 : p ≠ 0) {x : A}
    (hx : Polynomial.aeval x p = 0) (σ : A →ₐ[R] A) :
    ∀ n : ℕ, (σ ^ n) x ∈ p.rootSet A
  | 0 => by
      rw [pow_zero, AlgHom.one_apply, Polynomial.mem_rootSet',
        Polynomial.map_ne_zero_iff (FaithfulSMul.algebraMap_injective R A)]
      exact ⟨hp0, hx⟩
  | n + 1 => by
      have hn := pow_algHom_mem_rootSet hp0 hx σ n
      have hmul : (σ ^ (n + 1)) x = σ ((σ ^ n) x) := by
        rw [pow_succ', AlgHom.mul_apply]
      rw [hmul]
      exact Polynomial.rootSet_maps_to' (fun h ↦ h) σ hn

/-- In a domain `A` faithful over `R`, the iterates of an `R`-algebra endomorphism `σ : A →ₐ[R] A`
on an algebraic element `x` eventually repeat. -/
theorem exists_pow_apply_eq_of_algHom {x : A} (hx : IsAlgebraic R x) (σ : A →ₐ[R] A) :
    ∃ i j : ℕ, i < j ∧ (σ ^ i) x = (σ ^ j) x := by
  obtain ⟨p, hp0, hpx⟩ := hx
  let f : ℕ → p.rootSet A := fun n ↦ ⟨(σ ^ n) x, pow_algHom_mem_rootSet hp0 hpx σ n⟩
  obtain ⟨i, j, hij⟩ := Finite.exists_ne_map_eq_of_infinite f
  have heq : (σ ^ i) x = (σ ^ j) x := congrArg Subtype.val hij.2
  rcases lt_or_gt_of_ne hij.1 with hlt | hgt
  · exact ⟨i, j, hlt, heq⟩
  · exact ⟨j, i, hgt, heq.symm⟩

/-- In a domain `A` faithful over `R`, every element algebraic over `R` is fixed by some nonzero
power of any `R`-algebra automorphism `σ : A ≃ₐ[R] A`. -/
theorem exists_pow_apply_eq_self_of_algEquiv {x : A} (hx : IsAlgebraic R x) (σ : A ≃ₐ[R] A) :
    ∃ n : ℕ, n ≠ 0 ∧ (σ ^ n) x = x := by
  have hpow : ∀ (m : ℕ) (y : A), (σ.toAlgHom ^ m) y = (σ ^ m) y := by
    intro m
    induction m with
    | zero => intro y; rfl
    | succ m ih =>
        intro y
        rw [pow_succ', pow_succ', AlgHom.mul_apply, AlgEquiv.mul_apply, ih, AlgEquiv.coe_toAlgHom]
  obtain ⟨i, j, hij, heq⟩ := hx.exists_pow_apply_eq_of_algHom σ.toAlgHom
  rw [hpow, hpow] at heq
  refine ⟨j - i, Nat.sub_ne_zero_of_lt hij, ?_⟩
  apply (σ ^ i).injective
  have hmul : (σ ^ i * σ ^ (j - i)) x = (σ ^ j) x := by
    rw [← pow_add, Nat.add_sub_of_le hij.le]
  rw [← AlgEquiv.mul_apply, hmul, ← heq]

end IsAlgebraic

namespace TauCeti

section Orbit

variable {R A : Type*} [CommRing R] [CommRing A] [IsDomain A] [Algebra R A] [FaithfulSMul R A]

/-- In a domain `A` faithful over `R`, an element moved by every positive power of an `R`-algebra
automorphism `σ : A ≃ₐ[R] A` is transcendental over `R`. -/
theorem transcendental_of_forall_pow_algEquiv_ne_self (σ : A ≃ₐ[R] A) {x : A}
    (h : ∀ n : ℕ, n ≠ 0 → (σ ^ n) x ≠ x) : Transcendental R x := by
  intro hx
  obtain ⟨n, hn0, hnx⟩ := hx.exists_pow_apply_eq_self_of_algEquiv σ
  exact h n hn0 hnx

end Orbit

section Eigenvectors

variable {R A ι : Type*} [CommRing R] [CommRing A] [Algebra R A]

private theorem map_aeval_monomial_of_eigenvectors (σ : A →ₐ[R] A) {u : ι → R} {y : ι → A}
    (hσ : ∀ i, σ (y i) = algebraMap R A (u i) * y i) (d : ι →₀ ℕ) (c : R) :
    σ (MvPolynomial.aeval y (MvPolynomial.monomial d c)) =
      algebraMap R A (d.prod fun i k ↦ u i ^ k) *
        MvPolynomial.aeval y (MvPolynomial.monomial d c) := by
  rw [MvPolynomial.aeval_monomial, map_mul, AlgHom.commutes, map_finsuppProd]
  have hprod : (d.prod fun i k ↦ σ (y i ^ k)) =
      (d.prod fun i k ↦ algebraMap R A (u i ^ k)) * d.prod fun i k ↦ y i ^ k := by
    rw [← Finsupp.prod_mul]
    refine Finsupp.prod_congr fun i _ ↦ ?_
    rw [map_pow, hσ, mul_pow, map_pow]
  rw [hprod, ← map_finsuppProd]
  ring

/-- **Algebraic independence of eigenvectors with multiplicatively independent eigenvalues.**
Let `σ : A →ₐ[R] A` be an `R`-algebra endomorphism of a domain `A` faithful over `R`, and let
`y : ι → A` be nonzero elements satisfying `σ (y i) = algebraMap R A (u i) * y i`. If distinct
monomial exponent tuples `d : ι →₀ ℕ` produce distinct products `∏ i, u i ^ d i` in `R`, then `y`
is algebraically independent over `R`. -/
theorem algebraicIndependent_of_algHom_eigenvectors [IsDomain A] [FaithfulSMul R A]
    (σ : A →ₐ[R] A) {u : ι → R} {y : ι → A}
    (hy0 : ∀ i, y i ≠ 0) (hσ : ∀ i, σ (y i) = algebraMap R A (u i) * y i)
    (hu : Function.Injective fun d : ι →₀ ℕ ↦ d.prod fun i k ↦ u i ^ k) :
    AlgebraicIndependent R y := by
  classical
  let μ : (ι →₀ ℕ) → R := fun d ↦ d.prod fun i k ↦ u i ^ k
  have hinjR : Function.Injective (algebraMap R A) := FaithfulSMul.algebraMap_injective R A
  rw [algebraicIndependent_iff]
  suffices ∀ n : ℕ, ∀ P : MvPolynomial ι R, P.support.card = n →
      MvPolynomial.aeval y P = 0 → P = 0 by
    intro P hP
    exact this P.support.card P rfl hP
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro P hcard hP
    by_cases hP0 : P = 0
    · exact hP0
    obtain ⟨d₀, hd₀⟩ := MvPolynomial.support_nonempty.2 hP0
    let P' : MvPolynomial ι R :=
      ∑ d ∈ P.support, MvPolynomial.monomial d ((μ d - μ d₀) * P.coeff d)
    have hcoeff : ∀ d, P'.coeff d = (μ d - μ d₀) * P.coeff d := by
      intro d
      rw [MvPolynomial.coeff_sum]
      simp only [MvPolynomial.coeff_monomial, Finset.sum_ite_eq']
      by_cases hd : d ∈ P.support
      · simp [hd]
      · simp [hd, MvPolynomial.notMem_support_iff.1 hd]
    have hsupp_sub : P'.support ⊆ P.support := by
      intro d hd
      rw [MvPolynomial.mem_support_iff, hcoeff] at hd
      exact MvPolynomial.mem_support_iff.2 (right_ne_zero_of_mul hd)
    have hd₀_notMem : d₀ ∉ P'.support := by
      rw [MvPolynomial.mem_support_iff, hcoeff, sub_self, zero_mul, not_not]
    have hcard_lt : P'.support.card < n := by
      rw [← hcard]
      exact Finset.card_lt_card
        (Finset.ssubset_iff_of_subset hsupp_sub |>.2 ⟨d₀, hd₀, hd₀_notMem⟩)
    have haeval' : MvPolynomial.aeval y P' = 0 := by
      have hdecomp : MvPolynomial.aeval y P =
          ∑ d ∈ P.support, MvPolynomial.aeval y (MvPolynomial.monomial d (P.coeff d)) := by
        conv_lhs => rw [P.as_sum]
        rw [map_sum]
      have hsum : MvPolynomial.aeval y P' =
          σ (MvPolynomial.aeval y P) - algebraMap R A (μ d₀) * MvPolynomial.aeval y P := by
        simp only [P', map_sum]
        rw [hdecomp, map_sum σ, Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun d _ ↦ ?_
        rw [map_aeval_monomial_of_eigenvectors σ hσ d (P.coeff d),
          MvPolynomial.aeval_monomial, MvPolynomial.aeval_monomial]
        simp only [μ, map_mul, map_sub]
        ring
      rw [hsum, hP, map_zero, mul_zero, sub_zero]
    have hP'0 : P' = 0 := ih P'.support.card hcard_lt P' rfl haeval'
    have hsingleton : P.support = {d₀} := by
      refine Finset.eq_singleton_iff_unique_mem.2 ⟨hd₀, fun d hd ↦ ?_⟩
      by_contra hne
      have h0 : (μ d - μ d₀) * P.coeff d = 0 := by
        simpa [hP'0] using (hcoeff d).symm
      have h0A : algebraMap R A (μ d - μ d₀) * algebraMap R A (P.coeff d) = 0 := by
        rw [← map_mul, h0, map_zero]
      rcases mul_eq_zero.1 h0A with hμ | hc
      · exact hne (hu (sub_eq_zero.1 (hinjR (hμ.trans (map_zero _).symm))))
      · exact (MvPolynomial.mem_support_iff.1 hd) (hinjR (hc.trans (map_zero _).symm))
    have hPmon : P = MvPolynomial.monomial d₀ (P.coeff d₀) := by
      conv_lhs => rw [P.as_sum, hsingleton, Finset.sum_singleton]
    rw [hPmon, MvPolynomial.aeval_monomial] at hP
    have hyprod : (d₀.prod fun i k ↦ y i ^ k) ≠ 0 := by
      rw [Finsupp.prod]
      exact Finset.prod_ne_zero_iff.2 fun i _ ↦ pow_ne_zero _ (hy0 i)
    rcases mul_eq_zero.1 hP with hc0 | hprod0
    · exact absurd (hinjR (hc0.trans (map_zero _).symm)) (MvPolynomial.mem_support_iff.1 hd₀)
    · exact absurd hprod0 hyprod

end Eigenvectors

end TauCeti
