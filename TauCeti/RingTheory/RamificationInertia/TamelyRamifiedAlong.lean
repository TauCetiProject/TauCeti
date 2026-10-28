/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.Ideal.Over

/-!
# Unramified and tamely ramified algebras along a principal divisor

Let `R` be a commutative ring, `S` an `R`-algebra and `a ∈ R`. We say that `S` is *tamely
ramified along `a`* (`TauCeti.Algebra.IsTamelyRamifiedAlong R S a`) if for every prime `Q` of `S`
minimal over `aS` and lying over a prime `p` of `R` minimal over `aR`, the residue field
extension `κ(p) ⊆ κ(Q)` is separable and the ramification index of `Q` over `R` is invertible in
`κ(p)`. It is *unramified along `a`* (`TauCeti.Algebra.IsUnramifiedAlong R S a`) if the
ramification index is one instead.

For `R` Noetherian, `a` a nonzerodivisor with `R / aR` reduced and `S` the integral closure of
`R` in a finite étale `R[1/a]`-algebra, these are the affine forms of Stacks' notions of being
unramified, resp. tamely ramified, over `Spec R` in codimension one, relative to the open
`D(a)` (Stacks, Section 58.31).

## Main definitions

* `TauCeti.Algebra.IsUnramifiedAlong`
* `TauCeti.Algebra.IsTamelyRamifiedAlong`

## Main results

* `TauCeti.Algebra.IsUnramifiedAlong.isTamelyRamifiedAlong`: unramified implies tamely ramified.

## References

* [Stacks Project, Section 58.31](https://stacks.math.columbia.edu/tag/0BSE).
-/

public section

namespace TauCeti.Algebra

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] (a : R)

/-- `S` is **unramified along `a`**: for every prime `Q` of `S` minimal over `aS` lying over a
prime minimal over `aR`, the residue field extension is separable and the ramification index of
`Q` over `R` is one. Under the hypotheses of the module docstring on `R`, `a` and `S`, this is the
affine form, along the principal divisor `V(a)`, of Stacks' "unramified over `X` in codimension
one" (Section 58.31). -/
@[stacks 0BSE "affine form along a principal divisor"]
def IsUnramifiedAlong : Prop :=
  ∀ (Q : Ideal S) [Q.IsPrime], Q.under R ∈ (Ideal.span {a}).minimalPrimes →
    Q ∈ ((Ideal.span {a}).map (algebraMap R S)).minimalPrimes →
    letI := Localization.AtPrime.algebraOfLiesOver (Q.under R) Q
    Algebra.IsSeparable (Q.under R).ResidueField Q.ResidueField ∧ Q.ramificationIdx R = 1

/-- `S` is **tamely ramified along `a`**: for every prime `Q` of `S` minimal over `aS` lying over a
prime minimal over `aR`, the residue field extension is separable and the ramification index of
`Q` over `R` is invertible in the residue field below. Under the hypotheses of the module
docstring on `R`, `a` and `S`, this is the affine form, along the principal divisor `V(a)`, of
Stacks' "tamely ramified over `X` in codimension one" (Section 58.31). -/
@[stacks 0BSE "affine form along a principal divisor"]
def IsTamelyRamifiedAlong : Prop :=
  ∀ (Q : Ideal S) [Q.IsPrime], Q.under R ∈ (Ideal.span {a}).minimalPrimes →
    Q ∈ ((Ideal.span {a}).map (algebraMap R S)).minimalPrimes →
    letI := Localization.AtPrime.algebraOfLiesOver (Q.under R) Q
    Algebra.IsSeparable (Q.under R).ResidueField Q.ResidueField ∧
      IsUnit ((Q.ramificationIdx R : ℕ) : (Q.under R).ResidueField)

variable {R S a}

/-- Unfolds `IsUnramifiedAlong` to its defining condition on primes of `S`. -/
theorem isUnramifiedAlong_def :
    IsUnramifiedAlong R S a ↔
      ∀ (Q : Ideal S) [Q.IsPrime], Q.under R ∈ (Ideal.span {a}).minimalPrimes →
        Q ∈ ((Ideal.span {a}).map (algebraMap R S)).minimalPrimes →
        letI := Localization.AtPrime.algebraOfLiesOver (Q.under R) Q
        Algebra.IsSeparable (Q.under R).ResidueField Q.ResidueField ∧
          Q.ramificationIdx R = 1 :=
  Iff.rfl

/-- Unfolds `IsTamelyRamifiedAlong` to its defining condition on primes of `S`. -/
theorem isTamelyRamifiedAlong_def :
    IsTamelyRamifiedAlong R S a ↔
      ∀ (Q : Ideal S) [Q.IsPrime], Q.under R ∈ (Ideal.span {a}).minimalPrimes →
        Q ∈ ((Ideal.span {a}).map (algebraMap R S)).minimalPrimes →
        letI := Localization.AtPrime.algebraOfLiesOver (Q.under R) Q
        Algebra.IsSeparable (Q.under R).ResidueField Q.ResidueField ∧
          IsUnit ((Q.ramificationIdx R : ℕ) : (Q.under R).ResidueField) :=
  Iff.rfl

/-- If `S` is unramified along `a`, then it is tamely ramified along `a`. -/
theorem IsUnramifiedAlong.isTamelyRamifiedAlong (h : IsUnramifiedAlong R S a) :
    IsTamelyRamifiedAlong R S a := fun Q _ h₁ h₂ ↦
  ⟨(h Q h₁ h₂).1, by simp [(h Q h₁ h₂).2]⟩

/-- Every ring is unramified along every element over itself: at each prime the ramification index
is one and the residue field extension is trivial. -/
theorem isUnramifiedAlong_self (R : Type*) [CommRing R] (a : R) : IsUnramifiedAlong R R a := by
  intro Q _ _ _
  exact ⟨inferInstance, Ideal.ramificationIdx_eq_one Q R⟩

/-- Every ring is tamely ramified along every element over itself. -/
theorem isTamelyRamifiedAlong_self (R : Type*) [CommRing R] (a : R) :
    IsTamelyRamifiedAlong R R a :=
  (isUnramifiedAlong_self R a).isTamelyRamifiedAlong

end TauCeti.Algebra
