/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Etale.FiniteEtaleSplit.Basic
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Finiteness.Prod

/-!
# Finite étale algebras of constant rank, and splitting after a faithfully flat extension

The rank of a finite étale `R`-algebra `S` is a locally constant function on `Spec R`, so it may
take different values on different clopen pieces. Many constructions with finite étale covers,
such as Lenstra's splitting cover (Mathlib's `Algebra.IsFiniteSplit.exists_tensorProduct_of_etale`)
or the Galois closure by ordered tuples of distinct points, are stated for algebras of constant
rank `n`. This file reduces the general case to that one: `S` is a direct factor of the finite
étale algebra `S × ∏_{j < n} R ⧸ (1 - e j)` of constant rank `n`, where `n` bounds the rank of `S`
and the idempotent `e j` cuts out the locus where `j + rank S < n`.

As a consequence, every finite étale `R`-algebra becomes totally split, in the sense of
`TauCeti.Algebra.IsTotallySplit` (a finite product of quotients by idempotents, so with ranks that
may vary), after base change to some faithfully flat finite étale `R`-algebra.

## Main results

* `TauCeti.Algebra.exists_etale_rankAtStalk_prod_pi_quotient_eq`: a finite étale algebra is a
  direct factor of a finite étale algebra of constant rank.
* `TauCeti.Algebra.exists_faithfullyFlat_etale_isTotallySplit_tensorProduct`: a finite étale
  algebra is totally split after base change to a faithfully flat finite étale algebra.

## References

* H. W. Lenstra, *Galois theory for schemes*, Proposition 5.10.
* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: foundations*, Remark 1.4.7.
-/

public section

open TensorProduct

universe u

namespace TauCeti.Algebra

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] [Algebra.Etale R S]
  [Module.Finite R S]

/-- **Padding a finite étale algebra to constant rank.** A finite étale `R`-algebra `S` is a direct
factor of the finite étale `R`-algebra `S × ∏_{j < n} R ⧸ (1 - e j)` of constant rank `n`, for some
`n` and some idempotents `e j` of `R`. -/
theorem exists_etale_rankAtStalk_prod_pi_quotient_eq :
    ∃ (n : ℕ) (e : Fin n → R), (∀ j, IsIdempotentElem (e j)) ∧
      Algebra.Etale R (S × Π j, R ⧸ Ideal.span {1 - e j}) ∧
      Module.rankAtStalk (R := R) (S × Π j, R ⧸ Ideal.span {1 - e j}) = n := by
  have : Module.FinitePresentation R S := .of_finite_of_finitePresentation R S
  -- The rank of `S` is locally constant on the compact space `Spec R`, hence bounded.
  obtain ⟨n, hn⟩ := (Module.isLocallyConstant_rankAtStalk (R := R) (M := S)).range_finite.bddAbove
  obtain ⟨e, he, hrank⟩ := Module.exists_rankAtStalk_prod_pi_quotient_eq (R := R) S
    fun p ↦ hn ⟨p, rfl⟩
  have (j : Fin n) : Algebra.Etale R (R ⧸ Ideal.span {1 - e j}) :=
    Etale.quotient_span_singleton (he j).one_sub
  exact ⟨n, e, he, inferInstance, hrank⟩

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Algebra.Etale R S]
  [Module.Finite R S]

/-- **Finite étale algebras split after a faithfully flat finite étale extension.** For every
finite étale `R`-algebra `S` there is a faithfully flat finite étale `R`-algebra `T` such that
`T ⊗[R] S` is totally split over `T`. Unlike in Mathlib's
`Algebra.IsFiniteSplit.exists_tensorProduct_of_etale`, the rank of `S` need not be constant, and
the split algebra `T ⊗[R] S` then has varying rank too. -/
theorem exists_faithfullyFlat_etale_isTotallySplit_tensorProduct :
    ∃ (T : Type u) (_ : CommRing T) (_ : Algebra R T) (_ : Module.FaithfullyFlat R T)
      (_ : Module.Finite R T) (_ : Algebra.Etale R T), IsTotallySplit T (T ⊗[R] S) := by
  obtain ⟨n, e, -, _, hrank⟩ := exists_etale_rankAtStalk_prod_pi_quotient_eq R S
  -- Split the padded algebra of constant rank `n`, and keep its factor `T ⊗[R] S`.
  obtain ⟨T, _, _, hT, hfin, het, _⟩ :=
    Algebra.IsFiniteSplit.exists_tensorProduct_of_etale hrank
  have h : IsTotallySplit T (T ⊗[R] (S × Π j, R ⧸ Ideal.span {1 - e j})) := .of_isFiniteSplit
  exact ⟨T, _, _, hT, hfin, het,
    (h.of_algEquiv (Algebra.TensorProduct.prodRight R T T _ _)).of_prod_fst⟩

end TauCeti.Algebra
