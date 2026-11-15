/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Etale.FiniteEtaleSplit.Basic
import Mathlib.Algebra.Algebra.Shrink
import Mathlib.Data.Fintype.EquivFin
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.RingTheory.Finiteness.Small
import TauCeti.RingTheory.Spectrum.Prime.FreeLocus

/-!
# Finite étale algebras of constant rank, and splitting after a faithfully flat extension

The rank of a finite étale `R`-algebra `S` is a locally constant function on `Spec R`, so it may
take different values on different clopen pieces. Many constructions with finite étale covers,
such as Lenstra's splitting cover (Mathlib's `Algebra.IsFiniteSplit.exists_tensorProduct_of_etale`)
or the Galois closure by ordered tuples of distinct points, are stated for algebras of constant
rank `n`. This file refines the constant-rank splitting cover to identify the split sheets with any
finite index type `ι` of cardinality `n` and allow `S` in an arbitrary universe, and reduces the
general case to the constant-rank one: `S` is a direct factor of the finite étale algebra
`S × ∏_{j < n} R ⧸ (1 - e j)` of constant rank `n`, where `n` bounds the rank of `S` and the
idempotent `e j` cuts out the locus where `j + rank S < n`.

As a consequence, every finite étale `R`-algebra becomes totally split, in the sense of
`TauCeti.Algebra.IsTotallySplit` (a finite product of quotients by idempotents, so with ranks that
may vary), after base change to some faithfully flat finite étale `R`-algebra.

## Main results

* `TauCeti.Algebra.exists_etale_rankAtStalk_prod_pi_quotient_eq`: a finite étale algebra is a
  direct factor of a finite étale algebra of constant rank.
* `TauCeti.Algebra.exists_faithfullyFlat_etale_algEquiv_pi`: a finite étale algebra of constant
  rank `Fintype.card ι` becomes `T`-isomorphic to `ι → T` over a faithfully flat finite étale `T`.
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

section SplitCover

variable {R : Type u} {S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Algebra.Etale R S]
  [Module.Finite R S]

/-- **Splitting a finite étale algebra of constant rank.** Let `S` be a finite étale `R`-algebra of
constant stalk rank `Fintype.card ι`, with `R : Type u` and `S` in any universe. Then there exist a
faithfully flat finite étale `R`-algebra `T : Type u` and a `T`-algebra isomorphism
`T ⊗[R] S ≃ₐ[T] (ι → T)`. This refines Mathlib's
`Algebra.IsFiniteSplit.exists_tensorProduct_of_etale` by identifying the split sheets with `ι` and
allowing `S` in an arbitrary universe. -/
theorem exists_faithfullyFlat_etale_algEquiv_pi {ι : Type*} [Fintype ι]
    (h : Module.rankAtStalk (R := R) S = Fintype.card ι) :
    ∃ (T : Type u) (_ : CommRing T) (_ : Algebra R T) (_ : Module.FaithfullyFlat R T)
      (_ : Module.Finite R T) (_ : Algebra.Etale R T), Nonempty (T ⊗[R] S ≃ₐ[T] (ι → T)) := by
  cases subsingleton_or_nontrivial R
  · have : Subsingleton (R ⊗[R] S) := Module.subsingleton R _
    exact ⟨R, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      ⟨default⟩⟩
  have : Small.{u} S := Module.Finite.small R S
  let eS : Shrink.{u} S ≃ₐ[R] S := Shrink.algEquiv R S
  have : Algebra.Etale R (Shrink.{u} S) := .of_equiv eS.symm
  have : Module.Finite R (Shrink.{u} S) := .equiv eS.symm.toLinearEquiv
  have h₀ : Module.rankAtStalk (R := R) (Shrink.{u} S) = Fintype.card ι :=
    (Module.rankAtStalk_eq_of_equiv eS.toLinearEquiv).trans h
  obtain ⟨T, _, _, hT, hfin, het, _⟩ := Algebra.IsFiniteSplit.exists_tensorProduct_of_etale h₀
  obtain ⟨m, ⟨f⟩⟩ := Algebra.IsFiniteSplit.nonempty_algEquiv_fun T (T ⊗[R] Shrink.{u} S)
  have : Nontrivial T := (FaithfulSMul.algebraMap_injective R T).nontrivial
  obtain rfl : m = Fintype.card ι := by
    simpa using f.toLinearEquiv.finrank_eq.symm.trans
      (TauCeti.Module.finrank_tensorProduct_eq_of_rankAtStalk_eq h₀)
  exact ⟨T, _, _, hT, hfin, het, ⟨(Algebra.TensorProduct.congr AlgEquiv.refl eS.symm).trans
    (f.trans (AlgEquiv.piCongrLeft' T (fun _ ↦ T) (Fintype.equivFin ι).symm))⟩⟩

/-- **Finite étale algebras split after a faithfully flat finite étale extension.** For every
finite étale `R`-algebra `S` there is a faithfully flat finite étale `R`-algebra `T` such that
`T ⊗[R] S` is totally split over `T`. Unlike in Mathlib's
`Algebra.IsFiniteSplit.exists_tensorProduct_of_etale`, the rank of `S` need not be constant and `S`
need not live in the universe of `R`; the split algebra `T ⊗[R] S` may have varying rank. -/
theorem exists_faithfullyFlat_etale_isTotallySplit_tensorProduct :
    ∃ (T : Type u) (_ : CommRing T) (_ : Algebra R T) (_ : Module.FaithfullyFlat R T)
      (_ : Module.Finite R T) (_ : Algebra.Etale R T), IsTotallySplit T (T ⊗[R] S) := by
  obtain ⟨n, e, -, _, hrank⟩ := exists_etale_rankAtStalk_prod_pi_quotient_eq R S
  -- Split the padded algebra of constant rank `n`, and keep its factor `T ⊗[R] S`.
  obtain ⟨T, _, _, hT, hfin, het, ⟨f⟩⟩ :=
    exists_faithfullyFlat_etale_algEquiv_pi (ι := Fin n) (by simpa using hrank)
  have : Algebra.IsFiniteSplit T (T ⊗[R] (S × Π j, R ⧸ Ideal.span {1 - e j})) := ⟨n, ⟨f⟩⟩
  have h : IsTotallySplit T (T ⊗[R] (S × Π j, R ⧸ Ideal.span {1 - e j})) := .of_isFiniteSplit
  exact ⟨T, _, _, hT, hfin, het,
    (h.of_algEquiv (Algebra.TensorProduct.prodRight R T T _ _)).of_prod_fst⟩

end SplitCover

end TauCeti.Algebra
