/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Etale.Pi
public import Mathlib.RingTheory.Localization.Away.Basic
public import TauCeti.RingTheory.Idempotents.BaseChange

/-!
# Étale algebras and idempotent decompositions

Idempotents split an algebra into a product of its clopen components. This file records that
étaleness is compatible with both directions of such a splitting: a binary product of étale
algebras is étale (`TauCeti.Algebra.Etale.prod`), and the quotient of an étale algebra by an
idempotent, which is the complementary component, is étale
(`TauCeti.Algebra.Etale.quotient_span_singleton`). Mathlib supplies the finite products
`Π i, A i` indexed by a type; the binary product `A × B` is reduced to these.

Idempotents of the base split it in the same way, and étaleness is local for such a splitting: an
algebra is étale if its base change to every component of a complete orthogonal family of
idempotents of the base is (`TauCeti.Algebra.Etale.of_completeOrthogonalIdempotents`).
-/

public section

universe u v w

namespace TauCeti.Algebra.Etale

variable {R : Type u} [CommRing R]

section Prod

/-- The family `true ↦ A`, `false ↦ B`, which presents `A × B` as a product indexed by `Bool`.
It is a definition, rather than an abbreviation, so that the instances below are found by
instance search without unfolding `Bool.rec`. -/
private def boolFamily (A B : Type v) (b : Bool) : Type v :=
  Bool.rec B A b

variable {A B : Type v} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

private instance (b : Bool) : CommRing (boolFamily A B b) :=
  Bool.rec (motive := fun b ↦ CommRing (boolFamily A B b)) ‹CommRing B› ‹CommRing A› b

private instance (b : Bool) : Algebra R (boolFamily A B b) :=
  Bool.rec (motive := fun b ↦ Algebra R (boolFamily A B b)) ‹Algebra R B› ‹Algebra R A› b

private instance [Algebra.Etale R A] [Algebra.Etale R B] (b : Bool) :
    Algebra.Etale R (boolFamily A B b) :=
  Bool.rec (motive := fun b ↦ Algebra.Etale R (boolFamily A B b)) ‹_› ‹_› b

/-- The binary product of two étale algebras in the same universe is étale. -/
private theorem prod_of_univ [Algebra.Etale R A] [Algebra.Etale R B] :
    Algebra.Etale R (A × B) := by
  -- `boolFamily A B true` and `boolFamily A B false` unfold by `Bool.rec` to `A` and `B`, and the
  -- instances above to those of `A` and `B`. This definitional equality lets `Pi.evalAlgHom` land
  -- in `A` and `B`, and closes the surjectivity goal by `rfl`; it is used nowhere else.
  let φ : (Π b, boolFamily A B b) →ₐ[R] A × B :=
    (Pi.evalAlgHom R (boolFamily A B) true).prod (Pi.evalAlgHom R (boolFamily A B) false)
  have hφ : Function.Bijective φ := by
    refine ⟨fun f g h ↦ funext fun b ↦ ?_,
      fun p ↦ ⟨fun b ↦ Bool.rec (motive := boolFamily A B) p.2 p.1 b, rfl⟩⟩
    cases b
    · exact congrArg Prod.snd h
    · exact congrArg Prod.fst h
  exact .of_equiv (AlgEquiv.ofBijective φ hφ)

end Prod

/-- A binary product of étale algebras is étale. -/
instance prod {A : Type v} {B : Type w} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    [Algebra.Etale R A] [Algebra.Etale R B] : Algebra.Etale R (A × B) := by
  have : Algebra.Etale R (ULift.{w} A) := .of_equiv ULift.algEquiv.symm
  have : Algebra.Etale R (ULift.{v} B) := .of_equiv ULift.algEquiv.symm
  have : Algebra.Etale R (ULift.{w} A × ULift.{v} B) := prod_of_univ
  exact .of_equiv (AlgEquiv.prodCongr ULift.algEquiv ULift.algEquiv)

/-- The quotient of an étale algebra by an idempotent is étale: it is the localization away from
the complementary idempotent. -/
theorem quotient_span_singleton {S : Type v} [CommRing S] [Algebra R S] [Algebra.Etale R S]
    {e : S} (he : IsIdempotentElem e) : Algebra.Etale R (S ⧸ Ideal.span {e}) := by
  have : IsLocalization.Away (1 - e) (S ⧸ Ideal.span {e}) :=
    IsLocalization.away_of_isIdempotentElem he.one_sub
      (by rw [sub_sub_cancel, Ideal.Quotient.algebraMap_eq, Ideal.mk_ker])
      Ideal.Quotient.mk_surjective
  have : Algebra.Etale S (S ⧸ Ideal.span {e}) := .of_isLocalizationAway (1 - e)
  exact .comp R S _

open TensorProduct in
/-- Étaleness is local for a decomposition of the base by complete orthogonal idempotents: if the
base change of `X` to every component `T ⧸ (1 - f i)` is étale, then `X` is étale over `T`. -/
theorem of_completeOrthogonalIdempotents {T X : Type*} [CommRing T] [CommRing X]
    [Algebra T X] {ι : Type*} [Fintype ι] {f : ι → T} (hf : CompleteOrthogonalIdempotents f)
    (h : ∀ i, Algebra.Etale (T ⧸ Ideal.span {1 - f i}) ((T ⧸ Ideal.span {1 - f i}) ⊗[T] X)) :
    Algebra.Etale T X := by
  classical
  have (i : ι) : Algebra.Etale T ((T ⧸ Ideal.span {1 - f i}) ⊗[T] X) := by
    have := quotient_span_singleton (R := T) (S := T) (hf.idem i).one_sub
    have := h i
    exact Algebra.Etale.comp T (T ⧸ Ideal.span {1 - f i}) _
  exact .of_equiv (hf.tensorProductEquiv X).symm

end TauCeti.Algebra.Etale
