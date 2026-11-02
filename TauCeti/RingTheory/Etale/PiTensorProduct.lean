/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Etale.Basic
public import TauCeti.RingTheory.PiTensorProduct.Equiv

import Mathlib.Data.Fintype.Option

/-!
# Étale indexed tensor products

A tensor product of finitely many étale algebras is étale. The family may be dependent and the
index type may be empty; the empty tensor product is the base ring. Together with Mathlib's
`PiTensorProduct.finite`, this also shows that finite indexed tensor products of finite étale
algebras are finite étale.

In particular, tensor powers of a finite étale algebra remain finite étale. Their idempotent
components can therefore be used to construct finite étale algebras of ordered distinct points.
-/

public section

open scoped TensorProduct

namespace TauCeti.Algebra.Etale

universe u v w

variable {R : Type u} [CommRing R]

/-- A finite indexed tensor product of étale algebras is étale, including the empty tensor
product. No module-finiteness assumption on the individual algebras is required. -/
instance piTensorProduct {ι : Type v} [Finite ι] (A : ι → Type w)
    [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)] [∀ i, Algebra.Etale R (A i)] :
    Algebra.Etale R (⨂[R] i, A i) := by
  suffices h : ∀ (ι : Type v) [Finite ι] (A : ι → Type w) [∀ i, CommRing (A i)]
      [∀ i, Algebra R (A i)] [∀ i, Algebra.Etale R (A i)],
      Algebra.Etale R (⨂[R] i, A i) from h ι A
  intro ι _
  induction ι using Finite.induction_empty_option with
  | of_equiv e ih =>
    intro A _ _ _
    have := ih (fun i ↦ A (e i))
    exact .of_equiv (PiTensorProduct.reindexAlgEquiv A e.symm).symm
  | h_empty =>
    intro A _ _ _
    exact .of_equiv (PiTensorProduct.isEmptyAlgEquiv _ A).symm
  | h_option ih =>
    intro A _ _ _
    have := ih (fun i ↦ A (some i))
    have : Algebra.Etale R ((⨂[R] i, A (some i)) ⊗[R] A none) :=
      .comp R (⨂[R] i, A (some i)) _
    exact .of_equiv (PiTensorProduct.optionAlgEquiv A).symm

end TauCeti.Algebra.Etale
