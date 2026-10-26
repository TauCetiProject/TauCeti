/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TotallySplit

/-!
# Splitting finite étale algebras over a field

A finite étale algebra becomes a product of copies of the ground field after a finite
separable field extension. Thus all the points of a finite étale scheme can be labelled
over one finite separable extension, even when the ground field is imperfect.

The construction uses Mathlib's `Algebra.IsFiniteSplit.exists_tensorProduct_of_etale`,
which supplies a finite faithfully flat étale splitting algebra. A maximal-ideal quotient
of that algebra is a finite separable field and still splits the original algebra.

## References

* The Stacks Project, Tag 03QR (finite étale schemes over a field).
* H. W. Lenstra, *Galois theory for schemes*, Section 5.
-/

public section

open scoped TensorProduct

namespace TauCeti.Algebra.Etale

universe u

/-- A finite étale algebra over a field splits after a finite separable field extension.
The extension has the same universe as the original algebra and the ground field. -/
theorem exists_isFiniteSplit_tensorProduct (K A : Type u) [Field K] [CommRing A]
    [Algebra K A] [Algebra.Etale K A] :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L)
      (_ : Module.Finite K L) (_ : Algebra.IsSeparable K L),
      Algebra.IsFiniteSplit L (L ⊗[K] A) := by
  have : Module.Finite K A := Algebra.FormallyUnramified.finite_of_free K A
  obtain ⟨B, _, _, _, _, _, hB⟩ :=
    Algebra.IsFiniteSplit.exists_tensorProduct_of_etale (R := K) (S := A)
      (Module.rankAtStalk_eq_finrank_of_free (R := K) (M := A))
  have : Nontrivial B := (TensorProduct.lid K B).symm.toEquiv.nontrivial
  obtain ⟨m, hm⟩ := Ideal.exists_maximal B
  let := hm
  let : Field (B ⧸ m) := Ideal.Quotient.field m
  have : Algebra.IsSeparable K (B ⧸ m) := inferInstance
  have : Algebra.IsFiniteSplit (B ⧸ m) ((B ⧸ m) ⊗[B] (B ⊗[K] A)) := inferInstance
  exact ⟨B ⧸ m, inferInstance, inferInstance, inferInstance, inferInstance,
    Algebra.IsFiniteSplit.of_algEquiv
      (Algebra.TensorProduct.cancelBaseChange K B (B ⧸ m) (B ⧸ m) A)⟩

end TauCeti.Algebra.Etale
