/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- Public: the finite separable splitting-field theorem and `IsGalois` both occur in the exported
-- theorem. Mathlib's Galois module also supplies the finite and Galois normal-closure instances.
public import TauCeti.Algebra.CentralSimple.FiniteSeparable
public import Mathlib.FieldTheory.Galois.Basic

/-!
# Finite Galois splitting fields

Every finite-dimensional central simple algebra over a field is split by a finite Galois
subextension of a separable closure. Starting with a finite separable splitting field, its normal
closure is still finite and is Galois over the base field. Splitting persists after passing to that
larger field.

This puts the splitting field in the form needed to use its Galois group, for example in the
crossed-product description of central simple algebras.

## Main result

* `TauCeti.Algebra.exists_finiteGalois_splittingField`: a finite-dimensional central simple
  algebra has a finite Galois splitting field inside a separable closure.

## References

See P. Gille and T. Szamuely, *Central Simple Algebras and Galois Cohomology*, Section 2.2,
and R. S. Pierce, *Associative Algebras*, Chapter 13.
-/

public section

namespace TauCeti

namespace Algebra

universe u w

variable (K : Type u) [Field K] (A : Type w) [Ring A] [Algebra K A]
  [FiniteDimensional K A] [Algebra.IsCentral K A] [IsSimpleRing A]

/-- **Every finite-dimensional central simple algebra has a finite Galois splitting field.**

The field is an intermediate field of `SeparableClosure K`, so it comes with its specified
embedding into the separable closure as well as its finite-dimensional, Galois, and splitting
properties. -/
theorem exists_finiteGalois_splittingField :
    ∃ L : IntermediateField K (SeparableClosure K),
      FiniteDimensional K L ∧ IsGalois K L ∧ IsSplittingField K A L := by
  obtain ⟨L, hLfinite, hLsplit⟩ :=
    exists_isSplittingField_finiteDimensional_isSeparable K A
  let _ := hLfinite
  let M := IntermediateField.normalClosure K L (SeparableClosure K)
  have hLM : L ≤ M := IntermediateField.le_normalClosure L
  let _ : Algebra L M := (IntermediateField.inclusion hLM).toRingHom.toAlgebra
  let _ : IsScalarTower K L M := IsScalarTower.of_algHom (IntermediateField.inclusion hLM)
  have hMsplit : IsSplittingField K A M :=
    IsSplittingField.of_isScalarTower (K := K) (A := A) (L := L) hLsplit M
  exact ⟨M, inferInstance, inferInstance, hMsplit⟩

end Algebra

end TauCeti

end
