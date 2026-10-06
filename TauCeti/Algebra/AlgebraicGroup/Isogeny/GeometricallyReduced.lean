/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Isogeny.Basic
public import TauCeti.Algebra.AlgebraicGroup.GeometricallyReduced.FaithfullyFlat

/-!
# Finite dominant homomorphisms to geometrically reduced groups

Over any field, a finite dominant homomorphism to a geometrically reduced affine group
of finite type is an isogeny: faithful flatness follows from finiteness and dominance.
The source need not be reduced, and the field need not be perfect. This criterion lets
quotient and isogeny constructions use geometric hypotheses instead of assuming flatness.

## References

* J. S. Milne, *Algebraic Groups* (2017), Propositions 1.65(a) and 1.70.
-/

public section

open CategoryTheory

namespace TauCeti.CommHopfAlgCat

universe u

variable {k : Type u} [Field k] {H K : _root_.CommHopfAlgCat.{u} k}
  [Algebra.FiniteType k H] [Algebra.IsGeometricallyReduced k H]

/-- A homomorphism to a geometrically reduced finite-type affine group over a field is
an isogeny exactly when it is finite and dominant. No reducedness assumption on the source
or perfection assumption on the field is needed. -/
theorem isIsogeny_iff_finite_and_dominant (f : H ⟶ K) :
    IsIsogeny f ↔ f.hom.toAlgHom.Finite ∧
      DenseRange (PrimeSpectrum.comap f.hom.toAlgHom.toRingHom) := by
  constructor
  · intro hf
    exact ⟨hf.finite,
      ((RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.mp hf.faithfullyFlat).2).denseRange⟩
  · rintro ⟨hfin, hdom⟩
    let := f.hom.toAlgHom.toAlgebra
    have : IsScalarTower k H K :=
      .of_algebraMap_eq fun x ↦ (f.hom.toAlgHom.commutes x).symm
    have : Module.Finite H K := hfin
    have : Algebra.FiniteType k K := .trans (S := H) inferInstance inferInstance
    exact (isIsogeny_iff f).mpr
      ⟨hfin, (faithfullyFlat_iff_dominant_of_isGeometricallyReduced f).mpr hdom⟩

end TauCeti.CommHopfAlgCat
