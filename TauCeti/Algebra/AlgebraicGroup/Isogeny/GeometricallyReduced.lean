/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Isogeny.Descent
public import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.Flat
import Mathlib.RingTheory.TensorProduct.Finite
import TauCeti.RingTheory.Spectrum.Prime.Topology

/-!
# Finite dominant homomorphisms to geometrically reduced groups

Over any field, a finite dominant homomorphism to a geometrically reduced affine group
of finite type is an isogeny: faithful flatness follows from finiteness and dominance.
The source need not be reduced, and the field need not be perfect. This criterion lets
quotient and isogeny constructions use geometric hypotheses instead of assuming flatness.

The algebraically closed case is `TauCeti.CommHopfAlgCat.faithfullyFlat_of_dominant`, whose
finite-type hypothesis on the source holds because the morphism is finite. We apply it after
extending scalars to an algebraic closure, then use faithfully flat descent of isogenies. The common
universe is required by the existing isogeny descent theorem.

## References

* J. S. Milne, *Algebraic Groups* (2017), Propositions 1.65(a) and 1.70.
-/

public section

open CategoryTheory
open scoped TensorProduct

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
    have : IsReduced H := Algebra.isReduced_of_isGeometricallyReduced k
    have hinj : Function.Injective f.hom :=
      (RingHom.denseRange_comap_iff_injective _).mp hdom
    let L := AlgebraicClosure k
    let fL := baseChangeMap (K := L) f
    have hdomL : DenseRange (PrimeSpectrum.comap fL.hom.toAlgHom.toRingHom) :=
      RingHom.denseRange_comap_of_injective _ (baseChangeMap_injective f hinj)
    have hmap : fL.hom.toAlgHom.toRingHom =
        (Algebra.TensorProduct.map (AlgHom.id k L) f.hom.toAlgHom).toRingHom := by
      exact congrArg (fun g ↦ g.toAlgHom.toRingHom) (hom_baseChangeMap (K := L) f)
    have hfinL : fL.hom.toAlgHom.toRingHom.Finite := by
      rw [hmap]
      exact RingHom.Finite.tensorProductMap (f := AlgHom.id k L)
        (RingEquiv.refl L).finite hfin
    have : Algebra.FiniteType L (L ⊗[k] K) := by
      let := fL.hom.toAlgHom.toAlgebra
      have : IsScalarTower L (L ⊗[k] H) (L ⊗[k] K) :=
        .of_algebraMap_eq fun x ↦ (fL.hom.toAlgHom.commutes x).symm
      have : Module.Finite (L ⊗[k] H) (L ⊗[k] K) := hfinL
      exact .trans (S := L ⊗[k] H) inferInstance inferInstance
    exact (isIsogeny_baseChangeMap_iff (S := L) f).mp
      ((isIsogeny_iff fL).mpr ⟨hfinL, faithfullyFlat_of_dominant fL hdomL⟩)

end TauCeti.CommHopfAlgCat
