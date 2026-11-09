/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.TensorProduct.Nontrivial

/-!
# Images of spectra under tensor-product base change

The image of `Spec (C ⊗[A] B) → Spec C` is the inverse image of the image of
`Spec B → Spec A`. Thus spectral images commute with arbitrary base change, including when
neither algebra is flat. The proof uses the residue-field criterion for a nonempty fibre and
the nontrivial tensor product of the two residue fields over their common base residue field.
-/

public section

open scoped TensorProduct
open Algebra.TensorProduct

namespace PrimeSpectrum

/-- Spectral images commute with tensor-product base change. -/
theorem range_comap_algebraMap_tensorProduct
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] :
    Set.range (comap (algebraMap C (C ⊗[A] B))) =
      (comap (algebraMap A C)) ⁻¹' Set.range (comap (algebraMap A B)) := by
  ext q
  constructor
  · rintro ⟨r, rfl⟩
    refine ⟨PrimeSpectrum.comap includeRight.toRingHom r, ?_⟩
    simp only [← PrimeSpectrum.comap_comp_apply]
    congr 1
    ext a
    simp
  · rintro ⟨p, hp⟩
    let P := q.asIdeal.comap (algebraMap A C)
    let α := Ideal.ResidueField.mapₐ P q.asIdeal (Algebra.ofId A C) rfl
    let β := Ideal.ResidueField.mapₐ P p.asIdeal (Algebra.ofId A B)
      (congrArg PrimeSpectrum.asIdeal hp).symm
    let := α.toRingHom.toAlgebra
    let := β.toRingHom.toAlgebra
    have : IsScalarTower A P.ResidueField q.asIdeal.ResidueField :=
      IsScalarTower.of_algebraMap_eq' α.comp_algebraMap.symm
    have : IsScalarTower A P.ResidueField p.asIdeal.ResidueField :=
      IsScalarTower.of_algebraMap_eq' β.comp_algebraMap.symm
    have : Nontrivial (q.asIdeal.ResidueField ⊗[P.ResidueField] p.asIdeal.ResidueField) :=
      nontrivial_of_algebraMap_injective_of_isDomain _ _ _
        (algebraMap P.ResidueField q.asIdeal.ResidueField).injective
        (algebraMap P.ResidueField p.asIdeal.ResidueField).injective
    let φ : q.asIdeal.ResidueField ⊗[A] B →ₐ[A]
        q.asIdeal.ResidueField ⊗[P.ResidueField] p.asIdeal.ResidueField :=
      lift ((includeLeft : q.asIdeal.ResidueField →ₐ[P.ResidueField] _).restrictScalars A)
        (((includeRight : p.asIdeal.ResidueField →ₐ[P.ResidueField] _).restrictScalars A).comp
          (IsScalarTower.toAlgHom A B p.asIdeal.ResidueField)) (fun _ _ ↦ Commute.all ..)
    have : Nontrivial (q.asIdeal.ResidueField ⊗[A] B) := φ.toRingHom.domain_nontrivial
    have : Nontrivial (q.asIdeal.ResidueField ⊗[C] (C ⊗[A] B)) :=
      (Algebra.TensorProduct.cancelBaseChange A C q.asIdeal.ResidueField
        q.asIdeal.ResidueField B).toRingEquiv.nontrivial
    exact (PrimeSpectrum.nontrivial_iff_mem_rangeComap q).mp inferInstance

end PrimeSpectrum
