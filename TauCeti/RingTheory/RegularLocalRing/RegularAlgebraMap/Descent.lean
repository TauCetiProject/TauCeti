/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.RegularLocalRing.RegularAlgebraMap.Basic
import TauCeti.RingTheory.Flat.Tower
import TauCeti.RingTheory.RingHom.FaithfullyFlat

/-!
# Faithfully flat descent of regular ring maps

For a tower `A → B → C`, if `A → C` is regular and `B → C` is faithfully flat, then
`A → B` is regular. Flatness descends in the tower, and each fibre of `A → B` is
faithfully flat in the corresponding geometrically regular fibre of `A → C`.
No Noetherianity assumptions on the three rings are needed: Noetherianity of the
fibres descends along with their geometric regularity.

This allows regularity to be checked after a faithfully flat extension of the target,
for example after completing a local target ring.

## References

* The Stacks Project, Lemma 15.42.7, Tag 07NT.
-/

public section

namespace TauCeti.Excellence.RegularAlgebraMap

/-- In a tower `A → B → C`, regularity of `A → C` descends to `A → B` if `B → C` is
faithfully flat. -/
theorem of_faithfullyFlat (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    [RegularAlgebraMap A C] [Module.FaithfullyFlat B C] : RegularAlgebraMap A B where
  flat := Module.Flat.of_faithfullyFlat_of_flat A B C
  geometricallyRegular_fiber p _ := by
    have hf : (IsScalarTower.toAlgHom A B C).toRingHom.FaithfullyFlat :=
      RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance
    let f := Algebra.TensorProduct.lTensor (S := p.ResidueField) p.ResidueField
      (IsScalarTower.toAlgHom A B C)
    let : Algebra (p.Fiber B) (p.Fiber C) := f.toAlgebra
    have : IsScalarTower p.ResidueField (p.Fiber B) (p.Fiber C) := .of_algHom f
    have : Module.FaithfullyFlat (p.Fiber B) (p.Fiber C) :=
      hf.lTensor (S := p.ResidueField) p.ResidueField
    exact GeometricallyRegular.of_faithfullyFlat (C := p.Fiber C)

end TauCeti.Excellence.RegularAlgebraMap
