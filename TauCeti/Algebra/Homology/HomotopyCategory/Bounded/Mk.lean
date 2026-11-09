/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.HomotopyCategory.Bounded.Basic

/-!
# Classes of explicit bounded complexes in the bounded homotopy category

For a bounded cochain complex `K`, `TauCeti.HomotopyCategory.Bounded.mk K hK` is its class in
`Kᵇ(C)`, whose underlying object of the homotopy category is the class of `K` itself, and
`TauCeti.HomotopyCategory.Bounded.mkMap` is the class of a map of bounded complexes. With these,
statements about explicit complexes and chain maps are made in `Kᵇ(C)` without the comparison
isomorphisms of `TauCeti.HomotopyCategory.Bounded.quotient`. An object placed in degree `n` is
naturally isomorphic to the class of the complex concentrated in degree `n`.

## Main definitions

* `TauCeti.HomotopyCategory.Bounded.mk`: the class of a bounded complex.
* `TauCeti.HomotopyCategory.Bounded.mkMap`: the class of a map of bounded complexes.
* `TauCeti.HomotopyCategory.Bounded.singleFunctorObjIsoMk`: an object placed in degree `n` is the
  class of the complex concentrated in degree `n`.
-/

public section

open CategoryTheory CategoryTheory.Limits ZeroObject

universe v u

variable {C : Type u} [Category.{v} C]

namespace CochainComplex

/-- A complex concentrated in one degree is bounded. -/
lemma bounded_single [HasZeroMorphisms C] [HasZeroObject C] (n : ℤ) (A : C) :
    bounded C ((HomologicalComplex.single C (.up ℤ) n).obj A) :=
  (bounded_iff C _).2 ⟨n, n, inferInstance, inferInstance⟩

end CochainComplex

namespace TauCeti.HomotopyCategory.Bounded

variable [Preadditive C]

/-- The class in `Kᵇ(C)` of a bounded cochain complex. -/
abbrev mk (K : CochainComplex C ℤ) (hK : CochainComplex.bounded C K) :
    HomotopyCategory.Bounded C :=
  ⟨_, (HomotopyCategory.bounded_quotient_obj_iff K).2 hK⟩

/-- The class in `Kᵇ(C)` of a map of bounded cochain complexes. -/
abbrev mkMap {K L : CochainComplex C ℤ} {hK : CochainComplex.bounded C K}
    {hL : CochainComplex.bounded C L} (φ : K ⟶ L) : mk K hK ⟶ mk L hL :=
  ObjectProperty.homMk ((_root_.HomotopyCategory.quotient C (.up ℤ)).map φ)

variable [HasZeroObject C]

/-- An object placed in degree `n` of `Kᵇ(C)` is the class of the complex concentrated in
degree `n`. -/
noncomputable def singleFunctorObjIsoMk (n : ℤ) (A : C) :
    (singleFunctor C n).obj A ≅ mk _ (CochainComplex.bounded_single n A) :=
  (fullyFaithfulι C).preimageIso ((singleFunctorCompιIso C n).app A)

lemma ι_map_singleFunctorObjIsoMk_hom (n : ℤ) (A : C) :
    (ι C).map (singleFunctorObjIsoMk n A).hom = (singleFunctorCompιIso C n).hom.app A :=
  (fullyFaithfulι C).map_preimage _

/-- The comparison `singleFunctorObjIsoMk` is natural. -/
@[reassoc]
lemma singleFunctor_map_comp_singleFunctorObjIsoMk_hom (n : ℤ) {A B : C} (a : A ⟶ B) :
    (singleFunctor C n).map a ≫ (singleFunctorObjIsoMk n B).hom =
      (singleFunctorObjIsoMk n A).hom ≫
        mkMap ((HomologicalComplex.single C (.up ℤ) n).map a) := by
  apply (ι C).map_injective
  rw [Functor.map_comp, Functor.map_comp, ι_map_singleFunctorObjIsoMk_hom,
    ι_map_singleFunctorObjIsoMk_hom]
  exact (singleFunctorCompιIso C n).hom.naturality a

end TauCeti.HomotopyCategory.Bounded
