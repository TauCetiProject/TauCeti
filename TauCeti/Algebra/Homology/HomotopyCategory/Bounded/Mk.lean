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
`Kᵇ(C)` (`TauCeti/Algebra/Homology/HomotopyCategory/Bounded/Basic.lean`), whose underlying object of
the homotopy category is the class of `K` itself. This file adds
`TauCeti.HomotopyCategory.Bounded.mkMap`, the class of a map of bounded complexes. With these,
statements about explicit complexes and chain maps are made in `Kᵇ(C)` without the comparison
isomorphisms of `TauCeti.HomotopyCategory.Bounded.quotient`. An object placed in degree `n` is
naturally isomorphic to the class of the complex concentrated in degree `n`, and the class of
`A` in degree `a` is the shift by `n` of the class of `A` in degree `n + a`.

## Main definitions

* `TauCeti.HomotopyCategory.Bounded.mkMap`: the class of a map of bounded complexes.
* `TauCeti.HomotopyCategory.Bounded.singleFunctorObjIsoMk`: an object placed in degree `n` is the
  class of the complex concentrated in degree `n`.
* `TauCeti.HomotopyCategory.Bounded.mkSingleIsoShift`: the class of `A` in degree `a` is the shift
  by `n` of the class of `A` in degree `n + a`.

## Main results

* `TauCeti.HomotopyCategory.Bounded.mkMap_id`, `mkMap_comp`, `mkMap_zero`, `mkMap_add`,
  `mkMap_neg` and `ι_map_mkMap`: `mkMap` is a functorial, additive lift of the quotient map.
-/

public section

open CategoryTheory CategoryTheory.Limits ZeroObject

universe v u

variable {C : Type u} [Category.{v} C]

namespace TauCeti.HomotopyCategory.Bounded

variable [Preadditive C]

/-- The class in `Kᵇ(C)` of a map of bounded cochain complexes. -/
abbrev mkMap {K L : CochainComplex C ℤ} {hK : CochainComplex.bounded C K}
    {hL : CochainComplex.bounded C L} (φ : K ⟶ L) : mk K hK ⟶ mk L hL :=
  ObjectProperty.homMk ((_root_.HomotopyCategory.quotient C (.up ℤ)).map φ)

section mkMap

variable {K L M : CochainComplex C ℤ} {hK : CochainComplex.bounded C K}
  {hL : CochainComplex.bounded C L} {hM : CochainComplex.bounded C M}

@[simp]
lemma ι_map_mkMap (φ : K ⟶ L) :
    (ι C).map (mkMap φ : mk K hK ⟶ mk L hL) = (_root_.HomotopyCategory.quotient C (.up ℤ)).map φ :=
  rfl

@[simp]
lemma mkMap_id : (mkMap (𝟙 K) : mk K hK ⟶ mk K hK) = 𝟙 _ :=
  (ι C).map_injective (by simp)

@[reassoc]
lemma mkMap_comp (φ : K ⟶ L) (ψ : L ⟶ M) :
    (mkMap (φ ≫ ψ) : mk K hK ⟶ mk M hM) = (mkMap φ : _ ⟶ mk L hL) ≫ mkMap ψ :=
  (ι C).map_injective (by simp)

@[simp]
lemma mkMap_zero : (mkMap (0 : K ⟶ L) : mk K hK ⟶ mk L hL) = 0 :=
  (ι C).map_injective (by simp)

@[simp]
lemma mkMap_add (φ ψ : K ⟶ L) :
    (mkMap (φ + ψ) : mk K hK ⟶ mk L hL) = mkMap φ + mkMap ψ :=
  (ι C).map_injective (by rw [Functor.map_add]; simp)

@[simp]
lemma mkMap_neg (φ : K ⟶ L) : (mkMap (-φ) : mk K hK ⟶ mk L hL) = -mkMap φ :=
  (ι C).map_injective (by rw [Functor.map_neg]; simp)

end mkMap

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

/-- The class of `A` in degree `a` is the shift by `n` of the class of `A` in degree `a'`, for
`n + a = a'`. -/
noncomputable def mkSingleIsoShift (n a a' : ℤ) (h : n + a = a') (A : C) :
    mk _ (CochainComplex.bounded_single a A) ≅ (mk _ (CochainComplex.bounded_single a' A))⟦n⟧ :=
  (fullyFaithfulι C).preimageIso
    ((_root_.HomotopyCategory.quotient C (.up ℤ)).mapIso
      (((CochainComplex.singleFunctors C).shiftIso n a a' h).app A).symm ≪≫
      ((_root_.HomotopyCategory.quotient C (.up ℤ)).commShiftIso n).app _ ≪≫
        ((ι C).commShiftIso n).symm.app (mk _ (CochainComplex.bounded_single a' A)))

lemma ι_map_mkSingleIsoShift_hom (n a a' : ℤ) (h : n + a = a') (A : C) :
    (ι C).map (mkSingleIsoShift n a a' h A).hom =
      (_root_.HomotopyCategory.quotient C (.up ℤ)).map
        (((CochainComplex.singleFunctors C).shiftIso n a a' h).app A).inv ≫
      ((_root_.HomotopyCategory.quotient C (.up ℤ)).commShiftIso n).hom.app _ ≫
      ((ι C).commShiftIso n).inv.app (mk _ (CochainComplex.bounded_single a' A)) :=
  (fullyFaithfulι C).map_preimage _

/-- The comparison `mkSingleIsoShift` is natural. -/
@[reassoc]
lemma mkMap_single_comp_mkSingleIsoShift_hom (n a a' : ℤ) (h : n + a = a') {A B : C}
    (f : A ⟶ B) :
    mkMap ((HomologicalComplex.single C (.up ℤ) a).map f) ≫ (mkSingleIsoShift n a a' h B).hom =
      (mkSingleIsoShift n a a' h A).hom ≫
        (mkMap ((HomologicalComplex.single C (.up ℤ) a').map f))⟦n⟧' := by
  apply (ι C).map_injective
  rw [Functor.map_comp, Functor.map_comp, ι_map_mkSingleIsoShift_hom,
    ι_map_mkSingleIsoShift_hom]
  simp only [Category.assoc]
  rw [← Functor.commShiftIso_inv_naturality]
  simp only [ι_map_mkMap]
  rw [← Functor.commShiftIso_hom_naturality_assoc, ← Functor.map_comp_assoc,
    ← Functor.map_comp_assoc]
  congr 2
  exact ((CochainComplex.singleFunctors C).shiftIso n a a' h).inv.naturality f

end TauCeti.HomotopyCategory.Bounded
