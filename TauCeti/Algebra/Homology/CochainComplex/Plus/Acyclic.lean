/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.CochainComplex.Plus.InjectiveResolution
public import TauCeti.Algebra.Homology.HomologicalComplex.Acyclic

import TauCeti.Algebra.Homology.DerivedCategory.Plus.Basic
import TauCeti.Algebra.Homology.DerivedCategory.RightDerivedFunctor.Plus

/-!
# Adapted quasi-isomorphisms on bounded-below cochain complexes

Let `F : C ⥤ D` be an additive functor between abelian categories, where `C` has enough
injectives, and let `P : ObjectProperty C` be closed under isomorphisms, contain injective objects,
be closed under cokernels of monomorphisms, and have `F` exact on short exact sequences starting in
`P`. Then `F` preserves quasi-isomorphisms between any two bounded-below `P`-complexes
(`CategoryTheory.Functor.quasiIso_map_of_adapted`), and consequently preserves quasi-isomorphisms
from bounded-below `P`-complexes into bounded-below complexes of injectives
(`CategoryTheory.Functor.quasiIso_map_of_adapted_to_injective`).

## References

* `TauCeti/Algebra/Homology/DerivedCategory/RightDerivedFunctor/Plus.lean`, which proves
  `CategoryTheory.Functor.isIso_rightDerivedFunctorPlusUnit_app`, from which
  `quasiIso_map_of_adapted` follows via unit naturality and localization reflection.
* `TauCeti/CategoryTheory/Abelian/AcyclicResolution.lean`, whose adapted quasi-isomorphism API is
  adapted here to `CochainComplex.Plus`.
* The Stacks Project, Derived Categories, §13.15–§13.16 (tags 05T8, 015E).
* M. Kashiwara, P. Schapira, *Categories and Sheaves*, Grundlehren 332, Springer, 2006, §13.3.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor HomologicalComplex

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [EnoughInjectives C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]
  (F : C ⥤ D) [F.Additive]
  (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms]
  (hinj : ∀ (Y : C), Injective Y → P Y)
  (hP : ∀ S : ShortComplex C, S.ShortExact → P S.X₁ → P S.X₂ → P S.X₃)
  (hF : ∀ S : ShortComplex C, S.ShortExact → P S.X₁ → P S.X₂ → (S.map F).ShortExact)

include hinj hP hF in
/-- A quasi-isomorphism between bounded-below complexes in an adapted class remains a
quasi-isomorphism after applying `F`. -/
theorem quasiIso_map_of_adapted
    {K L : CochainComplex.Plus C} (f : K ⟶ L) [QuasiIso f.hom]
    (hK : ∀ n, P (K.obj.X n)) (hL : ∀ n, P (L.obj.X n)) :
    QuasiIso ((F.mapHomologicalComplex _).map f.hom) := by
  let := HasDerivedCategory.standard C
  let := HasDerivedCategory.standard D
  have : IsIso (F.rightDerivedFunctorPlusUnit.app K) :=
    F.isIso_rightDerivedFunctorPlusUnit_app P hP hF hinj K hK
  have : IsIso (F.rightDerivedFunctorPlusUnit.app L) :=
    F.isIso_rightDerivedFunctorPlusUnit_app P hP hF hinj L hL
  have : IsIso (DerivedCategory.Plus.Q.map f) :=
    TauCeti.DerivedCategory.Plus.isIso_Q_map_of_quasiIso f
  have h := F.rightDerivedFunctorPlusUnit.naturality f
  dsimp only [Functor.comp_map] at h
  have : IsIso (DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map f) ≫
      F.rightDerivedFunctorPlusUnit.app L) := by
    rw [h]
    infer_instance
  have : IsIso (DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map f)) :=
    IsIso.of_isIso_comp_right _ (F.rightDerivedFunctorPlusUnit.app L)
  exact (TauCeti.DerivedCategory.Plus.isIso_Q_map_iff_quasiIso
    (F.mapCochainComplexPlus.map f)).1 this

include hinj hP hF in
/-- **Adapted bounded-below complexes preserve quasi-isomorphisms into injective complexes.**
For a quasi-isomorphism `i : K ⟶ ι(I)` from a bounded-below `P`-complex `K` to a bounded-below
complex `I` of injective objects, `F(i)` is a quasi-isomorphism. -/
theorem quasiIso_map_of_adapted_to_injective
    {K : CochainComplex.Plus C} (hK : ∀ n, P (K.obj.X n))
    {I : CochainComplex.Plus (InjectiveObject C)}
    (i : K ⟶ (InjectiveObject.ι C).mapCochainComplexPlus.obj I) [QuasiIso i.hom] :
    QuasiIso ((F.mapHomologicalComplex _).map i.hom) :=
  F.quasiIso_map_of_adapted P hinj hP hF i hK fun n ↦ hinj _ (I.obj.X n).property

end CategoryTheory.Functor
