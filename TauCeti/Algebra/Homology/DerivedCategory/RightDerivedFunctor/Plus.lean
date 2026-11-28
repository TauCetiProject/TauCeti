/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import TauCeti.Algebra.Homology.HomologicalComplex.Acyclic

import TauCeti.Algebra.Homology.DerivedCategory.Plus.Basic
import TauCeti.Algebra.Homology.DerivedCategory.Plus.RightDerived

/-!
# Bounded below right derived functors from adapted complexes

Let `F : C ⥤ D` be an additive functor between abelian categories, where `C` has enough
injectives, and let `P` be a class of objects of `C` adapted to `F`:

* every injective object lies in `P`, and `P` is closed under isomorphisms;
* in a short exact sequence `0 ⟶ A ⟶ B ⟶ C ⟶ 0` with `A` and `B` in `P`, also `C` lies in `P`;
* `F` sends such a short exact sequence to a short exact sequence.

Mathlib's bounded below right derived functor
`F.rightDerivedFunctorPlus : DerivedCategory.Plus C ⥤ DerivedCategory.Plus D` comes with a natural
map `F.rightDerivedFunctorPlusUnit : F(K) ⟶ RF(K)` for bounded below complexes `K`, which is an
isomorphism when the terms of `K` are injective. This file shows that it is an isomorphism as soon
as the terms of `K` lie in `P` (`CategoryTheory.Functor.isIso_rightDerivedFunctorPlusUnit_app`):
a bounded below complex of `F`-acyclic objects computes the derived functor. For instance, flasque
sheaves form such a class for the global sections functor.

The proof embeds `K` by a monomorphism and quasi-isomorphism `K ⟶ L` into a bounded below complex
of injective objects (Mathlib's
`CochainComplex.Plus.modelCategoryQuillen.exists_mono_quasiIso_injective`), and applies
`CategoryTheory.Functor.quasiIso_map_of_mono_of_isStrictlyGE` (from
`TauCeti/Algebra/Homology/HomologicalComplex/Acyclic.lean`).

## Main results

* `CategoryTheory.Functor.isIso_rightDerivedFunctorPlusUnit_app`: for a bounded below complex `K`
  with terms in `P`, the map `F(K) ⟶ RF(K)` is an isomorphism in `D⁺(D)`.

## References

* The Stacks Project, Derived Categories, Lemma 13.15.6 (tag 05T8) and Lemma 13.16.7
  (tag 015E).
* M. Kashiwara, P. Schapira, *Categories and Sheaves*, Grundlehren 332, Springer, 2006,
  Definition 13.3.4 and Corollary 13.3.8, where such classes are called `F`-injective.
-/

public section

open CategoryTheory Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] {D : Type u₂} [Category.{v₂} D] [Abelian D]
  (F : C ⥤ D) [F.Additive] (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms]
  (hP : ∀ S : ShortComplex C, S.ShortExact → P S.X₁ → P S.X₂ → P S.X₃)
  (hF : ∀ S : ShortComplex C, S.ShortExact → P S.X₁ → P S.X₂ → (S.map F).ShortExact)

variable [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]

include hP hF in
/-- **Bounded below complexes in an adapted class compute the right derived functor.** Let `P` be
a class of objects containing the injective objects, closed under isomorphisms and under cokernels
of monomorphisms, on whose short exact sequences `F` is exact. For a bounded below complex `K`
with terms in `P`, the map `F(K) ⟶ RF(K)` in the bounded below derived category of `D` is an
isomorphism. -/
theorem isIso_rightDerivedFunctorPlusUnit_app (hinj : ∀ (Y : C), Injective Y → P Y)
    (K : CochainComplex.Plus C) (hK : ∀ n, P (K.obj.X n)) :
    IsIso (F.rightDerivedFunctorPlusUnit.app K) := by
  obtain ⟨b, _⟩ := K.property
  obtain ⟨L, i, _, hi, hL, hLb⟩ :=
    CochainComplex.Plus.modelCategoryQuillen.exists_mono_quasiIso_injective K.obj (b - 1) b
  -- view `L` in `CochainComplex.Plus C` and lift `i` to `K ⟶ L'`
  let L' : CochainComplex.Plus C := ⟨L, b - 1, hLb⟩
  let i' : K ⟶ L' := ObjectProperty.homMk i
  have : QuasiIso i'.hom := hi
  have : QuasiIso (F.mapCochainComplexPlus.map i').hom := by
    rw [Functor.mapCochainComplexPlus_map_hom]
    exact F.quasiIso_map_of_mono_of_isStrictlyGE P hP hF i (b - 1) hK fun n ↦ hinj _ (hL n)
  -- `i'` and `F(i')` are quasi-isomorphisms, and `F.rightDerivedFunctorPlusUnit.app L'` is an
  -- isomorphism because `L'` has injective terms
  have : IsIso (DerivedCategory.Plus.Q.map i') :=
    TauCeti.DerivedCategory.Plus.isIso_Q_map_of_quasiIso i'
  have : IsIso (DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map i')) :=
    TauCeti.DerivedCategory.Plus.isIso_Q_map_of_quasiIso (F.mapCochainComplexPlus.map i')
  have : ∀ n, Injective (L'.obj.X n) := hL
  have h := F.rightDerivedFunctorPlusUnit_naturality i'
  have : IsIso (F.rightDerivedFunctorPlusUnit.app K ≫
      F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map i')) := by
    rw [← h]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map i'))

end CategoryTheory.Functor
