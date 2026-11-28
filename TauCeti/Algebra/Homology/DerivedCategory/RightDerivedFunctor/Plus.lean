/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import TauCeti.Algebra.Homology.HomologicalComplex.Acyclic
public import TauCeti.Algebra.Homology.HomologySequenceLemmas

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
`CochainComplex.Plus.modelCategoryQuillen.exists_mono_quasiIso_injective`). The cokernel of
`K ⟶ L` is then an acyclic bounded below complex with terms in `P`, which `F` sends to an acyclic
complex (`HomologicalComplex.Acyclic.map_of_shortExact_of_isStrictlyGE`), so that `F(K) ⟶ F(L)`
is a quasi-isomorphism (`CategoryTheory.Functor.quasiIso_map_of_mono_of_isStrictlyGE`).

## Main results

* `CategoryTheory.Functor.quasiIso_map_of_mono_of_isStrictlyGE`: `F` sends a monomorphism and
  quasi-isomorphism into a bounded below complex, between complexes with terms in `P`, to a
  quasi-isomorphism.
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

include hP hF in
/-- Let `P` be a class of objects closed under isomorphisms and under cokernels of
monomorphisms, on whose short exact sequences `F` is exact. Then `F` sends a monomorphism and
quasi-isomorphism `K ⟶ L` between complexes with terms in `P`, where `L` vanishes below some degree
`b`, to a quasi-isomorphism. -/
theorem quasiIso_map_of_mono_of_isStrictlyGE {K L : CochainComplex C ℤ} (f : K ⟶ L) [Mono f]
    [QuasiIso f] (b : ℤ) [L.IsStrictlyGE b] (hK : ∀ n, P (K.X n))
    (hL : ∀ n, P (L.X n)) : QuasiIso ((F.mapHomologicalComplex _).map f) := by
  let S := ShortComplex.cokernelSequence f
  have hS : S.ShortExact := TauCeti.cokernelSequence_shortExact f
  have hSn := (HomologicalComplex.shortExact_iff_degreewise_shortExact S).1 hS
  -- the cokernel of `f` is acyclic, vanishes below degree `b` and has terms in `P`
  have : S.X₃.IsStrictlyGE b := (CochainComplex.isStrictlyGE_iff _ b).2 fun i hi ↦
    have : Epi (S.g.f i) := (hSn i).epi_g
    (L.isZero_of_isStrictlyGE b i hi).of_epi (S.g.f i)
  have hFS : (S.map (F.mapHomologicalComplex _)).ShortExact :=
    HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n ↦ hF _ (hSn n) (hK n) (hL n)
  exact hFS.quasiIso_f_iff.2 (HomologicalComplex.Acyclic.map_of_shortExact_of_isStrictlyGE F P hP hF
    b (hS.quasiIso_f_iff.1 (inferInstanceAs (QuasiIso f))) fun n ↦ hP _ (hSn n) (hK n) (hL n))

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
  -- `L`, viewed as a bounded below complex of injective objects: mapping its lift back along
  -- `InjectiveObject.ι C` gives `L` by definition, so `hLb` is the required bound
  let L' : CochainComplex.Plus (InjectiveObject C) :=
    ⟨HomologicalComplex.liftObjectProperty _ L hL, b - 1,
      (CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff _ (InjectiveObject.ι C) _).1 hLb⟩
  let i' : K ⟶ (InjectiveObject.ι C).mapCochainComplexPlus.obj L' := ObjectProperty.homMk i
  -- `i` and `F(i)` are quasi-isomorphisms; by definition `i'.hom` is `i` and
  -- `(F.mapCochainComplexPlus.map i').hom` is `(F.mapHomologicalComplex _).map i`
  have : IsIso (DerivedCategory.Plus.Q.map i') :=
    Localization.inverts _ (CochainComplex.Plus.quasiIso C) i'
      ((CochainComplex.Plus.quasiIso_iff C i').2 hi)
  have : IsIso (DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map i')) :=
    Localization.inverts _ (CochainComplex.Plus.quasiIso D) _
      ((CochainComplex.Plus.quasiIso_iff D _).2
        (F.quasiIso_map_of_mono_of_isStrictlyGE P hP hF i (b - 1) hK fun n ↦ hinj _ (hL n)))
  -- the map `F(L) ⟶ RF(L)` is an isomorphism, as `L` has injective terms
  have h := F.rightDerivedFunctorPlusUnit.naturality i'
  dsimp only [Functor.comp_map] at h
  have : IsIso (F.rightDerivedFunctorPlusUnit.app K ≫
      F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map i')) := by
    rw [← h]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map i'))

end CategoryTheory.Functor
