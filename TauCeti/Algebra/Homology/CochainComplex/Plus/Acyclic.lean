/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.CochainComplexPlus
public import Mathlib.CategoryTheory.Preadditive.Injective.InjectiveObject
public import TauCeti.Algebra.Homology.HomologicalComplex.Acyclic

import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import Mathlib.Algebra.Homology.Factorizations.CM5b
import TauCeti.Algebra.Homology.HomologySequenceLemmas

/-!
# Adapted quasi-isomorphisms on bounded-below cochain complexes

Let `F : C ⥤ D` be an additive functor between abelian categories, where `C` has enough
injectives, and let `P : ObjectProperty C` be closed under isomorphisms, contain injective objects,
be closed under cokernels of monomorphisms, and have `F` exact on short exact sequences starting in
`P`. Then `F` preserves quasi-isomorphisms from bounded-below `P`-complexes into bounded-below
complexes of injectives (`CategoryTheory.Functor.quasiIso_map_of_adapted_injective`), and
consequently preserves quasi-isomorphisms between any two bounded-below `P`-complexes
(`CategoryTheory.Functor.quasiIso_map_of_adapted`).

## References

* `TauCeti/CategoryTheory/Abelian/AcyclicResolution.lean`, whose adapted quasi-isomorphism proof
  pattern is adapted here to `CochainComplex.Plus`.
* Mathlib's `Mathlib/Algebra/Homology/Factorizations/CM5b.lean`, whose bounded-below injective
  monomorphism factorization `CochainComplex.cm5b` is used in `quasiIso_map_of_adapted_injective`.
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
/-- **Adapted bounded-below complexes preserve quasi-isomorphisms into injective complexes.**
For a quasi-isomorphism `i : K ⟶ ι(I)` from a bounded-below `P`-complex `K` to a bounded-below
complex `I` of injective objects, `F(i)` is a quasi-isomorphism. -/
theorem quasiIso_map_of_adapted_injective
    {K : CochainComplex.Plus C} (hK : ∀ n, P (K.obj.X n))
    {I : CochainComplex.Plus (InjectiveObject C)}
    (i : K ⟶ (InjectiveObject.ι C).mapCochainComplexPlus.obj I) [QuasiIso i.hom] :
    QuasiIso ((F.mapHomologicalComplex _).map i.hom) := by
  obtain ⟨b₁, _⟩ := K.property
  obtain ⟨b₂, _⟩ := I.property
  let b := min (b₁ - 1) b₂
  have : K.obj.IsStrictlyGE (b + 1) := K.obj.isStrictlyGE_of_ge (b + 1) b₁ (by omega)
  let L := ((InjectiveObject.ι C).mapCochainComplexPlus.obj I).obj
  have : I.obj.IsStrictlyGE b := I.obj.isStrictlyGE_of_ge b b₂ (min_le_right _ _)
  have : L.IsStrictlyGE b := by
    dsimp [L]
    infer_instance
  -- Factor `i.hom` via `cm5b` as a monomorphism `ψ` followed by the homotopy equivalence `p`.
  let ψ := CochainComplex.cm5b.i i.hom
  have : QuasiIso ψ := by
    have : QuasiIso (ψ ≫ CochainComplex.cm5b.p K.obj L) := by
      rw [CochainComplex.cm5b.fac]
      infer_instance
    exact quasiIso_of_comp_right ψ (CochainComplex.cm5b.p K.obj L)
  -- Apply `F` to the short exact cokernel sequence `0 ⟶ K ⟶ cone(𝟙 (I K)) ⊞ L ⟶ coker(ψ) ⟶ 0`.
  let S := ShortComplex.cokernelSequence ψ
  have hS : S.ShortExact := TauCeti.cokernelSequence_shortExact ψ
  have hSn := (HomologicalComplex.shortExact_iff_degreewise_shortExact S).1 hS
  have hX₂ (n : ℤ) : P (S.X₂.X n) := by
    have : Injective ((HomologicalComplex.eval C (.up ℤ) n).obj
        (CochainComplex.mappingCone (𝟙 (CochainComplex.cm5b.I K.obj)))) := by
      dsimp
      infer_instance
    have : Injective ((HomologicalComplex.eval C (.up ℤ) n).obj L) := (I.obj.X n).property
    have : Injective (S.X₂.X n) := Injective.of_iso
      ((HomologicalComplex.eval C (.up ℤ) n).mapBiprod _ _).symm inferInstance
    exact hinj _ inferInstance
  have hQge : S.X₃.IsStrictlyGE b := by
    have : S.X₂.IsStrictlyGE b :=
      inferInstanceAs
        ((CochainComplex.mappingCone (𝟙 (CochainComplex.cm5b.I K.obj)) ⊞ L).IsStrictlyGE b)
    rw [CochainComplex.isStrictlyGE_iff]
    intro n hn
    have := (hSn n).epi_g
    exact IsZero.of_epi (S.g.f n) (S.X₂.isZero_of_isStrictlyGE b n hn)
  have hFS : (S.map (F.mapHomologicalComplex _)).ShortExact :=
    HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n ↦
      hF _ (hSn n) (hK n) (hX₂ n)
  have : QuasiIso S.f := by
    dsimp [S, ShortComplex.cokernelSequence]
    infer_instance
  have : QuasiIso ((F.mapHomologicalComplex _).map ψ) :=
    hFS.quasiIso_f_iff.2 (HomologicalComplex.Acyclic.map_of_shortExact_of_isStrictlyGE F P hP hF
      b (hS.quasiIso_f_iff.1 inferInstance) fun n ↦ hP _ (hSn n) (hK n) (hX₂ n))
  have : QuasiIso ((F.mapHomologicalComplex _).map (CochainComplex.cm5b.p K.obj L)) :=
    (F.mapHomotopyEquiv (CochainComplex.cm5b.homotopyEquiv K.obj L)).quasiIso_hom
  rw [← CochainComplex.cm5b.fac i.hom, Functor.map_comp]
  infer_instance

include hinj hP hF in
/-- A quasi-isomorphism between bounded-below complexes in an adapted class remains a
quasi-isomorphism after applying `F`. -/
theorem quasiIso_map_of_adapted
    {K L : CochainComplex.Plus C} (f : K ⟶ L) [QuasiIso f.hom]
    (hK : ∀ n, P (K.obj.X n)) (hL : ∀ n, P (L.obj.X n)) :
    QuasiIso ((F.mapHomologicalComplex _).map f.hom) := by
  obtain ⟨b, _⟩ := L.property
  obtain ⟨I, _, j, hj⟩ := CochainComplex.Plus.exists_quasiIso_injective L b
  have : QuasiIso j.hom := (CochainComplex.Plus.quasiIso_iff C j).1 hj
  have : QuasiIso (f ≫ j).hom := inferInstanceAs (QuasiIso (f.hom ≫ j.hom))
  have : QuasiIso ((F.mapHomologicalComplex _).map j.hom) :=
    F.quasiIso_map_of_adapted_injective P hinj hP hF hL j
  have : QuasiIso ((F.mapHomologicalComplex _).map f.hom ≫
      (F.mapHomologicalComplex _).map j.hom) := by
    rw [← Functor.map_comp]
    exact F.quasiIso_map_of_adapted_injective P hinj hP hF hK (f ≫ j)
  exact quasiIso_of_comp_right ((F.mapHomologicalComplex _).map f.hom)
    ((F.mapHomologicalComplex _).map j.hom)

end CategoryTheory.Functor
