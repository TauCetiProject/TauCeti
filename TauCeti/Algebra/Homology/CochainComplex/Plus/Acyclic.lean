/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.CochainComplex.Plus.InjectiveResolution
public import TauCeti.Algebra.Homology.HomologicalComplex.Acyclic

import Mathlib.Algebra.Homology.Factorizations.CM5a

/-!
# Adapted quasi-isomorphisms on bounded-below cochain complexes

Let `F : C ⥤ D` be an additive functor between abelian categories, where `C` has enough
injectives, and let `P : ObjectProperty C` be closed under isomorphisms, contain injective objects,
be closed under cokernels of monomorphisms, and have `F` exact on short exact sequences starting in
`P`. Then `F` preserves quasi-isomorphisms from bounded-below `P`-complexes into bounded-below
complexes of injectives (`CategoryTheory.Functor.quasiIso_map_of_adapted_to_injective`), and
consequently preserves quasi-isomorphisms between any two bounded-below `P`-complexes
(`CategoryTheory.Functor.quasiIso_map_of_adapted`).

## References

* `TauCeti/CategoryTheory/Abelian/AcyclicResolution.lean`, whose adapted quasi-isomorphism proof
  pattern is adapted here to `CochainComplex.Plus`.
* Mathlib's `Mathlib/Algebra/Homology/Factorizations/CM5b.lean`, whose bounded-below injective
  monomorphism factorization `CochainComplex.cm5b` is used in
  `quasiIso_map_of_adapted_to_injective`.
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
theorem quasiIso_map_of_adapted_to_injective
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
  let M := CochainComplex.mappingCone (𝟙 (CochainComplex.cm5b.I K.obj)) ⊞ L
  have hX₂ (n : ℤ) : P (M.X n) := by
    have : Injective ((HomologicalComplex.eval C (.up ℤ) n).obj
        (CochainComplex.mappingCone (𝟙 (CochainComplex.cm5b.I K.obj)))) := by
      dsimp
      infer_instance
    have : Injective ((HomologicalComplex.eval C (.up ℤ) n).obj L) := (I.obj.X n).property
    have : Injective (M.X n) := Injective.of_iso
      ((HomologicalComplex.eval C (.up ℤ) n).mapBiprod _ _).symm inferInstance
    exact hinj _ inferInstance
  have : M.IsStrictlyGE b := inferInstance
  have : QuasiIso ((F.mapHomologicalComplex _).map ψ) :=
    F.quasiIso_map_of_mono_of_isStrictlyGE P hP hF ψ b hK hX₂
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
  obtain ⟨M, j₀, _, hM, _⟩ :=
    CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective L.obj b
  let K' : CochainComplex.Plus C := ⟨M, b, inferInstance⟩
  let I := CochainComplex.Plus.liftInjective K' hM
  let e := CochainComplex.Plus.liftInjectiveIso K' hM
  let j : L ⟶ (InjectiveObject.ι C).mapCochainComplexPlus.obj I :=
    ObjectProperty.homMk (j₀ ≫ e.inv.hom)
  have : QuasiIso j.hom := by
    dsimp [j]
    infer_instance
  have : QuasiIso (f ≫ j).hom := inferInstanceAs (QuasiIso (f.hom ≫ j.hom))
  have : QuasiIso ((F.mapHomologicalComplex _).map j.hom) :=
    F.quasiIso_map_of_adapted_to_injective P hinj hP hF hL j
  have : QuasiIso ((F.mapHomologicalComplex _).map f.hom ≫
      (F.mapHomologicalComplex _).map j.hom) := by
    rw [← Functor.map_comp]
    exact F.quasiIso_map_of_adapted_to_injective P hinj hP hF hK (f ≫ j)
  exact quasiIso_of_comp_right ((F.mapHomologicalComplex _).map f.hom)
    ((F.mapHomologicalComplex _).map j.hom)

end CategoryTheory.Functor
