/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.DerivedCategory.Basic
public import TauCeti.CategoryTheory.Exact.DerivedCategory.Injective
public import TauCeti.CategoryTheory.Exact.HomologicalComplex.Truncation
public import TauCeti.Algebra.Homology.HomotopyCategory.LowDegreeIso

/-!
# The bounded derived category inside the bounded below derived category

Let `E` be an exact structure. Bounded complexes are bounded below, and bounded acyclic complexes
are acyclic, so the inclusion `Kᵇ(C) ⥤ K⁺(C)` induces an additive functor
`Dᵇ(E) ⥤ D⁺(E)`. When `E` has enough injectives, this functor is fully faithful. No idempotent
completeness is needed (Keller, *Derived categories and their uses*, Lemma 11.7).

Let `X` and `Y` be bounded complexes, and let `r : Y ⟶ I` be an injective resolution: a map to a
bounded below complex of injectives with acyclic mapping cone. Morphisms into `I` are the same in
`K⁺(C)` and in `D⁺(E)`, since `I` is right orthogonal to the acyclic complexes. The resolution is
not bounded, but for `n` above `X` and `Y` it can be cut off at the cycles of its mapping cone,
`TauCeti.ExactStructure.exists_truncation_of_acyclic_mappingCone`: `r = r' ≫ j` with `r' : Y ⟶ T`
a map of bounded complexes with acyclic cone, and `j : T ⟶ I` an isomorphism in degrees `≤ n` and
a monomorphism in degree `n + 1`. Then maps and homotopies from `X` into `I` are the same as into
`T`, `CochainComplex.bijective_comp_quotient_map_of_isIso_of_mono`.

* **Fullness.** A morphism `α : X ⟶ Y` of `D⁺(E)` composed with `r` is the class of a map
  `f : X ⟶ I`, which factors through `T` as `g`. The fraction `r'⁻¹ ∘ g` of `Dᵇ(E)` maps to `α`.
* **Faithfulness.** A fraction `f ∘ s⁻¹` of `Dᵇ(E)`, with `f : X' ⟶ Y`, vanishing in `D⁺(E)` has
  `r ∘ f = 0` in `K⁺(C)`. With `n` above `X'` and `Y`, also `r' ∘ f = 0`, so `f = 0` in
  `Dᵇ(E)`.

## Main definitions

* `TauCeti.ExactStructure.BoundedDerivedCategory.toPlus`: the functor `Dᵇ(E) ⥤ D⁺(E)`, with
  `TauCeti.ExactStructure.BoundedDerivedCategory.QCompToPlusIso`.

## Main results

* `TauCeti.ExactStructure.EnoughInjectives.fullyFaithfulToPlus`: with enough injectives,
  `Dᵇ(E) ⥤ D⁺(E)` is fully faithful.

## References

* Bernhard Keller, *Derived categories and their uses*, Handbook of Algebra 1 (1996),
  Lemma 11.7.
* Bernhard Keller, *Chain complexes and stable categories*, Manuscripta Math. **67** (1990),
  379--417, Section 4.1.
-/

public section

namespace TauCeti.ExactStructure

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated ZeroObject

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
  (E : ExactStructure C)

/-- The inclusion `Kᵇ(C) ⥤ K⁺(C)` sends the morphisms inverted in `Dᵇ(E)` to morphisms inverted
in `D⁺(E)`. -/
theorem acyclicBounded_trW_le :
    E.acyclicBounded.trW ≤ E.acyclicPlus.trW.inverseImage (HomotopyCategory.Bounded.toPlus C) := by
  intro X Y f hf
  rw [MorphismProperty.inverseImage_iff, acyclicPlus_trW_iff]
  rw [acyclicBounded_trW_iff] at hf
  refine ObjectProperty.trW_monotone (fun X hX ↦ ?_) _ hf
  obtain ⟨K, _, ha, e⟩ := (E.boundedAcyclic_iff X).1 hX
  exact (E.homotopyAcyclic_iff X).2 ⟨K, ha, e⟩

namespace BoundedDerivedCategory

/-- The functor `Dᵇ(E) ⥤ D⁺(E)` induced by the inclusion of bounded complexes into bounded below
complexes. -/
noncomputable def toPlus : E.BoundedDerivedCategory ⥤ E.PlusDerivedCategory :=
  Localization.lift (HomotopyCategory.Bounded.toPlus C ⋙ PlusDerivedCategory.Q E)
    (fun _ _ f hf ↦ Localization.inverts (PlusDerivedCategory.Q E) E.acyclicPlus.trW _
      (E.acyclicBounded_trW_le f hf)) (Q E)

/-- The functor `Dᵇ(E) ⥤ D⁺(E)` is induced by the inclusion `Kᵇ(C) ⥤ K⁺(C)`. -/
noncomputable def QCompToPlusIso :
    Q E ⋙ toPlus E ≅ HomotopyCategory.Bounded.toPlus C ⋙ PlusDerivedCategory.Q E :=
  Localization.fac _ _ _

/-- The functor `Dᵇ(E) ⥤ D⁺(E)` on the image of a morphism of `Kᵇ(C)`. -/
theorem toPlus_map_Q {X Y : HomotopyCategory.Bounded C} (f : X ⟶ Y) :
    (toPlus E).map ((Q E).map f) = (QCompToPlusIso E).hom.app X ≫
      (PlusDerivedCategory.Q E).map ((HomotopyCategory.Bounded.toPlus C).map f) ≫
        (QCompToPlusIso E).inv.app Y :=
  (NatIso.naturality_2 (QCompToPlusIso E) f).symm

instance : (toPlus E).Additive :=
  (Localization.functor_additive_iff (Q E) E.acyclicBounded.trW (toPlus E)).2
    (Functor.additive_of_iso (QCompToPlusIso E).symm)

end BoundedDerivedCategory

open BoundedDerivedCategory

namespace EnoughInjectives

variable {E} (hE : E.EnoughInjectives)

/-- An injective resolution of a bounded complex, as a morphism of `K⁺(C)` into an object right
orthogonal to the acyclic complexes. -/
private structure BoundedResolution (Y : HomotopyCategory.Bounded C) where
  /-- The bounded below complex of injectives. -/
  I : CochainComplex C ℤ
  /-- A lower bound of `I`. -/
  a : ℤ
  isStrictlyGE : I.IsStrictlyGE a
  /-- The resolution map. -/
  r : Y.obj.as ⟶ I
  acyclic : E.acyclic (CochainComplex.mappingCone r)
  isInjective (k : ℤ) : E.isInjective (I.X k)

include hE in
private theorem nonempty_resolution (Y : HomotopyCategory.Bounded C) :
    Nonempty (BoundedResolution (E := E) Y) := by
  obtain ⟨a, b, _, _⟩ := HomotopyCategory.Bounded.exists_isStrictlyGE_isStrictlyLE Y
  obtain ⟨I, r, hIa, hI, hr⟩ := hE.exists_injectiveResolution Y.obj.as a
  exact ⟨⟨I, a, hIa, r, hr, hI⟩⟩

variable {Y : HomotopyCategory.Bounded C}

attribute [instance] BoundedResolution.isStrictlyGE

/-- The resolution as an object of `K⁺(C)`. -/
private abbrev resObj (R : BoundedResolution (E := E) Y) : _root_.HomotopyCategory.Plus C :=
  ⟨(_root_.HomotopyCategory.quotient C (.up ℤ)).obj R.I,
    (_root_.HomotopyCategory.plus_quotient_obj_iff R.I).2 ⟨R.a, inferInstance⟩⟩

/-- The resolution as a morphism of `K⁺(C)`. -/
private abbrev resHom (R : BoundedResolution (E := E) Y) :
    (HomotopyCategory.Bounded.toPlus C).obj Y ⟶ resObj R :=
  ObjectProperty.homMk ((_root_.HomotopyCategory.quotient C (.up ℤ)).map R.r)

private instance (R : BoundedResolution (E := E) Y) :
    IsIso ((PlusDerivedCategory.Q E).map (resHom R)) :=
  Localization.inverts _ E.acyclicPlus.trW _
    ((E.acyclicPlus_trW_iff _).2 (E.homotopyAcyclic_trW_quotient_map R.r R.acyclic))

/-- Morphisms into the resolution are the same in `K⁺(C)` and in `D⁺(E)`. -/
private theorem resolution_map_bijective (R : BoundedResolution (E := E) Y)
    (X : _root_.HomotopyCategory.Plus C) :
    Function.Bijective ((PlusDerivedCategory.Q E).map : (X ⟶ resObj R) → _) :=
  ObjectProperty.rightOrthogonal.map_bijective_of_isTriangulated
    (E.injectivePlus_le_rightOrthogonal _
      ((E.injectivePlus_iff _).2 ((E.plusInjective_iff _).2
        ⟨R.I, ⟨R.a, inferInstance⟩, R.isInjective, ⟨Iso.refl _⟩⟩))) _ X

/-- **The resolution truncated above `n`**: a map `rT : Y ⟶ B` of `Kᵇ(C)` inverted in `Dᵇ(E)` and
a map `jT : B ⟶ I` of `K⁺(C)` with `rT ≫ jT = r`, through which maps from complexes vanishing above
`n` into `I` factor uniquely. -/
private theorem exists_truncation (R : BoundedResolution (E := E) Y) (n : ℤ)
    [CochainComplex.IsStrictlyLE Y.obj.as n] :
    ∃ (B : HomotopyCategory.Bounded C) (rT : Y ⟶ B)
      (jT : (HomotopyCategory.Bounded.toPlus C).obj B ⟶ resObj R),
      E.acyclicBounded.trW rT ∧ (HomotopyCategory.Bounded.toPlus C).map rT ≫ jT = resHom R ∧
      ∀ X : HomotopyCategory.Bounded C, CochainComplex.IsStrictlyLE X.obj.as n →
        Function.Bijective fun g : X ⟶ B ↦ (HomotopyCategory.Bounded.toPlus C).map g ≫ jT := by
  obtain ⟨T, j, r', hrj, hiso, hmono, _, hge, hr'⟩ :=
    exists_truncation_of_acyclic_mappingCone R.r R.acyclic n
  have := hge R.a inferInstance
  let B := HomotopyCategory.Bounded.mk T
    ((CochainComplex.bounded_iff C T).2 ⟨min R.a (n + 1), n + 1, inferInstance, inferInstance⟩)
  refine ⟨B, ObjectProperty.homMk ((_root_.HomotopyCategory.quotient C (.up ℤ)).map r'),
    ObjectProperty.homMk ((_root_.HomotopyCategory.quotient C (.up ℤ)).map j),
    E.acyclicBounded_trW_homMk_quotient_map (X := Y) (Y := B) r' hr',
    ObjectProperty.hom_ext _
      (((_root_.HomotopyCategory.quotient C (.up ℤ)).map_comp r' j).symm.trans
        (congrArg (_root_.HomotopyCategory.quotient C (.up ℤ)).map hrj)),
    fun X _ ↦ ?_⟩
  -- On underlying morphisms of the homotopy category, the map is composition with `j`.
  have hb := CochainComplex.bijective_comp_quotient_map_of_isIso_of_mono (M := X.obj.as) j n
    hiso hmono
  refine ⟨fun g₁ g₂ h ↦ ObjectProperty.hom_ext _ (hb.1 (congrArg (·.hom) h)), fun f ↦ ?_⟩
  obtain ⟨g, hg⟩ := hb.2 f.hom
  exact ⟨ObjectProperty.homMk g, ObjectProperty.hom_ext _ hg⟩

include hE in
/-- **Faithfulness on objects of `Kᵇ(C)`**: a morphism of `Dᵇ(E)` vanishing in `D⁺(E)` is zero. -/
private theorem eq_zero_of_toPlus_map_eq_zero {X Y : HomotopyCategory.Bounded C}
    (β : (Q E).obj X ⟶ (Q E).obj Y) (hβ : (BoundedDerivedCategory.toPlus E).map β = 0) :
    β = 0 := by
  obtain ⟨φ, rfl⟩ := Localization.exists_rightFraction (Q E) E.acyclicBounded.trW β
  have := Localization.inverts (Q E) E.acyclicBounded.trW φ.s φ.hs
  suffices h : (Q E).map φ.f = 0 by
    rw [← cancel_epi ((Q E).map φ.s), φ.map_s_comp_map, h, comp_zero]
  have h₁ : (PlusDerivedCategory.Q E).map ((HomotopyCategory.Bounded.toPlus C).map φ.f) = 0 := by
    have h := (BoundedDerivedCategory.toPlus E).congr_map
      (φ.map_s_comp_map (Q E) (Localization.inverts _ _))
    rw [Functor.map_comp, hβ, comp_zero, BoundedDerivedCategory.toPlus_map_Q] at h
    simpa using h.symm
  -- `f` vanishes into the resolution, hence into its truncation, which `Dᵇ(E)` inverts.
  obtain ⟨R⟩ := nonempty_resolution hE Y
  have h₂ : (HomotopyCategory.Bounded.toPlus C).map φ.f ≫ resHom R = 0 :=
    (resolution_map_bijective R _).1 (by rw [Functor.map_comp, h₁, zero_comp, Functor.map_zero])
  obtain ⟨n, _, _⟩ := HomotopyCategory.Bounded.exists_isStrictlyLE_isStrictlyLE φ.X' Y
  obtain ⟨B, rT, jT, hrT, hρ, hbij⟩ := exists_truncation R n
  have := Localization.inverts (Q E) _ rT hrT
  have h₃ : φ.f ≫ rT = 0 :=
    (hbij φ.X' inferInstance).1 (by
      dsimp only
      rw [Functor.map_comp, Category.assoc, hρ, h₂, Functor.map_zero, zero_comp])
  rw [← cancel_mono ((Q E).map rT), zero_comp, ← Functor.map_comp, h₃, Functor.map_zero]

include hE in
/-- **Fullness on objects of `Kᵇ(C)`**: every morphism of `D⁺(E)` between bounded complexes comes
from `Dᵇ(E)`. -/
private theorem exists_toPlus_map_eq {X Y : HomotopyCategory.Bounded C}
    (α : (BoundedDerivedCategory.toPlus E).obj ((Q E).obj X) ⟶
      (BoundedDerivedCategory.toPlus E).obj ((Q E).obj Y)) :
    ∃ β, (BoundedDerivedCategory.toPlus E).map β = α := by
  let e := QCompToPlusIso E
  let α' := e.inv.app X ≫ α ≫ e.hom.app Y
  -- `α'` composed with the resolution of `Y` is the class of a map `fR` of `K⁺(C)`, which factors
  -- through the truncation of the resolution as `gT ≫ jT`.
  obtain ⟨R⟩ := nonempty_resolution hE Y
  obtain ⟨fR, hfR⟩ := (resolution_map_bijective R ((HomotopyCategory.Bounded.toPlus C).obj X)).2
    (α' ≫ (PlusDerivedCategory.Q E).map (resHom R))
  obtain ⟨n, _, _⟩ := HomotopyCategory.Bounded.exists_isStrictlyLE_isStrictlyLE X Y
  obtain ⟨B, rT, jT, hrT, hρ, hbij⟩ := exists_truncation R n
  obtain ⟨gT, hgT⟩ := (hbij X inferInstance).2 fR
  dsimp only at hgT
  have := Localization.inverts (Q E) _ rT hrT
  have : IsIso ((PlusDerivedCategory.Q E).map ((HomotopyCategory.Bounded.toPlus C).map rT)) :=
    Localization.inverts _ _ _ (E.acyclicBounded_trW_le rT hrT)
  have : IsIso ((PlusDerivedCategory.Q E).map jT) := by
    have : IsIso ((PlusDerivedCategory.Q E).map ((HomotopyCategory.Bounded.toPlus C).map rT) ≫
        (PlusDerivedCategory.Q E).map jT) := by
      rw [← Functor.map_comp, hρ]
      infer_instance
    exact IsIso.of_isIso_comp_left
      ((PlusDerivedCategory.Q E).map ((HomotopyCategory.Bounded.toPlus C).map rT)) _
  -- So `α'` is the class of the fraction `rT⁻¹ ∘ gT`.
  have key : (PlusDerivedCategory.Q E).map ((HomotopyCategory.Bounded.toPlus C).map gT) ≫
      inv ((PlusDerivedCategory.Q E).map ((HomotopyCategory.Bounded.toPlus C).map rT)) = α' := by
    rw [IsIso.comp_inv_eq, ← cancel_mono ((PlusDerivedCategory.Q E).map jT),
      ← Functor.map_comp, hgT, hfR, Category.assoc α', ← Functor.map_comp, hρ]
  refine ⟨(Q E).map gT ≫ inv ((Q E).map rT), ?_⟩
  rw [IsIso.comp_inv_eq] at key
  rw [Functor.map_comp, Functor.map_inv, IsIso.comp_inv_eq, BoundedDerivedCategory.toPlus_map_Q,
    BoundedDerivedCategory.toPlus_map_Q, key]
  simp [α', e]

include hE in
/-- **`Dᵇ(E) ⥤ D⁺(E)` is full** for an exact structure with enough injectives. -/
theorem full_toPlus : (BoundedDerivedCategory.toPlus E).Full where
  map_surjective {A B} α := by
    have := Localization.essSurj (Q E) E.acyclicBounded.trW
    let eA := (Q E).objObjPreimageIso A
    let eB := (Q E).objObjPreimageIso B
    obtain ⟨β, hβ⟩ := exists_toPlus_map_eq hE
      ((toPlus E).map eA.hom ≫ α ≫ (toPlus E).map eB.inv)
    refine ⟨eA.inv ≫ β ≫ eB.hom, ?_⟩
    simp [hβ, ← Functor.map_comp_assoc]

include hE in
/-- **`Dᵇ(E) ⥤ D⁺(E)` is faithful** for an exact structure with enough injectives. -/
theorem faithful_toPlus : (BoundedDerivedCategory.toPlus E).Faithful where
  map_injective {A B} β₁ β₂ h := by
    have := Localization.essSurj (Q E) E.acyclicBounded.trW
    let eA := (Q E).objObjPreimageIso A
    let eB := (Q E).objObjPreimageIso B
    have : eA.hom ≫ (β₁ - β₂) ≫ eB.inv = 0 :=
      eq_zero_of_toPlus_map_eq_zero hE _ (by simp [h])
    rw [Preadditive.sub_comp, Preadditive.comp_sub, sub_eq_zero, cancel_epi, cancel_mono] at this
    exact this

include hE in
/-- **`Dᵇ(E) ⥤ D⁺(E)` is fully faithful** for an exact structure with enough injectives, with no
idempotent completeness (Keller, *Derived categories and their uses*, Lemma 11.7). -/
noncomputable def fullyFaithfulToPlus : (BoundedDerivedCategory.toPlus E).FullyFaithful :=
  have := full_toPlus hE
  have := faithful_toPlus hE
  .ofFullyFaithful _

end EnoughInjectives

end TauCeti.ExactStructure
