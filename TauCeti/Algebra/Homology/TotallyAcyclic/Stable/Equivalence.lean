/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.GorensteinProjective.CompleteResolution
public import TauCeti.Algebra.Homology.TotallyAcyclic.Stable.Cycles

/-!
# The stable category of Gorenstein-projective modules as a homotopy category

The stable cycle functor from the homotopy category of totally acyclic complexes of finitely
generated projective modules to the stable category of finitely generated Gorenstein-projective
modules is an equivalence, in every degree. It is faithful because a map of totally acyclic
complexes inducing a stably zero map on cycles is null-homotopic, and full because every map of
cycles lifts to a map of complexes; both are the comparison theorem for complete resolutions in the
Frobenius category of Gorenstein-projective modules. Other degrees reduce to degree zero by
shifting. The inverse sends a module to a chosen complete resolution.

No noetherian hypothesis is needed. The triangulated structure of this homotopy category and the
triangle equivalence are not treated here; for a general Frobenius exact category they are
`TauCeti.ExactStructure.IsFrobenius.stableToCompleteResolutionHomotopyCategory_isTriangulated`.

## Main definitions

* `TauCeti.TotallyAcyclicComplex.completeResolutionFunctor`: chosen complete resolutions, as a
  functor from the stable category of Gorenstein-projective modules to the homotopy category of
  totally acyclic complexes.
* `TauCeti.TotallyAcyclicComplex.stableCyclesEquivalence`: the equivalence, with functor the stable
  cycles in degree zero and inverse the complete-resolution functor.

## Main results

* `TauCeti.TotallyAcyclicComplex.ker_stableCycles_le_homotopyIdeal`: a map whose stable cycle map
  in some degree vanishes is null-homotopic.
* `TauCeti.TotallyAcyclicComplex.stableCyclesFunctor` is full, faithful and an equivalence in
  every degree.

## References

* Ragnar-Olaf Buchweitz, *Maximal Cohen–Macaulay Modules and Tate Cohomology*, Section 4.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe v u

namespace TauCeti

namespace TotallyAcyclicComplex

variable (A : Type u) [Ring A] [Small.{v} A]

/-- A map of totally acyclic complexes whose stable map on cycles in degree zero vanishes is
null-homotopic. -/
private theorem ker_stableCycles_zero_le_homotopyIdeal :
    (cyclesFunctor A 0 ⋙
      (GorensteinProjectiveModuleCat.exactStructure.{v} A).projectiveStableFunctor).kerIdeal ≤
      homotopyIdeal A := by
  intro P Q f hf
  have hE := GorensteinProjectiveModuleCat.exactStructure_isFrobenius (A := A)
  rw [Functor.mem_kerIdeal_hom, Functor.comp_map,
    ExactStructure.projectiveStableFunctor_map_eq_zero_iff,
    ← hE.projectiveInjective_eq_isProjective] at hf
  exact (mem_homotopyIdeal_iff A f).2
    ⟨CochainComplex.IsTotallyAcyclic.homotopyZero P.property Q.property f.hom hf⟩

/-- The shift of totally acyclic complexes. -/
abbrev shift (n : ℤ) : TotallyAcyclicComplex.{v} A ⥤ TotallyAcyclicComplex.{v} A :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ CategoryTheory.shiftFunctor _ n)
    (fun P ↦ P.property.shift n)

/-- The cycles in degree zero of the shift by `n` are the cycles in degree `n`. -/
def shiftCyclesIso (n : ℤ) : shift A n ⋙ cyclesFunctor A 0 ≅ cyclesFunctor A n :=
  NatIso.ofComponents (fun P ↦ ObjectProperty.isoMk _ (P.obj.shiftCyclesIso n 0 n (add_zero n)))
    (fun f ↦ ObjectProperty.hom_ext _
      (CochainComplex.shiftCyclesIso_hom_naturality _ f.hom n 0 n (add_zero n)))

/-- A map of totally acyclic complexes whose stable map on cycles in some degree vanishes is
null-homotopic. -/
theorem ker_stableCycles_le_homotopyIdeal (n : ℤ) :
    (cyclesFunctor A n ⋙
      (GorensteinProjectiveModuleCat.exactStructure.{v} A).projectiveStableFunctor).kerIdeal ≤
      homotopyIdeal A := by
  intro P Q f hf
  let S := (GorensteinProjectiveModuleCat.exactStructure.{v} A).projectiveStableFunctor
  have h0 : (shift A n).map f ∈ (homotopyIdeal A).hom _ _ := by
    apply ker_stableCycles_zero_le_homotopyIdeal
    rw [Functor.mem_kerIdeal_hom, Functor.comp_map] at hf ⊢
    rw [← cancel_mono (S.map ((shiftCyclesIso A n).hom.app Q)), ← S.map_comp,
      ← Functor.comp_map, (shiftCyclesIso A n).hom.naturality, S.map_comp, hf]
    simp
  obtain ⟨h⟩ := (mem_homotopyIdeal_iff A _).1 h0
  -- Shift the null-homotopy back by `-n`.
  let e := shiftFunctorCompIsoId (CochainComplex (ModuleCat.{v} A) ℤ) n (-n) (add_neg_cancel n)
  refine (mem_homotopyIdeal_iff A f).2 ⟨(Homotopy.ofEq ?_).trans
    ((((h.shift (-n)).compLeft (e.inv.app P.obj)).compRight (e.hom.app Q.obj)).trans
      (Homotopy.ofEq (by simp)))⟩
  have := e.inv.naturality f.hom
  simp only [Functor.id_map, Functor.comp_map] at this
  change f.hom = (e.inv.app P.obj ≫ f.hom⟦n⟧'⟦-n⟧') ≫ e.hom.app Q.obj
  rw [← this, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

/-- Stable cycles in any degree are faithful on chain-homotopy classes. -/
instance (n : ℤ) : (stableCyclesFunctor.{v} A n).Faithful :=
  (MorphismIdeal.faithful_lift_iff _ _ _).2 (ker_stableCycles_le_homotopyIdeal A n)

/-- Every stable map of cycles in degree `n` comes from a chain map: lift it on the shift by `n`,
where it becomes a map of cycles in degree zero, and shift back. -/
instance (n : ℤ) : (stableCyclesFunctor.{v} A n).Full where
  map_surjective {P Q} g := by
    obtain ⟨g₀, rfl⟩ :=
      (GorensteinProjectiveModuleCat.exactStructure.{v} A).projectiveStableFunctor.map_surjective g
    obtain ⟨g₁, rfl⟩ : ∃ g₁ : P.as.obj.cycles n ⟶ Q.as.obj.cycles n, ObjectProperty.homMk g₁ = g₀ :=
      ⟨g₀.hom, rfl⟩
    let eP := P.as.obj.shiftCyclesIso n 0 n (add_zero n)
    let eQ := Q.as.obj.shiftCyclesIso n 0 n (add_zero n)
    let ψ := CochainComplex.IsTotallyAcyclic.lift (P.as.property.shift n) (Q.as.property.shift n)
      (eP.hom ≫ g₁ ≫ eQ.inv)
    let φ := (CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{v} A) ℤ) n).preimage ψ
    refine ⟨(quotient A).map (ObjectProperty.homMk φ), ?_⟩
    rw [stableCyclesFunctor_map_quotient_map]
    congr 1
    ext : 1
    change HomologicalComplex.cyclesMap φ n = g₁
    rw [← cancel_epi eP.hom,
      ← CochainComplex.shiftCyclesIso_hom_naturality, Functor.map_preimage,
      CochainComplex.IsTotallyAcyclic.cyclesMap_lift]
    simp [eQ]

/-- Stable cycles in any degree are an equivalence; essential surjectivity is
`TauCeti.TotallyAcyclicComplex.cyclesFunctor_essSurj`. -/
instance (n : ℤ) : (stableCyclesFunctor.{v} A n).IsEquivalence where

/-! ### The complete-resolution functor -/

variable {A}

/-- A chosen complete resolution of a Gorenstein-projective module. -/
def completeResolution (M : GorensteinProjectiveModuleCat.{v} A) : TotallyAcyclicComplex.{v} A :=
  ⟨((isGorensteinProjective_iff _).1 M.property).choose,
    ((isGorensteinProjective_iff _).1 M.property).choose_spec.1⟩

/-- The cycles in degree zero of the chosen complete resolution of `M` are `M`. -/
def completeResolutionCyclesIso (M : GorensteinProjectiveModuleCat.{v} A) :
    (cyclesFunctor A 0).obj (completeResolution M) ≅ M :=
  ObjectProperty.isoMk _ ((isGorensteinProjective_iff _).1 M.property).choose_spec.2.some

/-- The map of chosen complete resolutions lifting a map of Gorenstein-projective modules. -/
def completeResolutionMap {M N : GorensteinProjectiveModuleCat.{v} A} (f : M ⟶ N) :
    completeResolution M ⟶ completeResolution N :=
  ObjectProperty.homMk (CochainComplex.IsTotallyAcyclic.lift (completeResolution M).property
    (completeResolution N).property
    ((completeResolutionCyclesIso M).hom ≫ f ≫ (completeResolutionCyclesIso N).inv).hom)

/-- The lifted map induces the given map on cycles in degree zero, up to the chosen
identifications. -/
@[simp]
theorem cyclesFunctor_map_completeResolutionMap {M N : GorensteinProjectiveModuleCat.{v} A}
    (f : M ⟶ N) : (cyclesFunctor A 0).map (completeResolutionMap f) =
      (completeResolutionCyclesIso M).hom ≫ f ≫ (completeResolutionCyclesIso N).inv := by
  ext : 1
  exact CochainComplex.IsTotallyAcyclic.cyclesMap_lift _ _ _

variable (A)

/-- Chosen complete resolutions, as a functor to the homotopy category of totally acyclic
complexes; functoriality holds up to homotopy by the comparison theorem. -/
@[expose, simps]
def completeResolutionFunctor₀ :
    GorensteinProjectiveModuleCat.{v} A ⥤ HomotopyCategory.{v} A where
  obj M := (quotient A).obj (completeResolution M)
  map f := (quotient A).map (completeResolutionMap f)
  map_id M := (stableCyclesFunctor A 0).map_injective (by simp; rfl)
  map_comp f g := (stableCyclesFunctor A 0).map_injective (by simp)

/-- Stable cycles of the complete resolution of a map recover its stable class. -/
theorem stableCyclesFunctor_map_completeResolutionFunctor₀_map
    {M N : GorensteinProjectiveModuleCat.{v} A} (f : M ⟶ N) :
    (stableCyclesFunctor A 0).map ((completeResolutionFunctor₀ A).map f) =
      (GorensteinProjectiveModuleCat.exactStructure.{v} A).projectiveStableFunctor.map
        ((completeResolutionCyclesIso M).hom ≫ f ≫ (completeResolutionCyclesIso N).inv) :=
  (stableCyclesFunctor_map_quotient_map A 0 (completeResolutionMap f)).trans
    (congrArg _ (cyclesFunctor_map_completeResolutionMap f))

instance : (completeResolutionFunctor₀.{v} A).Additive where
  map_add {_ _ f g} := (stableCyclesFunctor A 0).map_injective (by
    rw [(stableCyclesFunctor A 0).map_add, stableCyclesFunctor_map_completeResolutionFunctor₀_map,
      stableCyclesFunctor_map_completeResolutionFunctor₀_map,
      stableCyclesFunctor_map_completeResolutionFunctor₀_map]
    simp
    rfl)

/-- Maps factoring through a finitely generated projective module have null-homotopic complete
resolutions. -/
theorem projectiveStableIdeal_le_ker_completeResolutionFunctor₀ :
    (GorensteinProjectiveModuleCat.exactStructure.{v} A).projectiveStableIdeal ≤
      (completeResolutionFunctor₀ A).kerIdeal := by
  intro M N f hf
  rw [Functor.mem_kerIdeal_hom]
  apply (stableCyclesFunctor A 0).map_injective
  rw [← MorphismIdeal.quotientFunctor_map_eq_zero_iff] at hf
  rw [stableCyclesFunctor_map_completeResolutionFunctor₀_map, Functor.map_zero]
  simp [hf]
  rfl

/-- **The complete-resolution functor** from the stable category of Gorenstein-projective
modules to the homotopy category of totally acyclic complexes. -/
abbrev completeResolutionFunctor :
    (GorensteinProjectiveModuleCat.exactStructure.{v} A).ProjectiveStableCategory ⥤
      HomotopyCategory.{v} A :=
  MorphismIdeal.lift _ (completeResolutionFunctor₀ A)
    (projectiveStableIdeal_le_ker_completeResolutionFunctor₀ A)

/-- Stable cycles of the chosen complete resolutions recover the stable category. -/
def completeResolutionFunctorCompStableCyclesIso :
    completeResolutionFunctor A ⋙ stableCyclesFunctor A 0 ≅ 𝟭 _ :=
  CategoryTheory.Quotient.natIsoLift _ <| NatIso.ofComponents
    (fun M ↦ (GorensteinProjectiveModuleCat.exactStructure.{v} A).projectiveStableFunctor.mapIso
      (completeResolutionCyclesIso M))
    (fun {M N} f ↦ by
      simp only [Functor.comp_map, CategoryTheory.Quotient.lift_map_functor_map]
      rw [stableCyclesFunctor_map_completeResolutionFunctor₀_map]
      let S := (GorensteinProjectiveModuleCat.exactStructure.{v} A).projectiveStableFunctor
      change S.map ((completeResolutionCyclesIso M).hom ≫ f ≫
          (completeResolutionCyclesIso N).inv) ≫ S.map (completeResolutionCyclesIso N).hom =
        S.map (completeResolutionCyclesIso M).hom ≫ S.map f
      rw [← S.map_comp, ← S.map_comp]
      simp)

/-- **The stable category of finitely generated Gorenstein-projective modules is equivalent to
the homotopy category of totally acyclic complexes of finitely generated projective modules.**
The functor takes cycles in degree zero; the inverse takes chosen complete resolutions. -/
@[expose]
def stableCyclesEquivalence : HomotopyCategory.{v} A ≌
    (GorensteinProjectiveModuleCat.exactStructure.{v} A).ProjectiveStableCategory :=
  let e := (stableCyclesFunctor.{v} A 0).asEquivalence
  e.changeInverse (e.inverse.leftUnitor.symm ≪≫
    Functor.isoWhiskerRight (completeResolutionFunctorCompStableCyclesIso A).symm e.inverse ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ e.unitIso.symm ≪≫ Functor.rightUnitor _)

@[simp]
theorem stableCyclesEquivalence_functor :
    (stableCyclesEquivalence A).functor = stableCyclesFunctor A 0 := rfl

@[simp]
theorem stableCyclesEquivalence_inverse :
    (stableCyclesEquivalence A).inverse = completeResolutionFunctor A := rfl

end TotallyAcyclicComplex

end TauCeti
