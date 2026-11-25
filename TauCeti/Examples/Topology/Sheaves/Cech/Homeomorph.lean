/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import TauCeti.Topology.Sheaves.Cech.Homeomorph
public import TauCeti.Topology.Sheaves.Cech.Skyscraper
public import TauCeti.Topology.Sheaves.Cech.LongExactSequence
public import TauCeti.Geometry.Manifold.Instances.OnePoint.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Sheaves.Points
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Universe

/-!
# Native Čech transport of nonzero sections

A skyscraper section on the sphere retains its value under a change of base universe.
Repeated covers distinguish tuple readings, while an empty base and a disconnected base
exercise the native zero and support laws.
-/

public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace TauCeti.Topology Homeomorph

universe u v

namespace TauCeti.Examples.CechHomeomorph

attribute [local instance] Classical.propDecidable

attribute [local instance] ModuleCat.hasLimitsOfSize TauCeti.hasSheafify_moduleCat

/-- Complex coefficients in a universe independent of the original sphere. -/
abbrev coefficient : ModuleCat.{v + 1} ℂ :=
  ModuleCat.of ℂ (ULift.{v + 1} ℂ)

/-- The native site-point skyscraper, without a relation between base and coefficient universes. -/
def pointSheaf :
    Sheaf (Opens.grothendieckTopology (TopCat.of (OnePoint ℂ))) (ModuleCat.{v + 1} ℂ) :=
  (Opens.pointGrothendieckTopology (OnePoint.infty : OnePoint ℂ)).skyscraperSheaf coefficient.{v}

/-- The original sphere and its copy in an arbitrary successor universe. -/
def liftHomeomorph : OnePoint ℂ ≃ₜ ULift.{u + 1} (OnePoint ℂ) := Homeomorph.ulift.symm

/-- Reading the native skyscraper product at its point over the whole space. -/
def pointRead : pointSheaf.{v}.obj.obj (op ⊤) ⟶ coefficient.{v} :=
  Pi.π (fun _ : ULift.{0} (PLift ((OnePoint.infty : OnePoint ℂ) ∈ (⊤ : Opens (OnePoint ℂ)))) ↦
    coefficient.{v}) ⟨⟨trivial⟩⟩

/-- The global section whose every point-fibre coordinate is one. -/
def oneSection : pointSheaf.{v}.obj.obj (op ⊤) :=
  (Pi.lift (fun _ ↦ 𝟙 coefficient.{v})).hom (ULift.up 1)

/-- The native section has its prescribed point-fibre reading. -/
theorem oneSection_read : pointRead.{v} oneSection.{v} = ULift.up 1 := by
  exact congrArg (fun f : coefficient.{v} ⟶ coefficient.{v} ↦ f (ULift.up 1))
    (Pi.lift_comp_π
      (fun _ : ULift.{0} (PLift ((OnePoint.infty : OnePoint ℂ) ∈
        (⊤ : Opens (OnePoint ℂ)))) ↦ 𝟙 coefficient.{v}) ⟨⟨trivial⟩⟩)

/-- The actual skyscraper section is nonzero. -/
theorem oneSection_ne_zero : oneSection.{v} ≠ 0 := by
  intro h
  have he := congrArg (fun s ↦ pointRead.{v} s) h
  rw [oneSection_read, map_zero] at he
  exact one_ne_zero (congrArg ULift.down he)

/-- The native degree-zero class of this section. -/
def oneClass := (Topology.cechCohomologyZeroIso pointSheaf.{v}).hom oneSection.{v}

/-- The native class detects the nonzero section. -/
theorem oneClass_ne_zero : oneClass.{v} ≠ 0 := by
  intro h
  apply oneSection_ne_zero.{v}
  apply (Topology.cechCohomologyZeroIso pointSheaf.{v}).toLinearEquiv.injective
  simpa [oneClass] using h

/-- Transport the original sheaf to the actual lifted sphere. -/
abbrev liftedSheaf :
    Sheaf (Opens.grothendieckTopology (TopCat.of (ULift.{u + 1} (OnePoint ℂ))))
      (ModuleCat.{max (u + 1) (v + 1)} ℂ) :=
  (liftHomeomorph.{u}.opensCongr.equivalence.sheafCongr
    (Opens.grothendieckTopology (OnePoint ℂ))
    (Opens.grothendieckTopology (ULift.{u + 1} (OnePoint ℂ)))
    (ModuleCat.{max (u + 1) (v + 1)} ℂ)).functor.obj
    pointSheaf.{max u v}

/-- The actual top-open section comparison of the native transported sheaf. -/
def sectionIso : pointSheaf.{max u v}.obj.obj (op ⊤) ≅ liftedSheaf.{u,v}.obj.obj (op ⊤) :=
  pointSheaf.{max u v}.obj.mapIso (eqToIso liftHomeomorph.{u}.opensCongr.symm.map_top).op

/-- The native section on the lifted sphere. -/
def liftedSection := sectionIso.{u,v}.hom oneSection.{max u v}

/-- The transported section still reads one in the original coefficient object. -/
theorem liftedSection_read :
    pointRead.{max u v} (sectionIso.{u,v}.inv liftedSection.{u,v}) = ULift.up 1 := by
  rw [liftedSection, Iso.hom_inv_id_apply]
  exact oneSection_read

/-- Native transport of the actual class, with the actual sheaf comparison. -/
def liftedClass :=
  ((liftHomeomorph.{u}).cechCohomologyIso
    (X := TopCat.of (OnePoint ℂ)) (Y := TopCat.of (ULift.{u + 1} (OnePoint ℂ)))
    (A := ModuleCat.{max (u + 1) (v + 1)} ℂ)
    0).hom.app pointSheaf.{max u v}.obj oneClass.{max u v}

/-- The actual degree-zero class of the section on the lifted sphere. -/
def liftedSectionClass :=
  (Topology.cechCohomologyZeroIso
    (A := ModuleCat.{max (u + 1) (v + 1)} ℂ) liftedSheaf.{u,v}).hom liftedSection.{u,v}

/-- Transport sends the native class to the class of the actual transported section. -/
theorem liftedClass_eq : liftedClass.{u,v} = liftedSectionClass.{u,v} := by
  have h := Homeomorph.cechCohomologyZeroIso_hom_comp_cechCohomologyIso_hom_app
    (X := TopCat.of (OnePoint ℂ)) (Y := TopCat.of (ULift.{u + 1} (OnePoint ℂ)))
    liftHomeomorph.{u} pointSheaf.{max u v}
  exact congrArg (fun f ↦ f.hom oneSection.{max u v}) h

/-- The actual transported cohomology class remains nonzero. -/
theorem liftedClass_ne_zero : liftedClass.{u,v} ≠ 0 := by
  rw [liftedClass_eq]
  intro h
  have hs := (Topology.cechCohomologyZeroIso
    (A := ModuleCat.{max (u + 1) (v + 1)} ℂ) liftedSheaf.{u,v}).toLinearEquiv.injective
      (h.trans (map_zero _).symm)
  have ht := sectionIso.{u,v}.toLinearEquiv.injective (hs.trans (map_zero _).symm)
  exact oneSection_ne_zero.{max u v} ht

/-- The original section as an element of native global sections. -/
def globalOne :=
  (Sheaf.ΓNatIsoSheafSections _ _ isTerminalTop).inv.app pointSheaf.{v} oneSection.{v}

/-- The class obtained by transporting native global sections and then applying Γ⁰. -/
def gammaTransportClass :=
  (sectionsIsoCechZero liftedSheaf.{u,v}).hom
    ((liftHomeomorph.{u}.globalSectionsIso (ModuleCat.{max (u + 1) (v + 1)} ℂ)).hom.app
      pointSheaf.{max u v} globalOne.{max u v})

/-- Transport through native global sections gives the same actual nonzero Čech class. -/
theorem gammaTransportClass_eq : gammaTransportClass.{u,v} = liftedClass.{u,v} := by
  let F := pointSheaf.{max u v}
  let γ := (Sheaf.ΓNatIsoSheafSections _ _ isTerminalTop).app F
  let c := Topology.cechCohomologyZeroIso F
  let d := (cechCohomologyIso
    (X := TopCat.of (OnePoint ℂ)) (Y := TopCat.of (ULift.{u + 1} (OnePoint ℂ)))
    (A := ModuleCat.{max (u + 1) (v + 1)} ℂ) liftHomeomorph.{u} 0).hom.app F.obj
  let g := (liftHomeomorph.{u}.globalSectionsIso
    (ModuleCat.{max (u + 1) (v + 1)} ℂ)).hom.app F
  have h : (sectionsIsoCechZero F).hom ≫ d =
      g ≫ (sectionsIsoCechZero liftedSheaf.{u,v}).hom :=
    sectionsIsoCechZero_hom_comp_cechCohomologyIso_hom_app
      (X := TopCat.of (OnePoint ℂ)) (Y := TopCat.of (ULift.{u + 1} (OnePoint ℂ)))
      liftHomeomorph.{u} F
  have hread : (sectionsIsoCechZero F).hom (γ.inv oneSection.{max u v}) =
      c.hom oneSection.{max u v} :=
    (ConcreteCategory.congr_hom (sectionsIsoCechZero_hom F)
      (γ.inv oneSection.{max u v})).trans
      ((ConcreteCategory.comp_apply γ.hom c.hom _).trans
        (congrArg c.hom (γ.inv_hom_id_apply oneSection.{max u v})))
  have happly := (ConcreteCategory.congr_hom h (γ.inv oneSection.{max u v})).symm
  simp only [ConcreteCategory.comp_apply] at happly
  exact happly.trans (congrArg d.hom hread)

/-- A genuinely cross-universe permutation of a repeated two-set cover. -/
def indexEquiv : Fin 2 ≃ ULift.{u + 1} (Fin 2) :=
  (Equiv.swap 0 1).trans Equiv.ulift.symm

/-- The constant presheaf used to distinguish the two degree-zero tuple coordinates. -/
abbrev tuplePresheaf : (Opens (OnePoint ℂ))ᵒᵖ ⥤ ModuleCat.{v + 1} ℂ :=
  (Functor.const _).obj coefficient.{v}

/-- A native degree-zero cochain with distinct zero and one tuple readings. -/
def tupleCochain :
    ((CategoryTheory.cechComplexFunctor (A := ModuleCat.{v + 1} ℂ)
      (fun _ : Fin 2 ↦ (⊤ : Opens (OnePoint ℂ)))).obj tuplePresheaf.{v}).X 0 :=
  (Pi.lift (fun a : Fin 1 → Fin 2 ↦ if a 0 = 0 then 0 else 𝟙 coefficient.{v})).hom
    (ULift.up 1)

/-- The zero tuple really reads zero in the native product of coefficient objects. -/
theorem tupleCochain_zero :
    (Pi.π (fun _ : Fin 1 → Fin 2 ↦ coefficient.{v}) (fun _ ↦ 0)) tupleCochain.{v} = 0 := by
  simp [tupleCochain]

/-- The other tuple really reads one, so the example detects index exchange. -/
theorem tupleCochain_one :
    (Pi.π (fun _ : Fin 1 → Fin 2 ↦ coefficient.{v}) (fun _ ↦ 1)) tupleCochain.{v} =
      ULift.up 1 := by
  simp [tupleCochain]

/-- Apply the actual complex reindexing map to the cochain on the repeated cover. -/
def reindexedCochain :=
  ((Equiv.cechComplexReindexIso indexEquiv.{u}
    (fun _ : ULift.{u + 1} (Fin 2) ↦ (⊤ : Opens (OnePoint ℂ)))).hom.app
      tuplePresheaf.{max u v}).f 0 tupleCochain.{max u v}

/-- The actual cross-universe map sends the one tuple to its prescribed transformed index. -/
theorem reindexedCochain_one :
    (Pi.π (fun _ : Fin 1 → ULift.{u + 1} (Fin 2) ↦ coefficient.{max u v})
      (indexEquiv.{u} ∘ (fun _ : Fin 1 ↦ 1))) reindexedCochain.{u,v} = ULift.up 1 := by
  have h := Equiv.cechComplexReindexIso_hom_app_f_π indexEquiv.{u}
    (fun _ : ULift.{u + 1} (Fin 2) ↦ (⊤ : Opens (OnePoint ℂ)))
    tuplePresheaf.{max u v} 0 (fun _ ↦ 1)
  exact (congrArg (fun f ↦ f.hom tupleCochain.{max u v}) h).trans tupleCochain_one

/-- The zero tuple also retains its value under the actual cross-universe index exchange. -/
theorem reindexedCochain_zero :
    (Pi.π (fun _ : Fin 1 → ULift.{u + 1} (Fin 2) ↦ coefficient.{max u v})
      (indexEquiv.{u} ∘ (fun _ : Fin 1 ↦ 0))) reindexedCochain.{u,v} = 0 := by
  have h := Equiv.cechComplexReindexIso_hom_app_f_π indexEquiv.{u}
    (fun _ : ULift.{u + 1} (Fin 2) ↦ (⊤ : Opens (OnePoint ℂ)))
    tuplePresheaf.{max u v} 0 (fun _ ↦ 0)
  exact (congrArg (fun f ↦ f.hom tupleCochain.{max u v}) h).trans tupleCochain_zero

/-- A point cover with a distinguished whole-space neighborhood. -/
def puncturedCover : PointOpenCover (OnePoint ℂ) where
  opens x := if x = OnePoint.infty then ⊤ else
    ⟨{OnePoint.infty}ᶜ, isClosed_singleton.isOpen_compl⟩
  mem_opens x := by
    by_cases hx : x = OnePoint.infty
    · simp [hx]
    · simp [hx]

/-- The full cover maps to the punctured cover by its constant index at infinity. -/
def coverRefinement :
    (default : PointOpenCover (OnePoint ℂ)).toFormalCoproduct ⟶
      puncturedCover.toFormalCoproduct where
  f _ := OnePoint.infty
  φ _ := homOfLE (by simp [puncturedCover])

/-- The native fixed-cover class of the actual nonzero section. -/
def coverClass (U : PointOpenCover (OnePoint ℂ)) :=
  HomologicalComplex.homologyMap
    (TauCeti.CategoryTheory.cechAugmentation U.opens isTerminalTop pointSheaf.{v}.obj) 0
    ((HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℕ) 0
      (pointSheaf.{v}.obj.obj (op ⊤))).inv oneSection.{v})

/-- The actual cover inclusion detects the chosen nonzero class. -/
theorem coverClass_inclusion (U : PointOpenCover (OnePoint ℂ)) :
    (TauCeti.CategoryTheory.cechCohomologyι PointOpenCover.toFormalCoproduct
      (fun _ _ h ↦ h) 0 U).app pointSheaf.{v}.obj (coverClass.{v} U) = oneClass.{v} := by
  exact (congrArg (fun f ↦ f.hom oneSection.{v})
    (cechCohomologyZeroIso_hom pointSheaf.{v} U)).symm

/-- The nonidentity refinement acts on the native representative as prescribed. -/
theorem coverClass_refinement :
    HomologicalComplex.homologyMap
      (CategoryTheory.cechComplexMap pointSheaf.{v}.obj coverRefinement) 0
      (coverClass.{v} puncturedCover) = coverClass.{v} default := by
  have h := congrArg (fun f ↦ HomologicalComplex.homologyMap f 0)
    (TauCeti.CategoryTheory.cechAugmentation_comp_cechComplexMap
      isTerminalTop pointSheaf.{v}.obj coverRefinement)
  rw [HomologicalComplex.homologyMap_comp] at h
  exact congrArg (fun f ↦ f.hom ((HomologicalComplex.singleObjHomologySelfIso
    (ComplexShape.up ℕ) 0 (pointSheaf.{v}.obj.obj (op ⊤))).inv oneSection.{v})) h

/-- Multiplication by two is an actual morphism of the native point sheaf. -/
def twiceSheafMap : pointSheaf.{v} ⟶ pointSheaf.{v} :=
  (Opens.pointGrothendieckTopology (OnePoint.infty : OnePoint ℂ)).skyscraperSheafFunctor.map
    ((2 : ℕ) • 𝟙 coefficient.{v})

/-- The coefficient-object morphism doubles the native point reading. -/
theorem twiceSheafMap_pointRead :
    (twiceSheafMap.{v}.hom.app (op ⊤)) ≫ pointRead.{v} =
      pointRead.{v} ≫ ((2 : ℕ) • 𝟙 coefficient.{v}) :=
  Pi.map_π (fun _ : ULift.{0} (PLift ((OnePoint.infty : OnePoint ℂ) ∈
    (⊤ : Opens (OnePoint ℂ)))) ↦ (2 : ℕ) • 𝟙 coefficient.{v}) ⟨⟨trivial⟩⟩

/-- The doubled section has actual value two. -/
theorem twiceSheafMap_oneSection_read :
    pointRead.{v} ((twiceSheafMap.{v}.hom.app (op ⊤)) oneSection.{v}) = ULift.up 2 := by
  calc
    _ = ((2 : ℕ) • 𝟙 coefficient.{v}) (pointRead.{v} oneSection.{v}) :=
      congrArg (fun f ↦ f.hom oneSection.{v}) twiceSheafMap_pointRead.{v}
    _ = ULift.up 2 := by
      rw [oneSection_read]
      simp only [two_nsmul, ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.hom_id]
      exact congrArg ULift.up (one_add_one_eq_two : (1 : ℂ) + 1 = 2)

/-- The actual same-category coefficient-object map commutes with native base transport. -/
theorem twiceSheafMap_transport :
    (cechCohomology (TopCat.of (ULift.{u + 1} (OnePoint ℂ)))
      (ModuleCat.{max (u + 1) (v + 1)} ℂ) 0).map
        (Functor.whiskerLeft liftHomeomorph.{u}.opensCongr.equivalence.inverse.op
          twiceSheafMap.{max u v}.hom)
        ((cechCohomologyIso
          (X := TopCat.of (OnePoint ℂ)) (Y := TopCat.of (ULift.{u + 1} (OnePoint ℂ)))
          (A := ModuleCat.{max (u + 1) (v + 1)} ℂ) liftHomeomorph.{u} 0).hom.app
            pointSheaf.{max u v}.obj oneClass.{max u v}) =
      (cechCohomologyIso
        (X := TopCat.of (OnePoint ℂ)) (Y := TopCat.of (ULift.{u + 1} (OnePoint ℂ)))
        (A := ModuleCat.{max (u + 1) (v + 1)} ℂ) liftHomeomorph.{u} 0).hom.app
          pointSheaf.{max u v}.obj
          ((cechCohomology (TopCat.of (OnePoint ℂ))
            (ModuleCat.{max (u + 1) (v + 1)} ℂ) 0).map
              twiceSheafMap.{max u v}.hom oneClass.{max u v}) := by
  have h := ConcreteCategory.congr_hom
    ((cechCohomologyIso
      (X := TopCat.of (OnePoint ℂ)) (Y := TopCat.of (ULift.{u + 1} (OnePoint ℂ)))
      (A := ModuleCat.{max (u + 1) (v + 1)} ℂ) liftHomeomorph.{u} 0).hom.naturality
        twiceSheafMap.{max u v}.hom) oneClass.{max u v}
  simp only [ConcreteCategory.comp_apply] at h
  exact h.symm

/-- A nonzero-valued presheaf on the literal empty base in arbitrary universe. -/
abbrev emptyPresheaf : (Opens PEmpty.{u + 1})ᵒᵖ ⥤ ModuleCat.{max (u + 1) (v + 1)} ℂ :=
  (Functor.const _).obj coefficient.{max u v}

/-- The actual empty-base presheaf is nonzero, as witnessed by one at the empty open. -/
theorem emptyPresheaf_not_isZero : ¬ IsZero emptyPresheaf.{u,v} := by
  intro h
  have hz : IsZero (emptyPresheaf.{u,v}.obj (op ⊥)) :=
    ((evaluation _ _).obj (op ⊥)).map_isZero h
  have he : (ULift.up 1 : emptyPresheaf.{u,v}.obj (op ⊥)) = 0 :=
    @Subsingleton.elim _ (ModuleCat.subsingleton_of_isZero hz) _ _
  exact one_ne_zero (congrArg ULift.down he)

/-- Native all-degree Čech cohomology vanishes despite the nonzero empty-open value. -/
theorem emptyPresheaf_cech_isZero (n : ℕ) :
    IsZero ((cechCohomology (TopCat.of PEmpty.{u + 1})
      (ModuleCat.{max (u + 1) (v + 1)} ℂ) n).obj emptyPresheaf.{u,v}) := by
  exact isZero_cechCohomology_obj_of_isEmpty _ _ _ _

/-- The actual reindexing map on an empty family, in arbitrary index universes. -/
def emptyIndexMap (n : ℕ) :=
  ((Equiv.cechComplexReindexIso
    (A := ModuleCat.{max (u + 1) (v + 1)} ℂ)
    (Equiv.ulift.symm : PEmpty.{u + 1} ≃ ULift.{v + 1} PEmpty.{u + 1})
    (fun _ ↦ (⊤ : Opens PEmpty.{u + 1}))).hom.app emptyPresheaf.{u,v}).f n

/-- Every native component of the empty-family comparison is the zero map. -/
theorem emptyIndexMap_eq_zero (n : ℕ) : emptyIndexMap.{u,v} n = 0 := by
  apply Pi.hom_ext
  intro a
  exact PEmpty.elim (a 0).down

/-- The native two-component compact base. -/
abbrev disconnectedBase := (OnePoint ℂ) ⊕ (OnePoint ℂ)

/-- A native skyscraper supported at infinity on the left component. -/
abbrev disconnectedSheaf :=
  skyscraperSheaf (X := TopCat.of disconnectedBase) (Sum.inl OnePoint.infty)
    (ModuleCat.of ℂ ℂ)

/-- The nonzero section of the actual disconnected-base sheaf. -/
def disconnectedSection : disconnectedSheaf.obj.obj (op ⊤) :=
  (skyscraperSheafGlobalSectionsIso (X := TopCat.of disconnectedBase)
    (Sum.inl OnePoint.infty) (ModuleCat.of ℂ ℂ)).inv 1

/-- The original section reads one on its supported component. -/
theorem disconnectedSection_read :
    (skyscraperSheafGlobalSectionsIso (X := TopCat.of disconnectedBase)
      (Sum.inl OnePoint.infty) (ModuleCat.of ℂ ℂ)).hom disconnectedSection = 1 :=
  (skyscraperSheafGlobalSectionsIso (X := TopCat.of disconnectedBase)
    (Sum.inl OnePoint.infty) (ModuleCat.of ℂ ℂ)).inv_hom_id_apply _

/-- The right component is a genuine open disjoint from the skyscraper support. -/
def rightOpen : Opens disconnectedBase := ⟨Set.range Sum.inr, isOpen_range_inr⟩

/-- The actual restriction to the other component is zero. -/
theorem disconnectedSection_right_zero :
    disconnectedSheaf.obj.map (homOfLE (show rightOpen ≤ ⊤ from le_top)).op
      disconnectedSection = 0 := by
  have ht : IsTerminal (disconnectedSheaf.obj.obj (op rightOpen)) := by
    rw [skyscraperSheaf_obj_obj, ite_eq_right (by simp [rightOpen])]
    exact terminalIsTerminal
  have := ModuleCat.subsingleton_of_isZero ht.isZero
  exact Subsingleton.elim _ _

/-- The native degree-zero class on the disconnected base. -/
def disconnectedClass :=
  (cechCohomologyZeroIso disconnectedSheaf).hom disconnectedSection

/-- The class really detects a nonzero supported section. -/
theorem disconnectedClass_ne_zero : disconnectedClass ≠ 0 := by
  intro h
  have hs := (cechCohomologyZeroIso disconnectedSheaf).toLinearEquiv.injective
    (h.trans (map_zero _).symm)
  have ht := congrArg
    (fun s ↦ (skyscraperSheafGlobalSectionsIso (X := TopCat.of disconnectedBase)
      (Sum.inl OnePoint.infty) (ModuleCat.of ℂ ℂ)).hom s) hs
  rw [disconnectedSection_read, map_zero] at ht
  exact one_ne_zero ht

/-- The native sheaf after the nonidentity component swap. -/
abbrev swappedSheaf :=
  ((Homeomorph.sumComm (OnePoint ℂ) (OnePoint ℂ)).opensCongr.equivalence.sheafCongr
    (Opens.grothendieckTopology disconnectedBase)
    (Opens.grothendieckTopology disconnectedBase) (ModuleCat.{0} ℂ)).functor.obj
    disconnectedSheaf

/-- The actual cohomology isomorphism, including the native underlying-presheaf comparison. -/
def swappedCechIso :
    (cechCohomology (TopCat.of disconnectedBase) (ModuleCat.{0} ℂ) 0).obj
        disconnectedSheaf.obj ≅
      (cechCohomology (TopCat.of disconnectedBase) (ModuleCat.{0} ℂ) 0).obj
        swappedSheaf.obj :=
  (cechCohomologyIso (X := TopCat.of disconnectedBase)
    (Y := TopCat.of disconnectedBase) (A := ModuleCat.{0} ℂ)
    (Homeomorph.sumComm (OnePoint ℂ) (OnePoint ℂ)) 0).app disconnectedSheaf.obj

/-- The actual swapped cohomology class remains nonzero. -/
theorem swappedClass_ne_zero : swappedCechIso.hom disconnectedClass ≠ 0 := by
  intro h
  exact disconnectedClass_ne_zero
    (swappedCechIso.toLinearEquiv.injective (h.trans (map_zero _).symm))

/-- The target sheaf has the original complex coefficient object on the right component. -/
def swappedRightIso : swappedSheaf.obj.obj (op rightOpen) ≅ ModuleCat.of ℂ ℂ :=
  eqToIso ((skyscraperSheaf_obj_obj _ _ _).trans
    (ite_eq_left (by simp [rightOpen, Homeomorph.opensCongr])))

/-- The actual target-side section reads one after the component swap. -/
theorem swappedRightIso_read_one : swappedRightIso.hom (swappedRightIso.inv 1) = 1 :=
  swappedRightIso.inv_hom_id_apply _

/-- The actual source restriction to the inverse image of the right component reads one. -/
private theorem source_swapped_right_read :
    (eqToIso ((skyscraperSheaf_obj_obj (X := TopCat.of disconnectedBase)
      (Sum.inl (OnePoint.infty : OnePoint ℂ))
      (ModuleCat.of ℂ ℂ) (op ((Homeomorph.sumComm (OnePoint ℂ) (OnePoint ℂ)).opensCongr.symm
        rightOpen))).trans (ite_eq_left (show
      (Sum.inl (OnePoint.infty : OnePoint ℂ) : disconnectedBase) ∈
        (Homeomorph.sumComm (OnePoint ℂ) (OnePoint ℂ)).opensCongr.symm rightOpen from by
          simp [rightOpen, Homeomorph.opensCongr])))).hom
      (disconnectedSheaf.obj.map
        (homOfLE (show (Homeomorph.sumComm (OnePoint ℂ) (OnePoint ℂ)).opensCongr.symm
          rightOpen ≤ ⊤ from le_top)).op disconnectedSection) = 1 := by
  let U := (Homeomorph.sumComm (OnePoint ℂ) (OnePoint ℂ)).opensCongr.symm rightOpen
  have hp : (Sum.inl (OnePoint.infty : OnePoint ℂ) : disconnectedBase) ∈ U := by
    simp [U, rightOpen, Homeomorph.opensCongr]
  let θ : disconnectedSheaf.obj.obj (op U) ≅ ModuleCat.of ℂ ℂ := eqToIso
    ((skyscraperSheaf_obj_obj (X := TopCat.of disconnectedBase)
      (Sum.inl (OnePoint.infty : OnePoint ℂ)) (ModuleCat.of ℂ ℂ) (op U)).trans
        (ite_eq_left hp))
  have hm : disconnectedSheaf.obj.map (homOfLE (show U ≤ ⊤ from le_top)).op ≫ θ.hom =
      (skyscraperSheafGlobalSectionsIso (X := TopCat.of disconnectedBase)
        (Sum.inl OnePoint.infty) (ModuleCat.of ℂ ℂ)).hom := by
    rw [skyscraperSheafGlobalSectionsIso_hom]
    simp only [θ, eqToIso.hom]
    rw [skyscraperSheaf_obj_map, dite_eq_left hp]
    exact eqToHom_trans _ _
  exact (congrArg (fun f ↦ f.hom disconnectedSection) hm).trans disconnectedSection_read

/-- The actual global section transported by the native underlying-presheaf comparison. -/
def swappedSection : swappedSheaf.obj.obj (op ⊤) :=
  disconnectedSheaf.obj.map
    (eqToHom (Homeomorph.sumComm (OnePoint ℂ) (OnePoint ℂ)).opensCongr.symm.map_top).op
      disconnectedSection

/-- The actual transported global section, restricted to the right component, reads one. -/
theorem swappedSection_right_read :
    swappedRightIso.hom
      (swappedSheaf.obj.map (homOfLE (show rightOpen ≤ ⊤ from le_top)).op swappedSection) =
        1 := by
  let h := Homeomorph.sumComm (OnePoint ℂ) (OnePoint ℂ)
  let i := (homOfLE (show rightOpen ≤ ⊤ from le_top)).op
  let q : op (⊤ : Opens disconnectedBase) ⟶
      h.opensCongr.equivalence.inverse.op.obj (op ⊤) :=
    (eqToHom h.opensCongr.symm.map_top).op
  have hc : disconnectedSheaf.obj.map q ≫ swappedSheaf.obj.map i =
      disconnectedSheaf.obj.map
        (homOfLE (show h.opensCongr.symm rightOpen ≤ ⊤ from le_top)).op := by
    -- The native site-equivalence map is inverse precomposition, not a separate comparison.
    erw [Equivalence.sheafCongr.functor_obj_obj_map]
    exact (disconnectedSheaf.obj.map_comp q
      (h.opensCongr.equivalence.inverse.op.map i)).symm.trans
        (congrArg disconnectedSheaf.obj.map (Subsingleton.elim _ _))
  let θ : disconnectedSheaf.obj.obj (op (h.opensCongr.symm rightOpen)) ≅
      ModuleCat.of ℂ ℂ := eqToIso
    ((skyscraperSheaf_obj_obj (X := TopCat.of disconnectedBase)
      (Sum.inl (OnePoint.infty : OnePoint ℂ))
      (ModuleCat.of ℂ ℂ) (op (h.opensCongr.symm rightOpen))).trans
        (ite_eq_left (show (Sum.inl (OnePoint.infty : OnePoint ℂ) : disconnectedBase) ∈
          h.opensCongr.symm rightOpen from by simp [h, rightOpen, Homeomorph.opensCongr])))
  have he := congrArg (fun f ↦ (f ≫ θ.hom).hom disconnectedSection) hc
  exact he.trans source_swapped_right_read

/-- The native split short exact sequence on the disconnected base. -/
def disconnectedSplit :
    ShortComplex (Sheaf (Opens.grothendieckTopology (TopCat.of disconnectedBase))
      (ModuleCat.{0} ℂ)) :=
  ShortComplex.mk (biprod.inl : disconnectedSheaf ⟶ disconnectedSheaf ⊞ disconnectedSheaf)
    biprod.snd (by simp)

/-- The sequence `0 → F → F ⊞ F → F → 0`, with first inclusion and second projection,
is short exact. -/
theorem disconnectedSplit_shortExact : disconnectedSplit.ShortExact :=
  (ShortComplex.Splitting.ofHasBinaryBiproduct disconnectedSheaf disconnectedSheaf).shortExact

/-- The actual sheaf connecting map of the split sequence is zero in every degree. -/
theorem disconnectedSplit_delta_zero (n : ℕ) :
    disconnectedSplit_shortExact.cechCohomologyδ n = 0 := by
  have h := disconnectedSplit_shortExact.cechCohomology_comp_δ n
  have : IsSplitEpi disconnectedSplit.g.hom :=
    ((ShortComplex.Splitting.ofHasBinaryBiproduct disconnectedSheaf disconnectedSheaf).map
      (sheafToPresheaf _ _)).isSplitEpi_g
  have : Epi ((cechCohomology (TopCat.of disconnectedBase) (ModuleCat.{0} ℂ) n).map
      disconnectedSplit.g.hom) := inferInstance
  exact (cancel_epi ((cechCohomology (TopCat.of disconnectedBase) (ModuleCat.{0} ℂ) n).map
    disconnectedSplit.g.hom)).mp (h.trans comp_zero.symm)

/-- Component swap carries the native connecting map through the actual δ square. -/
theorem disconnectedSplit_delta_transport (n : ℕ) :
    let E := (Homeomorph.sumComm (OnePoint ℂ) (OnePoint ℂ)).opensCongr.equivalence.sheafCongr
      (Opens.grothendieckTopology disconnectedBase)
      (Opens.grothendieckTopology disconnectedBase) (ModuleCat.{0} ℂ)
    disconnectedSplit_shortExact.cechCohomologyδ n ≫
        (cechCohomologyIso (X := TopCat.of disconnectedBase)
          (Y := TopCat.of disconnectedBase) (A := ModuleCat.{0} ℂ)
          (Homeomorph.sumComm (OnePoint ℂ) (OnePoint ℂ)) (n + 1)).hom.app
            disconnectedSplit.X₁.obj =
      (cechCohomologyIso (X := TopCat.of disconnectedBase)
        (Y := TopCat.of disconnectedBase) (A := ModuleCat.{0} ℂ)
        (Homeomorph.sumComm (OnePoint ℂ) (OnePoint ℂ)) n).hom.app disconnectedSplit.X₃.obj ≫
          (disconnectedSplit_shortExact.map_of_exact E.functor).cechCohomologyδ
            (X := TopCat.of disconnectedBase) (R := ℂ) n :=
  disconnectedSplit_shortExact.cechCohomologyδ_comp_cechCohomologyIso_hom_app
    (X := TopCat.of disconnectedBase) (Y := TopCat.of disconnectedBase)
    (Homeomorph.sumComm (OnePoint ℂ) (OnePoint ℂ)) n

/-- The actual split sequence after passing to native underlying presheaves. -/
abbrev disconnectedPresheafSplit :=
  disconnectedSplit.map (sheafToPresheaf (Opens.grothendieckTopology
    (TopCat.of disconnectedBase)) (ModuleCat.{0} ℂ))

/-- The actual fixed-cover complexes of the split sequence are short exact. -/
theorem disconnectedCover_shortExact :
    (disconnectedPresheafSplit.map (CategoryTheory.cechComplexFunctor
      (default : PointOpenCover disconnectedBase).opens)).ShortExact :=
  (((ShortComplex.Splitting.ofHasBinaryBiproduct disconnectedSheaf disconnectedSheaf).map
    (sheafToPresheaf _ _)).map (CategoryTheory.cechComplexFunctor
      (default : PointOpenCover disconnectedBase).opens)).shortExact

/-- The actual fixed-cover connecting map obeys the native component-swap square. -/
theorem disconnectedCover_delta_transport (n : ℕ) :
    disconnectedCover_shortExact.δ n (n + 1) rfl ≫
        HomologicalComplex.homologyMap
          ((cechComplexIso (X := TopCat.of disconnectedBase)
            (Y := TopCat.of disconnectedBase) (A := ModuleCat.{0} ℂ)
            (Homeomorph.sumComm (OnePoint ℂ) (OnePoint ℂ)) default).hom.app
              disconnectedPresheafSplit.X₁) (n + 1) =
      HomologicalComplex.homologyMap
        ((cechComplexIso (X := TopCat.of disconnectedBase)
          (Y := TopCat.of disconnectedBase) (A := ModuleCat.{0} ℂ)
          (Homeomorph.sumComm (OnePoint ℂ) (OnePoint ℂ)) default).hom.app
            disconnectedPresheafSplit.X₃) n ≫
        (cechComplexIso_shortExact (X := TopCat.of disconnectedBase)
          (Y := TopCat.of disconnectedBase) (Homeomorph.sumComm (OnePoint ℂ) (OnePoint ℂ))
          default disconnectedCover_shortExact).δ n (n + 1) rfl :=
  δ_comp_homologyMap_cechComplexIso_hom_app (X := TopCat.of disconnectedBase)
    (Y := TopCat.of disconnectedBase) (Homeomorph.sumComm (OnePoint ℂ) (OnePoint ℂ))
    default disconnectedCover_shortExact n

open TauCeti.CategoryTheory

/-- The swap's one coordinate is literally the lifted zero coordinate. -/
example :
    (Pi.π (fun _ : Fin 1 → ULift.{u + 1} (Fin 2) ↦ coefficient.{max u v})
      (fun _ ↦ ULift.up 0)) reindexedCochain.{u,v} = ULift.up 1 := by
  have hi : indexEquiv.{u} ∘ (fun _ : Fin 1 ↦ 1) = (fun _ ↦ ULift.up 0) := by
    funext x
    simp [indexEquiv]
  simpa only [hi] using reindexedCochain_one.{u,v}

/-- The inverse of the actual cross-universe map recovers the original cochain. -/
example :
    (((Equiv.cechComplexReindexIso indexEquiv.{u}
      (fun _ : ULift.{u + 1} (Fin 2) ↦ (⊤ : Opens (OnePoint ℂ)))).inv.app
        tuplePresheaf.{max u v}).f 0) reindexedCochain.{u,v} = tupleCochain.{max u v} := by
  have h := congrArg (fun f ↦ f.f 0)
    ((Equiv.cechComplexReindexIso indexEquiv.{u}
      (fun _ : ULift.{u + 1} (Fin 2) ↦ (⊤ : Opens (OnePoint ℂ)))).app
        tuplePresheaf.{max u v}).hom_inv_id
  simpa only [reindexedCochain, Iso.app_hom, Iso.app_inv, HomologicalComplex.comp_f,
    HomologicalComplex.id_f, ModuleCat.comp_apply, ModuleCat.id_apply] using
      congrArg (fun f ↦ f.hom tupleCochain.{max u v}) h

/-- The public inverse factor law reads each actual lifted tuple. -/
example (n : ℕ) (a : Fin (n + 1) → Fin 2) :
    ((Equiv.cechComplexReindexIso indexEquiv.{u}
      (fun _ : ULift.{u + 1} (Fin 2) ↦ (⊤ : Opens (OnePoint ℂ)))).inv.app
        tuplePresheaf.{max u v}).f n ≫ Pi.π _ a = Pi.π _ (indexEquiv.{u} ∘ a) :=
  Equiv.cechComplexReindexIso_inv_app_f_π _ _ _ n a

/-- Identity indexing leaves the complete native complex functor unchanged. -/
example :
    Equiv.cechComplexReindexIso (A := ModuleCat.{v + 1} ℂ) (Equiv.refl (Fin 2))
      (fun _ ↦ (⊤ : Opens (OnePoint ℂ))) = Iso.refl _ :=
  Equiv.cechComplexReindexIso_refl _

/-- Two actual cross-universe index changes obey the public composition law. -/
example :
    Equiv.cechComplexReindexIso (A := ModuleCat.{max (u + 1) (v + 1)} ℂ)
      (indexEquiv.{u}.trans indexEquiv.{u}.symm) (fun _ ↦ (⊤ : Opens (OnePoint ℂ))) =
      Equiv.cechComplexReindexIso indexEquiv.{u}
        ((fun _ ↦ (⊤ : Opens (OnePoint ℂ))) ∘ indexEquiv.{u}.symm) ≪≫
          Equiv.cechComplexReindexIso indexEquiv.{u}.symm (fun _ ↦ (⊤ : Opens (OnePoint ℂ))) :=
  Equiv.cechComplexReindexIso_trans _ _ _

/-- The nonidentity refinement remains a native refinement after lifting the sphere. -/
example :
    let h := liftHomeomorph.{u}
    let P := pointSheaf.{max u v}.obj
    let U : PointOpenCover (OnePoint ℂ) := default
    cechComplexMap P coverRefinement ≫ (cechComplexIso
      (X := TopCat.of (OnePoint ℂ)) (Y := TopCat.of (ULift.{u + 1} (OnePoint ℂ)))
      (A := ModuleCat.{max (u + 1) (v + 1)} ℂ) h U).hom.app P =
      (cechComplexIso
      (X := TopCat.of (OnePoint ℂ)) (Y := TopCat.of (ULift.{u + 1} (OnePoint ℂ)))
      (A := ModuleCat.{max (u + 1) (v + 1)} ℂ) h puncturedCover).hom.app P ≫
        cechComplexMap (h.opensCongr.equivalence.inverse.op ⋙ P)
          (U.mapHomeomorphHom h coverRefinement) :=
  cechComplexMap_comp_cechComplexIso_hom_app
    (X := TopCat.of (OnePoint ℂ)) (Y := TopCat.of (ULift.{u + 1} (OnePoint ℂ)))
    (A := ModuleCat.{max (u + 1) (v + 1)} ℂ) _ _ _ _

/-- The augmentation of the actual punctured cover is transported, including its top section. -/
example :
    let h := liftHomeomorph.{u}
    let P := pointSheaf.{max u v}.obj
    cechAugmentation puncturedCover.opens isTerminalTop P ≫
        (cechComplexIso
      (X := TopCat.of (OnePoint ℂ)) (Y := TopCat.of (ULift.{u + 1} (OnePoint ℂ)))
      (A := ModuleCat.{max (u + 1) (v + 1)} ℂ) h puncturedCover).hom.app P =
      (CochainComplex.single₀ (ModuleCat.{max (u + 1) (v + 1)} ℂ)).map
          (P.map (eqToHom h.opensCongr.symm.map_top).op) ≫
        cechAugmentation (puncturedCover.mapHomeomorph h).opens isTerminalTop
          (h.opensCongr.equivalence.inverse.op ⋙ P) :=
  cechAugmentation_comp_cechComplexIso_hom_app
    (X := TopCat.of (OnePoint ℂ)) (Y := TopCat.of (ULift.{u + 1} (OnePoint ℂ)))
    (A := ModuleCat.{max (u + 1) (v + 1)} ℂ) _ _ _

/-- The actual cover insertion transports in every degree, not just Γ⁰. -/
example (n : ℕ) :
    let h := liftHomeomorph.{u}
    let P := pointSheaf.{max u v}.obj
    (cechCohomologyι PointOpenCover.toFormalCoproduct (fun _ _ hf ↦ hf) n puncturedCover).app P ≫
        (cechCohomologyIso
          (X := TopCat.of (OnePoint ℂ)) (Y := TopCat.of (ULift.{u + 1} (OnePoint ℂ)))
          (A := ModuleCat.{max (u + 1) (v + 1)} ℂ) h n).hom.app P =
      HomologicalComplex.homologyMap ((cechComplexIso
      (X := TopCat.of (OnePoint ℂ)) (Y := TopCat.of (ULift.{u + 1} (OnePoint ℂ)))
      (A := ModuleCat.{max (u + 1) (v + 1)} ℂ) h puncturedCover).hom.app P) n ≫
        (cechCohomologyι PointOpenCover.toFormalCoproduct (fun _ _ hf ↦ hf) n
          (puncturedCover.mapHomeomorph h)).app (h.opensCongr.equivalence.inverse.op ⋙ P) :=
  cechCohomologyIso_hom_app_ι
    (X := TopCat.of (OnePoint ℂ)) (Y := TopCat.of (ULift.{u + 1} (OnePoint ℂ)))
    (A := ModuleCat.{max (u + 1) (v + 1)} ℂ) _ _ _ _

/-- Actual transport of the literal empty base has zero native cohomology in every degree. -/
example (n : ℕ) :
    let h : PEmpty.{u + 1} ≃ₜ ULift.{v + 1} PEmpty.{u + 1} := Homeomorph.ulift.symm
    IsZero ((cechCohomology (TopCat.of (ULift.{v + 1} PEmpty.{u + 1}))
      (ModuleCat.{max (u + 1) (v + 1)} ℂ) n).obj
        (h.opensCongr.equivalence.inverse.op ⋙ emptyPresheaf.{u,v})) :=
  isZero_cechCohomology_obj_of_isEmpty _ _ _ _

/-- Transporting the doubled section gives an actual target-side section. -/
def liftedTwiceSection := sectionIso.{u,v}.hom
  ((twiceSheafMap.{max u v}.hom.app (op ⊤)) oneSection.{max u v})

/-- The transported doubled section has the literal coefficient reading two. -/
theorem liftedTwiceSection_read :
    pointRead.{max u v} (sectionIso.{u,v}.inv liftedTwiceSection.{u,v}) = ULift.up 2 := by
  rw [liftedTwiceSection, Iso.hom_inv_id_apply]
  exact twiceSheafMap_oneSection_read

/-- The transported coefficient action is tied to the actual class of that doubled section. -/
theorem liftedTwiceClass_eq_section :
    (cechCohomology (TopCat.of (ULift.{u + 1} (OnePoint ℂ)))
      (ModuleCat.{max (u + 1) (v + 1)} ℂ) 0).map
        (Functor.whiskerLeft liftHomeomorph.{u}.opensCongr.equivalence.inverse.op
          twiceSheafMap.{max u v}.hom) liftedClass.{u,v} =
      (Topology.cechCohomologyZeroIso liftedSheaf.{u,v}).hom liftedTwiceSection.{u,v} := by
  let F := pointSheaf.{max u v}
  let α := twiceSheafMap.{max u v}
  let c := Topology.cechCohomologyZeroIso F
  let M := cechCohomology (TopCat.of (OnePoint ℂ))
    (ModuleCat.{max (u + 1) (v + 1)} ℂ) 0
  have hs : M.map α.hom oneClass.{max u v} =
      c.hom (α.hom.app (op ⊤) oneSection.{max u v}) := by
    have h := Topology.cechCohomologyZeroIso_hom_naturality F α
    exact (ConcreteCategory.comp_apply c.hom (M.map α.hom) oneSection.{max u v}).symm.trans
      ((ConcreteCategory.congr_hom h oneSection.{max u v}).symm.trans
        (ConcreteCategory.comp_apply (α.hom.app (op ⊤)) c.hom oneSection.{max u v}))
  have ht := Homeomorph.cechCohomologyZeroIso_hom_comp_cechCohomologyIso_hom_app
    (X := TopCat.of (OnePoint ℂ)) (Y := TopCat.of (ULift.{u + 1} (OnePoint ℂ)))
    liftHomeomorph.{u} F
  let d := (cechCohomologyIso
    (X := TopCat.of (OnePoint ℂ)) (Y := TopCat.of (ULift.{u + 1} (OnePoint ℂ)))
    (A := ModuleCat.{max (u + 1) (v + 1)} ℂ) liftHomeomorph.{u} 0).hom.app F.obj
  calc
    _ = d (M.map α.hom oneClass.{max u v}) := twiceSheafMap_transport.{u,v}
    _ = d (c.hom (α.hom.app (op ⊤) oneSection.{max u v})) := congrArg d.hom hs
    _ = (c.hom ≫ d) (α.hom.app (op ⊤) oneSection.{max u v}) :=
      (ConcreteCategory.comp_apply _ _ _).symm
    _ = _ := (ConcreteCategory.congr_hom ht (α.hom.app (op ⊤) oneSection.{max u v})).trans
      (ConcreteCategory.comp_apply _ _ _)

/-- On the genuine component swap, inverse cohomology transport is native pullback. -/
example (n : ℕ) :
    let h := Homeomorph.sumComm (OnePoint ℂ) (OnePoint ℂ)
    (cechCohomologyIso (X := TopCat.of disconnectedBase)
      (Y := TopCat.of disconnectedBase) (A := ModuleCat.{0} ℂ) h n).inv.app
        disconnectedSheaf.obj =
      (TopCat.isoOfHomeo (X := TopCat.of disconnectedBase)
          (Y := TopCat.of disconnectedBase) h).hom.cechCohomologyPullback
          (Q := disconnectedSheaf.obj) n
        (𝟙 ((TopCat.Presheaf.pushforward (ModuleCat.{0} ℂ)
          (TopCat.isoOfHomeo (X := TopCat.of disconnectedBase)
          (Y := TopCat.of disconnectedBase) h).hom).obj
          disconnectedSheaf.obj)) :=
  cechCohomologyIso_inv_app_eq_cechCohomologyPullback
    (X := TopCat.of disconnectedBase) (Y := TopCat.of disconnectedBase)
    (A := ModuleCat.{0} ℂ) _ _ _

/-- A value-two cochain on the one-member empty-open cover of the literal empty base. -/
def emptyFixedCochain :
    ((cechComplexFunctor (fun _ : Fin 1 ↦ (⊥ : Opens PEmpty.{u + 1}))).obj
      emptyPresheaf.{u,v}).X 0 :=
  (Pi.lift (fun _ : Fin 1 → Fin 1 ↦ 𝟙 coefficient.{max u v})).hom (ULift.up 2)

/-- Change the actual fixed cover's index universe without adding any point to the base. -/
def emptyFixedTransportedCochain :=
  ((Equiv.cechComplexReindexIso (Equiv.ulift.symm : Fin 1 ≃ ULift.{v + 1} (Fin 1))
    (fun _ ↦ (⊥ : Opens PEmpty.{u + 1}))).hom.app emptyPresheaf.{u,v}).f 0
      emptyFixedCochain.{u,v}

/-- This fixed-cover cochain reads two after transport; global empty-base Čech cohomology
still vanishes by `emptyPresheaf_cech_isZero`. No nonzero empty-open sheaf is asserted. -/
theorem emptyFixedTransportedCochain_read_two :
    (Pi.π (fun _ : Fin 1 → ULift.{v + 1} (Fin 1) ↦ coefficient.{max u v})
      (fun _ ↦ ULift.up 0)) emptyFixedTransportedCochain.{u,v} = ULift.up 2 := by
  have h := Equiv.cechComplexReindexIso_hom_app_f_π
    (Equiv.ulift.symm : Fin 1 ≃ ULift.{v + 1} (Fin 1))
    (fun _ ↦ (⊥ : Opens PEmpty.{u + 1})) emptyPresheaf.{u,v} 0 (fun _ ↦ 0)
  have hp : (Pi.π (fun _ : Fin 1 → Fin 1 ↦ coefficient.{max u v}) (fun _ ↦ 0))
      emptyFixedCochain.{u,v} = ULift.up 2 :=
    congrArg (fun f ↦ f.hom (ULift.up 2 : coefficient.{max u v}))
      (Pi.lift_comp_π (fun _ : Fin 1 → Fin 1 ↦ 𝟙 coefficient.{max u v}) (fun _ ↦ 0))
  exact (congrArg (fun f ↦ f.hom emptyFixedCochain.{u,v}) h).trans hp

/-- The component-swap inverse agrees with native pullback for the actual doubling map too. -/
example (n : ℕ) :
    let h := Homeomorph.sumComm (OnePoint ℂ) (OnePoint ℂ)
    let f := (TopCat.isoOfHomeo (X := TopCat.of disconnectedBase)
      (Y := TopCat.of disconnectedBase) h).hom
    let P := disconnectedSheaf.obj
    let φ : P ⟶ P := (2 : ℕ) • 𝟙 P
    (cechCohomologyIso (X := TopCat.of disconnectedBase)
      (Y := TopCat.of disconnectedBase) (A := ModuleCat.{0} ℂ) h n).inv.app P ≫
        (cechCohomology (TopCat.of disconnectedBase) (ModuleCat.{0} ℂ) n).map φ =
      f.cechCohomologyPullback (Q := P) n
        ((TopCat.Presheaf.pushforward (ModuleCat.{0} ℂ) f).map φ) := by
  intro h f P φ
  have hn := f.cechCohomologyPullback_naturality n (𝟙 _)
    ((TopCat.Presheaf.pushforward (ModuleCat.{0} ℂ) f).map φ) (𝟙 _) φ
    ((Category.id_comp _).trans (Category.id_comp _).symm)
  -- pushforward's presheaf map is definitionally whiskering, so its identity is map_id.
  erw [CategoryTheory.Functor.map_id, Category.id_comp] at hn
  exact (cechCohomologyIso_inv_app_eq_cechCohomologyPullback
    (X := TopCat.of disconnectedBase) (Y := TopCat.of disconnectedBase)
    (A := ModuleCat.{0} ℂ) h P n =≫ _).trans hn.symm

end TauCeti.Examples.CechHomeomorph

namespace TauCeti.Examples.CechHomeomorph

attribute [local instance] Classical.propDecidable
attribute [local instance] ModuleCat.hasLimitsOfSize TauCeti.hasSheafify_moduleCat

open CategoryTheory.Functor

/-- A universe-large native skyscraper supported on the left disconnected component. -/
abbrev compositionSheaf :
    Sheaf (Opens.grothendieckTopology (TopCat.of disconnectedBase)) (ModuleCat.{u + 1} ℂ) :=
  (Opens.pointGrothendieckTopology
    (Sum.inl (OnePoint.infty : OnePoint ℂ) : disconnectedBase)).skyscraperSheaf coefficient.{u}

/-- A section with actual coefficient value two. -/
def compositionSection : compositionSheaf.{u}.obj.obj (op ⊤) :=
  (Pi.lift (fun _ ↦ 𝟙 coefficient.{u})).hom (ULift.up 2)

/-- The literal point-fibre reading over the top open of the disconnected base. -/
def compositionRead : compositionSheaf.{u}.obj.obj (op ⊤) ⟶ coefficient.{u} :=
  Pi.π (fun _ : ULift.{0} (PLift ((Sum.inl (OnePoint.infty : OnePoint ℂ) : disconnectedBase) ∈
    (⊤ : Opens disconnectedBase))) ↦ coefficient.{u}) ⟨⟨trivial⟩⟩

/-- The chosen native section reads two at its supported point. -/
theorem compositionSection_read_two : compositionRead.{u} compositionSection.{u} = ULift.up 2 := by
  exact congrArg (fun f : coefficient.{u} ⟶ coefficient.{u} ↦ f (ULift.up 2))
    (Pi.lift_comp_π (fun _ : ULift.{0}
      (PLift ((Sum.inl (OnePoint.infty : OnePoint ℂ) : disconnectedBase) ∈
        (⊤ : Opens disconnectedBase))) ↦ 𝟙 coefficient.{u}) ⟨⟨trivial⟩⟩)

/-- The native degree-zero class of the value-two section. -/
def compositionClass := (cechCohomologyZeroIso compositionSheaf.{u}).hom compositionSection.{u}

/-- The component swap is followed by a genuine change of base universe. -/
def compositionLift : disconnectedBase ≃ₜ ULift.{u + 1} disconnectedBase := Homeomorph.ulift.symm

/-- The nonidentity component permutation used before the universe lift. -/
abbrev compositionSwap : disconnectedBase ≃ₜ disconnectedBase :=
  Homeomorph.sumComm (OnePoint ℂ) (OnePoint ℂ)

/-- The chosen permutation genuinely moves the supported point to the other component. -/
theorem compositionSwap_left :
    compositionSwap (Sum.inl (OnePoint.infty : OnePoint ℂ)) = Sum.inr OnePoint.infty := rfl

/-- The actual inverse-opens identification between sequential and composite coefficients. -/
def compositionCoefficientIso :
    compositionLift.{u}.opensCongr.equivalence.inverse.op ⋙
        (compositionSwap.opensCongr.equivalence.inverse.op ⋙ compositionSheaf.{u}.obj) ≅
      (compositionSwap.trans compositionLift.{u}).opensCongr.equivalence.inverse.op ⋙
        compositionSheaf.{u}.obj :=
  (eqToIso (congrArg (fun G : (Opens (ULift.{u + 1} disconnectedBase))ᵒᵖ ⥤
      (Opens disconnectedBase)ᵒᵖ ↦
      (Functor.whiskeringLeft _ _ (ModuleCat.{u + 1} ℂ)).obj G)
      (opensCongr_inverse_op_trans compositionSwap compositionLift.{u}).symm)).app
    compositionSheaf.{u}.obj

/-- The actual sequential swap/lift cohomology map, including canonical coefficient transport. -/
def compositionSequentialMap :
    (cechCohomology (TopCat.of disconnectedBase) (ModuleCat.{u + 1} ℂ) 0).obj
        compositionSheaf.{u}.obj ⟶
      (cechCohomology (TopCat.of (ULift.{u + 1} disconnectedBase))
        (ModuleCat.{u + 1} ℂ) 0).obj
        ((compositionSwap.trans compositionLift.{u}).opensCongr.equivalence.inverse.op ⋙
          compositionSheaf.{u}.obj) :=
  (compositionSwap.cechCohomologyIso (X := TopCat.of disconnectedBase)
    (Y := TopCat.of disconnectedBase) (A := ModuleCat.{u + 1} ℂ) 0).hom.app
      compositionSheaf.{u}.obj ≫
    (compositionLift.{u}.cechCohomologyIso (X := TopCat.of disconnectedBase)
      (Y := TopCat.of (ULift.{u + 1} disconnectedBase))
      (A := ModuleCat.{u + 1} ℂ) 0).hom.app
      (compositionSwap.opensCongr.equivalence.inverse.op ⋙ compositionSheaf.{u}.obj) ≫
    (cechCohomology (TopCat.of (ULift.{u + 1} disconnectedBase))
      (ModuleCat.{u + 1} ℂ) 0).map compositionCoefficientIso.{u}.hom

/-- Native swap/lift transport on the value-two section equals the actual composite map. -/
theorem compositionSequentialMap_eq :
    compositionSequentialMap.{u} =
      ((compositionSwap.trans compositionLift.{u}).cechCohomologyIso
        (X := TopCat.of disconnectedBase) (Y := TopCat.of (ULift.{u + 1} disconnectedBase))
        (A := ModuleCat.{u + 1} ℂ) 0).hom.app compositionSheaf.{u}.obj := by
  have h := congrArg (fun e ↦ e.hom.app compositionSheaf.{u}.obj)
    (Homeomorph.cechCohomologyIso_trans (X := TopCat.of disconnectedBase)
      (Y := TopCat.of disconnectedBase) (Z := TopCat.of (ULift.{u + 1} disconnectedBase))
      (A := ModuleCat.{u + 1} ℂ) compositionSwap compositionLift.{u} 0)
  have hcomponent := Functor.whiskeringLeft_transport_comp_hom_app
    compositionLift.{u}.opensCongr.equivalence.inverse.op
    compositionSwap.opensCongr.equivalence.inverse.op
    (compositionSwap.trans compositionLift.{u}).opensCongr.equivalence.inverse.op
    (opensCongr_inverse_op_trans compositionSwap compositionLift.{u}).symm
    (compositionSwap.cechCohomologyIso (X := TopCat.of disconnectedBase)
      (Y := TopCat.of disconnectedBase) (A := ModuleCat.{u + 1} ℂ) 0)
    (compositionLift.{u}.cechCohomologyIso (X := TopCat.of disconnectedBase)
      (Y := TopCat.of (ULift.{u + 1} disconnectedBase)) (A := ModuleCat.{u + 1} ℂ) 0)
    (Iso.refl _) compositionSheaf.{u}.obj
  simp only [Iso.trans_refl, Iso.refl_hom, NatTrans.id_app] at hcomponent
  rw [hcomponent] at h
  simpa only [compositionSequentialMap, compositionCoefficientIso, Iso.app_hom,
    Functor.whiskeringLeft_obj_obj, Functor.comp_obj, Category.comp_id]
    using h.symm

/-- Reading back the sequentially transported class returns the original nonzero value two. -/
theorem compositionSequential_read_two :
    compositionRead.{u}
      ((cechCohomologyZeroIso compositionSheaf.{u}).inv
        ((((compositionSwap.trans compositionLift.{u}).cechCohomologyIso
          (X := TopCat.of disconnectedBase) (Y := TopCat.of (ULift.{u + 1} disconnectedBase))
          (A := ModuleCat.{u + 1} ℂ) 0).inv.app compositionSheaf.{u}.obj)
            (compositionSequentialMap.{u} compositionClass.{u}))) = ULift.up 2 := by
  let e := ((compositionSwap.trans compositionLift.{u}).cechCohomologyIso
    (X := TopCat.of disconnectedBase) (Y := TopCat.of (ULift.{u + 1} disconnectedBase))
    (A := ModuleCat.{u + 1} ℂ) 0).app compositionSheaf.{u}.obj
  rw [compositionSequentialMap_eq]
  -- The local e is Iso.app of the composite transport, with these exact hom/inv components.
  change compositionRead.{u} ((cechCohomologyZeroIso compositionSheaf.{u}).inv
    (e.inv (e.hom compositionClass.{u}))) = ULift.up 2
  rw [e.hom_inv_id_apply, compositionClass, Iso.hom_inv_id_apply]
  exact compositionSection_read_two

/-- The actual sequentially transported class is nonzero, as detected by its value-two reading. -/
theorem compositionSequential_ne_zero :
    compositionSequentialMap.{u} compositionClass.{u} ≠ 0 := by
  intro hz
  have he := compositionSequential_read_two.{u}
  rw [hz, map_zero, map_zero, map_zero] at he
  exact two_ne_zero (congrArg ULift.down he).symm

end TauCeti.Examples.CechHomeomorph
