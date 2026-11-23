/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Cap.Unit
public import TauCeti.AlgebraicTopology.Cohomology.Cap.Relative
public import TauCeti.AlgebraicTopology.Cohomology.DegreeZero
public import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Topology.Instances.Discrete

/-!
# Nonzero and degenerate clients of cap coefficient naturality

Augmentation detects the negative and order-two cap outputs. For two discrete points modulo
the left point, an indicator lifted by the cohomology exact sequence caps the quotient right-point
class to the ambient right-point class; transporting its chain coefficients by twice identity
multiplies the output by two. The integral, modulo-two, modulo-four and zero-ring cases are checked.
The combined space/pair squares are applied to the right-point inclusion, and its negatively
transported value is detected modulo three. The coefficient square is checked on the empty space
in every degree, and an odd-degree chain example records the cap boundary sign.
-/

public noncomputable section

open CategoryTheory Limits MonoidalCategory HomologicalComplex TauCeti

universe u

namespace TauCeti

private theorem negUnit_action_square (R : Type u) [CommRing R] :
    ((-𝟙 (𝟙_ (ModuleCat.{u} R))) ▷ (𝟙_ (ModuleCat.{u} R))) ≫
        (λ_ (𝟙_ (ModuleCat.{u} R))).hom =
      ((𝟙_ (ModuleCat.{u} R)) ◁ 𝟙 (𝟙_ (ModuleCat.{u} R))) ≫
        (λ_ (𝟙_ (ModuleCat.{u} R))).hom ≫ (-𝟙 (𝟙_ (ModuleCat.{u} R))) := by
  simp

private theorem idUnit_diagonal_square (R : Type u) [CommRing R] :
    (𝟙 (𝟙_ (ModuleCat.{u} R))) ≫ (λ_ (𝟙_ (ModuleCat.{u} R))).inv =
      (λ_ (𝟙_ (ModuleCat.{u} R))).inv ≫
        ((𝟙 (𝟙_ (ModuleCat.{u} R))) ⊗ₘ (𝟙 (𝟙_ (ModuleCat.{u} R)))) := by
  rw [Category.id_comp, id_tensorHom_id, Category.comp_id]

end TauCeti

namespace TauCeti.CapCoefficientClients

/-- The topological point. -/
abbrev point : TopCat := TopCat.of PUnit

private theorem map_const_pointSection (k : Type u) [Ring k] (Y : TopCat.{u})
    (U : ModuleCat.{u} k) (y : Y) (r : U) :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) 0).obj U).map
        (TopCat.const (X := point) y) (singularHomology₀Section (X := point) U PUnit.unit r) =
      singularHomology₀Section (X := Y) U y r := by
  have hc := TopCat.const_apply (X := point) (Y := Y) y PUnit.unit
  have hn := singularHomology₀Section_naturality U (TopCat.const (X := point) y) PUnit.unit
  have ht := congrArg (fun z : Y ↦ singularHomology₀Section (X := Y) U z) hc
  exact (ConcreteCategory.comp_apply _ _ _).symm.trans
    (ConcreteCategory.congr_hom (hn.trans ht) r)

variable (R : Type u) [CommRing R]

/-- The normalized point class is nonzero over a nontrivial coefficient ring. -/
theorem pointClass_ne_zero [Nontrivial R] : (singularHomology₀Section (X :=
    CapCoefficientClients.point.{u}) (𝟙_ (ModuleCat R)) (PUnit.unit : CapCoefficientClients.point)
    (1 : R)) ≠ 0 := by
  exact singularHomology₀Section_apply_ne_zero R point (𝟙_ (ModuleCat R)) PUnit.unit
    (1 : R) one_ne_zero

/-- The relative pair is the point with its empty subspace. -/
abbrev emptyBoundaryPair : TopPair := TopPair.incl.obj point

/-- Change the value coefficient by the negative identity cochain map. -/
def negativeClass : point.singularCohomology (𝟙_ (ModuleCat.{u} R)) R
    (𝟙_ (ModuleCat.{u} R)) 0 :=
  homologyMap (((TopCat.toSSet.obj point).chainComplex
    (𝟙_ (ModuleCat.{u} R))).linearYonedaObjMap R (-𝟙 (𝟙_ (ModuleCat.{u} R)))) 0
      (point.singularCohomologyChainCoefficientMap R (𝟙_ (ModuleCat.{u} R))
        (𝟙 (𝟙_ (ModuleCat.{u} R))) 0 ((point.singularCohomologyZeroOne (k := R))))

/-- The full coefficient square computes the cap of the transported class as negative identity. -/
theorem cap_negativeClass :
    point.singularCap R (λ_ (𝟙_ (ModuleCat.{u} R))).inv (λ_ (𝟙_ (ModuleCat.{u} R))).hom
      0 0 0 rfl (negativeClass R) =
        -𝟙 (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) 0).obj
          (𝟙_ (ModuleCat.{u} R))).obj point) := by
  let U : ModuleCat.{u} R := 𝟙_ (ModuleCat.{u} R)
  have hh := TopCat.singularCap_coefficient_naturality point R
    (λ_ U).inv (λ_ U).inv (λ_ U).hom (λ_ U).hom
    (𝟙 U) (𝟙 U) (𝟙 U) (-𝟙 U) (-𝟙 U)
    (idUnit_diagonal_square R) (negUnit_action_square R) 0 0 0 rfl
        ((point.singularCohomologyZeroOne (k := R)))
  have hunit : point.singularCap R (λ_ U).inv (λ_ U).hom 0 0 0 rfl
      (point.singularCohomologyZeroOne (k := R)) = 𝟙 _ := by
    rw [TopCat.singularCohomologyZeroOne_def]
    exact TauCeti.singularCap_unit (X := point) R U 0
  rw [hunit] at hh
  rw [CategoryTheory.Functor.map_id, CategoryTheory.NatTrans.id_app,
    Category.id_comp, Category.id_comp] at hh
  have hcap : point.singularCap R (λ_ U).inv (λ_ U).hom 0 0 0 rfl (negativeClass R) =
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) 0).map (-𝟙 U)).app point := hh
  refine hcap.trans ?_
  rw [CategoryTheory.Functor.map_neg, CategoryTheory.Functor.map_id,
    CategoryTheory.NatTrans.app_neg]
  rw [CategoryTheory.NatTrans.id_app]

/-- The negative coefficient acts on the point class by negation. -/
theorem cap_negativeClass_pointClass :
    point.singularCap R (λ_ (𝟙_ (ModuleCat.{u} R))).inv (λ_ (𝟙_ (ModuleCat.{u} R))).hom
      0 0 0 rfl (negativeClass R) ((singularHomology₀Section (X :=
          CapCoefficientClients.point.{u}) (𝟙_ (ModuleCat R)) (PUnit.unit :
          CapCoefficientClients.point) (1 : R))) = -(singularHomology₀Section (X :=
          CapCoefficientClients.point.{u}) (𝟙_ (ModuleCat R)) (PUnit.unit :
          CapCoefficientClients.point) (1 : R)) := by
  rw [cap_negativeClass]
  simp

/-- The sign change is observable over the coefficients modulo three. -/
theorem negative_pointClass_ne_pointClass : -(singularHomology₀Section (X :=
    CapCoefficientClients.point.{0}) (𝟙_ (ModuleCat (ZMod 3))) (PUnit.unit :
    CapCoefficientClients.point) (1 : (ZMod 3))) ≠ (singularHomology₀Section (X :=
    CapCoefficientClients.point.{0}) (𝟙_ (ModuleCat (ZMod 3))) (PUnit.unit :
    CapCoefficientClients.point) (1 : (ZMod 3))) := by
  intro h
  have hh := congrArg (point.singularHomology₀ε (𝟙_ (ModuleCat (ZMod 3)))) h
  simp only [map_neg, singularHomology₀Section_singularHomology₀ε_apply] at hh
  exact (by decide : (-1 : ZMod 3) ≠ 1) hh

/-- On the point's singular chains, negative coefficient transport keeps the odd-degree minus. -/
theorem negative_point_boundary_sign
    (φ : ((TopCat.toSSet.obj point).chainComplex (𝟙_ (ModuleCat.{u} R))).X 1 ⟶
      𝟙_ (ModuleCat.{u} R)) :
    let X := TopCat.toSSet.obj point
    let U : ModuleCat.{u} R := 𝟙_ (ModuleCat.{u} R)
    let D := point.alexanderWhitneyDiagonal (λ_ U).inv
    let a := X.chainComplexPairing (λ_ U).hom
    let f := ((SSet.chainComplexFunctor (ModuleCat.{u} R)).map (𝟙 U)).app X
    let e := ((SSet.chainComplexFunctor (ModuleCat.{u} R)).map (-𝟙 U)).app X
    TauCeti.ChainComplex.capChain R D a 1 2 3 rfl (f.f 1 ≫ φ ≫ (-𝟙 U)) ≫
        (X.chainComplex U).d 2 1 =
      -((X.chainComplex U).d 3 2 ≫ f.f 2 ≫
          TauCeti.ChainComplex.capChain R D a 1 1 2 rfl φ ≫ e.f 1 -
        f.f 3 ≫ TauCeti.ChainComplex.capChain R D a 2 1 3 rfl
          ((X.chainComplex U).d 2 1 ≫ φ) ≫ e.f 1) := by
  dsimp only
  let U : ModuleCat.{u} R := 𝟙_ (ModuleCat.{u} R)
  have hD := TopCat.alexanderWhitneyDiagonal_coefficient_naturality point
    (λ_ U).inv (λ_ U).inv (𝟙 U) (𝟙 U) (𝟙 U) (idUnit_diagonal_square R)
  have ha :
      (NatTrans.mapHomologicalComplex ((tensoringLeft (ModuleCat.{u} R)).map (-𝟙 U)) _).app
          ((TopCat.toSSet.obj point).chainComplex U) ≫
        (TopCat.toSSet.obj point).chainComplexPairing (λ_ U).hom =
      ((tensorLeft U).mapHomologicalComplex _).map
          (((SSet.chainComplexFunctor (ModuleCat.{u} R)).map (𝟙 U)).app
            (TopCat.toSSet.obj point)) ≫
        (TopCat.toSSet.obj point).chainComplexPairing (λ_ U).hom ≫
          ((SSet.chainComplexFunctor (ModuleCat.{u} R)).map (-𝟙 U)).app
            (TopCat.toSSet.obj point) := by
    rw [SSet.whiskerRight_comp_chainComplexPairing,
      SSet.chainComplexPairing_comp_chainComplexFunctor_map_app,
      SSet.whiskerLeft_chainComplexFunctor_map_app_comp_chainComplexPairing]
    exact congrArg ((TopCat.toSSet.obj point).chainComplexPairing) (negUnit_action_square R)
  have hh := TauCeti.ChainComplex.capChain_coefficient_naturality_comp_d (k := R)
    (point.alexanderWhitneyDiagonal (λ_ U).inv)
    ((TopCat.toSSet.obj point).chainComplexPairing (λ_ U).hom)
    (point.alexanderWhitneyDiagonal (λ_ U).inv)
    ((TopCat.toSSet.obj point).chainComplexPairing (λ_ U).hom)
    _ _ _ (-𝟙 U) _ hD (fun j ↦ congrArg (fun g ↦ g.f j) ha) 1 1 2 rfl φ
  simpa only [pow_one, neg_one_zsmul] using hh

end TauCeti.CapCoefficientClients

namespace TauCeti.CapCoefficientProperPair

/-- The discrete two-point space. -/
abbrev twoPoints : TopCat := TopCat.of (Fin 2)

/-- The right point does not belong to the chosen left subspace. -/
theorem right_not_left : (1 : twoPoints) ∉ ({0} : Set twoPoints) := by decide

/-- The pair consisting of two points and its left singleton. -/
abbrev properPair : TopPair := TopPair.ofSubset (X := twoPoints) ({0} : Set twoPoints)

variable (k : Type) [CommRing k]

/-- The right-indicator function is constant on path components. -/
theorem indicator_path_invariant (x y : twoPoints) (h : Joined x y) :
    (if x = 1 then (1 : k) else 0) = (if y = 1 then 1 else 0) := by
  have he : x = y := by
    simpa using TotallyDisconnectedSpace.eq_of_continuous h.somePath h.somePath.continuous 0 1
  exact congrArg (fun z : twoPoints ↦ if z = 1 then (1 : k) else 0) he

/-- A cohomology class with value zero on the left and one on the right. -/
def indicatorClass : twoPoints.singularCohomology (𝟙_ (ModuleCat k)) k
    (𝟙_ (ModuleCat k)) 0 :=
  (exists_singularCohomologyZeroEval_eq (fun x : twoPoints ↦ if x = 1 then (1 : k) else 0)
    (indicator_path_invariant k)).choose

/-- The chosen class has exactly the specified point values. -/
@[simp]
theorem indicatorClass_eval (x : twoPoints) :
    singularCohomologyZeroEval x (indicatorClass k) = if x = 1 then (1 : k) else 0 :=
  (exists_singularCohomologyZeroEval_eq (fun x : twoPoints ↦ if x = 1 then (1 : k) else 0)
    (indicator_path_invariant k)).choose_spec x

/-- Restriction to the left singleton is zero. -/
theorem indicatorClass_restrict_left :
    TopCat.singularCohomologyMap properPair.map 0 (indicatorClass k) = 0 := by
  apply singularCohomologyZero_ext
  intro x
  have hn := singularCohomologyZeroEval_naturality
    (X := properPair.snd) (Y := twoPoints) (k := k) properPair.map x (indicatorClass k)
  have he : singularCohomologyZeroEval (properPair.map x) (indicatorClass k) =
      singularCohomologyZeroEval (0 : twoPoints) (indicatorClass k) :=
    congrArg (fun z : twoPoints ↦ singularCohomologyZeroEval z (indicatorClass k)) x.property
  have hzero : singularCohomologyZeroEval (0 : twoPoints) (indicatorClass k) = 0 :=
    by rw [indicatorClass_eval, ite_eq_right (by decide : (0 : twoPoints) ≠ 1)]
  exact hn.trans (he.trans (hzero.trans (map_zero _).symm))

/-- Exactness produces the relative indicator class on this proper pair. -/
theorem exists_relativeIndicatorClass :
    ∃ α : properPair.singularCohomology (𝟙_ (ModuleCat k)) k (𝟙_ (ModuleCat k)) 0,
      properPair.singularCohomologyπ (𝟙_ (ModuleCat k)) k (𝟙_ (ModuleCat k)) 0 α =
        indicatorClass k := by
  exact (ShortComplex.exact_iff_of_hasForget _).mp
    (properPair.singularCohomology_exact_space (𝟙_ (ModuleCat k)) k
      (𝟙_ (ModuleCat k)) 0) (indicatorClass k) (indicatorClass_restrict_left k)

/-- A relative lift of the right-indicator class. -/
def relativeIndicatorClass :
    properPair.singularCohomology (𝟙_ (ModuleCat k)) k (𝟙_ (ModuleCat k)) 0 :=
  (exists_relativeIndicatorClass k).choose

/-- Its image is the indicator, not an assumed relative normalization. -/
@[simp]
theorem relativeIndicatorClass_image :
    properPair.singularCohomologyπ (𝟙_ (ModuleCat k)) k (𝟙_ (ModuleCat k)) 0
      (relativeIndicatorClass k) = indicatorClass k := (exists_relativeIndicatorClass k).choose_spec

/-- Restriction of the indicator to the right point is the unit. -/
theorem indicatorClass_restrict_right :
    TopCat.singularCohomologyMap (TopCat.const (X := CapCoefficientClients.point) (1 : twoPoints))
        0 (indicatorClass k) =
      CapCoefficientClients.point.singularCohomologyZeroOne (k := k) := by
  apply singularCohomologyZero_ext
  intro x
  have hn := singularCohomologyZeroEval_naturality (TopCat.const (X :=
      CapCoefficientClients.point) (1 : twoPoints)) x (indicatorClass k)
  have hu : singularCohomologyZeroEval x
      (CapCoefficientClients.point.singularCohomologyZeroOne (k := k)) = 1 :=
    singularCohomologyZeroEval_singularCohomologyZeroOne x
  have hv : singularCohomologyZeroEval ((TopCat.const (X := CapCoefficientClients.point) (1 :
      twoPoints)) x) (indicatorClass k) = (1 : k) :=
    by rw [indicatorClass_eval, TopCat.const_apply, ite_eq_left rfl]
  exact hn.trans (hv.trans hu.symm)

/-- The class that will be the relative cap output is nonzero. -/
theorem rightPointClass_ne_zero [Nontrivial k] : (singularHomology₀Section (X := twoPoints) (𝟙_
    (ModuleCat k)) (1 : twoPoints) (1 : k)) ≠ 0 := by
  exact singularHomology₀Section_apply_ne_zero k twoPoints (𝟙_ (ModuleCat k))
    (1 : twoPoints) (1 : k) one_ne_zero

/-- Capping the ambient right-point generator with the indicator fixes that generator. -/
theorem cap_indicatorClass_rightPointClass :
    twoPoints.singularCap k (λ_ (𝟙_ (ModuleCat k))).inv
      (λ_ (𝟙_ (ModuleCat k))).hom 0 0 0 rfl (indicatorClass k) ((singularHomology₀Section (X :=
          twoPoints) (𝟙_ (ModuleCat k)) (1 : twoPoints) (1 : k))) =
        (singularHomology₀Section (X := twoPoints) (𝟙_ (ModuleCat k)) (1 : twoPoints) (1 : k)) := by
  have hh := TopCat.singularCap_naturality (TopCat.const (X := CapCoefficientClients.point) (1 :
      twoPoints)) k
    (λ_ (𝟙_ (ModuleCat k))).inv (λ_ (𝟙_ (ModuleCat k))).hom 0 0 0 rfl (indicatorClass k)
  rw [indicatorClass_restrict_right] at hh
  have hunit : CapCoefficientClients.point.singularCap k
      (λ_ (𝟙_ (ModuleCat k))).inv (λ_ (𝟙_ (ModuleCat k))).hom 0 0 0 rfl
        (CapCoefficientClients.point.singularCohomologyZeroOne (k := k)) = 𝟙 _ := by
    rw [TopCat.singularCohomologyZeroOne_def]
    exact TauCeti.singularCap_unit (X := CapCoefficientClients.point) k (𝟙_ (ModuleCat k)) 0
  rw [hunit] at hh
  have hpoint :
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat k) 0).obj
        (𝟙_ (ModuleCat k))).map (TopCat.const (X := CapCoefficientClients.point) (1 : twoPoints))
          (singularHomology₀Section (X := CapCoefficientClients.point.{0}) (𝟙_ (ModuleCat k))
            (PUnit.unit : CapCoefficientClients.point) (1 : k)) =
        singularHomology₀Section (X := twoPoints) (𝟙_ (ModuleCat k)) (1 : twoPoints) (1 : k) := by
    exact CapCoefficientClients.map_const_pointSection k twoPoints (𝟙_ (ModuleCat k))
      (1 : twoPoints) (1 : k)
  have he := ConcreteCategory.congr_hom hh
    (singularHomology₀Section (X := CapCoefficientClients.point.{0}) (𝟙_ (ModuleCat k))
      (PUnit.unit : CapCoefficientClients.point) (1 : k))
  simpa only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply, hpoint] using he.symm

/-- The relative right-point generator. -/
def relativeRightPointClass :
    properPair.singularHomology (C := ModuleCat k) (𝟙_ (ModuleCat k)) 0 :=
  properPair.singularHomologyπ (𝟙_ (ModuleCat k)) 0 ((singularHomology₀Section (X := twoPoints)
      (𝟙_ (ModuleCat k)) (1 : twoPoints) (1 : k)))

/-- The relative cap equals the ambient right-point class on this proper pair. -/
theorem cap_relativeIndicatorClass_relativeRightPointClass :
    properPair.singularCap k (λ_ (𝟙_ (ModuleCat k))).inv
      (λ_ (𝟙_ (ModuleCat k))).hom 0 0 0 rfl
        (relativeIndicatorClass k) (relativeRightPointClass k) = (singularHomology₀Section (X :=
            twoPoints) (𝟙_ (ModuleCat k)) (1 : twoPoints) (1 : k)) := by
  have hh := TopPair.singularCap_singularCohomologyπ properPair k
    (λ_ (𝟙_ (ModuleCat k))).inv (λ_ (𝟙_ (ModuleCat k))).hom
    0 0 0 rfl (relativeIndicatorClass k)
  rw [relativeIndicatorClass_image] at hh
  exact (ConcreteCategory.congr_hom hh ((singularHomology₀Section (X := twoPoints) (𝟙_ (ModuleCat
      k)) (1 : twoPoints) (1 : k)))).symm.trans
    (cap_indicatorClass_rightPointClass k)

/-- In particular the relative generator is not killed by the quotient modulo the left point. -/
theorem relativeRightPointClass_ne_zero [Nontrivial k] : relativeRightPointClass k ≠ 0 := by
  intro h
  have hh := cap_relativeIndicatorClass_relativeRightPointClass k
  rw [h, map_zero] at hh
  exact rightPointClass_ne_zero k hh.symm

/-- The relative indicator is itself nonzero, as witnessed by its cap output. -/
theorem relativeIndicatorClass_ne_zero [Nontrivial k] : relativeIndicatorClass k ≠ 0 := by
  intro h
  have hh := cap_relativeIndicatorClass_relativeRightPointClass k
  simp only [h, map_zero, ModuleCat.hom_zero, LinearMap.zero_apply] at hh
  exact rightPointClass_ne_zero k hh.symm

/-- Pull the relative indicator along twice the identity on its chain coefficients. -/
def doubledRelativeIndicatorClass :
    properPair.singularCohomology (𝟙_ (ModuleCat k)) k (𝟙_ (ModuleCat k)) 0 :=
  homologyMap ((TauCeti.ChainComplex.linearYonedaFunctor k (𝟙_ (ModuleCat k))).map
    (((SSetPair.chainComplexFunctor (ModuleCat k)).map
      (2 • 𝟙 (𝟙_ (ModuleCat k)))).app (TopPair.toSSetPair.obj properPair)).op ≫
    (properPair.singularChainComplex (𝟙_ (ModuleCat k))).linearYonedaObjMap
      k (𝟙 (𝟙_ (ModuleCat k)))) 0 (relativeIndicatorClass k)

private theorem relativeChainCoefficient_two :
    ((SSetPair.chainComplexFunctor (ModuleCat k)).map
      (2 • 𝟙 (𝟙_ (ModuleCat k)))).app (TopPair.toSSetPair.obj properPair) =
        2 • 𝟙 (properPair.singularChainComplex (𝟙_ (ModuleCat k))) := by
  apply (cancel_epi (properPair.singularChainComplexπ (𝟙_ (ModuleCat k)))).mp
  have hh := properPair.singularChainComplexπ_coefficient_naturality
    (2 • 𝟙 (𝟙_ (ModuleCat k)))
  rw [TauCeti.singularChainComplexFunctor_map_app] at hh
  have ha : ((SSet.chainComplexFunctor (ModuleCat k)).map
      (2 • 𝟙 (𝟙_ (ModuleCat k)))).app (TopCat.toSSet.obj properPair.fst) =
        2 • 𝟙 ((TopCat.toSSet.obj properPair.fst).chainComplex (𝟙_ (ModuleCat k))) := by
    simp only [two_smul, CategoryTheory.Functor.map_add, CategoryTheory.Functor.map_id,
      CategoryTheory.NatTrans.app_add, CategoryTheory.NatTrans.id_app]
  have hleft : (2 • 𝟙 ((TopCat.toSSet.obj properPair.fst).chainComplex
      (𝟙_ (ModuleCat k)))) ≫ properPair.singularChainComplexπ (𝟙_ (ModuleCat k)) =
        2 • properPair.singularChainComplexπ (𝟙_ (ModuleCat k)) :=
    (Preadditive.nsmul_comp _ _ 2).trans
      (congrArg (fun z ↦ (2 : ℕ) • z) (Category.id_comp _))
  have hright : properPair.singularChainComplexπ (𝟙_ (ModuleCat k)) ≫
      (2 • 𝟙 (properPair.singularChainComplex (𝟙_ (ModuleCat k)))) =
        2 • properPair.singularChainComplexπ (𝟙_ (ModuleCat k)) :=
    (Preadditive.comp_nsmul _ _ 2).trans
      (congrArg (fun z ↦ (2 : ℕ) • z) (Category.comp_id _))
  have hcoeff := congrArg (· ≫ properPair.singularChainComplexπ (𝟙_ (ModuleCat k))) ha
  have hscalar := hleft.trans hright.symm
  -- The quotient and functor chain aliases obstruct rewriting; retain their typed naturality.
  exact hh.symm.trans hcoeff |>.trans hscalar

private theorem doubleUnitCoefficient_square :
    (2 • 𝟙 (𝟙_ (ModuleCat k))) ≫ (λ_ (𝟙_ (ModuleCat k))).inv =
      (λ_ (𝟙_ (ModuleCat k))).inv ≫
        ((2 • 𝟙 (𝟙_ (ModuleCat k))) ⊗ₘ 𝟙 (𝟙_ (ModuleCat k))) := by
  let U : ModuleCat k := 𝟙_ (ModuleCat k)
  have ht : ((2 • 𝟙 U) ⊗ₘ 𝟙 U) = 2 • 𝟙 (U ⊗ U) := by
    rw [two_smul, MonoidalPreadditive.add_tensor]
    simpa only [two_smul] using congrArg (fun z ↦ z + z) (id_tensorHom_id U U)
  calc
    _ = 2 • (λ_ U).inv := by rw [Preadditive.nsmul_comp, Category.id_comp]
    _ = (λ_ U).inv ≫ (2 • 𝟙 (U ⊗ U)) := by
      rw [Preadditive.comp_nsmul, Category.comp_id]
    _ = _ := congrArg ((λ_ U).inv ≫ ·) ht.symm

/-- The new relative coefficient square detects twice the right-point generator. -/
theorem cap_doubledRelativeIndicatorClass_relativeRightPointClass :
    properPair.singularCap k (λ_ (𝟙_ (ModuleCat k))).inv
      (λ_ (𝟙_ (ModuleCat k))).hom 0 0 0 rfl
        (doubledRelativeIndicatorClass k) (relativeRightPointClass k) =
          2 • (singularHomology₀Section (X := twoPoints) (𝟙_ (ModuleCat k)) (1 : twoPoints) (1 :
              k)) := by
  let U : ModuleCat k := 𝟙_ (ModuleCat k)
  have hμ : (𝟙 U ▷ U) ≫ (λ_ U).hom = (U ◁ 𝟙 U) ≫ (λ_ U).hom ≫ 𝟙 U := by simp
  have hh := TopPair.singularCap_coefficient_naturality properPair k
    (λ_ U).inv (λ_ U).inv (λ_ U).hom (λ_ U).hom
    (2 • 𝟙 U) (𝟙 U) (2 • 𝟙 U) (𝟙 U) (𝟙 U)
    (doubleUnitCoefficient_square k) hμ
    0 0 0 rfl (relativeIndicatorClass k)
  have hcap : properPair.singularCap k (λ_ U).inv (λ_ U).hom 0 0 0 rfl
      (doubledRelativeIndicatorClass k) =
        homologyMap (((SSetPair.chainComplexFunctor (ModuleCat k)).map
          (2 • 𝟙 U)).app (TopPair.toSSetPair.obj properPair)) 0 ≫
            properPair.singularCap k (λ_ U).inv (λ_ U).hom 0 0 0 rfl
              (relativeIndicatorClass k) ≫
                ((AlgebraicTopology.singularHomologyFunctor (ModuleCat k) 0).map
                  (𝟙 U)).app properPair.fst := hh
  have hm : homologyMap (2 • 𝟙 (properPair.singularChainComplex U)) 0 =
      2 • 𝟙 (properPair.singularHomology (C := ModuleCat k) U 0) := by
    simp only [two_smul, HomologicalComplex.homologyMap_add, HomologicalComplex.homologyMap_id]
  have hc : properPair.singularCap k (λ_ U).inv (λ_ U).hom 0 0 0 rfl
      (doubledRelativeIndicatorClass k) =
        2 • properPair.singularCap k (λ_ U).inv (λ_ U).hom 0 0 0 rfl
          (relativeIndicatorClass k) := hcap.trans (by
    rw [relativeChainCoefficient_two, hm, CategoryTheory.Functor.map_id,
      CategoryTheory.NatTrans.id_app, Category.comp_id,
      Preadditive.nsmul_comp, Category.id_comp])
  exact (ConcreteCategory.congr_hom hc (relativeRightPointClass k)).trans
    (congrArg (fun z ↦ (2 : ℕ) • z) (cap_relativeIndicatorClass_relativeRightPointClass k))

/-- The augmentation observes the factor two, so this is not merely an identity test. -/
theorem augmentation_cap_doubledRelativeIndicatorClass :
    twoPoints.singularHomology₀ε (𝟙_ (ModuleCat k))
      (properPair.singularCap k (λ_ (𝟙_ (ModuleCat k))).inv
        (λ_ (𝟙_ (ModuleCat k))).hom 0 0 0 rfl
          (doubledRelativeIndicatorClass k) (relativeRightPointClass k)) = (2 : k) := by
  rw [cap_doubledRelativeIndicatorClass_relativeRightPointClass]
  exact (map_nsmul (twoPoints.singularHomology₀ε (𝟙_ (ModuleCat k))).hom
    2 (singularHomology₀Section (X := twoPoints) (𝟙_ (ModuleCat k)) (1 : twoPoints)
      (1 : k))).trans (by rw [singularHomology₀Section_singularHomology₀ε_apply]; simp)

/-- The doubled relative cap value with the coefficient action selected by `k`. -/
def doubledRelativeCapValue :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat k) 0).obj
      (𝟙_ (ModuleCat k))).obj twoPoints :=
  properPair.singularCap k (λ_ (𝟙_ (ModuleCat k))).inv
    (λ_ (𝟙_ (ModuleCat k))).hom 0 0 0 rfl
      (doubledRelativeIndicatorClass k) (relativeRightPointClass k)

/-- Over the integers, coefficient doubling produces a nonzero cap output. -/
theorem integral_doubled_cap_ne_zero : doubledRelativeCapValue ℤ ≠ 0 := by
  intro h
  have hh := congrArg (twoPoints.singularHomology₀ε (𝟙_ (ModuleCat ℤ))) h
  have he : twoPoints.singularHomology₀ε (𝟙_ (ModuleCat ℤ))
      (doubledRelativeCapValue ℤ) = (2 : ℤ) :=
    augmentation_cap_doubledRelativeIndicatorClass ℤ
  exact (by decide : (2 : ℤ) ≠ 0) (he.symm.trans (hh.trans (map_zero _)))

/-- In characteristic two, the transported proper-pair cap vanishes. -/
theorem mod_two_doubled_cap_eq_zero : doubledRelativeCapValue (ZMod 2) = 0 := by
  have hv : doubledRelativeCapValue (ZMod 2) =
      (2 : ℕ) • singularHomology₀Section (X := twoPoints) (𝟙_ (ModuleCat (ZMod 2)))
        (1 : twoPoints) (1 : ZMod 2) := by
    exact cap_doubledRelativeIndicatorClass_relativeRightPointClass (ZMod 2)
  rw [hv, ← Nat.cast_smul_eq_nsmul (ZMod 2)]
  simp [show (2 : ZMod 2) = 0 from by decide]

/-- Modulo four, the same nonidentity coefficient transport has nonzero output. -/
theorem mod_four_doubled_cap_ne_zero : doubledRelativeCapValue (ZMod 4) ≠ 0 := by
  intro h
  have hh := congrArg (twoPoints.singularHomology₀ε (𝟙_ (ModuleCat (ZMod 4)))) h
  have he : twoPoints.singularHomology₀ε (𝟙_ (ModuleCat (ZMod 4)))
      (doubledRelativeCapValue (ZMod 4)) = (2 : ZMod 4) :=
    augmentation_cap_doubledRelativeIndicatorClass (ZMod 4)
  exact (by decide : (2 : ZMod 4) ≠ 0) (he.symm.trans (hh.trans (map_zero _)))

/-- Its modulo-four output is killed by another multiplication by two. -/
theorem two_smul_mod_four_doubled_cap :
    (2 : ZMod 4) • doubledRelativeCapValue (ZMod 4) = 0 := by
  have hv : doubledRelativeCapValue (ZMod 4) =
      (2 : ℕ) • singularHomology₀Section (X := twoPoints) (𝟙_ (ModuleCat (ZMod 4)))
        (1 : twoPoints) (1 : ZMod 4) := by
    exact cap_doubledRelativeIndicatorClass_relativeRightPointClass (ZMod 4)
  rw [hv, ← Nat.cast_smul_eq_nsmul (ZMod 4), smul_smul]
  simp [show (2 : ZMod 4) * 2 = 0 from by decide]

/-- The same proper-pair expression imposes no nontriviality assumption on coefficients. -/
theorem zero_ring_doubled_cap_eq_zero : doubledRelativeCapValue (ZMod 1) = 0 := by
  have hv : doubledRelativeCapValue (ZMod 1) =
      (2 : ℕ) • singularHomology₀Section (X := twoPoints) (𝟙_ (ModuleCat (ZMod 1)))
        (1 : twoPoints) (1 : ZMod 1) := by
    exact cap_doubledRelativeIndicatorClass_relativeRightPointClass (ZMod 1)
  rw [hv, ← Nat.cast_smul_eq_nsmul (ZMod 1)]
  simp [show (2 : ZMod 1) = 0 from by decide]

/-- Inclusion of the right point, from the point with empty subspace into the proper pair. -/
def rightPointPairMap : CapCoefficientClients.emptyBoundaryPair ⟶ properPair :=
  TopPair.incl.map (TopCat.const (X := CapCoefficientClients.point) (1 : twoPoints)) ≫ TopPair.j
      properPair

/-- The ambient component is the right-point inclusion. -/
@[simp]
theorem rightPointPairMap_fst : TopPair.Hom.fst rightPointPairMap = (TopCat.const (X :=
    CapCoefficientClients.point) (1 : twoPoints)) := by
  exact (TopPair.Hom.fst_comp (TopPair.incl.map (TopCat.const (X := CapCoefficientClients.point)
      (1 : twoPoints)))
    (TopPair.j properPair)).trans (Category.comp_id _)

/-- The indicator after changing its value coefficient by negative identity. -/
def negativeIndicatorClass :
    twoPoints.singularCohomology (𝟙_ (ModuleCat k)) k (𝟙_ (ModuleCat k)) 0 :=
  homologyMap (((TopCat.toSSet.obj twoPoints).chainComplex
    (𝟙_ (ModuleCat k))).linearYonedaObjMap k (-𝟙 (𝟙_ (ModuleCat k)))) 0
      (twoPoints.singularCohomologyChainCoefficientMap k (𝟙_ (ModuleCat k))
        (𝟙 (𝟙_ (ModuleCat k))) 0 (indicatorClass k))

/-- The combined coefficient/space square on the right-point inclusion and its indicator. -/
theorem negative_indicator_space_square :
    CapCoefficientClients.point.singularCap k (λ_ (𝟙_ (ModuleCat k))).inv
      (λ_ (𝟙_ (ModuleCat k))).hom 0 0 0 rfl
        (TopCat.singularCohomologyMap (TopCat.const (X := CapCoefficientClients.point) (1 :
            twoPoints)) 0
          (negativeIndicatorClass k)) ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat k) 0).obj
          (𝟙_ (ModuleCat k))).map (TopCat.const (X := CapCoefficientClients.point) (1 :
              twoPoints)) =
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat k) 0).obj
          (𝟙_ (ModuleCat k))).map (TopCat.const (X := CapCoefficientClients.point) (1 :
              twoPoints)) ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat k) 0).map
          (𝟙 (𝟙_ (ModuleCat k)))).app twoPoints ≫
        twoPoints.singularCap k (λ_ (𝟙_ (ModuleCat k))).inv
          (λ_ (𝟙_ (ModuleCat k))).hom 0 0 0 rfl (indicatorClass k) ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat k) 0).map
          (-𝟙 (𝟙_ (ModuleCat k)))).app twoPoints := by
  let U : ModuleCat k := 𝟙_ (ModuleCat k)
  exact TopCat.singularCap_coefficient_naturality_map (TopCat.const (X :=
      CapCoefficientClients.point) (1 : twoPoints)) k
    (λ_ U).inv (λ_ U).inv (λ_ U).hom (λ_ U).hom
    (𝟙 U) (𝟙 U) (𝟙 U) (-𝟙 U) (-𝟙 U) (idUnit_diagonal_square k)
    (negUnit_action_square k)
    0 0 0 rfl (indicatorClass k)

/-- The cap value after negative coefficient transport and the right-point inclusion. -/
def negativeIndicatorSpaceValue :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat k) 0).obj
      (𝟙_ (ModuleCat k))).obj twoPoints :=
  (CapCoefficientClients.point.singularCap k (λ_ (𝟙_ (ModuleCat k))).inv
    (λ_ (𝟙_ (ModuleCat k))).hom 0 0 0 rfl
      (TopCat.singularCohomologyMap (TopCat.const (X := CapCoefficientClients.point) (1 :
          twoPoints)) 0 (negativeIndicatorClass k)) ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat k) 0).obj
          (𝟙_ (ModuleCat k))).map (TopCat.const (X := CapCoefficientClients.point) (1 :
              twoPoints))) ((singularHomology₀Section (X := CapCoefficientClients.point.{0}) (𝟙_
              (ModuleCat k)) (PUnit.unit : CapCoefficientClients.point) (1 : k)))

/-- Evaluating the combined square gives the negative right-point generator. -/
theorem negativeIndicatorSpaceValue_eq : negativeIndicatorSpaceValue k =
    -(singularHomology₀Section (X := twoPoints) (𝟙_ (ModuleCat k)) (1 : twoPoints) (1 : k)) := by
  let U : ModuleCat k := 𝟙_ (ModuleCat k)
  have hs := negative_indicator_space_square k
  simp only [CategoryTheory.Functor.map_neg, CategoryTheory.Functor.map_id,
    CategoryTheory.NatTrans.app_neg, CategoryTheory.NatTrans.id_app, Category.id_comp] at hs
  have hpoint :
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat k) 0).obj
        (𝟙_ (ModuleCat k))).map (TopCat.const (X := CapCoefficientClients.point) (1 : twoPoints))
          (singularHomology₀Section (X := CapCoefficientClients.point.{0}) (𝟙_ (ModuleCat k))
            (PUnit.unit : CapCoefficientClients.point) (1 : k)) =
        singularHomology₀Section (X := twoPoints) (𝟙_ (ModuleCat k)) (1 : twoPoints) (1 : k) := by
    exact CapCoefficientClients.map_const_pointSection k twoPoints (𝟙_ (ModuleCat k))
      (1 : twoPoints) (1 : k)
  have hv := ConcreteCategory.congr_hom hs ((singularHomology₀Section (X :=
      CapCoefficientClients.point.{0}) (𝟙_ (ModuleCat k)) (PUnit.unit :
      CapCoefficientClients.point) (1 : k)))
  have heval : negativeIndicatorSpaceValue k =
      -(twoPoints.singularCap k (λ_ U).inv (λ_ U).hom 0 0 0 rfl
        (indicatorClass k) ((singularHomology₀Section (X := twoPoints) (𝟙_ (ModuleCat k)) (1 :
            twoPoints) (1 : k)))) := by
    simpa only [negativeIndicatorSpaceValue, ConcreteCategory.comp_apply, hpoint,
      ModuleCat.hom_neg, LinearMap.neg_apply, ModuleCat.hom_id, LinearMap.id_apply] using hv
  exact heval.trans (congrArg (- ·) (cap_indicatorClass_rightPointClass k))

/-- Augmentation detects the minus sign of the transported cap output. -/
theorem augmentation_negativeIndicatorSpaceValue :
    twoPoints.singularHomology₀ε (𝟙_ (ModuleCat k)) (negativeIndicatorSpaceValue k) = (-1 : k) := by
  rw [negativeIndicatorSpaceValue_eq]
  exact (map_neg (twoPoints.singularHomology₀ε (𝟙_ (ModuleCat k))).hom
    (singularHomology₀Section (X := twoPoints) (𝟙_ (ModuleCat k)) (1 : twoPoints)
      (1 : k))).trans (congrArg (- ·)
        (singularHomology₀Section_singularHomology₀ε_apply k twoPoints
          (𝟙_ (ModuleCat k)) (1 : twoPoints) (1 : k)))

/-- Modulo three this evaluated cap is nonzero, so its sign is observable. -/
theorem negativeIndicatorSpaceValue_mod_three_ne_zero :
    negativeIndicatorSpaceValue (ZMod 3) ≠ 0 := by
  intro h
  have hh := congrArg (twoPoints.singularHomology₀ε (𝟙_ (ModuleCat (ZMod 3)))) h
  exact (by decide : (-1 : ZMod 3) ≠ 0)
    ((augmentation_negativeIndicatorSpaceValue (ZMod 3)).symm.trans (hh.trans (map_zero _)))

/-- It differs from the positive generator even though the underlying point inclusion is fixed. -/
theorem negativeIndicatorSpaceValue_mod_three_ne_rightPointClass :
    negativeIndicatorSpaceValue (ZMod 3) ≠ (singularHomology₀Section (X := twoPoints) (𝟙_
        (ModuleCat (ZMod 3))) (1 : twoPoints) (1 : (ZMod 3))) := by
  intro h
  have hh := congrArg (twoPoints.singularHomology₀ε (𝟙_ (ModuleCat (ZMod 3)))) h
  have hε := singularHomology₀Section_singularHomology₀ε_apply (ZMod 3) twoPoints
    (𝟙_ (ModuleCat (ZMod 3))) (1 : twoPoints) (1 : ZMod 3)
  exact (by decide : (-1 : ZMod 3) ≠ 1)
    ((augmentation_negativeIndicatorSpaceValue (ZMod 3)).symm.trans (hh.trans hε))

/-- The same nonidentity value transport is compatible with the map of proper pairs. -/
theorem negative_indicator_pair_square :
    CapCoefficientClients.emptyBoundaryPair.singularCap k
      (λ_ (𝟙_ (ModuleCat k))).inv (λ_ (𝟙_ (ModuleCat k))).hom 0 0 0 rfl
        (TopPair.singularCohomologyMap rightPointPairMap 0
          (homologyMap ((TauCeti.ChainComplex.linearYonedaFunctor k
            (𝟙_ (ModuleCat k))).map (((SSetPair.chainComplexFunctor (ModuleCat k)).map
              (𝟙 (𝟙_ (ModuleCat k)))).app (TopPair.toSSetPair.obj properPair)).op ≫
                (properPair.singularChainComplex (𝟙_ (ModuleCat k))).linearYonedaObjMap
                  k (-𝟙 (𝟙_ (ModuleCat k)))) 0 (relativeIndicatorClass k))) ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat k) 0).obj
          (𝟙_ (ModuleCat k))).map (TopPair.Hom.fst rightPointPairMap) =
      TopPair.singularHomologyMap rightPointPairMap (𝟙_ (ModuleCat k)) 0 ≫
        homologyMap (((SSetPair.chainComplexFunctor (ModuleCat k)).map
          (𝟙 (𝟙_ (ModuleCat k)))).app (TopPair.toSSetPair.obj properPair)) 0 ≫
        properPair.singularCap k (λ_ (𝟙_ (ModuleCat k))).inv
          (λ_ (𝟙_ (ModuleCat k))).hom 0 0 0 rfl (relativeIndicatorClass k) ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat k) 0).map
          (-𝟙 (𝟙_ (ModuleCat k)))).app properPair.fst := by
  let U : ModuleCat k := 𝟙_ (ModuleCat k)
  exact TopPair.singularCap_coefficient_naturality_map rightPointPairMap k
    (λ_ U).inv (λ_ U).inv (λ_ U).hom (λ_ U).hom
    (𝟙 U) (𝟙 U) (𝟙 U) (-𝟙 U) (-𝟙 U) (idUnit_diagonal_square k)
    (negUnit_action_square k)
    0 0 0 rfl (relativeIndicatorClass k)

end TauCeti.CapCoefficientProperPair

namespace TauCeti.CapCoefficientEdges

/-- The empty topological space. -/
abbrev emptySpace : TopCat := TopCat.of PEmpty

variable (R : Type u) [CommRing R]

/-- The coefficient square also elaborates on the literal empty space, in every degree. -/
theorem coefficient_square_empty (p q n : ℕ) (h : p + q = n)
    (α : emptySpace.singularCohomology (𝟙_ (ModuleCat.{u} R)) R
      (𝟙_ (ModuleCat.{u} R)) p) :
    emptySpace.singularCap R (λ_ (𝟙_ (ModuleCat.{u} R))).inv
      (λ_ (𝟙_ (ModuleCat.{u} R))).hom p q n h
        (homologyMap (((TopCat.toSSet.obj emptySpace).chainComplex
          (𝟙_ (ModuleCat.{u} R))).linearYonedaObjMap R (-𝟙 (𝟙_ (ModuleCat.{u} R)))) p
            (emptySpace.singularCohomologyChainCoefficientMap R (𝟙_ (ModuleCat.{u} R))
              (𝟙 (𝟙_ (ModuleCat.{u} R))) p α)) =
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) n).map
          (𝟙 (𝟙_ (ModuleCat.{u} R)))).app emptySpace ≫
        emptySpace.singularCap R (λ_ (𝟙_ (ModuleCat.{u} R))).inv
          (λ_ (𝟙_ (ModuleCat.{u} R))).hom p q n h α ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).map
          (-𝟙 (𝟙_ (ModuleCat.{u} R)))).app emptySpace := by
  let U : ModuleCat.{u} R := 𝟙_ (ModuleCat.{u} R)
  exact TopCat.singularCap_coefficient_naturality emptySpace R
    (λ_ U).inv (λ_ U).inv (λ_ U).hom (λ_ U).hom
    (𝟙 U) (𝟙 U) (𝟙 U) (-𝟙 U) (-𝟙 U) (idUnit_diagonal_square R)
    (negUnit_action_square R) p q n h α

end TauCeti.CapCoefficientEdges
