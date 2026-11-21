/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Monoidal
public import TauCeti.Topology.VectorBundle.FiniteRank.Dual
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# Hom bundles and closed monoidal structure for finite-rank bundle cores

For two point-indexed cores `A` and `D` of ranks `m` and `n`, `FiniteRankBundleCore.hom A D` is the
core of rank `m * n` whose chart at `i` is `A.core.baseSet i ∩ D.core.baseSet i` and whose
transition from chart `i` to chart `j` is operator conjugation
`ContinuousLinearMap.homCoordConj (A.core.coordChange j i x) (D.core.coordChange i j x)` in the
column coordinates of `ContinuousLinearEquiv.finProdCLM`.

Without assuming completeness of the scalar field:

* `homMap` acts contravariantly in the source and covariantly in the target, preserves
  isomorphisms, and gives the additive covariant functor `homRightFunctor`;
* `homEv` and `homCurry` exhibit `homRightFunctor A` as right adjoint to `tensorLeft A`, making
  `FiniteRankBundleCore 𝕜 B` a `MonoidalClosed` category whose internal Hom `(ihom A).obj D` is
  definitionally `hom A D` and whose precomposition `(MonoidalClosed.pre f).app D` is
  `homMap f (𝟙 D)`, and `homEv` is dinatural (`whiskerLeft_homMap_homEv`);
* `homRightFunctor A` and `MonoidalClosed.internalHom.flip.obj D` are additive, so internal Hom
  distributes over Whitney sums in both variables, naturally in all arguments
  (`homWhitneySumRightIso`, `homWhitneySumLeftIso`);
* `homTotalSpaceHomeomorph` identifies the reconstructed total space of `hom A D` with Mathlib's
  Hom bundle `TotalSpace ((Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜)) (fun x ↦ A.core.Fiber x →L[𝕜]
  D.core.Fiber x)` over the identity of the base, via `homFiberEquiv` on every fibre, naturally in
  both arguments (`homTotalSpaceHomeomorph_naturality`);
* pullback along a continuous base map commutes strictly with `hom`, `homMap`, evaluation, and
  coevaluation (`pullback_hom`, `pullbackMap_homMap`, `pullbackMap_homEv`,
  `pullbackMap_ihom_coev_app`).

When `𝕜` is complete, so `FiniteRankBundleCore.dual` is available, `A.dual ⊗ D` and `hom A D` have
identical coordinate data (`dual_tensor_eq_hom`), giving the natural isomorphism
`dualTensorIsoHom : A.dual ⊗ D ≅ hom A D` with identity fibre maps, and
`homUnitIsoDual : hom A (𝟙_ _) ≅ A.dual` via the right Kronecker unitor.

For the Hom bundle and its identification with `E* ⊗ F` see Milnor–Stasheff,
*Characteristic Classes*, §3, and Atiyah, *K-Theory*, §1.2.
-/

public section

open Bundle CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite Set VectorBundleCore

namespace TauCeti.FiniteRankBundleCore

open ContinuousLinearEquiv ContinuousLinearMap

section

variable {𝕜 B : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]

/-! ### The Hom core and bifunctoriality -/

/-- The internal Hom of two point-indexed cores, with intersected charts and operator-conjugation
transitions `homCoordConj (A.core.coordChange j i x) (D.core.coordChange i j x)`. -/
-- Expose the rank projection so the dependent fibre model reduces to `Fin (A.rank * D.rank) → 𝕜`.
@[expose]
noncomputable def hom (A D : FiniteRankBundleCore 𝕜 B) : FiniteRankBundleCore 𝕜 B where
  rank := A.rank * D.rank
  core :=
    { baseSet := fun i ↦ A.core.baseSet i ∩ D.core.baseSet i
      isOpen_baseSet := fun i ↦ (A.core.isOpen_baseSet i).inter (D.core.isOpen_baseSet i)
      indexAt := id
      mem_baseSet_at := fun x ↦ by
        simpa only [mem_inter_iff, id_eq, A.indexAt_eq, D.indexAt_eq] using
          And.intro (A.core.mem_baseSet_at x) (D.core.mem_baseSet_at x)
      coordChange := fun i j x ↦
        (A.core.coordChange j i x).homCoordConj (D.core.coordChange i j x)
      coordChange_self := fun i x hx v ↦ by
        rw [A.core.coordChange_self_eq_id hx.1, D.core.coordChange_self_eq_id hx.2,
          id_homCoordConj_id, ContinuousLinearMap.id_apply]
      continuousOn_coordChange := fun i j ↦
        ((A.core.continuousOn_coordChange j i).mono
          fun _ (hx : _ ∈ (A.core.baseSet i ∩ D.core.baseSet i) ∩
            (A.core.baseSet j ∩ D.core.baseSet j)) ↦ ⟨hx.2.1, hx.1.1⟩).clm_homCoordConj
          ((D.core.continuousOn_coordChange i j).mono
            (inter_subset_inter inter_subset_right inter_subset_right))
      coordChange_comp := fun i j k x hx v ↦ by
        rw [← ContinuousLinearMap.comp_apply, homCoordConj_comp_homCoordConj,
          A.core.coordChange_linear_comp k j i x ⟨⟨hx.2.1, hx.1.2.1⟩, hx.1.1.1⟩,
          D.core.coordChange_linear_comp i j k x ⟨⟨hx.1.1.2, hx.1.2.2⟩, hx.2.2⟩] }
  indexAt_eq := fun _ ↦ rfl

@[simp] theorem rank_hom (A D : FiniteRankBundleCore 𝕜 B) :
    (hom A D).rank = A.rank * D.rank := (rfl)

@[simp] theorem localTriv_baseSet_hom (A D : FiniteRankBundleCore 𝕜 B) (i : B) :
    ((hom A D).core.localTriv i).baseSet = A.core.baseSet i ∩ D.core.baseSet i := (rfl)

@[simp] theorem coordChange_hom (A D : FiniteRankBundleCore 𝕜 B) (i j x : B) :
    (hom A D).core.coordChange i j x =
      (A.core.coordChange j i x).homCoordConj (D.core.coordChange i j x) := (rfl)

/-- The Hom core between two trivial cores is the trivial core of product rank. -/
@[simp] theorem hom_trivial (m n : ℕ) :
    hom (trivial 𝕜 B m) (trivial 𝕜 B n) = trivial 𝕜 B (m * n) := by
  dsimp only [hom, trivial]
  congr 2
  · funext
    exact Set.univ_inter _
  · funext
    exact id_homCoordConj_id

variable {A A' A'' D D' D'' C C' : FiniteRankBundleCore 𝕜 B}

/-- Action of a contravariant source map `f : A' ⟶ A` and a covariant target map `g : D ⟶ D'` on
Hom cores, given in charts by `homCoordConj`. -/
noncomputable def homMap (f : A' ⟶ A) (g : D ⟶ D') : hom A D ⟶ hom A' D' where
  operator i j :=
    ⟨fun x ↦ (f.operator j i ⟨x.val, x.property.2.1, x.property.1.1⟩).homCoordConj
        (g.operator i j ⟨x.val, x.property.1.2, x.property.2.2⟩),
      ((f.operator j i).continuous.comp (continuous_subtypeVal.subtype_mk _)).clm_homCoordConj
        ((g.operator i j).continuous.comp (continuous_subtypeVal.subtype_mk _))⟩
  compatible i i' j j' x hi hi' hj hj' v := by
    have h : ((A'.core.coordChange j' j x).homCoordConj (D'.core.coordChange j j' x)).comp
        ((f.operator j i ⟨x, hj.1, hi.1⟩).homCoordConj (g.operator i j ⟨x, hi.2, hj.2⟩)) =
        ((f.operator j' i' ⟨x, hj'.1, hi'.1⟩).homCoordConj
          (g.operator i' j' ⟨x, hi'.2, hj'.2⟩)).comp
        ((A.core.coordChange i' i x).homCoordConj (D.core.coordChange i i' x)) := by
      rw [homCoordConj_comp_homCoordConj, homCoordConj_comp_homCoordConj,
        ← f.coordChange_comp_operator j' j i' i x hj'.1 hj.1 hi'.1 hi.1,
        g.coordChange_comp_operator i i' j j' x hi.2 hi'.2 hj.2 hj'.2]
    exact DFunLike.congr_fun h v

theorem operator_homMap (f : A' ⟶ A) (g : D ⟶ D') (i j : B)
    (x : ↥((hom A D).core.baseSet i ∩ (hom A' D').core.baseSet j)) :
    (homMap f g).operator i j x =
      (f.operator j i ⟨x.val, x.property.2.1, x.property.1.1⟩).homCoordConj
        (g.operator i j ⟨x.val, x.property.1.2, x.property.2.2⟩) := (rfl)

/-- On every fibre, `homMap f g` conjugates operators by `f.fiberMap x` on the right and
`g.fiberMap x` on the left. -/
@[simp] theorem fiberMap_homMap (f : A' ⟶ A) (g : D ⟶ D') (x : B) :
    (homMap f g).fiberMap x = (f.fiberMap x).homCoordConj (g.fiberMap x) :=
  (CoordinateHom.fiberMap_def _ x).trans <|
    (operator_homMap f g x x ⟨x, (hom A D).mem_baseSet_self x,
      (hom A' D').mem_baseSet_self x⟩).trans <| by
        rw [operator_self, operator_self]

@[simp] theorem id_homMap_id (A D : FiniteRankBundleCore 𝕜 B) :
    homMap (𝟙 A) (𝟙 D) = 𝟙 (hom A D) :=
  hom_ext fun x ↦ by
    rw [fiberMap_homMap, fiberMap_id, fiberMap_id, fiberMap_id]
    exact id_homCoordConj_id

@[reassoc (attr := simp)] theorem homMap_comp_homMap (f : A' ⟶ A) (f' : A'' ⟶ A')
    (g : D ⟶ D') (g' : D' ⟶ D'') :
    homMap f g ≫ homMap f' g' = homMap (f' ≫ f) (g ≫ g') :=
  hom_ext fun x ↦ by
    rw [fiberMap_comp, fiberMap_homMap, fiberMap_homMap, fiberMap_homMap, fiberMap_comp,
      fiberMap_comp]
    exact homCoordConj_comp_homCoordConj _ _ _ _

@[simp] theorem add_homMap (f₁ f₂ : A' ⟶ A) (g : D ⟶ D') :
    homMap (f₁ + f₂) g = homMap f₁ g + homMap f₂ g :=
  hom_ext fun x ↦ by
    rw [fiberMap_add, fiberMap_homMap, fiberMap_homMap, fiberMap_homMap, fiberMap_add]
    exact add_homCoordConj _ _ _

@[simp] theorem homMap_add (f : A' ⟶ A) (g₁ g₂ : D ⟶ D') :
    homMap f (g₁ + g₂) = homMap f g₁ + homMap f g₂ :=
  hom_ext fun x ↦ by
    rw [fiberMap_add, fiberMap_homMap, fiberMap_homMap, fiberMap_homMap, fiberMap_add]
    exact homCoordConj_add _ _ _

@[simp] theorem zero_homMap (g : D ⟶ D') :
    homMap (0 : A' ⟶ A) g = 0 :=
  hom_ext fun x ↦ by
    rw [fiberMap_homMap, CoordinateHom.fiberMap_zero, CoordinateHom.fiberMap_zero]
    exact zero_homCoordConj _

@[simp] theorem homMap_zero (f : A' ⟶ A) :
    homMap f (0 : D ⟶ D') = 0 :=
  hom_ext fun x ↦ by
    rw [fiberMap_homMap, CoordinateHom.fiberMap_zero, CoordinateHom.fiberMap_zero]
    exact homCoordConj_zero _

@[simp] theorem neg_homMap (f : A' ⟶ A) (g : D ⟶ D') :
    homMap (-f) g = -homMap f g :=
  eq_neg_of_add_eq_zero_left <| by rw [← add_homMap, neg_add_cancel, zero_homMap]

@[simp] theorem homMap_neg (f : A' ⟶ A) (g : D ⟶ D') :
    homMap f (-g) = -homMap f g :=
  eq_neg_of_add_eq_zero_left <| by rw [← homMap_add, neg_add_cancel, homMap_zero]

/-- `homMap` preserves bundle isomorphisms in both arguments. -/
instance (f : A' ⟶ A) (g : D ⟶ D') [IsIso f] [IsIso g] : IsIso (homMap f g) :=
  ⟨homMap (inv f) (inv g), by simp, by simp⟩

/-- Covariant Hom functor `hom A -` for fixed source `A`. -/
-- Expose the object and morphism maps, which consumers read off as `hom` and `homMap`.
@[expose, simps]
noncomputable def homRightFunctor (A : FiniteRankBundleCore 𝕜 B) :
    FiniteRankBundleCore 𝕜 B ⥤ FiniteRankBundleCore 𝕜 B where
  obj D := hom A D
  map g := homMap (𝟙 A) g
  map_id D := id_homMap_id A D
  map_comp g g' := by rw [homMap_comp_homMap, Category.id_comp]

instance (A : FiniteRankBundleCore 𝕜 B) : (homRightFunctor A).Additive where
  map_add {_ _ g₁ g₂} := homMap_add (𝟙 A) g₁ g₂

/-! ### Tensor-Hom adjunction and closed monoidal structure -/

/-- Evaluation bundle morphism `A ⊗ hom A D ⟶ D`, given on every fibre by `kroneckerHomEv`. -/
noncomputable def homEv (A D : FiniteRankBundleCore 𝕜 B) : A ⊗ hom A D ⟶ D :=
  constHom (fun _ _ hx ↦ hx.2.2) (kroneckerHomEv 𝕜 A.rank D.rank) fun i j x hi hj ↦ by
    have hcomp : (A.core.coordChange j i x).comp (A.core.coordChange i j x) =
        ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜) :=
      (A.core.coordChange_linear_comp i j i x ⟨⟨hi.1, hj.1⟩, hi.1⟩).trans
        (A.core.coordChange_self_eq_id hi.1)
    exact kroneckerHomEv_comp_kronecker_homCoordConj hcomp (D.core.coordChange i j x)

@[simp] theorem fiberMap_homEv (A D : FiniteRankBundleCore 𝕜 B) (x : B) :
    (homEv A D).fiberMap x = kroneckerHomEv 𝕜 A.rank D.rank :=
  fiberMap_constHom _ _ _ x

/-- Dinaturality of `homEv`: precomposing in `hom A D` with `f : A' ⟶ A` and postcomposing with
`g : D ⟶ D'` agrees with applying `f` on the first tensor factor and `g` on the output. -/
@[reassoc]
theorem whiskerLeft_homMap_homEv (f : A' ⟶ A) (g : D ⟶ D') :
    A' ◁ homMap f g ≫ homEv A' D' = f ▷ hom A D ≫ homEv A D ≫ g :=
  hom_ext fun x ↦ by
    simp only [fiberMap_comp, fiberMap_whiskerLeft, fiberMap_whiskerRight, fiberMap_homMap,
      fiberMap_homEv]
    exact kroneckerHomEv_comp_id_kronecker_homCoordConj (f.fiberMap x) (g.fiberMap x)

private theorem continuous_homCurry_section (f : A ⊗ C ⟶ D) :
    Continuous fun x ↦ TotalSpace.mk' ((Fin C.rank → 𝕜) →L[𝕜] (Fin (hom A D).rank → 𝕜))
      (E := fun y ↦ C.core.Fiber y →L[𝕜] (hom A D).core.Fiber y) x
      (kroneckerCurry 𝕜 A.rank C.rank D.rank (f.fiberMap x)) := by
  refine continuous_iff_continuousAt.2 fun x₀ ↦ ?_
  rw [continuousAt_hom_bundle]
  let U : Set B := C.core.baseSet x₀ ∩ (A.core.baseSet x₀ ∩ D.core.baseSet x₀)
  have hU : U ∈ nhds x₀ :=
    ((C.core.isOpen_baseSet x₀).inter
      ((A.core.isOpen_baseSet x₀).inter (D.core.isOpen_baseSet x₀))).mem_nhds
      ⟨C.mem_baseSet_self x₀, A.mem_baseSet_self x₀, D.mem_baseSet_self x₀⟩
  have hc : Continuous fun y : ↥U ↦
      kroneckerCurry 𝕜 A.rank C.rank D.rank
        (f.operator x₀ x₀ ⟨y.val, ⟨y.property.2.1, y.property.1⟩, y.property.2.2⟩) :=
    (kroneckerCurry 𝕜 A.rank C.rank D.rank).continuous.comp
      ((f.operator x₀ x₀).continuous.comp
        (Continuous.subtype_mk continuous_subtypeVal fun y : ↥U ↦ ⟨⟨y.property.2.1, y.property.1⟩,
            y.property.2.2⟩))
  refine ⟨continuousAt_id, ContinuousOn.continuousAt (s := U) ?_ hU⟩
  rw [continuousOn_iff_continuous_domRestrict]
  refine hc.congr fun y ↦ ?_
  dsimp only [Set.domRestrict_apply]
  have hfop := f.operator_eq x₀ x₀ ⟨y.val, ⟨y.property.2.1, y.property.1⟩, y.property.2.2⟩
  rw [inChartCoordinates_core] at hfop
  dsimp only [MonoidalCategoryStruct.tensorObj] at hfop
  rw [coordChange_tensor] at hfop
  have hin := C.core.inCoordinates_eq (hom A D).core
    (kroneckerCurry 𝕜 A.rank C.rank D.rank (f.fiberMap y.val))
    (by simpa only [C.indexAt_eq] using y.property.1)
    (by simpa only [(hom A D).indexAt_eq, VectorBundleCore.baseSet_at,
      localTriv_baseSet_hom] using y.property.2)
  simp only [C.indexAt_eq, (hom A D).indexAt_eq, coordChange_hom] at hin
  exact (congrArg (kroneckerCurry 𝕜 A.rank C.rank D.rank) hfop).trans <|
    (kroneckerCurry_comp_kronecker (A.core.coordChange x₀ y.val y.val)
      (C.core.coordChange x₀ y.val y.val) (D.core.coordChange y.val x₀ y.val)
          (f.fiberMap y.val)).trans
      hin.symm

/-- Currying of a bundle map `A ⊗ C ⟶ D` to a bundle map `C ⟶ hom A D`. -/
noncomputable def homCurry (f : A ⊗ C ⟶ D) : C ⟶ hom A D :=
  CoordinateHom.ofContinuous
    (fun x ↦ kroneckerCurry 𝕜 A.rank C.rank D.rank (f.fiberMap x))
    (continuous_homCurry_section f)

@[simp] theorem fiberMap_homCurry (f : A ⊗ C ⟶ D) (x : B) :
    (homCurry f).fiberMap x = kroneckerCurry 𝕜 A.rank C.rank D.rank (f.fiberMap x) :=
  congrFun (CoordinateHom.fiberMap_ofContinuous _ _) x

/-- Equivalence `(A ⊗ X ⟶ Y) ≃ (X ⟶ hom A Y)` given by `homCurry` and evaluation `homEv`. -/
noncomputable def homCurryEquiv (A X Y : FiniteRankBundleCore 𝕜 B) :
    (A ⊗ X ⟶ Y) ≃ (X ⟶ hom A Y) where
  toFun := homCurry
  invFun g := A ◁ g ≫ homEv A Y
  left_inv f := hom_ext fun x ↦ by
    rw [fiberMap_comp, fiberMap_homEv, fiberMap_whiskerLeft, fiberMap_homCurry]
    exact (kroneckerCurry_symm_apply_eq _).symm.trans
      ((kroneckerCurry 𝕜 A.rank X.rank Y.rank).symm_apply_apply (f.fiberMap x))
  right_inv g := hom_ext fun x ↦ by
    rw [fiberMap_homCurry, fiberMap_comp, fiberMap_homEv, fiberMap_whiskerLeft]
    exact (congrArg (kroneckerCurry 𝕜 A.rank X.rank Y.rank)
      (kroneckerCurry_symm_apply_eq _)).symm.trans
        ((kroneckerCurry 𝕜 A.rank X.rank Y.rank).apply_symm_apply (g.fiberMap x))

@[simp] theorem homCurryEquiv_apply (A X Y : FiniteRankBundleCore 𝕜 B) (f : A ⊗ X ⟶ Y) :
    homCurryEquiv A X Y f = homCurry f := (rfl)

@[simp] theorem homCurryEquiv_symm_apply (A X Y : FiniteRankBundleCore 𝕜 B) (g : X ⟶ hom A Y) :
    (homCurryEquiv A X Y).symm g = A ◁ g ≫ homEv A Y := (rfl)

/-- Adjunction `tensorLeft A ⊣ homRightFunctor A` for finite-rank bundle cores. -/
noncomputable def homAdjunction (A : FiniteRankBundleCore 𝕜 B) :
    tensorLeft A ⊣ homRightFunctor A :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun Y Z ↦ homCurryEquiv A Y Z
      homEquiv_naturality_left_symm := fun h g ↦
        MonoidalCategory.whiskerLeft_comp_assoc A h g (homEv A _)
      homEquiv_naturality_right := fun {Y Z Z'} f k ↦ hom_ext fun x ↦ by
        have h : (homCurry (f ≫ k : A ⊗ Y ⟶ Z')).fiberMap x =
            (homCurry (f : A ⊗ Y ⟶ Z) ≫ homMap (𝟙 A) k).fiberMap x := by
          rw [fiberMap_homCurry, fiberMap_comp, fiberMap_comp, fiberMap_homMap, fiberMap_homCurry,
            fiberMap_id]
          have h' := kroneckerCurry_comp_kronecker
            (ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜))
            (ContinuousLinearMap.id 𝕜 (Fin Y.rank → 𝕜)) (k.fiberMap x)
            (f.fiberMap x : (Fin (A.rank * Y.rank) → 𝕜) →L[𝕜] (Fin Z.rank → 𝕜))
          rw [id_kronecker_id, ContinuousLinearMap.comp_id] at h'
          exact h'
        exact h }

@[simp] theorem homAdjunction_homEquiv (A X Y : FiniteRankBundleCore 𝕜 B) :
    (homAdjunction A).homEquiv X Y = homCurryEquiv A X Y := by
  rw [homAdjunction, Adjunction.mkOfHomEquiv_homEquiv]

@[simp] theorem homAdjunction_counit_app (A D : FiniteRankBundleCore 𝕜 B) :
    (homAdjunction A).counit.app D = homEv A D := by
  rw [← (homAdjunction A).homEquiv_symm_id D, homAdjunction_homEquiv]
  exact (homCurryEquiv_symm_apply A (hom A D) D (𝟙 (hom A D))).trans <| by
    rw [MonoidalCategory.whiskerLeft_id, Category.id_comp]

@[simp] theorem homAdjunction_unit_app (A X : FiniteRankBundleCore 𝕜 B) :
    (homAdjunction A).unit.app X = homCurry (𝟙 (A ⊗ X)) := by
  rw [← (homAdjunction A).homEquiv_id X, homAdjunction_homEquiv]
  exact homCurryEquiv_apply A X (A ⊗ X) (𝟙 (A ⊗ X))

noncomputable instance (A : FiniteRankBundleCore 𝕜 B) : Closed A where
  rightAdj := homRightFunctor A
  adj := homAdjunction A

noncomputable instance : MonoidalClosed (FiniteRankBundleCore 𝕜 B) where

theorem ihom_obj (A D : FiniteRankBundleCore 𝕜 B) :
    (ihom A).obj D = hom A D := (rfl)

theorem ihom_map (A : FiniteRankBundleCore 𝕜 B) (g : D ⟶ D') :
    (ihom A).map g = homMap (𝟙 A) g := (rfl)

theorem ihom_adjunction (A : FiniteRankBundleCore 𝕜 B) :
    ihom.adjunction A = homAdjunction A := (rfl)

theorem monoidalClosed_curry_eq (f : A ⊗ C ⟶ D) :
    MonoidalClosed.curry f = homCurry f :=
  (MonoidalClosed.homEquiv_apply_eq f).symm.trans <|
    (congrFun (congrArg DFunLike.coe (homAdjunction_homEquiv A C D)) f).trans
      (homCurryEquiv_apply A C D f)

theorem monoidalClosed_uncurry_eq (g : C ⟶ (ihom A).obj D) :
    MonoidalClosed.uncurry g = A ◁ g ≫ homEv A D :=
  (MonoidalClosed.homEquiv_symm_apply_eq g).symm.trans <|
    (congrFun (congrArg (fun e ↦ (e.symm : _ → _)) (homAdjunction_homEquiv A C D)) g).trans
      (homCurryEquiv_symm_apply A C D g)

theorem ihom_ev_app (A D : FiniteRankBundleCore 𝕜 B) :
    (ihom.ev A).app D = homEv A D :=
  (MonoidalClosed.uncurry_id_eq_ev A D).symm.trans <|
    (monoidalClosed_uncurry_eq (𝟙 ((ihom A).obj D))).trans <|
      (congrArg (· ≫ homEv A D) (MonoidalCategory.whiskerLeft_id A (hom A D))).trans
        (Category.id_comp (homEv A D))

theorem ihom_coev_app (A C : FiniteRankBundleCore 𝕜 B) :
    (ihom.coev A).app C = homCurry (𝟙 (A ⊗ C)) :=
  (MonoidalClosed.curry_id_eq_coev A C).symm.trans (monoidalClosed_curry_eq (𝟙 (A ⊗ C)))

/-- Precomposition in the monoidal closed structure agrees with `homMap f (𝟙 D)`. -/
theorem monoidalClosed_pre_app (f : A' ⟶ A) (D : FiniteRankBundleCore 𝕜 B) :
    (MonoidalClosed.pre f).app D = homMap f (𝟙 D) := by
  apply MonoidalClosed.uncurry_injective
  have h : f ▷ hom A D ≫ homEv A D = A' ◁ homMap f (𝟙 D) ≫ homEv A' D := hom_ext fun x ↦ by
    rw [fiberMap_comp, fiberMap_comp, fiberMap_homEv, fiberMap_homEv, fiberMap_whiskerRight,
      fiberMap_whiskerLeft, fiberMap_homMap, fiberMap_id]
    exact (ContinuousLinearMap.id_comp _).symm.trans
      (kroneckerHomEv_comp_id_kronecker_homCoordConj (f.fiberMap x)
        (ContinuousLinearMap.id 𝕜 (Fin D.rank → 𝕜))).symm
  refine (MonoidalClosed.uncurry_pre f D).trans ?_
  rw [ihom_ev_app]
  exact h.trans
    (monoidalClosed_uncurry_eq (homMap f (𝟙 D) : (ihom A).obj D ⟶ (ihom A').obj D)).symm

@[simp] theorem rank_ihom_obj (A D : FiniteRankBundleCore 𝕜 B) :
    ((ihom A).obj D).rank = A.rank * D.rank := (rfl)

@[simp] theorem fiberMap_ihom_map (A : FiniteRankBundleCore 𝕜 B) (g : D ⟶ D') (x : B) :
    ((ihom A).map g).fiberMap x =
      (ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜)).homCoordConj (g.fiberMap x) :=
  (congrArg (fun k ↦ k.fiberMap x) (ihom_map A g)).trans <|
    (fiberMap_homMap (𝟙 A) g x).trans
      (congrArg (fun s ↦ s.homCoordConj (g.fiberMap x)) (fiberMap_id A x))

@[simp] theorem fiberMap_ihom_ev_app (A D : FiniteRankBundleCore 𝕜 B) (x : B) :
    ((ihom.ev A).app D).fiberMap x = kroneckerHomEv 𝕜 A.rank D.rank := by
  rw [ihom_ev_app]
  exact fiberMap_homEv A D x

@[simp] theorem fiberMap_ihom_coev_app (A C : FiniteRankBundleCore 𝕜 B) (x : B) :
    ((ihom.coev A).app C).fiberMap x =
      kroneckerCurry 𝕜 A.rank C.rank (A.rank * C.rank)
        (ContinuousLinearMap.id 𝕜 (Fin (A.rank * C.rank) → 𝕜)) := by
  rw [ihom_coev_app]
  exact (fiberMap_homCurry (𝟙 (A ⊗ C)) x).trans
    (congrArg (kroneckerCurry 𝕜 A.rank C.rank (A.rank * C.rank)) (fiberMap_id (A ⊗ C) x))

@[simp] theorem fiberMap_monoidalClosed_curry (f : A ⊗ C ⟶ D) (x : B) :
    (MonoidalClosed.curry f).fiberMap x =
      kroneckerCurry 𝕜 A.rank C.rank D.rank (f.fiberMap x) := by
  rw [monoidalClosed_curry_eq]
  exact fiberMap_homCurry f x

@[simp] theorem fiberMap_monoidalClosed_uncurry (g : C ⟶ (ihom A).obj D) (x : B) :
    (MonoidalClosed.uncurry g).fiberMap x =
      (kroneckerHomEv 𝕜 A.rank D.rank).comp
        ((ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜)).kronecker (g.fiberMap x)) := by
  have h (g' : C ⟶ hom A D) : (A ◁ g' ≫ homEv A D).fiberMap x =
      (kroneckerHomEv 𝕜 A.rank D.rank).comp
        ((ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜)).kronecker (g'.fiberMap x)) :=
    (fiberMap_comp (A ◁ g') (homEv A D) x).trans
      (congrArg₂ ContinuousLinearMap.comp (fiberMap_homEv A D x) (fiberMap_whiskerLeft A g' x))
  rw [monoidalClosed_uncurry_eq]
  exact h g

@[simp] theorem fiberMap_monoidalClosed_pre_app (f : A' ⟶ A) (D : FiniteRankBundleCore 𝕜 B)
    (x : B) :
    ((MonoidalClosed.pre f).app D).fiberMap x =
      (f.fiberMap x).homCoordConj (ContinuousLinearMap.id 𝕜 (Fin D.rank → 𝕜)) := by
  rw [monoidalClosed_pre_app]
  exact (fiberMap_homMap f (𝟙 D) x).trans
    (congrArg (f.fiberMap x).homCoordConj (fiberMap_id D x))

/-- Read through `finProdCLM`, the fibre map of `MonoidalClosed.curry f` sends `(c, u)` to
`f.fiberMap x` applied to the pure tensor `u ⊗ c`. -/
theorem finProdCLM_fiberMap_monoidalClosed_curry_apply (f : A ⊗ C ⟶ D) (x : B)
    (c : Fin C.rank → 𝕜) (u : Fin A.rank → 𝕜) :
    finProdCLM 𝕜 A.rank D.rank ((MonoidalClosed.curry f).fiberMap x c) u =
      f.fiberMap x (fun k ↦ u (finProdFinEquiv.symm k).1 * c (finProdFinEquiv.symm k).2) := by
  rw [fiberMap_monoidalClosed_curry]
  exact finProdCLM_kroneckerCurry_apply (f.fiberMap x) c u

/-- Read through `finProdCLM`, the internal identity `MonoidalClosed.id A` scales the identity
operator on each fibre. -/
@[simp] theorem finProdCLM_fiberMap_monoidalClosed_id (A : FiniteRankBundleCore 𝕜 B) (x : B)
    (c : Fin 1 → 𝕜) :
    finProdCLM 𝕜 A.rank A.rank ((MonoidalClosed.id A).fiberMap x c) =
      c 0 • ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜) := by
  ext u j
  rw [MonoidalClosed.id_eq]
  refine (congrFun (finProdCLM_fiberMap_monoidalClosed_curry_apply (ρ_ A).hom x c u) j).trans ?_
  rw [fiberMap_rightUnitor_hom]
  exact (kroneckerRid_apply
    (fun k : Fin (A.rank * 1) ↦ u (finProdFinEquiv.symm k).1 * c (finProdFinEquiv.symm k).2)
      j).trans (by simp [mul_comm])

/-- Read through `finProdCLM`, internal composition `MonoidalClosed.comp A D C` composes operators
on pure-tensor coordinate vectors. -/
theorem finProdCLM_fiberMap_monoidalClosed_comp (A D C : FiniteRankBundleCore 𝕜 B) (x : B)
    (f : Fin (A.rank * D.rank) → 𝕜) (g : Fin (D.rank * C.rank) → 𝕜) (u : Fin A.rank → 𝕜) :
    finProdCLM 𝕜 A.rank C.rank (((MonoidalClosed.comp A D C).fiberMap x)
        (fun k ↦ f (finProdFinEquiv.symm k).1 * g (finProdFinEquiv.symm k).2)) u =
      finProdCLM 𝕜 D.rank C.rank g (finProdCLM 𝕜 A.rank D.rank f u) := by
  ext l
  have hcur : finProdCLM 𝕜 A.rank C.rank (((MonoidalClosed.comp A D C).fiberMap x)
        (fun k ↦ f (finProdFinEquiv.symm k).1 * g (finProdFinEquiv.symm k).2)) u =
      (MonoidalClosed.compTranspose A D C).fiberMap x
        (fun k : Fin (A.rank * ((A.rank * D.rank) * (D.rank * C.rank))) ↦
          u (finProdFinEquiv.symm k).1 *
            (f (finProdFinEquiv.symm (finProdFinEquiv.symm k).2).1 *
              g (finProdFinEquiv.symm (finProdFinEquiv.symm k).2).2)) := by
    rw [MonoidalClosed.comp_eq]
    exact finProdCLM_fiberMap_monoidalClosed_curry_apply
      (MonoidalClosed.compTranspose A D C) x
      (fun k ↦ f (finProdFinEquiv.symm k).1 * g (finProdFinEquiv.symm k).2) u
  have hct : (MonoidalClosed.compTranspose A D C).fiberMap x =
      ((kroneckerHomEv 𝕜 D.rank C.rank).comp
        ((kroneckerHomEv 𝕜 A.rank D.rank).kronecker
          (ContinuousLinearMap.id 𝕜 (Fin (D.rank * C.rank) → 𝕜)))).comp
        (kroneckerAssoc 𝕜 A.rank (A.rank * D.rank)
          (D.rank * C.rank)).symm.toContinuousLinearMap := by
    rw [MonoidalClosed.compTranspose_eq]
    exact (fiberMap_comp _ _ x).trans <|
      congrArg₂ ContinuousLinearMap.comp
        ((fiberMap_comp _ _ x).trans
          (congrArg₂ ContinuousLinearMap.comp (fiberMap_ihom_ev_app D C x)
            ((fiberMap_whiskerRight ((ihom.ev A).app D) ((ihom D).obj C) x).trans
              (congrArg (·.kronecker (ContinuousLinearMap.id 𝕜 (Fin (D.rank * C.rank) → 𝕜)))
                (fiberMap_ihom_ev_app A D x)))))
        (fiberMap_associator_inv A ((ihom A).obj D) ((ihom D).obj C) x)
  have hct_apply (z : Fin (A.rank * ((A.rank * D.rank) * (D.rank * C.rank))) → 𝕜) :
      (MonoidalClosed.compTranspose A D C).fiberMap x z =
        kroneckerHomEv 𝕜 D.rank C.rank
          (((kroneckerHomEv 𝕜 A.rank D.rank).kronecker
            (ContinuousLinearMap.id 𝕜 (Fin (D.rank * C.rank) → 𝕜)))
            ((kroneckerAssoc 𝕜 A.rank (A.rank * D.rank) (D.rank * C.rank)).symm z)) :=
    DFunLike.congr_fun hct z
  refine (congrFun (hcur.trans (hct_apply _)) l).trans ?_
  simp only [kroneckerHomEv_apply, kronecker_apply, ContinuousLinearMap.id_apply, finProdCLM_apply]
  simp_rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [kroneckerAssoc_symm_apply, Equiv.symm_apply_apply]
  ring

/-! ### Whitney-sum distributivity for internal Hom -/

section WhitneySum

instance (D : FiniteRankBundleCore 𝕜 B) :
    (MonoidalClosed.internalHom.flip.obj D).Additive where
  map_add {_ _ f₁ f₂} := by
    dsimp only [Functor.flip_obj_map]
    rw [MonoidalClosed.internalHom_map, MonoidalClosed.internalHom_map,
      MonoidalClosed.internalHom_map, monoidalClosed_pre_app, monoidalClosed_pre_app,
      monoidalClosed_pre_app, unop_add]
    exact add_homMap f₁.unop f₂.unop (𝟙 D)

/-- The image of `whitneyBicone D₁ D₂` under the additive functor `homRightFunctor A`. -/
-- Expose the point projection so the types of the four legs reduce to the Hom Whitney sum.
@[expose]
noncomputable def homWhitneyRightBicone (A D₁ D₂ : FiniteRankBundleCore 𝕜 B) :
    BinaryBicone (hom A D₁) (hom A D₂) :=
  (homRightFunctor A).mapBinaryBicone (whitneyBicone D₁ D₂)

@[simp] theorem homWhitneyRightBicone_pt (A D₁ D₂ : FiniteRankBundleCore 𝕜 B) :
    (homWhitneyRightBicone A D₁ D₂).pt = hom A (whitneySum D₁ D₂) := (rfl)

@[simp] theorem homWhitneyRightBicone_fst (A D₁ D₂ : FiniteRankBundleCore 𝕜 B) :
    (homWhitneyRightBicone A D₁ D₂).fst = homMap (𝟙 A) (whitneyFst D₁ D₂) := (rfl)

@[simp] theorem homWhitneyRightBicone_snd (A D₁ D₂ : FiniteRankBundleCore 𝕜 B) :
    (homWhitneyRightBicone A D₁ D₂).snd = homMap (𝟙 A) (whitneySnd D₁ D₂) := (rfl)

@[simp] theorem homWhitneyRightBicone_inl (A D₁ D₂ : FiniteRankBundleCore 𝕜 B) :
    (homWhitneyRightBicone A D₁ D₂).inl = homMap (𝟙 A) (whitneyInl D₁ D₂) := (rfl)

@[simp] theorem homWhitneyRightBicone_inr (A D₁ D₂ : FiniteRankBundleCore 𝕜 B) :
    (homWhitneyRightBicone A D₁ D₂).inr = homMap (𝟙 A) (whitneyInr D₁ D₂) := (rfl)

/-- `homWhitneyRightBicone` is a binary bilimit because `homRightFunctor A` is additive. -/
noncomputable def homWhitneyRightBiconeIsBilimit (A D₁ D₂ : FiniteRankBundleCore 𝕜 B) :
    (homWhitneyRightBicone A D₁ D₂).IsBilimit :=
  have := preservesBinaryBiproduct_of_preservesBiproduct (homRightFunctor A) D₁ D₂
  isBinaryBilimitOfPreserves (homRightFunctor A) (whitneyBiconeIsBilimit D₁ D₂)

/-- Hom into a Whitney sum is isomorphic to the Whitney sum of the Homs. -/
noncomputable def homWhitneySumRightIso (A D₁ D₂ : FiniteRankBundleCore 𝕜 B) :
    hom A (whitneySum D₁ D₂) ≅ whitneySum (hom A D₁) (hom A D₂) :=
  (homWhitneyRightBiconeIsBilimit A D₁ D₂).isLimit.conePointUniqueUpToIso
    (whitneyBiconeIsBilimit (hom A D₁) (hom A D₂)).isLimit

@[reassoc (attr := simp)]
theorem homWhitneySumRightIso_hom_whitneyFst (A D₁ D₂ : FiniteRankBundleCore 𝕜 B) :
    (homWhitneySumRightIso A D₁ D₂).hom ≫ whitneyFst (hom A D₁) (hom A D₂) =
      homMap (𝟙 A) (whitneyFst D₁ D₂) :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ (Discrete.mk WalkingPair.left)

@[reassoc (attr := simp)]
theorem homWhitneySumRightIso_hom_whitneySnd (A D₁ D₂ : FiniteRankBundleCore 𝕜 B) :
    (homWhitneySumRightIso A D₁ D₂).hom ≫ whitneySnd (hom A D₁) (hom A D₂) =
      homMap (𝟙 A) (whitneySnd D₁ D₂) :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ (Discrete.mk WalkingPair.right)

/-- The image of `(whitneyBicone A₁ A₂).op` under the additive contravariant internal Hom functor
`MonoidalClosed.internalHom.flip.obj D`. -/
-- Expose the point projection so the types of the four legs reduce to the Hom Whitney sum.
@[expose]
noncomputable def homWhitneyLeftBicone (A₁ A₂ D : FiniteRankBundleCore 𝕜 B) :
    BinaryBicone (hom A₁ D) (hom A₂ D) :=
  (MonoidalClosed.internalHom.flip.obj D).mapBinaryBicone (whitneyBicone A₁ A₂).op

@[simp] theorem homWhitneyLeftBicone_pt (A₁ A₂ D : FiniteRankBundleCore 𝕜 B) :
    (homWhitneyLeftBicone A₁ A₂ D).pt = hom (whitneySum A₁ A₂) D := (rfl)

@[simp] theorem homWhitneyLeftBicone_fst (A₁ A₂ D : FiniteRankBundleCore 𝕜 B) :
    (homWhitneyLeftBicone A₁ A₂ D).fst = homMap (whitneyInl A₁ A₂) (𝟙 D) := by
  dsimp only [homWhitneyLeftBicone, Functor.mapBinaryBicone_fst, BinaryBicone.op_fst,
    whitneyBicone_inl, Functor.flip_obj_map, MonoidalClosed.internalHom_map]
  exact monoidalClosed_pre_app (whitneyInl A₁ A₂) D

@[simp] theorem homWhitneyLeftBicone_snd (A₁ A₂ D : FiniteRankBundleCore 𝕜 B) :
    (homWhitneyLeftBicone A₁ A₂ D).snd = homMap (whitneyInr A₁ A₂) (𝟙 D) := by
  dsimp only [homWhitneyLeftBicone, Functor.mapBinaryBicone_snd, BinaryBicone.op_snd,
    whitneyBicone_inr, Functor.flip_obj_map, MonoidalClosed.internalHom_map]
  exact monoidalClosed_pre_app (whitneyInr A₁ A₂) D

@[simp] theorem homWhitneyLeftBicone_inl (A₁ A₂ D : FiniteRankBundleCore 𝕜 B) :
    (homWhitneyLeftBicone A₁ A₂ D).inl = homMap (whitneyFst A₁ A₂) (𝟙 D) := by
  dsimp only [homWhitneyLeftBicone, Functor.mapBinaryBicone_inl, BinaryBicone.op_inl,
    whitneyBicone_fst, Functor.flip_obj_map, MonoidalClosed.internalHom_map]
  exact monoidalClosed_pre_app (whitneyFst A₁ A₂) D

@[simp] theorem homWhitneyLeftBicone_inr (A₁ A₂ D : FiniteRankBundleCore 𝕜 B) :
    (homWhitneyLeftBicone A₁ A₂ D).inr = homMap (whitneySnd A₁ A₂) (𝟙 D) := by
  dsimp only [homWhitneyLeftBicone, Functor.mapBinaryBicone_inr, BinaryBicone.op_inr,
    whitneyBicone_snd, Functor.flip_obj_map, MonoidalClosed.internalHom_map]
  exact monoidalClosed_pre_app (whitneySnd A₁ A₂) D

/-- `homWhitneyLeftBicone` is a binary bilimit because `MonoidalClosed.internalHom.flip.obj D` is
additive. -/
noncomputable def homWhitneyLeftBiconeIsBilimit (A₁ A₂ D : FiniteRankBundleCore 𝕜 B) :
    (homWhitneyLeftBicone A₁ A₂ D).IsBilimit :=
  have := preservesBinaryBiproduct_of_preservesBiproduct
    (MonoidalClosed.internalHom.flip.obj D) (op A₁) (op A₂)
  isBinaryBilimitOfPreserves (MonoidalClosed.internalHom.flip.obj D)
    (whitneyBiconeIsBilimit A₁ A₂).op

/-- Hom out of a Whitney sum is isomorphic to the Whitney sum of the Homs. -/
noncomputable def homWhitneySumLeftIso (A₁ A₂ D : FiniteRankBundleCore 𝕜 B) :
    hom (whitneySum A₁ A₂) D ≅ whitneySum (hom A₁ D) (hom A₂ D) :=
  (homWhitneyLeftBiconeIsBilimit A₁ A₂ D).isLimit.conePointUniqueUpToIso
    (whitneyBiconeIsBilimit (hom A₁ D) (hom A₂ D)).isLimit

@[reassoc (attr := simp)]
theorem homWhitneySumLeftIso_hom_whitneyFst (A₁ A₂ D : FiniteRankBundleCore 𝕜 B) :
    (homWhitneySumLeftIso A₁ A₂ D).hom ≫ whitneyFst (hom A₁ D) (hom A₂ D) =
      homMap (whitneyInl A₁ A₂) (𝟙 D) :=
  (IsLimit.conePointUniqueUpToIso_hom_comp _ _ (Discrete.mk WalkingPair.left)).trans
    (homWhitneyLeftBicone_fst A₁ A₂ D)

@[reassoc (attr := simp)]
theorem homWhitneySumLeftIso_hom_whitneySnd (A₁ A₂ D : FiniteRankBundleCore 𝕜 B) :
    (homWhitneySumLeftIso A₁ A₂ D).hom ≫ whitneySnd (hom A₁ D) (hom A₂ D) =
      homMap (whitneyInr A₁ A₂) (𝟙 D) :=
  (IsLimit.conePointUniqueUpToIso_hom_comp _ _ (Discrete.mk WalkingPair.right)).trans
    (homWhitneyLeftBicone_snd A₁ A₂ D)

/-- Naturality of `homWhitneySumRightIso` in the source and both target summands. -/
@[reassoc]
theorem homMap_whitneyMap_homWhitneySumRightIso_hom {D₁ D₂ D₁' D₂' : FiniteRankBundleCore 𝕜 B}
    (f : A' ⟶ A) (g₁ : D₁ ⟶ D₁') (g₂ : D₂ ⟶ D₂') :
    homMap f (whitneyMap g₁ g₂) ≫ (homWhitneySumRightIso A' D₁' D₂').hom =
      (homWhitneySumRightIso A D₁ D₂).hom ≫ whitneyMap (homMap f g₁) (homMap f g₂) :=
  whitneySum_hom_ext (by simp) (by simp)

/-- Naturality of `homWhitneySumLeftIso` in both source summands and the target. -/
@[reassoc]
theorem homMap_whitneyMap_homWhitneySumLeftIso_hom {A₁ A₂ A₁' A₂' : FiniteRankBundleCore 𝕜 B}
    (f₁ : A₁' ⟶ A₁) (f₂ : A₂' ⟶ A₂) (g : D ⟶ D') :
    homMap (whitneyMap f₁ f₂) g ≫ (homWhitneySumLeftIso A₁' A₂' D').hom =
      (homWhitneySumLeftIso A₁ A₂ D).hom ≫ whitneyMap (homMap f₁ g) (homMap f₂ g) :=
  whitneySum_hom_ext (by simp) (by simp)

end WhitneySum

/-! ### Identification with Mathlib's Hom bundle -/

/-- Fibrewise identification of `(hom A D).core.Fiber x` with continuous linear maps between the
fibres of `A` and `D`, given by `ContinuousLinearEquiv.finProdCLM`. -/
noncomputable def homFiberEquiv (A D : FiniteRankBundleCore 𝕜 B) (x : B) :
    (hom A D).core.Fiber x ≃L[𝕜] (A.core.Fiber x →L[𝕜] D.core.Fiber x) :=
  finProdCLM 𝕜 A.rank D.rank

@[simp] theorem homFiberEquiv_apply_apply (A D : FiniteRankBundleCore 𝕜 B) (x : B)
    (v : Fin (A.rank * D.rank) → 𝕜) (u : Fin A.rank → 𝕜) (j : Fin D.rank) :
    homFiberEquiv A D x v u j = ∑ i : Fin A.rank, u i * v (finProdFinEquiv (i, j)) :=
  finProdCLM_apply v u j

@[simp] theorem homFiberEquiv_symm_apply (A D : FiniteRankBundleCore 𝕜 B) (x : B)
    (T : A.core.Fiber x →L[𝕜] D.core.Fiber x) (i : Fin A.rank) (j : Fin D.rank) :
    (homFiberEquiv A D x).symm T (finProdFinEquiv (i, j)) = T (Pi.single i 1) j :=
  finProdCLM_symm_apply T i j

/-- In frames at `a` containing `x`, reading `homFiberEquiv A D x v` via `inCoordinates` recovers
the coordinates of `v` in `(hom A D).core.localTriv a` via `finProdCLM`. -/
theorem homFiberEquiv_inCoordinates (A D : FiniteRankBundleCore 𝕜 B) (a x : B)
    (hxA : x ∈ A.core.baseSet a) (hxD : x ∈ D.core.baseSet a) (v : (hom A D).core.Fiber x) :
    ContinuousLinearMap.inCoordinates (Fin A.rank → 𝕜) A.core.Fiber
        (Fin D.rank → 𝕜) D.core.Fiber a x a x (homFiberEquiv A D x v) =
      finProdCLM 𝕜 A.rank D.rank (((hom A D).core.localTriv a) ⟨x, v⟩).2 := by
  have h' := A.core.inCoordinates_eq D.core (homFiberEquiv A D x v)
    (by simpa only [A.indexAt_eq] using hxA) (by simpa only [D.indexAt_eq] using hxD)
  simp only [A.indexAt_eq, D.indexAt_eq, homFiberEquiv] at h'
  simp only [VectorBundleCore.localTriv_apply, (hom A D).indexAt_eq, coordChange_hom]
  exact h'.trans (finProdCLM_homCoordConj (A.core.coordChange a x x)
    (D.core.coordChange x a x) v).symm

private theorem localTriv_homFiberEquiv_symm (A D : FiniteRankBundleCore 𝕜 B) (i : B)
    (q : TotalSpace ((Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜))
      (fun x ↦ A.core.Fiber x →L[𝕜] D.core.Fiber x))
    (hqA : q.proj ∈ A.core.baseSet i) (hqD : q.proj ∈ D.core.baseSet i) :
    (((hom A D).core.localTriv i) ⟨q.proj, (homFiberEquiv A D q.proj).symm q.snd⟩).2 =
      (finProdCLM 𝕜 A.rank D.rank).symm
        ((trivializationAt ((Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜))
          (fun x ↦ A.core.Fiber x →L[𝕜] D.core.Fiber x) i q).2) := by
  apply (finProdCLM 𝕜 A.rank D.rank).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, ← homFiberEquiv_inCoordinates A D i q.proj hqA hqD,
    ContinuousLinearEquiv.apply_symm_apply, hom_trivializationAt_apply]

/-- The reconstructed total space of `hom A D` is homeomorphic to Mathlib's Hom bundle between
`A.core.Fiber` and `D.core.Fiber` over the identity of the base, without assuming completeness of
the scalar field. -/
noncomputable def homTotalSpaceHomeomorph (A D : FiniteRankBundleCore 𝕜 B) :
    (hom A D).core.TotalSpace ≃ₜ
      TotalSpace ((Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜))
        (fun x ↦ A.core.Fiber x →L[𝕜] D.core.Fiber x) where
  toFun p := ⟨p.proj, homFiberEquiv A D p.proj p.snd⟩
  invFun p := ⟨p.proj, (homFiberEquiv A D p.proj).symm p.snd⟩
  left_inv p := by simp
  right_inv p := by simp
  continuous_toFun := by
    refine continuous_iff_continuousAt.2 fun p ↦ ?_
    rw [continuousAt_hom_bundle]
    refine ⟨(hom A D).core.continuous_proj.continuousAt, ?_⟩
    have hp : p ∈ ((hom A D).core.localTriv p.proj).source :=
      ((hom A D).core.mem_localTriv_source p.proj p).2 ((hom A D).core.mem_baseSet_at p.proj)
    have hU := ((hom A D).core.localTriv p.proj).open_source.mem_nhds hp
    have hc := (((hom A D).core.localTriv p.proj).continuousOn.continuousAt hU).snd
    refine ((finProdCLM 𝕜 A.rank D.rank).continuous.continuousAt.comp hc).congr ?_
    filter_upwards [hU] with q hq
    have hq' := ((hom A D).core.mem_localTriv_source p.proj q).1 hq
    exact (homFiberEquiv_inCoordinates A D p.proj q.proj hq'.1 hq'.2 q.snd).symm
  continuous_invFun := by
    refine continuous_iff_continuousAt.2 fun p ↦ ?_
    rw [FiberBundle.continuousAt_totalSpace]
    refine ⟨(FiberBundle.continuous_proj ((Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜))
      (fun x ↦ A.core.Fiber x →L[𝕜] D.core.Fiber x)).continuousAt, ?_⟩
    let e := trivializationAt ((Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜))
      (fun x ↦ A.core.Fiber x →L[𝕜] D.core.Fiber x) p.proj
    have hp : p ∈ e.source := FiberBundle.mem_trivializationAt_proj_source
    have hU := e.open_source.mem_nhds hp
    have hc := (finProdCLM 𝕜 A.rank D.rank).symm.continuous.continuousAt.comp
      ((e.continuousOn.continuousAt hU).snd)
    refine hc.congr_of_eventuallyEq ?_
    filter_upwards [hU] with q hq
    have hq_mem : q.proj ∈ A.core.baseSet p.proj ∩ D.core.baseSet p.proj := by
      simpa only [e, hom_trivializationAt_source, Set.mem_preimage, A.trivializationAt_core,
        D.trivializationAt_core, ← VectorBundleCore.baseSet_at] using hq
    dsimp only [Function.comp_apply]
    rw [(hom A D).trivializationAt_core]
    exact localTriv_homFiberEquiv_symm A D p.proj q hq_mem.1 hq_mem.2

@[simp] theorem homTotalSpaceHomeomorph_apply (A D : FiniteRankBundleCore 𝕜 B)
    (p : (hom A D).core.TotalSpace) :
    homTotalSpaceHomeomorph A D p = ⟨p.proj, homFiberEquiv A D p.proj p.snd⟩ := (rfl)

@[simp] theorem homTotalSpaceHomeomorph_symm_apply (A D : FiniteRankBundleCore 𝕜 B)
    (p : TotalSpace ((Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜))
      (fun x ↦ A.core.Fiber x →L[𝕜] D.core.Fiber x)) :
    (homTotalSpaceHomeomorph A D).symm p = ⟨p.proj, (homFiberEquiv A D p.proj).symm p.snd⟩ := (rfl)

/-- Under `homFiberEquiv`, `homMap f g` acts by precomposing with `f.fiberMap x` and postcomposing
with `g.fiberMap x`. -/
theorem homFiberEquiv_fiberMap_homMap (f : A' ⟶ A) (g : D ⟶ D') (x : B)
    (v : Fin (A.rank * D.rank) → 𝕜) :
    homFiberEquiv A' D' x ((homMap f g).fiberMap x v) =
      (g.fiberMap x).comp ((homFiberEquiv A D x v).comp (f.fiberMap x)) := by
  rw [fiberMap_homMap]
  exact finProdCLM_homCoordConj (f.fiberMap x) (g.fiberMap x) v

/-- `homTotalSpaceHomeomorph` intertwines `homMap f g` on the internal Hom core with precomposition
by `f.fiberMap` and postcomposition by `g.fiberMap` on Mathlib's Hom bundle. -/
theorem homTotalSpaceHomeomorph_naturality (f : A' ⟶ A) (g : D ⟶ D')
    (p : (hom A D).core.TotalSpace) :
    homTotalSpaceHomeomorph A' D' ((homMap f g).totalSpaceMap p) =
      ⟨p.proj, (g.fiberMap p.proj).comp
        (((homTotalSpaceHomeomorph A D p).snd).comp (f.fiberMap p.proj))⟩ := by
  rcases p with ⟨x, v⟩
  rw [CoordinateHom.totalSpaceMap_mk, homTotalSpaceHomeomorph_apply, homTotalSpaceHomeomorph_apply]
  exact congrArg (TotalSpace.mk' ((Fin A'.rank → 𝕜) →L[𝕜] (Fin D'.rank → 𝕜)) x)
    (homFiberEquiv_fiberMap_homMap f g x v)

/-! ### Dual-tensor comparison over a complete scalar field -/

section CompleteSpace

variable [CompleteSpace 𝕜]

/-- Over a complete scalar field, `A.dual ⊗ D` and `hom A D` have identical coordinate data. -/
theorem dual_tensor_eq_hom (A D : FiniteRankBundleCore 𝕜 B) :
    A.dual ⊗ D = hom A D := by
  dsimp only [MonoidalCategoryStruct.tensorObj, tensor, dual, hom]
  congr 2
  funext i j x
  exact piTranspose_kronecker_eq_homCoordConj _ _

/-- Over a complete scalar field, `A.dual ⊗ D` is isomorphic to `hom A D` by the identity
coordinate equivalence on every fibre. -/
noncomputable def dualTensorIsoHom (A D : FiniteRankBundleCore 𝕜 B) :
    A.dual ⊗ D ≅ hom A D :=
  constIso (fun _ ↦ rfl) (ContinuousLinearEquiv.refl 𝕜 (Fin (A.rank * D.rank) → 𝕜))
    fun i j x _ _ ↦ by
      -- Unfold the unexposed `MonoidalCategoryStruct.tensorObj` projection inside `A.dual ⊗ D`.
      change (ContinuousLinearMap.id 𝕜 _).comp
          ((A.core.coordChange j i x).piTranspose.kronecker (D.core.coordChange i j x)) =
        ((A.core.coordChange j i x).homCoordConj (D.core.coordChange i j x)).comp
          (ContinuousLinearMap.id 𝕜 _)
      rw [ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id,
        piTranspose_kronecker_eq_homCoordConj]

@[simp] theorem fiberMap_dualTensorIsoHom_hom (A D : FiniteRankBundleCore 𝕜 B) (x : B) :
    (dualTensorIsoHom A D).hom.fiberMap x =
      ContinuousLinearMap.id 𝕜 (Fin (A.rank * D.rank) → 𝕜) :=
  fiberMap_constIso_hom _ _ _ x

@[simp] theorem fiberMap_dualTensorIsoHom_inv (A D : FiniteRankBundleCore 𝕜 B) (x : B) :
    (dualTensorIsoHom A D).inv.fiberMap x =
      ContinuousLinearMap.id 𝕜 (Fin (A.rank * D.rank) → 𝕜) :=
  fiberMap_constIso_inv _ _ _ x

/-- Naturality of `dualTensorIsoHom` with respect to `dualMap f ⊗ₘ g` and `homMap f g`. -/
@[reassoc (attr := simp)]
theorem dualTensorIsoHom_naturality (f : A' ⟶ A) (g : D ⟶ D') :
    (dualMap f ⊗ₘ g) ≫ (dualTensorIsoHom A' D').hom =
      (dualTensorIsoHom A D).hom ≫ homMap f g :=
  hom_ext fun x ↦ by
    simp only [fiberMap_comp, fiberMap_tensorHom_monoidal, fiberMap_dualMap,
      fiberMap_dualTensorIsoHom_hom, fiberMap_homMap]
    exact (ContinuousLinearMap.id_comp _).trans <|
      (piTranspose_kronecker_eq_homCoordConj _ _).trans (ContinuousLinearMap.comp_id _).symm

/-- Internal Hom into the monoidal unit `𝟙_ _` is isomorphic to the dual core `A.dual`, via the
right Kronecker unitor `kroneckerRid`. -/
noncomputable def homUnitIsoDual (A : FiniteRankBundleCore 𝕜 B) :
    hom A (𝟙_ (FiniteRankBundleCore 𝕜 B)) ≅ A.dual :=
  constIso (fun _ ↦ Set.inter_univ _) (kroneckerRid 𝕜 A.rank) fun i j x _ _ ↦ by
    -- Unfold the unexposed `MonoidalCategoryStruct.tensorUnit` projection inside `𝟙_ _`.
    change (kroneckerRid 𝕜 A.rank).toContinuousLinearMap.comp
        ((A.core.coordChange j i x).homCoordConj (ContinuousLinearMap.id 𝕜 (Fin 1 → 𝕜))) =
      (A.core.coordChange j i x).piTranspose.comp (kroneckerRid 𝕜 A.rank).toContinuousLinearMap
    rw [← piTranspose_kronecker_eq_homCoordConj]
    exact ContinuousLinearMap.kroneckerRid_comp_kronecker _

@[simp] theorem fiberMap_homUnitIsoDual_hom (A : FiniteRankBundleCore 𝕜 B) (x : B) :
    (homUnitIsoDual A).hom.fiberMap x = (kroneckerRid 𝕜 A.rank).toContinuousLinearMap :=
  fiberMap_constIso_hom _ _ _ x

@[simp] theorem fiberMap_homUnitIsoDual_inv (A : FiniteRankBundleCore 𝕜 B) (x : B) :
    (homUnitIsoDual A).inv.fiberMap x = (kroneckerRid 𝕜 A.rank).symm.toContinuousLinearMap :=
  fiberMap_constIso_inv _ _ _ x

/-- Naturality of `homUnitIsoDual` with respect to `homMap f (𝟙 _)` and `dualMap f`. -/
@[reassoc (attr := simp)]
theorem homUnitIsoDual_naturality (f : A' ⟶ A) :
    homMap f (𝟙 (𝟙_ (FiniteRankBundleCore 𝕜 B))) ≫ (homUnitIsoDual A').hom =
      (homUnitIsoDual A).hom ≫ dualMap f :=
  hom_ext fun x ↦ by
    simp only [fiberMap_comp, fiberMap_homMap, fiberMap_id, fiberMap_homUnitIsoDual_hom,
      fiberMap_dualMap, ← piTranspose_kronecker_eq_homCoordConj]
    exact ContinuousLinearMap.kroneckerRid_comp_kronecker _

end CompleteSpace

end

/-! ### Pullback base change for Hom cores -/

section Pullback

variable {𝕜 X Y : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace X] [TopologicalSpace Y]

/-- Pulling back commutes strictly with forming Hom cores. -/
@[simp] theorem pullback_hom (A D : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y)) :
    (hom A D).pullback f = hom (A.pullback f) (D.pullback f) := (rfl)

/-- Pulling back commutes with `homMap`. -/
@[simp] theorem pullbackMap_homMap {A A' D D' : FiniteRankBundleCore 𝕜 Y}
    (a : A' ⟶ A) (b : D ⟶ D') (f : C(X, Y)) :
    pullbackMap (homMap a b) f = homMap (pullbackMap a f) (pullbackMap b f) :=
  hom_ext fun x ↦ (fiberMap_pullbackMap (homMap a b) f x).trans <|
    (fiberMap_homMap a b (f x)).trans <| by
      rw [← fiberMap_pullbackMap a f x, ← fiberMap_pullbackMap b f x]
      exact (fiberMap_homMap (pullbackMap a f) (pullbackMap b f) x).symm

/-- Pulling back commutes with the evaluation morphism `homEv`. -/
@[simp] theorem pullbackMap_homEv (A D : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y)) :
    pullbackMap (homEv A D) f = homEv (A.pullback f) (D.pullback f) :=
  hom_ext fun x ↦ (fiberMap_pullbackMap (homEv A D) f x).trans <|
    (fiberMap_homEv A D (f x)).trans (fiberMap_homEv (A.pullback f) (D.pullback f) x).symm

/-- Pulling back commutes with the coevaluation morphism `(ihom.coev A).app D`. -/
@[simp] theorem pullbackMap_ihom_coev_app (A D : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y)) :
    pullbackMap ((ihom.coev A).app D) f = (ihom.coev (A.pullback f)).app (D.pullback f) :=
  hom_ext fun x ↦ (fiberMap_pullbackMap ((ihom.coev A).app D) f x).trans <|
    (fiberMap_ihom_coev_app A D (f x)).trans
      (fiberMap_ihom_coev_app (A.pullback f) (D.pullback f) x).symm

end Pullback

end TauCeti.FiniteRankBundleCore
