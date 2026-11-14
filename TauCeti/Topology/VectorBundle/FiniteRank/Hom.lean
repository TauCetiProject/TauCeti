/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Monoidal
public import TauCeti.Topology.VectorBundle.FiniteRank.Dual
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided

/-!
# Hom bundles, closed monoidal structure, and rigidity for finite-rank bundle cores

For two point-indexed cores `A` and `D` of ranks `m` and `n`, `FiniteRankBundleCore.hom A D` is the
core of rank `m * n` whose chart at `i` is `A.core.baseSet i ∩ D.core.baseSet i` and whose
transition from chart `i` to chart `j` is operator conjugation
`ContinuousLinearMap.homCoordConj (A.core.coordChange j i x) (D.core.coordChange i j x)` in the
column coordinates of `ContinuousLinearEquiv.finProdCLM`.

Without assuming completeness of the scalar field:

* `homMap` acts contravariantly in the source and covariantly in the target, giving the additive
  functors `homRightFunctor`, `homLeftFunctor`, and `homFunctor`, and distributing over Whitney
  sums in both variables (`homWhitneySumRightIso`, `homWhitneySumLeftIso`);
* `homEv` and `homCurry` exhibit `homRightFunctor A` as right adjoint to `tensorLeft A`, making
  `FiniteRankBundleCore 𝕜 B` a `MonoidalClosed` category whose internal Hom `(ihom A).obj D` is
  definitionally `hom A D` and whose precomposition `MonoidalClosed.pre f` is `homMap f (𝟙 _)`;
* `homTotalSpaceHomeomorph` identifies the reconstructed total space of `hom A D` with Mathlib's
  Hom bundle `TotalSpace ((Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜)) (fun x ↦ A.core.Fiber x →L[𝕜]
  D.core.Fiber x)` over the identity of the base, via `homFiberEquiv` on every fibre;
* pullback along a continuous base map commutes strictly with `hom` and `homMap`
  (`pullback_hom`, `pullbackMap_homMap`).

When `𝕜` is complete, so `FiniteRankBundleCore.dual` is available:

* `A.dual ⊗ D` has literally the same coordinate transitions as `hom A D` (`dual_tensor_eq_hom`),
  giving the canonical isomorphism `dualTensorHomIso : A.dual ⊗ D ≅ hom A D` with identity fibre
  maps and `homUnitIso : hom A (𝟙_ _) ≅ A.dual`;
* `coevaluationHom` and `evaluationHom` satisfy the snake identities (`ExactPairing A A.dual`),
  making `FiniteRankBundleCore 𝕜 B` a `RightRigidCategory` and (by symmetry) a `RigidCategory`
  with `Aᘁ = A.dual`, `ᘁA = A.dual`, and right adjoint mates `fᘁ = dualMap f`
  (`rightAdjointMate_eq_dualMap`). This supplies the `RightRigidCategory` input consumed by
  `TauCeti.SplitK0.dual` on the split Grothendieck ring of finite-rank cores.

For the Hom bundle and its identification with `E* ⊗ F` see Milnor–Stasheff,
*Characteristic Classes*, §3, and Atiyah, *K-Theory*, §1.2.
-/

public section

open Bundle CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite Set VectorBundleCore

namespace TauCeti.FiniteRankBundleCore

open ContinuousLinearEquiv ContinuousLinearMap

section

variable {𝕜 B : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]

/-! ### The Hom core, bifunctoriality, and Whitney-sum distributivity -/

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
    ⟨fun x ↦ (f.operator j i ⟨x.1, x.2.2.1, x.2.1.1⟩).homCoordConj
        (g.operator i j ⟨x.1, x.2.1.2, x.2.2.2⟩),
      ((f.operator j i).continuous.comp (continuous_subtype_val.subtype_mk _)).clm_homCoordConj
        ((g.operator i j).continuous.comp (continuous_subtype_val.subtype_mk _))⟩
  compatible i i' j j' x hi hi' hj hj' v := by
    change ((A'.core.coordChange j' j x).homCoordConj (D'.core.coordChange j j' x)).comp
        ((f.operator j i ⟨x, hj.1, hi.1⟩).homCoordConj (g.operator i j ⟨x, hi.2, hj.2⟩)) v =
      ((f.operator j' i' ⟨x, hj'.1, hi'.1⟩).homCoordConj (g.operator i' j' ⟨x, hi'.2, hj'.2⟩)).comp
        ((A.core.coordChange i' i x).homCoordConj (D.core.coordChange i i' x)) v
    rw [homCoordConj_comp_homCoordConj, homCoordConj_comp_homCoordConj,
      ← f.coordChange_comp_operator j' j i' i x hj'.1 hj.1 hi'.1 hi.1,
      g.coordChange_comp_operator i i' j j' x hi.2 hi'.2 hj.2 hj'.2]

/-- On every fibre, `homMap f g` conjugates operators by `f.fiberMap x` on the right and
`g.fiberMap x` on the left. -/
@[simp] theorem fiberMap_homMap (f : A' ⟶ A) (g : D ⟶ D') (x : B) :
    (homMap f g).fiberMap x = (f.fiberMap x).homCoordConj (g.fiberMap x) := by
  refine (CoordinateHom.fiberMap_def _ x).trans ?_
  change (f.operator x x ⟨x, A'.mem_baseSet_self x, A.mem_baseSet_self x⟩).homCoordConj
    (g.operator x x ⟨x, D.mem_baseSet_self x, D'.mem_baseSet_self x⟩) = _
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

/-- Covariant Hom functor `hom A -` for fixed source `A`. -/
@[expose, simps]
noncomputable def homRightFunctor (A : FiniteRankBundleCore 𝕜 B) :
    FiniteRankBundleCore 𝕜 B ⥤ FiniteRankBundleCore 𝕜 B where
  obj D := hom A D
  map g := homMap (𝟙 A) g
  map_id D := id_homMap_id A D
  map_comp g g' := by rw [homMap_comp_homMap, Category.id_comp]

instance (A : FiniteRankBundleCore 𝕜 B) : (homRightFunctor A).Additive where
  map_add {_ _ g₁ g₂} := homMap_add (𝟙 A) g₁ g₂

/-- Contravariant Hom functor `hom - D` for fixed target `D`. -/
@[expose, simps]
noncomputable def homLeftFunctor (D : FiniteRankBundleCore 𝕜 B) :
    (FiniteRankBundleCore 𝕜 B)ᵒᵖ ⥤ FiniteRankBundleCore 𝕜 B where
  obj A := hom A.unop D
  map f := homMap f.unop (𝟙 D)
  map_id A := id_homMap_id A.unop D
  map_comp f f' := by rw [homMap_comp_homMap, Category.id_comp]; rfl

instance (D : FiniteRankBundleCore 𝕜 B) : (homLeftFunctor D).Additive where
  map_add {_ _ f₁ f₂} := add_homMap f₁.unop f₂.unop (𝟙 D)

variable (𝕜 B) in
/-- Curried Hom bifunctor `(FiniteRankBundleCore 𝕜 B)ᵒᵖ ⥤ FiniteRankBundleCore 𝕜 B ⥤
FiniteRankBundleCore 𝕜 B`. -/
@[expose]
noncomputable def homFunctor :
    (FiniteRankBundleCore 𝕜 B)ᵒᵖ ⥤ FiniteRankBundleCore 𝕜 B ⥤ FiniteRankBundleCore 𝕜 B where
  obj X := homRightFunctor X.unop
  map f :=
    { app := fun Y ↦ homMap f.unop (𝟙 Y)
      naturality := fun Y Y' g ↦ by
        change homMap (𝟙 _) g ≫ homMap f.unop (𝟙 Y') = homMap f.unop (𝟙 Y) ≫ homMap (𝟙 _) g
        simp only [homMap_comp_homMap, Category.id_comp, Category.comp_id] }
  map_id X := NatTrans.ext (funext fun Y ↦ id_homMap_id X.unop Y)
  map_comp f f' := NatTrans.ext (funext fun Y ↦
    (congrArg (fun h ↦ homMap h (𝟙 Y)) (unop_comp (f := f) (g := f'))).trans <|
      (congrArg (homMap (f'.unop ≫ f.unop)) (Category.id_comp (𝟙 Y)).symm).trans
        (homMap_comp_homMap f.unop f'.unop (𝟙 Y) (𝟙 Y)).symm)

@[simp] theorem homFunctor_obj (X : (FiniteRankBundleCore 𝕜 B)ᵒᵖ) :
    (homFunctor 𝕜 B).obj X = homRightFunctor X.unop := (rfl)

@[simp] theorem homFunctor_map_app {X X' : (FiniteRankBundleCore 𝕜 B)ᵒᵖ} (f : X ⟶ X')
    (Y : FiniteRankBundleCore 𝕜 B) :
    ((homFunctor 𝕜 B).map f).app Y = homMap f.unop (𝟙 Y) := (rfl)

section WhitneySum

/-- The image of `whitneyBicone D₁ D₂` under the additive functor `homRightFunctor A`. -/
@[expose]
noncomputable def homWhitneyRightBicone (A D₁ D₂ : FiniteRankBundleCore 𝕜 B) :
    BinaryBicone (hom A D₁) (hom A D₂) :=
  (homRightFunctor A).mapBinaryBicone (whitneyBicone D₁ D₂)

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

/-- The image of `(whitneyBicone A₁ A₂).op` under the additive functor `homLeftFunctor D`. -/
@[expose]
noncomputable def homWhitneyLeftBicone (A₁ A₂ D : FiniteRankBundleCore 𝕜 B) :
    BinaryBicone (hom A₁ D) (hom A₂ D) :=
  (homLeftFunctor D).mapBinaryBicone (whitneyBicone A₁ A₂).op

/-- `homWhitneyLeftBicone` is a binary bilimit because `homLeftFunctor D` is additive. -/
noncomputable def homWhitneyLeftBiconeIsBilimit (A₁ A₂ D : FiniteRankBundleCore 𝕜 B) :
    (homWhitneyLeftBicone A₁ A₂ D).IsBilimit :=
  have := preservesBinaryBiproduct_of_preservesBiproduct (homLeftFunctor D) (op A₁) (op A₂)
  isBinaryBilimitOfPreserves (homLeftFunctor D) (whitneyBiconeIsBilimit A₁ A₂).op

/-- Hom out of a Whitney sum is isomorphic to the Whitney sum of the Homs. -/
noncomputable def homWhitneySumLeftIso (A₁ A₂ D : FiniteRankBundleCore 𝕜 B) :
    hom (whitneySum A₁ A₂) D ≅ whitneySum (hom A₁ D) (hom A₂ D) :=
  (homWhitneyLeftBiconeIsBilimit A₁ A₂ D).isLimit.conePointUniqueUpToIso
    (whitneyBiconeIsBilimit (hom A₁ D) (hom A₂ D)).isLimit

@[reassoc (attr := simp)]
theorem homWhitneySumLeftIso_hom_whitneyFst (A₁ A₂ D : FiniteRankBundleCore 𝕜 B) :
    (homWhitneySumLeftIso A₁ A₂ D).hom ≫ whitneyFst (hom A₁ D) (hom A₂ D) =
      homMap (whitneyInl A₁ A₂) (𝟙 D) :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ (Discrete.mk WalkingPair.left)

@[reassoc (attr := simp)]
theorem homWhitneySumLeftIso_hom_whitneySnd (A₁ A₂ D : FiniteRankBundleCore 𝕜 B) :
    (homWhitneySumLeftIso A₁ A₂ D).hom ≫ whitneySnd (hom A₁ D) (hom A₂ D) =
      homMap (whitneyInr A₁ A₂) (𝟙 D) :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ (Discrete.mk WalkingPair.right)

end WhitneySum

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
        (f.operator x₀ x₀ ⟨y.1, ⟨y.2.2.1, y.2.1⟩, y.2.2.2⟩) :=
    (kroneckerCurry 𝕜 A.rank C.rank D.rank).continuous.comp
      ((f.operator x₀ x₀).continuous.comp
        (Continuous.subtype_mk continuous_subtype_val fun y : ↥U ↦ ⟨⟨y.2.2.1, y.2.1⟩, y.2.2.2⟩))
  refine ⟨continuousAt_id, ContinuousOn.continuousAt (s := U) ?_ hU⟩
  rw [continuousOn_iff_continuous_domRestrict]
  refine hc.congr fun y ↦ ?_
  dsimp only [Set.domRestrict_apply]
  have hfop := f.operator_eq x₀ x₀ ⟨y.1, ⟨y.2.2.1, y.2.1⟩, y.2.2.2⟩
  rw [inChartCoordinates_core] at hfop
  have hin := C.core.inCoordinates_eq (hom A D).core
    (kroneckerCurry 𝕜 A.rank C.rank D.rank (f.fiberMap y.1))
    (by simpa only [C.indexAt_eq] using y.2.1)
    (by simpa only [(hom A D).indexAt_eq, VectorBundleCore.baseSet_at,
      localTriv_baseSet_hom] using y.2.2)
  simp only [C.indexAt_eq, (hom A D).indexAt_eq, coordChange_hom] at hin
  ext c w
  have h₁ := congrFun (DFunLike.congr_fun
    (congrArg (kroneckerCurry 𝕜 A.rank C.rank D.rank) hfop) c) w
  have h₂ := congrFun (DFunLike.congr_fun
    (kroneckerCurry_comp_kronecker (A.core.coordChange x₀ y.1 y.1)
      (C.core.coordChange x₀ y.1 y.1) (D.core.coordChange y.1 x₀ y.1) (f.fiberMap y.1)) c) w
  have h₃ := congrFun (DFunLike.congr_fun hin c) w
  exact h₁.trans (h₂.trans h₃.symm)

/-- Currying of a bundle map `A ⊗ C ⟶ D` to a bundle map `C ⟶ hom A D`. -/
noncomputable def homCurry (f : A ⊗ C ⟶ D) : C ⟶ hom A D :=
  CoordinateHom.ofContinuous
    (fun x ↦ kroneckerCurry 𝕜 A.rank C.rank D.rank (f.fiberMap x))
    (continuous_homCurry_section f)

@[simp] theorem fiberMap_homCurry (f : A ⊗ C ⟶ D) (x : B) :
    (homCurry f).fiberMap x = kroneckerCurry 𝕜 A.rank C.rank D.rank (f.fiberMap x) :=
  congrFun (CoordinateHom.fiberMap_ofContinuous _ _) x

/-- Equivalence `(A ⊗ X ⟶ Y) ≃ (X ⟶ hom A Y)` given by `homCurry` and evaluation `homEv`. -/
@[expose]
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
@[expose]
noncomputable def homAdjunction (X : FiniteRankBundleCore 𝕜 B) :
    tensorLeft X ⊣ homRightFunctor X :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun Y Z ↦ homCurryEquiv X Y Z
      homEquiv_naturality_left_symm := fun h g ↦
        MonoidalCategory.whiskerLeft_comp_assoc X h g (homEv X _)
      homEquiv_naturality_right := fun {Y Z Z'} f k ↦ hom_ext fun x ↦
        (fiberMap_homCurry (A := X) (C := Y) (f ≫ k) x).trans <| by
          rw [fiberMap_comp (f := f) (g := k)]
          refine (?_ : _ = ((homMap (𝟙 X) k).fiberMap x).comp
            ((homCurry (A := X) (C := Y) f).fiberMap x)).trans
              (fiberMap_comp (homCurry (A := X) (C := Y) f) (homMap (𝟙 X) k) x).symm
          rw [fiberMap_homMap, fiberMap_homCurry, fiberMap_id]
          let f₀ : (Fin (X.rank * Y.rank) → 𝕜) →L[𝕜] (Fin Z.rank → 𝕜) := f.fiberMap x
          have h := kroneckerCurry_comp_kronecker
            (ContinuousLinearMap.id 𝕜 (Fin X.rank → 𝕜))
            (ContinuousLinearMap.id 𝕜 (Fin Y.rank → 𝕜)) (k.fiberMap x) f₀
          simp only [id_kronecker_id, ContinuousLinearMap.comp_id] at h
          exact h }

noncomputable instance (A : FiniteRankBundleCore 𝕜 B) : Closed A where
  rightAdj := homRightFunctor A
  adj := homAdjunction A

noncomputable instance : MonoidalClosed (FiniteRankBundleCore 𝕜 B) where

@[simp] theorem ihom_obj (A D : FiniteRankBundleCore 𝕜 B) :
    (ihom A).obj D = hom A D := (rfl)

@[simp] theorem ihom_map (A : FiniteRankBundleCore 𝕜 B) (g : D ⟶ D') :
    (ihom A).map g = homMap (𝟙 A) g := (rfl)

theorem monoidalClosed_curry_eq (f : A ⊗ C ⟶ D) :
    MonoidalClosed.curry f = homCurry f := by
  change (homAdjunction A).homEquiv C D f = homCurry f
  rw [homAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  rfl

@[simp] theorem ihom_ev_app (A D : FiniteRankBundleCore 𝕜 B) :
    (ihom.ev A).app D = homEv A D :=
  (congrArg (· ≫ homEv A D) (MonoidalCategory.whiskerLeft_id A (hom A D))).trans
    (Category.id_comp (homEv A D))

theorem monoidalClosed_uncurry_eq (g : C ⟶ (ihom A).obj D) :
    MonoidalClosed.uncurry g = A ◁ g ≫ homEv A D :=
  (MonoidalClosed.uncurry_eq g).trans (by rw [ihom_ev_app])

theorem finProdCLM_fiberMap_monoidalClosed_curry_apply (f : A ⊗ C ⟶ D) (x : B)
    (c : Fin C.rank → 𝕜) (u : Fin A.rank → 𝕜) :
    finProdCLM 𝕜 A.rank D.rank ((MonoidalClosed.curry f).fiberMap x c) u =
      f.fiberMap x (fun k ↦ u (finProdFinEquiv.symm k).1 * c (finProdFinEquiv.symm k).2) := by
  have h : (MonoidalClosed.curry f).fiberMap x =
      kroneckerCurry 𝕜 A.rank C.rank D.rank (f.fiberMap x) :=
    (congrArg (fun g ↦ g.fiberMap x) (monoidalClosed_curry_eq f)).trans (fiberMap_homCurry f x)
  exact (DFunLike.congr_fun (congrArg (finProdCLM 𝕜 A.rank D.rank)
    (DFunLike.congr_fun h c)) u).trans (finProdCLM_kroneckerCurry_apply (f.fiberMap x) c u)

/-- Precomposition in the monoidal closed structure agrees with `homMap f (𝟙 D)`. -/
@[simp] theorem pre_app (f : A' ⟶ A) (D : FiniteRankBundleCore 𝕜 B) :
    (MonoidalClosed.pre f).app D = homMap f (𝟙 D) := by
  apply MonoidalClosed.uncurry_injective
  refine (MonoidalClosed.uncurry_pre f D).trans <|
    (congrArg (f ▷ hom A D ≫ ·) (ihom_ev_app A D)).trans <|
      (?_ : f ▷ hom A D ≫ homEv A D = A' ◁ homMap f (𝟙 D) ≫ homEv A' D).trans
        (monoidalClosed_uncurry_eq (homMap f (𝟙 D) : (ihom A).obj D ⟶ (ihom A').obj D)).symm
  refine hom_ext fun x ↦ ?_
  rw [fiberMap_comp, fiberMap_comp, fiberMap_homEv, fiberMap_homEv, fiberMap_whiskerRight,
    fiberMap_whiskerLeft, fiberMap_homMap, fiberMap_id]
  apply (kroneckerCurry 𝕜 A'.rank (A.rank * D.rank) D.rank).injective
  have h₁ := kroneckerCurry_comp_kronecker (f.fiberMap x)
    (ContinuousLinearMap.id 𝕜 (Fin (A.rank * D.rank) → 𝕜))
    (ContinuousLinearMap.id 𝕜 (Fin D.rank → 𝕜)) (kroneckerHomEv 𝕜 A.rank D.rank)
  rw [ContinuousLinearMap.id_comp, kroneckerCurry_kroneckerHomEv, ContinuousLinearMap.comp_id,
    ContinuousLinearMap.comp_id] at h₁
  let G := (f.fiberMap x).homCoordConj (ContinuousLinearMap.id 𝕜 (Fin D.rank → 𝕜))
  exact h₁.trans ((ContinuousLinearEquiv.apply_symm_apply
    (kroneckerCurry 𝕜 A'.rank (A.rank * D.rank) D.rank) G).symm.trans
      (congrArg (kroneckerCurry 𝕜 A'.rank (A.rank * D.rank) D.rank)
        (kroneckerCurry_symm_apply_eq (m := A'.rank) (n := D.rank) G)))

/-- Read through `finProdCLM`, the internal identity `MonoidalClosed.id A` scales the identity
operator on each fibre. -/
@[simp] theorem finProdCLM_fiberMap_monoidalClosed_id (A : FiniteRankBundleCore 𝕜 B) (x : B)
    (c : Fin 1 → 𝕜) :
    finProdCLM 𝕜 A.rank A.rank ((MonoidalClosed.id A).fiberMap x c) =
      c 0 • ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜) := by
  ext u j
  have h₁ := congrFun (finProdCLM_fiberMap_monoidalClosed_curry_apply (ρ_ A).hom x c u) j
  have h₂ := congrFun (DFunLike.congr_fun (fiberMap_rightUnitor_hom A x)
    (fun k : Fin (A.rank * 1) ↦ u (finProdFinEquiv.symm k).1 * c (finProdFinEquiv.symm k).2)) j
  refine h₁.trans (h₂.trans ((kroneckerRid_apply _ j).trans ?_))
  simp [mul_comm]

/-- Read through `finProdCLM`, internal composition `MonoidalClosed.comp A D C` composes operators
on pure-tensor coordinate vectors. -/
theorem finProdCLM_fiberMap_monoidalClosed_comp (A D C : FiniteRankBundleCore 𝕜 B) (x : B)
    (f : Fin (A.rank * D.rank) → 𝕜) (g : Fin (D.rank * C.rank) → 𝕜) (u : Fin A.rank → 𝕜) :
    finProdCLM 𝕜 A.rank C.rank (((MonoidalClosed.comp A D C).fiberMap x)
        (fun k ↦ f (finProdFinEquiv.symm k).1 * g (finProdFinEquiv.symm k).2)) u =
      finProdCLM 𝕜 D.rank C.rank g (finProdCLM 𝕜 A.rank D.rank f u) := by
  let w : Fin ((A.rank * D.rank) * (D.rank * C.rank)) → 𝕜 :=
    fun k ↦ f (finProdFinEquiv.symm k).1 * g (finProdFinEquiv.symm k).2
  let rhs : A ⊗ (hom A D ⊗ hom D C) ⟶ C :=
    (α_ A (hom A D) (hom D C)).inv ≫ homEv A D ▷ hom D C ≫ homEv D C
  have hct : MonoidalClosed.compTranspose A D C = rhs :=
    (congrArg (fun e ↦ (α_ A (hom A D) (hom D C)).inv ≫ e ▷ hom D C ≫ (ihom.ev D).app C)
      (ihom_ev_app A D)).trans
      (congrArg ((α_ A (hom A D) (hom D C)).inv ≫ homEv A D ▷ hom D C ≫ ·) (ihom_ev_app D C))
  let pureCLM : (Fin (A.rank * ((A.rank * D.rank) * (D.rank * C.rank))) → 𝕜) →L[𝕜]
      (Fin C.rank → 𝕜) :=
    (kroneckerHomEv 𝕜 D.rank C.rank).comp
      (((kroneckerHomEv 𝕜 A.rank D.rank).kronecker
        (ContinuousLinearMap.id 𝕜 (Fin (D.rank * C.rank) → 𝕜))).comp
        (kroneckerAssoc 𝕜 A.rank (A.rank * D.rank)
          (D.rank * C.rank)).symm.toContinuousLinearMap)
  have hrhs : rhs.fiberMap x = pureCLM := by
    simp only [rhs, fiberMap_comp, fiberMap_homEv, fiberMap_whiskerRight, fiberMap_associator_inv]
    rfl
  let z : Fin (A.rank * ((A.rank * D.rank) * (D.rank * C.rank))) → 𝕜 :=
    fun k ↦ u (finProdFinEquiv.symm k).1 * w (finProdFinEquiv.symm k).2
  ext l
  have h₁ := congrFun
    (finProdCLM_fiberMap_monoidalClosed_curry_apply (MonoidalClosed.compTranspose A D C) x w u) l
  have h₂ := congrFun (DFunLike.congr_fun (congrArg (fun e ↦ e.fiberMap x) hct) z) l
  have h₃ := congrFun (DFunLike.congr_fun hrhs z) l
  refine h₁.trans (h₂.trans (h₃.trans (?_ : pureCLM z l = _)))
  simp only [pureCLM, ContinuousLinearMap.comp_apply, kroneckerHomEv_apply, kronecker_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearEquiv.coe_coe, kroneckerAssoc_symm_apply,
    Equiv.symm_apply_apply, finProdCLM_apply, z, w]
  simp_rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
  ring

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
  ext u j
  have h' := congrFun (DFunLike.congr_fun
    (A.core.inCoordinates_eq D.core (homFiberEquiv A D x v)
      (by simpa only [A.indexAt_eq] using hxA) (by simpa only [D.indexAt_eq] using hxD)) u) j
  have h'' := congrFun (DFunLike.congr_fun
    (finProdCLM_homCoordConj (A.core.coordChange a x x) (D.core.coordChange x a x) v) u) j
  simp only [A.indexAt_eq, D.indexAt_eq, homFiberEquiv] at h'
  simp only [VectorBundleCore.localTriv_apply, (hom A D).indexAt_eq, coordChange_hom]
  exact h'.trans h''.symm

private theorem localTriv_homFiberEquiv_symm (A D : FiniteRankBundleCore 𝕜 B) (i : B)
    (q : TotalSpace ((Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜))
      (fun x ↦ A.core.Fiber x →L[𝕜] D.core.Fiber x))
    (hqA : q.proj ∈ A.core.baseSet i) (hqD : q.proj ∈ D.core.baseSet i) :
    (((hom A D).core.localTriv i) ⟨q.proj, (homFiberEquiv A D q.proj).symm q.2⟩).2 =
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
  toFun p := ⟨p.proj, homFiberEquiv A D p.proj p.2⟩
  invFun p := ⟨p.proj, (homFiberEquiv A D p.proj).symm p.2⟩
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
    exact (homFiberEquiv_inCoordinates A D p.proj q.proj hq'.1 hq'.2 q.2).symm
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
    homTotalSpaceHomeomorph A D p = ⟨p.proj, homFiberEquiv A D p.proj p.2⟩ := (rfl)

@[simp] theorem homTotalSpaceHomeomorph_symm_apply (A D : FiniteRankBundleCore 𝕜 B)
    (p : TotalSpace ((Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜))
      (fun x ↦ A.core.Fiber x →L[𝕜] D.core.Fiber x)) :
    (homTotalSpaceHomeomorph A D).symm p = ⟨p.proj, (homFiberEquiv A D p.proj).symm p.2⟩ := (rfl)

/-- Under `homFiberEquiv`, `homMap f g` acts by precomposing with `f.fiberMap x` and postcomposing
with `g.fiberMap x`. -/
theorem homFiberEquiv_fiberMap_homMap (f : A' ⟶ A) (g : D ⟶ D') (x : B)
    (v : Fin (A.rank * D.rank) → 𝕜) :
    homFiberEquiv A' D' x ((homMap f g).fiberMap x v) =
      (g.fiberMap x).comp ((homFiberEquiv A D x v).comp (f.fiberMap x)) := by
  rw [fiberMap_homMap]
  exact finProdCLM_homCoordConj (f.fiberMap x) (g.fiberMap x) v

/-! ### Dual-tensor comparison and rigidity over a complete scalar field -/

section CompleteSpace

variable [CompleteSpace 𝕜]

/-- Over a complete scalar field, `A.dual ⊗ D` and `hom A D` have identical coordinate data. -/
theorem dual_tensor_eq_hom (A D : FiniteRankBundleCore 𝕜 B) :
    A.dual ⊗ D = hom A D := by
  change tensor A.dual D = hom A D
  dsimp only [tensor, dual, hom]
  congr 2
  funext i j x
  exact piTranspose_kronecker_eq_homCoordConj _ _

/-- Canonical isomorphism `A.dual ⊗ D ≅ hom A D`, whose underlying fibre map on every fibre is the
identity of `Fin (A.rank * D.rank) → 𝕜`. -/
noncomputable def dualTensorHomIso (A D : FiniteRankBundleCore 𝕜 B) :
    A.dual ⊗ D ≅ hom A D :=
  constIso (fun _ ↦ rfl) (ContinuousLinearEquiv.refl 𝕜 (Fin (A.rank * D.rank) → 𝕜))
    fun _ _ _ _ _ ↦ (ContinuousLinearMap.id_comp _).trans
      ((piTranspose_kronecker_eq_homCoordConj _ _).trans (ContinuousLinearMap.comp_id _).symm)

@[simp] theorem fiberMap_dualTensorHomIso_hom (A D : FiniteRankBundleCore 𝕜 B) (x : B) :
    (dualTensorHomIso A D).hom.fiberMap x =
      ContinuousLinearMap.id 𝕜 (Fin (A.rank * D.rank) → 𝕜) :=
  fiberMap_constIso_hom _ _ _ x

@[simp] theorem fiberMap_dualTensorHomIso_inv (A D : FiniteRankBundleCore 𝕜 B) (x : B) :
    (dualTensorHomIso A D).inv.fiberMap x =
      ContinuousLinearMap.id 𝕜 (Fin (A.rank * D.rank) → 𝕜) :=
  fiberMap_constIso_inv _ _ _ x

/-- Naturality of `dualTensorHomIso` in both arguments: `dualMap f ⊗ₘ g` corresponds to
`homMap f g`. -/
@[reassoc (attr := simp)]
theorem dualTensorHomIso_naturality (f : A' ⟶ A) (g : D ⟶ D') :
    (dualMap f ⊗ₘ g) ≫ (dualTensorHomIso A' D').hom =
      (dualTensorHomIso A D).hom ≫ homMap f g :=
  hom_ext fun x ↦ by
    rw [fiberMap_comp, fiberMap_comp, fiberMap_dualTensorHomIso_hom,
      fiberMap_dualTensorHomIso_hom, fiberMap_tensorHom_monoidal, fiberMap_dualMap,
      fiberMap_homMap]
    exact (ContinuousLinearMap.id_comp _).trans
      ((piTranspose_kronecker_eq_homCoordConj _ _).trans (ContinuousLinearMap.comp_id _).symm)

/-- Hom into the monoidal unit is canonically isomorphic to the dual core. -/
noncomputable def homUnitIso (A : FiniteRankBundleCore 𝕜 B) :
    hom A (𝟙_ (FiniteRankBundleCore 𝕜 B)) ≅ A.dual :=
  (dualTensorHomIso A (𝟙_ (FiniteRankBundleCore 𝕜 B))).symm ≪≫ ρ_ A.dual

/-- Coevaluation bundle morphism `𝟙_ _ ⟶ A ⊗ A.dual`, given in every chart by `kroneckerCoev`. -/
noncomputable def coevaluationHom (A : FiniteRankBundleCore 𝕜 B) :
    𝟙_ (FiniteRankBundleCore 𝕜 B) ⟶ A ⊗ A.dual where
  operator _ _ := ContinuousMap.const _ (kroneckerCoev 𝕜 A.rank)
  compatible _ _ j j' x _ _ hj hj' v := by
    change ((A.core.coordChange j j' x).kronecker (A.core.coordChange j' j x).piTranspose)
      (kroneckerCoev 𝕜 A.rank v) = kroneckerCoev 𝕜 A.rank v
    have hcomp : (A.core.coordChange j j' x).comp (A.core.coordChange j' j x) =
        ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜) :=
      (A.core.coordChange_linear_comp j' j j' x ⟨⟨hj'.1, hj.1⟩, hj'.1⟩).trans
        (A.core.coordChange_self_eq_id hj'.1)
    exact congrFun (congrArg DFunLike.coe (kronecker_piTranspose_comp_kroneckerCoev hcomp)) v

@[simp] theorem fiberMap_coevaluationHom (A : FiniteRankBundleCore 𝕜 B) (x : B) :
    (coevaluationHom A).fiberMap x = kroneckerCoev 𝕜 A.rank :=
  CoordinateHom.fiberMap_def _ x

/-- Dinaturality of `coevaluationHom` with respect to `dualMap`. -/
@[reassoc]
theorem coevaluationHom_comp_whiskerRight (f : A ⟶ D) :
    coevaluationHom A ≫ f ▷ A.dual = coevaluationHom D ≫ D ◁ dualMap f :=
  hom_ext fun x ↦ by
    rw [fiberMap_comp, fiberMap_comp, fiberMap_whiskerRight, fiberMap_whiskerLeft,
      fiberMap_dualMap, fiberMap_coevaluationHom, fiberMap_coevaluationHom]
    exact kronecker_comp_kroneckerCoev (f.fiberMap x)

/-- Evaluation bundle morphism `A.dual ⊗ A ⟶ 𝟙_ _`, given in every chart by `kroneckerEv`. -/
noncomputable def evaluationHom (A : FiniteRankBundleCore 𝕜 B) :
    A.dual ⊗ A ⟶ 𝟙_ (FiniteRankBundleCore 𝕜 B) where
  operator _ _ := ContinuousMap.const _ (kroneckerEv 𝕜 A.rank)
  compatible i i' _ _ x hi hi' _ _ v := by
    change kroneckerEv 𝕜 A.rank v = kroneckerEv 𝕜 A.rank
      (((A.core.coordChange i' i x).piTranspose.kronecker (A.core.coordChange i i' x)) v)
    have hcomp : (A.core.coordChange i' i x).comp (A.core.coordChange i i' x) =
        ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜) :=
      (A.core.coordChange_linear_comp i i' i x ⟨⟨hi.1, hi'.1⟩, hi.1⟩).trans
        (A.core.coordChange_self_eq_id hi.1)
    exact (congrFun (congrArg DFunLike.coe (kroneckerEv_comp_piTranspose_kronecker hcomp)) v).symm

@[simp] theorem fiberMap_evaluationHom (A : FiniteRankBundleCore 𝕜 B) (x : B) :
    (evaluationHom A).fiberMap x = kroneckerEv 𝕜 A.rank :=
  CoordinateHom.fiberMap_def _ x

/-- Dinaturality of `evaluationHom` with respect to `dualMap`. -/
@[reassoc]
theorem whiskerRight_comp_evaluationHom (f : A ⟶ D) :
    dualMap f ▷ A ≫ evaluationHom A = D.dual ◁ f ≫ evaluationHom D :=
  hom_ext fun x ↦ by
    rw [fiberMap_comp, fiberMap_comp, fiberMap_whiskerRight, fiberMap_whiskerLeft,
      fiberMap_dualMap, fiberMap_evaluationHom, fiberMap_evaluationHom]
    exact kroneckerEv_comp_kronecker (f.fiberMap x)

/-- `A` and `A.dual` form an exact pairing in the monoidal category of finite-rank cores. -/
noncomputable instance exactPairingDual (A : FiniteRankBundleCore 𝕜 B) :
    ExactPairing A A.dual where
  coevaluation' := coevaluationHom A
  evaluation' := evaluationHom A
  coevaluation_evaluation' := hom_ext fun x ↦ by
    simp only [fiberMap_comp, fiberMap_whiskerLeft, fiberMap_whiskerRight,
      fiberMap_associator_inv, fiberMap_coevaluationHom, fiberMap_evaluationHom,
      fiberMap_rightUnitor_hom, fiberMap_leftUnitor_inv]
    exact kroneckerEv_kronecker_comp_kroneckerAssoc_symm_comp_kronecker_kroneckerCoev A.rank
  evaluation_coevaluation' := hom_ext fun x ↦ by
    simp only [fiberMap_comp, fiberMap_whiskerLeft, fiberMap_whiskerRight,
      fiberMap_associator_hom, fiberMap_coevaluationHom, fiberMap_evaluationHom,
      fiberMap_leftUnitor_hom, fiberMap_rightUnitor_inv]
    exact kronecker_kroneckerEv_comp_kroneckerAssoc_comp_kroneckerCoev_kronecker A.rank

noncomputable instance (A : FiniteRankBundleCore 𝕜 B) : HasRightDual A where
  rightDual := A.dual

@[simp] theorem rightDual_eq_dual (A : FiniteRankBundleCore 𝕜 B) : Aᘁ = A.dual := (rfl)

@[simp] theorem coevaluation_eq_coevaluationHom (A : FiniteRankBundleCore 𝕜 B) :
    η_ A A.dual = coevaluationHom A := (rfl)

@[simp] theorem evaluation_eq_evaluationHom (A : FiniteRankBundleCore 𝕜 B) :
    ε_ A A.dual = evaluationHom A := (rfl)

noncomputable instance : RightRigidCategory (FiniteRankBundleCore 𝕜 B) where

noncomputable instance : RigidCategory (FiniteRankBundleCore 𝕜 B) :=
  BraidedCategory.rigidCategoryOfRightRigidCategory

@[simp] theorem leftDual_eq_dual (A : FiniteRankBundleCore 𝕜 B) :
    (ᘁA : FiniteRankBundleCore 𝕜 B) = A.dual := (rfl)

/-- The categorical right adjoint mate `fᘁ` of a bundle morphism is `dualMap f`. -/
@[simp] theorem rightAdjointMate_eq_dualMap (f : A ⟶ D) : fᘁ = dualMap f := by
  change (ρ_ D.dual).inv ≫ D.dual ◁ coevaluationHom A ≫ D.dual ◁ (f ▷ A.dual) ≫
    (α_ D.dual D A.dual).inv ≫ evaluationHom D ▷ A.dual ≫ (λ_ A.dual).hom = dualMap f
  rw [← MonoidalCategory.whiskerLeft_comp_assoc, coevaluationHom_comp_whiskerRight,
    MonoidalCategory.whiskerLeft_comp_assoc, MonoidalCategory.associator_inv_naturality_right_assoc,
    MonoidalCategory.whisker_exchange_assoc]
  have hsnake : D.dual ◁ coevaluationHom D ≫ (α_ D.dual D D.dual).inv ≫
      evaluationHom D ▷ D.dual = (ρ_ D.dual).hom ≫ (λ_ D.dual).inv :=
    ExactPairing.coevaluation_evaluation D D.dual
  slice_lhs 2 4 => rw [hsnake]
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id_assoc,
    MonoidalCategory.leftUnitor_naturality, Iso.inv_hom_id_assoc]

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

end Pullback

end TauCeti.FiniteRankBundleCore
