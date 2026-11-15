/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Monoidal
public import TauCeti.Topology.VectorBundle.FiniteRank.Dual
public import TauCeti.Topology.VectorBundle.FiniteRank.Pullback
public import TauCeti.Analysis.Normed.Operator.HomCoords
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# Internal Hom bundles and closed monoidal structure of finite-rank cores

For point-indexed cores `A` and `D` of ranks `a` and `d`, `FiniteRankBundleCore.hom A D` is their
internal Hom core of rank `a * d`. Its chart at each base point is the intersection of the charts
of `A` and `D`, and its transition from chart `i` to chart `j` conjugates operators in coordinates
by the reverse transition of `A` and the forward transition of `D`
(`ContinuousLinearMap.finHomMap`), where a continuous linear map on `Fin a → 𝕜` is stored by its
values on the standard basis (`ContinuousLinearEquiv.finHomEquiv`). Neither completeness of the
scalar field nor any separation or compactness hypothesis on the base is required.

Bundle morphisms `f : A' ⟶ A` and `g : D ⟶ D'` induce `homHom f g : hom A D ⟶ hom A' D'`, acting on
fibres by precomposition with `f` and postcomposition with `g`. Together with the coordinate
evaluation `homEv : A ⊗ hom A D ⟶ D` and coevaluation `homCoev : Y ⟶ hom A (A ⊗ Y)`, this equips
`FiniteRankBundleCore 𝕜 B` with a `MonoidalClosed` structure whose internal Hom `A ⟶[C] D` is
definitionally `hom A D`. Mathlib's `MonoidalClosed` API then provides currying, uncurrying,
precomposition (`pre_app`), internal identity and composition morphisms, and the bijection between
external morphisms `A ⟶ D` and global sections `𝟙_ _ ⟶ hom A D`, all of which are identified
fibrewise with their operator-level counterparts through `homFiberEquiv`.

The construction distributes over Whitney sums in both arguments (`whitneySumHomIso` and
`homWhitneySumIso`), commutes strictly with base change (`pullback_hom`, `pullback_tensor`), and
is identified on total spaces with Mathlib's Hom bundle (`homTotalSpaceHomeomorph`). Over a
complete scalar field, where dual cores are defined via `ContinuousLinearEquiv.piRing`, the
canonical contraction `A.dual ⊗ D ≅ hom A D` (`dualTensorIsoHom`) has the identity coordinate
matrix on every fibre, and `hom A (𝟙_ _) ≅ A.dual` (`homUnitIsoDual`).

For the Hom bundle and its transition functions see Milnor–Stasheff, *Characteristic Classes*, §3,
and Atiyah, *K-Theory*, §1.2.
-/

public section

open Bundle CategoryTheory VectorBundleCore Opposite Set
open scoped MonoidalCategory

namespace TauCeti.FiniteRankBundleCore

section General

variable {𝕜 B : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]

/-- The internal Hom core `Hom(A, D)`, with intersected charts and two-sided operator conjugation
transitions `ContinuousLinearMap.finHomMap`. -/
-- Expose the rank projection and allow implicit-argument reduction of coordinate models.
@[expose, implicit_reducible]
def hom (A D : FiniteRankBundleCore 𝕜 B) : FiniteRankBundleCore 𝕜 B where
  rank := A.rank * D.rank
  core :=
    { baseSet := fun i => A.core.baseSet i ∩ D.core.baseSet i
      isOpen_baseSet := fun i => (A.core.isOpen_baseSet i).inter (D.core.isOpen_baseSet i)
      indexAt := id
      mem_baseSet_at := fun x => by
        simpa only [mem_inter_iff, id_eq, A.indexAt_eq, D.indexAt_eq] using
          And.intro (A.core.mem_baseSet_at x) (D.core.mem_baseSet_at x)
      coordChange := fun i j x =>
        (A.core.coordChange j i x).finHomMap (D.core.coordChange i j x)
      coordChange_self := fun i x hx v => by
        rw [A.core.coordChange_self_eq_id hx.1, D.core.coordChange_self_eq_id hx.2,
          ContinuousLinearMap.finHomMap_id, ContinuousLinearMap.id_apply]
      continuousOn_coordChange := fun i j =>
        ((A.core.continuousOn_coordChange j i).mono
          (fun _ (hx : _ ∈ (A.core.baseSet i ∩ D.core.baseSet i) ∩
            (A.core.baseSet j ∩ D.core.baseSet j)) => ⟨hx.2.1, hx.1.1⟩)).clm_finHomMap
          ((D.core.continuousOn_coordChange i j).mono
            (fun _ (hx : _ ∈ (A.core.baseSet i ∩ D.core.baseSet i) ∩
              (A.core.baseSet j ∩ D.core.baseSet j)) => ⟨hx.1.2, hx.2.2⟩))
      coordChange_comp := fun i j k x hx v => by
        rw [← ContinuousLinearMap.comp_apply, ContinuousLinearMap.finHomMap_comp,
          A.core.coordChange_linear_comp k j i x ⟨⟨hx.2.1, hx.1.2.1⟩, hx.1.1.1⟩,
          D.core.coordChange_linear_comp i j k x ⟨⟨hx.1.1.2, hx.1.2.2⟩, hx.2.2⟩] }
  indexAt_eq := fun _ => rfl

@[simp] theorem rank_hom (A D : FiniteRankBundleCore 𝕜 B) :
    (hom A D).rank = A.rank * D.rank := (rfl)

@[simp] theorem localTriv_baseSet_hom (A D : FiniteRankBundleCore 𝕜 B) (i : B) :
    ((hom A D).core.localTriv i).baseSet = A.core.baseSet i ∩ D.core.baseSet i := (rfl)

/-- The transition of `hom A D` from chart `i` to chart `j` conjugates by the transition of `A`
from `j` to `i` and the transition of `D` from `i` to `j`. -/
@[simp] theorem coordChange_hom (A D : FiniteRankBundleCore 𝕜 B) (i j x : B) :
    (hom A D).core.coordChange i j x =
      (A.core.coordChange j i x).finHomMap (D.core.coordChange i j x) := (rfl)

/-- The internal Hom between trivial cores of ranks `m` and `n` is the trivial core of rank
`m * n`. -/
@[simp] theorem hom_trivial (m n : ℕ) :
    hom (trivial 𝕜 B m) (trivial 𝕜 B n) = trivial 𝕜 B (m * n) := by
  simp only [hom, trivial, Set.univ_inter, ContinuousLinearMap.finHomMap_id]
  rfl

variable {A A' A'' D D' D'' C Y Y' : FiniteRankBundleCore 𝕜 B}

/-- Functorial action on internal Hom cores, contravariant in the source and covariant in the
target, given in charts by `ContinuousLinearMap.finHomMap`. -/
def homHom (f : A' ⟶ A) (g : D ⟶ D') : hom A D ⟶ hom A' D' where
  operator i j :=
    ⟨fun x => (f.operator j i ⟨x.1, x.2.2.1, x.2.1.1⟩).finHomMap
        (g.operator i j ⟨x.1, x.2.1.2, x.2.2.2⟩),
      ((f.operator j i).continuous.comp (continuous_subtype_val.subtype_mk _)).clm_finHomMap
        ((g.operator i j).continuous.comp (continuous_subtype_val.subtype_mk _))⟩
  compatible i i' j j' x hi hi' hj hj' v := by
    -- Unfold the chart-operator literal and `Set.inter` membership on the chart domains.
    change ((A'.core.coordChange j' j x).finHomMap (D'.core.coordChange j j' x)).comp
        ((f.operator j i ⟨x, hj.1, hi.1⟩).finHomMap (g.operator i j ⟨x, hi.2, hj.2⟩)) v =
      ((f.operator j' i' ⟨x, hj'.1, hi'.1⟩).finHomMap (g.operator i' j' ⟨x, hi'.2, hj'.2⟩)).comp
        ((A.core.coordChange i' i x).finHomMap (D.core.coordChange i i' x)) v
    rw [ContinuousLinearMap.finHomMap_comp, ContinuousLinearMap.finHomMap_comp,
      ← f.coordChange_comp_operator j' j i' i x hj'.1 hj.1 hi'.1 hi.1,
      g.coordChange_comp_operator i i' j j' x hi.2 hi'.2 hj.2 hj'.2]

/-- On every fibre, `homHom f g` acts by two-sided operator conjugation `finHomMap`. -/
@[simp] theorem fiberMap_homHom (f : A' ⟶ A) (g : D ⟶ D') (x : B) :
    (homHom f g).fiberMap x = (f.fiberMap x).finHomMap (g.fiberMap x) := by
  calc
    _ = (f.operator x x ⟨x, A'.mem_baseSet_self x, A.mem_baseSet_self x⟩).finHomMap
        (g.operator x x ⟨x, D.mem_baseSet_self x, D'.mem_baseSet_self x⟩) :=
      CoordinateHom.fiberMap_def _ x
    _ = _ := by rw [operator_self, operator_self]

@[simp] theorem id_homHom_id (A D : FiniteRankBundleCore 𝕜 B) :
    homHom (𝟙 A) (𝟙 D) = 𝟙 (hom A D) :=
  hom_ext fun x => by
    rw [fiberMap_homHom, fiberMap_id, fiberMap_id, fiberMap_id]
    exact ContinuousLinearMap.finHomMap_id

@[reassoc (attr := simp)]
theorem homHom_comp_homHom (f : A' ⟶ A) (f' : A'' ⟶ A') (g : D ⟶ D') (g' : D' ⟶ D'') :
    homHom f g ≫ homHom f' g' = homHom (f' ≫ f) (g ≫ g') :=
  hom_ext fun x => by
    rw [fiberMap_comp, fiberMap_homHom, fiberMap_homHom, fiberMap_homHom, fiberMap_comp,
      fiberMap_comp]
    exact ContinuousLinearMap.finHomMap_comp _ _ _ _

@[simp] theorem add_homHom (f f' : A' ⟶ A) (g : D ⟶ D') :
    homHom (f + f') g = homHom f g + homHom f' g :=
  hom_ext fun x => by
    rw [fiberMap_add, fiberMap_homHom, fiberMap_homHom, fiberMap_homHom, fiberMap_add]
    exact ContinuousLinearMap.add_finHomMap _ _ _

@[simp] theorem homHom_add (f : A' ⟶ A) (g g' : D ⟶ D') :
    homHom f (g + g') = homHom f g + homHom f g' :=
  hom_ext fun x => by
    rw [fiberMap_add, fiberMap_homHom, fiberMap_homHom, fiberMap_homHom, fiberMap_add]
    exact ContinuousLinearMap.finHomMap_add _ _ _

@[simp] theorem zero_homHom (g : D ⟶ D') : homHom (0 : A' ⟶ A) g = 0 :=
  hom_ext fun x => by
    rw [fiberMap_homHom, CoordinateHom.fiberMap_zero, CoordinateHom.fiberMap_zero]
    exact ContinuousLinearMap.zero_finHomMap _

@[simp] theorem homHom_zero (f : A' ⟶ A) : homHom f (0 : D ⟶ D') = 0 :=
  hom_ext fun x => by
    rw [fiberMap_homHom, CoordinateHom.fiberMap_zero, CoordinateHom.fiberMap_zero]
    exact ContinuousLinearMap.finHomMap_zero _

@[simp] theorem neg_homHom (f : A' ⟶ A) (g : D ⟶ D') :
    homHom (-f) g = -homHom f g := by
  rw [eq_neg_iff_add_eq_zero, ← add_homHom, neg_add_cancel, zero_homHom]

@[simp] theorem homHom_neg (f : A' ⟶ A) (g : D ⟶ D') :
    homHom f (-g) = -homHom f g := by
  rw [eq_neg_iff_add_eq_zero, ← homHom_add, neg_add_cancel, homHom_zero]

/-- `homHom` preserves bundle isomorphisms in both arguments. -/
instance (f : A' ⟶ A) (g : D ⟶ D') [IsIso f] [IsIso g] : IsIso (homHom f g) :=
  ⟨homHom (inv f) (inv g), by simp, by simp⟩

/-- Covariant Hom functor `hom A -` with fixed source `A`. -/
-- Expose so the closed monoidal internal Hom `ihom A` reduces definitionally to `hom A -`.
@[expose, simps]
def homFunctorRight (A : FiniteRankBundleCore 𝕜 B) :
    FiniteRankBundleCore 𝕜 B ⥤ FiniteRankBundleCore 𝕜 B where
  obj D := hom A D
  map g := homHom (𝟙 A) g
  map_id D := id_homHom_id A D
  map_comp g g' := by rw [homHom_comp_homHom, Category.id_comp]

instance (A : FiniteRankBundleCore 𝕜 B) : (homFunctorRight A).Additive where
  map_add := homHom_add (𝟙 A) _ _

/-- Contravariant Hom functor `hom - D` with fixed target `D`. -/
-- Expose the object and morphism maps, which `@[simps]` exports as definitional projections.
@[expose, simps]
def homFunctorLeft (D : FiniteRankBundleCore 𝕜 B) :
    (FiniteRankBundleCore 𝕜 B)ᵒᵖ ⥤ FiniteRankBundleCore 𝕜 B where
  obj A := hom A.unop D
  map f := homHom f.unop (𝟙 D)
  map_id A := id_homHom_id A.unop D
  map_comp f f' := by rw [homHom_comp_homHom, Category.comp_id]; rfl

instance (D : FiniteRankBundleCore 𝕜 B) : (homFunctorLeft D).Additive where
  map_add {_ _ f f'} := add_homHom f.unop f'.unop (𝟙 D)

/-! ### Evaluation, coevaluation, and closed monoidal structure -/

/-- Evaluation morphism `A ⊗ hom A D ⟶ D`, induced by the constant coordinate contraction
`ContinuousLinearMap.finHomEv`. -/
def homEv (A D : FiniteRankBundleCore 𝕜 B) : A ⊗ hom A D ⟶ D :=
  constHom (fun _ => inter_subset_right.trans inter_subset_right)
    (ContinuousLinearMap.finHomEv 𝕜 A.rank D.rank)
    fun i j x hi hj => ContinuousLinearMap.finHomEv_comp_kronecker_finHomMap
      (by rw [A.core.coordChange_linear_comp i j i x ⟨⟨hi.1, hj.1⟩, hi.1⟩,
            A.core.coordChange_self_eq_id hi.1]) _

@[simp] theorem fiberMap_homEv (A D : FiniteRankBundleCore 𝕜 B) (x : B) :
    (homEv A D).fiberMap x = ContinuousLinearMap.finHomEv 𝕜 A.rank D.rank :=
  fiberMap_constHom _ _ _ x

/-- Dinaturality of `homEv`: precomposing in `hom A D` with `f : A' ⟶ A` and postcomposing with
`g : D ⟶ D'` agrees with applying `f` on the first tensor factor and `g` on the output. -/
@[reassoc]
theorem whiskerLeft_homHom_homEv (f : A' ⟶ A) (g : D ⟶ D') :
    A' ◁ homHom f g ≫ homEv A' D' = f ▷ hom A D ≫ homEv A D ≫ g :=
  hom_ext fun x => by
    simp only [fiberMap_comp, fiberMap_whiskerLeft, fiberMap_whiskerRight, fiberMap_homHom,
      fiberMap_homEv]
    exact ContinuousLinearMap.finHomEv_comp_id_kronecker_finHomMap _ _

/-- Coevaluation morphism `Y ⟶ hom A (A ⊗ Y)`, given in charts `(i, j)` by `finHomCoev` after the
transition of `Y` from `i` to `j`. -/
def homCoev (A Y : FiniteRankBundleCore 𝕜 B) : Y ⟶ hom A (A ⊗ Y) where
  operator i j :=
    ⟨fun x => (ContinuousLinearMap.finHomCoev 𝕜 A.rank Y.rank).comp (Y.core.coordChange i j x.1),
      ((Y.core.continuousOn_coordChange i j).mono
        fun _ (hx : _ ∈ Y.core.baseSet i ∩
          (A.core.baseSet j ∩ (A.core.baseSet j ∩ Y.core.baseSet j))) =>
            ⟨hx.1, hx.2.2.2⟩).domRestrict.const_clm_comp
        (ContinuousLinearMap.finHomCoev 𝕜 A.rank Y.rank)⟩
  compatible i i' j j' x hi hi' hj hj' v := by
    -- Unfold the unexposed `MonoidalCategoryStruct.tensorObj` projection inside `(A ⊗ Y).core`.
    change ((A.core.coordChange j' j x).finHomMap
        ((A.core.coordChange j j' x).kronecker (Y.core.coordChange j j' x))).comp
        (ContinuousLinearMap.finHomCoev 𝕜 A.rank Y.rank) (Y.core.coordChange i j x v) =
      ContinuousLinearMap.finHomCoev 𝕜 A.rank Y.rank
        (Y.core.coordChange i' j' x (Y.core.coordChange i i' x v))
    rw [ContinuousLinearMap.finHomMap_kronecker_comp_finHomCoev
        (by rw [A.core.coordChange_linear_comp j' j j' x ⟨⟨hj'.1, hj.1⟩, hj'.1⟩,
              A.core.coordChange_self_eq_id hj'.1]),
      ContinuousLinearMap.comp_apply,
      Y.core.coordChange_comp i j j' x ⟨⟨hi, hj.2.2⟩, hj'.2.2⟩,
      Y.core.coordChange_comp i i' j' x ⟨⟨hi, hi'⟩, hj'.2.2⟩]

@[simp] theorem fiberMap_homCoev (A Y : FiniteRankBundleCore 𝕜 B) (x : B) :
    (homCoev A Y).fiberMap x = ContinuousLinearMap.finHomCoev 𝕜 A.rank Y.rank := by
  calc
    _ = (ContinuousLinearMap.finHomCoev 𝕜 A.rank Y.rank).comp
        (Y.core.coordChange (Y.core.indexAt x) x x) :=
      CoordinateHom.fiberMap_def _ x
    _ = _ := by rw [Y.indexAt_eq, coordChange_self, ContinuousLinearMap.comp_id]

@[reassoc]
theorem homCoev_naturality (A : FiniteRankBundleCore 𝕜 B) (g : Y ⟶ Y') :
    g ≫ homCoev A Y' = homCoev A Y ≫ homHom (𝟙 A) (A ◁ g) :=
  hom_ext fun x => by
    simp only [fiberMap_comp, fiberMap_homCoev, fiberMap_homHom, fiberMap_id,
      fiberMap_whiskerLeft]
    exact (ContinuousLinearMap.finHomMap_kronecker_comp_finHomCoev
      (ContinuousLinearMap.id_comp _) (g.fiberMap x)).symm

@[reassoc (attr := simp)]
theorem whiskerLeft_homCoev_homEv (A Y : FiniteRankBundleCore 𝕜 B) :
    A ◁ homCoev A Y ≫ homEv A (A ⊗ Y) = 𝟙 (A ⊗ Y) :=
  hom_ext fun x => by
    rw [fiberMap_comp, fiberMap_whiskerLeft, fiberMap_homCoev, fiberMap_homEv, fiberMap_id]
    exact ContinuousLinearMap.finHomEv_comp_id_kronecker_finHomCoev A.rank Y.rank

@[reassoc (attr := simp)]
theorem homCoev_homHom_homEv (A D : FiniteRankBundleCore 𝕜 B) :
    homCoev A (hom A D) ≫ homHom (𝟙 A) (homEv A D) = 𝟙 (hom A D) :=
  hom_ext fun x => by
    rw [fiberMap_comp, fiberMap_homCoev, fiberMap_homHom, fiberMap_id, fiberMap_homEv, fiberMap_id]
    exact ContinuousLinearMap.finHomMap_id_finHomEv_comp_finHomCoev A.rank D.rank

/-- Every finite-rank core `A` is closed, with right adjoint `homFunctorRight A`. -/
instance instClosed (A : FiniteRankBundleCore 𝕜 B) : Closed A where
  rightAdj := homFunctorRight A
  adj := Adjunction.mkOfUnitCounit
    { unit :=
        { app := homCoev A
          naturality := fun _ _ g => homCoev_naturality A g }
      counit :=
        { app := homEv A
          naturality := fun _ _ g =>
            (whiskerLeft_homHom_homEv (𝟙 A) g).trans
              (by rw [MonoidalCategory.id_whiskerRight, Category.id_comp]; rfl) }
      left_triangle := NatTrans.ext <| funext fun Y => by
        dsimp [homFunctorRight, MonoidalCategory.tensorLeft]
        simp
      right_triangle := NatTrans.ext <| funext fun D => by
        dsimp [homFunctorRight]
        simp }

/-- Finite-rank cores over any base and nontrivially normed field form a closed monoidal
category. -/
instance instMonoidalClosed : MonoidalClosed (FiniteRankBundleCore 𝕜 B) where

@[simp] theorem ihom_obj (A D : FiniteRankBundleCore 𝕜 B) :
    (A ⟶[FiniteRankBundleCore 𝕜 B] D) = hom A D := (rfl)

@[simp] theorem ihom_map (A : FiniteRankBundleCore 𝕜 B) (g : D ⟶ D') :
    (ihom A).map g = homHom (𝟙 A) g := (rfl)

@[simp] theorem ihom_ev_app (A D : FiniteRankBundleCore 𝕜 B) :
    (ihom.ev A).app D = homEv A D := (rfl)

@[simp] theorem ihom_coev_app (A Y : FiniteRankBundleCore 𝕜 B) :
    (ihom.coev A).app Y = homCoev A Y := (rfl)

/-- Categorical precomposition `MonoidalClosed.pre f` in the internal Hom agrees with
`homHom f (𝟙 D)`. -/
@[simp] theorem pre_app (f : A' ⟶ A) (D : FiniteRankBundleCore 𝕜 B) :
    (MonoidalClosed.pre f).app D = homHom f (𝟙 D) := by
  apply MonoidalClosed.uncurry_injective
  refine (MonoidalClosed.uncurry_pre f D).trans ?_
  -- `ihom` is semireducible in Mathlib, so `rw` at implicit transparency cannot unify
  -- `(ihom A).obj` with `hom A` inside morphism composition.
  change f ▷ hom A D ≫ homEv A D = A' ◁ homHom f (𝟙 D) ≫ homEv A' D
  simpa only [Category.comp_id] using (whiskerLeft_homHom_homEv f (𝟙 D)).symm

/-! ### Fibrewise operator equivalence, currying, and comparison with Mathlib's Hom bundle -/

/-- Identification of the fibre of `hom A D` at `x` with the space of continuous linear maps from
the fibre of `A` at `x` to the fibre of `D` at `x`. -/
def homFiberEquiv (A D : FiniteRankBundleCore 𝕜 B) (x : B) :
    (hom A D).core.Fiber x ≃L[𝕜] (A.core.Fiber x →L[𝕜] D.core.Fiber x) :=
  (ContinuousLinearEquiv.finHomEquiv 𝕜 A.rank D.rank).symm

@[simp] theorem homFiberEquiv_apply (A D : FiniteRankBundleCore 𝕜 B) (x : B)
    (v : Fin (A.rank * D.rank) → 𝕜) (u : Fin A.rank → 𝕜) (j : Fin D.rank) :
    homFiberEquiv A D x v u j = ∑ i : Fin A.rank, u i * v (finProdFinEquiv (i, j)) :=
  ContinuousLinearEquiv.finHomEquiv_symm_apply v u j

@[simp] theorem homFiberEquiv_symm_apply (A D : FiniteRankBundleCore 𝕜 B) (x : B)
    (f : A.core.Fiber x →L[𝕜] D.core.Fiber x) (i : Fin A.rank) (j : Fin D.rank) :
    (homFiberEquiv A D x).symm f (finProdFinEquiv (i, j)) = f (Pi.single i 1) j :=
  ContinuousLinearEquiv.finHomEquiv_apply f i j

/-- Under `homFiberEquiv`, `homHom f g` acts by precomposition with `f.fiberMap x` and
postcomposition with `g.fiberMap x`. -/
theorem homFiberEquiv_fiberMap_homHom (f : A' ⟶ A) (g : D ⟶ D') (x : B)
    (v : Fin (A.rank * D.rank) → 𝕜) :
    homFiberEquiv A' D' x ((homHom f g).fiberMap x v) =
      (g.fiberMap x).comp ((homFiberEquiv A D x v).comp (f.fiberMap x)) := by
  rw [fiberMap_homHom]
  exact ContinuousLinearMap.finHomEquiv_symm_finHomMap _ _ v

/-- Under `homFiberEquiv`, currying a morphism `f : A ⊗ Y ⟶ D` evaluates `f.fiberMap x` on pure
Kronecker vectors `u ⊗ y`. -/
theorem homFiberEquiv_fiberMap_curry (f : A ⊗ Y ⟶ D) (x : B) (y : Fin Y.rank → 𝕜)
    (u : Fin A.rank → 𝕜) :
    homFiberEquiv A D x ((MonoidalClosed.curry f).fiberMap x y) u =
      f.fiberMap x (fun k ↦ u (finProdFinEquiv.symm k).1 * y (finProdFinEquiv.symm k).2) := by
  -- Unfold semireducible `MonoidalClosed.curry` and `VectorBundleCore.Fiber` at default
  -- transparency so coordinate `rw` lemmas match at implicit transparency.
  change (ContinuousLinearEquiv.finHomEquiv 𝕜 A.rank D.rank).symm
    ((homCoev A Y ≫ homHom (𝟙 A) f).fiberMap x y) u = _
  rw [fiberMap_comp, ContinuousLinearMap.comp_apply, fiberMap_homHom,
    ContinuousLinearMap.finHomEquiv_symm_finHomMap, fiberMap_id, fiberMap_homCoev]
  refine congrArg (f.fiberMap x) (funext fun k ↦ ?_)
  obtain ⟨⟨i, l⟩, rfl⟩ := finProdFinEquiv.surjective k
  simp only [Equiv.symm_apply_apply]
  exact ContinuousLinearMap.finHomEquiv_symm_finHomCoev_apply y u i l

/-- Uncurrying `g : Y ⟶ hom A D` acts on a pure Kronecker vector `u ⊗ y` by applying the operator
`homFiberEquiv A D x (g.fiberMap x y)` to `u`. -/
theorem fiberMap_uncurry_mul (g : Y ⟶ hom A D) (x : B) (u : Fin A.rank → 𝕜)
    (y : Fin Y.rank → 𝕜) :
    (MonoidalClosed.uncurry (A := A) g).fiberMap x
        (fun k ↦ u (finProdFinEquiv.symm k).1 * y (finProdFinEquiv.symm k).2) =
      homFiberEquiv A D x (g.fiberMap x y) u := by
  have hev : (A ◁ g ≫ homEv A D).fiberMap x =
      (ContinuousLinearMap.finHomEv 𝕜 A.rank D.rank).comp
        ((ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜)).kronecker (g.fiberMap x)) := by
    rw [fiberMap_comp, fiberMap_whiskerLeft, fiberMap_homEv]
    rfl
  have hvec : ((ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜)).kronecker (g.fiberMap x))
      (fun k ↦ u (finProdFinEquiv.symm k).1 * y (finProdFinEquiv.symm k).2) =
      fun k ↦ u (finProdFinEquiv.symm k).1 * g.fiberMap x y (finProdFinEquiv.symm k).2 := by
    ext k
    obtain ⟨⟨i, r⟩, rfl⟩ := finProdFinEquiv.surjective k
    have hrow : (fun l ↦ u i * y l) = u i • y := rfl
    simp only [ContinuousLinearMap.kronecker_apply, ContinuousLinearMap.id_apply,
      Equiv.symm_apply_apply, hrow, map_smul, Pi.smul_apply, smul_eq_mul]
  refine (DFunLike.congr_fun hev _).trans ?_
  -- Align `(A ⊗ hom A D).rank` with `A.rank * (A.rank * D.rank)` across the unexposed monoidal
  -- tensor projection so `rw [hvec]` applies.
  change ContinuousLinearMap.finHomEv 𝕜 A.rank D.rank
    (((ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜)).kronecker (g.fiberMap x))
      (fun k ↦ u (finProdFinEquiv.symm k).1 * y (finProdFinEquiv.symm k).2)) =
    (ContinuousLinearEquiv.finHomEquiv 𝕜 A.rank D.rank).symm (g.fiberMap x y) u
  rw [hvec]
  exact ContinuousLinearMap.finHomEv_mul u (g.fiberMap x y)

/-- Under `homFiberEquiv`, the global section `MonoidalClosed.curry' f : 𝟙_ _ ⟶ hom A D` attached
to `f : A ⟶ D` evaluates at `1` to `f.fiberMap x`. -/
theorem homFiberEquiv_fiberMap_curry' (f : A ⟶ D) (x : B) :
    homFiberEquiv A D x
        ((MonoidalClosed.curry' f).fiberMap x (1 : Fin (𝟙_ (FiniteRankBundleCore 𝕜 B)).rank → 𝕜)) =
      f.fiberMap x := by
  ext u
  have h := homFiberEquiv_fiberMap_curry ((ρ_ A).hom ≫ f) x
    (1 : Fin (𝟙_ (FiniteRankBundleCore 𝕜 B)).rank → 𝕜) u
  have hρ : ((ρ_ A).hom ≫ f).fiberMap x =
      (f.fiberMap x).comp (ContinuousLinearEquiv.kroneckerRid 𝕜 A.rank).toContinuousLinearMap := by
    rw [fiberMap_comp, fiberMap_rightUnitor_hom]
    rfl
  refine h.trans ((DFunLike.congr_fun hρ _).trans ?_)
  -- Align `(A ⊗ 𝟙_ _).rank` with `A.rank * 1` across the unexposed `MonoidalCategoryStruct`
  -- projections so `kroneckerRid_apply` fires.
  change f.fiberMap x (ContinuousLinearEquiv.kroneckerRid 𝕜 A.rank
    (fun k : Fin (A.rank * 1) ↦ u (finProdFinEquiv.symm k).1 *
      (1 : Fin 1 → 𝕜) (finProdFinEquiv.symm k).2)) = f.fiberMap x u
  refine congrArg (f.fiberMap x) (funext fun i ↦ ?_)
  simp only [ContinuousLinearEquiv.kroneckerRid_apply, Equiv.symm_apply_apply, Pi.one_apply,
    mul_one]

/-- Under `homFiberEquiv`, the enriched identity `MonoidalClosed.id A : 𝟙_ _ ⟶ hom A A` evaluates
at `1` to the identity operator on every fibre. -/
theorem homFiberEquiv_fiberMap_monoidalClosed_id (A : FiniteRankBundleCore 𝕜 B) (x : B) :
    homFiberEquiv A A x
        ((MonoidalClosed.id A).fiberMap x (1 : Fin (𝟙_ (FiniteRankBundleCore 𝕜 B)).rank → 𝕜)) =
      ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜) := by
  rw [← MonoidalClosed.curry'_id, homFiberEquiv_fiberMap_curry', fiberMap_id]

/-- Under `homFiberEquiv`, the enriched composition `MonoidalClosed.comp A D C` acts on a pure
Kronecker pair `v ⊗ w` by operator composition. -/
theorem homFiberEquiv_fiberMap_monoidalClosed_comp (A D C : FiniteRankBundleCore 𝕜 B) (x : B)
    (v : Fin (A.rank * D.rank) → 𝕜) (w : Fin (D.rank * C.rank) → 𝕜) :
    homFiberEquiv A C x ((MonoidalClosed.comp A D C).fiberMap x
        (fun k ↦ v (finProdFinEquiv.symm k).1 * w (finProdFinEquiv.symm k).2)) =
      (homFiberEquiv D C x w).comp (homFiberEquiv A D x v) := by
  ext u
  have hcurry := homFiberEquiv_fiberMap_curry (MonoidalClosed.compTranspose A D C) x
    (fun k ↦ v (finProdFinEquiv.symm k).1 * w (finProdFinEquiv.symm k).2) u
  have hct : (MonoidalClosed.compTranspose A D C).fiberMap x =
      (ContinuousLinearMap.finHomEv 𝕜 D.rank C.rank).comp
        (((ContinuousLinearMap.finHomEv 𝕜 A.rank D.rank).kronecker
          (ContinuousLinearMap.id 𝕜 (Fin (D.rank * C.rank) → 𝕜))).comp
          (ContinuousLinearEquiv.kroneckerAssoc 𝕜 A.rank (A.rank * D.rank)
            (D.rank * C.rank)).symm.toContinuousLinearMap) := by
    -- Unfold `MonoidalClosed.compTranspose` from `ihom` to `hom` at default transparency.
    change ((α_ A (hom A D) (hom D C)).inv ≫ homEv A D ▷ hom D C ≫ homEv D C).fiberMap x = _
    simp only [fiberMap_comp, fiberMap_associator_inv, fiberMap_whiskerRight, fiberMap_homEv]
    rfl
  refine hcurry.trans ((DFunLike.congr_fun hct _).trans ?_)
  -- Align `(A ⊗ (hom A D ⊗ hom D C)).rank` with `A.rank * ((A.rank * D.rank) * (D.rank * C.rank))`
  -- across the unexposed `tensorObj` projection.
  change ContinuousLinearMap.finHomEv 𝕜 D.rank C.rank
    (((ContinuousLinearMap.finHomEv 𝕜 A.rank D.rank).kronecker
      (ContinuousLinearMap.id 𝕜 (Fin (D.rank * C.rank) → 𝕜)))
      ((ContinuousLinearEquiv.kroneckerAssoc 𝕜 A.rank (A.rank * D.rank) (D.rank * C.rank)).symm
        (fun k ↦ u (finProdFinEquiv.symm k).1 *
          (v (finProdFinEquiv.symm (finProdFinEquiv.symm k).2).1 *
            w (finProdFinEquiv.symm (finProdFinEquiv.symm k).2).2)))) = _
  exact ContinuousLinearMap.finHomEv_comp_kronecker_kroneckerAssoc_symm_mul u v w

/-- In matching frames centred at `a`, the Hom-bundle coordinate expression of
`homFiberEquiv A D x v` is the operator represented by the chart coordinates of `v` in
`(hom A D).core.localTriv a`. -/
theorem homFiberEquiv_inCoordinates (A D : FiniteRankBundleCore 𝕜 B) (a x : B)
    (hxA : x ∈ A.core.baseSet a) (hxD : x ∈ D.core.baseSet a)
    (v : (hom A D).core.Fiber x) :
    ContinuousLinearMap.inCoordinates (Fin A.rank → 𝕜) A.core.Fiber
        (Fin D.rank → 𝕜) D.core.Fiber a x a x (homFiberEquiv A D x v) =
      homFiberEquiv A D x (((hom A D).core.localTriv a ⟨x, v⟩).2) := by
  have hbA : x ∈ A.core.baseSet (A.core.indexAt a) := by rwa [A.indexAt_eq]
  have hbD : x ∈ D.core.baseSet (D.core.indexAt a) := by rwa [D.indexAt_eq]
  rw [ContinuousLinearMap.inCoordinates, D.core.trivializationAt_continuousLinearMapAt hbD,
    A.core.trivializationAt_symmL hbA]
  simp only [A.indexAt_eq, D.indexAt_eq, VectorBundleCore.localTriv_apply, (hom A D).indexAt_eq,
    coordChange_hom, homFiberEquiv]
  exact (ContinuousLinearMap.finHomEquiv_symm_finHomMap _ _ v).symm

theorem localTriv_homFiberEquiv_symm (A D : FiniteRankBundleCore 𝕜 B) (a x : B)
    (hxA : x ∈ A.core.baseSet a) (hxD : x ∈ D.core.baseSet a)
    (f : A.core.Fiber x →L[𝕜] D.core.Fiber x) :
    ((hom A D).core.localTriv a ⟨x, (homFiberEquiv A D x).symm f⟩).2 =
      ContinuousLinearEquiv.finHomEquiv 𝕜 A.rank D.rank
        (ContinuousLinearMap.inCoordinates (Fin A.rank → 𝕜) A.core.Fiber
          (Fin D.rank → 𝕜) D.core.Fiber a x a x f) := by
  apply (ContinuousLinearEquiv.finHomEquiv 𝕜 A.rank D.rank).symm.injective
  have h := homFiberEquiv_inCoordinates A D a x hxA hxD ((homFiberEquiv A D x).symm f)
  rw [ContinuousLinearEquiv.apply_symm_apply] at h
  rw [ContinuousLinearEquiv.symm_apply_apply]
  exact h.symm

/-- The reconstructed total space of `hom A D` is homeomorphic to Mathlib's Hom bundle between `A`
and `D`, covering the identity on the base and acting by `homFiberEquiv` on each fibre. -/
def homTotalSpaceHomeomorph (A D : FiniteRankBundleCore 𝕜 B) :
    (hom A D).core.TotalSpace ≃ₜ
      TotalSpace ((Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜))
        (fun x => A.core.Fiber x →L[𝕜] D.core.Fiber x) where
  toFun p := ⟨p.proj, homFiberEquiv A D p.proj p.2⟩
  invFun p := ⟨p.proj, (homFiberEquiv A D p.proj).symm p.2⟩
  left_inv p := by simp
  right_inv p := by simp
  continuous_toFun := by
    refine continuous_iff_continuousAt.2 fun p => ?_
    rw [continuousAt_hom_bundle]
    refine ⟨(hom A D).core.continuous_proj.continuousAt, ?_⟩
    have hp : p ∈ ((hom A D).core.localTriv p.proj).source :=
      ((hom A D).core.mem_localTriv_source p.proj p).2 ((hom A D).core.mem_baseSet_at p.proj)
    have hU := ((hom A D).core.localTriv p.proj).open_source.mem_nhds hp
    have hc := (((hom A D).core.localTriv p.proj).continuousOn.continuousAt hU).snd
    refine ((homFiberEquiv A D p.proj).continuous.continuousAt.comp hc).congr ?_
    filter_upwards [hU] with q hq
    have hmem := ((hom A D).core.mem_localTriv_source p.proj q).1 hq
    exact (homFiberEquiv_inCoordinates A D p.proj q.proj hmem.1 hmem.2 q.2).symm
  continuous_invFun := by
    refine continuous_iff_continuousAt.2 fun p => ?_
    rw [FiberBundle.continuousAt_totalSpace]
    have hproj : ContinuousAt
        (TotalSpace.proj : TotalSpace ((Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜))
          (fun x => A.core.Fiber x →L[𝕜] D.core.Fiber x) → B) p :=
      (FiberBundle.continuous_proj _ _).continuousAt
    refine ⟨hproj, ?_⟩
    have hid : ContinuousAt
        (id : TotalSpace ((Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜))
          (fun x => A.core.Fiber x →L[𝕜] D.core.Fiber x) → _) p := continuousAt_id
    rw [continuousAt_hom_bundle] at hid
    have hmem₀ : p.proj ∈ (hom A D).core.baseSet p.proj := (hom A D).mem_baseSet_self p.proj
    have hV := hproj.preimage_mem_nhds (((hom A D).core.isOpen_baseSet p.proj).mem_nhds hmem₀)
    have hc := (ContinuousLinearEquiv.finHomEquiv 𝕜 A.rank D.rank).continuous.continuousAt.comp
      hid.2
    refine hc.congr ?_
    filter_upwards [hV] with q hq
    dsimp only [Function.comp_apply, id_eq]
    rw [(hom A D).trivializationAt_core]
    exact (localTriv_homFiberEquiv_symm A D p.proj q.proj hq.1 hq.2 q.2).symm

@[simp] theorem homTotalSpaceHomeomorph_apply (A D : FiniteRankBundleCore 𝕜 B)
    (p : (hom A D).core.TotalSpace) :
    homTotalSpaceHomeomorph A D p = ⟨p.proj, homFiberEquiv A D p.proj p.2⟩ := (rfl)

@[simp] theorem homTotalSpaceHomeomorph_symm_apply (A D : FiniteRankBundleCore 𝕜 B)
    (p : TotalSpace ((Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜))
      (fun x => A.core.Fiber x →L[𝕜] D.core.Fiber x)) :
    (homTotalSpaceHomeomorph A D).symm p = ⟨p.proj, (homFiberEquiv A D p.proj).symm p.2⟩ := (rfl)

/-- `homTotalSpaceHomeomorph` intertwines `homHom f g` on the internal Hom core with precomposition
by `f.fiberMap` and postcomposition by `g.fiberMap` on Mathlib's Hom bundle. -/
theorem homTotalSpaceHomeomorph_naturality (f : A' ⟶ A) (g : D ⟶ D')
    (p : (hom A D).core.TotalSpace) :
    homTotalSpaceHomeomorph A' D' ((homHom f g).totalSpaceMap p) =
      ⟨p.proj, (g.fiberMap p.proj).comp
        (((homTotalSpaceHomeomorph A D p).2).comp (f.fiberMap p.proj))⟩ := by
  rcases p with ⟨x, v⟩
  rw [CoordinateHom.totalSpaceMap_mk, homTotalSpaceHomeomorph_apply, homTotalSpaceHomeomorph_apply]
  exact congrArg
    (TotalSpace.mk' ((Fin A'.rank → 𝕜) →L[𝕜] (Fin D'.rank → 𝕜)) x)
    (homFiberEquiv_fiberMap_homHom f g x v)

/-! ### Distributivity over Whitney sums -/

section WhitneySum

/-- Internal Hom distributes over Whitney sums in the target:
`hom A (whitneySum D D') ≅ whitneySum (hom A D) (hom A D')`. -/
def homWhitneySumIso (A D D' : FiniteRankBundleCore 𝕜 B) :
    hom A (whitneySum D D') ≅ whitneySum (hom A D) (hom A D') where
  hom := whitneyLift (homHom (𝟙 A) (whitneyFst D D')) (homHom (𝟙 A) (whitneySnd D D'))
  inv := whitneyDesc (homHom (𝟙 A) (whitneyInl D D')) (homHom (𝟙 A) (whitneyInr D D'))
  hom_inv_id := by
    rw [whitneyLift_desc, homHom_comp_homHom, homHom_comp_homHom, Category.id_comp,
      ← homHom_add, whitney_total, id_homHom_id]
  inv_hom_id := whitneySum_hom_ext (whitneySum_hom_ext' (by simp) (by simp))
    (whitneySum_hom_ext' (by simp) (by simp))

@[simp] theorem homWhitneySumIso_hom (A D D' : FiniteRankBundleCore 𝕜 B) :
    (homWhitneySumIso A D D').hom =
      whitneyLift (homHom (𝟙 A) (whitneyFst D D')) (homHom (𝟙 A) (whitneySnd D D')) := (rfl)

@[simp] theorem homWhitneySumIso_inv (A D D' : FiniteRankBundleCore 𝕜 B) :
    (homWhitneySumIso A D D').inv =
      whitneyDesc (homHom (𝟙 A) (whitneyInl D D')) (homHom (𝟙 A) (whitneyInr D D')) := (rfl)

@[reassoc]
theorem homHom_homWhitneySumIso_hom (f : A' ⟶ A) (g : D ⟶ Y) (g' : D' ⟶ Y') :
    homHom f (whitneyMap g g') ≫ (homWhitneySumIso A' Y Y').hom =
      (homWhitneySumIso A D D').hom ≫ whitneyMap (homHom f g) (homHom f g') :=
  whitneySum_hom_ext (by simp) (by simp)

/-- Internal Hom distributes over Whitney sums in the source:
`hom (whitneySum A A') D ≅ whitneySum (hom A D) (hom A' D)`. -/
def whitneySumHomIso (A A' D : FiniteRankBundleCore 𝕜 B) :
    hom (whitneySum A A') D ≅ whitneySum (hom A D) (hom A' D) where
  hom := whitneyLift (homHom (whitneyInl A A') (𝟙 D)) (homHom (whitneyInr A A') (𝟙 D))
  inv := whitneyDesc (homHom (whitneyFst A A') (𝟙 D)) (homHom (whitneySnd A A') (𝟙 D))
  hom_inv_id := by
    rw [whitneyLift_desc, homHom_comp_homHom, homHom_comp_homHom, Category.comp_id,
      ← add_homHom, whitney_total, id_homHom_id]
  inv_hom_id := whitneySum_hom_ext (whitneySum_hom_ext' (by simp) (by simp))
    (whitneySum_hom_ext' (by simp) (by simp))

@[simp] theorem whitneySumHomIso_hom (A A' D : FiniteRankBundleCore 𝕜 B) :
    (whitneySumHomIso A A' D).hom =
      whitneyLift (homHom (whitneyInl A A') (𝟙 D)) (homHom (whitneyInr A A') (𝟙 D)) := (rfl)

@[simp] theorem whitneySumHomIso_inv (A A' D : FiniteRankBundleCore 𝕜 B) :
    (whitneySumHomIso A A' D).inv =
      whitneyDesc (homHom (whitneyFst A A') (𝟙 D)) (homHom (whitneySnd A A') (𝟙 D)) := (rfl)

@[reassoc]
theorem homHom_whitneySumHomIso_hom (f : Y ⟶ A) (f' : Y' ⟶ A') (g : D ⟶ D') :
    homHom (whitneyMap f f') g ≫ (whitneySumHomIso Y Y' D').hom =
      (whitneySumHomIso A A' D).hom ≫ whitneyMap (homHom f g) (homHom f' g) :=
  whitneySum_hom_ext (by simp) (by simp)

end WhitneySum

end General

/-! ### Base-change compatibility -/

section Pullback

universe u v w

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜]
  {X : Type u} {Y : Type w} [TopologicalSpace X] [TopologicalSpace Y]

/-- Pulling back commutes strictly with tensor products of finite-rank cores. -/
@[simp] theorem pullback_tensor (A D : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y)) :
    (A ⊗ D).pullback f = A.pullback f ⊗ D.pullback f := (rfl)

/-- Pulling back commutes strictly with internal Hom cores. -/
@[simp] theorem pullback_hom (A D : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y)) :
    (hom A D).pullback f = hom (A.pullback f) (D.pullback f) := (rfl)

/-- Pulling back commutes with `tensorHom` on bundle morphisms. -/
@[simp] theorem pullbackMap_tensorHom {A A' D D' : FiniteRankBundleCore 𝕜 Y}
    (a : A ⟶ A') (b : D ⟶ D') (f : C(X, Y)) :
    pullbackMap (a ⊗ₘ b) f = pullbackMap a f ⊗ₘ pullbackMap b f :=
  hom_ext fun x => (fiberMap_pullbackMap (a ⊗ₘ b) f x).trans <|
    (fiberMap_tensorHom_monoidal a b (f x)).trans <| by
      rw [← fiberMap_pullbackMap a f x, ← fiberMap_pullbackMap b f x]
      exact (fiberMap_tensorHom_monoidal (pullbackMap a f) (pullbackMap b f) x).symm

/-- Pulling back commutes with `homHom` on bundle morphisms. -/
@[simp] theorem pullbackMap_homHom {A A' D D' : FiniteRankBundleCore 𝕜 Y}
    (a : A' ⟶ A) (b : D ⟶ D') (f : C(X, Y)) :
    pullbackMap (homHom a b) f = homHom (pullbackMap a f) (pullbackMap b f) :=
  hom_ext fun x => (fiberMap_pullbackMap (homHom a b) f x).trans <|
    (fiberMap_homHom a b (f x)).trans <| by
      rw [← fiberMap_pullbackMap a f x, ← fiberMap_pullbackMap b f x]
      exact (fiberMap_homHom (pullbackMap a f) (pullbackMap b f) x).symm

/-- Pulling back commutes with the evaluation morphism `homEv`. -/
@[simp] theorem pullbackMap_homEv (A D : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y)) :
    pullbackMap (homEv A D) f = homEv (A.pullback f) (D.pullback f) :=
  hom_ext fun x => (fiberMap_pullbackMap (homEv A D) f x).trans <|
    (fiberMap_homEv A D (f x)).trans (fiberMap_homEv (A.pullback f) (D.pullback f) x).symm

/-- Pulling back commutes with the coevaluation morphism `homCoev`. -/
@[simp] theorem pullbackMap_homCoev (A D : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y)) :
    pullbackMap (homCoev A D) f = homCoev (A.pullback f) (D.pullback f) :=
  hom_ext fun x => (fiberMap_pullbackMap (homCoev A D) f x).trans <|
    (fiberMap_homCoev A D (f x)).trans (fiberMap_homCoev (A.pullback f) (D.pullback f) x).symm

end Pullback

/-! ### Comparison with dual-tensor cores over a complete scalar field -/

section Dual

variable {𝕜 B : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [TopologicalSpace B]
  {A A' D D' : FiniteRankBundleCore 𝕜 B}

/-- Over a complete scalar field, `A.dual ⊗ D` is isomorphic to `hom A D` by the identity
coordinate equivalence on every fibre, since `finHomMap` equals `piTranspose` tensored with the
target transition. -/
noncomputable def dualTensorIsoHom (A D : FiniteRankBundleCore 𝕜 B) :
    A.dual ⊗ D ≅ hom A D :=
  constIso (fun _ => rfl) (ContinuousLinearEquiv.refl 𝕜 (Fin (A.rank * D.rank) → 𝕜))
    fun i j x _ _ => by
      ext v k
      -- Unfold the unexposed `MonoidalCategoryStruct.tensorObj` projection inside `(A.dual ⊗ D)`.
      change ((A.core.coordChange j i x).piTranspose.kronecker (D.core.coordChange i j x)) v k =
        (A.core.coordChange j i x).finHomMap (D.core.coordChange i j x) v k
      rw [ContinuousLinearMap.finHomMap_eq_piTranspose_kronecker]

@[simp] theorem fiberMap_dualTensorIsoHom_hom (A D : FiniteRankBundleCore 𝕜 B) (x : B) :
    (dualTensorIsoHom A D).hom.fiberMap x =
      ContinuousLinearMap.id 𝕜 (Fin (A.rank * D.rank) → 𝕜) :=
  fiberMap_constIso_hom _ _ _ x

@[simp] theorem fiberMap_dualTensorIsoHom_inv (A D : FiniteRankBundleCore 𝕜 B) (x : B) :
    (dualTensorIsoHom A D).inv.fiberMap x =
      ContinuousLinearMap.id 𝕜 (Fin (A.rank * D.rank) → 𝕜) :=
  fiberMap_constIso_inv _ _ _ x

/-- Naturality of `dualTensorIsoHom` with respect to `dualMap f ⊗ₘ g` and `homHom f g`. -/
@[reassoc (attr := simp)]
theorem dualTensorIsoHom_naturality (f : A' ⟶ A) (g : D ⟶ D') :
    (dualMap f ⊗ₘ g) ≫ (dualTensorIsoHom A' D').hom =
      (dualTensorIsoHom A D).hom ≫ homHom f g :=
  hom_ext fun x => by
    simp only [fiberMap_comp, fiberMap_tensorHom_monoidal, fiberMap_dualMap,
      fiberMap_dualTensorIsoHom_hom, fiberMap_homHom,
      ContinuousLinearMap.finHomMap_eq_piTranspose_kronecker]
    exact (ContinuousLinearMap.id_comp _).trans (ContinuousLinearMap.comp_id _).symm

/-- Internal Hom into the monoidal unit `𝟙_ _` is isomorphic to the dual core `A.dual`, via the
right Kronecker unitor `kroneckerRid`. -/
noncomputable def homUnitIsoDual (A : FiniteRankBundleCore 𝕜 B) :
    hom A (𝟙_ (FiniteRankBundleCore 𝕜 B)) ≅ A.dual :=
  constIso (fun _ => Set.inter_univ _) (ContinuousLinearEquiv.kroneckerRid 𝕜 A.rank)
    fun i j x _ _ => by
      -- Unfold the unexposed `MonoidalCategoryStruct.tensorUnit` projection inside `𝟙_ _`.
      change (ContinuousLinearEquiv.kroneckerRid 𝕜 A.rank).toContinuousLinearMap.comp
          ((A.core.coordChange j i x).finHomMap (ContinuousLinearMap.id 𝕜 (Fin 1 → 𝕜))) =
        (A.core.coordChange j i x).piTranspose.comp
          (ContinuousLinearEquiv.kroneckerRid 𝕜 A.rank).toContinuousLinearMap
      rw [ContinuousLinearMap.finHomMap_eq_piTranspose_kronecker]
      exact ContinuousLinearMap.kroneckerRid_comp_kronecker _

@[simp] theorem fiberMap_homUnitIsoDual_hom (A : FiniteRankBundleCore 𝕜 B) (x : B) :
    (homUnitIsoDual A).hom.fiberMap x =
      (ContinuousLinearEquiv.kroneckerRid 𝕜 A.rank).toContinuousLinearMap :=
  fiberMap_constIso_hom _ _ _ x

@[simp] theorem fiberMap_homUnitIsoDual_inv (A : FiniteRankBundleCore 𝕜 B) (x : B) :
    (homUnitIsoDual A).inv.fiberMap x =
      (ContinuousLinearEquiv.kroneckerRid 𝕜 A.rank).symm.toContinuousLinearMap :=
  fiberMap_constIso_inv _ _ _ x

@[reassoc (attr := simp)]
theorem homUnitIsoDual_naturality (f : A' ⟶ A) :
    homHom f (𝟙 (𝟙_ (FiniteRankBundleCore 𝕜 B))) ≫ (homUnitIsoDual A').hom =
      (homUnitIsoDual A).hom ≫ dualMap f :=
  hom_ext fun x => by
    simp only [fiberMap_comp, fiberMap_homHom, fiberMap_id, fiberMap_homUnitIsoDual_hom,
      fiberMap_dualMap, ContinuousLinearMap.finHomMap_eq_piTranspose_kronecker]
    exact ContinuousLinearMap.kroneckerRid_comp_kronecker _

end Dual

end TauCeti.FiniteRankBundleCore
