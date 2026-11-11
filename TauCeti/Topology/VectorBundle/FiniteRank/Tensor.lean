/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Basic
public import TauCeti.Analysis.Normed.Operator.Kronecker

/-!
# Tensor products of finite-rank bundle cores

The tensor product of two point-indexed cores of ranks `a` and `b` has rank `a * b`, the
intersections of the two charts at each point, and the Kronecker products of the two
transition maps as its transitions (`ContinuousLinearMap.kronecker`, with coordinate pair
`(i, j)` at index `finProdFinEquiv (i, j)`). The mixed-product law for Kronecker products is
exactly the cocycle condition, so this is again a Mathlib `VectorBundleCore`.

Two bundle morphisms have the Kronecker product of their chart operators as tensor product,
a continuous fibrewise linear map whose fibre maps are the Kronecker products of the fibre maps
(`FiniteRankBundleCore.fiberMap_tensorHom`). The construction is a bifunctor: it preserves
identities and composition, is additive in each variable, and preserves isomorphisms.
The base is arbitrary, and the scalar field need not be complete.

The construction uses Mathlib's coordinate cores and the coordinate morphisms
`VectorBundleCore.CoordinateHom`.
-/

public section

open CategoryTheory VectorBundleCore Set

namespace TauCeti.FiniteRankBundleCore

variable {𝕜 B : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]

/-- The tensor product, with intersected charts and Kronecker products of the transitions. -/
-- Expose the rank projection so the dependent model reduces to the product coordinates.
@[expose]
def tensor (A D : FiniteRankBundleCore 𝕜 B) : FiniteRankBundleCore 𝕜 B where
  rank := A.rank * D.rank
  core :=
    { baseSet := fun i => A.core.baseSet i ∩ D.core.baseSet i
      isOpen_baseSet := fun i => (A.core.isOpen_baseSet i).inter (D.core.isOpen_baseSet i)
      indexAt := id
      mem_baseSet_at := fun x => by
        simpa only [mem_inter_iff, id_eq, A.indexAt_eq, D.indexAt_eq] using
          And.intro (A.core.mem_baseSet_at x) (D.core.mem_baseSet_at x)
      coordChange := fun i j x =>
        (A.core.coordChange i j x).kronecker (D.core.coordChange i j x)
      coordChange_self := fun i x hx v => by
        rw [A.core.coordChange_self_eq_id hx.1, D.core.coordChange_self_eq_id hx.2,
          ContinuousLinearMap.id_kronecker_id, ContinuousLinearMap.id_apply]
      continuousOn_coordChange := fun i j =>
        ((A.core.continuousOn_coordChange i j).mono
          (inter_subset_inter inter_subset_left inter_subset_left)).clm_kronecker
          ((D.core.continuousOn_coordChange i j).mono
            (inter_subset_inter inter_subset_right inter_subset_right))
      coordChange_comp := fun i j k x hx v => by
        rw [← ContinuousLinearMap.comp_apply, ContinuousLinearMap.kronecker_comp_kronecker,
          A.core.coordChange_linear_comp i j k x ⟨⟨hx.1.1.1, hx.1.2.1⟩, hx.2.1⟩,
          D.core.coordChange_linear_comp i j k x ⟨⟨hx.1.1.2, hx.1.2.2⟩, hx.2.2⟩] }
  indexAt_eq := fun _ => rfl

@[simp] theorem rank_tensor (A D : FiniteRankBundleCore 𝕜 B) :
    (tensor A D).rank = A.rank * D.rank := (rfl)

@[simp] theorem localTriv_baseSet_tensor (A D : FiniteRankBundleCore 𝕜 B) (i : B) :
    ((tensor A D).core.localTriv i).baseSet = A.core.baseSet i ∩ D.core.baseSet i := (rfl)

/-- The transitions of the tensor product are the Kronecker products of the transitions. -/
@[simp] theorem coordChange_tensor (A D : FiniteRankBundleCore 𝕜 B) (i j x : B) :
    (tensor A D).core.coordChange i j x =
      (A.core.coordChange i j x).kronecker (D.core.coordChange i j x) := (rfl)

variable {A A' A'' D D' D'' : FiniteRankBundleCore 𝕜 B}

/-- Changing frames in a tensor product acts separately on the two operator factors.
The formula holds even outside the chart domains, using the core transition operators there. -/
@[simp]
theorem inChartCoordinates_tensor_kronecker (A A' D D' : FiniteRankBundleCore 𝕜 B)
    (f : (Fin A.rank → 𝕜) →L[𝕜] (Fin A'.rank → 𝕜))
    (g : (Fin D.rank → 𝕜) →L[𝕜] (Fin D'.rank → 𝕜)) (i j x : B) :
    (tensor A D).core.inChartCoordinates (tensor A' D').core i j x (f.kronecker g) =
      (A.core.inChartCoordinates A'.core i j x f).kronecker
        (D.core.inChartCoordinates D'.core i j x g) := by
  -- Normalize the dependent coordinate spaces; the tensor core has indexAt = id and
  -- coordChange = the Kronecker product, which identifies the first frame-change expression.
  dsimp +instances only [tensor]
  calc
    _ = ((A'.core.coordChange x j x).kronecker (D'.core.coordChange x j x)).comp
        ((f.kronecker g).comp
          ((A.core.coordChange i x x).kronecker (D.core.coordChange i x x))) := by
      ext v
      simp only [VectorBundleCore.inChartCoordinates_apply, ContinuousLinearMap.comp_apply]
      rfl
    _ = ((A'.core.coordChange x j x).comp (f.comp (A.core.coordChange i x x))).kronecker
        ((D'.core.coordChange x j x).comp (g.comp (D.core.coordChange i x x))) := by
      rw [ContinuousLinearMap.kronecker_comp_kronecker,
        ContinuousLinearMap.kronecker_comp_kronecker]
    _ = _ := by
      congr 1 <;> ext v <;>
        simp only [VectorBundleCore.inChartCoordinates_apply, ContinuousLinearMap.comp_apply,
          indexAt_eq]

/-- The tensor product of two bundle maps, given in charts by Kronecker products of the chart
operators. -/
def tensorHom (f : A ⟶ A') (g : D ⟶ D') : tensor A D ⟶ tensor A' D' where
  operator i j :=
    ⟨fun x => (f.operator i j ⟨x.1, x.2.1.1, x.2.2.1⟩).kronecker
        (g.operator i j ⟨x.1, x.2.1.2, x.2.2.2⟩),
      ((f.operator i j).continuous.comp (continuous_subtype_val.subtype_mk _)).clm_kronecker
        ((g.operator i j).continuous.comp (continuous_subtype_val.subtype_mk _))⟩
  compatible i i' j j' x hi hi' hj hj' v := by
    -- Both sides are Kronecker products; compare the two factors as operators.
    change ((A'.core.coordChange j j' x).kronecker (D'.core.coordChange j j' x)).comp
        ((f.operator i j ⟨x, hi.1, hj.1⟩).kronecker (g.operator i j ⟨x, hi.2, hj.2⟩)) v =
      ((f.operator i' j' ⟨x, hi'.1, hj'.1⟩).kronecker (g.operator i' j' ⟨x, hi'.2, hj'.2⟩)).comp
        ((A.core.coordChange i i' x).kronecker (D.core.coordChange i i' x)) v
    rw [ContinuousLinearMap.kronecker_comp_kronecker, ContinuousLinearMap.kronecker_comp_kronecker,
      f.coordChange_comp_operator i i' j j' x hi.1 hi'.1 hj.1 hj'.1,
      g.coordChange_comp_operator i i' j j' x hi.2 hi'.2 hj.2 hj'.2]

/-- On every fibre, the tensor product of two bundle maps is the Kronecker product of their
fibre maps. -/
@[simp] theorem fiberMap_tensorHom (f : A ⟶ A') (g : D ⟶ D') (x : B) :
    (tensorHom f g).fiberMap x = (f.fiberMap x).kronecker (g.fiberMap x) := by
  calc
    _ = (f.operator x x ⟨x, A.mem_baseSet_self x, A'.mem_baseSet_self x⟩).kronecker
        (g.operator x x ⟨x, D.mem_baseSet_self x, D'.mem_baseSet_self x⟩) :=
      CoordinateHom.fiberMap_def _ x
    _ = _ := by rw [operator_self, operator_self]

/-- The tensor product of two identity morphisms is the identity. -/
@[simp] theorem id_tensorHom_id (A D : FiniteRankBundleCore 𝕜 B) :
    tensorHom (𝟙 A) (𝟙 D) = 𝟙 (tensor A D) := by
  apply hom_ext
  intro x
  rw [fiberMap_tensorHom, fiberMap_id, fiberMap_id, fiberMap_id]
  exact ContinuousLinearMap.id_kronecker_id

-- In the following proofs the fibre maps of tensor products have the product coordinates as
-- model, which the Kronecker-product lemmas state for `Fin (A.rank * D.rank) → 𝕜`; the exposed
-- rank projection identifies the two models.

/-- Tensor products of morphisms compose factorwise: composing in both factors simultaneously
commutes with forming the tensor product. -/
@[reassoc (attr := simp)] theorem tensorHom_comp_tensorHom (f : A ⟶ A') (f' : A' ⟶ A'')
    (g : D ⟶ D') (g' : D' ⟶ D'') :
    tensorHom f g ≫ tensorHom f' g' = tensorHom (f ≫ f') (g ≫ g') := by
  apply hom_ext
  intro x
  rw [fiberMap_comp, fiberMap_tensorHom, fiberMap_tensorHom, fiberMap_tensorHom, fiberMap_comp,
    fiberMap_comp]
  exact ContinuousLinearMap.kronecker_comp_kronecker _ _ _ _

@[simp] theorem add_tensorHom (f f' : A ⟶ A') (g : D ⟶ D') :
    tensorHom (f + f') g = tensorHom f g + tensorHom f' g := by
  apply hom_ext
  intro x
  rw [fiberMap_add, fiberMap_tensorHom, fiberMap_tensorHom, fiberMap_tensorHom, fiberMap_add]
  exact ContinuousLinearMap.add_kronecker _ _ _

@[simp] theorem tensorHom_add (f : A ⟶ A') (g g' : D ⟶ D') :
    tensorHom f (g + g') = tensorHom f g + tensorHom f g' := by
  apply hom_ext
  intro x
  rw [fiberMap_add, fiberMap_tensorHom, fiberMap_tensorHom, fiberMap_tensorHom, fiberMap_add]
  exact ContinuousLinearMap.kronecker_add _ _ _

@[simp] theorem zero_tensorHom (g : D ⟶ D') : tensorHom (0 : A ⟶ A') g = 0 := by
  apply hom_ext
  intro x
  rw [fiberMap_tensorHom, CoordinateHom.fiberMap_zero, CoordinateHom.fiberMap_zero]
  exact ContinuousLinearMap.zero_kronecker _

@[simp] theorem tensorHom_zero (f : A ⟶ A') : tensorHom f (0 : D ⟶ D') = 0 := by
  apply hom_ext
  intro x
  rw [fiberMap_tensorHom, CoordinateHom.fiberMap_zero, CoordinateHom.fiberMap_zero]
  exact ContinuousLinearMap.kronecker_zero _

@[simp] theorem neg_tensorHom (f : A ⟶ A') (g : D ⟶ D') :
    tensorHom (-f) g = -tensorHom f g := by
  rw [eq_neg_iff_add_eq_zero, ← add_tensorHom, neg_add_cancel, zero_tensorHom]

@[simp] theorem tensorHom_neg (f : A ⟶ A') (g : D ⟶ D') :
    tensorHom f (-g) = -tensorHom f g := by
  rw [eq_neg_iff_add_eq_zero, ← tensorHom_add, neg_add_cancel, tensorHom_zero]

/-- The tensor product of two bundle isomorphisms is an isomorphism. -/
instance (f : A ⟶ A') (g : D ⟶ D') [IsIso f] [IsIso g] : IsIso (tensorHom f g) :=
  ⟨tensorHom (inv f) (inv g), by simp, by simp⟩

end TauCeti.FiniteRankBundleCore
