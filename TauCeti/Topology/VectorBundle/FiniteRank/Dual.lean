/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.ModelEquiv
public import TauCeti.Topology.VectorBundle.FiniteRank.Pullback
public import TauCeti.Topology.VectorBundle.FiniteRank.Monoidal
public import TauCeti.Analysis.Normed.Operator.PiTranspose
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Preadditive.Opposite
public import Mathlib.Topology.VectorBundle.Constructions
import TauCeti.Analysis.Normed.Module.FiniteDimension
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Pi.Prod

/-!
# Duals of finite-rank bundle cores

The dual of a point-indexed core `A` keeps the charts of `A`; its transition from chart `i` to
chart `j` is the transpose of the transition of `A` from `j` to `i`, computed by
`ContinuousLinearMap.piTranspose`. A coordinate vector `w` in a dual chart stands for the
functional `v ↦ ∑ k, v k * w k` on the corresponding chart of `A`.

A bundle map `f : A ⟶ D` has the transposed bundle map `dualMap f : D.dual ⟶ A.dual`, whose
fibre maps are the transposes of those of `f`. This gives the contravariant additive functor
`dualFunctor`. Transposition is an involution, so the double dual is naturally isomorphic to
the identity (`dualDualNatIso`), with identity fibre maps, and `dualFunctor` is an
anti-equivalence. The dual of a trivial core is the trivial core of the same rank, the
transposed Whitney-sum inclusions and projections identify the dual of a Whitney sum with the
Whitney sum of the duals (`dualWhitneySumIso`), dualizing commutes strictly with pullback
along continuous maps of bases (`pullback_dual`, `pullbackMap_dualMap`,
`dualFunctor_comp_pullbackFunctor`), and for any rank-one core `A` the tensor product `A.dual ⊗ A`
is canonically isomorphic to the monoidal unit (`dualTensorIsoUnit`).

`dualTotalSpaceHomeomorph` identifies the reconstructed total space of `A.dual` with the
total space of Mathlib's dual bundle of `A`, the bundle of continuous linear maps from the
fibres of `A` to the trivial line, over the identity of the base. Under this identification
`dualMap f` is precomposition with `f` (`dualFiberEquiv_fiberMap_dualMap`). Thus the transposed
chart transitions present the actual dual bundle, with its Hom-bundle topology.

For an actual vector bundle `V` presented as `ofBundle 𝕜 e V` along a model coordinate
equivalence `e : F ≃L[𝕜] (Fin r → 𝕜)`, `ofBundleDualTotalSpaceHomeomorph e V` identifies
`(ofBundle 𝕜 e V).dual` with Mathlib's dual bundle `fun x ↦ V x →L[𝕜] 𝕜`, compatibly with
changes of coordinate equivalence (`ofBundleDualFiberEquiv_dualMap_changeIso`).

The scalar field is assumed complete, as for Mathlib's identification
`ContinuousLinearEquiv.piRing` of a coordinate space with its continuous dual. The base is
arbitrary, and zero ranks and the empty base are included.

For the dual bundle and its transition functions see Milnor–Stasheff, *Characteristic Classes*,
§3.
-/

public section

open Bundle CategoryTheory CategoryTheory.Limits VectorBundleCore Opposite
open scoped MonoidalCategory

namespace TauCeti.FiniteRankBundleCore

variable {𝕜 B : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [TopologicalSpace B]

/-- The dual of a finite-rank core: the same charts, with transposed reverse transitions. -/
-- Expose the rank projection so the dependent model reduces to the original coordinates.
@[expose]
noncomputable def dual (A : FiniteRankBundleCore 𝕜 B) : FiniteRankBundleCore 𝕜 B where
  rank := A.rank
  core :=
    { baseSet := A.core.baseSet
      isOpen_baseSet := A.core.isOpen_baseSet
      indexAt := id
      mem_baseSet_at := fun x => by simpa only [id_eq, A.indexAt_eq] using A.core.mem_baseSet_at x
      coordChange := fun i j x => (A.core.coordChange j i x).piTranspose
      coordChange_self := fun i x hx v => by
        -- The core axiom is pointwise; lift it by extensionality to an operator equality so it
        -- can be rewritten beneath `piTranspose`.
        rw [show A.core.coordChange i i x = ContinuousLinearMap.id 𝕜 _ from
          ContinuousLinearMap.ext (A.core.coordChange_self i x hx),
          ContinuousLinearMap.piTranspose_id, ContinuousLinearMap.id_apply]
      continuousOn_coordChange := fun i j =>
        ((A.core.continuousOn_coordChange j i).mono
          fun _ (hx : _ ∈ A.core.baseSet i ∩ A.core.baseSet j) => ⟨hx.2, hx.1⟩).piTranspose
      coordChange_comp := fun i j k x hx v => by
        rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.piTranspose_comp]
        congr 2
        exact ContinuousLinearMap.ext
          (A.core.coordChange_comp k j i x ⟨⟨hx.2, hx.1.2⟩, hx.1.1⟩) }
  indexAt_eq := fun _ => rfl

@[simp] theorem rank_dual (A : FiniteRankBundleCore 𝕜 B) : A.dual.rank = A.rank := (rfl)

/-- The dual has the same charts as the original core. -/
@[simp] theorem localTriv_baseSet_dual (A : FiniteRankBundleCore 𝕜 B) (i : B) :
    (A.dual.core.localTriv i).baseSet = A.core.baseSet i := (rfl)

/-- The transition of the dual from chart `i` to chart `j` is the transpose of the transition
of the original core from `j` to `i`. -/
@[simp] theorem coordChange_dual (A : FiniteRankBundleCore 𝕜 B) (i j x : B) :
    A.dual.core.coordChange i j x = (A.core.coordChange j i x).piTranspose := (rfl)

/-- The dual of a trivial core is trivial. -/
@[simp] theorem dual_trivial (n : ℕ) : (trivial 𝕜 B n).dual = trivial 𝕜 B n := by
  simp only [dual, trivial, ContinuousLinearMap.piTranspose_id]
  -- The remaining fields are the same data; only proof fields and binder names differ.
  rfl

variable {A D C : FiniteRankBundleCore 𝕜 B}

/-- The transpose of a bundle map, a bundle map between the duals in the opposite direction.
Its chart operators are the transposes of the chart operators of `f`. -/
noncomputable def dualMap (f : A ⟶ D) : D.dual ⟶ A.dual where
  operator i j :=
    ⟨fun x => (f.operator j i ⟨x.val, x.property.2, x.property.1⟩).piTranspose,
      ((f.operator j i).continuous.comp (continuous_subtypeVal.subtype_mk _)).piTranspose⟩
  compatible i i' j j' x hi hi' hj hj' v := by
    have h : (f.operator j i ⟨x, hj, hi⟩).comp (A.core.coordChange j' j x) =
        (D.core.coordChange i' i x).comp (f.operator j' i' ⟨x, hj', hi'⟩) :=
      ContinuousLinearMap.ext fun w => (f.compatible j' j i' i x hj' hj hi' hi w).symm
    have h' := congrArg (fun T => T.piTranspose v) h
    simp only [ContinuousLinearMap.piTranspose_comp] at h'
    -- The dual transitions are the transposes of the reverse original transitions.
    exact h'

theorem operator_dualMap (f : A ⟶ D) (i j : B)
    (x : ↥(D.dual.core.baseSet i ∩ A.dual.core.baseSet j)) :
    (dualMap f).operator i j x = (f.operator j i ⟨x.val, x.property.2, x.property.1⟩).piTranspose :=
        (rfl)

/-- On every fibre, the transposed bundle map is the transpose of the original fibre map. -/
@[simp] theorem fiberMap_dualMap (f : A ⟶ D) (x : B) :
    (dualMap f).fiberMap x = (f.fiberMap x).piTranspose := by
  have h (h₁ : x ∈ A.core.baseSet x) (h₂ : x ∈ D.core.baseSet x) :
      f.operator x x ⟨x, h₁, h₂⟩ = f.fiberMap x := by
    rw [CoordinateHom.operator_eq]
    ext v
    simp only [inChartCoordinates_apply, A.indexAt_eq, D.indexAt_eq, coordChange_self,
      ContinuousLinearMap.id_apply]
  exact (CoordinateHom.fiberMap_def _ x).trans (congrArg ContinuousLinearMap.piTranspose
    (h (by simpa only [A.indexAt_eq] using A.core.mem_baseSet_at x)
      (by simpa only [D.indexAt_eq] using D.core.mem_baseSet_at x)))

@[simp] theorem dualMap_id (A : FiniteRankBundleCore 𝕜 B) : dualMap (𝟙 A) = 𝟙 A.dual :=
  hom_ext fun x => by
    rw [fiberMap_dualMap, fiberMap_id, fiberMap_id]
    exact ContinuousLinearMap.piTranspose_id

@[simp] theorem dualMap_comp (f : A ⟶ D) (g : D ⟶ C) :
    dualMap (f ≫ g) = dualMap g ≫ dualMap f :=
  hom_ext fun x => by
    simp only [fiberMap_comp, fiberMap_dualMap, ContinuousLinearMap.piTranspose_comp]
    -- The two sides differ only in writing the rank of a dual as the original rank.
    rfl

@[simp] theorem dualMap_zero : dualMap (0 : A ⟶ D) = 0 :=
  hom_ext fun x => by
    simp only [fiberMap_dualMap, CoordinateHom.fiberMap_zero,
      ContinuousLinearMap.piTranspose_zero]
    -- The two sides differ only in writing the rank of a dual as the original rank.
    rfl

@[simp] theorem dualMap_add (f g : A ⟶ D) : dualMap (f + g) = dualMap f + dualMap g :=
  hom_ext fun x => by
    simp only [fiberMap_dualMap, fiberMap_add, ContinuousLinearMap.piTranspose_add]
    -- The two sides differ only in writing the rank of a dual as the original rank.
    rfl

@[simp] theorem dualMap_neg (f : A ⟶ D) : dualMap (-f) = -dualMap f :=
  hom_ext fun x => by
    simp only [fiberMap_dualMap, fiberMap_neg, ContinuousLinearMap.piTranspose_neg]
    -- The two sides differ only in writing the rank of a dual as the original rank.
    rfl

theorem dualMap_injective : Function.Injective (dualMap : (A ⟶ D) → (D.dual ⟶ A.dual)) :=
  fun f g h => hom_ext fun x => ContinuousLinearMap.piTranspose_injective <| by
    rw [← fiberMap_dualMap, ← fiberMap_dualMap, h]

variable (𝕜 B) in
/-- Duality as a contravariant functor on finite-rank cores. -/
-- Expose the object and morphism maps, which consumers read off as duals and transposes.
@[expose, simps]
noncomputable def dualFunctor : (FiniteRankBundleCore 𝕜 B)ᵒᵖ ⥤ FiniteRankBundleCore 𝕜 B where
  obj A := A.unop.dual
  map f := dualMap f.unop
  map_id A := dualMap_id A.unop
  map_comp f g := dualMap_comp g.unop f.unop

/-- Duality is additive on bundle maps. -/
instance : (dualFunctor 𝕜 B).Additive where
  map_add {_ _ f g} := dualMap_add f.unop g.unop

/-- The identification of the double dual with the original core. In charts it is the
transition map of `A`, since transposition is an involution. -/
noncomputable def dualDualHom (A : FiniteRankBundleCore 𝕜 B) : A.dual.dual ⟶ A where
  operator i j := ⟨(A.core.baseSet i ∩ A.core.baseSet j).domRestrict (A.core.coordChange i j),
    (A.core.continuousOn_coordChange i j).domRestrict⟩
  compatible i i' j j' x hi hi' hj hj' v := by
    -- The double-dual transition is the doubly transposed transition of `A`.
    change A.core.coordChange j j' x (A.core.coordChange i j x v) =
      A.core.coordChange i' j' x ((A.core.coordChange i i' x).piTranspose.piTranspose v)
    rw [ContinuousLinearMap.piTranspose_piTranspose]
    exact (A.core.coordChange_comp i j j' x ⟨⟨hi, hj⟩, hj'⟩ v).trans
      (A.core.coordChange_comp i i' j' x ⟨⟨hi, hi'⟩, hj'⟩ v).symm

/-- The inverse identification of the original core with its double dual. -/
noncomputable def dualDualInv (A : FiniteRankBundleCore 𝕜 B) : A ⟶ A.dual.dual where
  operator i j := ⟨(A.core.baseSet i ∩ A.core.baseSet j).domRestrict (A.core.coordChange i j),
    (A.core.continuousOn_coordChange i j).domRestrict⟩
  compatible i i' j j' x hi hi' hj hj' v := by
    -- The double-dual transition is the doubly transposed transition of `A`.
    change (A.core.coordChange j j' x).piTranspose.piTranspose (A.core.coordChange i j x v) =
      A.core.coordChange i' j' x (A.core.coordChange i i' x v)
    rw [ContinuousLinearMap.piTranspose_piTranspose]
    exact (A.core.coordChange_comp i j j' x ⟨⟨hi, hj⟩, hj'⟩ v).trans
      (A.core.coordChange_comp i i' j' x ⟨⟨hi, hi'⟩, hj'⟩ v).symm

@[simp] theorem fiberMap_dualDualHom (A : FiniteRankBundleCore 𝕜 B) (x : B) :
    (dualDualHom A).fiberMap x = ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜) := by
  refine (CoordinateHom.fiberMap_def _ x).trans ?_
  -- The chart operators are transitions of `A`; the charts of a dual are labelled by points.
  change A.core.coordChange x (A.core.indexAt x) x = _
  rw [A.indexAt_eq, coordChange_self]

@[simp] theorem fiberMap_dualDualInv (A : FiniteRankBundleCore 𝕜 B) (x : B) :
    (dualDualInv A).fiberMap x = ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜) := by
  refine (CoordinateHom.fiberMap_def _ x).trans ?_
  -- The chart operators are transitions of `A`; the charts of a dual are labelled by points.
  change A.core.coordChange (A.core.indexAt x) x x = _
  rw [A.indexAt_eq, coordChange_self]

/-- The double dual of a core is isomorphic to the core, by identity maps on all fibres. -/
noncomputable def dualDualIso (A : FiniteRankBundleCore 𝕜 B) : A.dual.dual ≅ A where
  hom := dualDualHom A
  inv := dualDualInv A
  hom_inv_id := hom_ext fun x => by
    rw [fiberMap_comp, fiberMap_dualDualHom, fiberMap_dualDualInv, fiberMap_id]
    exact ContinuousLinearMap.id_comp _
  inv_hom_id := hom_ext fun x => by
    rw [fiberMap_comp, fiberMap_dualDualHom, fiberMap_dualDualInv, fiberMap_id]
    exact ContinuousLinearMap.id_comp _

@[simp] theorem dualDualIso_hom (A : FiniteRankBundleCore 𝕜 B) :
    (dualDualIso A).hom = dualDualHom A := (rfl)

@[simp] theorem dualDualIso_inv (A : FiniteRankBundleCore 𝕜 B) :
    (dualDualIso A).inv = dualDualInv A := (rfl)

/-- The double transpose of a bundle map is the map itself, under `dualDualIso`. -/
@[reassoc (attr := simp)]
theorem dualDualHom_naturality (f : A ⟶ D) :
    dualMap (dualMap f) ≫ dualDualHom D = dualDualHom A ≫ f :=
  hom_ext fun x => by
    simp only [fiberMap_comp, fiberMap_dualMap, fiberMap_dualDualHom]
    -- `simp` does not rewrite the identity composites, which are stated at the double-dual rank.
    exact (ContinuousLinearMap.id_comp _).trans
      ((ContinuousLinearMap.piTranspose_piTranspose _).trans (ContinuousLinearMap.comp_id _).symm)

variable (𝕜 B) in
/-- The double dual functor is naturally isomorphic to the identity. -/
noncomputable def dualDualNatIso :
    (dualFunctor 𝕜 B).rightOp ⋙ dualFunctor 𝕜 B ≅ 𝟭 (FiniteRankBundleCore 𝕜 B) :=
  NatIso.ofComponents dualDualIso fun f => dualDualHom_naturality f

@[simp] theorem dualDualNatIso_hom_app (A : FiniteRankBundleCore 𝕜 B) :
    (dualDualNatIso 𝕜 B).hom.app A = dualDualHom A := (rfl)

@[simp] theorem dualDualNatIso_inv_app (A : FiniteRankBundleCore 𝕜 B) :
    (dualDualNatIso 𝕜 B).inv.app A = dualDualInv A := (rfl)

section WhitneySum

/-- The transposes of the Whitney-sum inclusions and projections, exhibiting the dual of a
Whitney sum as a biproduct of the duals. It is the image under `dualFunctor` of the opposite
Whitney bicone. -/
-- Expose the point projection so the types of the four legs reduce to the dual Whitney sum.
@[expose]
noncomputable def dualWhitneyBicone (A D : FiniteRankBundleCore 𝕜 B) :
    BinaryBicone A.dual D.dual :=
  (dualFunctor 𝕜 B).mapBinaryBicone (whitneyBicone A D).op

@[simp] theorem dualWhitneyBicone_pt (A D : FiniteRankBundleCore 𝕜 B) :
    (dualWhitneyBicone A D).pt = (whitneySum A D).dual := (rfl)

@[simp] theorem dualWhitneyBicone_fst (A D : FiniteRankBundleCore 𝕜 B) :
    (dualWhitneyBicone A D).fst = dualMap (whitneyInl A D) := (rfl)

@[simp] theorem dualWhitneyBicone_snd (A D : FiniteRankBundleCore 𝕜 B) :
    (dualWhitneyBicone A D).snd = dualMap (whitneyInr A D) := (rfl)

@[simp] theorem dualWhitneyBicone_inl (A D : FiniteRankBundleCore 𝕜 B) :
    (dualWhitneyBicone A D).inl = dualMap (whitneyFst A D) := (rfl)

@[simp] theorem dualWhitneyBicone_inr (A D : FiniteRankBundleCore 𝕜 B) :
    (dualWhitneyBicone A D).inr = dualMap (whitneySnd A D) := (rfl)

/-- The transposed inclusions and projections of a Whitney sum form a biproduct, since the
additive functor `dualFunctor` preserves biproducts. -/
noncomputable def dualWhitneyBiconeIsBilimit (A D : FiniteRankBundleCore 𝕜 B) :
    (dualWhitneyBicone A D).IsBilimit :=
  have := preservesBinaryBiproduct_of_preservesBiproduct (dualFunctor 𝕜 B) (op A) (op D)
  isBinaryBilimitOfPreserves (dualFunctor 𝕜 B) (whitneyBiconeIsBilimit A D).op

/-- The dual of a Whitney sum is the Whitney sum of the duals. -/
noncomputable def dualWhitneySumIso (A D : FiniteRankBundleCore 𝕜 B) :
    (whitneySum A D).dual ≅ whitneySum A.dual D.dual :=
  (dualWhitneyBiconeIsBilimit A D).isLimit.conePointUniqueUpToIso
    (whitneyBiconeIsBilimit A.dual D.dual).isLimit

/-- Followed by the first projection, the identification of the dual of a Whitney sum is the
transpose of the first inclusion. -/
@[reassoc (attr := simp)]
theorem dualWhitneySumIso_hom_whitneyFst (A D : FiniteRankBundleCore 𝕜 B) :
    (dualWhitneySumIso A D).hom ≫ whitneyFst A.dual D.dual = dualMap (whitneyInl A D) :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ (Discrete.mk WalkingPair.left)

/-- Followed by the second projection, the identification of the dual of a Whitney sum is the
transpose of the second inclusion. -/
@[reassoc (attr := simp)]
theorem dualWhitneySumIso_hom_whitneySnd (A D : FiniteRankBundleCore 𝕜 B) :
    (dualWhitneySumIso A D).hom ≫ whitneySnd A.dual D.dual = dualMap (whitneyInr A D) :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ (Discrete.mk WalkingPair.right)

end WhitneySum

variable (𝕜 B) in
/-- The double dual on the opposite category is naturally isomorphic to the identity. This is the
unit of the duality anti-equivalence, whose counit is `dualDualNatIso`. -/
noncomputable def dualDualOpNatIso :
    𝟭 (FiniteRankBundleCore 𝕜 B)ᵒᵖ ≅ dualFunctor 𝕜 B ⋙ (dualFunctor 𝕜 B).rightOp :=
  NatIso.ofComponents (fun A => (dualDualIso A.unop).op) fun f =>
    Quiver.Hom.unop_inj (dualDualHom_naturality f.unop).symm

/-- Duality is an anti-equivalence of finite-rank cores. -/
instance : (dualFunctor 𝕜 B).IsEquivalence :=
  (CategoryTheory.Equivalence.mk (dualFunctor 𝕜 B) (dualFunctor 𝕜 B).rightOp
    (dualDualOpNatIso 𝕜 B) (dualDualNatIso 𝕜 B)).isEquivalence_functor

section MathlibDual

/-- The coordinate vector `w` in the dual core, read as the functional `v ↦ ∑ k, v k * w k` on
the corresponding fibre of `A`. -/
noncomputable def dualFiberEquiv (A : FiniteRankBundleCore 𝕜 B) (x : B) :
    A.dual.core.Fiber x ≃L[𝕜] (A.core.Fiber x →L[𝕜] Trivial B 𝕜 x) :=
  (ContinuousLinearEquiv.piRing (𝕜 := 𝕜) (E := 𝕜) (Fin A.rank)).symm

@[simp] theorem dualFiberEquiv_apply_apply (A : FiniteRankBundleCore 𝕜 B) (x : B)
    (w : Fin A.rank → 𝕜) (v : Fin A.rank → 𝕜) :
    dualFiberEquiv A x w v = ∑ k, v k * w k :=
  (ContinuousLinearEquiv.piRing_symm_apply (𝕜 := 𝕜) w v).trans (by simp only [smul_eq_mul])

/-- The coordinates of a functional on a fibre of `A` are its values on the standard basis. -/
@[simp] theorem dualFiberEquiv_symm_apply (A : FiniteRankBundleCore 𝕜 B) (x : B)
    (f : A.core.Fiber x →L[𝕜] Trivial B 𝕜 x) (i : Fin A.rank) :
    (dualFiberEquiv A x).symm f i = f (Pi.single i 1) :=
  ContinuousLinearEquiv.piRing_apply (𝕜 := 𝕜) (E := 𝕜) f i

/-- In a frame of the original bundle, the functional represented by a dual-core vector has
as coefficient vector the coordinates of that vector in the dual frame. -/
theorem dualFiberEquiv_inCoordinates (A : FiniteRankBundleCore 𝕜 B) (a x : B)
    (hx : x ∈ A.core.baseSet a) (w : A.dual.core.Fiber x) :
    ContinuousLinearMap.inCoordinates (Fin A.rank → 𝕜) A.core.Fiber 𝕜 (Trivial B 𝕜)
        a x a x (dualFiberEquiv A x w) =
      (ContinuousLinearEquiv.piRing (𝕜 := 𝕜) (E := 𝕜) (Fin A.rank)).symm
        ((A.dual.core.localTriv a) ⟨x, w⟩).2 := by
  have hb : x ∈ A.core.baseSet (A.core.indexAt a) := by rwa [A.indexAt_eq]
  rw [ContinuousLinearMap.inCoordinates, A.core.trivializationAt_symmL hb]
  simp only [Trivial.fiberBundle_trivializationAt', Trivial.continuousLinearMapAt_trivialization,
    ContinuousLinearMap.id_comp, A.indexAt_eq, VectorBundleCore.localTriv_apply,
    coordChange_dual]
  exact (ContinuousLinearMap.piRing_symm_piTranspose _ _).symm

/-- Reading dual coordinates as functionals is continuous on total spaces, for the topology of
Mathlib's Hom bundle on the target. -/
theorem continuous_dualFiberEquiv (A : FiniteRankBundleCore 𝕜 B) :
    Continuous fun p : A.dual.core.TotalSpace =>
      TotalSpace.mk' ((Fin A.rank → 𝕜) →L[𝕜] 𝕜)
        (E := fun x => A.core.Fiber x →L[𝕜] Trivial B 𝕜 x) p.proj
        (dualFiberEquiv A p.proj p.snd) := by
  refine continuous_iff_continuousAt.2 fun p => ?_
  rw [continuousAt_hom_bundle]
  refine ⟨A.dual.core.continuous_proj.continuousAt, ?_⟩
  -- In the chart labelled by the base point, the target coordinates are the dual coordinates
  -- read as functionals.
  have hp : p ∈ (A.dual.core.localTriv p.proj).source :=
    (A.dual.core.mem_localTriv_source p.proj p).2 (A.dual.core.mem_baseSet_at p.proj)
  have hU := (A.dual.core.localTriv p.proj).open_source.mem_nhds hp
  have hc := (((A.dual.core.localTriv p.proj).continuousOn.continuousAt hU).snd)
  refine ((ContinuousLinearEquiv.piRing (𝕜 := 𝕜) (E := 𝕜) (Fin A.rank)).symm.continuous
    |>.continuousAt.comp hc).congr ?_
  filter_upwards [hU] with q hq
  exact (A.dualFiberEquiv_inCoordinates p.proj q.proj
    ((A.dual.core.mem_localTriv_source p.proj q).1 hq) q.snd).symm

/-- The reconstructed total space of the dual core is the total space of Mathlib's dual bundle
of `A`, over the identity of the base and by `dualFiberEquiv` on each fibre. -/
noncomputable def dualTotalSpaceHomeomorph (A : FiniteRankBundleCore 𝕜 B) :
    A.dual.core.TotalSpace ≃ₜ
      TotalSpace ((Fin A.rank → 𝕜) →L[𝕜] 𝕜) (fun x => A.core.Fiber x →L[𝕜] Trivial B 𝕜 x) :=
  bundleHomeomorph (dualFiberEquiv A) (continuous_dualFiberEquiv A)

@[simp] theorem dualTotalSpaceHomeomorph_apply (A : FiniteRankBundleCore 𝕜 B)
    (p : A.dual.core.TotalSpace) :
    dualTotalSpaceHomeomorph A p = ⟨p.proj, dualFiberEquiv A p.proj p.snd⟩ :=
  bundleHomeomorph_apply _ _ p

@[simp] theorem dualTotalSpaceHomeomorph_symm_apply (A : FiniteRankBundleCore 𝕜 B)
    (p : TotalSpace ((Fin A.rank → 𝕜) →L[𝕜] 𝕜) (fun x => A.core.Fiber x →L[𝕜] Trivial B 𝕜 x)) :
    (dualTotalSpaceHomeomorph A).symm p = ⟨p.proj, (dualFiberEquiv A p.proj).symm p.snd⟩ :=
  bundleHomeomorph_symm_apply _ _ p

/-- Under the identification with functionals, the transposed bundle map is precomposition
with the original fibre map. -/
theorem dualFiberEquiv_fiberMap_dualMap (f : A ⟶ D) (x : B) (w : Fin D.rank → 𝕜) :
    dualFiberEquiv A x ((dualMap f).fiberMap x w) = (dualFiberEquiv D x w).comp (f.fiberMap x) := by
  rw [fiberMap_dualMap]
  exact ContinuousLinearMap.piRing_symm_piTranspose _ _

end MathlibDual

section Pullback

variable {X : Type*} {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Pulling back commutes strictly with taking dual cores. -/
@[simp] theorem pullback_dual (A : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y)) :
    A.dual.pullback f = (A.pullback f).dual := (rfl)

/-- Pulling back commutes with transposing bundle maps. -/
@[simp] theorem pullbackMap_dualMap {A D : FiniteRankBundleCore 𝕜 Y} (a : A ⟶ D)
    (f : C(X, Y)) :
    pullbackMap (dualMap a) f = dualMap (pullbackMap a f) := by
  apply hom_ext
  intro x
  rw [fiberMap_pullbackMap, fiberMap_dualMap, ← fiberMap_pullbackMap a f x]
  -- `D.dual.pullback f` and `A.dual.pullback f` are definitionally `(D.pullback f).dual` and
  -- `(A.pullback f).dual` (`pullback_dual`), identifying the implicit cores of `fiberMap`.
  exact Eq.symm (fiberMap_dualMap _ x)

/-- Duality commutes strictly with pullback as contravariant functors. -/
theorem dualFunctor_comp_pullbackFunctor (f : C(X, Y)) :
    dualFunctor 𝕜 Y ⋙ pullbackFunctor f = (pullbackFunctor f).op ⋙ dualFunctor 𝕜 X :=
  Functor.hext (fun _ => rfl) fun _ _ a => heq_of_eq (pullbackMap_dualMap a.unop f)

/-- Pulling back the double-dual identification gives the double-dual identification of the
pullback. -/
@[simp] theorem pullbackMap_dualDualHom (A : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y)) :
    pullbackMap (dualDualHom A) f = dualDualHom (A.pullback f) := by
  apply hom_ext
  intro x
  rw [fiberMap_pullbackMap, fiberMap_dualDualHom]
  -- `A.dual.dual.pullback f` is definitionally `(A.pullback f).dual.dual` (`pullback_dual`).
  exact Eq.symm (fiberMap_dualDualHom _ x)

/-- Pulling back the inverse double-dual identification gives the inverse double-dual
identification of the pullback. -/
@[simp] theorem pullbackMap_dualDualInv (A : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y)) :
    pullbackMap (dualDualInv A) f = dualDualInv (A.pullback f) := by
  apply hom_ext
  intro x
  rw [fiberMap_pullbackMap, fiberMap_dualDualInv]
  -- `A.dual.dual.pullback f` is definitionally `(A.pullback f).dual.dual` (`pullback_dual`).
  exact Eq.symm (fiberMap_dualDualInv _ x)

/-- On every fibre, `dualFiberEquiv` on a pulled-back dual core evaluates the functional of `A` at
the image base point. -/
theorem dualFiberEquiv_pullback_apply (A : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y))
    (x : X) (w : Fin A.rank → 𝕜) (v : Fin A.rank → 𝕜) :
    dualFiberEquiv (A.pullback f) x w v = dualFiberEquiv A (f x) w v := by
  simp only [dualFiberEquiv_apply_apply]
  -- Both sums range over `Fin A.rank` definitionally, as recorded by `rank_pullback`.
  rfl

end Pullback

section RankOne

/-- For a rank-one core `A`, the tensor product `A.dual ⊗ A` has identity transitions on all chart
overlaps. -/
theorem coordChange_dual_tensor_eq_id (A : FiniteRankBundleCore 𝕜 B) (hA : A.rank = 1)
    {i j x : B} (hi : x ∈ (A.dual ⊗ A).core.baseSet i) (hj : x ∈ (A.dual ⊗ A).core.baseSet j) :
    (A.dual ⊗ A).core.coordChange i j x =
      ContinuousLinearMap.id 𝕜 (Fin (A.dual ⊗ A).rank → 𝕜) := by
  simp only [baseSet_at, localTriv_baseSet_tensorObj, localTriv_baseSet_dual, Set.mem_inter_iff,
    and_self] at hi hj
  let : Unique (Fin A.rank) := ⟨⟨⟨0, by omega⟩⟩, fun k ↦ Fin.ext (by omega)⟩
  set c := A.core.coordChange i j x (fun _ ↦ 1) default
  set d := A.core.coordChange j i x (fun _ ↦ 1) default
  have hT : A.core.coordChange i j x = c • ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜) :=
    (A.core.coordChange i j x).eq_smul_id_of_unique
  have hS : A.core.coordChange j i x = d • ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜) :=
    (A.core.coordChange j i x).eq_smul_id_of_unique
  have hdc : d * c = 1 := by
    have hcomp := congrFun (A.core.coordChange_comp i j i x ⟨⟨hi, hj⟩, hi⟩ (fun _ ↦ 1)) default
    rw [A.core.coordChange_self i x hi, hT, hS] at hcomp
    simpa [mul_comm] using hcomp
  have hS_tr : A.dual.core.coordChange i j x =
      d • ContinuousLinearMap.id 𝕜 (Fin A.dual.rank → 𝕜) := by
    rw [coordChange_dual, hS, ← ContinuousLinearMap.piTransposeL_apply, map_smul,
      ContinuousLinearMap.piTransposeL_apply, ContinuousLinearMap.piTranspose_id]
    -- `A.dual.rank = A.rank` definitionally (`rank_dual`).
    rfl
  rw [coordChange_tensorObj, hS_tr, hT, ContinuousLinearMap.smul_kronecker,
    ContinuousLinearMap.kronecker_smul, smul_smul, hdc, one_smul,
    ContinuousLinearMap.id_kronecker_id]
  -- `(A.dual ⊗ A).rank = A.dual.rank * A.rank` definitionally (`rank_tensorObj`).
  rfl

/-- Canonical evaluation isomorphism `A.dual ⊗ A ≅ 𝟙_` for a rank-one core `A`. -/
noncomputable def dualTensorIsoUnit (A : FiniteRankBundleCore 𝕜 B) (hA : A.rank = 1) :
    A.dual ⊗ A ≅ 𝟙_ (FiniteRankBundleCore 𝕜 B) :=
  isoTrivialOfCoordChangeEqId (A.dual ⊗ A)
    (ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ : Fin 1 ↦ 𝕜) (finCongr (by simp [hA])))
    fun _ _ _ hi hj ↦ A.coordChange_dual_tensor_eq_id hA hi hj

@[simp] theorem fiberMap_dualTensorIsoUnit_hom (A : FiniteRankBundleCore 𝕜 B) (hA : A.rank = 1)
    (x : B) :
    (A.dualTensorIsoUnit hA).hom.fiberMap x =
      (ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ : Fin 1 ↦ 𝕜)
        (finCongr (by simp [hA]))).toContinuousLinearMap :=
  fiberMap_isoTrivialOfCoordChangeEqId_hom _ _ _ x

@[simp] theorem fiberMap_dualTensorIsoUnit_inv (A : FiniteRankBundleCore 𝕜 B) (hA : A.rank = 1)
    (x : B) :
    (A.dualTensorIsoUnit hA).inv.fiberMap x =
      (ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ : Fin 1 ↦ 𝕜)
        (finCongr (by simp [hA]))).symm.toContinuousLinearMap :=
  fiberMap_isoTrivialOfCoordChangeEqId_inv _ _ _ x

end RankOne

section OfBundleDual

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

section DualBundle

variable {r : ℕ} (e : F ≃L[𝕜] (Fin r → 𝕜)) (V : B → Type*)
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

/-- On the fibre over `x`, identify a dual coordinate vector `w : Fin r → 𝕜` of
`(ofBundle 𝕜 e V).dual` with the continuous linear functional on `V x` pairing a vector with
coordinates `u = e ((trivializationAt F V x) ⟨x, v⟩).2` to `∑ k, u k * w k`. -/
noncomputable def ofBundleDualFiberEquiv (x : B) :
    (ofBundle 𝕜 e V).dual.core.Fiber x ≃L[𝕜] (V x →L[𝕜] 𝕜) :=
  (dualFiberEquiv (ofBundle 𝕜 e V) x).trans
    ((ofBundleFiberEquiv e V x).arrowCongr (ContinuousLinearEquiv.refl 𝕜 𝕜))

/-- Forward precomposition formula: `ofBundleDualFiberEquiv e V x w` is `dualFiberEquiv` composed
with `(ofBundleFiberEquiv e V x).symm`. -/
theorem ofBundleDualFiberEquiv_apply (x : B) (w : Fin r → 𝕜) :
    ofBundleDualFiberEquiv e V x w =
      (dualFiberEquiv (ofBundle 𝕜 e V) x w).comp
        (ofBundleFiberEquiv e V x).symm.toContinuousLinearMap := by
  ext v
  exact (congrFun (congrArg DFunLike.coe
    (ContinuousLinearEquiv.trans_apply (dualFiberEquiv (ofBundle 𝕜 e V) x)
      ((ofBundleFiberEquiv e V x).arrowCongr (ContinuousLinearEquiv.refl 𝕜 𝕜)) w)) v).trans
    (by simp only [ContinuousLinearEquiv.arrowCongr_apply, ContinuousLinearEquiv.refl_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe])

/-- Inverse precomposition formula: `(ofBundleDualFiberEquiv e V x).symm α` is the dual
coordinates of `α` precomposed with `ofBundleFiberEquiv e V x`. -/
theorem ofBundleDualFiberEquiv_symm (x : B) (α : V x →L[𝕜] 𝕜) :
    (ofBundleDualFiberEquiv e V x).symm α =
      (dualFiberEquiv (ofBundle 𝕜 e V) x).symm
        (α.comp (ofBundleFiberEquiv e V x).toContinuousLinearMap) := by
  refine (ContinuousLinearEquiv.symm_trans_apply _ _ α).trans <|
    congrArg (dualFiberEquiv (ofBundle 𝕜 e V) x).symm <|
      (ContinuousLinearEquiv.symm_apply_eq _).2 ?_
  ext v
  simp only [ContinuousLinearEquiv.arrowCongr_apply, ContinuousLinearEquiv.refl_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply]

/-- Explicit dual pairing convention: a dual coordinate vector `w` evaluates on `v : V x` by
pairing the `e`-coordinates of `v` in `trivializationAt F V x` with `w`. -/
@[simp]
theorem ofBundleDualFiberEquiv_apply_apply (x : B) (w : Fin r → 𝕜) (v : V x) :
    ofBundleDualFiberEquiv e V x w v =
      ∑ k, e ((trivializationAt F V x) ⟨x, v⟩).2 k * w k := by
  rw [ofBundleDualFiberEquiv_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, ofBundleFiberEquiv_symm_apply]
  exact dualFiberEquiv_apply_apply (ofBundle 𝕜 e V) x w _

/-- Evaluated on a vector `(trivializationAt F V x).symm x u` of the preferred trivialization at
`x`, a dual coordinate vector `w` pairs `e u` with `w`. -/
theorem ofBundleDualFiberEquiv_apply_symm (x : B) (w : Fin r → 𝕜) (u : F) :
    ofBundleDualFiberEquiv e V x w ((trivializationAt F V x).symm x u) =
      ∑ k, e u k * w k := by
  rw [ofBundleDualFiberEquiv_apply_apply,
    (trivializationAt F V x).apply_mk_symm (mem_baseSet_trivializationAt F V x) u]

/-- The `i`th standard basis vector `Pi.single i 1` of the dual core corresponds to the `i`th
coordinate functional `u ↦ e u i` on the preferred trivialization at `x`. -/
theorem ofBundleDualFiberEquiv_single_apply_symm (x : B) (i : Fin r) (u : F) :
    ofBundleDualFiberEquiv e V x (Pi.single i 1) ((trivializationAt F V x).symm x u) =
      e u i :=
  (ofBundleDualFiberEquiv_apply_symm e V x (Pi.single i 1) u).trans
    (by simp [Pi.single_apply])

/-- The dual coordinates of a functional `α : V x →L[𝕜] 𝕜` are its values on the basis vectors
`(trivializationAt F V x).symm x (e.symm (Pi.single i 1))`. -/
@[simp]
theorem ofBundleDualFiberEquiv_symm_apply (x : B) (α : V x →L[𝕜] 𝕜) (i : Fin r) :
    (ofBundleDualFiberEquiv e V x).symm α i =
      α ((trivializationAt F V x).symm x (e.symm (Pi.single i 1))) := by
  rw [ofBundleDualFiberEquiv_symm]
  exact (dualFiberEquiv_symm_apply (ofBundle 𝕜 e V) x _ i).trans <|
    (ContinuousLinearMap.comp_apply _ _ _).trans <|
      congrArg α (ofBundleFiberEquiv_apply e V x (Pi.single i 1))

/-- In the preferred Hom-bundle chart at `a`, `ofBundleDualFiberEquiv` reads a dual-core
coordinate vector through the constant continuous linear equivalence
`w ↦ (ContinuousLinearEquiv.piRing.symm w) ∘L e`. -/
theorem ofBundleDualFiberEquiv_inCoordinates (a : B) {x : B}
    (hx : x ∈ (trivializationAt F V a).baseSet) (w : Fin r → 𝕜) :
    ContinuousLinearMap.inCoordinates F V 𝕜 (Trivial B 𝕜) a x a x
        (ofBundleDualFiberEquiv e V x w) =
      ((ContinuousLinearEquiv.piRing (𝕜 := 𝕜) (E := 𝕜) (Fin r)).symm
        (((ofBundle 𝕜 e V).dual.core.localTriv a ⟨x, w⟩).2)).comp e.toContinuousLinearMap := by
  have hx' : x ∈ (ofBundle 𝕜 e V).core.baseSet a := (baseSet_ofBundle e V a).symm ▸ hx
  have hdual := congrArg (·.comp e.toContinuousLinearMap)
    (dualFiberEquiv_inCoordinates (ofBundle 𝕜 e V) a x hx' w)
  refine ContinuousLinearMap.ext fun u ↦ ?_
  have hin := congrArg (fun f : F →L[𝕜] 𝕜 ↦ f u) hdual
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inCoordinates,
    ContinuousLinearEquiv.coe_coe, (ofBundle 𝕜 e V).trivializationAt_core] at hin
  let v₀ : (ofBundle 𝕜 e V).core.Fiber x :=
    ((ofBundle 𝕜 e V).core.localTriv a).symmL 𝕜 x (e u)
  have htriv_snd : (trivializationAt F V a ⟨x, ofBundleFiberEquiv e V x v₀⟩).2 = u := by
    refine (trivializationAt_ofBundleFiberEquiv_snd e V a hx v₀).trans ?_
    have hv₀ : (((ofBundle 𝕜 e V).core.localTriv a) ⟨x, v₀⟩).2 = e u := by
      dsimp only [v₀]
      rw [((ofBundle 𝕜 e V).core.localTriv a).symmL_apply hx']
      exact congrArg Prod.snd (((ofBundle 𝕜 e V).core.localTriv a).apply_mk_symm hx' (e u))
    rw [hv₀, e.symm_apply_apply]
  have hfib : ofBundleFiberEquiv e V x v₀ = (trivializationAt F V a).symmL 𝕜 x u := by
    rw [(trivializationAt F V a).symmL_apply hx, ← htriv_snd]
    exact ((trivializationAt F V a).symm_apply_apply_mk hx (ofBundleFiberEquiv e V x v₀)).symm
  refine (congrArg (fun g : 𝕜 →L[𝕜] 𝕜 ↦ g _)
    (Trivial.continuousLinearMapAt_trivialization 𝕜 B 𝕜 x)).trans ?_
  rw [ContinuousLinearMap.id_apply]
  refine (congrArg (ofBundleDualFiberEquiv e V x w) hfib.symm).trans ?_
  have hpair : ofBundleDualFiberEquiv e V x w (ofBundleFiberEquiv e V x v₀) =
      dualFiberEquiv (ofBundle 𝕜 e V) x w v₀ := by
    rw [ofBundleDualFiberEquiv_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, (ofBundleFiberEquiv e V x).symm_apply_apply]
  refine hpair.trans ?_
  refine (congrArg (fun g : 𝕜 →L[𝕜] 𝕜 ↦ g _)
    (Trivial.continuousLinearMapAt_trivialization 𝕜 B 𝕜 x)).symm.trans ?_
  exact hin

/-- Near any `p₀`, reading `ofBundleDualFiberEquiv` in the Hom-bundle chart at `p₀.proj`
eventually agrees with a fixed continuous linear equivalence applied to the dual core chart at
`p₀.proj`. -/
theorem eventuallyEq_inCoordinates_ofBundleDualFiberEquiv
    (p₀ : (ofBundle 𝕜 e V).dual.core.TotalSpace) :
    (fun q : (ofBundle 𝕜 e V).dual.core.TotalSpace ↦
        ContinuousLinearMap.inCoordinates F V 𝕜 (Trivial B 𝕜) p₀.proj q.proj p₀.proj q.proj
          (ofBundleDualFiberEquiv e V q.proj q.snd)) =ᶠ[nhds p₀]
      fun q ↦
        ((ContinuousLinearEquiv.piRing (𝕜 := 𝕜) (E := 𝕜) (Fin r)).symm.trans
          (e.symm.arrowCongr (ContinuousLinearEquiv.refl 𝕜 𝕜))).toContinuousLinearMap
          (((ofBundle 𝕜 e V).dual.core.localTriv p₀.proj q).2) := by
  have hnhds := (ofBundle 𝕜 e V).dual.core.localTrivAt_source_mem_nhds p₀
  rw [VectorBundleCore.localTrivAt, (ofBundle 𝕜 e V).dual.indexAt_eq] at hnhds
  filter_upwards [hnhds] with q hq
  exact (ofBundleDualFiberEquiv_inCoordinates e V p₀.proj
    ((baseSet_ofBundle e V p₀.proj) ▸
      ((ofBundle 𝕜 e V).dual.core.mem_localTriv_source p₀.proj q).1 hq) q.snd).trans
    (ContinuousLinearEquiv.piRing_symm_trans_arrowCongr_apply e _).symm

/-- Reading dual-core coordinates as functionals on `V` is continuous on total spaces. -/
theorem continuous_ofBundleDualFiberEquiv :
    Continuous fun p : (ofBundle 𝕜 e V).dual.core.TotalSpace ↦
      TotalSpace.mk' (F →L[𝕜] 𝕜) (E := fun x ↦ V x →L[𝕜] 𝕜) p.proj
        (ofBundleDualFiberEquiv e V p.proj p.snd) := by
  refine continuous_iff_continuousAt.2 fun p ↦ ?_
  rw [continuousAt_hom_bundle]
  refine ⟨(ofBundle 𝕜 e V).dual.core.continuous_proj.continuousAt, ?_⟩
  let L : (Fin r → 𝕜) →L[𝕜] (F →L[𝕜] 𝕜) :=
    ((ContinuousLinearEquiv.piRing (𝕜 := 𝕜) (E := 𝕜) (Fin r)).symm.trans
      (e.symm.arrowCongr (ContinuousLinearEquiv.refl 𝕜 𝕜))).toContinuousLinearMap
  have hc : ContinuousAt
      (fun q : (ofBundle 𝕜 e V).dual.core.TotalSpace ↦
        ((ofBundle 𝕜 e V).dual.core.localTriv p.proj q).2) p := by
    simpa only [VectorBundleCore.localTrivAt, (ofBundle 𝕜 e V).dual.indexAt_eq] using
      (ofBundle 𝕜 e V).dual.core.continuousAt_localTrivAt_snd p
  exact (L.continuous.continuousAt.comp hc).congr_of_eventuallyEq
    (eventuallyEq_inCoordinates_ofBundleDualFiberEquiv e V p)

/-- The reconstructed total space of `(ofBundle 𝕜 e V).dual` is homeomorphic to Mathlib's dual
bundle `fun x ↦ V x →L[𝕜] 𝕜`, over the identity of the base and by `ofBundleDualFiberEquiv` on
each fibre. -/
noncomputable def ofBundleDualTotalSpaceHomeomorph :
    (ofBundle 𝕜 e V).dual.core.TotalSpace ≃ₜ
      TotalSpace (F →L[𝕜] 𝕜) (fun x ↦ V x →L[𝕜] 𝕜) :=
  bundleHomeomorph (𝕜 := 𝕜) (ofBundleDualFiberEquiv e V)
    (continuous_ofBundleDualFiberEquiv e V)

@[simp]
theorem ofBundleDualTotalSpaceHomeomorph_apply
    (p : (ofBundle 𝕜 e V).dual.core.TotalSpace) :
    ofBundleDualTotalSpaceHomeomorph e V p =
      ⟨p.proj, ofBundleDualFiberEquiv e V p.proj p.snd⟩ :=
  bundleHomeomorph_apply _ _ p

@[simp]
theorem ofBundleDualTotalSpaceHomeomorph_symm_apply
    (p : TotalSpace (F →L[𝕜] 𝕜) (fun x ↦ V x →L[𝕜] 𝕜)) :
    (ofBundleDualTotalSpaceHomeomorph e V).symm p =
      ⟨p.proj, (ofBundleDualFiberEquiv e V p.proj).symm p.snd⟩ :=
  bundleHomeomorph_symm_apply _ _ p

end DualBundle

section DualChange

variable {r₁ r₂ : ℕ} (e₁ : F ≃L[𝕜] (Fin r₁ → 𝕜)) (e₂ : F ≃L[𝕜] (Fin r₂ → 𝕜))
  (V : B → Type*) [∀ x, AddCommMonoid (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

/-- Composing the dual change-of-coordinates maps `e₁ ↦ e₂` and `e₂ ↦ e₁` yields the identity
morphism on `(ofBundle 𝕜 e₂ V).dual`. -/
theorem dualMap_changeIso_comp_eq_id :
    (dualMap (ofBundleChangeIso e₁ e₂ V).hom) ≫
        (dualMap (ofBundleChangeIso e₂ e₁ V).hom) =
      𝟙 (ofBundle 𝕜 e₂ V).dual := by
  rw [← ofBundleChangeIso_inv e₂ e₁ V]
  exact ((dualFunctor 𝕜 B).mapIso (ofBundleChangeIso e₂ e₁ V).op).inv_hom_id

end DualChange

section DualChangeBundle

variable {r₁ r₂ : ℕ} (e₁ : F ≃L[𝕜] (Fin r₁ → 𝕜)) (e₂ : F ≃L[𝕜] (Fin r₂ → 𝕜))
  (V : B → Type*) [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

/-- Changing the coordinate equivalence acts contravariantly on the dual core and commutes with the
identification `ofBundleDualFiberEquiv` to `V x →L[𝕜] 𝕜`. -/
theorem ofBundleDualFiberEquiv_dualMap_changeIso (x : B) (w : Fin r₁ → 𝕜) :
    ofBundleDualFiberEquiv e₂ V x
        ((dualMap (ofBundleChangeIso e₂ e₁ V).hom).fiberMap x w) =
      ofBundleDualFiberEquiv e₁ V x w := by
  ext v
  refine (congrArg (· v) (ofBundleDualFiberEquiv_apply e₂ V x _)).trans ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ofBundleDualFiberEquiv_apply, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  refine (congrArg (fun f ↦ f ((ofBundleFiberEquiv e₂ V x).symm v))
    (dualFiberEquiv_fiberMap_dualMap (ofBundleChangeIso e₂ e₁ V).hom x w)).trans ?_
  refine (ContinuousLinearMap.comp_apply (dualFiberEquiv (ofBundle 𝕜 e₁ V) x w)
    ((ofBundleChangeIso e₂ e₁ V).hom.fiberMap x) ((ofBundleFiberEquiv e₂ V x).symm v)).trans ?_
  refine congrArg (dualFiberEquiv (ofBundle 𝕜 e₁ V) x w) ?_
  refine (ofBundleFiberEquiv e₁ V x).eq_symm_apply.mpr <|
    (ofBundleFiberEquiv_changeIso e₂ e₁ V x _).trans ?_
  exact (ofBundleFiberEquiv e₂ V x).apply_symm_apply v

end DualChangeBundle

end OfBundleDual

end TauCeti.FiniteRankBundleCore
