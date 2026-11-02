/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Biproduct
public import TauCeti.Analysis.Normed.Operator.PiTranspose
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Preadditive.Opposite
public import Mathlib.Topology.VectorBundle.Constructions

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
anti-equivalence. The dual of a trivial core is the trivial core of the same rank, and the
transposed Whitney-sum inclusions and projections identify the dual of a Whitney sum with the
Whitney sum of the duals (`dualWhitneySumIso`).

`dualTotalSpaceHomeomorph` identifies the reconstructed total space of `A.dual` with the
total space of Mathlib's dual bundle of `A`, the bundle of continuous linear maps from the
fibres of `A` to the trivial line, over the identity of the base. Under this identification
`dualMap f` is precomposition with `f` (`dualFiberEquiv_fiberMap_dualMap`). Thus the transposed
chart transitions present the actual dual bundle, with its Hom-bundle topology.

The scalar field is assumed complete, as for Mathlib's identification
`ContinuousLinearEquiv.piRing` of a coordinate space with its continuous dual. The base is
arbitrary, and zero ranks and the empty base are included.

For the dual bundle and its transition functions see Milnor–Stasheff, *Characteristic Classes*,
§3.
-/

public section

open Bundle CategoryTheory CategoryTheory.Limits VectorBundleCore Opposite

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
    ⟨fun x => (f.operator j i ⟨x.1, x.2.2, x.2.1⟩).piTranspose,
      ((f.operator j i).continuous.comp (continuous_subtype_val.subtype_mk _)).piTranspose⟩
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
    (dualMap f).operator i j x = (f.operator j i ⟨x.1, x.2.2, x.2.1⟩).piTranspose := (rfl)

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

/-- Reading dual coordinates as functionals is continuous on total spaces, for the topology of
Mathlib's Hom bundle on the target. -/
theorem continuous_dualFiberEquiv (A : FiniteRankBundleCore 𝕜 B) :
    Continuous fun p : A.dual.core.TotalSpace =>
      TotalSpace.mk' ((Fin A.rank → 𝕜) →L[𝕜] 𝕜)
        (E := fun x => A.core.Fiber x →L[𝕜] Trivial B 𝕜 x) p.proj
        (dualFiberEquiv A p.proj p.2) := by
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
  have hq' : q.proj ∈ A.core.baseSet p.proj :=
    (A.dual.core.mem_localTriv_source p.proj q).1 hq
  have hb : q.proj ∈ A.core.baseSet (A.core.indexAt p.proj) := by
    rwa [A.indexAt_eq]
  have key : (dualFiberEquiv A q.proj q.2).comp (A.core.coordChange p.proj q.proj q.proj) =
      (ContinuousLinearEquiv.piRing (𝕜 := 𝕜) (E := 𝕜) (Fin A.rank)).symm
        ((A.core.coordChange p.proj q.proj q.proj).piTranspose q.2) :=
    (ContinuousLinearMap.piRing_symm_piTranspose _ _).symm
  rw [ContinuousLinearMap.inCoordinates, A.core.trivializationAt_symmL (b₀ := p.proj) hb]
  simp only [Trivial.fiberBundle_trivializationAt', Trivial.continuousLinearMapAt_trivialization,
    ContinuousLinearMap.id_comp, A.indexAt_eq]
  exact key.symm

/-- The reconstructed total space of the dual core is the total space of Mathlib's dual bundle
of `A`, over the identity of the base and by `dualFiberEquiv` on each fibre. -/
noncomputable def dualTotalSpaceHomeomorph (A : FiniteRankBundleCore 𝕜 B) :
    A.dual.core.TotalSpace ≃ₜ
      TotalSpace ((Fin A.rank → 𝕜) →L[𝕜] 𝕜) (fun x => A.core.Fiber x →L[𝕜] Trivial B 𝕜 x) :=
  bundleHomeomorph (dualFiberEquiv A) (continuous_dualFiberEquiv A)

@[simp] theorem dualTotalSpaceHomeomorph_apply (A : FiniteRankBundleCore 𝕜 B)
    (p : A.dual.core.TotalSpace) :
    dualTotalSpaceHomeomorph A p = ⟨p.proj, dualFiberEquiv A p.proj p.2⟩ :=
  bundleHomeomorph_apply _ _ p

@[simp] theorem dualTotalSpaceHomeomorph_symm_apply (A : FiniteRankBundleCore 𝕜 B)
    (p : TotalSpace ((Fin A.rank → 𝕜) →L[𝕜] 𝕜) (fun x => A.core.Fiber x →L[𝕜] Trivial B 𝕜 x)) :
    (dualTotalSpaceHomeomorph A).symm p = ⟨p.proj, (dualFiberEquiv A p.proj).symm p.2⟩ :=
  bundleHomeomorph_symm_apply _ _ p

/-- Under the identification with functionals, the transposed bundle map is precomposition
with the original fibre map. -/
theorem dualFiberEquiv_fiberMap_dualMap (f : A ⟶ D) (x : B) (w : Fin D.rank → 𝕜) :
    dualFiberEquiv A x ((dualMap f).fiberMap x w) = (dualFiberEquiv D x w).comp (f.fiberMap x) := by
  rw [fiberMap_dualMap]
  exact ContinuousLinearMap.piRing_symm_piTranspose _ _

end MathlibDual

end TauCeti.FiniteRankBundleCore
