/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.GroupAction.Quotient
public import TauCeti.Topology.VectorBundle.FiniteRank.Dual
public import TauCeti.Topology.VectorBundle.FiniteRank.Tensor
public import TauCeti.Topology.VectorBundle.FiniteRank.ExteriorPower

/-!
# Descent of bundle maps, sections, and operations for finite-rank cores over orbit quotients

Let a group `G` act on a topological space `M` with orbit projection
`q = TauCeti.continuousQuotientMk G M : C(M, MulAction.orbitRel.Quotient G M)`, and let
`A D : FiniteRankBundleCore 𝕜 (MulAction.orbitRel.Quotient G M)` be finite-rank vector-bundle cores
over the orbit space. Because `(A.pullback q).core.Fiber x` and `A.core.Fiber (q x)` share the
preferred coordinate space `Fin A.rank → 𝕜`, `G`-invariant morphisms and sections over `M` descend
canonically to the orbit space without completeness of `𝕜` or continuity of the `G`-action:

* `FiniteRankBundleCore.orbitRelQuotientDesc` and `FiniteRankBundleCore.orbitRelQuotientDescIso`:
  descends `G`-invariant morphisms (`eq_orbitRelQuotientDesc_iff`) and isomorphisms
  (`isIso_orbitRelQuotientDesc_iff`) from `M` to `M ⧸ G`.
* Bundle-map descent commutes with equivariant pullback
  (`orbitRelQuotientDesc_pullbackEquivariant`), continuous coordinate functors
  (`orbitRelQuotientDesc_mapHom`), exterior powers (`orbitRelQuotientDesc_exteriorPower_map`),
  determinant lines (`orbitRelQuotientDesc_detMap`), duals (`orbitRelQuotientDesc_dualMap`), and
  tensor products (`orbitRelQuotientDesc_tensorHom`).
* Section descent (`continuous_section_orbitRelQuotientRec_core_iff`) commutes with equivariant
  pullback (`orbitRelQuotientRec_pullback`), bundle-map evaluation
  (`orbitRelQuotientRec_fiberMap_apply`), dual pairing (`orbitRelQuotientLift_dualFiberEquiv`),
  pure tensors (`orbitRelQuotientRec_pureTensorSection`), exterior powers
  (`orbitRelQuotientRec_wedgeSection`), and determinants (`orbitRelQuotientRec_detSection`).

## References

* Norman Steenrod, *The Topology of Fibre Bundles*, §§2–3.
* M. F. Atiyah, *K-Theory*, §1.2 and §1.6.
* Daniel Huybrechts, *Complex Geometry: An Introduction*, §2.2.
-/

public section

open Bundle CategoryTheory MulAction TauCeti.MulAction Set Topology VectorBundleCore

namespace TauCeti.FiniteRankBundleCore

section BundleMapDescent

variable {𝕜 G M : Type*} [NontriviallyNormedField 𝕜] [Group G] [MulAction G M]
  [TopologicalSpace M] {A D E : FiniteRankBundleCore 𝕜 (orbitRel.Quotient G M)}

private theorem continuous_hom_orbitRelQuotientLift
    (a : A.pullback (continuousQuotientMk G M) ⟶ D.pullback (continuousQuotientMk G M))
    (ha : ∀ (g : G) (x : M), a.fiberMap (g • x) = a.fiberMap x) :
    Continuous fun z ↦ TotalSpace.mk' ((Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜))
      (E := fun y ↦ A.core.Fiber y →L[𝕜] D.core.Fiber y) z
      (orbitRelQuotientLift a.fiberMap ha z) := by
  let q := continuousQuotientMk G M
  let f : M → (Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜) := a.fiberMap
  have hf : ∀ (g : G) (x : M), f (g • x) = f x := ha
  change Continuous fun z ↦ TotalSpace.mk' ((Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜))
    (E := fun y ↦ A.core.Fiber y →L[𝕜] D.core.Fiber y) z (orbitRelQuotientLift f hf z)
  have hq : Topology.IsQuotientMap (Quotient.mk (orbitRel G M)) := isQuotientMap_quot_mk
  rw [hq.continuous_iff]
  have hcomp : ((fun z ↦ TotalSpace.mk' ((Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜))
      (E := fun y ↦ A.core.Fiber y →L[𝕜] D.core.Fiber y) z (orbitRelQuotientLift f hf z)) ∘
      Quotient.mk (orbitRel G M)) =
      fun x ↦ TotalSpace.mk' ((Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜))
        (E := fun y ↦ A.core.Fiber y →L[𝕜] D.core.Fiber y) (q x) (f x) :=
    funext fun x ↦ congrArg (TotalSpace.mk' ((Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜))
      (E := fun y ↦ A.core.Fiber y →L[𝕜] D.core.Fiber y) (q x))
      (orbitRelQuotientLift_mk (f := f) (hf := hf) x)
  rw [hcomp]
  refine continuous_iff_continuousAt.2 fun x₀ ↦ ?_
  rw [continuousAt_hom_bundle]
  refine ⟨q.continuous.continuousAt, ?_⟩
  let U := (A.pullback q).core.baseSet x₀ ∩ (D.pullback q).core.baseSet x₀
  have hU := (((A.pullback q).core.isOpen_baseSet x₀).inter
    ((D.pullback q).core.isOpen_baseSet x₀)).mem_nhds
    ⟨(A.pullback q).mem_baseSet_self x₀, (D.pullback q).mem_baseSet_self x₀⟩
  have hc : ContinuousOn
      (fun x ↦ (A.pullback q).core.inChartCoordinates (D.pullback q).core x₀ x₀ x (a.fiberMap x))
      U := continuousOn_iff_continuous_domRestrict.2
    ((a.operator x₀ x₀).continuous.congr fun x ↦ a.operator_eq x₀ x₀ x)
  refine (hc.continuousAt hU).congr ?_
  filter_upwards [hU] with x hx
  have hxA : q x ∈ A.core.baseSet (A.core.indexAt (q x₀)) := by rw [A.indexAt_eq]; exact hx.1
  have hxD : q x ∈ D.core.baseSet (D.core.indexAt (q x₀)) := by rw [D.indexAt_eq]; exact hx.2
  refine ContinuousLinearMap.ext fun (v : Fin A.rank → 𝕜) ↦ ?_
  rw [inChartCoordinates_pullback A D q x₀ x₀ x (a.fiberMap x)]
  change A.core.inChartCoordinates D.core (q x₀) (q x₀) (q x) (f x) v =
    ContinuousLinearMap.inCoordinates (Fin A.rank → 𝕜) A.core.Fiber (Fin D.rank → 𝕜) D.core.Fiber
      (q x₀) (q x) (q x₀) (q x) (f x) v
  rw [A.core.inCoordinates_eq D.core (f x) hxA hxD, inChartCoordinates_apply,
    A.indexAt_eq (q x), D.indexAt_eq (q x), A.indexAt_eq (q x₀), D.indexAt_eq (q x₀)]
  rfl

/-- **Bundle-map descent for finite-rank cores.** A morphism
`a : A.pullback (continuousQuotientMk G M) ⟶ D.pullback (continuousQuotientMk G M)` whose
preferred-coordinate `fiberMap` is `G`-invariant descends to a morphism `A ⟶ D` over the orbit
space, without completeness of `𝕜` or continuity assumptions on the `G`-action. -/
def orbitRelQuotientDesc
    (a : A.pullback (continuousQuotientMk G M) ⟶ D.pullback (continuousQuotientMk G M))
    (ha : ∀ (g : G) (x : M), a.fiberMap (g • x) = a.fiberMap x) : A ⟶ D :=
  CoordinateHom.ofContinuous (orbitRelQuotientLift a.fiberMap ha)
    (continuous_hom_orbitRelQuotientLift a ha)

/-- On preferred fibre coordinates, `orbitRelQuotientDesc` is `MulAction.orbitRelQuotientLift` of
`a.fiberMap`. -/
@[simp] theorem fiberMap_orbitRelQuotientDesc
    (a : A.pullback (continuousQuotientMk G M) ⟶ D.pullback (continuousQuotientMk G M))
    (ha : ∀ (g : G) (x : M), a.fiberMap (g • x) = a.fiberMap x) (z : orbitRel.Quotient G M) :
    (orbitRelQuotientDesc a ha).fiberMap z = orbitRelQuotientLift a.fiberMap ha z :=
  congrFun (CoordinateHom.fiberMap_ofContinuous _ _) z

/-- Over the orbit of `x`, `orbitRelQuotientDesc a ha` evaluates to `a.fiberMap x`. -/
theorem fiberMap_orbitRelQuotientDesc_mk
    (a : A.pullback (continuousQuotientMk G M) ⟶ D.pullback (continuousQuotientMk G M))
    (ha : ∀ (g : G) (x : M), a.fiberMap (g • x) = a.fiberMap x) (x : M) :
    (orbitRelQuotientDesc a ha).fiberMap (Quotient.mk (orbitRel G M) x) = a.fiberMap x := by
  rw [fiberMap_orbitRelQuotientDesc, orbitRelQuotientLift_mk]

/-- On reconstructed total spaces, `orbitRelQuotientDesc a ha` acts over `Quotient.mk _ x` by
`a.fiberMap x`. -/
theorem totalSpaceMap_orbitRelQuotientDesc_mk
    (a : A.pullback (continuousQuotientMk G M) ⟶ D.pullback (continuousQuotientMk G M))
    (ha : ∀ (g : G) (x : M), a.fiberMap (g • x) = a.fiberMap x)
    (x : M) (v : A.core.Fiber (Quotient.mk (orbitRel G M) x)) :
    (orbitRelQuotientDesc a ha).totalSpaceMap ⟨Quotient.mk (orbitRel G M) x, v⟩ =
      ⟨Quotient.mk (orbitRel G M) x, a.fiberMap x v⟩ := by
  rw [CoordinateHom.totalSpaceMap_mk, fiberMap_orbitRelQuotientDesc_mk]

/-- Pulling back `orbitRelQuotientDesc a ha` along the orbit projection recovers `a`. -/
@[simp] theorem pullbackMap_orbitRelQuotientDesc
    (a : A.pullback (continuousQuotientMk G M) ⟶ D.pullback (continuousQuotientMk G M))
    (ha : ∀ (g : G) (x : M), a.fiberMap (g • x) = a.fiberMap x) :
    pullbackMap (orbitRelQuotientDesc a ha) (continuousQuotientMk G M) = a :=
  hom_ext fun x ↦ by
    rw [fiberMap_pullbackMap, continuousQuotientMk_apply, fiberMap_orbitRelQuotientDesc_mk]

/-- **Uniqueness of bundle-map descent.** A morphism `b : A ⟶ D` over the orbit space equals
`orbitRelQuotientDesc a ha` if and only if its pullback to `M` is `a`. -/
theorem eq_orbitRelQuotientDesc_iff {b : A ⟶ D}
    {a : A.pullback (continuousQuotientMk G M) ⟶ D.pullback (continuousQuotientMk G M)}
    {ha : ∀ (g : G) (x : M), a.fiberMap (g • x) = a.fiberMap x} :
    b = orbitRelQuotientDesc a ha ↔ pullbackMap b (continuousQuotientMk G M) = a := by
  refine ⟨fun h ↦ h ▸ pullbackMap_orbitRelQuotientDesc a ha, fun h ↦ hom_ext fun z ↦ ?_⟩
  induction z using Quotient.inductionOn with | h x =>
  simpa only [fiberMap_pullbackMap, continuousQuotientMk_apply, fiberMap_orbitRelQuotientDesc_mk]
    using congrArg (fun c ↦ c.fiberMap x) h

/-- Every morphism over the orbit space is the descent of its pullback along the orbit
projection. -/
@[simp] theorem orbitRelQuotientDesc_pullbackMap (b : A ⟶ D)
    (hb : ∀ (g : G) (x : M), (pullbackMap b (continuousQuotientMk G M)).fiberMap (g • x) =
      (pullbackMap b (continuousQuotientMk G M)).fiberMap x) :
    orbitRelQuotientDesc (pullbackMap b (continuousQuotientMk G M)) hb = b :=
  (eq_orbitRelQuotientDesc_iff.2 rfl).symm

/-- Descending the identity on `A.pullback (continuousQuotientMk G M)` gives `𝟙 A`. -/
@[simp] theorem orbitRelQuotientDesc_id
    (h : ∀ (g : G) (x : M),
      CoordinateHom.fiberMap (𝟙 (A.pullback (continuousQuotientMk G M))) (g • x) =
        CoordinateHom.fiberMap (𝟙 (A.pullback (continuousQuotientMk G M))) x) :
    orbitRelQuotientDesc (𝟙 (A.pullback (continuousQuotientMk G M))) h = 𝟙 A :=
  (eq_orbitRelQuotientDesc_iff.2 (pullbackMap_id A (continuousQuotientMk G M))).symm

/-- Bundle-map descent commutes with composition of morphisms. -/
@[simp] theorem orbitRelQuotientDesc_comp
    (a : A.pullback (continuousQuotientMk G M) ⟶ D.pullback (continuousQuotientMk G M))
    (b : D.pullback (continuousQuotientMk G M) ⟶ E.pullback (continuousQuotientMk G M))
    (ha : ∀ (g : G) (x : M), a.fiberMap (g • x) = a.fiberMap x)
    (hb : ∀ (g : G) (x : M), b.fiberMap (g • x) = b.fiberMap x)
    (hab : ∀ (g : G) (x : M), (a ≫ b).fiberMap (g • x) = (a ≫ b).fiberMap x) :
    orbitRelQuotientDesc (a ≫ b) hab = orbitRelQuotientDesc a ha ≫ orbitRelQuotientDesc b hb := by
  symm
  rw [eq_orbitRelQuotientDesc_iff, pullbackMap_comp, pullbackMap_orbitRelQuotientDesc,
    pullbackMap_orbitRelQuotientDesc]

/-- Bundle-map descent preserves the zero morphism. -/
@[simp] theorem orbitRelQuotientDesc_zero
    (h : ∀ (g : G) (x : M),
      CoordinateHom.fiberMap
        (0 : A.pullback (continuousQuotientMk G M) ⟶ D.pullback (continuousQuotientMk G M))
        (g • x) =
      CoordinateHom.fiberMap
        (0 : A.pullback (continuousQuotientMk G M) ⟶ D.pullback (continuousQuotientMk G M)) x) :
    orbitRelQuotientDesc
      (0 : A.pullback (continuousQuotientMk G M) ⟶ D.pullback (continuousQuotientMk G M)) h = 0 :=
  (eq_orbitRelQuotientDesc_iff.2 (pullbackMap_zero A D (continuousQuotientMk G M))).symm

/-- Bundle-map descent preserves addition of morphisms. -/
@[simp] theorem orbitRelQuotientDesc_add
    (a b : A.pullback (continuousQuotientMk G M) ⟶ D.pullback (continuousQuotientMk G M))
    (ha : ∀ (g : G) (x : M), a.fiberMap (g • x) = a.fiberMap x)
    (hb : ∀ (g : G) (x : M), b.fiberMap (g • x) = b.fiberMap x)
    (hab : ∀ (g : G) (x : M), (a + b).fiberMap (g • x) = (a + b).fiberMap x) :
    orbitRelQuotientDesc (a + b) hab = orbitRelQuotientDesc a ha + orbitRelQuotientDesc b hb := by
  symm
  rw [eq_orbitRelQuotientDesc_iff, pullbackMap_add, pullbackMap_orbitRelQuotientDesc,
    pullbackMap_orbitRelQuotientDesc]

/-- Bundle-map descent preserves negation of morphisms. -/
@[simp] theorem orbitRelQuotientDesc_neg
    (a : A.pullback (continuousQuotientMk G M) ⟶ D.pullback (continuousQuotientMk G M))
    (ha : ∀ (g : G) (x : M), a.fiberMap (g • x) = a.fiberMap x)
    (hna : ∀ (g : G) (x : M), (-a).fiberMap (g • x) = (-a).fiberMap x) :
    orbitRelQuotientDesc (-a) hna = -orbitRelQuotientDesc a ha := by
  symm
  rw [eq_orbitRelQuotientDesc_iff, pullbackMap_neg, pullbackMap_orbitRelQuotientDesc]

/-- For an isomorphism of pulled-back finite-rank cores, `G`-invariance of `e.hom.fiberMap`
implies `G`-invariance of `e.inv.fiberMap`. -/
theorem fiberMap_inv_smul
    (e : A.pullback (continuousQuotientMk G M) ≅ D.pullback (continuousQuotientMk G M))
    (he : ∀ (g : G) (x : M), e.hom.fiberMap (g • x) = e.hom.fiberMap x) (g : G) (x : M) :
    e.inv.fiberMap (g • x) = e.inv.fiberMap x := by
  have hleft : e.inv.fiberMap (g • x) ∘L e.hom.fiberMap (g • x) =
      ContinuousLinearMap.id 𝕜 (Fin (A.pullback (continuousQuotientMk G M)).rank → 𝕜) := by
    simpa only [fiberMap_comp, fiberMap_id] using congrArg (fun c ↦ c.fiberMap (g • x)) e.hom_inv_id
  have hright : e.hom.fiberMap x ∘L e.inv.fiberMap x =
      ContinuousLinearMap.id 𝕜 (Fin (D.pullback (continuousQuotientMk G M)).rank → 𝕜) := by
    simpa only [fiberMap_comp, fiberMap_id] using congrArg (fun c ↦ c.fiberMap x) e.inv_hom_id
  calc e.inv.fiberMap (g • x)
      = e.inv.fiberMap (g • x) ∘L (e.hom.fiberMap x ∘L e.inv.fiberMap x) := by
        rw [hright, ContinuousLinearMap.comp_id]
    _ = (e.inv.fiberMap (g • x) ∘L e.hom.fiberMap (g • x)) ∘L e.inv.fiberMap x := by
        rw [← he g x, ContinuousLinearMap.comp_assoc]
    _ = e.inv.fiberMap x := by rw [hleft, ContinuousLinearMap.id_comp]

/-- A `G`-invariant isomorphism between pulled-back finite-rank cores descends to an isomorphism
over the orbit space; `G`-invariance of the inverse follows automatically. -/
def orbitRelQuotientDescIso
    (e : A.pullback (continuousQuotientMk G M) ≅ D.pullback (continuousQuotientMk G M))
    (he : ∀ (g : G) (x : M), e.hom.fiberMap (g • x) = e.hom.fiberMap x) : A ≅ D where
  hom := orbitRelQuotientDesc e.hom he
  inv := orbitRelQuotientDesc e.inv (fiberMap_inv_smul e he)
  hom_inv_id := hom_ext fun z ↦ Quotient.inductionOn z fun x ↦
    ContinuousLinearMap.ext fun (v : Fin A.rank → 𝕜) ↦ by
      simpa only [fiberMap_comp, fiberMap_id, fiberMap_orbitRelQuotientDesc_mk,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using
        congrArg (fun c ↦ c.fiberMap x v) e.hom_inv_id
  inv_hom_id := hom_ext fun z ↦ Quotient.inductionOn z fun x ↦
    ContinuousLinearMap.ext fun (v : Fin D.rank → 𝕜) ↦ by
      simpa only [fiberMap_comp, fiberMap_id, fiberMap_orbitRelQuotientDesc_mk,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using
        congrArg (fun c ↦ c.fiberMap x v) e.inv_hom_id

@[simp] theorem orbitRelQuotientDescIso_hom
    (e : A.pullback (continuousQuotientMk G M) ≅ D.pullback (continuousQuotientMk G M))
    (he : ∀ (g : G) (x : M), e.hom.fiberMap (g • x) = e.hom.fiberMap x) :
    (orbitRelQuotientDescIso e he).hom = orbitRelQuotientDesc e.hom he := (rfl)

@[simp] theorem orbitRelQuotientDescIso_inv
    (e : A.pullback (continuousQuotientMk G M) ≅ D.pullback (continuousQuotientMk G M))
    (he : ∀ (g : G) (x : M), e.hom.fiberMap (g • x) = e.hom.fiberMap x) :
    (orbitRelQuotientDescIso e he).inv = orbitRelQuotientDesc e.inv (fiberMap_inv_smul e he) :=
  (rfl)

/-- `orbitRelQuotientDesc a ha` is an isomorphism in `FiniteRankBundleCore` if and only if `a`
is. -/
theorem isIso_orbitRelQuotientDesc_iff
    (a : A.pullback (continuousQuotientMk G M) ⟶ D.pullback (continuousQuotientMk G M))
    (ha : ∀ (g : G) (x : M), a.fiberMap (g • x) = a.fiberMap x) :
    IsIso (orbitRelQuotientDesc a ha) ↔ IsIso a :=
  ⟨fun _ ↦ pullbackMap_orbitRelQuotientDesc a ha ▸
    (pullbackFunctor (continuousQuotientMk G M)).map_isIso (orbitRelQuotientDesc a ha),
    fun _ ↦ (orbitRelQuotientDescIso (asIso a) ha).isIso_hom⟩

end BundleMapDescent

/-! ### Bundle-map descent commutes with bundle operations -/

section BundleMapOperations

variable {𝕜 G H M M' : Type*} [NontriviallyNormedField 𝕜]
  [Group G] [Group H] [MulAction G M] [MulAction H M']
  [TopologicalSpace M] [TopologicalSpace M']

/-- Pull back a morphism over `M` along a continuous `σ`-equivariant map `φ : M' →ₑ[σ] M`, viewed as
a morphism between the pullbacks to `M'` of the cores pulled back along
`φ.orbitRelQuotientContinuousMap hφ`. -/
def pullbackEquivariant {σ : H → G} (φ : M' →ₑ[σ] M) (hφ : Continuous φ)
    {A D : FiniteRankBundleCore 𝕜 (orbitRel.Quotient G M)}
    (a : A.pullback (continuousQuotientMk G M) ⟶ D.pullback (continuousQuotientMk G M)) :
    (A.pullback (φ.orbitRelQuotientContinuousMap hφ)).pullback (continuousQuotientMk H M') ⟶
      (D.pullback (φ.orbitRelQuotientContinuousMap hφ)).pullback (continuousQuotientMk H M') :=
  eqToHom (congrArg A.pullback (φ.orbitRelQuotientContinuousMap_comp_continuousQuotientMk hφ)) ≫
    pullbackMap a ⟨φ, hφ⟩ ≫
    eqToHom
      (congrArg D.pullback (φ.orbitRelQuotientContinuousMap_comp_continuousQuotientMk hφ).symm)

/-- On total spaces, `pullbackEquivariant φ hφ a` factors as `(pullbackMap a ⟨φ, hφ⟩).totalSpaceMap`
conjugated by `eqToHom` along `φ.orbitRelQuotientContinuousMap_comp_continuousQuotientMk hφ`. -/
theorem totalSpaceMap_pullbackEquivariant {σ : H → G} (φ : M' →ₑ[σ] M) (hφ : Continuous φ)
    {A D : FiniteRankBundleCore 𝕜 (orbitRel.Quotient G M)}
    (a : A.pullback (continuousQuotientMk G M) ⟶ D.pullback (continuousQuotientMk G M)) :
    (pullbackEquivariant φ hφ a).totalSpaceMap =
      (eqToHom (congrArg D.pullback
        (φ.orbitRelQuotientContinuousMap_comp_continuousQuotientMk hφ).symm)).totalSpaceMap ∘
      (pullbackMap a ⟨φ, hφ⟩).totalSpaceMap ∘
      (eqToHom (congrArg A.pullback
        (φ.orbitRelQuotientContinuousMap_comp_continuousQuotientMk hφ))).totalSpaceMap :=
  (CoordinateHom.totalSpaceMap_comp _ _).trans <|
    (congrArg (· ∘ _) (CoordinateHom.totalSpaceMap_comp _ _)).trans (Function.comp_assoc _ _ _)

/-- On preferred fibre coordinates, `pullbackEquivariant φ hφ a` evaluates `a.fiberMap` at
`φ x'`. -/
@[simp] theorem fiberMap_pullbackEquivariant {σ : H → G} (φ : M' →ₑ[σ] M) (hφ : Continuous φ)
    {A D : FiniteRankBundleCore 𝕜 (orbitRel.Quotient G M)}
    (a : A.pullback (continuousQuotientMk G M) ⟶ D.pullback (continuousQuotientMk G M)) (x' : M') :
    (pullbackEquivariant φ hφ a).fiberMap x' = a.fiberMap (φ x') := by
  have heq (C : FiniteRankBundleCore 𝕜 (orbitRel.Quotient G M))
      {f₁ f₂ : C(M', orbitRel.Quotient G M)} (hf : f₁ = f₂) (v : Fin C.rank → 𝕜) :
      CoordinateHom.fiberMap (eqToHom (congrArg C.pullback hf)) x' v = v := by
    cases hf; rw [eqToHom_refl, fiberMap_id]; rfl
  refine ContinuousLinearMap.ext fun (v : Fin A.rank → 𝕜) ↦ ?_
  dsimp only [pullbackEquivariant]
  rw [fiberMap_comp, fiberMap_comp]
  have h1 := heq A (φ.orbitRelQuotientContinuousMap_comp_continuousQuotientMk hφ) v
  have h2 := congrArg (· v) (fiberMap_pullbackMap a ⟨φ, hφ⟩ x')
  have h3 := heq D (φ.orbitRelQuotientContinuousMap_comp_continuousQuotientMk hφ).symm
    (a.fiberMap (φ x') v)
  change CoordinateHom.fiberMap
      (eqToHom (congrArg D.pullback
        (φ.orbitRelQuotientContinuousMap_comp_continuousQuotientMk hφ).symm)) x'
      ((pullbackMap a ⟨φ, hφ⟩).fiberMap x'
        (CoordinateHom.fiberMap (eqToHom (congrArg A.pullback
          (φ.orbitRelQuotientContinuousMap_comp_continuousQuotientMk hφ))) x' v)) =
    a.fiberMap (φ x') v
  rw [h1]
  exact (congrArg _ h2).trans h3

/-- **Bundle-map descent commutes with equivariant pullback.** Descending
`pullbackEquivariant φ hφ a` over `M' / H` agrees with pulling back `orbitRelQuotientDesc a ha`
along `φ.orbitRelQuotientContinuousMap hφ`. -/
@[simp] theorem orbitRelQuotientDesc_pullbackEquivariant {σ : H → G}
    (φ : M' →ₑ[σ] M) (hφ : Continuous φ)
    {A D : FiniteRankBundleCore 𝕜 (orbitRel.Quotient G M)}
    (a : A.pullback (continuousQuotientMk G M) ⟶ D.pullback (continuousQuotientMk G M))
    (ha : ∀ (g : G) (x : M), a.fiberMap (g • x) = a.fiberMap x)
    (ha' : ∀ (h : H) (x' : M'), (pullbackEquivariant φ hφ a).fiberMap (h • x') =
      (pullbackEquivariant φ hφ a).fiberMap x') :
    orbitRelQuotientDesc (pullbackEquivariant φ hφ a) ha' =
      pullbackMap (orbitRelQuotientDesc a ha) (φ.orbitRelQuotientContinuousMap hφ) :=
  hom_ext fun q' ↦ Quotient.inductionOn q' fun x' ↦ by
    rw [fiberMap_orbitRelQuotientDesc_mk, fiberMap_pullbackEquivariant, fiberMap_pullbackMap,
      φ.orbitRelQuotientContinuousMap_mk, fiberMap_orbitRelQuotientDesc_mk]

/-- **Bundle-map descent commutes with continuous coordinate functors.** -/
@[simp] theorem orbitRelQuotientDesc_mapHom {𝕜' : Type*} [NontriviallyNormedField 𝕜']
    (Φ : CoordinateFunctor 𝕜 𝕜') {A D : FiniteRankBundleCore 𝕜 (orbitRel.Quotient G M)}
    (a : A.pullback (continuousQuotientMk G M) ⟶ D.pullback (continuousQuotientMk G M))
    (ha : ∀ (g : G) (x : M), a.fiberMap (g • x) = a.fiberMap x)
    (hΦa : ∀ (g : G) (x : M), (Φ.mapHom a).fiberMap (g • x) = (Φ.mapHom a).fiberMap x) :
    orbitRelQuotientDesc (A := Φ.mapCore A) (D := Φ.mapCore D) (Φ.mapHom a) hΦa =
      Φ.mapHom (orbitRelQuotientDesc a ha) :=
  ((eq_orbitRelQuotientDesc_iff (A := Φ.mapCore A) (D := Φ.mapCore D)).2
    ((Φ.mapHom_pullbackMap (orbitRelQuotientDesc a ha) (continuousQuotientMk G M)).symm.trans
      (congrArg Φ.mapHom (pullbackMap_orbitRelQuotientDesc a ha)))).symm

/-- **Bundle-map descent commutes with exterior powers.** -/
@[simp] theorem orbitRelQuotientDesc_exteriorPower_map (j : ℕ)
    {A D : FiniteRankBundleCore 𝕜 (orbitRel.Quotient G M)}
    (a : A.pullback (continuousQuotientMk G M) ⟶ D.pullback (continuousQuotientMk G M))
    (ha : ∀ (g : G) (x : M), a.fiberMap (g • x) = a.fiberMap x)
    (hja : ∀ (g : G) (x : M),
      ((exteriorPower 𝕜 M j).map a).fiberMap (g • x) = ((exteriorPower 𝕜 M j).map a).fiberMap x) :
    orbitRelQuotientDesc (A := (exteriorPower 𝕜 (orbitRel.Quotient G M) j).obj A)
        (D := (exteriorPower 𝕜 (orbitRel.Quotient G M) j).obj D)
        ((exteriorPower 𝕜 M j).map a) hja =
      (exteriorPower 𝕜 (orbitRel.Quotient G M) j).map (orbitRelQuotientDesc a ha) :=
  orbitRelQuotientDesc_mapHom (CoordinateFunctor.exteriorPower 𝕜 j) a ha hja

/-- **Bundle-map descent commutes with determinant line bundles.** -/
@[simp] theorem orbitRelQuotientDesc_detMap {A D : FiniteRankBundleCore 𝕜 (orbitRel.Quotient G M)}
    (a : A.pullback (continuousQuotientMk G M) ⟶ D.pullback (continuousQuotientMk G M))
    (hr : A.rank = D.rank) (ha : ∀ (g : G) (x : M), a.fiberMap (g • x) = a.fiberMap x)
    (hda : ∀ (g : G) (x : M), (detMap a hr).fiberMap (g • x) = (detMap a hr).fiberMap x :=
      fun g x ↦ fiberMap_detMap_eq_of_fiberMap_eq (a := a) (b := a) hr (ha g x)) :
    orbitRelQuotientDesc (A := A.det) (D := D.det) (detMap a hr) hda =
      detMap (orbitRelQuotientDesc a ha) hr :=
  ((eq_orbitRelQuotientDesc_iff (A := A.det) (D := D.det)).2
    ((pullbackMap_detMap (orbitRelQuotientDesc a ha) hr (continuousQuotientMk G M)).trans
      (congrArg (fun x : A.pullback (continuousQuotientMk G M) ⟶
          D.pullback (continuousQuotientMk G M) ↦ detMap x hr)
        (pullbackMap_orbitRelQuotientDesc a ha)))).symm

/-- **Isomorphism descent commutes with determinant line bundles.** -/
@[simp] theorem orbitRelQuotientDescIso_detIso
    {A D : FiniteRankBundleCore 𝕜 (orbitRel.Quotient G M)}
    (e : A.pullback (continuousQuotientMk G M) ≅ D.pullback (continuousQuotientMk G M))
    (hr : A.rank = D.rank) (he : ∀ (g : G) (x : M), e.hom.fiberMap (g • x) = e.hom.fiberMap x)
    (hde : ∀ (g : G) (x : M),
      (detIso e hr).hom.fiberMap (g • x) = (detIso e hr).hom.fiberMap x := fun g x ↦ by
      simpa only [detIso_hom] using
        fiberMap_detMap_eq_of_fiberMap_eq (a := e.hom) (b := e.hom) hr (he g x)) :
    orbitRelQuotientDescIso (A := A.det) (D := D.det) (detIso e hr) hde =
      detIso (orbitRelQuotientDescIso e he) hr :=
  Iso.ext <| (orbitRelQuotientDescIso_hom (A := A.det) (D := D.det) (detIso e hr) hde).trans <|
    (((eq_orbitRelQuotientDesc_iff (A := A.det) (D := D.det)).2
      ((pullbackMap_detMap (orbitRelQuotientDesc e.hom he) hr (continuousQuotientMk G M)).trans
        ((congrArg (fun x : A.pullback (continuousQuotientMk G M) ⟶
            D.pullback (continuousQuotientMk G M) ↦ detMap x hr)
          (pullbackMap_orbitRelQuotientDesc e.hom he)).trans
          (detIso_hom e hr).symm))).symm).trans
      (detIso_hom (orbitRelQuotientDescIso e he) hr).symm

/-- **Bundle-map descent commutes with dual bundles.** -/
@[simp] theorem orbitRelQuotientDesc_dualMap [CompleteSpace 𝕜]
    {A D : FiniteRankBundleCore 𝕜 (orbitRel.Quotient G M)}
    (a : A.pullback (continuousQuotientMk G M) ⟶ D.pullback (continuousQuotientMk G M))
    (ha : ∀ (g : G) (x : M), a.fiberMap (g • x) = a.fiberMap x)
    (ha' : ∀ (g : G) (x : M), (dualMap a).fiberMap (g • x) = (dualMap a).fiberMap x) :
    orbitRelQuotientDesc (A := D.dual) (D := A.dual) (dualMap a) ha' =
      dualMap (orbitRelQuotientDesc a ha) :=
  ((eq_orbitRelQuotientDesc_iff (A := D.dual) (D := A.dual)).2
    ((pullbackMap_dualMap (orbitRelQuotientDesc a ha) (continuousQuotientMk G M)).trans
      (congrArg dualMap (pullbackMap_orbitRelQuotientDesc a ha)))).symm

/-- **Bundle-map descent commutes with tensor products.** -/
@[simp] theorem orbitRelQuotientDesc_tensorHom
    {A A' D D' : FiniteRankBundleCore 𝕜 (orbitRel.Quotient G M)}
    (a : A.pullback (continuousQuotientMk G M) ⟶ A'.pullback (continuousQuotientMk G M))
    (b : D.pullback (continuousQuotientMk G M) ⟶ D'.pullback (continuousQuotientMk G M))
    (ha : ∀ (g : G) (x : M), a.fiberMap (g • x) = a.fiberMap x)
    (hb : ∀ (g : G) (x : M), b.fiberMap (g • x) = b.fiberMap x)
    (hab : ∀ (g : G) (x : M), (tensorHom a b).fiberMap (g • x) = (tensorHom a b).fiberMap x) :
    orbitRelQuotientDesc (A := tensor A D) (D := tensor A' D') (tensorHom a b) hab =
      tensorHom (orbitRelQuotientDesc a ha) (orbitRelQuotientDesc b hb) :=
  ((eq_orbitRelQuotientDesc_iff (A := tensor A D) (D := tensor A' D')).2
    ((pullbackMap_tensorHom (orbitRelQuotientDesc a ha) (orbitRelQuotientDesc b hb)
      (continuousQuotientMk G M)).trans
      (by rw [pullbackMap_orbitRelQuotientDesc, pullbackMap_orbitRelQuotientDesc]))).symm

end BundleMapOperations

/-! ### Section descent and commutation with bundle operations -/

section SectionDescent

variable {𝕜 G H M M' : Type*} [NontriviallyNormedField 𝕜]
  [Group G] [Group H] [MulAction G M] [MulAction H M']
  [TopologicalSpace M] [TopologicalSpace M']

/-- **Section continuity descent for finite-rank cores.** For a `G`-invariant section `t` over `M`,
the descended section `MulAction.orbitRelQuotientRec t ht` of `A` over `M / G` is continuous if and
only if `t` is continuous as a section of `(A.pullback (continuousQuotientMk G M)).core`. -/
theorem continuous_section_orbitRelQuotientRec_core_iff
    (A : FiniteRankBundleCore 𝕜 (orbitRel.Quotient G M))
    {t : ∀ x : M, A.core.Fiber (Quotient.mk (orbitRel G M) x)}
    (ht : ∀ (g : G) (x : M), t (g • x) ≍ t x) :
    Continuous (fun z ↦ TotalSpace.mk' (Fin A.rank → 𝕜) z (orbitRelQuotientRec t ht z)) ↔
      Continuous fun x ↦ TotalSpace.mk' (Fin (A.pullback (continuousQuotientMk G M)).rank → 𝕜)
        (E := (A.pullback (continuousQuotientMk G M)).core.Fiber) x (t x) := by
  have hlift : (fun x ↦ A.pullbackLift (continuousQuotientMk G M)
      (TotalSpace.mk' (Fin (A.pullback (continuousQuotientMk G M)).rank → 𝕜)
        (E := (A.pullback (continuousQuotientMk G M)).core.Fiber) x (t x))) =
      fun x ↦ TotalSpace.mk' (Fin A.rank → 𝕜) (Quotient.mk (orbitRel G M) x) (t x) :=
    funext fun x ↦ A.pullbackLift_mk (continuousQuotientMk G M) x (t x)
  rw [continuous_section_orbitRelQuotientRec_iff,
    A.continuous_core_pullback_iff (continuousQuotientMk G M), hlift]
  exact ⟨fun h ↦ ⟨continuous_id, h⟩, fun h ↦ h.2⟩

/-- **Section descent commutes with equivariant pullback.** Along a continuous `σ`-equivariant map
`φ : M' →ₑ[σ] M`, descending the pulled-back section `fun x' ↦ t (φ x')` over `M' / H` agrees with
pulling back the descended section `MulAction.orbitRelQuotientRec t ht` along
`φ.orbitRelQuotientContinuousMap hφ`. -/
@[simp] theorem orbitRelQuotientRec_pullback {σ : H → G} (φ : M' →ₑ[σ] M) (hφ : Continuous φ)
    (A : FiniteRankBundleCore 𝕜 (orbitRel.Quotient G M))
    {t : ∀ x : M, A.core.Fiber (Quotient.mk (orbitRel G M) x)}
    (ht : ∀ (g : G) (x : M), t (g • x) ≍ t x)
    (ht' : ∀ (h : H) (x' : M'),
      (t (φ (h • x')) : (A.pullback (φ.orbitRelQuotientContinuousMap hφ)).core.Fiber
        (Quotient.mk (orbitRel H M') (h • x'))) ≍
      (t (φ x') : (A.pullback (φ.orbitRelQuotientContinuousMap hφ)).core.Fiber
        (Quotient.mk (orbitRel H M') x')))
    (z' : orbitRel.Quotient H M') :
    orbitRelQuotientRec (V := (A.pullback (φ.orbitRelQuotientContinuousMap hφ)).core.Fiber)
        (fun x' ↦ t (φ x')) ht' z' =
      orbitRelQuotientRec t ht (φ.orbitRelQuotientContinuousMap hφ z') := by
  rw [MulActionHom.coe_orbitRelQuotientContinuousMap]
  exact φ.orbitRelQuotientRec_orbitRelQuotientMap (V := A.core.Fiber) (ht := ht) (ht' := ht')
    (fun _ ↦ heq_of_eq rfl) z'

/-- **Section descent commutes with bundle-map evaluation.** Evaluating `orbitRelQuotientDesc a ha`
on a descended section agrees with descending `fun x ↦ a.fiberMap x (t x)`. -/
@[simp] theorem orbitRelQuotientRec_fiberMap_apply
    {A D : FiniteRankBundleCore 𝕜 (orbitRel.Quotient G M)}
    (a : A.pullback (continuousQuotientMk G M) ⟶ D.pullback (continuousQuotientMk G M))
    (ha : ∀ (g : G) (x : M), a.fiberMap (g • x) = a.fiberMap x)
    {t : ∀ x : M, A.core.Fiber (Quotient.mk (orbitRel G M) x)}
    (ht : ∀ (g : G) (x : M), t (g • x) ≍ t x)
    (hat : ∀ (g : G) (x : M),
      (a.fiberMap (g • x) (t (g • x)) : D.core.Fiber (Quotient.mk (orbitRel G M) (g • x))) ≍
        (a.fiberMap x (t x) : D.core.Fiber (Quotient.mk (orbitRel G M) x)) := fun g x ↦ by
      simpa only [fiberMap_orbitRelQuotientDesc_mk] using
        apply_smul_heq (fun z v ↦ (orbitRelQuotientDesc a ha).fiberMap z v) ht g x)
    (z : orbitRel.Quotient G M) :
    orbitRelQuotientRec (V := D.core.Fiber) (fun x ↦ a.fiberMap x (t x)) hat z =
      (orbitRelQuotientDesc a ha).fiberMap z (orbitRelQuotientRec t ht z) := by
  have h := orbitRelQuotientRec_map (fun q v ↦ (orbitRelQuotientDesc a ha).fiberMap q v) ht z
  refine (congrFun (eq_orbitRelQuotientRec_iff.2 fun x ↦ ?_) z).symm.trans h
  rw [orbitRelQuotientRec_mk]
  exact congrArg (· (t x)) (fiberMap_orbitRelQuotientDesc_mk a ha x)

/-- **Section descent commutes with dual pairing.** Pairing a descended dual section with a
descended primal section via `dualFiberEquiv` agrees with descending their upstairs pairing. -/
@[simp] theorem orbitRelQuotientLift_dualFiberEquiv [CompleteSpace 𝕜]
    (A : FiniteRankBundleCore 𝕜 (orbitRel.Quotient G M))
    {w : ∀ x : M, A.dual.core.Fiber (Quotient.mk (orbitRel G M) x)}
    {v : ∀ x : M, A.core.Fiber (Quotient.mk (orbitRel G M) x)}
    (hw : ∀ (g : G) (x : M), w (g • x) ≍ w x) (hv : ∀ (g : G) (x : M), v (g • x) ≍ v x)
    (hwv : ∀ (g : G) (x : M),
      dualFiberEquiv (A.pullback (continuousQuotientMk G M)) (g • x) (w (g • x)) (v (g • x)) =
        dualFiberEquiv (A.pullback (continuousQuotientMk G M)) x (w x) (v x) := fun g x ↦
      (dualFiberEquiv_pullback_apply A (continuousQuotientMk G M) (g • x) (w (g • x))
        (v (g • x))).trans ((eq_of_heq (apply₂_smul_heq (fun q w' v' ↦ dualFiberEquiv A q w' v')
          hw hv g x)).trans
          (dualFiberEquiv_pullback_apply A (continuousQuotientMk G M) x (w x) (v x)).symm))
    (z : orbitRel.Quotient G M) :
    orbitRelQuotientLift
        (fun x ↦ dualFiberEquiv (A.pullback (continuousQuotientMk G M)) x (w x) (v x)) hwv z =
      dualFiberEquiv A z (orbitRelQuotientRec w hw z) (orbitRelQuotientRec v hv z) := by
  rw [← orbitRelQuotientRec_const hwv]
  have h := orbitRelQuotientRec_map₂ (W := Trivial (orbitRel.Quotient G M) 𝕜)
    (fun q w' v' ↦ dualFiberEquiv A q w' v') hw hv z
  refine (congrFun (eq_orbitRelQuotientRec_iff.2 fun x ↦ ?_) z).symm.trans h
  rw [orbitRelQuotientRec_mk]
  exact (dualFiberEquiv_pullback_apply A (continuousQuotientMk G M) x (w x) (v x)).symm

/-- For continuous `G`-invariant dual and primal sections over `M`, their descended scalar pairing
on `M ⧸ G` is continuous. -/
theorem continuous_orbitRelQuotientLift_dualFiberEquiv [CompleteSpace 𝕜]
    (A : FiniteRankBundleCore 𝕜 (orbitRel.Quotient G M))
    {w : ∀ x : M, A.dual.core.Fiber (Quotient.mk (orbitRel G M) x)}
    {v : ∀ x : M, A.core.Fiber (Quotient.mk (orbitRel G M) x)}
    (hw : ∀ (g : G) (x : M), w (g • x) ≍ w x) (hv : ∀ (g : G) (x : M), v (g • x) ≍ v x)
    (hwc : Continuous fun x ↦
      TotalSpace.mk' (Fin (A.pullback (continuousQuotientMk G M)).dual.rank → 𝕜)
        (E := (A.pullback (continuousQuotientMk G M)).dual.core.Fiber) x (w x))
    (hvc : Continuous fun x ↦ TotalSpace.mk' (Fin (A.pullback (continuousQuotientMk G M)).rank → 𝕜)
      (E := (A.pullback (continuousQuotientMk G M)).core.Fiber) x (v x))
    (hwv : ∀ (g : G) (x : M),
      dualFiberEquiv (A.pullback (continuousQuotientMk G M)) (g • x) (w (g • x)) (v (g • x)) =
        dualFiberEquiv (A.pullback (continuousQuotientMk G M)) x (w x) (v x) := fun g x ↦
      (dualFiberEquiv_pullback_apply A (continuousQuotientMk G M) (g • x) (w (g • x))
        (v (g • x))).trans ((eq_of_heq (apply₂_smul_heq (fun q w' v' ↦ dualFiberEquiv A q w' v')
          hw hv g x)).trans
          (dualFiberEquiv_pullback_apply A (continuousQuotientMk G M) x (w x) (v x)).symm)) :
    Continuous (orbitRelQuotientLift
      (fun x ↦ dualFiberEquiv (A.pullback (continuousQuotientMk G M)) x (w x) (v x)) hwv) :=
  continuous_orbitRelQuotientLift_iff.2 <|
    continuous_snd.comp ((Bundle.Trivial.homeomorphProd M 𝕜).continuous.comp
      (((continuous_dualFiberEquiv (A.pullback (continuousQuotientMk G M))).comp hwc)
        |>.clm_bundle_apply hvc))

/-- **Section descent commutes with pure tensor products.** -/
@[simp] theorem orbitRelQuotientRec_pureTensorSection
    (A D : FiniteRankBundleCore 𝕜 (orbitRel.Quotient G M))
    {s₁ : ∀ x : M, A.core.Fiber (Quotient.mk (orbitRel G M) x)}
    {s₂ : ∀ x : M, D.core.Fiber (Quotient.mk (orbitRel G M) x)}
    (hs₁ : ∀ (g : G) (x : M), s₁ (g • x) ≍ s₁ x) (hs₂ : ∀ (g : G) (x : M), s₂ (g • x) ≍ s₂ x)
    (hst : ∀ (g : G) (x : M),
      (pureTensorSection (A.pullback (continuousQuotientMk G M))
        (D.pullback (continuousQuotientMk G M)) s₁ s₂ (g • x) :
          (tensor A D).core.Fiber (Quotient.mk (orbitRel G M) (g • x))) ≍
      (pureTensorSection (A.pullback (continuousQuotientMk G M))
        (D.pullback (continuousQuotientMk G M)) s₁ s₂ x :
          (tensor A D).core.Fiber (Quotient.mk (orbitRel G M) x)))
    (z : orbitRel.Quotient G M) :
    orbitRelQuotientRec (V := (tensor A D).core.Fiber)
        (pureTensorSection (A.pullback (continuousQuotientMk G M))
          (D.pullback (continuousQuotientMk G M)) s₁ s₂) hst z =
      pureTensorSection A D (orbitRelQuotientRec s₁ hs₁) (orbitRelQuotientRec s₂ hs₂) z := by
  let F : ∀ q, A.core.Fiber q → D.core.Fiber q → (tensor A D).core.Fiber q :=
    fun q v₁ v₂ ↦ pureTensorSection A D (fun _ ↦ v₁) (fun _ ↦ v₂) q
  have h := orbitRelQuotientRec_map₂ F hs₁ hs₂ z
  have hpure : F z (orbitRelQuotientRec s₁ hs₁ z) (orbitRelQuotientRec s₂ hs₂ z) =
      pureTensorSection A D (orbitRelQuotientRec s₁ hs₁) (orbitRelQuotientRec s₂ hs₂) z := by
    funext k
    obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective k
    exact (pureTensorSection_apply_finProdFinEquiv A D
      (fun _ ↦ orbitRelQuotientRec s₁ hs₁ z) (fun _ ↦ orbitRelQuotientRec s₂ hs₂ z) z i j).trans
      (pureTensorSection_apply_finProdFinEquiv A D
        (orbitRelQuotientRec s₁ hs₁) (orbitRelQuotientRec s₂ hs₂) z i j).symm
  refine ((congrFun (eq_orbitRelQuotientRec_iff.2 fun x ↦ ?_) z).symm.trans h).trans hpure
  rw [orbitRelQuotientRec_mk]
  funext k
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective k
  exact (pureTensorSection_apply_finProdFinEquiv A D (fun _ ↦ s₁ x) (fun _ ↦ s₂ x)
      (Quotient.mk (orbitRel G M) x) i j).trans
    (pureTensorSection_apply_finProdFinEquiv (A.pullback (continuousQuotientMk G M))
      (D.pullback (continuousQuotientMk G M)) s₁ s₂ x i j).symm

/-- Descending the pure tensor of two continuous `G`-invariant sections yields a continuous section
of `tensor A D` over `M ⧸ G`. -/
theorem continuous_section_orbitRelQuotientRec_pureTensorSection
    (A D : FiniteRankBundleCore 𝕜 (orbitRel.Quotient G M))
    {s₁ : ∀ x : M, A.core.Fiber (Quotient.mk (orbitRel G M) x)}
    {s₂ : ∀ x : M, D.core.Fiber (Quotient.mk (orbitRel G M) x)}
    (hs₁ : ∀ (g : G) (x : M), s₁ (g • x) ≍ s₁ x) (hs₂ : ∀ (g : G) (x : M), s₂ (g • x) ≍ s₂ x)
    (hs₁c : Continuous fun x ↦ TotalSpace.mk' (Fin (A.pullback (continuousQuotientMk G M)).rank → 𝕜)
      (E := (A.pullback (continuousQuotientMk G M)).core.Fiber) x (s₁ x))
    (hs₂c : Continuous fun x ↦ TotalSpace.mk' (Fin (D.pullback (continuousQuotientMk G M)).rank → 𝕜)
      (E := (D.pullback (continuousQuotientMk G M)).core.Fiber) x (s₂ x))
    (hst : ∀ (g : G) (x : M),
      (pureTensorSection (A.pullback (continuousQuotientMk G M))
        (D.pullback (continuousQuotientMk G M)) s₁ s₂ (g • x) :
          (tensor A D).core.Fiber (Quotient.mk (orbitRel G M) (g • x))) ≍
      (pureTensorSection (A.pullback (continuousQuotientMk G M))
        (D.pullback (continuousQuotientMk G M)) s₁ s₂ x :
          (tensor A D).core.Fiber (Quotient.mk (orbitRel G M) x))) :
    Continuous fun z ↦ TotalSpace.mk' (Fin (tensor A D).rank → 𝕜) z
      (orbitRelQuotientRec (V := (tensor A D).core.Fiber)
        (pureTensorSection (A.pullback (continuousQuotientMk G M))
          (D.pullback (continuousQuotientMk G M)) s₁ s₂) hst z) := by
  refine (continuous_pureTensorSection A D
    ((continuous_section_orbitRelQuotientRec_core_iff A hs₁).2 hs₁c)
    ((continuous_section_orbitRelQuotientRec_core_iff D hs₂).2 hs₂c)).congr fun z ↦
    congrArg (TotalSpace.mk' (Fin (tensor A D).rank → 𝕜) z)
      (orbitRelQuotientRec_pureTensorSection A D hs₁ hs₂ hst z).symm

/-- **Section descent commutes with exterior powers (`wedgeSection`).** -/
@[simp] theorem orbitRelQuotientRec_wedgeSection (j : ℕ)
    (A : FiniteRankBundleCore 𝕜 (orbitRel.Quotient G M))
    {s : Fin j → ∀ x : M, A.core.Fiber (Quotient.mk (orbitRel G M) x)}
    (hs : ∀ (k : Fin j) (g : G) (x : M), s k (g • x) ≍ s k x)
    (hws : ∀ (g : G) (x : M),
      (wedgeSection j (A.pullback (continuousQuotientMk G M)) s (g • x) :
        ((exteriorPower 𝕜 (orbitRel.Quotient G M) j).obj A).core.Fiber
          (Quotient.mk (orbitRel G M) (g • x))) ≍
      (wedgeSection j (A.pullback (continuousQuotientMk G M)) s x :
        ((exteriorPower 𝕜 (orbitRel.Quotient G M) j).obj A).core.Fiber
          (Quotient.mk (orbitRel G M) x)))
    (z : orbitRel.Quotient G M) :
    orbitRelQuotientRec (V := ((exteriorPower 𝕜 (orbitRel.Quotient G M) j).obj A).core.Fiber)
        (wedgeSection j (A.pullback (continuousQuotientMk G M)) s) hws z =
      wedgeSection j A (fun k ↦ orbitRelQuotientRec (s k) (hs k)) z := by
  let F : ∀ q, (Fin j → A.core.Fiber q) →
      ((exteriorPower 𝕜 (orbitRel.Quotient G M) j).obj A).core.Fiber q :=
    fun q u ↦ wedgeSection j A (fun k _ ↦ u k) q
  have hmap := orbitRelQuotientRec_map (t := fun x k ↦ s k x) F (pi_smul_heq hs) z
  have hrec : orbitRelQuotientRec
      (V := ((exteriorPower 𝕜 (orbitRel.Quotient G M) j).obj A).core.Fiber)
      (wedgeSection j (A.pullback (continuousQuotientMk G M)) s) hws =
      orbitRelQuotientRec (fun x ↦ F (Quotient.mk (orbitRel G M) x) (fun k ↦ s k x))
        (apply_smul_heq (t := fun x k ↦ s k x) F (pi_smul_heq hs)) :=
    (eq_orbitRelQuotientRec_iff.2 fun x ↦ by
      rw [orbitRelQuotientRec_mk]
      exact (wedgeSection_pullback_apply j A (continuousQuotientMk G M) s x).symm).symm
  rw [congrFun hrec z, hmap, orbitRelQuotientRec_pi hs z]
  exact wedgeSection_congr fun _ ↦ rfl

/-- Descending the exterior product of `j` continuous `G`-invariant sections yields a continuous
section of `(exteriorPower 𝕜 (M ⧸ G) j).obj A`. -/
theorem continuous_section_orbitRelQuotientRec_wedgeSection (j : ℕ)
    (A : FiniteRankBundleCore 𝕜 (orbitRel.Quotient G M))
    {s : Fin j → ∀ x : M, A.core.Fiber (Quotient.mk (orbitRel G M) x)}
    (hs : ∀ (k : Fin j) (g : G) (x : M), s k (g • x) ≍ s k x)
    (hsc : ∀ k, Continuous fun x ↦
      TotalSpace.mk' (Fin (A.pullback (continuousQuotientMk G M)).rank → 𝕜)
        (E := (A.pullback (continuousQuotientMk G M)).core.Fiber) x (s k x))
    (hws : ∀ (g : G) (x : M),
      (wedgeSection j (A.pullback (continuousQuotientMk G M)) s (g • x) :
        ((exteriorPower 𝕜 (orbitRel.Quotient G M) j).obj A).core.Fiber
          (Quotient.mk (orbitRel G M) (g • x))) ≍
      (wedgeSection j (A.pullback (continuousQuotientMk G M)) s x :
        ((exteriorPower 𝕜 (orbitRel.Quotient G M) j).obj A).core.Fiber
          (Quotient.mk (orbitRel G M) x))) :
    Continuous fun z ↦
      TotalSpace.mk' (Fin ((exteriorPower 𝕜 (orbitRel.Quotient G M) j).obj A).rank → 𝕜) z
        (orbitRelQuotientRec (V := ((exteriorPower 𝕜 (orbitRel.Quotient G M) j).obj A).core.Fiber)
          (wedgeSection j (A.pullback (continuousQuotientMk G M)) s) hws z) :=
  (continuous_wedgeSection j A fun k ↦
    (continuous_section_orbitRelQuotientRec_core_iff A (hs k)).2 (hsc k)).congr fun z ↦
    congrArg (TotalSpace.mk' (Fin ((exteriorPower 𝕜 (orbitRel.Quotient G M) j).obj A).rank → 𝕜) z)
      (orbitRelQuotientRec_wedgeSection j A hs hws z).symm

/-- **Section descent commutes with determinant wedges (`detSection`).** -/
@[simp] theorem orbitRelQuotientRec_detSection (A : FiniteRankBundleCore 𝕜 (orbitRel.Quotient G M))
    {s : Fin A.rank → ∀ x : M, A.core.Fiber (Quotient.mk (orbitRel G M) x)}
    (hs : ∀ (k : Fin A.rank) (g : G) (x : M), s k (g • x) ≍ s k x)
    (hds : ∀ (g : G) (x : M),
      (detSection (A.pullback (continuousQuotientMk G M)) s (g • x) :
        A.det.core.Fiber (Quotient.mk (orbitRel G M) (g • x))) ≍
      (detSection (A.pullback (continuousQuotientMk G M)) s x :
        A.det.core.Fiber (Quotient.mk (orbitRel G M) x)))
    (z : orbitRel.Quotient G M) :
    orbitRelQuotientRec (V := A.det.core.Fiber)
        (detSection (A.pullback (continuousQuotientMk G M)) s) hds z =
      detSection A (fun k ↦ orbitRelQuotientRec (s k) (hs k)) z :=
  orbitRelQuotientRec_wedgeSection A.rank A hs hds z

/-- Descending the determinant wedge of `A.rank` continuous `G`-invariant sections yields a
continuous section of `A.det` over `M ⧸ G`. -/
theorem continuous_section_orbitRelQuotientRec_detSection
    (A : FiniteRankBundleCore 𝕜 (orbitRel.Quotient G M))
    {s : Fin A.rank → ∀ x : M, A.core.Fiber (Quotient.mk (orbitRel G M) x)}
    (hs : ∀ (k : Fin A.rank) (g : G) (x : M), s k (g • x) ≍ s k x)
    (hsc : ∀ k, Continuous fun x ↦
      TotalSpace.mk' (Fin (A.pullback (continuousQuotientMk G M)).rank → 𝕜)
        (E := (A.pullback (continuousQuotientMk G M)).core.Fiber) x (s k x))
    (hds : ∀ (g : G) (x : M),
      (detSection (A.pullback (continuousQuotientMk G M)) s (g • x) :
        A.det.core.Fiber (Quotient.mk (orbitRel G M) (g • x))) ≍
      (detSection (A.pullback (continuousQuotientMk G M)) s x :
        A.det.core.Fiber (Quotient.mk (orbitRel G M) x))) :
    Continuous fun z ↦ TotalSpace.mk' (Fin A.det.rank → 𝕜) z
      (orbitRelQuotientRec (V := A.det.core.Fiber)
        (detSection (A.pullback (continuousQuotientMk G M)) s) hds z) :=
  (continuous_detSection A fun k ↦
    (continuous_section_orbitRelQuotientRec_core_iff A (hs k)).2 (hsc k)).congr fun z ↦
    congrArg (TotalSpace.mk' (Fin A.det.rank → 𝕜) z)
      (orbitRelQuotientRec_detSection A hs hds z).symm

end SectionDescent

end TauCeti.FiniteRankBundleCore
