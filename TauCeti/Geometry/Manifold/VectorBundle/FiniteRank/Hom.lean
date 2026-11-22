/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Hom
public import TauCeti.Geometry.Manifold.ContMDiff.Kronecker
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteRank.Picard

/-!
# Smooth and holomorphic Hom cores

The Hom core `FiniteRankBundleCore.hom A D` of two finite-rank `C^n` cores is `C^n`: its
transitions are the operator conjugations `homCoordConj (A.core.coordChange j i x)
(D.core.coordChange i j x)` of the original transitions. Over a complex manifold at regularity
`∞` this is the holomorphic Hom bundle, on the existing Hom-core carrier.

The bifunctor `homMap`, the evaluation `homEv` and the currying `homCurry` preserve regularity:

* `contMDiffOn_inChartCoordinates_homMap`: in charts, `homMap f g` is the operator conjugation of
  the chart operators of `f` and `g`, so `C^n` chart operators give `C^n` chart operators, without
  completeness of `𝕜` or regularity of the cores;
* `contMDiff_totalSpaceMap_homMap`, `contMDiff_totalSpaceMap_homEv`,
  `contMDiff_totalSpaceMap_homCurry`: between `C^n` cores, these bundle maps are `C^n` on total
  spaces whenever their inputs are.

Consequently the tensor-Hom adjunction of finite-rank cores restricts to `C^n` cores and `C^n`
bundle maps, and `ContMDiffFiniteRankBundleCore I n B` is a monoidal closed category whose
internal Hom has underlying core `FiniteRankBundleCore.hom`
(`ContMDiffFiniteRankBundleCore.toCore_ihom_obj`), with evaluation, coevaluation, currying and
precomposition given by the corresponding maps of finite-rank cores. For `I = 𝓘(ℂ, EB)` and
`n = ∞` this is the closed structure of holomorphic finite-rank cores.

Over a complete scalar field, `FiniteRankBundleCore.homTotalSpaceDiffeomorph` identifies the
total space of `hom A D` with Mathlib's Hom bundle between `A.core.Fiber` and `D.core.Fiber`.
Its underlying homeomorphism is `FiniteRankBundleCore.homTotalSpaceHomeomorph`, so it reads a
coordinate vector as an operator through `ContinuousLinearEquiv.finProdCLM` on every fibre.

## References

* J. W. Milnor and J. D. Stasheff, *Characteristic Classes*, §3.
* D. Huybrechts, *Complex Geometry: An Introduction*, §2.2.
-/

public section

open Bundle CategoryTheory MonoidalCategory Set VectorBundleCore
open scoped Manifold ContDiff

namespace TauCeti.FiniteRankBundleCore

open ContinuousLinearEquiv ContinuousLinearMap

variable {𝕜 B : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]
  {EB HB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  [TopologicalSpace HB] [ChartedSpace HB B] {I : ModelWithCorners 𝕜 EB HB} {n : ℕ∞ω}

/-- The Hom core of two finite-rank `C^n` cores is `C^n`. For complex scalars and `n = ∞`,
this equips the shared Hom core with its holomorphic structure. -/
instance isContMDiff_hom (A D : FiniteRankBundleCore 𝕜 B)
    [A.core.IsContMDiff I n] [D.core.IsContMDiff I n] :
    (hom A D).core.IsContMDiff I n where
  contMDiffOn_coordChange i j :=
    ((A.core.contMDiffOn_coordChange (n := n) I j i).mono
      fun _ (hx : _ ∈ (A.core.baseSet i ∩ D.core.baseSet i) ∩
        (A.core.baseSet j ∩ D.core.baseSet j)) ↦ ⟨hx.2.1, hx.1.1⟩).clm_homCoordConj
      ((D.core.contMDiffOn_coordChange (n := n) I i j).mono
        (inter_subset_inter inter_subset_right inter_subset_right))

variable {A A' D D' C : FiniteRankBundleCore 𝕜 B}

/-- If the chart operators of `f` and `g` are `C^n`, so are the chart operators of `homMap f g`.
Neither regularity of the cores nor completeness of `𝕜` is needed. -/
theorem contMDiffOn_inChartCoordinates_homMap (f : A' ⟶ A) (g : D ⟶ D')
    (hf : ∀ i j, ContMDiffOn I 𝓘(𝕜, (Fin A'.rank → 𝕜) →L[𝕜] (Fin A.rank → 𝕜)) n
      (fun x ↦ A'.core.inChartCoordinates A.core i j x (f.fiberMap x))
      (A'.core.baseSet i ∩ A.core.baseSet j))
    (hg : ∀ i j, ContMDiffOn I 𝓘(𝕜, (Fin D.rank → 𝕜) →L[𝕜] (Fin D'.rank → 𝕜)) n
      (fun x ↦ D.core.inChartCoordinates D'.core i j x (g.fiberMap x))
      (D.core.baseSet i ∩ D'.core.baseSet j)) (i j : B) :
    ContMDiffOn I 𝓘(𝕜, (Fin (hom A D).rank → 𝕜) →L[𝕜] (Fin (hom A' D').rank → 𝕜)) n
      (fun x ↦ (hom A D).core.inChartCoordinates (hom A' D').core i j x
        ((homMap f g).fiberMap x))
      ((hom A D).core.baseSet i ∩ (hom A' D').core.baseSet j) :=
  (((hf j i).mono fun _ (hx : _ ∈ (A.core.baseSet i ∩ D.core.baseSet i) ∩
      (A'.core.baseSet j ∩ D'.core.baseSet j)) ↦ ⟨hx.2.1, hx.1.1⟩).clm_homCoordConj
    ((hg i j).mono (inter_subset_inter inter_subset_right inter_subset_right))).congr
      fun _ hx ↦ inChartCoordinates_homMap f g hx

section IsContMDiff

variable [A.core.IsContMDiff I n] [A'.core.IsContMDiff I n]
  [D.core.IsContMDiff I n] [D'.core.IsContMDiff I n] [C.core.IsContMDiff I n]

omit [C.core.IsContMDiff I n] in
/-- `homMap` of `C^n` bundle maps between `C^n` cores is `C^n` on total spaces, without
completeness of the scalar field. In particular, the Hom bifunctor preserves holomorphic bundle
maps. -/
theorem contMDiff_totalSpaceMap_homMap (f : A' ⟶ A) (g : D ⟶ D')
    (hf : ContMDiff (I.prod 𝓘(𝕜, Fin A'.rank → 𝕜)) (I.prod 𝓘(𝕜, Fin A.rank → 𝕜)) n
      f.totalSpaceMap)
    (hg : ContMDiff (I.prod 𝓘(𝕜, Fin D.rank → 𝕜)) (I.prod 𝓘(𝕜, Fin D'.rank → 𝕜)) n
      g.totalSpaceMap) :
    ContMDiff (I.prod 𝓘(𝕜, Fin (hom A D).rank → 𝕜))
      (I.prod 𝓘(𝕜, Fin (hom A' D').rank → 𝕜)) n (homMap f g).totalSpaceMap :=
  (homMap f g).contMDiff_totalSpaceMap
    (contMDiffOn_inChartCoordinates_homMap f g
      (contMDiffOn_inChartCoordinates_of_contMDiff_totalSpaceMap f hf)
      (contMDiffOn_inChartCoordinates_of_contMDiff_totalSpaceMap g hg))

omit [A'.core.IsContMDiff I n] [D'.core.IsContMDiff I n] [C.core.IsContMDiff I n] in
/-- The evaluation map `A ⊗ hom A D ⟶ D` of `C^n` cores is `C^n` on total spaces. -/
theorem contMDiff_totalSpaceMap_homEv :
    ContMDiff (I.prod 𝓘(𝕜, Fin (A ⊗ hom A D).rank → 𝕜)) (I.prod 𝓘(𝕜, Fin D.rank → 𝕜)) n
      (homEv A D).totalSpaceMap := by
  refine (homEv A D).contMDiff_totalSpaceMap fun i j ↦ ?_
  -- In the charts at `i`, evaluation is the constant operator `kroneckerHomEv`.
  refine contMDiffOn_inChartCoordinates_of_coordChange_comp (homEv A D)
    (fun _ (hx : _ ∈ A.core.baseSet i ∩ (A.core.baseSet i ∩ D.core.baseSet i)) ↦ hx.2.2)
    (kroneckerHomEv 𝕜 A.rank D.rank) fun x hx v ↦ ?_
  have hx' : x ∈ A.core.baseSet i := hx.1.1
  have hcomp : (A.core.coordChange x i x).comp (A.core.coordChange i x x) =
      ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜) :=
    (A.core.coordChange_linear_comp i x i x ⟨⟨hx', A.mem_baseSet_self x⟩, hx'⟩).trans
      (A.core.coordChange_self_eq_id hx')
  rw [fiberMap_homEv, coordChange_tensorObj, coordChange_hom]
  exact DFunLike.congr_fun
    (kroneckerHomEv_comp_kronecker_homCoordConj hcomp (D.core.coordChange i x x)) v

omit [A'.core.IsContMDiff I n] [D.core.IsContMDiff I n] [D'.core.IsContMDiff I n] in
/-- The coevaluation map `C ⟶ hom A (A ⊗ C)` of `C^n` cores is `C^n` on total spaces. -/
theorem contMDiff_totalSpaceMap_homCurry_id :
    ContMDiff (I.prod 𝓘(𝕜, Fin C.rank → 𝕜)) (I.prod 𝓘(𝕜, Fin (hom A (A ⊗ C)).rank → 𝕜)) n
      (homCurry (𝟙 (A ⊗ C))).totalSpaceMap := by
  refine (homCurry (𝟙 (A ⊗ C))).contMDiff_totalSpaceMap fun i j ↦ ?_
  -- In the charts at `j`, coevaluation is the constant operator `kroneckerCurry (id)`.
  refine contMDiffOn_inChartCoordinates_of_comp_coordChange (homCurry (𝟙 (A ⊗ C)))
    (fun _ (hx : _ ∈ A.core.baseSet j ∩ (A.core.baseSet j ∩ C.core.baseSet j)) ↦ hx.2.2)
    (kroneckerCurry 𝕜 A.rank C.rank (A ⊗ C).rank (ContinuousLinearMap.id 𝕜 _))
    fun x hx v ↦ ?_
  have hx' : x ∈ A.core.baseSet j := hx.2.1
  have hcomp : (A.core.coordChange x j x).comp (A.core.coordChange j x x) =
      ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜) :=
    (A.core.coordChange_linear_comp j x j x ⟨⟨hx', A.mem_baseSet_self x⟩, hx'⟩).trans
      (A.core.coordChange_self_eq_id hx')
  rw [fiberMap_homCurry, fiberMap_id, coordChange_hom, coordChange_tensorObj]
  exact DFunLike.congr_fun
    (homCoordConj_kronecker_comp_kroneckerCurry_id hcomp (C.core.coordChange x j x)) v

omit [A'.core.IsContMDiff I n] [D'.core.IsContMDiff I n] in
/-- Currying a `C^n` bundle map `A ⊗ C ⟶ D` of `C^n` cores gives a `C^n` bundle map
`C ⟶ hom A D`. -/
theorem contMDiff_totalSpaceMap_homCurry (f : A ⊗ C ⟶ D)
    (hf : ContMDiff (I.prod 𝓘(𝕜, Fin (A ⊗ C).rank → 𝕜)) (I.prod 𝓘(𝕜, Fin D.rank → 𝕜)) n
      f.totalSpaceMap) :
    ContMDiff (I.prod 𝓘(𝕜, Fin C.rank → 𝕜)) (I.prod 𝓘(𝕜, Fin (hom A D).rank → 𝕜)) n
      (homCurry f).totalSpaceMap := by
  -- Currying factors through the coevaluation: `homCurry f = homCurry 𝟙 ≫ homMap 𝟙 f`.
  have h : homCurry f = homCurry (𝟙 (A ⊗ C)) ≫ homMap (𝟙 A) f := by
    rw [← homCurry_comp, Category.id_comp]
  rw [h]
  exact CoordinateHom.contMDiff_totalSpaceMap_comp
    (contMDiff_totalSpaceMap_homMap (𝟙 A) f (CoordinateHom.contMDiff_totalSpaceMap_id _) hf)
    contMDiff_totalSpaceMap_homCurry_id

end IsContMDiff

/-! ### Identification with Mathlib's Hom bundle -/

/-- Reading the vectors of the Hom core as operators is `C^n` on total spaces, in the induced
Hom-bundle charts. -/
theorem contMDiff_homFiberEquiv (A D : FiniteRankBundleCore 𝕜 B) :
    ContMDiff (I.prod 𝓘(𝕜, Fin (hom A D).rank → 𝕜))
      (I.prod 𝓘(𝕜, (Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜))) n
      (fun p : (hom A D).core.TotalSpace ↦
        TotalSpace.mk' ((Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜))
          (E := fun x ↦ A.core.Fiber x →L[𝕜] D.core.Fiber x) p.proj
          (homFiberEquiv A D p.proj p.snd)) := by
  intro p
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_proj _, ?_⟩
  have hp : p ∈ ((hom A D).core.localTriv p.proj).source :=
    ((hom A D).core.mem_localTriv_source p.proj p).2 ((hom A D).core.mem_baseSet_at p.proj)
  have hU := ((hom A D).core.localTriv p.proj).open_source.mem_nhds hp
  refine ((finProdCLM 𝕜 A.rank D.rank).contDiff.contMDiff.contMDiffAt.comp p
    ((hom A D).contMDiffAt_localTriv_snd (I := I) (n := n) p)).congr_of_eventuallyEq ?_
  filter_upwards [hU] with q hq
  have hq' := ((hom A D).core.mem_localTriv_source p.proj q).1 hq
  exact homFiberEquiv_inCoordinates A D p.proj q.proj hq'.1 hq'.2 q.snd

variable [CompleteSpace 𝕜]

/-- The Hom core and Mathlib's Hom bundle are `C^n` diffeomorphic by the canonical
identification `homFiberEquiv` of each coordinate vector with an operator between fibres. -/
noncomputable def homTotalSpaceDiffeomorph (A D : FiniteRankBundleCore 𝕜 B)
    (I : ModelWithCorners 𝕜 EB HB) (n : ℕ∞ω) :
    (hom A D).core.TotalSpace ≃ₘ^n⟮I.prod 𝓘(𝕜, Fin (hom A D).rank → 𝕜),
      I.prod 𝓘(𝕜, (Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜))⟯
        TotalSpace ((Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜))
          (fun x ↦ A.core.Fiber x →L[𝕜] D.core.Fiber x) :=
  bundleDiffeomorph (homFiberEquiv A D) (contMDiff_homFiberEquiv (I := I) (n := n) A D)

/-- The diffeomorphism retains the canonical Hom-bundle homeomorphism. -/
@[simp]
theorem homTotalSpaceDiffeomorph_toHomeomorph (A D : FiniteRankBundleCore 𝕜 B) :
    (homTotalSpaceDiffeomorph A D I n).toHomeomorph = homTotalSpaceHomeomorph A D :=
  Homeomorph.ext fun p ↦ (bundleDiffeomorph_apply (IB := I) (n := n) (homFiberEquiv A D)
    (contMDiff_homFiberEquiv A D) p).trans (homTotalSpaceHomeomorph_apply A D p).symm

/-- The forward comparison reads a Hom coordinate vector as an operator in the same fibre. -/
@[simp]
theorem homTotalSpaceDiffeomorph_apply (A D : FiniteRankBundleCore 𝕜 B)
    (p : (hom A D).core.TotalSpace) :
    homTotalSpaceDiffeomorph A D I n p = ⟨p.proj, homFiberEquiv A D p.proj p.snd⟩ :=
  bundleDiffeomorph_apply _ _ p

/-- The inverse comparison records the matrix coefficients of the operator in the same fibre. -/
@[simp]
theorem homTotalSpaceDiffeomorph_symm_apply (A D : FiniteRankBundleCore 𝕜 B)
    (p : TotalSpace ((Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜))
      (fun x ↦ A.core.Fiber x →L[𝕜] D.core.Fiber x)) :
    (homTotalSpaceDiffeomorph A D I n).symm p =
      ⟨p.proj, (homFiberEquiv A D p.proj).symm p.snd⟩ :=
  bundleDiffeomorph_symm_apply _ _ p

end TauCeti.FiniteRankBundleCore

/-! ### The monoidal closed category of `C^n` cores -/

namespace TauCeti.ContMDiffFiniteRankBundleCore

open FiniteRankBundleCore (hom homMap homCurry)

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {I : ModelWithCorners 𝕜 EB HB} {n : ℕ∞ω}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]

/-- The internal Hom functor `D ↦ hom A D` on `C^n` cores, acting on `C^n` bundle maps by
postcomposition. -/
-- Expose the object map so that `((homRightFunctor A).obj D).toCore` reduces to `hom`.
@[expose]
noncomputable def homRightFunctor (A : ContMDiffFiniteRankBundleCore I n B) :
    ContMDiffFiniteRankBundleCore I n B ⥤ ContMDiffFiniteRankBundleCore I n B where
  obj D := ⟨hom A.toCore D.toCore, inferInstance⟩
  map g := ⟨homMap (𝟙 A.toCore) g.toHom,
    FiniteRankBundleCore.contMDiff_totalSpaceMap_homMap _ _
      (CoordinateHom.contMDiff_totalSpaceMap_id _) g.contMDiff_totalSpaceMap⟩
  map_id D := hom_ext (FiniteRankBundleCore.id_homMap_id _ _)
  map_comp f g := hom_ext (by
    simp only [comp_toHom, FiniteRankBundleCore.homMap_comp_homMap, Category.comp_id])

@[simp] theorem toCore_homRightFunctor_obj (A D : ContMDiffFiniteRankBundleCore I n B) :
    ((homRightFunctor A).obj D).toCore = hom A.toCore D.toCore := (rfl)

@[simp] theorem homRightFunctor_map_toHom (A : ContMDiffFiniteRankBundleCore I n B)
    {D D' : ContMDiffFiniteRankBundleCore I n B} (g : D ⟶ D') :
    ((homRightFunctor A).map g).toHom = homMap (𝟙 A.toCore) g.toHom := (rfl)

/-- The `C^n` evaluation map `A ⊗ hom A D ⟶ D`. -/
noncomputable def homEv (A D : ContMDiffFiniteRankBundleCore I n B) :
    A ⊗ (homRightFunctor A).obj D ⟶ D :=
  ⟨FiniteRankBundleCore.homEv A.toCore D.toCore, FiniteRankBundleCore.contMDiff_totalSpaceMap_homEv⟩

@[simp] theorem homEv_toHom (A D : ContMDiffFiniteRankBundleCore I n B) :
    (homEv A D).toHom = FiniteRankBundleCore.homEv A.toCore D.toCore := (rfl)

/-- Currying of `C^n` bundle maps `A ⊗ X ⟶ Y` to `C^n` bundle maps `X ⟶ hom A Y`, with inverse
given by evaluation. -/
noncomputable def homCurryEquiv (A X Y : ContMDiffFiniteRankBundleCore I n B) :
    (A ⊗ X ⟶ Y) ≃ (X ⟶ (homRightFunctor A).obj Y) where
  toFun f := ⟨homCurry f.toHom,
    FiniteRankBundleCore.contMDiff_totalSpaceMap_homCurry f.toHom f.contMDiff_totalSpaceMap⟩
  invFun g := (A ◁ g) ≫ homEv A Y
  left_inv f := hom_ext <| by
    simp only [comp_toHom, whiskerLeft_toHom, homEv_toHom]
    exact FiniteRankBundleCore.whiskerLeft_homCurry_homEv f.toHom
  right_inv g := hom_ext <| by
    simp only [comp_toHom, whiskerLeft_toHom, homEv_toHom]
    exact FiniteRankBundleCore.homCurry_whiskerLeft_homEv g.toHom

@[simp] theorem homCurryEquiv_apply_toHom (A X Y : ContMDiffFiniteRankBundleCore I n B)
    (f : A ⊗ X ⟶ Y) : (homCurryEquiv A X Y f).toHom = homCurry f.toHom := (rfl)

@[simp] theorem homCurryEquiv_symm_apply (A X Y : ContMDiffFiniteRankBundleCore I n B)
    (g : X ⟶ (homRightFunctor A).obj Y) :
    (homCurryEquiv A X Y).symm g = (A ◁ g) ≫ homEv A Y := (rfl)

/-- The tensor-Hom adjunction `tensorLeft A ⊣ homRightFunctor A` for `C^n` cores. -/
noncomputable def homAdjunction (A : ContMDiffFiniteRankBundleCore I n B) :
    tensorLeft A ⊣ homRightFunctor A :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y ↦ homCurryEquiv A X Y
      homEquiv_naturality_left_symm := fun h g ↦ by simp [homCurryEquiv_symm_apply]
      homEquiv_naturality_right := fun f k ↦ hom_ext <| by
        simp only [comp_toHom, homRightFunctor_map_toHom]
        exact FiniteRankBundleCore.homCurry_comp f.toHom k.toHom }

theorem homAdjunction_homEquiv (A X Y : ContMDiffFiniteRankBundleCore I n B) :
    (homAdjunction A).homEquiv X Y = homCurryEquiv A X Y := by
  rw [homAdjunction, Adjunction.mkOfHomEquiv_homEquiv]

/-- `C^n` finite-rank cores form a monoidal closed category, with internal Hom the Hom core.
Over a complex manifold at regularity `∞` this is the closed structure of holomorphic cores. -/
noncomputable instance : MonoidalClosed (ContMDiffFiniteRankBundleCore I n B) where
  closed A := { rightAdj := homRightFunctor A, adj := homAdjunction A }

@[simp] theorem toCore_ihom_obj (A D : ContMDiffFiniteRankBundleCore I n B) :
    ((ihom A).obj D).toCore = hom A.toCore D.toCore := (rfl)

@[simp] theorem ihom_map_toHom (A : ContMDiffFiniteRankBundleCore I n B)
    {D D' : ContMDiffFiniteRankBundleCore I n B} (g : D ⟶ D') :
    ((ihom A).map g).toHom = homMap (𝟙 A.toCore) g.toHom := (rfl)

theorem ihom_adjunction (A : ContMDiffFiniteRankBundleCore I n B) :
    ihom.adjunction A = homAdjunction A := (rfl)

@[simp] theorem monoidalClosed_curry_toHom {A X Y : ContMDiffFiniteRankBundleCore I n B}
    (f : A ⊗ X ⟶ Y) : (MonoidalClosed.curry f).toHom = homCurry f.toHom :=
  (congrArg Hom.toHom ((MonoidalClosed.homEquiv_apply_eq f).symm.trans
    (congrFun (congrArg DFunLike.coe (homAdjunction_homEquiv A X Y)) f))).trans
      (homCurryEquiv_apply_toHom A X Y f)

@[simp] theorem monoidalClosed_uncurry_toHom {A X Y : ContMDiffFiniteRankBundleCore I n B}
    (g : X ⟶ (ihom A).obj Y) :
    (MonoidalClosed.uncurry g).toHom =
      (A.toCore ◁ g.toHom) ≫ FiniteRankBundleCore.homEv A.toCore Y.toCore := by
  have h : MonoidalClosed.uncurry g = (homCurryEquiv A X Y).symm g :=
    (MonoidalClosed.homEquiv_symm_apply_eq g).symm.trans
      (congrFun (congrArg (fun e ↦ (e.symm : _ → _)) (homAdjunction_homEquiv A X Y)) g)
  -- `homCurryEquiv_symm_apply`, `comp_toHom`, `whiskerLeft_toHom` and `homEv_toHom` hold by `rfl`,
  -- but `rw` cannot use them: here the objects are only definitionally the Hom core.
  rw [h]
  rfl

@[simp] theorem ihom_ev_app_toHom (A D : ContMDiffFiniteRankBundleCore I n B) :
    ((ihom.ev A).app D).toHom = FiniteRankBundleCore.homEv A.toCore D.toCore := by
  rw [← MonoidalClosed.uncurry_id_eq_ev, monoidalClosed_uncurry_toHom, id_toHom,
    MonoidalCategory.whiskerLeft_id]
  exact Category.id_comp _

@[simp] theorem ihom_coev_app_toHom (A X : ContMDiffFiniteRankBundleCore I n B) :
    ((ihom.coev A).app X).toHom = homCurry (𝟙 (A.toCore ⊗ X.toCore)) := by
  -- The remaining goal identifies `(A ⊗ X).toCore` with `A.toCore ⊗ X.toCore`, as in
  -- `tensorObj_toCore`, inside the dependent argument of `homCurry`.
  rw [← MonoidalClosed.curry_id_eq_coev, monoidalClosed_curry_toHom, id_toHom]
  rfl

/-- Precomposition in the monoidal closed structure of `C^n` cores is `homMap f (𝟙 D)`. -/
@[simp] theorem monoidalClosed_pre_app_toHom {A A' : ContMDiffFiniteRankBundleCore I n B}
    (f : A' ⟶ A) (D : ContMDiffFiniteRankBundleCore I n B) :
    ((MonoidalClosed.pre f).app D).toHom = homMap f.toHom (𝟙 D.toCore) := by
  -- Both sides uncurry to `f ▷ hom A D ≫ homEv A D` in finite-rank cores.
  have h := congrArg Hom.toHom (MonoidalClosed.uncurry_pre f D)
  rw [monoidalClosed_uncurry_toHom, comp_toHom, whiskerRight_toHom, ihom_ev_app_toHom] at h
  have h' : (A'.toCore ◁ homMap f.toHom (𝟙 D.toCore)) ≫
      FiniteRankBundleCore.homEv A'.toCore D.toCore =
        (f.toHom ▷ hom A.toCore D.toCore) ≫ FiniteRankBundleCore.homEv A.toCore D.toCore := by
    rw [FiniteRankBundleCore.whiskerLeft_homMap_homEv, Category.comp_id]
  exact (FiniteRankBundleCore.homCurry_whiskerLeft_homEv _).symm.trans <|
    (congrArg homCurry (h.trans h'.symm)).trans
      (FiniteRankBundleCore.homCurry_whiskerLeft_homEv _)

end TauCeti.ContMDiffFiniteRankBundleCore
