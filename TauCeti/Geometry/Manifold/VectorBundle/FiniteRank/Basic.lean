/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CoordinateHom
public import TauCeti.Geometry.Manifold.VectorBundle.Trivialization
import Mathlib.Geometry.Manifold.ContMDiff.Constructions

/-!
# Smooth local fibre coordinates and intertwining maps of finite-rank bundle cores

For a point-indexed finite-rank vector-bundle core `E : FiniteRankBundleCore 𝕜 B` over a charted
space `B`, the preferred trivialization at a base point `x` is the chart `E.core.localTriv x`
(`FiniteRankBundleCore.trivializationAt_core`). Consequently, the fibre coordinate in
`E.core.localTriv p₀.proj` is `C^n` at every total-space point `p₀`
(`FiniteRankBundleCore.contMDiffAt_localTriv_snd`), without any smoothness hypothesis on the base
atlas or on the transition functions of `E`.

This file provides general `C^n` criteria for morphisms and bundle maps whose local coordinates are
intertwined by a fixed continuous linear map:

* `FiniteRankBundleCore.contMDiff_of_localTriv_snd`,
  `FiniteRankBundleCore.contMDiff_of_trivializationAt_snd`, and
  `FiniteRankBundleCore.contMDiff_totalSpaceMap_of_coordChange` establish `C^n` regularity of
  total-space maps without `C^n` assumptions on the cores;
* `FiniteRankBundleCore.contMDiffOn_inChartCoordinates_of_coordChange_comp` and
  `FiniteRankBundleCore.contMDiffOn_inChartCoordinates_of_comp_coordChange` establish `C^n`
  regularity of chart operators when the target or source core is `C^n`;
* `FiniteRankBundleCore.contMDiff_totalSpaceMap_iff_inChartCoordinates` shows that a bundle map
  between `C^n` cores has a `C^n` total-space map if and only if every chart operator is `C^n`,
  without completeness of `𝕜`, and `FiniteRankBundleCore.isoToDiffeomorph` turns an isomorphism
  with `C^n` forward and inverse total-space maps into a `C^n` diffeomorphism;
* `FiniteRankBundleCore.isContMDiff_trivial`,
  `FiniteRankBundleCore.contMDiff_totalSpaceMap_constHom`,
  `FiniteRankBundleCore.constIsoDiffeomorph`, and
  `FiniteRankBundleCore.contMDiff_totalSpaceMap_isoTrivialOfCoordChangeEqId_hom` show that trivial
  cores are `C^n` and that constant intertwining maps and identity-transition trivializations
  induce `C^n` maps and diffeomorphisms of total spaces without smoothness or completeness
  assumptions.

## References

* D. Huybrechts, *Complex Geometry: An Introduction*, §2.2.
-/

public section

open Bundle CategoryTheory Set VectorBundleCore
open scoped Manifold ContDiff

namespace TauCeti.FiniteRankBundleCore

variable {𝕜 B : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]
  {EB HB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  [TopologicalSpace HB] [ChartedSpace HB B] {I : ModelWithCorners 𝕜 EB HB} {n : ℕ∞ω}

/-- For any point-indexed finite-rank core `E`, the fibre coordinate in the chart at `p₀.proj` is
`C^n` at `p₀`. -/
theorem contMDiffAt_localTriv_snd (E : FiniteRankBundleCore 𝕜 B) (p₀ : E.core.TotalSpace) :
    ContMDiffAt (I.prod 𝓘(𝕜, Fin E.rank → 𝕜)) 𝓘(𝕜, Fin E.rank → 𝕜) n
      (fun p : E.core.TotalSpace ↦ (E.core.localTriv p₀.proj p).2) p₀ := by
  simpa only [E.trivializationAt_core] using
    p₀.contMDiffAt_trivializationAt_snd (IB := I) (n := n)

/-- A map from `E.core.TotalSpace` into the total space of a fibre bundle `V` covering the
identity of `B` whose fibre coordinate in every preferred trivialization is a fixed continuous
linear map `L` of the chart coordinate in `E` is `C^n`, without any smoothness hypothesis on the
base or transition functions. -/
theorem contMDiff_of_localTriv_snd {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {V : B → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)]
    [FiberBundle F V] (E : FiniteRankBundleCore 𝕜 B) (f : E.core.TotalSpace → TotalSpace F V)
    (hf_proj : ∀ p, (f p).proj = p.proj) (L : (Fin E.rank → 𝕜) →L[𝕜] F)
    (hL : ∀ (b : B) (p : E.core.TotalSpace),
      (trivializationAt F V b (f p)).2 = L ((E.core.localTriv b p).2)) :
    ContMDiff (I.prod 𝓘(𝕜, Fin E.rank → 𝕜)) (I.prod 𝓘(𝕜, F)) n f := by
  intro p₀
  rw [Bundle.contMDiffAt_totalSpace_iff, hf_proj p₀]
  refine ⟨((contMDiff_proj E.core.Fiber).congr hf_proj).contMDiffAt, ?_⟩
  exact (L.contDiff.comp_contMDiffAt (E.contMDiffAt_localTriv_snd p₀)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun p ↦ hL p₀.proj p)

/-- A map from the total space of a fibre bundle `V` into `E.core.TotalSpace` covering the
identity of `B` whose chart coordinate in `E` at every base point is a fixed continuous linear
map `L` of the fibre coordinate in the preferred trivialization of `V` is `C^n`, without any
smoothness hypothesis on the base or transition functions. -/
theorem contMDiff_of_trivializationAt_snd {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {V : B → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)]
    [FiberBundle F V] (E : FiniteRankBundleCore 𝕜 B) (f : TotalSpace F V → E.core.TotalSpace)
    (hf_proj : ∀ p, (f p).proj = p.proj) (L : F →L[𝕜] (Fin E.rank → 𝕜))
    (hL : ∀ (b : B) (p : TotalSpace F V),
      (E.core.localTriv b (f p)).2 = L ((trivializationAt F V b p).2)) :
    ContMDiff (I.prod 𝓘(𝕜, F)) (I.prod 𝓘(𝕜, Fin E.rank → 𝕜)) n f := by
  intro p₀
  rw [Bundle.contMDiffAt_totalSpace_iff, hf_proj p₀, E.trivializationAt_core]
  refine ⟨((contMDiff_proj V).congr hf_proj).contMDiffAt, ?_⟩
  exact (L.contDiff.comp_contMDiffAt
    (p₀.contMDiffAt_trivializationAt_snd (IB := I) (n := n))).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun p ↦ hL p₀.proj p)

/-- A morphism `a : E ⟶ E'` of point-indexed finite-rank cores whose fibre maps intertwine the
point-to-chart transitions with a fixed continuous linear map `L` glues to a `C^n` map of total
spaces, without any smoothness assumption on the base or on the cores. -/
theorem contMDiff_totalSpaceMap_of_coordChange {E E' : FiniteRankBundleCore 𝕜 B} (a : E ⟶ E')
    (L : (Fin E.rank → 𝕜) →L[𝕜] (Fin E'.rank → 𝕜))
    (hL : ∀ x b v, E'.core.coordChange x b x (a.fiberMap x v) = L (E.core.coordChange x b x v)) :
    ContMDiff (I.prod 𝓘(𝕜, Fin E.rank → 𝕜)) (I.prod 𝓘(𝕜, Fin E'.rank → 𝕜)) n
      a.totalSpaceMap := by
  refine E.contMDiff_of_localTriv_snd a.totalSpaceMap a.totalSpaceMap_proj L fun b ⟨x, v⟩ ↦ ?_
  rw [E'.trivializationAt_core]
  simp only [CoordinateHom.totalSpaceMap_mk, localTriv_apply, E.indexAt_eq, E'.indexAt_eq]
  exact hL x b v

/-- If `E.core.baseSet i ⊆ E'.core.baseSet i`, `E'` is a `C^n` core, and `a : E ⟶ E'` intertwines
the transitions from `i` to each point `x` with a fixed continuous linear map `L`, then the
`(i, j)` chart operator of `a` is `C^n` on `E.core.baseSet i ∩ E'.core.baseSet j`. -/
theorem contMDiffOn_inChartCoordinates_of_coordChange_comp {E E' : FiniteRankBundleCore 𝕜 B}
    [E'.core.IsContMDiff I n] (a : E ⟶ E') {i j : B}
    (hbase : E.core.baseSet i ⊆ E'.core.baseSet i)
    (L : (Fin E.rank → 𝕜) →L[𝕜] (Fin E'.rank → 𝕜))
    (hL : ∀ x ∈ E.core.baseSet i ∩ E'.core.baseSet j, ∀ v,
      a.fiberMap x (E.core.coordChange i x x v) = E'.core.coordChange i x x (L v)) :
    ContMDiffOn I 𝓘(𝕜, (Fin E.rank → 𝕜) →L[𝕜] (Fin E'.rank → 𝕜)) n
      (fun x ↦ E.core.inChartCoordinates E'.core i j x (a.fiberMap x))
      (E.core.baseSet i ∩ E'.core.baseSet j) := by
  -- On the overlap, the `(i, j)` chart operator equals `(E'.core.coordChange i j ·).comp L`.
  have hE' : ContMDiffOn I 𝓘(𝕜, (Fin E'.rank → 𝕜) →L[𝕜] (Fin E'.rank → 𝕜)) n
      (E'.core.coordChange i j) (E.core.baseSet i ∩ E'.core.baseSet j) :=
    (E'.core.contMDiffOn_coordChange I i j).mono fun _ h ↦ ⟨hbase h.1, h.2⟩
  refine (hE'.clm_comp (contMDiffOn_const (c := L))).congr fun x hx ↦ ?_
  ext v : 1
  rw [inChartCoordinates_core_apply, hL x hx v, ContinuousLinearMap.comp_apply]
  exact E'.core.coordChange_comp i x j x ⟨⟨hbase hx.1, E'.mem_baseSet_self x⟩, hx.2⟩ (L v)

/-- If `E'.core.baseSet j ⊆ E.core.baseSet j`, `E` is a `C^n` core, and `a : E ⟶ E'` intertwines
the transitions from each point `x` to `j` with a fixed continuous linear map `L`, then the
`(i, j)` chart operator of `a` is `C^n` on `E.core.baseSet i ∩ E'.core.baseSet j`. -/
theorem contMDiffOn_inChartCoordinates_of_comp_coordChange {E E' : FiniteRankBundleCore 𝕜 B}
    [E.core.IsContMDiff I n] (a : E ⟶ E') {i j : B}
    (hbase : E'.core.baseSet j ⊆ E.core.baseSet j)
    (L : (Fin E.rank → 𝕜) →L[𝕜] (Fin E'.rank → 𝕜))
    (hL : ∀ x ∈ E.core.baseSet i ∩ E'.core.baseSet j, ∀ v,
      E'.core.coordChange x j x (a.fiberMap x v) = L (E.core.coordChange x j x v)) :
    ContMDiffOn I 𝓘(𝕜, (Fin E.rank → 𝕜) →L[𝕜] (Fin E'.rank → 𝕜)) n
      (fun x ↦ E.core.inChartCoordinates E'.core i j x (a.fiberMap x))
      (E.core.baseSet i ∩ E'.core.baseSet j) := by
  -- On the overlap, the `(i, j)` chart operator equals `L.comp (E.core.coordChange i j ·)`.
  have hE : ContMDiffOn I 𝓘(𝕜, (Fin E.rank → 𝕜) →L[𝕜] (Fin E.rank → 𝕜)) n
      (E.core.coordChange i j) (E.core.baseSet i ∩ E'.core.baseSet j) :=
    (E.core.contMDiffOn_coordChange I i j).mono fun _ h ↦ ⟨h.1, hbase h.2⟩
  refine ((contMDiffOn_const (c := L)).clm_comp hE).congr fun x hx ↦ ?_
  ext v : 1
  rw [inChartCoordinates_core_apply, hL x hx, ContinuousLinearMap.comp_apply,
    E.core.coordChange_comp i x j x ⟨⟨hx.1, E.mem_baseSet_self x⟩, hbase hx.2⟩]

/-- The trivial finite-rank core is smooth at every regularity. -/
instance isContMDiff_trivial (r : ℕ) : (trivial 𝕜 B r).core.IsContMDiff I n where
  contMDiffOn_coordChange _ _ := contMDiffOn_const

/-- A constant operator intertwining the transitions of cores on chart overlaps defines a `C^n`
map of total spaces without smoothness hypotheses on the cores. -/
theorem contMDiff_totalSpaceMap_constHom {A D : FiniteRankBundleCore 𝕜 B}
    (hbase : ∀ i, A.core.baseSet i ⊆ D.core.baseSet i)
    (T : (Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜))
    (hT : ∀ i j x, x ∈ A.core.baseSet i → x ∈ A.core.baseSet j →
      T.comp (A.core.coordChange i j x) = (D.core.coordChange i j x).comp T) :
    ContMDiff (I.prod 𝓘(𝕜, Fin A.rank → 𝕜)) (I.prod 𝓘(𝕜, Fin D.rank → 𝕜)) n
      (constHom hbase T hT).totalSpaceMap := by
  intro p₀
  rw [Bundle.contMDiffAt_totalSpace_iff, (constHom hbase T hT).totalSpaceMap_proj p₀,
    D.trivializationAt_core]
  refine ⟨((contMDiff_proj A.core.Fiber).congr
    (constHom hbase T hT).totalSpaceMap_proj).contMDiffAt, ?_⟩
  refine (T.contDiff.comp_contMDiffAt (A.contMDiffAt_localTriv_snd p₀)).congr_of_eventuallyEq ?_
  filter_upwards [A.localTriv_source_mem_nhds p₀] with q hq
  rcases q with ⟨x, v⟩
  simp only [Function.comp_apply, CoordinateHom.totalSpaceMap_mk, fiberMap_constHom,
    D.core.localTriv_apply, A.core.localTriv_apply, D.indexAt_eq, A.indexAt_eq]
  exact congrFun (congrArg DFunLike.coe
    (hT x p₀.proj x (A.mem_baseSet_self x)
      ((A.core.mem_localTriv_source p₀.proj ⟨x, v⟩).1 hq)).symm) v

/-- An isomorphism of finite-rank cores whose forward and inverse maps are `C^n` on total spaces
induces a `C^n` diffeomorphism of total spaces, without completeness or smoothness of
transitions. -/
def isoToDiffeomorph {A D : FiniteRankBundleCore 𝕜 B} (e : A ≅ D)
    (he_hom : ContMDiff (I.prod 𝓘(𝕜, Fin A.rank → 𝕜)) (I.prod 𝓘(𝕜, Fin D.rank → 𝕜)) n
      e.hom.totalSpaceMap)
    (he_inv : ContMDiff (I.prod 𝓘(𝕜, Fin D.rank → 𝕜)) (I.prod 𝓘(𝕜, Fin A.rank → 𝕜)) n
      e.inv.totalSpaceMap) :
    A.core.TotalSpace ≃ₘ^n⟮I.prod 𝓘(𝕜, Fin A.rank → 𝕜),
      I.prod 𝓘(𝕜, Fin D.rank → 𝕜)⟯ D.core.TotalSpace :=
  CoordinateHom.toDiffeomorphOfInv e.hom e.inv e.hom_inv_id e.inv_hom_id he_hom he_inv

@[simp] theorem coe_isoToDiffeomorph {A D : FiniteRankBundleCore 𝕜 B} (e : A ≅ D)
    (he_hom : ContMDiff (I.prod 𝓘(𝕜, Fin A.rank → 𝕜)) (I.prod 𝓘(𝕜, Fin D.rank → 𝕜)) n
      e.hom.totalSpaceMap)
    (he_inv : ContMDiff (I.prod 𝓘(𝕜, Fin D.rank → 𝕜)) (I.prod 𝓘(𝕜, Fin A.rank → 𝕜)) n
      e.inv.totalSpaceMap) :
    ⇑(isoToDiffeomorph e he_hom he_inv) = e.hom.totalSpaceMap :=
  CoordinateHom.coe_toDiffeomorphOfInv _ _ _ _ _ _

@[simp] theorem coe_isoToDiffeomorph_symm {A D : FiniteRankBundleCore 𝕜 B} (e : A ≅ D)
    (he_hom : ContMDiff (I.prod 𝓘(𝕜, Fin A.rank → 𝕜)) (I.prod 𝓘(𝕜, Fin D.rank → 𝕜)) n
      e.hom.totalSpaceMap)
    (he_inv : ContMDiff (I.prod 𝓘(𝕜, Fin D.rank → 𝕜)) (I.prod 𝓘(𝕜, Fin A.rank → 𝕜)) n
      e.inv.totalSpaceMap) :
    ⇑(isoToDiffeomorph e he_hom he_inv).symm = e.inv.totalSpaceMap :=
  CoordinateHom.coe_toDiffeomorphOfInv_symm _ _ _ _ _ _

/-- A fixed continuous linear equivalence intertwining transition functions on chart overlaps
induces a `C^n` bundle diffeomorphism over the identity, without smoothness hypotheses on the
cores. -/
noncomputable def constIsoDiffeomorph {A D : FiniteRankBundleCore 𝕜 B}
    (hbase : ∀ i, A.core.baseSet i = D.core.baseSet i)
    (e : (Fin A.rank → 𝕜) ≃L[𝕜] (Fin D.rank → 𝕜))
    (he : ∀ i j x, x ∈ A.core.baseSet i → x ∈ A.core.baseSet j →
      (e : (Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜)).comp (A.core.coordChange i j x) =
        (D.core.coordChange i j x).comp (e : (Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜))) :
    A.core.TotalSpace ≃ₘ^n⟮I.prod 𝓘(𝕜, Fin A.rank → 𝕜),
      I.prod 𝓘(𝕜, Fin D.rank → 𝕜)⟯ D.core.TotalSpace :=
  isoToDiffeomorph (constIso hbase e he)
    ((contMDiff_totalSpaceMap_constHom (I := I) (n := n) (fun i ↦ (hbase i).le)
      e.toContinuousLinearMap he).congr fun ⟨x, v⟩ ↦ by
        rw [CoordinateHom.totalSpaceMap_mk, CoordinateHom.totalSpaceMap_mk,
          fiberMap_constHom, fiberMap_constIso_hom])
    ((contMDiff_totalSpaceMap_constHom (I := I) (n := n) (fun i ↦ (hbase i).ge)
      e.symm.toContinuousLinearMap (coordChange_intertwines_symm hbase e he)).congr fun ⟨x, v⟩ ↦ by
        rw [CoordinateHom.totalSpaceMap_mk, CoordinateHom.totalSpaceMap_mk,
          fiberMap_constHom, fiberMap_constIso_inv])

/-- The smooth comparison is the original constant core isomorphism on total spaces. -/
@[simp]
theorem coe_constIsoDiffeomorph {A D : FiniteRankBundleCore 𝕜 B}
    (hbase : ∀ i, A.core.baseSet i = D.core.baseSet i)
    (e : (Fin A.rank → 𝕜) ≃L[𝕜] (Fin D.rank → 𝕜))
    (he : ∀ i j x, x ∈ A.core.baseSet i → x ∈ A.core.baseSet j →
      (e : (Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜)).comp (A.core.coordChange i j x) =
        (D.core.coordChange i j x).comp (e : (Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜))) :
    ⇑(constIsoDiffeomorph (I := I) (n := n) hbase e he) =
      (constIso hbase e he).hom.totalSpaceMap :=
  coe_isoToDiffeomorph _ _ _

/-- The inverse smooth comparison is the inverse of the original core isomorphism. -/
@[simp]
theorem coe_constIsoDiffeomorph_symm {A D : FiniteRankBundleCore 𝕜 B}
    (hbase : ∀ i, A.core.baseSet i = D.core.baseSet i)
    (e : (Fin A.rank → 𝕜) ≃L[𝕜] (Fin D.rank → 𝕜))
    (he : ∀ i j x, x ∈ A.core.baseSet i → x ∈ A.core.baseSet j →
      (e : (Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜)).comp (A.core.coordChange i j x) =
        (D.core.coordChange i j x).comp (e : (Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜))) :
    ⇑(constIsoDiffeomorph (I := I) (n := n) hbase e he).symm =
      (constIso hbase e he).inv.totalSpaceMap :=
  coe_isoToDiffeomorph_symm _ _ _

section IsContMDiff

variable {A D : FiniteRankBundleCore 𝕜 B}
  [A.core.IsContMDiff I n] [D.core.IsContMDiff I n]
theorem contMDiffOn_inChartCoordinates_of_contMDiff_totalSpaceMap (f : A ⟶ D)
    (hf : ContMDiff (I.prod 𝓘(𝕜, Fin A.rank → 𝕜)) (I.prod 𝓘(𝕜, Fin D.rank → 𝕜)) n
      f.totalSpaceMap) (i j : B) :
    ContMDiffOn I 𝓘(𝕜, (Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜)) n
      (fun x ↦ A.core.inChartCoordinates D.core i j x (f.fiberMap x))
      (A.core.baseSet i ∩ D.core.baseSet j) := by
  have : MemTrivializationAtlas (A.core.localTriv i) := ⟨⟨i, rfl⟩⟩
  have : MemTrivializationAtlas (D.core.localTriv j) := ⟨⟨j, rfl⟩⟩
  set U := A.core.baseSet i ∩ D.core.baseSet j
  have hU : IsOpen U := (A.core.isOpen_baseSet i).inter (D.core.isOpen_baseSet j)
  -- Each column is obtained by feeding a constant standard basis section in chart `i` into
  -- `f.totalSpaceMap` and reading the image in chart `j`.
  have hcol (k : Fin A.rank) : ContMDiffOn I 𝓘(𝕜, Fin D.rank → 𝕜) n
      (fun x ↦ A.core.inChartCoordinates D.core i j x (f.fiberMap x) (Pi.single k 1)) U := by
    have hs := (A.core.localTriv i).contMDiffOn_section_symm (IB := I) (n := n) hU
      inter_subset_left (contMDiffOn_const (c := Pi.single k (1 : 𝕜)))
    have hfs : ContMDiffOn I (I.prod 𝓘(𝕜, Fin D.rank → 𝕜)) n
        (fun x ↦ TotalSpace.mk' (Fin D.rank → 𝕜) (E := D.core.Fiber) x
          (f.fiberMap x ((A.core.localTriv i).symm x (Pi.single k 1)))) U :=
      (hf.comp_contMDiffOn hs).congr fun x _ ↦ (f.totalSpaceMap_mk x _).symm
    refine (((D.core.localTriv j).contMDiffOn_section_iff hU inter_subset_right).mp hfs).congr
      fun x hx ↦ ?_
    simp only [VectorBundleCore.inChartCoordinates_apply, D.core.localTriv_apply,
      A.core.localTriv_symm_apply i hx.1]
  let Φ : (Fin A.rank → Fin D.rank → 𝕜) → (Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜) :=
    fun g ↦ ∑ k : Fin A.rank,
      ContinuousLinearMap.smulRightL 𝕜 𝕜 𝕜 (Fin A.rank → 𝕜) (Fin D.rank → 𝕜)
        (ContinuousLinearMap.proj k) (g k)
  have hΦ : ContDiff 𝕜 n Φ :=
    ContDiff.sum fun k _ ↦
      (ContinuousLinearMap.smulRightL 𝕜 𝕜 𝕜 (Fin A.rank → 𝕜) (Fin D.rank → 𝕜)
        (ContinuousLinearMap.proj k)).contDiff.comp (contDiff_apply 𝕜 _ k)
  refine (hΦ.contMDiff.comp_contMDiffOn (contMDiffOn_pi_module_iff.mpr hcol)).congr fun x _ ↦ ?_
  ext v m
  have hv : (∑ k : Fin A.rank, v k • Pi.single k (1 : 𝕜)) = v := by
    ext l; simp [Finset.sum_apply, Pi.single_apply]
  symm
  calc
    (Φ fun k ↦ A.core.inChartCoordinates D.core i j x (f.fiberMap x) (Pi.single k 1)) v m
      = (∑ k : Fin A.rank,
          A.core.inChartCoordinates D.core i j x (f.fiberMap x) (v k • Pi.single k 1)) m := by
        simp only [Φ, sum_apply, ContinuousLinearMap.smulRightL_apply_apply,
          ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, _root_.map_smul]
    _ = A.core.inChartCoordinates D.core i j x (f.fiberMap x) v m := by rw [← map_sum, hv]

/-- For a morphism between `C^n` finite-rank cores, the glued map of total spaces is `C^n`
if and only if every chart operator is `C^n` on its domain, without completeness of `𝕜`. -/
theorem contMDiff_totalSpaceMap_iff_inChartCoordinates (f : A ⟶ D) :
    ContMDiff (I.prod 𝓘(𝕜, Fin A.rank → 𝕜)) (I.prod 𝓘(𝕜, Fin D.rank → 𝕜)) n f.totalSpaceMap ↔
      ∀ i j, ContMDiffOn I 𝓘(𝕜, (Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜)) n
        (fun x ↦ A.core.inChartCoordinates D.core i j x (f.fiberMap x))
        (A.core.baseSet i ∩ D.core.baseSet j) :=
  ⟨contMDiffOn_inChartCoordinates_of_contMDiff_totalSpaceMap f, f.contMDiff_totalSpaceMap⟩

end IsContMDiff

/-- The forward total-space map of `isoTrivialOfCoordChangeEqId` is `C^n` at every regularity. -/
theorem contMDiff_totalSpaceMap_isoTrivialOfCoordChangeEqId_hom
    (A : FiniteRankBundleCore 𝕜 B) {r : ℕ}
    (e : (Fin A.rank → 𝕜) ≃L[𝕜] (Fin r → 𝕜))
    (h : ∀ i j x, x ∈ A.core.baseSet i → x ∈ A.core.baseSet j →
      A.core.coordChange i j x = ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜)) :
    ContMDiff (I.prod 𝓘(𝕜, Fin A.rank → 𝕜)) (I.prod 𝓘(𝕜, Fin (trivial 𝕜 B r).rank → 𝕜)) n
      (isoTrivialOfCoordChangeEqId A e h).hom.totalSpaceMap := by
  have : A.core.IsContMDiff I n :=
    ⟨fun i j ↦ contMDiffOn_const.congr fun x hx ↦ h i j x hx.1 hx.2⟩
  let c : (Fin A.rank → 𝕜) →L[𝕜] Fin (trivial 𝕜 B r).rank → 𝕜 := e.toContinuousLinearMap
  exact CoordinateHom.contMDiff_totalSpaceMap _ fun i j ↦
    (contMDiffOn_const (c := c)).congr fun x hx ↦
      (CoordinateHom.operator_eq (isoTrivialOfCoordChangeEqId A e h).hom i j ⟨x, hx⟩).symm.trans
        (operator_isoTrivialOfCoordChangeEqId_hom A e h i j ⟨x, hx⟩)

/-- The inverse total-space map of `isoTrivialOfCoordChangeEqId` is `C^n` at every regularity. -/
theorem contMDiff_totalSpaceMap_isoTrivialOfCoordChangeEqId_inv
    (A : FiniteRankBundleCore 𝕜 B) {r : ℕ}
    (e : (Fin A.rank → 𝕜) ≃L[𝕜] (Fin r → 𝕜))
    (h : ∀ i j x, x ∈ A.core.baseSet i → x ∈ A.core.baseSet j →
      A.core.coordChange i j x = ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜)) :
    ContMDiff (I.prod 𝓘(𝕜, Fin (trivial 𝕜 B r).rank → 𝕜)) (I.prod 𝓘(𝕜, Fin A.rank → 𝕜)) n
      (isoTrivialOfCoordChangeEqId A e h).inv.totalSpaceMap := by
  have : A.core.IsContMDiff I n :=
    ⟨fun i j ↦ contMDiffOn_const.congr fun x hx ↦ h i j x hx.1 hx.2⟩
  let c : (Fin (trivial 𝕜 B r).rank → 𝕜) →L[𝕜] Fin A.rank → 𝕜 := e.symm.toContinuousLinearMap
  exact CoordinateHom.contMDiff_totalSpaceMap _ fun i j ↦
    (contMDiffOn_const (c := c)).congr fun x hx ↦
      (CoordinateHom.operator_eq (isoTrivialOfCoordChangeEqId A e h).inv i j ⟨x, hx⟩).symm.trans
        (operator_isoTrivialOfCoordChangeEqId_inv A e h i j ⟨x, hx⟩)

end TauCeti.FiniteRankBundleCore
