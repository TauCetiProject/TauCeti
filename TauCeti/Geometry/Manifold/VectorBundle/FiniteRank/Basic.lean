/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CoordinateHom
public import TauCeti.Geometry.Manifold.VectorBundle.Trivialization

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

* `FiniteRankBundleCore.contMDiff_of_localTriv_snd` and
  `FiniteRankBundleCore.contMDiff_totalSpaceMap_of_coordChange` establish `C^n` regularity on total
  spaces without `C^n` assumptions on the cores;
* `FiniteRankBundleCore.contMDiffOn_inChartCoordinates_of_coordChange_comp` and
  `FiniteRankBundleCore.contMDiffOn_inChartCoordinates_of_comp_coordChange` establish `C^n`
  regularity of chart operators when the target or source core is `C^n`;
* `FiniteRankBundleCore.isContMDiff_trivial`,
  `FiniteRankBundleCore.contMDiff_totalSpaceMap_constHom`, and
  `FiniteRankBundleCore.constIsoDiffeomorph` show that trivial cores are `C^n` and that constant
  intertwining maps and equivalences (`constHom`, `constIso`) between `C^n` cores induce `C^n` maps
  and diffeomorphisms of total spaces without completeness assumptions on the scalar field.

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

variable {A D : FiniteRankBundleCore 𝕜 B}
  [A.core.IsContMDiff I n] [D.core.IsContMDiff I n]

/-- A constant operator intertwining the transitions of smooth cores defines a smooth map
of total spaces. The source chart domains need only lie in the corresponding target domains. -/
theorem contMDiff_totalSpaceMap_constHom
    (hbase : ∀ i, A.core.baseSet i ⊆ D.core.baseSet i)
    (T : (Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜))
    (hT : ∀ i j x, x ∈ A.core.baseSet i → x ∈ A.core.baseSet j →
      T.comp (A.core.coordChange i j x) = (D.core.coordChange i j x).comp T) :
    ContMDiff (I.prod 𝓘(𝕜, Fin A.rank → 𝕜)) (I.prod 𝓘(𝕜, Fin D.rank → 𝕜)) n
      (constHom hbase T hT).totalSpaceMap := by
  apply CoordinateHom.contMDiff_totalSpaceMap
  intro i j
  refine (((D.core.contMDiffOn_coordChange I i j).mono
    (fun x (hx : x ∈ A.core.baseSet i ∩ D.core.baseSet j) ↦
      ⟨hbase i hx.1, hx.2⟩)).clm_comp (contMDiffOn_const (c := T))).congr ?_
  intro x hx
  rw [← CoordinateHom.operator_eq (constHom hbase T hT) i j ⟨x, hx⟩]
  rw [operator_constHom]
  rfl

/-- A fixed continuous linear equivalence intertwining smooth transition functions induces a
smooth bundle equivalence over the identity, using the existing core total spaces. -/
noncomputable def constIsoDiffeomorph
    (hbase : ∀ i, A.core.baseSet i = D.core.baseSet i)
    (e : (Fin A.rank → 𝕜) ≃L[𝕜] (Fin D.rank → 𝕜))
    (he : ∀ i j x, x ∈ A.core.baseSet i → x ∈ A.core.baseSet j →
      (e : (Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜)).comp (A.core.coordChange i j x) =
        (D.core.coordChange i j x).comp (e : (Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜))) :
    A.core.TotalSpace ≃ₘ^n⟮I.prod 𝓘(𝕜, Fin A.rank → 𝕜),
      I.prod 𝓘(𝕜, Fin D.rank → 𝕜)⟯ D.core.TotalSpace where
  toFun := (constIso hbase e he).hom.totalSpaceMap
  invFun := (constIso hbase e he).inv.totalSpaceMap
  left_inv := fun ⟨x, v⟩ ↦ by
    simp only [CoordinateHom.totalSpaceMap_def, fiberMap_constIso_hom, fiberMap_constIso_inv]
    exact congrArg (fun w : Fin A.rank → 𝕜 ↦ (⟨x, w⟩ : A.core.TotalSpace))
      (e.symm_apply_apply v)
  right_inv := fun ⟨x, v⟩ ↦ by
    simp only [CoordinateHom.totalSpaceMap_def, fiberMap_constIso_hom, fiberMap_constIso_inv]
    exact congrArg (fun w : Fin D.rank → 𝕜 ↦ (⟨x, w⟩ : D.core.TotalSpace))
      (e.apply_symm_apply v)
  contMDiff_toFun :=
    (contMDiff_totalSpaceMap_constHom (I := I) (n := n) (fun i ↦ (hbase i).le)
      e.toContinuousLinearMap he).congr fun p ↦ by
        simp only [CoordinateHom.totalSpaceMap_def, fiberMap_constHom, fiberMap_constIso_hom]
        rfl
  contMDiff_invFun :=
    (contMDiff_totalSpaceMap_constHom (I := I) (n := n) (fun i ↦ (hbase i).ge)
      e.symm.toContinuousLinearMap (coordChange_intertwines_symm hbase e he)).congr fun p ↦ by
        simp only [CoordinateHom.totalSpaceMap_def, fiberMap_constHom, fiberMap_constIso_inv]
        rfl

/-- The smooth comparison is the original constant core isomorphism on total spaces. -/
@[simp]
theorem coe_constIsoDiffeomorph
    (hbase : ∀ i, A.core.baseSet i = D.core.baseSet i)
    (e : (Fin A.rank → 𝕜) ≃L[𝕜] (Fin D.rank → 𝕜))
    (he : ∀ i j x, x ∈ A.core.baseSet i → x ∈ A.core.baseSet j →
      (e : (Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜)).comp (A.core.coordChange i j x) =
        (D.core.coordChange i j x).comp (e : (Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜))) :
    ⇑(constIsoDiffeomorph (I := I) (n := n) hbase e he) =
      (constIso hbase e he).hom.totalSpaceMap := (rfl)

/-- The inverse smooth comparison is the inverse of the original core isomorphism. -/
@[simp]
theorem coe_constIsoDiffeomorph_symm
    (hbase : ∀ i, A.core.baseSet i = D.core.baseSet i)
    (e : (Fin A.rank → 𝕜) ≃L[𝕜] (Fin D.rank → 𝕜))
    (he : ∀ i j x, x ∈ A.core.baseSet i → x ∈ A.core.baseSet j →
      (e : (Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜)).comp (A.core.coordChange i j x) =
        (D.core.coordChange i j x).comp (e : (Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜))) :
    ⇑(constIsoDiffeomorph (I := I) (n := n) hbase e he).symm =
      (constIso hbase e he).inv.totalSpaceMap := (rfl)

end TauCeti.FiniteRankBundleCore
