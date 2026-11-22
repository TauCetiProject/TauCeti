/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FrameBundle
public import TauCeti.Geometry.Manifold.FiberBundle.MapFiber
public import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import Mathlib.Geometry.Manifold.VectorBundle.Basic

/-!
# The smooth frame bundle of a smooth vector bundle

Let `E → B` be a `C^k` vector bundle over a complete nontrivially normed field `𝕜`, with model fibre
`F` isomorphic to `𝕜ⁿ` by `σ : F ≃ 𝕜ⁿ`. Its frame bundle `TauCeti.FrameBundle 𝕜 n F E` is an open
subset of the total space of the `C^k` vector bundle `Hom(B × 𝕜ⁿ, E)`, so it carries the manifold
structure of an open subset of that total space, modelled on `IB.prod 𝓘(𝕜, 𝕜ⁿ →L[𝕜] F)`. No other
smooth structure is put on frames.

The general linear group `GL n 𝕜 = Matrix.GeneralLinearGroup (Fin n) 𝕜` carries the Lie group
structure of the units of the matrix algebra with the `L∞` operator norm. The trivializations of
the frame bundle induced by those of `E` (`Bundle.Trivialization.frameBundle`) are `C^k`
diffeomorphisms from their sources onto open subsets of `B × GL n 𝕜`
(`Bundle.Trivialization.contMDiffOn_frameBundle`,
`Bundle.Trivialization.contMDiffOn_frameBundle_symm`): read in the trivialization of the Hom bundle
induced by the same trivialization of `E`, a frame and its matrix differ by a fixed continuous
linear isomorphism. So the atlas of these trivializations is `C^k`
(`TauCeti.FrameBundle.isContMDiff_atlas`), and Tau Ceti's presentation of bundles by their total
space makes the fibres of the frame bundle a `C^k` fibre bundle
(`TauCeti.FrameBundle.contMDiffFiberBundle`), principal for `GL n 𝕜`
(`TauCeti.FrameBundle.principalBundle`). Its charted total space is `C^k` diffeomorphic to the frame
bundle itself by `⟨b, v⟩ ↦ v`, over `B` and equivariantly
(`TauCeti.MapFiber.Atlas.totalSpaceDiffeomorph`). The right action of `GL n 𝕜` on frames is `C^k`
(`TauCeti.FrameBundle.contMDiff_smul`).

## Main results

* `Bundle.Trivialization.contMDiffOn_frameBundle`,
  `Bundle.Trivialization.contMDiffOn_frameBundle_symm`: the trivializations of the frame bundle are
  `C^k` with `C^k` inverses.
* `TauCeti.FrameBundle.isContMDiff_atlas`: the atlas of the frame bundle is `C^k`.
* `TauCeti.FrameBundle.contMDiffFiberBundle`: the frame bundle is a `C^k` fibre bundle with fibre
  `GL n 𝕜`.
* `TauCeti.FrameBundle.contMDiff_smul`: the right action of `GL n 𝕜` on frames is `C^k`.

## References

* S. Kobayashi, K. Nomizu, *Foundations of Differential Geometry I*, Interscience, 1963,
  Ch. I, §5, Example 5.2 (the bundle of linear frames).
* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer,
  1993, §10.11 (the frame bundle of a vector bundle).
-/

public section

noncomputable section

open Bundle Set Function Manifold MulOpposite TopologicalSpace TauCeti TauCeti.FrameBundle
open scoped ContDiff Manifold Matrix.Norms.Operator

attribute [local instance] NormedAddCommGroup.toSeminormedAddCommGroup

attribute [local instance] Matrix.linftyOpTopologicalSpace

attribute [local instance] memTrivializationAtlas_trivialization

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] {n : ℕ} {k : WithTop ℕ∞}
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {E : B → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜 (E x)]
  [TopologicalSpace (TotalSpace F E)] [∀ x, TopologicalSpace (E x)] [FiberBundle F E]
  [VectorBundle 𝕜 F E] [∀ x, IsTopologicalAddGroup (E x)] [∀ x, ContinuousSMul 𝕜 (E x)]
  [ContMDiffVectorBundle k F E IB]

namespace Bundle.Trivialization

variable (e : Trivialization F (π F E)) [MemTrivializationAtlas e] (σ : F ≃L[𝕜] (Fin n → 𝕜))

/-- The matrix of a frame in the local frame of a trivialization `e` of `E` is `C^k` on the
frames over the base set of `e`. -/
theorem contMDiffOn_matrixIn :
    ContMDiffOn (IB.prod 𝓘(𝕜, (Fin n → 𝕜) →L[𝕜] F)) 𝓘(𝕜, Matrix (Fin n) (Fin n) 𝕜) k
      (e.matrixIn σ : FrameBundle 𝕜 n F E → _) (FrameBundle.proj ⁻¹' e.baseSet) :=
  ((σ.toMatrixCLE.contDiff.contMDiff.comp contMDiff_snd).comp_contMDiffOn
    ((Trivialization.contMDiffOn _).comp contMDiff_subtypeVal.contMDiffOn
      e.mapsTo_coe_source_continuousLinearMap)).congr fun v _ ↦ e.matrixIn_eq σ v

/-- The trivializations of the frame bundle induced by those of `E` are `C^k` on their sources. -/
theorem contMDiffOn_frameBundle :
    ContMDiffOn (IB.prod 𝓘(𝕜, (Fin n → 𝕜) →L[𝕜] F)) (IB.prod 𝓘(𝕜, Matrix (Fin n) (Fin n) 𝕜)) k
      (e.frameBundle σ : FrameBundle 𝕜 n F E → B × GL (Fin n) 𝕜) (e.frameBundle σ).source := by
  rw [source_frameBundle]
  refine ContMDiffOn.congr ?_ fun v _ ↦ frameBundle_apply e σ v
  refine ((Bundle.contMDiff_proj (IB := IB) (n := k) (F := (Fin n → 𝕜) →L[𝕜] F) _).comp
    contMDiff_subtypeVal).contMDiffOn.prodMk ?_
  -- Smoothness into `GL n 𝕜`, an open subset of the matrices, is smoothness of the matrix.
  have hval : ContMDiffOn (IB.prod 𝓘(𝕜, (Fin n → 𝕜) →L[𝕜] F)) 𝓘(𝕜, Matrix (Fin n) (Fin n) 𝕜) k
      (fun v : FrameBundle 𝕜 n F E ↦ (e.unitIn σ v : Matrix (Fin n) (Fin n) 𝕜))
      (proj ⁻¹' e.baseSet) :=
    (e.contMDiffOn_matrixIn σ).congr fun v hv ↦ e.coe_unitIn σ hv
  refine ((contMDiffOn_isOpenEmbedding_symm (I := 𝓘(𝕜, Matrix (Fin n) (Fin n) 𝕜)) (n := k)
    Units.isOpenEmbedding_val).comp hval fun v _ ↦ mem_range_self _).congr fun v _ ↦ ?_
  exact (Units.isOpenEmbedding_val.toOpenPartialHomeomorph_left_inv _).symm

/-- The inverses of the trivializations of the frame bundle induced by those of `E` are `C^k` on
their targets. -/
theorem contMDiffOn_frameBundle_symm :
    ContMDiffOn (IB.prod 𝓘(𝕜, Matrix (Fin n) (Fin n) 𝕜)) (IB.prod 𝓘(𝕜, (Fin n → 𝕜) →L[𝕜] F)) k
      (e.frameBundle σ : Trivialization (GL (Fin n) 𝕜)
        (proj : FrameBundle 𝕜 n F E → B)).toOpenPartialHomeomorph.symm
      (e.frameBundle σ).target := by
  let eH := (Trivial.trivialization B (Fin n → 𝕜)).continuousLinearMap (RingHom.id 𝕜) e
  have hval := (eH.contMDiffOn_symm (IB := IB) (n := k)).comp (contMDiff_fst.prodMk
    ((σ.toMatrixCLE.symm.contDiff.contMDiff.comp Units.contMDiff_val).comp
      contMDiff_snd)).contMDiffOn (e.mapsTo_toMatrixCLE_symm_target_continuousLinearMap σ)
  rw [target_frameBundle]
  intro p hp
  have key : ∀ q ∈ e.baseSet ×ˢ (univ : Set (GL (Fin n) 𝕜)),
      ((e.frameBundle σ).toOpenPartialHomeomorph.symm q).val =
        eH.toPartialEquiv.symm (q.1, σ.toMatrixCLE.symm q.2) := fun q hq ↦ by
    rw [frameBundle_symm_apply]
    exact e.coe_smul_frameAt σ hq.1 q.2
  -- A map into the open subset of frames is `C^k` when its composite with the inclusion is.
  exact (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff _ _ _).1
    ((hval p hp).congr key (key p hp))

end Bundle.Trivialization

namespace TauCeti.FrameBundle

variable (E) in
/-- The atlas of the frame bundle induced by the trivializations of `E` is `C^k`: its
trivializations are `C^k` diffeomorphisms onto open subsets of `B × GL n 𝕜`. -/
theorem isContMDiff_atlas (σ : F ≃L[𝕜] (Fin n → 𝕜)) :
    (atlas E σ).IsContMDiff k IB 𝓘(𝕜, Matrix (Fin n) (Fin n) 𝕜)
      (IB.prod 𝓘(𝕜, (Fin n → 𝕜) →L[𝕜] F)) where
  contMDiffOn_trivAt b := by
    rw [atlas_trivAt]
    exact (trivializationAt F E b).contMDiffOn_frameBundle σ
  contMDiffOn_trivAt_symm b := by
    rw [atlas_trivAt]
    exact (trivializationAt F E b).contMDiffOn_frameBundle_symm σ

variable (E) in
/-- **The frame bundle is a smooth fibre bundle.** For an isomorphism `σ : F ≃ 𝕜ⁿ`, the fibres of
the frame bundle of a `C^k` vector bundle form a `C^k` fibre bundle with fibre `GL n 𝕜`, principal
by `TauCeti.FrameBundle.principalBundle`. -/
theorem contMDiffFiberBundle (σ : F ≃L[𝕜] (Fin n → 𝕜)) :
    letI := (atlas E σ).fiberBundle
    ContMDiffFiberBundle k (GL (Fin n) 𝕜) (MapFiber (proj : FrameBundle 𝕜 n F E → B)) IB
      𝓘(𝕜, Matrix (Fin n) (Fin n) 𝕜) :=
  (atlas E σ).contMDiffFiberBundle (isContMDiff_atlas E σ)

/-- **The right action on frames is smooth.** The action `(v, g) ↦ v • g` of `GL n 𝕜` on the frames
of a `C^k` vector bundle is `C^k`. -/
theorem contMDiff_smul :
    ContMDiff ((IB.prod 𝓘(𝕜, (Fin n → 𝕜) →L[𝕜] F)).prod 𝓘(𝕜, Matrix (Fin n) (Fin n) 𝕜))
      (IB.prod 𝓘(𝕜, (Fin n → 𝕜) →L[𝕜] F)) k
      (fun p : FrameBundle 𝕜 n F E × GL (Fin n) 𝕜 ↦ op p.2 • p.1) := by
  intro p
  let e := trivializationAt F E p.1.proj
  have hp : p.1.proj ∈ e.baseSet := mem_baseSet_trivializationAt F E p.1.proj
  -- The frame `p.1` identifies `𝕜ⁿ` with `F` through `e`.
  let σ : F ≃L[𝕜] (Fin n → 𝕜) := (p.1.frameEquiv.trans (e.continuousLinearEquivAt 𝕜 _ hp)).symm
  let t := e.frameBundle (n := n) σ
  have hU : (Prod.fst : FrameBundle 𝕜 n F E × GL (Fin n) 𝕜 → _) ⁻¹' (proj ⁻¹' e.baseSet) ∈
      nhds p :=
    ((e.open_baseSet.preimage continuous_proj).preimage continuous_fst).mem_nhds hp
  -- In the trivialization `t`, the action is right multiplication on the `GL n 𝕜` factor.
  have hcoord : ContMDiffOn ((IB.prod 𝓘(𝕜, (Fin n → 𝕜) →L[𝕜] F)).prod
      𝓘(𝕜, Matrix (Fin n) (Fin n) 𝕜)) (IB.prod 𝓘(𝕜, Matrix (Fin n) (Fin n) 𝕜)) k
      (fun q : FrameBundle 𝕜 n F E × GL (Fin n) 𝕜 ↦ ((t q.1).1, (t q.1).2 * q.2))
      (Prod.fst ⁻¹' (proj ⁻¹' e.baseSet)) := by
    have ht := (e.contMDiffOn_frameBundle (IB := IB) (k := k) σ).comp
      (contMDiff_fst (M := FrameBundle 𝕜 n F E) (N := GL (Fin n) 𝕜)
        (J := 𝓘(𝕜, Matrix (Fin n) (Fin n) 𝕜))).contMDiffOn fun q hq ↦ by
          rwa [Trivialization.source_frameBundle]
    exact (contMDiff_fst.comp_contMDiffOn ht).prodMk
      ((contMDiff_mul 𝓘(𝕜, Matrix (Fin n) (Fin n) 𝕜) k).comp_contMDiffOn
        ((contMDiff_snd.comp_contMDiffOn ht).prodMk contMDiff_snd.contMDiffOn))
  refine (((e.contMDiffOn_frameBundle_symm σ).comp hcoord fun q hq ↦ by
    rw [Trivialization.target_frameBundle]
    exact ⟨by simpa [t] using hq, trivial⟩).contMDiffAt hU).congr_of_eventuallyEq
      (Filter.eventually_of_mem hU fun q hq ↦ ?_)
  have hq' : op q.2 • q.1 ∈ t.source := by
    rw [Trivialization.source_frameBundle]
    exact hq
  rw [comp_apply, ← Trivialization.frameBundle_smul e σ hq q.2,
    (by simp [t] : (t q.1).1 = (op q.2 • q.1).proj)]
  exact (t.symm_apply_mk_proj hq').symm

end TauCeti.FrameBundle
