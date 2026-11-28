/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Dual
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteRank.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Hom.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Trivialization

/-!
# Smooth and holomorphic dual cores

Dualizing a finite-rank bundle core preserves its regularity: dual transitions are the
transposes of reverse transitions, and transposition is continuous linear. Over a complex
manifold this constructs the holomorphic dual on the existing dual-core carrier.

`dualTotalSpaceDiffeomorph` identifies that construction with Mathlib's dual bundle, the
bundle of continuous linear maps to the trivial line. Its underlying homeomorphism is
`dualTotalSpaceHomeomorph`; in a frame it reads a dual coordinate vector as the functional
with those coefficients. It is `𝕜`-linear on fibres (complex-linear, not conjugate-linear,
when `𝕜 = ℂ`).
The naturality formula `dualFiberEquiv_fiberMap_dualMap` for the underlying identification
also describes this diffeomorphism.

For a vector bundle `V` with model fibre `F` and coordinate equivalence `e : F ≃L[𝕜] (Fin r → 𝕜)`:

* `ofBundleDualTotalSpaceDiffeomorph` identifies `(ofBundle 𝕜 e V).dual.core.TotalSpace` with
  Mathlib's dual bundle `fun x ↦ V x →L[𝕜] 𝕜` via `ofBundleDualFiberEquiv`;
* `ofBundleDualChangeDiffeomorph` lifts `(dualFunctor 𝕜 B).mapIso (ofBundleChangeIso e₂ e₁ V).op`
  to a `C^n` diffeomorphism between `(ofBundle 𝕜 e₁ V).dual.core.TotalSpace` and
  `(ofBundle 𝕜 e₂ V).dual.core.TotalSpace`, commuting with `ofBundleDualTotalSpaceDiffeomorph`
  (`ofBundleDualTotalSpaceDiffeomorph_changeDiffeomorph`).

No regularity of the base atlas or transitions is needed for the comparisons themselves: their
expressions in the corresponding bundle charts are fixed continuous linear equivalences.
The regularity instance supplies the smooth bundle structure when the original core is smooth.

## References

* J. W. Milnor and J. D. Stasheff, *Characteristic Classes*, §3.
* D. Huybrechts, *Complex Geometry: An Introduction*, §2.2.
-/

public section

open Bundle CategoryTheory FiberBundle Set VectorBundleCore
open scoped Manifold ContDiff Topology

namespace TauCeti.FiniteRankBundleCore

variable {𝕜 B : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [TopologicalSpace B] {EB HB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  [TopologicalSpace HB] [ChartedSpace HB B] {I : ModelWithCorners 𝕜 EB HB} {n : ℕ∞ω}

/-- The dual of a `C^n` finite-rank core is `C^n`. For complex scalars at regularity `∞`,
this is the holomorphic dual structure on the shared dual core. -/
instance isContMDiff_dual (A : FiniteRankBundleCore 𝕜 B) [A.core.IsContMDiff I n] :
    A.dual.core.IsContMDiff I n where
  contMDiffOn_coordChange i j := by
    -- The dual core keeps the same coordinate spaces and chart domains; unfold its
    -- projections before elaborating the operator-space topology and the composition.
    dsimp +instances only [dual]
    have ht := (ContinuousLinearMap.piTransposeL 𝕜 (Fin A.rank) (Fin A.rank)).contMDiff
      |>.comp_contMDiffOn ((A.core.contMDiffOn_coordChange (n := n) I j i).mono
        (fun _ (hx : _ ∈ A.core.baseSet i ∩ A.core.baseSet j) ↦ ⟨hx.2, hx.1⟩))
    simpa only [Function.comp_def, ContinuousLinearMap.piTransposeL_apply] using ht

/-- Reading the vectors of the dual core as functionals is `C^n` on total spaces, in the
induced dual-bundle charts. -/
theorem contMDiff_dualFiberEquiv (A : FiniteRankBundleCore 𝕜 B) :
    ContMDiff (I.prod 𝓘(𝕜, Fin A.dual.rank → 𝕜))
      (I.prod 𝓘(𝕜, (Fin A.rank → 𝕜) →L[𝕜] 𝕜)) n
      (fun p : A.dual.core.TotalSpace ↦
        TotalSpace.mk' ((Fin A.rank → 𝕜) →L[𝕜] 𝕜)
          (E := fun x ↦ A.core.Fiber x →L[𝕜] Trivial B 𝕜 x) p.proj
          (dualFiberEquiv A p.proj p.snd)) := by
  intro p
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_proj _, ?_⟩
  have hp : p ∈ (A.dual.core.localTriv p.proj).source :=
    (A.dual.core.mem_localTriv_source p.proj p).2 (A.dual.core.mem_baseSet_at p.proj)
  have hU := (A.dual.core.localTriv p.proj).open_source.mem_nhds hp
  have hc := Bundle.TotalSpace.contMDiffAt_trivializationAt_snd
    (IB := I) (n := n) p
  have htriv : trivializationAt (Fin A.dual.rank → 𝕜) A.dual.core.Fiber p.proj =
      A.dual.core.localTriv p.proj := by
    rw [VectorBundleCore.trivializationAt, VectorBundleCore.localTrivAt, A.dual.indexAt_eq]
  rw [htriv] at hc
  refine ((ContinuousLinearEquiv.piRing (𝕜 := 𝕜) (E := 𝕜) (Fin A.rank)).symm.contDiff.contMDiff
    |>.contMDiffAt.comp p hc).congr_of_eventuallyEq ?_
  filter_upwards [hU] with q hq
  exact (A.dualFiberEquiv_inCoordinates p.proj q.proj
    ((A.dual.core.mem_localTriv_source p.proj q).1 hq) q.snd)

/-- The dual core and Mathlib's dual bundle are `C^n` diffeomorphic by the canonical
`𝕜`-linear identification of each coordinate vector with a functional. -/
noncomputable def dualTotalSpaceDiffeomorph (A : FiniteRankBundleCore 𝕜 B)
    (I : ModelWithCorners 𝕜 EB HB) (n : ℕ∞ω) :
    A.dual.core.TotalSpace ≃ₘ^n⟮I.prod 𝓘(𝕜, Fin A.dual.rank → 𝕜),
      I.prod 𝓘(𝕜, (Fin A.rank → 𝕜) →L[𝕜] 𝕜)⟯
        TotalSpace ((Fin A.rank → 𝕜) →L[𝕜] 𝕜)
          (fun x ↦ A.core.Fiber x →L[𝕜] Trivial B 𝕜 x) :=
  bundleDiffeomorph (dualFiberEquiv A) (A.contMDiff_dualFiberEquiv (I := I) (n := n))

/-- The diffeomorphism retains the canonical dual-bundle homeomorphism. -/
@[simp]
theorem dualTotalSpaceDiffeomorph_toHomeomorph (A : FiniteRankBundleCore 𝕜 B) :
    (A.dualTotalSpaceDiffeomorph I n).toHomeomorph = A.dualTotalSpaceHomeomorph := by
  apply Homeomorph.ext
  intro p
  exact (bundleDiffeomorph_apply (IB := I) (n := n) (dualFiberEquiv A)
    A.contMDiff_dualFiberEquiv p).trans (A.dualTotalSpaceHomeomorph_apply p).symm

/-- The forward comparison reads a dual coordinate vector as a functional in the same fibre. -/
@[simp]
theorem dualTotalSpaceDiffeomorph_apply (A : FiniteRankBundleCore 𝕜 B)
    (p : A.dual.core.TotalSpace) :
    A.dualTotalSpaceDiffeomorph I n p = ⟨p.proj, dualFiberEquiv A p.proj p.snd⟩ :=
  bundleDiffeomorph_apply _ _ p

/-- The inverse comparison records the coefficients of the functional in the same fibre. -/
@[simp]
theorem dualTotalSpaceDiffeomorph_symm_apply (A : FiniteRankBundleCore 𝕜 B)
    (p : TotalSpace ((Fin A.rank → 𝕜) →L[𝕜] 𝕜)
      (fun x ↦ A.core.Fiber x →L[𝕜] Trivial B 𝕜 x)) :
    (A.dualTotalSpaceDiffeomorph I n).symm p =
      ⟨p.proj, (dualFiberEquiv A p.proj).symm p.snd⟩ :=
  bundleDiffeomorph_symm_apply _ _ p

section OfBundleDual

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

section DualBundle

variable {r : ℕ} (e : F ≃L[𝕜] (Fin r → 𝕜)) (V : B → Type*)
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

/-- Reading dual-core coordinates as functionals on `V` is `C^n` on total spaces. -/
theorem contMDiff_ofBundleDualFiberEquiv :
    ContMDiff (I.prod 𝓘(𝕜, Fin (ofBundle 𝕜 e V).dual.rank → 𝕜))
      (I.prod 𝓘(𝕜, F →L[𝕜] 𝕜)) n
      (fun p : (ofBundle 𝕜 e V).dual.core.TotalSpace ↦
        TotalSpace.mk' (F →L[𝕜] 𝕜) (E := fun x ↦ V x →L[𝕜] 𝕜) p.proj
          (ofBundleDualFiberEquiv e V p.proj p.snd)) := by
  intro p
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_proj _, ?_⟩
  let L : (Fin (ofBundle 𝕜 e V).dual.rank → 𝕜) →L[𝕜] (F →L[𝕜] 𝕜) :=
    ((ContinuousLinearEquiv.piRing (𝕜 := 𝕜) (E := 𝕜) (Fin r)).symm.trans
      (e.symm.arrowCongr (ContinuousLinearEquiv.refl 𝕜 𝕜))).toContinuousLinearMap
  exact (L.contDiff.comp_contMDiffAt
    ((ofBundle 𝕜 e V).dual.contMDiffAt_localTriv_snd (I := I) (n := n) p)).congr_of_eventuallyEq
      (eventuallyEq_inCoordinates_ofBundleDualFiberEquiv e V p)

/-- The reconstructed total space of `(ofBundle 𝕜 e V).dual` is `C^n` diffeomorphic to Mathlib's
dual bundle `fun x ↦ V x →L[𝕜] 𝕜`, over the identity of the base and fibrewise `𝕜`-linear via
`ofBundleDualFiberEquiv`. No smoothness assumption on `V` is required. -/
noncomputable def ofBundleDualTotalSpaceDiffeomorph
    (I : ModelWithCorners 𝕜 EB HB) (n : ℕ∞ω) :
    (ofBundle 𝕜 e V).dual.core.TotalSpace ≃ₘ^n⟮
      I.prod 𝓘(𝕜, Fin (ofBundle 𝕜 e V).dual.rank → 𝕜), I.prod 𝓘(𝕜, F →L[𝕜] 𝕜)⟯
      TotalSpace (F →L[𝕜] 𝕜) (fun x ↦ V x →L[𝕜] 𝕜) :=
  bundleDiffeomorph (ofBundleDualFiberEquiv e V)
    (contMDiff_ofBundleDualFiberEquiv (I := I) (n := n) e V)

@[simp]
theorem ofBundleDualTotalSpaceDiffeomorph_toHomeomorph :
    (ofBundleDualTotalSpaceDiffeomorph e V I n).toHomeomorph =
      ofBundleDualTotalSpaceHomeomorph e V :=
  Homeomorph.ext fun p ↦
    (bundleDiffeomorph_apply _ _ p).trans (ofBundleDualTotalSpaceHomeomorph_apply e V p).symm

@[simp]
theorem ofBundleDualTotalSpaceDiffeomorph_apply
    (p : (ofBundle 𝕜 e V).dual.core.TotalSpace) :
    ofBundleDualTotalSpaceDiffeomorph e V I n p =
      ⟨p.proj, ofBundleDualFiberEquiv e V p.proj p.snd⟩ :=
  bundleDiffeomorph_apply _ _ p

@[simp]
theorem ofBundleDualTotalSpaceDiffeomorph_symm_apply
    (p : TotalSpace (F →L[𝕜] 𝕜) (fun x ↦ V x →L[𝕜] 𝕜)) :
    (ofBundleDualTotalSpaceDiffeomorph e V I n).symm p =
      ⟨p.proj, (ofBundleDualFiberEquiv e V p.proj).symm p.snd⟩ :=
  bundleDiffeomorph_symm_apply _ _ p

end DualBundle

section DualChange

variable {r₁ r₂ : ℕ} (e₁ : F ≃L[𝕜] (Fin r₁ → 𝕜)) (e₂ : F ≃L[𝕜] (Fin r₂ → 𝕜))
  (V : B → Type*) [∀ x, AddCommMonoid (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

/-- Changing the coordinate equivalence from `e₁` to `e₂` induces a `C^n` diffeomorphism of dual
core total spaces, lifting `(dualFunctor 𝕜 B).mapIso (ofBundleChangeIso e₂ e₁ V).op` with fibre
map `(e₂.symm.trans e₁).piTranspose`. -/
noncomputable def ofBundleDualChangeDiffeomorph
    (I : ModelWithCorners 𝕜 EB HB) (n : ℕ∞ω) :
    (ofBundle 𝕜 e₁ V).dual.core.TotalSpace ≃ₘ^n⟮
      I.prod 𝓘(𝕜, Fin (ofBundle 𝕜 e₁ V).dual.rank → 𝕜),
      I.prod 𝓘(𝕜, Fin (ofBundle 𝕜 e₂ V).dual.rank → 𝕜)⟯
      (ofBundle 𝕜 e₂ V).dual.core.TotalSpace :=
  isoToDiffeomorphOfConst
    ((dualFunctor 𝕜 B).mapIso (ofBundleChangeIso e₂ e₁ V).op)
    (fun i ↦ by
      rw [VectorBundleCore.baseSet_at, VectorBundleCore.baseSet_at,
        localTriv_baseSet_dual, localTriv_baseSet_dual, baseSet_ofBundle, baseSet_ofBundle])
    ((e₂.symm.trans e₁).piTranspose :
      (Fin (ofBundle 𝕜 e₁ V).dual.rank → 𝕜) ≃L[𝕜] (Fin (ofBundle 𝕜 e₂ V).dual.rank → 𝕜))
    (fun i j x _ _ ↦ by
      rw [coordChange_dual, coordChange_dual]
      let T : (Fin r₁ → 𝕜) ≃L[𝕜] (Fin r₂ → 𝕜) := (e₂.symm.trans e₁).piTranspose
      have h : T.toContinuousLinearMap.comp ((ofBundle 𝕜 e₁ V).core.coordChange j i x).piTranspose =
          ((ofBundle 𝕜 e₂ V).core.coordChange j i x).piTranspose.comp T.toContinuousLinearMap := by
        rw [ContinuousLinearEquiv.coe_piTranspose,
          ← ContinuousLinearMap.piTranspose_comp, ← ContinuousLinearMap.piTranspose_comp]
        congr 1; ext u
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
          ContinuousLinearEquiv.trans_apply, coordChange_ofBundle,
          ContinuousLinearEquiv.symm_apply_apply]
      exact h)
    (fun x ↦
      (congrArg (fun f ↦ CoordinateHom.fiberMap f x)
        ((Functor.mapIso_hom (dualFunctor 𝕜 B) (ofBundleChangeIso e₂ e₁ V).op).trans <|
          (dualFunctor_map 𝕜 B (ofBundleChangeIso e₂ e₁ V).op.hom).trans <|
            congrArg dualMap
              (congrArg Quiver.Hom.unop (Iso.op_hom (ofBundleChangeIso e₂ e₁ V))))).trans <|
        ((fiberMap_dualMap (ofBundleChangeIso e₂ e₁ V).hom x).trans
          (congrArg ContinuousLinearMap.piTranspose
            (fiberMap_ofBundleChangeIso_hom e₂ e₁ V x))).trans
          (ContinuousLinearEquiv.coe_piTranspose (e₂.symm.trans e₁)).symm)

@[simp]
theorem ofBundleDualChangeDiffeomorph_apply
    (p : (ofBundle 𝕜 e₁ V).dual.core.TotalSpace) :
    ofBundleDualChangeDiffeomorph e₁ e₂ V I n p =
      (dualMap (ofBundleChangeIso e₂ e₁ V).hom).totalSpaceMap p :=
  (congrFun (coe_isoToDiffeomorphOfConst _ _ _ _ _) p).trans <|
    congrArg (CoordinateHom.totalSpaceMap · p)
      ((Functor.mapIso_hom (dualFunctor 𝕜 B) (ofBundleChangeIso e₂ e₁ V).op).trans <|
        (dualFunctor_map 𝕜 B (ofBundleChangeIso e₂ e₁ V).op.hom).trans <|
          congrArg dualMap (congrArg Quiver.Hom.unop (Iso.op_hom (ofBundleChangeIso e₂ e₁ V))))

@[simp]
theorem ofBundleDualChangeDiffeomorph_symm_apply
    (p : (ofBundle 𝕜 e₂ V).dual.core.TotalSpace) :
    (ofBundleDualChangeDiffeomorph e₁ e₂ V I n).symm p =
      (dualMap (ofBundleChangeIso e₁ e₂ V).hom).totalSpaceMap p :=
  (congrFun (coe_isoToDiffeomorphOfConst_symm _ _ _ _ _) p).trans <|
    congrArg (CoordinateHom.totalSpaceMap · p)
      ((Functor.mapIso_inv (dualFunctor 𝕜 B) (ofBundleChangeIso e₂ e₁ V).op).trans <|
        (dualFunctor_map 𝕜 B (ofBundleChangeIso e₂ e₁ V).op.inv).trans <|
          congrArg dualMap
            ((congrArg Quiver.Hom.unop (Iso.op_inv (ofBundleChangeIso e₂ e₁ V))).trans
              (ofBundleChangeIso_inv e₂ e₁ V)))

end DualChange

section DualChangeCompat

variable {r₁ r₂ : ℕ} (e₁ : F ≃L[𝕜] (Fin r₁ → 𝕜)) (e₂ : F ≃L[𝕜] (Fin r₂ → 𝕜))
  (V : B → Type*) [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

/-- Changing the coordinate equivalence commutes with `ofBundleDualTotalSpaceDiffeomorph`. -/
theorem ofBundleDualTotalSpaceDiffeomorph_changeDiffeomorph
    (p : (ofBundle 𝕜 e₁ V).dual.core.TotalSpace) :
    ofBundleDualTotalSpaceDiffeomorph e₂ V I n
        (ofBundleDualChangeDiffeomorph e₁ e₂ V I n p) =
      ofBundleDualTotalSpaceDiffeomorph e₁ V I n p := by
  rcases p with ⟨x, v⟩
  rw [ofBundleDualChangeDiffeomorph_apply, ofBundleDualTotalSpaceDiffeomorph_apply,
    ofBundleDualTotalSpaceDiffeomorph_apply, CoordinateHom.totalSpaceMap_mk]
  exact congrArg (TotalSpace.mk' (F →L[𝕜] 𝕜) x)
    (ofBundleDualFiberEquiv_dualMap_changeIso e₁ e₂ V x v)

end DualChangeCompat

end OfBundleDual

end TauCeti.FiniteRankBundleCore
